import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyCompFinMemIntLocAdele
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitFinCutIdeleOfNotMem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixIntegralOfAddCharTraceDual

noncomputable section

namespace GlobalTheory.ThK.ConeEulerChr

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.ConeEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem tendsto_liftV (a : ∀ v : Pl F, Fv F v) (ha : ∀ v, a v ∈ v.adicCompletionIntegers F) :
    Tendsto (fun v => GlobalTheory.LatVac.liftV v (a v)) cofinite (𝓝 0) := by
  have hf : ∀ v w : Pl F, evalV F w (singleFin v (a v)) ∈ w.adicCompletionIntegers F := fun v w => by
    by_cases h : w = v
    · subst h; rw [evalV_singleFin_self]; exact ha w
    · rw [evalV_singleFin_ne h]; exact zero_mem _
  have hc := (RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) (𝓕 := cofinite)).continuous
  have ht : Tendsto (fun v : Pl F => fun w : HeightOneSpectrum (𝓞 F) =>
      (⟨evalV F w (singleFin v (a v)), hf v w⟩ : (w.adicCompletionIntegers F : Set (w.adicCompletion F)))) cofinite
      (𝓝 fun w => ⟨0, zero_mem (w.adicCompletionIntegers F)⟩) := by
    refine tendsto_pi_nhds.2 fun w => tendsto_subtype_rng.2 ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_cofinite_ne w] with v hv
    exact (evalV_singleFin_ne (Ne.symm hv) _).symm
  have h2 : Tendsto (fun v : Pl F => singleFin v (a v)) cofinite (𝓝 (0 : Af F)) := (hc.tendsto _).comp ht
  have hp : Continuous fun β : Af F => pairA F 0 β := continuous_const.prodMk continuous_id
  exact (hp.tendsto 0).comp h2

theorem exists_coords {v : Pl F} {y : Fv F v ⊗[F] E} (hy : y ∈ intLoc F E v) :
    ∃ a : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → Fv F v, (∀ i, a i ∈ v.adicCompletionIntegers F) ∧
      y = ∑ i, a i ⊗ₜ[F] ((RingOfIntegers.basis E i : 𝓞 E) : E) := by
  refine intLoc_induction (p := fun y => ∃ a : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → Fv F v,
    (∀ i, a i ∈ v.adicCompletionIntegers F) ∧ y = ∑ i, a i ⊗ₜ[F] ((RingOfIntegers.basis E i : 𝓞 E) : E))
    (fun a ha x => ?_) ⟨0, fun _ => zero_mem _, by simp⟩ ?_ ?_ hy
  · refine ⟨fun i => (RingOfIntegers.basis E).repr x i • a, fun i => zsmul_mem ha _, ?_⟩
    have hx : (x : E) = ∑ i, (RingOfIntegers.basis E).repr x i • ((RingOfIntegers.basis E i : 𝓞 E) : E) := by
      conv_lhs => rw [← (RingOfIntegers.basis E).sum_repr x]
      simp
    rw [hx, TensorProduct.tmul_sum]
    exact Finset.sum_congr rfl fun i _ => (TensorProduct.smul_tmul _ _ _).symm
  · rintro _ _ ⟨a, ha, rfl⟩ ⟨c, hc, rfl⟩
    exact ⟨a + c, fun i => add_mem (ha i) (hc i), by simp [TensorProduct.add_tmul, Finset.sum_add_distrib]⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact ⟨-a, fun i => neg_mem (ha i), by simp [TensorProduct.neg_tmul]⟩

theorem tendsto_zero_of_intLoc (x : Pl F → AE F E)
    (h : ∀ᶠ v in cofinite, At (evFin F v) (x v) ∧ compFin F E v (x v) ∈ intLoc F E v) :
    Tendsto x cofinite (𝓝 0) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  have key : ∀ v : Pl F, ∃ a : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → Fv F v,
      (∀ i, a i ∈ v.adicCompletionIntegers F) ∧ (At (evFin F v) (x v) ∧ compFin F E v (x v) ∈ intLoc F E v →
      x v = ∑ i, GlobalTheory.LatVac.liftV v (a i) • ((1 : AF F) ⊗ₜ[F] ((RingOfIntegers.basis E i : 𝓞 E) : E))) := fun v => by
    by_cases hv : At (evFin F v) (x v) ∧ compFin F E v (x v) ∈ intLoc F E v
    · obtain ⟨a, ha, e⟩ := exists_coords hv.2
      obtain ⟨h1, h2⟩ := at_evFin_iff.1 hv.1
      refine ⟨a, ha, fun _ => GlobalTheory.Doubling.adele_ext (fun w => ?_) fun w => ?_⟩
      · rw [h1, map_sum]
        exact (Finset.sum_eq_zero fun i _ => by
          rw [compInf_smul, show evInf F w (GlobalTheory.LatVac.liftV v (a i)) = 0 from rfl, zero_smul]).symm
      · rw [map_sum]
        by_cases hw : w = v
        · subst hw
          rw [e]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [compFin_smul, GlobalTheory.LatVac.evFin_liftV]
          change _ = a i • (evFin F w 1 ⊗ₜ[F] _)
          rw [map_one, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
          rfl
        · rw [h2 w hw]
          exact (Finset.sum_eq_zero fun i _ => by
            rw [compFin_smul, show evFin F w (GlobalTheory.LatVac.liftV v (a i)) = 0 from evalV_singleFin_ne hw _,
              zero_smul]).symm
    · exact ⟨0, fun _ => zero_mem _, fun h => absurd h hv⟩
  choose a ha e using key
  have ht : Tendsto (fun v => ∑ i, GlobalTheory.LatVac.liftV v (a v i) •
      ((1 : AF F) ⊗ₜ[F] ((RingOfIntegers.basis E i : 𝓞 E) : E) : AE F E)) cofinite
      (𝓝 (∑ i, (0 : AF F) • ((1 : AF F) ⊗ₜ[F] ((RingOfIntegers.basis E i : 𝓞 E) : E) : AE F E))) :=
    tendsto_finset_sum _ fun i _ => (tendsto_liftV (fun v => a v i) fun v => ha v i).smul_const _
  simp only [zero_smul, Finset.sum_const_zero] at ht
  refine ht.congr' ?_
  filter_upwards [h] with v hv using (e v hv).symm

theorem tendsto_one_of_unitsAt (m : Pl F → (AE F E)ˣ) (h : ∀ᶠ v in cofinite, m v ∈ unitsAt E v) :
    Tendsto m cofinite (𝓝 1) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  have key : ∀ m : Pl F → (AE F E)ˣ, (∀ᶠ v in cofinite, m v ∈ unitsAt E v) →
      Tendsto (fun v => (m v : AE F E)) cofinite (𝓝 1) := fun m h => by
    have := (tendsto_zero_of_intLoc (fun v => (m v : AE F E) - 1) (h.mono fun v hv => ⟨hv.1, by
      rw [map_sub, map_one]; exact sub_mem (mem_unitsAt.1 hv).2.1 (one_mem _)⟩)).add_const 1
    simpa using this
  rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  exact (key m h).prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp
    (key (fun v => (m v)⁻¹) (h.mono fun v hv => inv_mem hv)))

theorem eventually_chr_eq_one {ν : Chr F E} (hν : Continuous ν) (m : Pl F → (AE F E)ˣ)
    (h : ∀ᶠ v in cofinite, m v ∈ unitsAt E v) : ∀ᶠ v in cofinite, ν (m v) = 1 := by
  have key : ∀ v, ∃ n : ℕ, ‖(ν (m v) : ℂ) ^ n - 1‖ < 1 → ν (m v) = 1 := fun v => by
    by_contra hc
    push Not at hc
    exact (hc 0).2 (GlobalTheory.CharDualMat.circle_eq_one_of_pow_near _ fun n => (hc n).1)
  choose n hn using key
  have ht := tendsto_one_of_unitsAt (fun v => m v ^ n v) (h.mono fun v hv => pow_mem hv _)
  have hc : Continuous fun x : (AE F E)ˣ => ‖(ν x : ℂ) - 1‖ :=
    ((continuous_subtype_val.comp hν).sub continuous_const).norm
  have h1 := ((hc.tendsto 1).comp ht).eventually (gt_mem_nhds (show ‖(ν 1 : ℂ) - 1‖ < 1 by simp))
  filter_upwards [h1] with v hv
  exact hn v (by simpa using hv)

theorem cutIdele_eq (S : Finset (Pl F)) (l : (AE F E)ˣ) :
    GlobalTheory.Doubling.cutIdele S l = unitArch F E l * ∏ v ∈ S, unitAt E v l := by
  have h1 : (eInf F).1 = 1 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by
    rw [map_one]; exact evI_realAd_one)
  have ha : GlobalTheory.Doubling.cutIdele ∅ l = unitArch F E l := by
    refine GlobalTheory.Doubling.idele_ext (fun w => ?_) fun v => ?_
    · rw [GlobalTheory.Doubling.unitInf_cutIdele]
      refine Units.ext ?_
      change compInf F E w l = compInf F E w (eInf F • (l : AE F E) + (1 - eInf F) • 1)
      have h : evInf F w (eInf F) = 1 := congrFun h1 w
      rw [map_add, compInf_smul, compInf_smul, map_sub, map_one, h, sub_self, zero_smul, one_smul, add_zero]
    · rw [GlobalTheory.Doubling.unitFin_cutIdele_of_notMem _ (Finset.notMem_empty v)]
      have := at_evI_iff.1 (unitArch_mem l) v
      rw [map_sub, map_one, sub_eq_zero] at this
      exact Units.ext this.symm
  rw [← ha, GlobalTheory.Doubling.cutIdele, GlobalTheory.Doubling.cutIdele, Finset.prod_empty, mul_one]
  congr 1
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [← ideleAt_unitFin (unitAt_mem v l)]
  exact congrArg _ (Units.ext (compFin_unitAt_self v l).symm)

theorem chr_abs_eq_finprod : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (ν : Chr F E), Continuous ν → ∀ (l : (AE F E)ˣ) (z : ℕ),
    (Function.mulSupport fun v : Pl F => (ν (unitAt E v l) : ℂ) * ((absE F E (unitAt E v l) : ℝ) : ℂ) ^ z).Finite ∧
    (ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z = (ν (unitArch F E l) : ℂ) * ((absE F E (unitArch F E l) : ℝ) : ℂ) ^ z *
      ∏ᶠ v : Pl F, (ν (unitAt E v l) : ℂ) * ((absE F E (unitAt E v l) : ℝ) : ℂ) ^ z := by
  intro F E _ _ _ _ _ ν hν l z
  have hu := eventually_unitAt_mem_unitsAt F E l
  have hfin : (Function.mulSupport fun v : Pl F =>
      (ν (unitAt E v l) : ℂ) * ((absE F E (unitAt E v l) : ℝ) : ℂ) ^ z).Finite := by
    refine (eventually_cofinite.1 (hu.and (eventually_chr_eq_one hν _ hu))).subset fun v hv h => hv ?_
    simp only [h.2, absE_of_mem_unitsAt h.1]
    simp
  refine ⟨hfin, ?_⟩
  let χ : (AE F E)ˣ →* ℂ :=
    { toFun := fun x => (ν x : ℂ) * ((absE F E x : ℝ) : ℂ) ^ z
      map_one' := by simp
      map_mul' := fun x y => by simp only [map_mul, Circle.coe_mul, NNReal.coe_mul, Complex.ofReal_mul]; ring }
  have hχ : Continuous χ := (continuous_subtype_val.comp hν).mul
    ((Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp GlobalTheory.Doubling.continuous_absE)).pow z)
  refine tendsto_nhds_unique ((hχ.tendsto l).comp (GlobalTheory.Doubling.tendsto_cutIdele l)) (tendsto_const_nhds.congr' ?_)
  filter_upwards [eventually_ge_atTop hfin.toFinset] with S hS
  rw [finprod_eq_prod_of_mulSupport_toFinset_subset _ hfin hS, Function.comp_apply, cutIdele_eq, map_mul, map_prod]
  rfl

end GlobalTheory.ThK.ConeEulerChr

end
