import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModModT
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.FDMSubCompact
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsOpenNsmulCompletedHomLatticeFiniteAdelic
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUniqueAdelicMatrixRealComponentsFinitePart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumTranslateConjugateJetBound
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualCLatP
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio

namespace GlobalTheory.VacNormMean

theorem integral_eq_mean {G V : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [MeasurableSpace G]
    [BorelSpace G] [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [SecondCountableTopology V]
    [LocallyCompactSpace V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]
    (ν : Measure G) [ν.IsAddLeftInvariant] (Y : G →+ V) (hY : Continuous Y) (P Γ : AddSubgroup G) [Countable Γ]
    (hP : IsOpen (P : Set G)) (Λ : AddSubgroup V) [DiscreteTopology Λ] (hsurj : ∀ v, ∃ p ∈ P, Y p = v)
    (happ : ∀ w, ∃ γ ∈ Γ, γ + w ∈ P) (h1 : ∀ γ ∈ Γ, γ ∈ P → Y γ ∈ Λ) (h2 : ∀ l ∈ Λ, ∃ γ ∈ Γ, γ ∈ P ∧ Y γ = l)
    (hinj : ∀ γ ∈ Γ, γ ∈ P → Y γ = 0 → γ = 0) (𝓕 : Set G) (h𝓕 : IsAddFundamentalDomain Γ 𝓕 ν) (hone : ν 𝓕 = 1)
    (g : G → ℝ) (hg : ∀ γ ∈ Γ, ∀ w, g (γ + w) = g w) (h : V → ℝ) (hh : Continuous h) (hgh : ∀ p ∈ P, g p = h (Y p)) :
    ∫ w in 𝓕, g w ∂ν = ⨍ z in Classical.epsilon (fun Fd => IsAddFundamentalDomain Λ Fd μ), h z ∂μ := by
  haveI := GlobalTheory.countable_of_discrete_addSubgroup Λ
  obtain ⟨F0, hF0m, hF0u, hF0⟩ := GlobalTheory.exists_isAddFundamentalDomain_addSubgroup Λ
  have hS := Classical.epsilon_spec (⟨F0, hF0 μ⟩ : ∃ Fd, IsAddFundamentalDomain Λ Fd μ)
  set S := Classical.epsilon (fun Fd => IsAddFundamentalDomain Λ Fd μ)
  haveI : MeasurableConstVAdd Γ G := ⟨fun c => (continuous_const.add continuous_id).measurable⟩
  haveI : VAddInvariantMeasure Γ G ν := ⟨fun c s _ => measure_preimage_add ν (c : G) s⟩
  haveI : MeasurableConstVAdd Λ V := ⟨fun c => (continuous_const.add continuous_id).measurable⟩
  haveI : VAddInvariantMeasure Λ V μ := ⟨fun c s _ => measure_preimage_add μ (c : V) s⟩
  have hper : ∀ l ∈ Λ, ∀ v, h (l + v) = h v := by
    intro l hl v
    obtain ⟨γ, hγ, hγP, rfl⟩ := h2 l hl
    obtain ⟨p, hp, rfl⟩ := hsurj v
    rw [← map_add, ← hgh _ (P.add_mem hγP hp), hg γ hγ, hgh p hp]
  have hm' : MeasurableSet (Y ⁻¹' F0 ∩ (P : Set G)) := (hY.measurable hF0m).inter hP.measurableSet
  have hfd : IsAddFundamentalDomain Γ (Y ⁻¹' F0 ∩ (P : Set G)) ν := by
    refine IsAddFundamentalDomain.mk' hm'.nullMeasurableSet fun w => ?_
    obtain ⟨γ, hγ, hγw⟩ := happ w
    obtain ⟨l, hl, hlu⟩ := hF0u (Y (γ + w))
    obtain ⟨γ', hγ', hγ'P, e⟩ := h2 l l.2
    refine ⟨⟨γ' + γ, Γ.add_mem hγ' hγ⟩, ⟨?_, ?_⟩, ?_⟩
    · change Y (γ' + γ + w) ∈ F0
      rw [add_assoc, map_add, e]; exact hl
    · change γ' + γ + w ∈ P
      rw [add_assoc]; exact P.add_mem hγ'P hγw
    · rintro ⟨β, hβ⟩ ⟨hb1, hb2⟩
      change Y (β + w) ∈ F0 at hb1
      change β + w ∈ P at hb2
      have a1 : β - γ ∈ P := by simpa using P.sub_mem hb2 hγw
      have a2 : β - γ ∈ Γ := Γ.sub_mem hβ hγ
      have a3 := hlu ⟨Y (β - γ), h1 _ a2 a1⟩ (by
        change Y (β - γ) + Y (γ + w) ∈ F0
        rw [← map_add, ← add_assoc, sub_add_cancel]; exact hb1)
      have a4 : Y (β - γ) = l := congrArg Subtype.val a3
      have a5 := hinj _ (Γ.sub_mem a2 hγ') (P.sub_mem a1 hγ'P) (by rw [map_sub, a4, e, sub_self])
      apply Subtype.ext
      change β = γ' + γ
      rw [sub_sub, sub_eq_zero] at a5
      rw [a5, add_comm]
  set m : Measure V := (ν.restrict (P : Set G)).map Y with hm
  have hmA : ∀ A, MeasurableSet A → m A = ν (Y ⁻¹' A ∩ (P : Set G)) := fun A hA => by
    rw [hm, Measure.map_apply hY.measurable hA, Measure.restrict_apply (hY.measurable hA)]
  have hinv : ∀ (v : V) A, MeasurableSet A → m ((fun x => v + x) ⁻¹' A) = m A := by
    intro v A hA
    obtain ⟨p, hp, rfl⟩ := hsurj v
    rw [hmA _ (measurable_const_add _ hA), hmA _ hA, ← measure_preimage_add ν p (Y ⁻¹' A ∩ _)]
    congr 1
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, map_add, SetLike.mem_coe, Pi.add_apply, id]
    exact and_congr_right fun _ => (P.add_mem_cancel_left hp).symm
  haveI : m.IsAddLeftInvariant := (forall_measure_preimage_add_iff m).1 hinv
  have hm1 : m F0 = 1 := by rw [hmA _ hF0m, ← hone]; exact hfd.measure_eq h𝓕
  haveI : SigmaFinite m := by
    refine Measure.sigmaFinite_of_countable (S := Set.range fun l : Λ => (fun x => (l : V) + x) ⁻¹' F0)
      (Set.countable_range _) ?_ ?_
    · rintro _ ⟨l, rfl⟩
      rw [hinv _ _ hF0m, hm1]; exact ENNReal.one_lt_top
    · rw [Set.sUnion_range, Set.eq_univ_iff_forall]
      intro x
      obtain ⟨l, hl, -⟩ := hF0u x
      exact Set.mem_iUnion.2 ⟨l, hl⟩
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts V) := inferInstance
  have hK0 : μ K ≠ 0 := (Measure.measure_pos_of_nonempty_interior μ K.interior_nonempty).ne'
  have hc : m = (m K / μ K) • μ := measure_eq_sub_vadd m μ hK0 K.isCompact.measure_lt_top.ne
  generalize m K / μ K = c at hc
  have hcF : c * μ S = 1 := by
    rw [hS.measure_eq (hF0 μ), ← hm1, hc, Measure.smul_apply, smul_eq_mul]
  have hcr : c.toReal = (μ S).toReal⁻¹ := by
    have := congrArg ENNReal.toReal hcF
    rw [ENNReal.toReal_mul, ENNReal.toReal_one] at this
    exact eq_inv_of_mul_eq_one_left this
  rw [h𝓕.setIntegral_eq hfd (fun γ w => hg γ γ.2 w), setAverage_eq, hS.setIntegral_eq (hF0 μ) (fun l v => hper l l.2 v),
    setIntegral_congr_fun hm' (fun w hw => hgh w hw.2), ← Measure.restrict_restrict (hY.measurable hF0m),
    ← setIntegral_map hF0m hh.aestronglyMeasurable hY.measurable.aemeasurable, ← hm, hc, Measure.restrict_smul,
    integral_smul_measure, hcr, Measure.real]

open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf YYl embV)
open Formalism.MainNotions.StandardLatticesGL3 (stdL La0)

variable {D : D7}

theorem selfDual_std (V : HSp D) (hG : V.gram = 1) : IsSelfDualC V (stdLat V) := by
  have e : stdLat V = GlobalTheory.SW.stdL D.host.E V.rank := by
    ext x
    rw [GlobalTheory.SW.Base.mem_stdL]
    simp only [stdLat, Formalism.MainNotions.StandardLatticesGL3.stdL, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]
    refine forall_congr' fun i => ?_
    exact ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun h => ⟨⟨x i, h⟩, rfl⟩⟩
  rw [e]; exact GlobalTheory.Ker.Base.selfDualC_stdL hG

theorem discreteTopology_unitCurvePeriodLattice (δ : ℂ) (a d : ℕ) (hc : Formalism.MainNotions.StandardLatticesGL3.Crv D ⊤ δ) : DiscreteTopology (La0 D (tor0 D ⊤ δ) a d) := by
  have hSD0 : ∀ N : ℕ, Formalism.MainNotions.StandardLatticesGL3.SD D (stdL D N) := by
    intro N
    obtain ⟨Lt, h1, h2, -⟩ := GlobalTheory.NormSum.exists_lattice_of_adelic_point D N
    rw [← h2]; exact (h1 1).2
  exact GlobalTheory.ConjJet.discrete_of_int D (tor0 D ⊤ δ) _ (area_pos hc) D.host.hyp.2.1.pos
    (GlobalTheory.ThetaLine.theta_line D (GlobalTheory.InducedType.induced_type D).1 ⊤ δ hc a d _
      (Or.inr ⟨_, _, hSD0 _, hSD0 _, rfl⟩)).2.2.2.2.2.2

theorem mem_unitCurvePeriodLattice_iff (δ : ℂ) (a d : ℕ) (x : VC D a d) :
    x ∈ La0 D (tor0 D ⊤ δ) a d ↔ ∃ z ∈ YYl D (stdL D a) (stdL D d), x = fun τ i j => δ * embT D τ (z i j) := by
  constructor
  · intro hx
    refine AddSubgroup.closure_induction (p := fun x _ => ∃ z ∈ YYl D (stdL D a) (stdL D d),
      x = fun τ i j => δ * embT D τ (z i j)) ?_ ⟨0, zero_mem _, by funext τ i j; simp⟩ ?_ ?_ hx
    · rintro _ ⟨w, hw, A, hA, rfl⟩
      refine AddSubgroup.closure_induction (p := fun w _ => ∃ z ∈ YYl D (stdL D a) (stdL D d),
        w • embV D (tor0 D ⊤ δ) A = fun τ i j => δ * embT D τ (z i j)) ?_ ⟨0, zero_mem _, by funext τ i j; simp⟩ ?_ ?_ hw
      · rintro _ ⟨c, -, rfl⟩
        have hc : IsIntegral ℤ ((c : D.host.K) : D.host.E) := c.2.map_of_comp_eq (RingHom.id ℤ) D.host.K.subtype
          (RingHom.ext_int _ _)
        refine ⟨(⟨_, hc⟩ : 𝓞 D.host.E) • A, Submodule.smul_mem _ _ hA, ?_⟩
        funext τ i j
        change δ * D.host.φ₀ _ * embT D τ (A i j) = δ * embT D τ (((c : D.host.K) : D.host.E) * A i j)
        rw [map_mul, (GlobalTheory.InducedType.induced_type D).1.1 τ, mul_assoc]
      · rintro u v _ _ ⟨z, hz, e⟩ ⟨z', hz', e'⟩
        exact ⟨z + z', add_mem hz hz', by rw [add_smul, e, e']; funext τ i j; simp [mul_add]⟩
      · rintro u _ ⟨z, hz, e⟩
        exact ⟨-z, neg_mem hz, by rw [neg_smul, e]; funext τ i j; simp⟩
    · rintro u v _ _ ⟨z, hz, e⟩ ⟨z', hz', e'⟩
      exact ⟨z + z', add_mem hz hz', by rw [e, e']; funext τ i j; simp [mul_add]⟩
    · rintro u _ ⟨z, hz, e⟩
      exact ⟨-z, neg_mem hz, by rw [e]; funext τ i j; simp⟩
  · rintro ⟨z, hz, rfl⟩
    exact AddSubgroup.subset_closure ⟨δ, AddSubgroup.subset_closure ⟨1, Submodule.mem_top, by simp⟩, z, hz, rfl⟩

noncomputable def coordHom (θ : InfFam D) (S T : HSp D) (δ : ℂ) (r : D.host.E) : WO S T →+ VC D S.rank T.rank where
  toFun := coordY θ rfl rfl δ r
  map_zero' := by
    funext τ i j
    change δ * embT D τ r * θ τ (infPart D 0) = 0
    rw [RingHom.map_zero, RingHom.map_zero, mul_zero]
  map_add' x y := by
    funext τ i j
    change δ * embT D τ r * θ τ (infPart D (x i j + y i j)) =
      δ * embT D τ r * θ τ (infPart D (x i j)) + δ * embT D τ r * θ τ (infPart D (y i j))
    rw [RingHom.map_add, RingHom.map_add, mul_add]

theorem coordHom_ratW {θ : InfFam D} (hθ : IsInfFam θ) (S T : HSp D) (δ : ℂ) (r : D.host.E)
    (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    coordHom θ S T δ r (ratW T S M) = fun τ i j => δ * embT D τ (r * M i j) := by
  funext τ i j
  change δ * embT D τ r * θ τ (infPart D (incA D (M i j))) = _
  rw [GlobalTheory.FockCompare.comp_incA hθ, map_mul, mul_assoc]
  rfl

theorem coordHom_of_inf (θ : InfFam D) (S T : HSp D) (δ : ℂ) (r : D.host.E) {u : WO S T} (hu : u.map (infPart D) = 0) :
    coordHom θ S T δ r u = 0 := by
  funext τ i j
  have : infPart D (u i j) = 0 := congrFun (congrFun hu i) j
  change δ * embT D τ r * θ τ (infPart D (u i j)) = 0
  rw [this, RingHom.map_zero, mul_zero]

theorem eq_of_inf_fin {θ : InfFam D} (hθ : IsInfFam θ) {S T : HSp D} {u v : WO S T} (hu : u.map (infPart D) = 0)
    (hv : v.map (infPart D) = 0) (h : u.map (finPart D) = v.map (finPart D)) : u = v := by
  have hz : ∀ {u : WO S T}, u.map (infPart D) = 0 → ∀ τ, compAt θ τ u = 0 := fun {u} hu τ => by
    funext i j
    have : infPart D (u i j) = 0 := congrFun (congrFun hu i) j
    change θ τ (infPart D (u i j)) = 0
    rw [this, RingHom.map_zero]
  exact (GlobalTheory.StdUnn.exists_unique_of_comp_finPart D θ hθ _ _ (fun _ => 0) v).unique ⟨hz hu, h⟩ ⟨hz hv, rfl⟩

set_option maxHeartbeats 1600000 in

theorem ip_eq_normSq : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (δ : ℂ) (r : D.host.E), Setup ψ θ S T ⊤ δ r →
  ∀ LT : Lat T, IsSelfDualC T LT →
    (∀ z : Matrix (Fin d) (Fin a) D.host.E, z ∈ Formalism.MainNotions.TaylorLogMetric.YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D a) (Formalism.MainNotions.StandardLatticesGL3.stdL D d) ↔
      finPt hS hT r z ∈ latO S T (stdLat S) LT fun _ => True) →
  ∀ e0 ∈ Formalism.MainNotions.TaylorLogMetric.Th D (Formalism.MainNotions.TaylorLogMetric.tor0 D ⊤ δ) (Formalism.MainNotions.StandardLatticesGL3.stdL D a) (Formalism.MainNotions.StandardLatticesGL3.stdL D d), ∀ f₀,
    Reads ψ θ hS hT ⊤ δ r e0 f₀ → IsSphOff ψ S T (stdLat S) LT ∅ f₀ →
  ∀ (ν : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) ν 𝓕 →
    ip S T ν 𝓕 f₀ f₀ = (Formalism.MainNotions.TaylorLogMetric.normSq D (Formalism.MainNotions.TaylorLogMetric.tor0 D ⊤ δ) (Formalism.MainNotions.StandardLatticesGL3.La0 D (Formalism.MainNotions.TaylorLogMetric.tor0 D ⊤ δ) a d) e0 : ℝ) := by
  intro D ψ θ S T a d hS hT δ r hset LT hLT hiff e0 he0 f₀ hread hsph ν 𝓕 hcov
  subst hS hT
  have hψ : ∀ x, ‖ψ x‖ = 1 := hset.std.1.2.1
  have hSD := selfDual_std S hset.gS
  have hr : r ≠ 0 := hset.scale.ne_zero hset.crv.1.1
  have hδ : δ ≠ 0 := delta_ne_zero hset.crv
  have hrτ : ∀ τ, embT D τ r ≠ 0 := fun τ => (map_ne_zero _).2 hr
  have hvac : IsLatVac (heisO ψ S T) (latO S T (stdLat S) LT fun _ => True) f₀ := by
    have := hsph
    simp only [IsSphOff, Finset.notMem_empty, not_false_eq_true] at this
    exact this
  have hL : ∀ u ∈ latO S T (stdLat S) LT (fun _ => True), ∀ w, ‖f₀ (w + u)‖ = ‖f₀ w‖ := by
    intro u hu w
    obtain ⟨ε, hε, h⟩ := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hset.std hSD hLT).2.2 f₀ hvac u hu
    have h1 := congrArg (fun f => ‖f w‖) (h f₀ hvac)
    simp only [heisO, norm_mul, hψ, one_mul, Pi.smul_apply, smul_eq_mul] at h1
    rcases hε with rfl | rfl <;> simpa using h1
  have hLinf := fun u (hu : u ∈ latO S T (stdLat S) LT fun _ => True) => GlobalTheory.VacUnique.latO_inf S T _ _ _ hu
  have hopen := GlobalTheory.LatOpen.isOpen_nsmul_latO D S T _ _ hSD hLT 1 one_pos
  have happ := GlobalTheory.LatVac.approx hSD hLT
  generalize latO S T (stdLat S) LT (fun _ => True) = L at hiff hL hLinf hopen happ
  let φ : WO S T →+ Matrix (Fin T.rank) (Fin S.rank) _ := (finPart D).toAddMonoidHom.mapMatrix
  have hφ : ∀ w, φ w = w.map (finPart D) := fun _ => rfl
  let P : AddSubgroup (WO S T) := (L.map φ).comap φ
  have hP : ∀ w, w ∈ P ↔ ∃ l ∈ L, φ l = φ w := fun _ => Iff.rfl
  have hPo : IsOpen (P : Set (WO S T)) := by
    convert hopen using 1
    ext w
    refine (hP w).trans (exists_congr fun l => and_congr_right fun _ => ?_)
    rw [one_nsmul, ← hφ, φ.map_sub, sub_eq_zero]
    exact eq_comm
  haveI := hcov.1
  haveI : Countable (ratL T S) := Formalism.IndefR.Eqv.countable_ratMx (D := D) T.rank S.rank
  haveI := discreteTopology_unitCurvePeriodLattice δ S.rank T.rank hset.crv
  have hcont : Continuous fun z : VC D S.rank T.rank =>
      ‖e0 z‖ ^ 2 * Real.exp (-Real.pi * (Hf D (tor0 D ⊤ δ) z z).re) := by
    have := he0.1.continuous
    unfold Hf
    fun_prop
  have key := integral_eq_mean (volume : Measure (VC D S.rank T.rank)) ν (coordHom θ S T δ r) ?_ P (ratL T S) hPo
    (La0 D (tor0 D ⊤ δ) S.rank T.rank) ?_ ?_ ?_ ?_ ?_ 𝓕 hcov.2.1 hcov.2.2 (fun w => ‖f₀ w‖ ^ 2) ?_ _ hcont ?_
  · rw [ip, Formalism.MainNotions.TaylorLogMetric.normSq, ← key, ← integral_complex_ofReal]
    simp only [Complex.mul_conj', Complex.ofReal_pow]
  · refine continuous_pi fun τ => continuous_pi fun i => continuous_pi fun j => ?_
    exact continuous_const.mul ((GlobalTheory.RealWeil.continuous_compAt hset.inf τ _ _).matrix_elem i j)
  · intro v
    obtain ⟨x, h1, h2⟩ := (GlobalTheory.StdUnn.exists_unique_of_comp_finPart D θ hset.inf _ _
      (fun τ => Matrix.of fun i j => (δ * embT D τ r)⁻¹ * v τ i j) 0).exists
    refine ⟨x, (hP x).2 ⟨0, zero_mem _, h2.symm⟩, ?_⟩
    funext τ i j
    change δ * embT D τ r * compAt θ τ x i j = _
    rw [h1, Matrix.of_apply, mul_inv_cancel_left₀ (mul_ne_zero hδ (hrτ τ))]
  · intro w
    obtain ⟨M, u, hu, h⟩ := happ w
    refine ⟨-ratW T S M, neg_mem ⟨M, rfl⟩, (hP _).2 ⟨u, hu, ?_⟩⟩
    rw [map_add, map_neg, eq_neg_add_iff_add_eq]
    funext i j
    exact (h i j).symm
  · rintro _ ⟨M, rfl⟩ hM
    obtain ⟨l, hl, e⟩ := (hP _).1 hM
    have e1 : l = GlobalTheory.VacUnique.finRat S T M :=
      eq_of_inf_fin hset.inf (hLinf l hl) (GlobalTheory.VacUnique.finRat_inf S T M) e
    have e2 : finPt rfl rfl r (-(r • M)) = l := by
      rw [e1, finPt]
      congr 1
      ext i j
      simp [hr]
    refine (mem_unitCurvePeriodLattice_iff δ _ _ _).2 ⟨r • M, ?_, coordHom_ratW hset.inf S T δ r M⟩
    exact neg_mem_iff.1 ((hiff _).2 (e2 ▸ hl))
  · intro l hl
    obtain ⟨z, hz, rfl⟩ := (mem_unitCurvePeriodLattice_iff δ _ _ _).1 hl
    refine ⟨ratW T S (Matrix.of fun i j => -(r⁻¹ * (-z) i j)), ⟨_, rfl⟩, (hP _).2 ⟨_, (hiff _).1 (neg_mem hz), rfl⟩, ?_⟩
    rw [coordHom_ratW hset.inf]
    funext τ i j
    simp [hr]
  · rintro _ ⟨M, rfl⟩ - h0
    have h1 := (coordHom_ratW hset.inf S T δ r M).symm.trans h0
    have : M = 0 := by
      ext i j
      have := congrFun (congrFun (congrFun h1 (D.eTau.symm (Classical.arbitrary _))) i) j
      simpa [hδ, hr] using this
    rw [this, map_zero]
  · rintro _ ⟨M, rfl⟩ w
    have h1 := congrArg norm (hread.1.quasi M w)
    rw [norm_mul, hψ, one_mul] at h1
    exact congrArg (· ^ 2) h1
  · intro p hp
    obtain ⟨l, hl, e⟩ := (hP _).1 hp
    have h1 : (p - l).map (finPart D) = 0 := by rw [← hφ, map_sub, e, sub_self]
    have h2 : coordY θ rfl rfl δ r (p - l) = coordHom θ S T δ r p := by
      change coordHom θ S T δ r (p - l) = _
      rw [map_sub, coordHom_of_inf θ S T δ r (hLinf l hl), sub_zero]
    have h3 := hL l hl (p - l)
    rw [sub_add_cancel, hread.2 _ h1, h2] at h3
    change ‖f₀ p‖ ^ 2 = _
    rw [h3, norm_mul, mul_pow, mul_comm, Complex.norm_exp, ← Real.exp_nat_mul]
    congr 2
    simp
    ring

end GlobalTheory.VacNormMean
