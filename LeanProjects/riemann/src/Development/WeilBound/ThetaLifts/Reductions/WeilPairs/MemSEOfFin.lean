import Mathlib
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.EtaDef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryHeckeCharacterExtendingBaseCharacte
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCongruenceKernelIdeleCharacterTrivialAtInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTensorCongruenceOfSupportedAtInfinity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHalfAbstract
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitEqNormCompletionTensorOfIsInertAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFieldCompletionTensorOfIsInertAtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceSplitOrInertStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemNormGroupIffEverywhereNorm

noncomputable section

open scoped TensorProduct Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF Formalism.IndefR.LiftF
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HeckeExtend GlobalTheory.HeckeExtend.AtInf GlobalTheory.SplitDetCharF

namespace PositivityTheory.ThKW.Eta

theorem exists_ext {G : Type} [CommGroup G] (U V : Subgroup G) (lam : G →* Circle)
    (h : ∀ x ∈ U, x ∈ V → lam x = 1) : ∃ ν : G →* Circle, (∀ x ∈ V, ν x = 1) ∧ ∀ x ∈ U, ν x = lam x := by
  let ψ0 : U →* G ⧸ V := (QuotientGroup.mk' V).comp U.subtype
  have hker : ψ0.ker ≤ (lam.comp U.subtype).ker := fun a ha => h a a.2 ((QuotientGroup.eq_one_iff _).1 ha)
  letI : DivisibleBy (Additive Circle) ℕ := divisibleByOfSMulRightSurj _ _ fun {n} hn u => by
    obtain ⟨t, ht⟩ := Circle.exp_surjective u.toMul
    refine ⟨Additive.ofMul (Circle.exp (t / n)), ?_⟩
    show Additive.ofMul (Circle.exp (t / n) ^ n) = u
    rw [← Circle.exp_nsmul, nsmul_eq_mul, mul_div_cancel₀ _ (Nat.cast_ne_zero.2 hn), ht]
    rfl
  letI : DivisibleBy (Additive Circle) ℤ := AddGroup.divisibleByIntOfDivisibleByNat _
  obtain ⟨ρ, hρ⟩ := (Module.Baer.of_divisible (Additive Circle)).extension_property_addMonoidHom
    (MonoidHom.toAdditive (QuotientGroup.kerLift ψ0)) (QuotientGroup.kerLift_injective ψ0)
    (MonoidHom.toAdditive (QuotientGroup.lift ψ0.ker (lam.comp U.subtype) hker))
  let κ : G ⧸ V →* Circle := MonoidHom.toAdditive.symm ρ
  have hκ : ∀ x, κ (QuotientGroup.kerLift ψ0 x) = QuotientGroup.lift ψ0.ker (lam.comp U.subtype) hker x :=
    fun x => DFunLike.congr_fun hρ (Additive.ofMul x)
  refine ⟨κ.comp (QuotientGroup.mk' V), fun z hz => ?_, fun x hx => hκ ((⟨x, hx⟩ : U) : U ⧸ ψ0.ker)⟩
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff z).2 hz, map_one]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (F E) in

def fI : AF F ⊗[F] E := algebraMap (AF F) (AF F ⊗[F] E) (uFin F)

theorem uFin_mul (t : AF F) : uFin F * t = pairA F 0 t.2 := Prod.ext (zero_mul _) (one_mul _)

theorem fI_idem : fI F E * fI F E = fI F E := by
  rw [fI, ← map_mul, uFin_mul]; rfl

theorem fI_mem : fI F E ∈ SE F E :=
  AddSubgroup.subset_closure ⟨uFin F, ⟨1, fun _ => one_mem _, by rw [one_smul]; rfl⟩, 1, by simp [fI]⟩

theorem inf_j (a : AF F) : infPartF F E (algebraMap (AF F) (AF F ⊗[F] E) a) = a.1 ⊗ₜ[F] (1 : E) := rfl

theorem fin_j (a : AF F) : finPartF F E (algebraMap (AF F) (AF F ⊗[F] E) a) = a.2 ⊗ₜ[F] (1 : E) := rfl

theorem fin_fI : finPartF F E (fI F E) = 1 := rfl

theorem small (T : Set (AF F ⊗[F] E)) (hT : T ∈ 𝓝 0) : ∃ N : ℕ, 0 < N ∧ ∀ s ∈ SE F E, N • (fI F E * s) ∈ T := by
  classical
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := IsModuleTopology.toContinuousSMul (AF F) (AF F ⊗[F] E)
  let b := RingOfIntegers.basis E
  let P : Af F →+ AF F := AddMonoidHom.inr (Ainf F) (Af F)
  have hP : Continuous P := continuous_const.prodMk continuous_id
  let Φ : (Module.Free.ChooseBasisIndex ℤ (𝓞 E) → Af F) →+ AF F ⊗[F] E :=
    AddMonoidHom.mk' (fun c => ∑ i, P (c i) • incAF F E (b i)) fun c c' => by
      simp only [Pi.add_apply, map_add, add_smul, Finset.sum_add_distrib]
  have hΦ : ∀ c, Φ c = ∑ i, P (c i) • incAF F E (b i) := fun _ => rfl
  have hc : Continuous Φ := continuous_finset_sum _ fun i _ => by
    have h1 : Continuous fun a : AF F => a • incAF F E (b i) := by
      first
        | fun_prop
        | exact Continuous.smul (f := fun a : AF F => a) (g := fun _ => incAF F E (b i)) continuous_id continuous_const
        | exact IsModuleTopology.continuous_of_linearMap (LinearMap.toSpanSingleton (AF F) _ (incAF F E (b i)))
    exact h1.comp (hP.comp (continuous_apply i))
  have hrep : ∀ s ∈ SE F E, ∃ c : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → Af F,
      (∀ i v, c i v ∈ v.adicCompletionIntegers F) ∧ fI F E * s = Φ c := by
    intro s hs
    induction hs using AddSubgroup.closure_induction with
    | mem g hg =>
      obtain ⟨t, ⟨c0, h0, e0⟩, o, rfl⟩ := hg
      rw [one_smul] at e0
      refine ⟨fun i => b.repr o i • c0, fun i v => zsmul_mem (h0 v) _, ?_⟩
      have e1 : incAF F E o = ∑ i, b.repr o i • incAF F E (b i) := by
        have := congrArg ((incAF F E).comp (algebraMap (𝓞 E) E)) (b.sum_repr o).symm
        rw [map_sum] at this
        simp only [map_zsmul] at this
        exact this
      rw [hΦ, fI, ← mul_assoc, ← map_mul, uFin_mul, e0, e1, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_zsmul, smul_assoc, mul_smul_comm, Algebra.smul_def (P c0)]
      rfl
    | zero => exact ⟨0, fun _ _ => zero_mem _, by rw [mul_zero, map_zero]⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, h1, e1⟩ := hx
      obtain ⟨c', h2, e2⟩ := hy
      exact ⟨c + c', fun i v => add_mem (h1 i v) (h2 i v), by rw [mul_add, map_add, e1, e2]⟩
    | neg x _ hx =>
      obtain ⟨c, h1, e1⟩ := hx
      exact ⟨-c, fun i v => neg_mem (h1 i v), by rw [mul_neg, map_neg, e1]⟩
  have h1 : Φ ⁻¹' T ∈ 𝓝 0 := hc.continuousAt.preimage_mem_nhds (by rw [map_zero]; exact hT)
  rw [nhds_pi, Filter.mem_pi] at h1
  obtain ⟨I, -, W, hW, hsub⟩ := h1
  obtain ⟨N, hN, hNW⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F (⋂ i, W i) (Filter.iInter_mem.2 hW)
  refine ⟨N, hN, fun s hs => ?_⟩
  obtain ⟨c, h2, e⟩ := hrep s hs
  rw [e, ← map_nsmul]
  exact hsub fun i _ => Set.mem_iInter.1 (hNW _ (h2 i)) i

variable (F E) in

def GF : Subgroup (AF F ⊗[F] E)ˣ where
  carrier := {w | (1 - fI F E) * (w : AF F ⊗[F] E) = 1 - fI F E}
  one_mem' := mul_one _
  mul_mem' {x y} hx hy := by
    show (1 - fI F E) * ((x : AF F ⊗[F] E) * y) = _
    rw [← mul_assoc, hx, hy]
  inv_mem' {x} hx := by
    show (1 - fI F E) * ((x⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = _
    have hx' : (1 - fI F E) * (x : AF F ⊗[F] E) = 1 - fI F E := hx
    conv_lhs => rw [← hx']
    rw [mul_assoc, Units.mul_inv, mul_one]

theorem exists_level (η : (AF F ⊗[F] E)ˣ →* Circle) (hη : Continuous η) :
    ∃ N : ℕ, 0 < N ∧ ∀ w ∈ WE F E N, w ∈ GF F E → η w = 1 := by
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hV : {u | ‖((η u : Circle) : ℂ) - 1‖ < 1 / 2} ∈ 𝓝 (1 : (AF F ⊗[F] E)ˣ) := by
    refine (isOpen_lt (((continuous_subtype_val.comp hη).sub continuous_const).norm) continuous_const).mem_nhds ?_
    show ‖((η 1 : Circle) : ℂ) - 1‖ < 1 / 2
    simp
  rw [Units.isInducing_embedProduct.nhds_eq_comap, Filter.mem_comap] at hV
  obtain ⟨T, hT, hTV⟩ := hV
  obtain ⟨T1, hT1, T2, hT2, hTT⟩ := mem_nhds_prod_iff.1 hT
  have hf : Continuous fun b : AF F ⊗[F] E => 1 + b := by
    first
      | fun_prop
      | exact continuous_add_left 1
      | exact continuous_const_add 1
  have h1 : (fun b : AF F ⊗[F] E => 1 + b) ⁻¹' T1 ∈ 𝓝 0 :=
    hf.continuousAt.preimage_mem_nhds (by rw [add_zero]; exact hT1)
  have h2 : (fun b : AF F ⊗[F] E => MulOpposite.op (1 + b)) ⁻¹' T2 ∈ 𝓝 0 :=
    (MulOpposite.continuous_op.comp hf).continuousAt.preimage_mem_nhds
      (by rw [Function.comp_apply, add_zero]; exact hT2)
  obtain ⟨N, hN, hNW⟩ := small _ (Filter.inter_mem h1 h2)
  have key : ∀ z : AF F ⊗[F] E, z - 1 ∈ CE F E N → (1 - fI F E) * z = 1 - fI F E →
      z ∈ T1 ∧ MulOpposite.op z ∈ T2 := by
    intro z hz hz'
    obtain ⟨s, hs, e⟩ := mem_CE.1 hz
    have e2 : 1 + N • (fI F E * s) = z := by
      rw [← mul_smul_comm, e]
      linear_combination -hz'
    have := hNW s hs
    rw [← e2]
    exact this
  refine ⟨N, hN, fun w hw hg => Subtype.ext (GlobalTheory.CuspRep.eq_one_of_pow_near fun n => ?_)⟩
  have a1 := pow_mem hw n
  have a2 := pow_mem hg n
  have := hTV (a := w ^ n) (hTT ⟨(key _ a1.1 a2).1, (key _ a1.2 (inv_mem a2)).2⟩)
  simpa using this

theorem mem_SE_of_fin {z : AF F ⊗[F] E} (hz : finPartF F E z ∈ intAEF F E) : z ∈ SE F E := by
  have h1 : ∀ y ∈ intAEF F E, ∃ s ∈ SE F E, finPartF F E s = y := by
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem g hg =>
      obtain ⟨a, ha, x, rfl⟩ := hg
      refine ⟨_, AddSubgroup.subset_closure ⟨pairA F 0 a, ⟨a, ha, by rw [one_smul]; rfl⟩, x, rfl⟩, ?_⟩
      rw [map_mul, fin_j]
      show (a ⊗ₜ[F] (1 : E)) * ((1 : Af F) ⊗ₜ[F] (x : E)) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | zero => exact ⟨0, zero_mem _, map_zero _⟩
    | add x y _ _ hx hy =>
      obtain ⟨s, h1, rfl⟩ := hx
      obtain ⟨t, h2, rfl⟩ := hy
      exact ⟨s + t, add_mem h1 h2, map_add _ _ _⟩
    | neg x _ hx =>
      obtain ⟨s, h1, rfl⟩ := hx
      exact ⟨-s, neg_mem h1, map_neg _ _⟩
  obtain ⟨s, hs, e⟩ := h1 _ hz
  have h2 : At (evI F) (z - s) := by
    intro u hu
    have hu1 : u.1 = 0 := (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).1 hu
    rw [Algebra.smul_def]
    refine adele_tensor_ext _ ?_ ?_
    · rw [map_mul, inf_j, hu1, TensorProduct.zero_tmul, zero_mul]
    · rw [map_mul, map_sub, e, sub_self, mul_zero]
  obtain ⟨t, ht, e2⟩ := mem_CE.1 (mem_CE_of_atInf F E 1 one_pos _ h2)
  rw [one_smul] at e2
  rw [← sub_add_cancel z s, ← e2]
  exact add_mem ht hs

theorem mem_SE_of_CE {N : ℕ} {z : AF F ⊗[F] E} (h : z - 1 ∈ CE F E N) : z ∈ SE F E := by
  obtain ⟨s, hs, e⟩ := mem_CE.1 h
  rw [← sub_add_cancel z 1, ← e]
  exact add_mem (nsmul_mem hs N) one_mem_SE

theorem CE_one {z : AF F ⊗[F] E} (h : z ∈ SE F E) : z ∈ CE F E 1 := mem_CE.2 ⟨z, h, one_smul _ _⟩

theorem CE_mul {M N : ℕ} {z : AF F ⊗[F] E} (h : z ∈ CE F E (M * N)) : z ∈ CE F E M := by
  obtain ⟨s, hs, e⟩ := mem_CE.1 h
  exact mem_CE.2 ⟨N • s, nsmul_mem hs N, by rw [← e, smul_smul]⟩

open Classical in

def sing (v : HeightOneSpectrum (𝓞 F)) (x : Fv F v) : Af F :=
  ⟨Function.update (0 : ∀ w : HeightOneSpectrum (𝓞 F), Fv F w) v x, by
    filter_upwards [(Set.finite_singleton v).compl_mem_cofinite] with w hw
    rw [Function.update_of_ne hw]
    exact zero_mem _⟩

open Classical in
theorem sing_self (v : HeightOneSpectrum (𝓞 F)) (x : Fv F v) : evalV F v (sing v x) = x :=
  Function.update_self v x _

open Classical in
theorem sing_ne {v w : HeightOneSpectrum (𝓞 F)} (x : Fv F v) (h : w ≠ v) : evalV F w (sing v x) = 0 :=
  Function.update_of_ne h x _

theorem sing_mul (v : HeightOneSpectrum (𝓞 F)) (x y : Fv F v) : sing v x * sing v y = sing v (x * y) := by
  refine af_ext' F fun w => ?_
  by_cases h : w = v
  · subst h; rw [map_mul, sing_self, sing_self, sing_self]
  · rw [map_mul, sing_ne _ h, sing_ne (x * y) h, zero_mul]

def phi {v : HeightOneSpectrum (𝓞 F)} (τ : E →ₐ[F] Fv F v) : AF F ⊗[F] E →ₐ[F] Fv F v :=
  Algebra.TensorProduct.lift ((evalV F v).comp (sndA F)) τ fun _ _ => Commute.all _ _

theorem phi_j {v : HeightOneSpectrum (𝓞 F)} (τ : E →ₐ[F] Fv F v) (a : AF F) :
    phi τ (algebraMap (AF F) (AF F ⊗[F] E) a) = evalV F v a.2 := by
  show phi τ (a ⊗ₜ[F] (1 : E)) = _
  rw [phi, Algebra.TensorProduct.lift_tmul, map_one, mul_one]
  rfl

theorem phi_inc {v : HeightOneSpectrum (𝓞 F)} (τ : E →ₐ[F] Fv F v) (x : E) : phi τ (incAF F E x) = τ x := by
  show phi τ ((1 : AF F) ⊗ₜ[F] x) = _
  rw [phi, Algebra.TensorProduct.lift_tmul, map_one, one_mul]

theorem phi_mem {v : HeightOneSpectrum (𝓞 F)} (τ : E →ₐ[F] Fv F v) {z : AF F ⊗[F] E} (hz : z ∈ SE F E) :
    phi τ z ∈ v.adicCompletionIntegers F := by
  induction hz using AddSubgroup.closure_induction with
  | mem g hg =>
    obtain ⟨t, ⟨c0, h0, e0⟩, o, rfl⟩ := hg
    rw [one_smul] at e0
    rw [map_mul, phi_j, phi_inc, e0]
    refine mul_mem (h0 v) ?_
    have h2 : IsIntegral (v.adicCompletionIntegers F) (τ (o : E)) := by
      obtain ⟨p, hp, e⟩ := map_isIntegral_int τ o.2
      refine ⟨p.map (Int.castRingHom _), hp.map _, ?_⟩
      rw [Polynomial.eval₂_map]
      exact (congrArg (fun g => Polynomial.eval₂ g (τ (o : E)) p) (RingHom.ext_int _ _)).trans e
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
    rw [← hy]
    exact y.2
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

theorem exists_idem {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {v : HeightOneSpectrum (𝓞 F)} (τ : E →ₐ[F] Fv F v) :
    ∃ e, IsSplitIdemF σ e ∧ IsSplitIdemF σ (cAF σ e) ∧ cAF σ (cAF σ e) = e ∧ phi τ e = 1 := by
  obtain ⟨θ, d, hd0, hσθ, hθθ, -⟩ := exists_int_basis hcm
  have hs : τ θ * τ θ = algebraMap F (Fv F v) (d : F) := by rw [← map_mul, hθθ, AlgHom.commutes]
  have hcj : ∀ a, cAF σ (algebraMap (AF F) (AF F ⊗[F] E) a) = algebraMap (AF F) (AF F ⊗[F] E) a :=
    fun a => (cA σ).commutes a
  have hcδ : cAF σ (incAF F E θ) = -incAF F E θ := by
    rw [← map_neg, ← hσθ]; rfl
  have hδ2 : incAF F E θ * incAF F E θ = algebraMap (AF F) (AF F ⊗[F] E) (algebraMap F (AF F) (d : F)) := by
    rw [← map_mul, hθθ, incAF_algebraMap]
  have hd : (2 * (d : F)) ≠ 0 := mul_ne_zero two_ne_zero hd0
  have hH : algebraMap (AF F) (AF F ⊗[F] E) (algebraMap F (AF F) (2 * (d : F))⁻¹) *
      (2 * algebraMap (AF F) (AF F ⊗[F] E) (algebraMap F (AF F) (d : F))) = 1 := by
    have := congrArg ((algebraMap (AF F) (AF F ⊗[F] E)).comp (algebraMap F (AF F))) (inv_mul_cancel₀ hd)
    rw [map_mul, map_mul, map_ofNat, map_one] at this
    exact this
  have hII : algebraMap (AF F) (AF F ⊗[F] E) (pairA F 0 (sing v 1)) * algebraMap (AF F) (AF F ⊗[F] E) (pairA F 0 (sing v 1)) =
      algebraMap (AF F) (AF F ⊗[F] E) (pairA F 0 (sing v 1)) := by
    rw [← map_mul, pair_mul, sing_mul, one_mul]
  have hIS : algebraMap (AF F) (AF F ⊗[F] E) (pairA F 0 (sing v 1)) *
      algebraMap (AF F) (AF F ⊗[F] E) (pairA F 0 (sing v (τ θ))) =
      algebraMap (AF F) (AF F ⊗[F] E) (pairA F 0 (sing v (τ θ))) := by
    rw [← map_mul, pair_mul, sing_mul, one_mul]
  have hSS : algebraMap (AF F) (AF F ⊗[F] E) (pairA F 0 (sing v (τ θ))) *
      algebraMap (AF F) (AF F ⊗[F] E) (pairA F 0 (sing v (τ θ))) =
      algebraMap (AF F) (AF F ⊗[F] E) (pairA F 0 (sing v 1)) *
        algebraMap (AF F) (AF F ⊗[F] E) (algebraMap F (AF F) (d : F)) := by
    rw [← map_mul, ← map_mul, pair_mul, pair_mul', sing_mul, hs]
    congr 2
    refine af_ext' F fun w => ?_
    by_cases h : w = v
    · subst h; rw [map_mul, sing_self, sing_self, one_mul, evalV_snd_algebraMap]
    · rw [map_mul, sing_ne _ h, sing_ne (1 : Fv F v) h, zero_mul]
  have hpl : IsPlaceIdemF F v (pairA F 0 (sing v 1)) := ⟨_, rfl, sing_self v 1, fun w h => sing_ne _ h⟩
  have p1 : phi τ (algebraMap (AF F) (AF F ⊗[F] E) (pairA F 0 (sing v 1))) = 1 := (phi_j τ _).trans (sing_self v 1)
  have p2 : phi τ (algebraMap (AF F) (AF F ⊗[F] E) (pairA F 0 (sing v (τ θ)))) = τ θ :=
    (phi_j τ _).trans (sing_self v _)
  have p3 := congrArg (phi τ) hH
  have p4 := congrArg (phi τ) hδ2
  rw [map_mul, map_mul, map_ofNat, map_one] at p3
  rw [map_mul, phi_inc] at p4
  have c1 := hcj (pairA F 0 (sing v 1))
  have c2 := hcj (pairA F 0 (sing v (τ θ)))
  have c3 := hcj (algebraMap F (AF F) (d : F))
  have c4 := hcj (algebraMap F (AF F) (2 * (d : F))⁻¹)
  have p5 := phi_inc τ θ
  have hI0 : algebraMap (AF F) (AF F ⊗[F] E) (pairA F 0 (sing v 1)) =
    algebraMap (AF F) (AEF F E) (pairA F 0 (sing v 1)) := rfl
  generalize algebraMap (AF F) (AF F ⊗[F] E) (pairA F 0 (sing v (τ θ))) = S at *
  generalize algebraMap (AF F) (AF F ⊗[F] E) (algebraMap F (AF F) (d : F)) = D at *
  generalize algebraMap (AF F) (AF F ⊗[F] E) (algebraMap F (AF F) (2 * (d : F))⁻¹) = H at *
  generalize incAF F E θ = δ at *
  obtain ⟨I, hI⟩ : ∃ I, I = algebraMap (AF F) (AF F ⊗[F] E) (pairA F 0 (sing v 1)) := ⟨_, rfl⟩
  rw [← hI] at hII hIS hSS p1 c1
  obtain ⟨e, he⟩ : ∃ e, e = H * (I * D + S * δ) := ⟨_, rfl⟩
  have hce : cAF σ e = H * (I * D - S * δ) := by
    rw [he, map_mul, map_add, map_mul, map_mul, c1, c2, c3, c4, hcδ]; ring
  have hcc : cAF σ (cAF σ e) = e := by
    rw [hce, he, map_mul, map_sub, map_mul, map_mul, c1, c2, c3, c4, hcδ]; ring
  have h2 : e * cAF σ e = 0 := by
    rw [hce, he]
    linear_combination H * H * D * D * hII - H * H * δ * δ * hSS - H * H * I * D * hδ2
  have h3 : e + cAF σ e = I := by
    rw [hce, he]
    linear_combination I * hH
  have h4 : I * e = e := by
    rw [he]
    linear_combination H * D * hII + H * δ * hIS
  have h1 : e * e = e := by
    linear_combination e * h3 - h2 + h4
  refine ⟨e, ⟨h1, h2, v, _, hpl, h3.trans hI⟩,
    ⟨by rw [← map_mul, h1], by rw [hcc, mul_comm, h2], v, _, hpl, by rw [hcc, add_comm]; exact h3.trans hI⟩, hcc, ?_⟩
  rw [he, map_mul, map_add, map_mul, map_mul, p1, p2, p5]
  linear_combination p3 + phi τ H * p4

theorem exists_sep (v : HeightOneSpectrum (𝓞 F)) : ∃ N : ℕ, 0 < N ∧ ∀ y : F, IsIntegral ℤ y → (∀ φ : F →+* ℂ, ‖φ y‖ ≤ 8) →
    ∀ c ∈ v.adicCompletionIntegers F, algebraMap F (Fv F v) y = N • c → y = 0 := by
  have hfin := NumberField.Embeddings.finite_of_norm_le F ℂ 8
  have hc : Continuous fun b : Af F => evalV F v b := RestrictedProduct.continuous_eval v
  let Z : Set (Fv F v) := algebraMap F (Fv F v) '' ({y : F | IsIntegral ℤ y ∧ ∀ φ : F →+* ℂ, ‖φ y‖ ≤ 8} \ {0})
  have hZ : Z.Finite := (hfin.subset Set.diff_subset).image _
  have h0 : (fun b : Af F => evalV F v b) ⁻¹' Zᶜ ∈ 𝓝 (0 : Af F) := by
    refine (hZ.isClosed.isOpen_compl.preimage hc).mem_nhds ?_
    rintro ⟨y, hy, e⟩
    have e' : algebraMap F (Fv F v) y = 0 := e.trans (map_zero (evalV F v))
    exact hy.2 ((map_eq_zero _).1 e')
  obtain ⟨N, hN, hW⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F _ h0
  refine ⟨N, hN, fun y h1 h2 c hc' e => ?_⟩
  by_contra hy
  refine hW (sing v c) (fun w => ?_) ⟨y, ⟨⟨h1, h2⟩, hy⟩, ?_⟩
  · show evalV F w (sing v c) ∈ _
    by_cases h : w = v
    · subst h; rw [sing_self]; exact hc'
    · rw [sing_ne _ h]; exact zero_mem _
  · show _ = evalV F v (N • sing v c)
    rw [map_nsmul, sing_self, e]

theorem local_norm {σ : E →ₐ[F] E} {B : Base F E} (hB : B.IsGood σ) (v : HeightOneSpectrum (𝓞 F)) (u : (Fv F v)ˣ)
    (h1 : 2 * (u : Fv F v) ∈ v.adicCompletionIntegers F)
    (h2 : 2 * ((u⁻¹ : (Fv F v)ˣ) : Fv F v) ∈ v.adicCompletionIntegers F) :
    u ∈ GlobalTheory.QuadSymbol.normGroup F E (Fv F v) := by
  obtain ⟨δ, b, hδ, hb0, hb1, hbb⟩ :=
    GlobalTheory.QuadNormBase.exists_basis F E σ hB.cm.2.2.1 (sig_invol hB.cm) (sig_ne hB.cm)
  have hbb' : b 1 * b 1 = algebraMap F E δ := hbb
  refine (GlobalTheory.QuadSymbol.mem_normGroup_iff_form b hb0 hbb').2 ?_
  rcases GlobalTheory.T.place_split_or_inert F E σ B hB v with ⟨⟨τ⟩⟩ | ⟨w, hw⟩
  · have hs : τ (b 1) * τ (b 1) = algebraMap F (Fv F v) δ := by rw [← map_mul, hbb', AlgHom.commutes]
    have hs0 : τ (b 1) ≠ 0 := (map_ne_zero τ).2 (b.ne_zero 1)
    have h20 : (2 : Fv F v) ≠ 0 := by
      rw [← map_ofNat (algebraMap F (Fv F v)) 2]
      exact (map_ne_zero _).2 two_ne_zero
    refine ⟨((u : Fv F v) + 1) / 2, ((u : Fv F v) - 1) / (2 * τ (b 1)), ?_⟩
    rw [← hs]
    field_simp
    ring
  · have hv2 : Valued.v (2 : Fv F v) = 1 := by
      have e : (2 : Fv F v) = algebraMap F (Fv F v) (algebraMap (𝓞 F) F 2) := by rw [map_ofNat, map_ofNat]
      rw [e]
      refine (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _).trans ?_
      refine le_antisymm (v.valuation_le_one 2) (not_lt.1 fun h => (hB.inert v w hw).1 ?_)
      exact (v.valuation_lt_one_iff_mem 2).1 h
    have a1 : Valued.v (2 * (u : Fv F v)) ≤ 1 := h1
    have a2 : Valued.v (2 * ((u⁻¹ : (Fv F v)ˣ) : Fv F v)) ≤ 1 := h2
    rw [map_mul, hv2, one_mul] at a1 a2
    have hu : Valued.v (u : Fv F v) = 1 := by
      refine le_antisymm a1 ?_
      have hm := congrArg Valued.v u.mul_inv
      rw [map_mul, map_one] at hm
      rw [← hm]
      exact mul_le_of_le_one_right' a2
    obtain ⟨z, hz⟩ := GlobalTheory.InertUnitNorm.unit_eq_mul_conj F E σ B hB v w hw (GlobalTheory.T.isField_completion_tensor_of_isInertAt F E σ B hB v w hw) u hu
    obtain ⟨x, y, rfl⟩ := tensor_decomp (A := Fv F v) (b 1) (fun x => ⟨b.repr x 0, b.repr x 1, by
      have hx := b.sum_repr x
      rw [Fin.sum_univ_two, hb0] at hx
      exact hx.symm⟩) z
    refine ⟨x, y, tensor_inj (F := F) (E := E) ?_⟩
    have e1 : ((1 : Fv F v) ⊗ₜ[F] b 1) * ((1 : Fv F v) ⊗ₜ[F] b 1) =
        algebraMap (Fv F v) (Fv F v ⊗[F] E) (algebraMap F (Fv F v) δ) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, hbb', ← IsScalarTower.algebraMap_apply,
        Algebra.TensorProduct.algebraMap_apply']
    rw [hz, map_add, map_mul, AlgHom.commutes, AlgHom.commutes, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hb1,
      TensorProduct.tmul_neg, map_sub, map_mul, map_pow, map_pow, ← e1]
    ring

end PositivityTheory.ThKW.Eta

end
