import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInfiniteDecomp
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix Topology

noncomputable section
namespace GlobalTheory.SqCls

theorem finite_units_quot_sq_field {k : Type} [NontriviallyNormedField k] [CompleteSpace k] [ProperSpace k]
    (h2 : (2 : k) ≠ 0) (K : Type) [Field K] [Algebra k K] [FiniteDimensional k K] :
    Finite (Kˣ ⧸ (powMonoidHom 2 : Kˣ →* Kˣ).range) := by
  classical
  set S := (powMonoidHom 2 : Kˣ →* Kˣ).range with hS
  let V := Fin (Module.finrank k K) → k
  let e : K ≃ₗ[k] V := (Module.finBasis k K).equivFun
  let B : V →ₗ[k] V →ₗ[k] V :=
    ((LinearMap.mul k K).compl₁₂ (e.symm : V →ₗ[k] K) (e.symm : V →ₗ[k] K)).compr₂ (e : K →ₗ[k] V)
  have hB : ∀ a b, B a b = e (e.symm a * e.symm b) := fun a b => rfl
  have hsq := eventually_exists_sq_normed h2 B (e := e 1) (fun v => by simp [hB]) (fun v => by simp [hB])
  have key : ∀ y : Kˣ, ∀ᶠ a in 𝓝 (e y), ∀ g : Kˣ, e g = a → y⁻¹ * g ∈ S := by
    intro y
    let f : V →ₗ[k] V := B (e (y⁻¹ : Kˣ))
    have hf : Continuous f := f.continuous_of_finiteDimensional
    have hfy : f (e y) = e 1 := by simp [f, hB]
    have := (hf.tendsto (e y)).eventually (hfy ▸ hsq)
    filter_upwards [this] with a ⟨z, hz⟩ g hg
    have h1 : ((y⁻¹ : Kˣ) : K) * g = e.symm z * e.symm z := by
      apply e.injective
      rw [← hB, hz, ← hg]
      simp [f, hB]
    have hz0 : e.symm z ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at h1
      exact (mul_ne_zero (Units.ne_zero _) (Units.ne_zero g)) h1
    refine ⟨Units.mk0 _ hz0, ?_⟩
    ext
    simp only [powMonoidHom_apply, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0]
    rw [sq, ← h1]
  obtain ⟨c, hc0, hc1⟩ := NormedField.exists_norm_lt_one k
  set q : ℝ := ‖c‖ ^ 2 with hq
  have hq0 : 0 < q := by positivity
  have hq1 : q < 1 := by rw [hq]; nlinarith
  set C : Set V := Metric.closedBall 0 1 ∩ {b | q ≤ ‖b‖} with hC
  have hCc : IsCompact C := (isCompact_closedBall 0 1).inter_right (isClosed_le continuous_const continuous_norm)
  have hCne : ∀ b ∈ C, e.symm b ≠ 0 := by
    intro b hb h0
    have : b = 0 := by simpa using congrArg e h0
    have := hb.2
    simp_all
  let y : V → Kˣ := fun b => if h : e.symm b ≠ 0 then Units.mk0 _ h else 1
  have hy : ∀ b ∈ C, e (y b) = b := fun b hb => by
    simp only [y, dif_pos (hCne b hb), Units.val_mk0, LinearEquiv.apply_symm_apply]
  let U : V → Set V := fun b => {a | ∀ g : Kˣ, e g = a → (y b)⁻¹ * g ∈ S}
  have hU : ∀ b ∈ C, U b ∈ 𝓝 b := fun b hb => by
    have := key (y b)
    rw [hy b hb] at this
    exact this
  obtain ⟨t, htC, hcov⟩ := hCc.elim_nhds_subcover U hU
  refine Finite.of_surjective (fun b : t => (QuotientGroup.mk (y b.1) : Kˣ ⧸ S)) ?_
  intro x
  induction x using QuotientGroup.induction_on with
  | H g =>
  have ha : 0 < ‖e g‖ := norm_pos_iff.2 (fun h => Units.ne_zero g (e.injective (h.trans (map_zero e).symm)))
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ioc_zpow ha (one_lt_inv_iff₀.2 ⟨hq0, hq1⟩)
  let u : kˣ := Units.mk0 c (norm_pos_iff.1 hc0) ^ (n + 1)
  let w : Kˣ := Units.map (algebraMap k K : k →* K) u
  have hnorm : ‖e (w ^ 2 * g : Kˣ)‖ = q ^ (n + 1) * ‖e g‖ := by
    have : ((w ^ 2 * g : Kˣ) : K) = ((u : k) ^ 2) • (g : K) := by
      simp [w, Algebra.smul_def]
    rw [this, map_smul, norm_smul, norm_pow]
    congr 1
    simp only [u, Units.val_zpow_eq_zpow_val, Units.val_mk0, norm_zpow, hq]
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
  have hmem : e (w ^ 2 * g : Kˣ) ∈ C := by
    refine ⟨?_, ?_⟩
    · rw [mem_closedBall_zero_iff, hnorm]
      have := mul_le_mul_of_nonneg_left hn2 (zpow_nonneg hq0.le (n + 1))
      rwa [inv_zpow', ← zpow_add₀ hq0.ne', add_neg_cancel, zpow_zero] at this
    · show q ≤ ‖e (w ^ 2 * g : Kˣ)‖
      rw [hnorm]
      have := mul_lt_mul_of_pos_left hn1 (zpow_pos hq0 (n + 1))
      rw [inv_zpow', ← zpow_add₀ hq0.ne', show n + 1 + -n = 1 by ring, zpow_one] at this
      exact this.le
  obtain ⟨b, hbt, hb⟩ := Set.mem_iUnion₂.1 (hcov hmem)
  refine ⟨⟨b, hbt⟩, ?_⟩
  have h3 := hb (w ^ 2 * g) rfl
  have h4 : w ^ 2 ∈ S := ⟨w, rfl⟩
  refine QuotientGroup.eq.2 ?_
  have := S.mul_mem h3 (S.inv_mem h4)
  rw [mul_comm (w ^ 2) g] at this
  convert this using 1
  group

end GlobalTheory.SqCls

namespace GlobalTheory.SqCls

theorem finite_units_quot_sq_of_reduced {k : Type} [Field k]
    (hK : ∀ (K : Type) [Field K] [Algebra k K] [FiniteDimensional k K], Finite (Kˣ ⧸ (powMonoidHom 2 : Kˣ →* Kˣ).range))
    (R : Type) [CommRing R] [Algebra k R] [FiniteDimensional k R] [IsReduced R] :
    Finite (Rˣ ⧸ (powMonoidHom 2 : Rˣ →* Rˣ).range) := by
  classical
  haveI : IsArtinianRing R := IsArtinianRing.of_finite k R
  haveI hmax : ∀ I : MaximalSpectrum R, I.asIdeal.IsMaximal := fun I => I.isMaximal
  letI : ∀ I : MaximalSpectrum R, Field (R ⧸ I.asIdeal) := fun I => Ideal.Quotient.field _
  haveI : ∀ I : MaximalSpectrum R, FiniteDimensional k (R ⧸ I.asIdeal) := fun I =>
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ k I.asIdeal).toLinearMap (Ideal.Quotient.mkₐ_surjective k _)
  haveI : Finite (MaximalSpectrum R) := inferInstance
  haveI : ∀ I : MaximalSpectrum R, Finite ((R ⧸ I.asIdeal)ˣ ⧸ (powMonoidHom 2 : (R ⧸ I.asIdeal)ˣ →* _).range) :=
    fun I => hK _
  let φ : Rˣ →* ∀ I : MaximalSpectrum R, (R ⧸ I.asIdeal)ˣ ⧸ (powMonoidHom 2 : (R ⧸ I.asIdeal)ˣ →* _).range :=
    Pi.monoidHom fun I => (QuotientGroup.mk' _).comp (Units.map (Ideal.Quotient.mk I.asIdeal : R →* R ⧸ I.asIdeal))
  have hker : φ.ker ≤ (powMonoidHom 2 : Rˣ →* Rˣ).range := by
    intro u hu
    have h1 : ∀ I : MaximalSpectrum R, ∃ w : (R ⧸ I.asIdeal)ˣ, w ^ 2 = Units.map (Ideal.Quotient.mk I.asIdeal : R →* _) u :=
      fun I => by
        have h' : (QuotientGroup.mk (Units.map (Ideal.Quotient.mk I.asIdeal : R →* R ⧸ I.asIdeal) u) :
            (R ⧸ I.asIdeal)ˣ ⧸ (powMonoidHom 2 : (R ⧸ I.asIdeal)ˣ →* _).range) = 1 :=
          congrFun ((MonoidHom.mem_ker).1 hu) I
        rw [QuotientGroup.eq_one_iff] at h'
        obtain ⟨w, hw⟩ := h'
        exact ⟨w, hw⟩
    choose w hw using h1
    let e := IsArtinianRing.equivPi R
    have he : ∀ x I, e x I = Ideal.Quotient.mk I.asIdeal x := fun x I => rfl
    let z : R := e.symm fun I => (w I : R ⧸ I.asIdeal)
    let z' : R := e.symm fun I => ((w I)⁻¹ : (R ⧸ I.asIdeal)ˣ)
    have hzz : z * z' = 1 := e.injective (funext fun I => by simp [z, z', map_mul])
    refine ⟨⟨z, z', hzz, by rw [mul_comm, hzz]⟩, ?_⟩
    ext
    apply e.injective
    funext I
    have := congrArg Units.val (hw I)
    simp only [Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_coe] at this
    have hz : Ideal.Quotient.mk I.asIdeal z = w I := by rw [← he, e.apply_symm_apply]
    simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val]
    rw [he, he, map_pow, hz, this]
  haveI : Finite (Rˣ ⧸ φ.ker) := Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange φ).toEquiv.symm
  exact Finite.of_surjective (QuotientGroup.map _ _ (MonoidHom.id _) hker) (by
    intro q
    induction q using QuotientGroup.induction_on with
    | H g => exact ⟨QuotientGroup.mk g, rfl⟩)

end GlobalTheory.SqCls

namespace GlobalTheory.SqCls

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ}

def fixSub (P : PPol σ r) (k : Type) [CommRing k] [Algebra F k] : Subalgebra k (k ⊗[F] Fld P) where
  carrier := {a | sigR k (star' P) a = a}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at *
    rw [map_mul, ha, hb]
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at *
    rw [map_add, ha, hb]
  algebraMap_mem' t := by
    simp [sigR, Algebra.TensorProduct.algebraMap_apply]

theorem finite_cls_of_fixSub (P : PPol σ r) (k : Type) [CommRing k] [Algebra F k]
    (h : Finite ((fixSub P k)ˣ ⧸ (powMonoidHom 2 : (fixSub P k)ˣ →* (fixSub P k)ˣ).range)) : Finite (Cls P k) := by
  classical
  have hfix : ∀ x : plusUnits P k, sigR k (star' P) (x.1 : k ⊗[F] Fld P) = x.1 := fun x =>
    congrArg Units.val x.2
  let φ : (fixSub P k)ˣ →* plusUnits P k :=
    { toFun := fun u => ⟨Units.map (fixSub P k).val.toMonoidHom u, Units.ext u.1.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp }
  have hφ : Function.Surjective φ := by
    intro x
    have h1 := hfix x
    have h2 := hfix x⁻¹
    refine ⟨⟨⟨x.1.1, h1⟩, ⟨(x⁻¹ : plusUnits P k).1.1, h2⟩, Subtype.ext ?_, Subtype.ext ?_⟩, ?_⟩
    · simp
    · simp
    · ext; rfl
  let ψ : (fixSub P k)ˣ →* Cls P k := (QuotientGroup.mk' _).comp φ
  have hψ : Function.Surjective ψ := (QuotientGroup.mk'_surjective _).comp hφ
  have hsq : (powMonoidHom 2 : (fixSub P k)ˣ →* (fixSub P k)ˣ).range ≤ ψ.ker := by
    rintro _ ⟨u, rfl⟩
    rw [MonoidHom.mem_ker]
    show (QuotientGroup.mk (φ (u ^ 2)) : plusUnits P k ⧸ (norms P k).subgroupOf (plusUnits P k)) = 1
    rw [QuotientGroup.eq_one_iff, map_pow, Subgroup.mem_subgroupOf]
    refine ⟨(φ u).1, ?_⟩
    ext
    simp only [MonoidHom.mul_apply, MonoidHom.id_apply, Units.val_mul, Units.coe_map, MonoidHom.coe_coe,
      RingHom.toMonoidHom_eq_coe, Subgroup.coe_pow, Units.val_pow_eq_pow_val]
    rw [hfix (φ u), sq]
  exact Finite.of_surjective (QuotientGroup.lift _ ψ hsq) (by
    intro q
    obtain ⟨u, rfl⟩ := hψ q
    exact ⟨QuotientGroup.mk u, rfl⟩)

end GlobalTheory.SqCls

namespace GlobalTheory.SqCls

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ}

theorem finite_cls_of_normed [NumberField F] [NumberField E] (P : PPol σ r) (k : Type) [NontriviallyNormedField k]
    [CompleteSpace k] [ProperSpace k] [Algebra F k] (hred : IsReduced (k ⊗[F] Fld P)) : Finite (Cls P k) := by
  have h2 : (2 : k) ≠ 0 := by
    have := (algebraMap F k).injective.ne (two_ne_zero (α := F))
    rwa [map_ofNat, map_zero] at this
  haveI : Module.Finite F (Fld P) := Module.Finite.of_restrictScalars_finite ℚ F (Fld P)
  haveI : IsReduced (fixSub P k) := isReduced_of_injective (fixSub P k).val Subtype.val_injective
  exact finite_cls_of_fixSub P k
    (finite_units_quot_sq_of_reduced (k := k) (by intro K _ _ _; exact finite_units_quot_sq_field h2 K) (fixSub P k))

theorem finite_cls : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r), (∀ v : HeightOneSpectrum (𝓞 F), Finite (Cls P (Fv F v))) ∧ ∀ w : InfinitePlace F, Finite (Cls P w.Completion) := by
  intro F E _ _ _ _ _ σ _ r P
  constructor
  · intro v
    obtain ⟨ψ, -, hb, -⟩ := GlobalTheory.TraceClasses.exists_finite_decomp F (Fld P)
    letI : NontriviallyNormedField (v.adicCompletion F) := Valued.toNontriviallyNormedField _ _
    haveI := GlobalTheory.LocalData.isLocalField v
    haveI : ProperSpace (v.adicCompletion F) :=
      ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace (v.adicCompletion F)
    exact finite_cls_of_normed P (v.adicCompletion F) (isReduced_of_injective (Pi.ringHom (ψ v)) (hb v).1)
  · intro w
    obtain ⟨χ, -, hb⟩ := GlobalTheory.TraceClasses.exists_infinite_decomp F (Fld P)
    letI : NontriviallyNormedField w.Completion :=
      { (inferInstance : NormedField w.Completion) with
        non_trivial := ⟨2, by
          rw [← (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _),
            map_ofNat]
          simp⟩ }
    haveI : ProperSpace w.Completion :=
      ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace w.Completion
    exact finite_cls_of_normed P w.Completion (isReduced_of_injective (Pi.ringHom (χ w)) (hb w).1)

end GlobalTheory.SqCls
