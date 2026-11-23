import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsContent
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EventuallyMeasurableSetPrimV
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LatticeGramScalarAlmostAll
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteAlgebrasOverHenselianAndComplete
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperbolicPairUnitaryTransitiveStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitQuadraticOrderPrincipalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticOrderPrincipalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalOrderQuadraticAlmostAllStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypMass

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypMass.PrimDec

theorem hform_single {A : Type} [CommRing A] (τ : A →+* A) {N : ℕ} (H : Matrix (Fin N) (Fin N) A) (a b : Fin N) :
    hform τ H (Pi.single a 1) (Pi.single b 1) = H a b := by
  simp [hform, Pi.single_apply, Finset.sum_ite_eq]

theorem exists_content {T : Type} [CommRing T] [IsArtinianRing T] (O : Subring T) [IsPrincipalIdealRing O] {N : ℕ}
    (y : Fin N → T) (hy : ∀ k, y k ∈ O) (hfree : ∀ c : T, (∀ k, c * y k = 0) → c = 0) :
    ∃ x ∈ O, IsUnit x ∧ ∃ y₀ a : Fin N → T, (∀ k, y₀ k ∈ O) ∧ (∀ k, a k ∈ O) ∧ (∀ k, y k = x * y₀ k) ∧
      ∑ k, a k * y₀ k = 1 := by
  let yO : Fin N → O := fun k => ⟨y k, hy k⟩
  obtain ⟨x, hx⟩ := (IsPrincipalIdealRing.principal (Ideal.span (Set.range yO))).principal
  have hdiv : ∀ k, ∃ t : O, t * x = yO k := fun k => by
    have h : yO k ∈ Ideal.span (Set.range yO) := Ideal.subset_span ⟨k, rfl⟩
    rw [hx] at h
    exact Ideal.mem_span_singleton'.1 h
  choose t ht using hdiv
  have hxm : x ∈ Ideal.span (Set.range yO) := by
    rw [hx]; exact Ideal.mem_span_singleton_self x
  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.1 hxm
  have hyk : ∀ k, y k = (x : T) * (t k : T) := fun k => by
    have := congrArg Subtype.val (ht k)
    simp only [Subring.coe_mul, yO] at this
    rw [← this, mul_comm]
  have hnz : (x : T) ∈ nonZeroDivisors T := by
    rw [mem_nonZeroDivisors_iff_right]
    intro c hc
    exact hfree c fun k => by rw [hyk, ← mul_assoc, hc, zero_mul]
  have hu : IsUnit (x : T) := (IsArtinianRing.isUnit_iff_mem_nonZeroDivisors).2 hnz
  refine ⟨x, x.2, hu, fun k => t k, fun k => a k, fun k => (t k).2, fun k => (a k).2, hyk, ?_⟩
  have h1 : (x : T) * ∑ k, (a k : T) * (t k : T) = x * 1 := by
    have := congrArg Subtype.val ha
    simp only [Subring.coe_mul, AddSubmonoidClass.coe_finset_sum, yO] at this
    rw [mul_one, Finset.mul_sum]
    conv_rhs => rw [← this]
    exact Finset.sum_congr rfl fun k _ => by rw [hyk k]; ring
  exact hu.mul_left_cancel h1

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M d : ℕ}
  (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))

theorem exists_of_mem_primV (O : Subring (Fv F v ⊗[F] E))
    (hO : ∀ y, y ∈ O ↔ ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈ v.adicCompletionIntegers F)
    {y : Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E} (hy : y ∈ primV σ J b v) :
    (∀ i, y 0 i ∈ O) ∧ ∃ a : Fin (M + 2) → Fv F v ⊗[F] E, (∀ i, a i ∈ O) ∧ ∑ k, a k * y 0 k = 1 := by
  obtain ⟨g, hg, rfl⟩ := hy
  set G : GL (Fin (M + 2)) (Fv F v ⊗[F] E) := HA.mat (Fv F v) σ (hypOne J) g with hG
  have hact : ∀ (X : Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) (t : Fin 1),
      actW (Fv F v) σ (hypOne J) g X t = (G : Matrix _ _ _) *ᵥ X t := fun _ _ => rfl
  have hlat : ∀ X : Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E, X ∈ latV b v ↔ ∀ a i, X a i ∈ O :=
    fun X => GlobalTheory.CompanionTheory.SW.GoodTrans.mem_latV_iff b v O hO X
  have he : (e0 (Fv F v ⊗[F] E) M) ∈ latV b v := by
    rw [hlat]
    intro a i
    induction i using Fin.cases with
    | zero => exact O.one_mem
    | succ i => exact O.zero_mem
  have hy := (hg _).2 he
  rw [hlat] at hy
  let Gi : Matrix (Fin (M + 2)) (Fin (M + 2)) (Fv F v ⊗[F] E) := ((G⁻¹ : GL (Fin (M + 2)) (Fv F v ⊗[F] E)) : Matrix (Fin (M + 2)) (Fin (M + 2)) (Fv F v ⊗[F] E))
  refine ⟨hy 0, fun k => Gi 0 k, fun k => ?_, ?_⟩
  · let x : Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E :=
      fun _ => Gi *ᵥ Pi.single k 1
    have hgx : actW (Fv F v) σ (hypOne J) g x ∈ latV b v := by
      rw [hlat]
      intro a i
      rw [hact]
      simp only [x]
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
      by_cases h : i = k
      · subst h; simpa using O.one_mem
      · simpa [Pi.single_apply, h] using O.zero_mem
    have hx := (hg x).1 hgx
    rw [hlat] at hx
    have := hx 0 0
    simpa [x, Matrix.mulVec_single_one] using this
  · have h0 : Gi *ᵥ ((G : Matrix (Fin (M + 2)) (Fin (M + 2)) (Fv F v ⊗[F] E)) *ᵥ e0 (Fv F v ⊗[F] E) M 0) =
        e0 (Fv F v ⊗[F] E) M 0 := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    have h1 := congrFun h0 0
    rw [← hact] at h1
    simpa [Matrix.mulVec, dotProduct, e0] using h1

theorem mem_primV_of (O : Subring (Fv F v ⊗[F] E))
    (hO : ∀ y, y ∈ O ↔ ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈ v.adicCompletionIntegers F)
    (hstab : ∀ y ∈ O, sigR (Fv F v) σ y ∈ O) (hss : ∀ z, sigR (Fv F v) σ (sigR (Fv F v) σ z) = z)
    (h2 : IsUnit (2 : O))
    (hgood : ∀ s β : O, IsUnit β → sigR (Fv F v) σ β = β → ∃ ε z : O,
      (ε : Fv F v ⊗[F] E) * sigR (Fv F v) σ ε = 1 ∧ ((β : Fv F v ⊗[F] E) - sigR (Fv F v) σ ε * s) * z = 1)
    (Hi : Matrix (Fin (M + 2)) (Fin (M + 2)) (Fv F v ⊗[F] E))
    (hHO : ∀ i j, JR (Fv F v) (hypOne J) i j ∈ O) (hHiO : ∀ i j, Hi i j ∈ O)
    (hmul : JR (Fv F v) (hypOne J) * Hi = 1)
    (hJ : ∀ i j, sigR (Fv F v) σ (JR (Fv F v) (hypOne J) j i) = JR (Fv F v) (hypOne J) i j)
    (y : Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) (hy : ∀ i, y 0 i ∈ O)
    (a : Fin (M + 2) → Fv F v ⊗[F] E) (ha : ∀ i, a i ∈ O) (hsum : ∑ k, a k * y 0 k = 1)
    (hiso : hform (sigR (Fv F v) σ) (JR (Fv F v) (hypOne J)) (y 0) (y 0) = 0) : y ∈ primV σ J b v := by
  set s := sigR (Fv F v) σ with hs
  set H : Matrix (Fin (M + 2)) (Fin (M + 2)) (Fv F v ⊗[F] E) := JR (Fv F v) (hypOne J) with hH
  let τ : O →+* O := s.restrict O O hstab
  have hτ : ∀ a : O, ((τ a : O) : Fv F v ⊗[F] E) = s a := fun a => rfl
  let HO : Matrix (Fin (M + 2)) (Fin (M + 2)) O := fun i j => ⟨H i j, hHO i j⟩
  let HiO : Matrix (Fin (M + 2)) (Fin (M + 2)) O := fun i j => ⟨Hi i j, hHiO i j⟩
  let y0 : Fin (M + 2) → O := fun i => ⟨y 0 i, hy i⟩
  let a0 : Fin (M + 2) → O := fun i => ⟨a i, ha i⟩
  have hcoe : ∀ p q : Fin (M + 2) → O, ((hform τ HO p q : O) : Fv F v ⊗[F] E) =
      hform s H (fun i => (p i : Fv F v ⊗[F] E)) (fun i => (q i : Fv F v ⊗[F] E)) := by
    intro p q
    simp [hform, hτ, HO]
  have hval : ∀ g : GL (Fin (M + 2)) O, ((bc O.subtype g : GL (Fin (M + 2)) (Fv F v ⊗[F] E)) :
      Matrix (Fin (M + 2)) (Fin (M + 2)) (Fv F v ⊗[F] E)) =
      (g : Matrix (Fin (M + 2)) (Fin (M + 2)) O).map O.subtype := fun g => rfl
  have hmulO : HO * HiO = 1 := by
    refine Matrix.ext fun i j => Subtype.ext ?_
    have := congrFun (congrFun hmul i) j
    rw [Matrix.mul_apply] at this
    rw [Matrix.mul_apply, AddSubmonoidClass.coe_finset_sum]
    simp only [Subring.coe_mul, HO, HiO]
    rw [this]
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  obtain ⟨g0, hg0, hgx⟩ := GlobalTheory.T.hyperbolic_pair_unitary_transitive O τ (fun z => Subtype.ext (hss z)) h2
    (fun p β hβ hf => by
      obtain ⟨ε, z, h1, h3⟩ := hgood p β hβ (congrArg Subtype.val hf)
      exact ⟨ε, z, Subtype.ext h1, Subtype.ext h3⟩)
    (M + 2) HO HiO hmulO (fun i j => Subtype.ext (hJ i j)) (Pi.single 0 1) (Pi.single 1 1) y0 a0
    (by rw [hform_single]; exact Subtype.ext (by simp [HO, H, JR, hypOne_zero_zero]))
    (by rw [hform_single]; exact Subtype.ext (by simp [HO, H, JR, hypOne_one_one]))
    (by rw [hform_single]; exact Subtype.ext (by simp [HO, H, JR, hypOne_zero_one]))
    (Subtype.ext (by rw [hcoe]; exact hiso))
    (Subtype.ext (by simpa [a0, y0] using hsum))
  have hmem : bc O.subtype g0 ∈ HR (Fv F v) σ (hypOne J) := by
    have h0 : cT τ (g0 : Matrix (Fin (M + 2)) (Fin (M + 2)) O) * HO *
        (g0 : Matrix (Fin (M + 2)) (Fin (M + 2)) O) = HO := hg0
    have h1 := congrArg (RingHom.mapMatrix O.subtype) h0
    rw [map_mul, map_mul] at h1
    show cT s ((bc O.subtype g0 : GL (Fin (M + 2)) (Fv F v ⊗[F] E)) :
      Matrix (Fin (M + 2)) (Fin (M + 2)) (Fv F v ⊗[F] E)) * H *
      ((bc O.subtype g0 : GL (Fin (M + 2)) (Fv F v ⊗[F] E)) :
        Matrix (Fin (M + 2)) (Fin (M + 2)) (Fv F v ⊗[F] E)) = H
    exact h1
  let h' : HA (Fv F v) σ (hypOne J) := (⟨bc O.subtype g0, hmem⟩ : HR (Fv F v) σ (hypOne J))
  have hact : ∀ (X : Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) (t : Fin 1),
      actW (Fv F v) σ (hypOne J) h' X t = ((bc O.subtype g0 : GL (Fin (M + 2)) (Fv F v ⊗[F] E)) :
        Matrix (Fin (M + 2)) (Fin (M + 2)) (Fv F v ⊗[F] E)) *ᵥ X t := fun _ _ => rfl
  refine ⟨h', fun X => ?_, ?_⟩
  · rw [GlobalTheory.CompanionTheory.SW.GoodTrans.mem_latV_iff b v O hO, GlobalTheory.CompanionTheory.SW.GoodTrans.mem_latV_iff b v O hO]
    constructor
    · intro hX t i
      have e : X t = ((bc O.subtype g0⁻¹ : GL (Fin (M + 2)) (Fv F v ⊗[F] E)) :
          Matrix (Fin (M + 2)) (Fin (M + 2)) (Fv F v ⊗[F] E)) *ᵥ
          (((bc O.subtype g0 : GL (Fin (M + 2)) (Fv F v ⊗[F] E)) :
          Matrix (Fin (M + 2)) (Fin (M + 2)) (Fv F v ⊗[F] E)) *ᵥ X t) := by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
          Matrix.one_mulVec]
      rw [e]
      refine GlobalTheory.CompanionTheory.SW.GoodTrans.mulVec_mem O _ (fun p q => ?_) _ (fun j => ?_) i
      · rw [hval]
        exact ((g0⁻¹ : GL (Fin (M + 2)) O) : Matrix (Fin (M + 2)) (Fin (M + 2)) O) p q |>.2
      · rw [← hact]; exact hX t j
    · intro hX t i
      rw [hact]
      refine GlobalTheory.CompanionTheory.SW.GoodTrans.mulVec_mem O _ (fun p q => ?_) _ (hX t) i
      rw [hval]
      exact ((g0 : Matrix (Fin (M + 2)) (Fin (M + 2)) O) p q).2
  · funext t
    rw [Fin.fin_one_eq_zero t, hact, hval]
    funext i
    have h1 := congrArg Subtype.val (congrFun hgx i)
    have he : e0 (Fv F v ⊗[F] E) M 0 = fun j => ((Pi.single 0 1 : Fin (M + 2) → O) j : Fv F v ⊗[F] E) := by
      funext j
      induction j using Fin.cases with
      | zero => simp [e0]
      | succ j => simp [e0, Pi.single_apply, Fin.succ_ne_zero]
    rw [he]
    simpa [Matrix.mulVec, dotProduct, y0] using h1

end Loc

theorem eventually_primV_decomposition : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ (ι : Type) (c : ι → Fv F v ⊗[F] E) (w : ι → ℕ), IsContent σ b v c w → MeasurableSet (primV σ J b v) ∧ (∀ i, ∀ y ∈ primV σ J b v, scalT (c i) y ∈ latV b v) ∧ (∀ i j, ∀ y ∈ primV σ J b v, ∀ y' ∈ primV σ J b v, scalT (c i) y = scalT (c j) y' → i = j) ∧ (∀ y : Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E, LinearIndependent (Fv F v ⊗[F] E) y → gramR (Fv F v) σ (hypOne J) y = 0 → y ∈ latV b v → ∃ i, ∃ y₀ ∈ primV σ J b v, y = scalT (c i) y₀) := by
  intro F E _ _ _ _ _ σ hσ M J hJ d b
  have hND := PrimMeas.isHermND_hypOne σ J hJ
  have hinv : ∀ x, σ (σ x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hσ.2.2.2, hσ.2.2.2, star_star]
  have I := GlobalTheory.CompanionTheory.SW.GoodInt.rational_integral_units F E σ hσ d b
  filter_upwards [PrimMeas.eventually_measurableSet_primV F E σ hσ M J hJ d b,
    GlobalTheory.CompanionTheory.SW.GoodRing.good_ring F E σ hσ d b, GlobalTheory.T.local_order_quadratic_almost_all F E σ hσ d b,
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => I.1 (hypOne J i j),
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => I.1 ((hypOne J)⁻¹ i j)]
    with v hmeas hring hquad hH hHi
  obtain ⟨O, hO, hstab, -, h2, -, hgood, -⟩ := hring
  intro ι c w hc
  obtain ⟨hc1, -, -, hc4, hc5⟩ := hc
  have hss : ∀ z : Fv F v ⊗[F] E, sigR (Fv F v) σ (sigR (Fv F v) σ z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e =>
      show a ⊗ₜ[F] σ (σ e) = a ⊗ₜ[F] e
      rw [hinv]
    | add p q hp hq => rw [map_add, map_add, hp, hq]
  have hint : ∀ x, x ∈ intK b v ↔ x ∈ O := fun x => (hO x).symm
  set Hi : Matrix (Fin (M + 2)) (Fin (M + 2)) (Fv F v ⊗[F] E) := JR (Fv F v) (hypOne J)⁻¹ with hHidef
  have hHO : ∀ i j, JR (Fv F v) (hypOne J) i j ∈ O := fun i j => (hO _).2 (hH i j)
  have hHiO : ∀ i j, Hi i j ∈ O := fun i j => (hO _).2 (hHi i j)
  have hmul : JR (Fv F v) (hypOne J) * Hi = 1 := by
    have h1 : hypOne J * (hypOne J)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hND.2)
    have h3 := congrArg (RingHom.mapMatrix (inclR (F := F) (E := E) (Fv F v))) h1
    rw [map_mul, map_one] at h3
    exact h3
  have hJR : ∀ i j, sigR (Fv F v) σ (JR (Fv F v) (hypOne J) j i) = JR (Fv F v) (hypOne J) i j := by
    intro i j
    show sigR (Fv F v) σ (inclR (Fv F v) (hypOne J j i)) = inclR (Fv F v) (hypOne J i j)
    rw [← hND.1 i j]
    rfl
  have hprim := fun y hy a ha hsum hiso => mem_primV_of σ J b v O hO hstab hss h2 hgood Hi hHO hHiO hmul hJR y hy a ha hsum hiso
  have hex := fun {y} (hy : y ∈ primV σ J b v) => exists_of_mem_primV σ J b v O hO hy
  have hlat : ∀ X : Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E, X ∈ latV b v ↔ ∀ a i, X a i ∈ O :=
    fun X => GlobalTheory.CompanionTheory.SW.GoodTrans.mem_latV_iff b v O hO X
  have hpir : IsPrincipalIdealRing O := by
    obtain ⟨ι', δ, D, h1, h3, h4, h5, h6⟩ := hquad O hO
    haveI := GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v
    haveI : HenselianLocalRing (v.adicCompletionIntegers F) := GlobalTheory.henselianLocalRing_of_isAdicComplete _
    by_cases hsq : ∃ e, D = e * e
    · obtain ⟨e, rfl⟩ := hsq
      exact GlobalTheory.T.split_quadratic_order_principal _ O ι' δ e h1 h3 h4 (isUnit_of_mul_isUnit_left h5) h6
    · exact GlobalTheory.T.unramified_quadratic_order_principal _ O ι' δ D h1 h3 h4 h5 h6 hsq
  haveI : Module.Finite (Fv F v) (Fv F v ⊗[F] E) := by
    haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
    infer_instance
  haveI : IsArtinianRing (Fv F v ⊗[F] E) := IsArtinianRing.of_finite (Fv F v) _
  refine ⟨hmeas, fun i y hy => ?_, fun i j y hy y' hy' he => ?_, fun y hli hg hy => ?_⟩
  · have h1 := (hex hy).1
    rw [hlat]
    intro a k
    rw [Fin.fin_one_eq_zero a]
    exact O.mul_mem ((hint _).1 (hc1 i).2) (h1 k)
  · obtain ⟨h1, a, ha, hs⟩ := hex hy
    obtain ⟨h1', a', ha', hs'⟩ := hex hy'
    have hek : ∀ k, c i * y 0 k = c j * y' 0 k := fun k => congrFun (congrFun he 0) k
    set u := ∑ k, a k * y' 0 k with hu
    set u' := ∑ k, a' k * y 0 k with hu'
    have huO : u ∈ O := O.sum_mem fun k _ => O.mul_mem (ha k) (h1' k)
    have hu'O : u' ∈ O := O.sum_mem fun k _ => O.mul_mem (ha' k) (h1 k)
    have e1 : c i = c j * u := by
      calc c i = c i * ∑ k, a k * y 0 k := by rw [hs, mul_one]
        _ = c j * u := by
          rw [hu, Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by linear_combination (a k) * hek k
    have e2 : c j = c i * u' := by
      calc c j = c j * ∑ k, a' k * y' 0 k := by rw [hs', mul_one]
        _ = c i * u' := by
          rw [hu', Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by linear_combination -(a' k) * hek k
    have huu : u * u' = 1 := by
      have : c i * (u * u') = c i * 1 := by
        calc c i * (u * u') = (c i * u') * u := by ring
          _ = c i * 1 := by rw [← e2, ← e1, mul_one]
      exact (hc1 i).1.mul_left_cancel this
    exact hc5 i j u ((hint _).2 huO) u' ((hint _).2 hu'O) huu e1
  · rw [hlat] at hy
    have hfree : ∀ t : Fv F v ⊗[F] E, (∀ k, t * y 0 k = 0) → t = 0 := by
      intro t ht
      have h1 := Fintype.linearIndependent_iff.1 hli (fun _ => t) (by
        funext k
        simpa [Fin.sum_univ_succ] using ht k)
      exact h1 0
    obtain ⟨x, hxO, hxu, y₀, a, hy₀, ha, hyx, hs⟩ := exists_content O (y 0) (hy 0) hfree
    obtain ⟨i, u, huO, u', hu'O, huu, hxc⟩ := hc4 x ((hint _).2 hxO) hxu
    rw [hint] at huO hu'O
    refine ⟨i, fun _ k => u * y₀ k, hprim _ (fun k => O.mul_mem huO (hy₀ k)) (fun k => u' * a k)
      (fun k => O.mul_mem hu'O (ha k)) ?_ ?_, ?_⟩
    · calc ∑ k, u' * a k * (u * y₀ k) = (u * u') * ∑ k, a k * y₀ k := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
        _ = 1 := by rw [huu, hs, one_mul]
    · have h0 : hform (sigR (Fv F v) σ) (JR (Fv F v) (hypOne J)) (y 0) (y 0) = 0 := congrFun (congrFun hg 0) 0
      have hsc : ∀ (t : Fv F v ⊗[F] E) (p : Fin (M + 2) → Fv F v ⊗[F] E),
          hform (sigR (Fv F v) σ) (JR (Fv F v) (hypOne J)) (fun k => t * p k) (fun k => t * p k) =
            sigR (Fv F v) σ t * t * hform (sigR (Fv F v) σ) (JR (Fv F v) (hypOne J)) p p := by
        intro t p
        simp only [hform, Finset.mul_sum, map_mul]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      have hyy : y 0 = fun k => x * y₀ k := funext hyx
      rw [hyy, hsc] at h0
      have hxs : IsUnit (sigR (Fv F v) σ x * x) := (hxu.map (sigR (Fv F v) σ)).mul hxu
      have h00 := hxs.mul_right_eq_zero.1 h0
      show hform _ _ (fun k => u * y₀ k) (fun k => u * y₀ k) = 0
      rw [hsc, h00, mul_zero]
    · funext t k
      rw [Fin.fin_one_eq_zero t]
      show y 0 k = c i * (u * y₀ k)
      rw [hyx k, hxc]; ring

end GlobalTheory.CompanionTheory.WeilSiegel.HypMass.PrimDec
