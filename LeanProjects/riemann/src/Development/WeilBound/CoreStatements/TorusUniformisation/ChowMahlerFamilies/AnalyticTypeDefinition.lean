import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformisedEigenFrameOne
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.KahlerFormsOverSubalgebraClosureProperties
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FamilyUnifExpUnique
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieMultIffExistsFrame

section
open NumberField Matrix
open scoped TensorProduct

namespace PositivityTheory.Xgn.AnalyticTypeDefinition

theorem exists_matrix {E : Type} [Field E] [NumberField E] {La : Type} [AddCommGroup La] [Module (𝓞 E) La]
    [Module.Finite (𝓞 E) La] [Module.Projective (𝓞 E) La] {I : Type} [Fintype I] [DecidableEq I] (e : I → La)
    (he : LinearIndependent (𝓞 E) e) (hc : Fintype.card I = Module.finrank (𝓞 E) La) (gam : La →ₗ[𝓞 E] La) :
    ∃ A : Matrix I I E, A.det = LinearMap.det (gam.baseChange E) ∧
      ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (τ : E →+* ℂ) (φ : La →+ M),
        (∀ (a : 𝓞 E) x, φ (a • x) = τ (a : E) • φ x) → ∀ m, φ (gam (e m)) = ∑ n, τ (A m n) • φ (e n) := by
  let j : La →ₗ[𝓞 E] E ⊗[𝓞 E] La := TensorProduct.mk (𝓞 E) E La 1
  haveI : IsLocalizedModule (nonZeroDivisors (𝓞 E)) j :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors (𝓞 E)) E j).2 (TensorProduct.isBaseChange _ _ _)
  have hli : LinearIndependent E (j ∘ e) := he.of_isLocalizedModule E (nonZeroDivisors (𝓞 E)) j
  have hr : Fintype.card I = Module.finrank E (E ⊗[𝓞 E] La) := by
    rw [hc]
    exact ((TensorProduct.isBaseChange (𝓞 E) La E).finrank_eq).symm
  haveI : FiniteDimensional E (E ⊗[𝓞 E] La) := inferInstance
  let b : Module.Basis I E (E ⊗[𝓞 E] La) := basisOfLinearIndependentOfCardEqFinrank' _ hli hr
  have hb : ∀ n, b n = j (e n) := fun n => by simp [b]
  refine ⟨(LinearMap.toMatrix b b (gam.baseChange E))ᵀ, by rw [det_transpose, LinearMap.det_toMatrix], ?_⟩
  intro M _ _ τ φ hφ m
  have h1 : j (gam (e m)) = ∑ n, (LinearMap.toMatrix b b (gam.baseChange E)) n m • j (e n) := by
    have := (b.sum_repr (gam.baseChange E (b m))).symm
    simp only [LinearMap.toMatrix_apply, ← hb]
    rw [← this, hb]
    rfl
  obtain ⟨N, hN⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 E))
    (fun n => (LinearMap.toMatrix b b (gam.baseChange E)) n m)
  choose a ha using hN
  have h2 : j ((N : 𝓞 E) • gam (e m)) = j (∑ n, a n • e n) := by
    rw [map_smul, h1, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [map_smul, ← smul_assoc, ← ha n, algebraMap_smul]
  obtain ⟨s, hs⟩ := IsLocalizedModule.exists_of_eq (S := nonZeroDivisors (𝓞 E)) (f := j) h2
  have h3 := congrArg φ hs
  simp only [Submonoid.smul_def, hφ, map_sum] at h3
  have hs0 : τ ((s : 𝓞 E) : E) ≠ 0 := by
    simpa using nonZeroDivisors.ne_zero s.2
  have hN0 : τ ((N : 𝓞 E) : E) ≠ 0 := by
    simpa using nonZeroDivisors.ne_zero N.2
  have h4 := smul_right_injective M hs0 h3
  apply smul_right_injective M hN0
  simp only []
  rw [h4, Finset.smul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [smul_smul, ← map_mul, transpose_apply]
  congr 2
  exact (ha n).trans (Algebra.smul_def _ _)

theorem change_basis {p q g : ℕ} (T T' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (V : Fin p → Fin g → ℂ)
    (W : Fin q → Fin g → ℂ) (πe πf : Fin p ⊕ Fin q → Fin g → ℂ)
    (Se Sf A A' : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (hA : A.det = 1) (hA' : A'.det = 1)
    (h1 : ∀ m, T (πf m) = ∑ n, A m n • T (πe n)) (h2 : ∀ m, T' (πf m) = ∑ n, A' m n • T' (πe n))
    (hS : Sf = A * Se * A'ᵀ) (C : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ) (Fm B : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ)
    (hC : ∀ a, T (∑ m, C a m • πf m) = V a) (hB : ∀ n, T' (πf n) = ∑ j, B j n • W j)
    (hF : ∀ j n, ∑ m, Fm j m * Sf m n = B j n) :
    ∃ (C' : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ) (Fm' B' : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ),
      (∀ a, T (∑ m, C' a m • πe m) = V a) ∧ (∀ n, T' (πe n) = ∑ j, B' j n • W j) ∧
      (∀ j n, ∑ m, Fm' j m * Se m n = B' j n) ∧ (Matrix.fromRows C' Fm').det = (Matrix.fromRows C Fm).det := by
  have hu : IsUnit A'.det := by rw [hA']; exact isUnit_one
  have hu' : IsUnit A'ᵀ.det := by rw [det_transpose]; exact hu
  refine ⟨C * A, Fm * A, B * A'ᵀ⁻¹, fun a => ?_, fun n => ?_, fun j n => ?_, ?_⟩
  · rw [← hC a]
    simp only [map_sum, map_smul, h1, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
    exact Finset.sum_comm
  · have e1 : (Matrix.of fun m k => T' (πf m) k) = A' * Matrix.of fun m k => T' (πe m) k := by
      ext m k; simp [h2, Matrix.mul_apply, Finset.sum_apply]
    have e2 : (Matrix.of fun m k => T' (πf m) k) = Bᵀ * Matrix.of W := by
      ext m k; simp [hB, Matrix.mul_apply, Finset.sum_apply]
    have e3 : (Matrix.of fun m k => T' (πe m) k) = (B * A'ᵀ⁻¹)ᵀ * Matrix.of W := by
      rw [transpose_mul, ← transpose_nonsing_inv, transpose_transpose, Matrix.mul_assoc, ← e2, e1,
        ← Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.one_mul]
    funext k
    have := congrFun (congrFun e3 n) k
    rw [Matrix.mul_apply] at this
    simpa [Finset.sum_apply] using this
  · have e1 : Fm * Sf = B := by ext j n; exact hF j n
    have e2 : Fm * A * Se = B * A'ᵀ⁻¹ := by
      rw [← e1, hS, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hu', Matrix.mul_one]
    exact congrFun (congrFun e2 j) n
  · rw [← fromRows_mul, det_mul, hA, mul_one]

theorem entry_zero {E : Type} [Field E] [NumberField E] {g : ℕ} (ty : Fin g → (E →+* ℂ))
    (h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hh : ∀ (a : 𝓞 E) z, h (fun k => ty k (a : E) * z k) = fun k => ty k (a : E) * h z k) (j k : Fin g)
    (hjk : ty j ≠ ty k) : h (Pi.single k 1) j = 0 := by
  by_contra h0
  apply hjk
  refine IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun a => ?_)
  have e1 : (fun i => ty i (a : E) * (Pi.single k (1 : ℂ) : Fin g → ℂ) i) = ty k (a : E) • Pi.single k (1 : ℂ) := by
    funext i
    by_cases hi : i = k
    · subst hi; simp
    · simp [hi]
  have := congrFun (hh a (Pi.single k 1)) j
  rw [e1, map_smul] at this
  exact (mul_right_cancel₀ h0 this).symm

end PositivityTheory.Xgn.AnalyticTypeDefinition
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace PositivityTheory.Xgn.AnalyticTypeDefinition

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

noncomputable def tyLin {g : ℕ} (ty : Fin g → (E →+* ℂ)) (τ : E →+* ℂ) : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) where
  toFun := tyPart ty τ
  map_add' a b := by funext k; simp only [tyPart, Pi.add_apply]; split_ifs <;> simp
  map_smul' a b := by funext k; simp only [tyPart, Pi.smul_apply]; split_ifs <;> simp

theorem tyPart_comm {g : ℕ} (ty : Fin g → (E →+* ℂ)) (h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hh : ∀ (a : 𝓞 E) z, h (fun k => ty k (a : E) * z k) = fun k => ty k (a : E) * h z k) (τ : E →+* ℂ)
    (z : Fin g → ℂ) : tyPart ty τ (h z) = h (tyPart ty τ z) := by
  have : tyLin ty τ ∘ₗ h = h ∘ₗ tyLin ty τ := by
    refine LinearMap.pi_ext' fun k => LinearMap.ext_ring ?_
    show tyPart ty τ (h (Pi.single k 1)) = h (tyPart ty τ (Pi.single k 1))
    by_cases hk : ty k = τ
    · have e1 : tyPart ty τ (Pi.single k (1 : ℂ)) = Pi.single k 1 := by
        funext i
        simp only [tyPart]
        split_ifs with hi
        · rfl
        · rw [Pi.single_eq_of_ne]; rintro rfl; exact hi hk
      rw [e1]
      funext j
      simp only [tyPart]
      split_ifs with hj
      · rfl
      · exact (entry_zero ty h hh j k (by rw [hk]; exact hj)).symm
    · have e1 : tyPart ty τ (Pi.single k (1 : ℂ)) = 0 := by
        funext i
        simp only [tyPart]
        split_ifs with hi
        · rw [Pi.single_eq_of_ne]; · rfl
          rintro rfl; exact hk hi
        · rfl
      rw [e1, map_zero]
      funext j
      simp only [tyPart]
      split_ifs with hj
      · exact entry_zero ty h hh j k (by rw [hj]; exact fun h' => hk h'.symm)
      · rfl
  exact LinearMap.congr_fun this z

theorem comm_of_period (D₁ D₂ : Datum H) {g : ℕ} (ty : Fin g → (E →+* ℂ)) (P : D₁.La →+ (Fin g → ℂ))
    (P' : D₂.La →+ (Fin g → ℂ)) (hP : IsPeriod D₁ ty P) (hP' : IsPeriod D₂ ty P')
    (h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (gam : D₁.La →ₗ[𝓞 E] D₂.La) (hgam : ∀ a, P' (gam a) = h (P a))
    (a : 𝓞 E) (z : Fin g → ℂ) : h (fun k => ty k (a : E) * z k) = fun k => ty k (a : E) * h z k := by
  let d : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) := LinearMap.pi fun k => ty k (a : E) • LinearMap.proj k
  have : (h ∘ₗ d).restrictScalars ℝ = (d ∘ₗ h).restrictScalars ℝ := by
    refine LinearMap.ext_on_range hP.2.2.2.1 fun x => ?_
    show h (d (P x)) = d (h (P x))
    have e1 : d (P x) = P (a • x) := funext fun i => (hP.1 a x i).symm
    have e2 : d (P' (gam x)) = P' (a • gam x) := funext fun i => (hP'.1 a _ i).symm
    rw [e1, ← hgam, ← hgam, e2, map_smul]
  exact LinearMap.congr_fun this z

theorem deriv_transport {g : ℕ} {X : Scheme.{0}} (e e' : (Fin g → ℂ) → (Sp ℂ ⟶ X))
    (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (he : ∀ z, e' (h z) = e z) (w : Fin g → ℂ) (v : Sp (DualNumber ℂ) ⟶ X)
    (hv : IsDerivAt0 e w v) : IsDerivAt0 e' (h w) v := by
  refine ⟨by rw [hv.1, ← he, map_zero], fun U hU f => ?_⟩
  rw [hv.2 U hU f]
  have e1 : (fun z => valAt' (e z) U f) = (fun z => valAt' (e' z) U f) ∘ h.toContinuousLinearEquiv := by
    funext z; simp [he]
  rw [e1, ContinuousLinearEquiv.comp_right_fderiv]
  simp

theorem tyPart_smul (D : Datum H) {g : ℕ} (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty P)
    (τ : E →+* ℂ) (a : 𝓞 E) (x : D.La) : tyPart ty τ (P (a • x)) = τ (a : E) • tyPart ty τ (P x) := by
  funext k
  simp only [tyPart, Pi.smul_apply, hP.1]
  split_ifs with hk
  · rw [hk]; rfl
  · simp

noncomputable def sesqL (D : Datum H) (τ : E →+* ℂ) (y : D.La) : D.La →+ ℂ :=
  AddMonoidHom.mk' (fun x => τ (sesq D x y)) fun x x' => by
    simp [sesq, Finset.sum_add_distrib, add_mul]

noncomputable def sesqR (D : Datum H) (τ : E →+* ℂ) (x : D.La) : D.La →+ ℂ :=
  AddMonoidHom.mk' (fun y => τ (sesq D x y)) fun y y' => by
    simp [sesq, Finset.sum_add_distrib, add_mul]

def Cond (D : Datum H) {g p q : ℕ} (ty : Fin g → (E →+* ℂ)) (τ' : E →+* ℂ) (e : Fin p ⊕ Fin q → D.La)
    (P : D.La →+ (Fin g → ℂ)) (V : Fin p → Fin g → ℂ) (W : Fin q → Fin g → ℂ)
    (C : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ) (Fm B : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ) : Prop :=
  (∀ a, tyPart ty τ' (∑ m, C a m • P (e m)) = V a) ∧
    (∀ n, tyPart ty (ComplexEmbedding.conjugate τ') (P (e n)) = ∑ j, B j n • W j) ∧
    (∀ j n, ∑ m, Fm j m * τ' (sesq D (e m) (e n)) = B j n)

theorem cond_transport (D : Datum H) {g p q : ℕ} (ty : Fin g → (E →+* ℂ)) (τ' : E →+* ℂ) (e : Fin p ⊕ Fin q → D.La)
    (he : LinearIndependent (𝓞 E) e) (hc : p + q = D.p + D.q)
    (P P' : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty P) (hP' : IsPeriod D ty P')
    (h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (gam : D.La →ₗ[𝓞 E] D.La) (hgam : ∀ a, P' (gam a) = h (P a))
    (hiso : ∀ a b, D.EF (gam a) (gam b) = D.EF a b) (hdet : LinearMap.det (gam.baseChange E) = 1)
    (V : Fin p → Fin g → ℂ) (W : Fin q → Fin g → ℂ)
    (C : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ) (Fm B : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ)
    (hC : Cond D ty τ' e P V W C Fm B) :
    ∃ C' Fm' B', Cond D ty τ' e P' (fun a => h (V a)) (fun j => h (W j)) C' Fm' B' ∧
      (Matrix.fromRows C' Fm').det = (Matrix.fromRows C Fm).det := by
  haveI := D.fin
  haveI := D.proj
  obtain ⟨A, hA, hφ⟩ := exists_matrix e he (by rw [D.rank, ← hc]; simp) gam
  rw [hdet] at hA
  have hcomm := tyPart_comm ty h (comm_of_period D D ty P P' hP hP' h gam hgam)
  have hT : ∀ (τ : E →+* ℂ) m, tyLin ty τ (P' (gam (e m))) = ∑ n, (A.map τ) m n • tyLin ty τ (P' (e n)) := fun τ m =>
    hφ _ τ ((tyLin ty τ).toAddMonoidHom.comp P') (tyPart_smul D ty P' hP' τ) m
  have hd : ∀ τ : E →+* ℂ, (A.map τ).det = 1 := fun τ => by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hA, map_one]
  have hs : ∀ x y, sesq D (gam x) (gam y) = sesq D x y := fun x y => by
    simp only [sesq, ← map_smul, hiso]
  have hL : ∀ y m, τ' (sesq D (gam (e m)) y) = ∑ n, τ' (A m n) • τ' (sesq D (e n) y) := fun y m =>
    hφ _ τ' (sesqL D τ' y) (fun a x => by
      show τ' (sesq D (a • x) y) = τ' a * τ' (sesq D x y)
      rw [GlobalTheory.CompanionTheory.Ar.Fl.Test.sesq_smul_left, map_mul]) m
  have hR : ∀ x m, τ' (sesq D x (gam (e m))) =
      ∑ n, ComplexEmbedding.conjugate τ' (A m n) • τ' (sesq D x (e n)) := fun x m =>
    hφ _ (ComplexEmbedding.conjugate τ') (sesqR D τ' x) (fun a y => by
      show τ' (sesq D x (a • y)) = ComplexEmbedding.conjugate τ' a * τ' (sesq D x y)
      obtain ⟨b, rfl⟩ := H.bar.surjective a
      rw [GlobalTheory.CompanionTheory.Ar.Fl.Test.sesq_smul_right, map_mul, H.bar_eq]
      congr 1
      show _ = starRingEnd ℂ (τ' _)
      rw [IsCMField.complexEmbedding_complexConj, Complex.conj_conj]) m
  obtain ⟨C', Fm', B', k1, k2, k3, k4⟩ := change_basis (tyLin ty τ') (tyLin ty (ComplexEmbedding.conjugate τ'))
    (fun a => h (V a)) (fun j => h (W j)) (fun m => P' (e m)) (fun m => P' (gam (e m)))
    (Matrix.of fun m n => τ' (sesq D (e m) (e n))) (Matrix.of fun m n => τ' (sesq D (e m) (e n)))
    (A.map τ') (A.map (ComplexEmbedding.conjugate τ')) (hd _) (hd _) (hT _) (hT _)
    (by
      ext m n
      rw [Matrix.of_apply, ← hs, hR, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hL, Matrix.mul_apply, smul_eq_mul, mul_comm]
      rfl) C Fm B
    (fun a => by
      show tyPart ty τ' _ = _
      rw [← hC.1 a, ← hcomm]
      simp only [hgam, map_sum, map_smul])
    (fun n => by
      show tyPart ty _ _ = _
      rw [hgam, hcomm, hC.2.1]
      simp only [map_sum, map_smul])
    hC.2.2
  exact ⟨C', Fm', B', ⟨k1, k2, k3⟩, k4⟩

theorem solve (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (τ τ' : E →+* ℂ) (σ : c.F →+* ℂ) (g : ℕ)
    (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty)
    (hty : IsTypeFn H D.p D.q ty) (hrt : τ' (H.rt : E) = H.rt0) (hτ : ∀ a : 𝓞 E, σ (tauIn c τ a) = τ' (a : E))
    (i : Fin FU.n) (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (P : (FU.Di i).La →+ (Fin g → ℂ))
    (y : Sp ℂ ⟶ Xo.XF c) (v : Vecs y D.p) (w : Vecs y D.q) (he : LinearIndependent (𝓞 E) e)
    (hP : IsPeriod (FU.Di i) ty P) (hy : under y = FU.u i P) (hfr : IsFramed Set.univ τ σ y v w) :
    ∃ d : ℂ, d ≠ 0 ∧ ∀ V W C Fm B, (∀ a, IsDerivAt0 (fun z => (FU.ex i P z).left) (V a) (v a).left) →
      (∀ j, IsDerivAt0 (fun z => (FU.ex i P z).left) (W j) (w j).left) →
      Cond (FU.Di i) ty τ' e P V W C Fm B → (Matrix.fromRows C Fm).det = d := by
  obtain ⟨⟨V₀, W₀, F₀, B₀, d⟩, ⟨k1, k2, k3, k4, k5, -, k7⟩, -⟩ :=
    anSolve E H D l Xo c τ τ' σ g ty FU hty hrt hτ i e P y v w he hP hy hfr
  obtain ⟨-, -, hv, hw⟩ := hfr
  have hc : ∀ a : 𝓞 E, (σ.comp (tauIn c (ComplexEmbedding.conjugate τ))) a = ComplexEmbedding.conjugate τ' (a : E) := by
    intro a
    have h1 : tauIn c (ComplexEmbedding.conjugate τ) a = tauIn c τ (H.bar a) := by
      apply Subtype.ext
      show ComplexEmbedding.conjugate τ (a : E) = τ ((H.bar a : 𝓞 E) : E)
      rw [H.bar_eq, IsCMField.complexEmbedding_complexConj]
      rfl
    show σ (tauIn c (ComplexEmbedding.conjugate τ) a) = _
    rw [h1, hτ, H.bar_eq, IsCMField.complexEmbedding_complexConj]
    rfl
  obtain ⟨V₁, hVd, -, -⟩ := GlobalTheory.T.period_eigen_frame E H D l Xo _ g ty FU i P (under y) (σ.comp (tauIn c τ)) τ' D.p v hP hy hτ hv
  obtain ⟨W₁, hWd, hWl, -⟩ :=
    GlobalTheory.T.period_eigen_frame E H D l Xo _ g ty FU i P (under y) _ (ComplexEmbedding.conjugate τ') D.q w hP hy hc hw
  obtain ⟨Hm, hHh, -, hHi⟩ := id hP.2.2.2.2
  obtain ⟨-, -, hd⟩ := GlobalTheory.T.period_hermitian_type_compatibility E H (FU.Di i) g ty P Hm hP hHh hHi
  have hcard : Fintype.card (Fin D.p ⊕ Fin D.q) = (FU.Di i).p + (FU.Di i).q := by
    rw [(FU.sig i).1, (FU.sig i).2]; simp
  have hS : (Matrix.of fun m n => τ' (sesq (FU.Di i) (e m) (e n))).det ≠ 0 := by
    have := hd 0 _ e hcard he
    have h2 : (Matrix.of fun m n => τ' (sesq (FU.Di i) (e m) (e n))) =
      (Matrix.of fun m n => sesq (FU.Di i) (e m) (e n)).map τ' := rfl
    rw [h2, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero τ').2 this
  refine ⟨d, k5, fun V W C Fm B a1 a2 a3 => ?_⟩
  have eV : V = V₀ := funext fun a => ((hVd a _).1 (a1 a)).trans ((hVd a _).1 (k1 a)).symm
  have eW : W = W₁ := funext fun a => (hWd a _).1 (a2 a)
  have eW₀ : W₀ = W₁ := funext fun a => (hWd a _).1 (k2 a)
  subst eV eW eW₀
  have eB : B = B₀ := by
    ext j n
    exact (Fintype.linearIndependent_iffₛ.1 hWl) (fun j => B j n) (fun j => B₀ j n) ((a3.2.1 n).symm.trans (k3 n)) j
  have eF : Fm = F₀ := by
    have e1 : Fm * (Matrix.of fun m n => τ' (sesq (FU.Di i) (e m) (e n))) =
        F₀ * (Matrix.of fun m n => τ' (sesq (FU.Di i) (e m) (e n))) := by
      ext j n
      exact ((a3.2.2 j n).trans (congrFun (congrFun eB j) n)).trans (k4 j n).symm
    have := congrArg (· * (Matrix.of fun m n => τ' (sesq (FU.Di i) (e m) (e n)))⁻¹) e1
    simpa only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (Ne.isUnit hS), Matrix.mul_one] using this
  rw [eF]
  exact k7 C a3.1

theorem level_of_marking {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} (U : FamilyUnif Xo σ ty) (i : Fin U.n) (gam : (U.Di i).La ≃ₗ[𝓞 E] (U.Di i).La)
    (hgam : ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∃ e, gam (U.t i a) = U.t i a + l.M • e) :
    ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (U.Di i).La), ∃ e, gam a = a + l.M • e := by
  intro a ha
  refine Submodule.smul_induction_on ha (fun r hr b _ => ?_) ?_
  · obtain ⟨a', e', rfl⟩ := U.t_surj i b
    obtain ⟨e, he⟩ := hgam (r • a') (Submodule.smul_mem_smul hr Submodule.mem_top)
    obtain ⟨k, hk⟩ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
    refine ⟨e + k • r • (gam e' - e'), ?_⟩
    rw [smul_add, ← map_smul, map_add, he, hk, smul_comm r, map_nsmul, map_smul gam, mul_smul, mul_smul, smul_add,
      smul_sub, smul_sub, smul_sub]
    abel
  · rintro x y ⟨e, he⟩ ⟨e', he'⟩
    exact ⟨e + e', by rw [map_add, he, he', smul_add]; abel⟩

end PositivityTheory.Xgn.AnalyticTypeDefinition

theorem PositivityTheory.Xgn.analytic_type_definition : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (τ τ' : E →+* ℂ) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty), IsTypeFn H D.p D.q ty → τ' (H.rt : E) = H.rt0 → (∀ a : 𝓞 E, σ (tauIn c τ a) = τ' (a : E)) → ∀ (e : ∀ i : Fin FU.n, Fin D.p ⊕ Fin D.q → (FU.Di i).La) (ρ : Fin FU.n → ℂ), (∀ i, LinearIndependent (𝓞 E) (e i)) → ∃ Φ : CFn Xo c, ∀ i, IsFlatAn Set.univ τ τ' σ Φ FU i (e i) (ρ i) := by
  intro E _ _ _ H D l Xo c τ τ' σ g ty FU hty hrt hτ e ρ he
  have key : ∀ (y : Sp ℂ ⟶ Xo.XF c) (v : Vecs y D.p) (w : Vecs y D.q), ∃ φ : ℂ, ∀ i P V W C Fm B,
      IsPeriod (FU.Di i) ty P → under y = FU.u i P → IsFramed Set.univ τ σ y v w →
      (∀ a, IsDerivAt0 (fun z => (FU.ex i P z).left) (V a) (v a).left) →
      (∀ j, IsDerivAt0 (fun z => (FU.ex i P z).left) (W j) (w j).left) →
      PositivityTheory.Xgn.AnalyticTypeDefinition.Cond (FU.Di i) ty τ' (e i) P V W C Fm B → φ * (Matrix.fromRows C Fm).det = ρ i := by
    intro y v w
    by_cases hex : ∃ i P, IsPeriod (FU.Di i) ty P ∧ under y = FU.u i P ∧ IsFramed Set.univ τ σ y v w
    · obtain ⟨i₀, P₀, hP₀, hy₀, hfr⟩ := hex
      obtain ⟨d, hd0, hd⟩ := PositivityTheory.Xgn.AnalyticTypeDefinition.solve D l Xo c τ τ' σ g ty FU hty hrt hτ i₀ (e i₀) P₀ y v w
        (he i₀) hP₀ hy₀ hfr
      refine ⟨ρ i₀ / d, fun i P V W C Fm B hP hy _ a1 a2 a3 => ?_⟩
      obtain rfl : i = i₀ := FU.disj i i₀ P P₀ hP hP₀ (hy.symm.trans hy₀)
      obtain ⟨h, gam, b1, b2, b3, b4, -⟩ :=
        GlobalTheory.familyUnif_exp_unique E H D l Xo _ g ty FU i i P P₀ hP hP₀ (hy.symm.trans hy₀)
      have hdet := per_det_one E H (FU.Di i) l gam b3 (PositivityTheory.Xgn.AnalyticTypeDefinition.level_of_marking FU i gam b4)
      obtain ⟨C', Fm', B', k1, k2⟩ := PositivityTheory.Xgn.AnalyticTypeDefinition.cond_transport (FU.Di i) ty τ' (e i) (he i)
        (by rw [(FU.sig i).1, (FU.sig i).2]) P P₀ hP hP₀ h.toLinearMap gam.toLinearMap b2 b3 hdet V W C Fm B a3
      rw [← k2, hd _ _ C' Fm' B'
        (fun a => PositivityTheory.Xgn.AnalyticTypeDefinition.deriv_transport _ _ h b1 _ _ (a1 a))
        (fun j => PositivityTheory.Xgn.AnalyticTypeDefinition.deriv_transport _ _ h b1 _ _ (a2 j)) k1]
      exact div_mul_cancel₀ _ hd0
    · exact ⟨0, fun i P V W C Fm B hP hy hfr _ _ _ => absurd ⟨i, P, hP, hy, hfr⟩ hex⟩
  choose Φ hΦ using key
  exact ⟨Φ, fun i P y v w V W C Fm B h1 h2 h3 h4 h5 h6 h7 h8 => hΦ y v w i P V W C Fm B h1 h2 h3 h4 h5 ⟨h6, h7, h8⟩⟩
