import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsGlIsometryCompEqOfNondegenerate
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsIntegralValIntegerIff

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HermTuple

open Matrix Module

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
open Matrix Module in
private theorem exists_inv_pair_mul_eq_of_mul_eq {K n m : Type*} [Field K] [Fintype n]
    [DecidableEq n] [Fintype m] [DecidableEq m] (X Y : Matrix n m K) (A A' : Matrix m n K)
    (hM : IsUnit (A * X).det) (h : A' * Y = A * X) :
    ∃ T T' : Matrix n n K, T * T' = 1 ∧ T' * T = 1 ∧ T * X = Y ∧ A' * T = A := by
  obtain ⟨N, hN1, hN2⟩ : ∃ N : Matrix m m K, A * X * N = 1 ∧ N * (A * X) = 1 :=
    ⟨(A * X)⁻¹, Matrix.mul_nonsing_inv _ hM, Matrix.nonsing_inv_mul _ hM⟩
  have hAXN : ∀ w, A *ᵥ (X *ᵥ (N *ᵥ w)) = w := fun w => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hN1, Matrix.one_mulVec]
  have hAYN : ∀ w, A' *ᵥ (Y *ᵥ (N *ᵥ w)) = w := fun w => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h, hN1, Matrix.one_mulVec]
  have hNAX : ∀ w, N *ᵥ (A *ᵥ (X *ᵥ w)) = w := fun w => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, hN2, Matrix.one_mulVec]
  have hsurj : Function.Surjective (Matrix.mulVecLin A) := fun w =>
    ⟨X *ᵥ (N *ᵥ w), by rw [Matrix.mulVecLin_apply, hAXN]⟩
  have hsurj' : Function.Surjective (Matrix.mulVecLin A') := fun w =>
    ⟨Y *ᵥ (N *ᵥ w), by rw [Matrix.mulVecLin_apply, hAYN]⟩
  have hrank : Module.finrank K (LinearMap.ker (Matrix.mulVecLin A)) =
      Module.finrank K (LinearMap.ker (Matrix.mulVecLin A')) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin A)
    have h2 := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin A')
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at h1
    rw [LinearMap.range_eq_top.mpr hsurj', finrank_top] at h2
    omega
  let ψ := LinearEquiv.ofFinrankEq _ _ hrank
  let p : (n → K) →ₗ[K] LinearMap.ker (Matrix.mulVecLin A) :=
    LinearMap.codRestrict _ (LinearMap.id - Matrix.mulVecLin (X * N * A)) fun v => by
      simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, LinearMap.sub_apply,
        LinearMap.id_apply, Matrix.mulVec_sub, ← Matrix.mulVec_mulVec, hAXN, sub_self]
  let p' : (n → K) →ₗ[K] LinearMap.ker (Matrix.mulVecLin A') :=
    LinearMap.codRestrict _ (LinearMap.id - Matrix.mulVecLin (Y * N * A')) fun v => by
      simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, LinearMap.sub_apply,
        LinearMap.id_apply, Matrix.mulVec_sub, ← Matrix.mulVec_mulVec, hAYN, sub_self]
  let φ : (n → K) →ₗ[K] (n → K) := Matrix.mulVecLin (Y * N * A) +
    (LinearMap.ker (Matrix.mulVecLin A')).subtype ∘ₗ ψ.toLinearMap ∘ₗ p
  let φ' : (n → K) →ₗ[K] (n → K) := Matrix.mulVecLin (X * N * A') +
    (LinearMap.ker (Matrix.mulVecLin A)).subtype ∘ₗ ψ.symm.toLinearMap ∘ₗ p'
  have hker : ∀ k : LinearMap.ker (Matrix.mulVecLin A'), A' *ᵥ (k : n → K) = 0 := fun k => k.2
  have hker' : ∀ k : LinearMap.ker (Matrix.mulVecLin A), A *ᵥ (k : n → K) = 0 := fun k => k.2
  have hφ_eq : ∀ v, φ v = Y *ᵥ (N *ᵥ (A *ᵥ v)) + (ψ (p v) : n → K) := fun v => by
    simp only [φ, LinearMap.add_apply, LinearMap.comp_apply, Matrix.mulVecLin_apply,
      Submodule.subtype_apply, LinearEquiv.coe_coe, ← Matrix.mulVec_mulVec]
  have hφ'_eq : ∀ u, φ' u = X *ᵥ (N *ᵥ (A' *ᵥ u)) + (ψ.symm (p' u) : n → K) := fun u => by
    simp only [φ', LinearMap.add_apply, LinearMap.comp_apply, Matrix.mulVecLin_apply,
      Submodule.subtype_apply, LinearEquiv.coe_coe, ← Matrix.mulVec_mulVec]
  have hp_eq : ∀ v, (p v : n → K) = v - X *ᵥ (N *ᵥ (A *ᵥ v)) := fun v => by
    simp only [p, LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.id_apply,
      Matrix.mulVecLin_apply, ← Matrix.mulVec_mulVec]
  have hp'_eq : ∀ u, (p' u : n → K) = u - Y *ᵥ (N *ᵥ (A' *ᵥ u)) := fun u => by
    simp only [p', LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.id_apply,
      Matrix.mulVecLin_apply, ← Matrix.mulVec_mulVec]
  have hAφ : ∀ v, A' *ᵥ φ v = A *ᵥ v := fun v => by
    rw [hφ_eq, Matrix.mulVec_add, hAYN, hker, add_zero]
  have hAφ' : ∀ u, A *ᵥ φ' u = A' *ᵥ u := fun u => by
    rw [hφ'_eq, Matrix.mulVec_add, hAXN, hker', add_zero]
  have hpφ : ∀ v, p' (φ v) = ψ (p v) := fun v => by
    apply Subtype.ext
    rw [hp'_eq, hAφ, hφ_eq, add_sub_cancel_left]
  have hpφ' : ∀ u, p (φ' u) = ψ.symm (p' u) := fun u => by
    apply Subtype.ext
    rw [hp_eq, hAφ', hφ'_eq, add_sub_cancel_left]
  have hleft : ∀ v, φ' (φ v) = v := fun v => by
    rw [hφ'_eq, hpφ, hAφ, LinearEquiv.symm_apply_apply, hp_eq, add_sub_cancel]
  have hright : ∀ u, φ (φ' u) = u := fun u => by
    rw [hφ_eq, hpφ', hAφ', LinearEquiv.apply_symm_apply, hp'_eq, add_sub_cancel]
  have hφX : ∀ w, φ (X *ᵥ w) = Y *ᵥ w := fun w => by
    have hpX : p (X *ᵥ w) = 0 := by
      apply Subtype.ext
      rw [hp_eq, hNAX, sub_self, ZeroMemClass.coe_zero]
    rw [hφ_eq, hpX, map_zero, ZeroMemClass.coe_zero, add_zero, hNAX]
  refine ⟨LinearMap.toMatrix' φ, LinearMap.toMatrix' φ', ?_, ?_, ?_, ?_⟩
  · rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    exact LinearMap.ext hright
  · rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    exact LinearMap.ext hleft
  · apply Matrix.toLin'.injective
    refine LinearMap.ext fun w => ?_
    rw [Matrix.toLin'_mul, LinearMap.comp_apply, Matrix.toLin'_toMatrix', Matrix.toLin'_apply,
      Matrix.toLin'_apply, hφX]
  · apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    rw [Matrix.toLin'_mul, LinearMap.comp_apply, Matrix.toLin'_toMatrix', Matrix.toLin'_apply,
      Matrix.toLin'_apply, hAφ]

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
open Matrix Module in
private theorem matrix_eq_of_map_fst_snd {K E p q : Type*} [Field K] [CommRing E]
    (e : E ≃+* K × K) {P Q : Matrix p q E}
    (h₁ : P.map ((RingHom.fst K K).comp e.toRingHom) = Q.map ((RingHom.fst K K).comp e.toRingHom))
    (h₂ : P.map ((RingHom.snd K K).comp e.toRingHom) = Q.map ((RingHom.snd K K).comp e.toRingHom)) :
    P = Q := by
  ext a b
  apply e.injective
  exact Prod.ext (congrFun (congrFun h₁ a) b) (congrFun (congrFun h₂ a) b)

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
open Matrix Module in

theorem _root_.GlobalTheory.HermTuple.exists_matrix_split {K E n m : Type*} [Field K] [CommRing E]
    [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m] (c : E →+* E) (e : E ≃+* K × K) (he : ∀ x, e (c x) = (e x).swap)
    (G : Matrix n n E) (hG : ∀ a b, c (G a b) = G b a) (hdet : IsUnit G.det) (X Y : Matrix n m E)
    (hu : IsUnit (Xᵀ * G * X.map c).det) (h : Yᵀ * G * Y.map c = Xᵀ * G * X.map c) :
    ∃ γ : Matrix n n E, γᵀ * G * γ.map c = G ∧ γ * X = Y := by
  set f₁ : E →+* K := (RingHom.fst K K).comp e.toRingHom with hf₁
  set f₂ : E →+* K := (RingHom.snd K K).comp e.toRingHom with hf₂
  have hc₁ : ∀ z, f₁ (c z) = f₂ z := fun z => by
    simp only [hf₁, hf₂, RingHom.comp_apply, RingHom.coe_fst, RingHom.coe_snd,
      RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, he, Prod.fst_swap]
  have hc₂ : ∀ z, f₂ (c z) = f₁ z := fun z => by
    simp only [hf₁, hf₂, RingHom.comp_apply, RingHom.coe_fst, RingHom.coe_snd,
      RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, he, Prod.snd_swap]
  have hXc₁ : (X.map c).map f₁ = X.map f₂ := by ext; simp [hc₁]
  have hYc₁ : (Y.map c).map f₁ = Y.map f₂ := by ext; simp [hc₁]
  have hG₂ : G.map f₂ = (G.map f₁)ᵀ := by
    ext a b
    rw [Matrix.map_apply, ← hG b a, hc₂]
    rfl
  have hG₁ : IsUnit (G.map f₁).det := by
    have := hdet.map f₁
    rwa [RingHom.map_det, RingHom.mapMatrix_apply] at this
  have hM : IsUnit ((G.map f₁ * X.map f₂)ᵀ * X.map f₁).det := by
    have := hu.map f₁
    rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.map_mul,
      Matrix.transpose_map, hXc₁] at this
    rw [Matrix.transpose_mul, ← Matrix.det_transpose]
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
  have h₁ : (Y.map f₁)ᵀ * G.map f₁ * Y.map f₂ = (X.map f₁)ᵀ * G.map f₁ * X.map f₂ := by
    have := congrArg (fun P => Matrix.map P f₁) h
    simpa only [Matrix.map_mul, Matrix.transpose_map, hXc₁, hYc₁] using this
  have hA : (G.map f₁ * Y.map f₂)ᵀ * Y.map f₁ = (G.map f₁ * X.map f₂)ᵀ * X.map f₁ := by
    have := congrArg Matrix.transpose h₁
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
  obtain ⟨T, T', hTT', hT'T, hTX, hAT⟩ :=
    exists_inv_pair_mul_eq_of_mul_eq (X.map f₁) (Y.map f₁) _ _ hM hA
  have hGG : G.map f₁ * (G.map f₁)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hG₁
  have hGG' : (G.map f₁)⁻¹ * G.map f₁ = 1 := Matrix.nonsing_inv_mul _ hG₁
  let γ : Matrix n n E := Matrix.of fun a b => e.symm (T a b, ((G.map f₁)⁻¹ * T'ᵀ * G.map f₁) a b)
  have hγ₁ : γ.map f₁ = T := by ext; simp [γ, hf₁]
  have hγ₂ : γ.map f₂ = (G.map f₁)⁻¹ * T'ᵀ * G.map f₁ := by ext; simp [γ, hf₂]
  have hγc₁ : (γ.map c).map f₁ = γ.map f₂ := by ext; simp only [Matrix.map_apply, hc₁]
  have hγc₂ : (γ.map c).map f₂ = γ.map f₁ := by ext; simp only [Matrix.map_apply, hc₂]
  have key : Tᵀ * G.map f₁ * ((G.map f₁)⁻¹ * T'ᵀ * G.map f₁) = G.map f₁ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (G.map f₁), ← Matrix.mul_assoc (G.map f₁), hGG,
      Matrix.one_mul, ← Matrix.mul_assoc, ← Matrix.transpose_mul, hT'T, Matrix.transpose_one,
      Matrix.one_mul]
  have hTY : Tᵀ * (G.map f₁ * Y.map f₂) = G.map f₁ * X.map f₂ := by
    have := congrArg Matrix.transpose hAT
    simpa [Matrix.transpose_mul] using this
  refine ⟨γ, matrix_eq_of_map_fst_snd e ?_ ?_, matrix_eq_of_map_fst_snd e ?_ ?_⟩
  · rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hγ₁, hγc₁, hγ₂, key]
  · rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hγ₂, hγc₂, hγ₁, hG₂]
    have := congrArg Matrix.transpose key
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
  · rw [Matrix.map_mul, hγ₁, hTX]
  · rw [Matrix.map_mul, hγ₂, Matrix.mul_assoc, Matrix.mul_assoc, ← hTY, ← Matrix.mul_assoc T'ᵀ,
      ← Matrix.transpose_mul, hTT', Matrix.transpose_one, Matrix.one_mul, ← Matrix.mul_assoc,
      hGG', Matrix.one_mul]

theorem exists_matrix {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CharZero F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) {n m : ℕ}
    (G : Matrix (Fin n) (Fin n) E) (hG : ∀ a b, L.cj (G a b) = G b a) (hdet : IsUnit G.det)
    (X Y : Matrix (Fin n) (Fin m) E)
    (hu : IsUnit (Xᵀ * G * X.map L.cj).det) (h : Yᵀ * G * Y.map L.cj = Xᵀ * G * X.map L.cj) :
    ∃ γ : Matrix (Fin n) (Fin n) E, γᵀ * G * γ.map L.cj = G ∧ γ * X = Y := by
  rcases GlobalTheory.SgLoc.LocE_isField_or_split L with hE | ⟨e, he⟩
  · letI := hE.toField
    have h2 : (2 : E) ≠ 0 := by
      have : (algebraMap F E 2) ≠ 0 := by
        rw [map_ne_zero]; exact two_ne_zero
      rwa [map_ofNat] at this
    obtain ⟨γ, h1, h3⟩ := GlobalTheory.HermWitt.exists_gl_isometry_mul_eq_of_det_ne_zero
      (c := (L.cj : E →+* E)) h2 L.cj_cj hG (X := X) (Y := Y) hu.ne_zero h
    exact ⟨γ, h1, h3⟩
  · exact exists_matrix_split (L.cj : E →+* E) e.toRingEquiv he G hG hdet X Y hu h

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
open Matrix Module in
private theorem transpose_mul_mul_map_apply_eq_sum {R p q q' : Type*} [CommRing R] [Fintype p]
    (c : R →+* R) (G : Matrix p p R) (U : Matrix p q R) (V : Matrix p q' R) (i : q) (j : q') :
    (Uᵀ * G * V.map c) i j = ∑ a, ∑ b, U a i * G a b * c (V b j) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
open Matrix Module in
private theorem isField_or_exists_swap_ringEquiv {F : Type} [Field F] [ValuativeRel F]
    [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
    (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) : IsField E ∨ ∃ e : E ≃+* F × F, ∀ x, e (L.cj x) = (e x).swap := by
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ L.rank
  haveI : Nontrivial E := Module.nontrivial_of_finrank_eq_succ L.rank
  haveI := L.reduced
  by_cases hfield : IsField E
  · exact Or.inl hfield
  right
  obtain ⟨u, hu0, hu⟩ : ∃ u : E, u ≠ 0 ∧ ∀ w, u * w ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    exact hfield ⟨exists_pair_ne E, mul_comm, fun ha => hcon _ ha⟩
  obtain ⟨t, ht⟩ := (L.cj_fix (u + L.cj u)).1 (by rw [map_add, L.cj_cj, add_comm])
  obtain ⟨s, hs⟩ := (L.cj_fix (u * L.cj u)).1 (by rw [map_mul, L.cj_cj, mul_comm])
  have hs0 : s = 0 := by
    by_contra hs0
    apply hu (L.cj u * algebraMap F E s⁻¹)
    rw [← mul_assoc, ← hs, ← map_mul, mul_inv_cancel₀ hs0, map_one]
  have huu : u * L.cj u = 0 := by rw [← hs, hs0, map_zero]
  have hsq : u * u = algebraMap F E t * u := by
    rw [ht]
    linear_combination (-1 : E) * huu
  have ht0 : t ≠ 0 := by
    rintro rfl
    apply hu0
    apply IsReduced.eq_zero
    exact ⟨2, by rw [pow_two, hsq, map_zero, zero_mul]⟩
  have hcu0 : L.cj u ≠ 0 := by
    intro h
    apply hu0
    rw [← L.cj_cj u, h, map_zero]
  set p := algebraMap F E t⁻¹ * u with hp
  set q := algebraMap F E t⁻¹ * L.cj u with hq
  have h1 : p + q = 1 := by
    rw [hp, hq, ← mul_add, ← ht, ← map_mul, inv_mul_cancel₀ ht0, map_one]
  have h0 : p * q = 0 := by
    rw [hp, hq]
    linear_combination (algebraMap F E t⁻¹ * algebraMap F E t⁻¹) * huu
  have hp0 : p ≠ 0 := by
    intro h
    apply hu0
    have hpu : algebraMap F E t * p = u := by
      rw [hp, ← mul_assoc, ← map_mul, mul_inv_cancel₀ ht0, map_one, one_mul]
    rw [← hpu, h, mul_zero]
  have hq0 : q ≠ 0 := by
    intro h
    apply hcu0
    have hqu : algebraMap F E t * q = L.cj u := by
      rw [hq, ← mul_assoc, ← map_mul, mul_inv_cancel₀ ht0, map_one, one_mul]
    rw [← hqu, h, mul_zero]
  have hpp : p * p = p := by linear_combination p * h1 - h0
  have hqq : q * q = q := by linear_combination q * h1 - h0
  have hcp : L.cj p = q := by rw [hp, hq, map_mul, AlgEquiv.commutes]
  have hcq : L.cj q = p := by rw [hp, hq, map_mul, AlgEquiv.commutes, L.cj_cj]
  clear_value p q
  let φ : F × F →ₐ[F] E := _root_.GlobalTheory.SgLoc.idemPairHom p q h1 h0
  have hφ : ∀ a b : F, φ (a, b) = algebraMap F E a * p + algebraMap F E b * q := by
    intro a b
    simp [φ, _root_.GlobalTheory.SgLoc.idemPairHom, Algebra.smul_def]
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨a, b⟩ hab
    rw [hφ] at hab
    have ha : algebraMap F E a * p = 0 := by
      linear_combination p * hab - algebraMap F E a * hpp - algebraMap F E b * h0
    have hb : algebraMap F E b * q = 0 := by
      linear_combination q * hab - algebraMap F E a * h0 - algebraMap F E b * hqq
    rw [← Algebra.smul_def, smul_eq_zero] at ha hb
    exact Prod.ext (ha.resolve_right hp0) (hb.resolve_right hq0)
  have hdim : Module.finrank F (F × F) = Module.finrank F E := by
    rw [L.rank, Module.finrank_prod, Module.finrank_self]
  have hbij : Function.Bijective φ :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
      (f := φ.toLinearMap)).1 hinj⟩
  have hcj : ∀ w : F × F, L.cj (φ w) = φ w.swap := by
    rintro ⟨a, b⟩
    rw [hφ, Prod.swap_prod_mk, hφ]
    simp only [map_add, map_mul, AlgEquiv.commutes, hcp, hcq]
    ring
  let eφ := AlgEquiv.ofBijective φ hbij
  have hsymm : ∀ w, eφ.symm (φ w) = w := fun w => eφ.symm_apply_apply w
  refine ⟨eφ.symm.toRingEquiv, fun x => ?_⟩
  obtain ⟨w, rfl⟩ := hbij.2 x
  change eφ.symm (L.cj (φ w)) = (eφ.symm (φ w)).swap
  rw [hcj, hsymm, hsymm]

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
open Matrix Module in

theorem _root_.GlobalTheory.HermTuple.witt_tuples : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), _root_.GlobalTheory.HL.IsHermND L Hm → ∀ (m : ℕ) (x y : Fin m → Fin n → E), (∀ i j, _root_.GlobalTheory.HL.hf L Hm (x i) (x j) = _root_.GlobalTheory.HL.hf L Hm (y i) (y j)) → IsUnit (Matrix.of fun i j => _root_.GlobalTheory.HL.hf L Hm (x i) (x j)).det → ∃ g ∈ _root_.GlobalTheory.HL.isomG L Hm, ∀ i, g (x i) = y i := by
  intro F _ _ _ _ _ E _ _ _ L n Hm hHm m x y hxy hunit
  haveI : Nontrivial E := Module.nontrivial_of_finrank_eq_succ L.rank
  have hHm' := hHm
  unfold _root_.GlobalTheory.HL.IsHermND _root_.GlobalTheory.HL.IsHerm _root_.GlobalTheory.HL.cT at hHm'
  obtain ⟨hherm, hdet⟩ := hHm'
  have hG : ∀ a b, L.cj (Hm a b) = Hm b a := fun a b => by
    simpa using congrFun (congrFun hherm b) a
  let c : E →+* E := L.cj.toRingEquiv.toRingHom
  have hform : ∀ u v : Fin n → E,
      _root_.GlobalTheory.HL.hf L Hm u v = ∑ a, ∑ b, u a * Hm a b * c (v b) := by
    intro u v
    unfold _root_.GlobalTheory.HL.hf
    rfl
  let X : Matrix (Fin n) (Fin m) E := Matrix.of fun k i => x i k
  let Y : Matrix (Fin n) (Fin m) E := Matrix.of fun k i => y i k
  have hXY : Yᵀ * Hm * Y.map c = Xᵀ * Hm * X.map c := by
    ext i j
    rw [transpose_mul_mul_map_apply_eq_sum, transpose_mul_mul_map_apply_eq_sum, ← hform,
      ← hform]
    exact (hxy i j).symm
  have hXu : IsUnit (Xᵀ * Hm * X.map c).det := by
    convert hunit using 2
    ext i j
    rw [transpose_mul_mul_map_apply_eq_sum, ← hform]
    rfl
  have h2 : (2 : E) ≠ 0 := by
    intro h2
    apply (two_ne_zero : (2 : F) ≠ 0)
    apply (algebraMap F E).injective
    rw [map_ofNat, map_zero]
    exact h2
  obtain ⟨P, hPG, hPX⟩ : ∃ P : Matrix (Fin n) (Fin n) E, Pᵀ * Hm * P.map c = Hm ∧ P * X = Y := by
    rcases isField_or_exists_swap_ringEquiv L with hfield | ⟨e, he⟩
    · letI : Field E := hfield.toField
      obtain ⟨γ, hγG, hγX⟩ := _root_.GlobalTheory.HermWitt.exists_gl_isometry_mul_eq_of_det_ne_zero h2 (c := c)
        (fun t => L.cj_cj t) hG hXu.ne_zero hXY
      exact ⟨γ, hγG, hγX⟩
    · exact _root_.GlobalTheory.HermTuple.exists_matrix_split c e he Hm hG hdet X Y hXu hXY
  have hPdet : IsUnit P.det := by
    have hd := congrArg Matrix.det hPG
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hd
    have h' : IsUnit (P.det * Hm.det * (P.map c).det) := by
      rw [hd]
      exact hdet
    exact isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left h')
  letI := P.invertibleOfIsUnitDet hPdet
  have hcol : ∀ u : Fin n → E,
      (Matrix.of fun k (_ : Unit) => (P *ᵥ u) k) = P * Matrix.of fun k (_ : Unit) => u k := by
    intro u
    ext k l
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have hform' : ∀ u v : Fin n → E, _root_.GlobalTheory.HL.hf L Hm u v =
      ((Matrix.of fun k (_ : Unit) => u k)ᵀ * Hm *
        (Matrix.of fun k (_ : Unit) => v k).map c) () () := by
    intro u v
    rw [transpose_mul_mul_map_apply_eq_sum, hform]
    rfl
  refine ⟨Matrix.toLinearEquiv' P ‹_›, ?_, fun i => ?_⟩
  · change ∀ u v, _root_.GlobalTheory.HL.hf L Hm (P *ᵥ u) (P *ᵥ v) =
      _root_.GlobalTheory.HL.hf L Hm u v
    intro u v
    rw [hform', hform', hcol, hcol, Matrix.transpose_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Hm, ← Matrix.mul_assoc Pᵀ, ← Matrix.mul_assoc Pᵀ Hm, hPG]
  · change P *ᵥ x i = y i
    ext k
    have := congrFun (congrFun hPX k) i
    simpa [X, Y, Matrix.mul_apply, Matrix.mulVec, dotProduct] using this

end GlobalTheory.HermTuple
