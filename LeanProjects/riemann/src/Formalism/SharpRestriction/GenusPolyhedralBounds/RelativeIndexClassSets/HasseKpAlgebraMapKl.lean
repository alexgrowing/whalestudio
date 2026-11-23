import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AlgebraMapOlInjective

noncomputable section

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace Tay

open MvPowerSeries Finset.HasAntidiagonal

variable {σ : Type*} {A : Type*} [CommRing A]

def IsTay (τ : A →+* MvPowerSeries σ A) : Prop := ∀ x, constantCoeff (τ x) = x

def co (τ : A →+* MvPowerSeries σ A) (β : σ →₀ ℕ) : A →+ A :=
  (coeff β : MvPowerSeries σ A →ₗ[A] A).toAddMonoidHom.comp τ.toAddMonoidHom

theorem co_apply (τ : A →+* MvPowerSeries σ A) (β : σ →₀ ℕ) (x : A) : co τ β x = coeff β (τ x) := rfl

theorem co_zero {τ : A →+* MvPowerSeries σ A} (h : IsTay τ) (x : A) : co τ 0 x = x := by
  rw [co_apply, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact h x

theorem co_mul [DecidableEq σ] (τ : A →+* MvPowerSeries σ A) (β : σ →₀ ℕ) (x y : A) :
    co τ β (x * y) = ∑ q ∈ antidiagonal β, co τ q.1 x * co τ q.2 y := by
  simp only [co_apply, map_mul, MvPowerSeries.coeff_mul]

def cw (d : A →+ A) : MvPowerSeries σ A →+ MvPowerSeries σ A where
  toFun f := fun n => d (coeff n f)
  map_zero' := by ext n; exact map_zero d
  map_add' f g := by ext n; exact map_add d _ _

theorem coeff_cw (d : A →+ A) (f : MvPowerSeries σ A) (n : σ →₀ ℕ) : coeff n (cw d f) = d (coeff n f) := rfl

theorem cw_mul (d : A →+ A) (hd : ∀ x y, d (x * y) = x * d y + y * d x) (f g : MvPowerSeries σ A) :
    cw d (f * g) = f * cw d g + g * cw d f := by
  classical
  ext n
  rw [mul_comm g (cw d f)]
  simp only [coeff_cw, MvPowerSeries.coeff_mul, map_add, map_sum, hd, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun q _ => by ring

def dv (τ : A →+* MvPowerSeries σ A) (p : σ) : A →+ A := co τ (Finsupp.single p 1)

theorem dv_eq (τ : A →+* MvPowerSeries σ A) (p : σ) (x : A) : dv τ p x = constantCoeff (pderiv A p (τ x)) := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_pderiv]
  simp [dv, co_apply]

theorem dv_mul {τ : A →+* MvPowerSeries σ A} (h : IsTay τ) (p : σ) (x y : A) :
    dv τ p (x * y) = x * dv τ p y + y * dv τ p x := by
  simp only [dv_eq, map_mul, Derivation.leibniz, map_add, smul_eq_mul, h x, h y]

def IterAt (τ : A →+* MvPowerSeries σ A) (p : σ) (x : A) : Prop := pderiv A p (τ x) = cw (dv τ p) (τ x)

theorem iterAt_iff (τ : A →+* MvPowerSeries σ A) (p : σ) (x : A) :
    IterAt τ p x ↔ ∀ β : σ →₀ ℕ, (β p + 1) • co τ (β + Finsupp.single p 1) x = dv τ p (co τ β x) := by
  unfold IterAt
  rw [MvPowerSeries.ext_iff]
  refine forall_congr' fun β => ?_
  rw [MvPowerSeries.coeff_pderiv, coeff_cw, co_apply, co_apply, nsmul_eq_mul, Nat.cast_succ]
  constructor <;> intro hh <;> linear_combination hh

theorem IterAt.add {τ : A →+* MvPowerSeries σ A} {p : σ} {x y : A} (hx : IterAt τ p x) (hy : IterAt τ p y) :
    IterAt τ p (x + y) := by
  unfold IterAt at hx hy ⊢
  simp only [map_add, hx, hy]

theorem IterAt.mul {τ : A →+* MvPowerSeries σ A} (h : IsTay τ) {p : σ} {x y : A} (hx : IterAt τ p x)
    (hy : IterAt τ p y) : IterAt τ p (x * y) := by
  unfold IterAt at hx hy ⊢
  rw [map_mul, Derivation.leibniz, hx, hy, smul_eq_mul, smul_eq_mul, cw_mul _ (dv_mul h p)]

theorem IterAt.of_mul {τ : A →+* MvPowerSeries σ A} (h : IsTay τ) {p : σ} {s y : A} (hs : IterAt τ p s)
    (hsy : IterAt τ p (s * y)) (hu : IsUnit s) : IterAt τ p y := by
  unfold IterAt at hs hsy ⊢
  have hu' : IsUnit (τ s) := hu.map τ
  rw [map_mul, Derivation.leibniz, cw_mul _ (dv_mul h p), hs, smul_eq_mul, smul_eq_mul] at hsy
  exact hu'.mul_left_cancel (add_right_cancel hsy)

def IsCst (τ : A →+* MvPowerSeries σ A) (c : A) : Prop := τ c = C c

theorem IsCst.co {τ : A →+* MvPowerSeries σ A} {c : A} (hc : IsCst τ c) {β : σ →₀ ℕ} (hβ : β ≠ 0) :
    Tay.co τ β c = 0 := by
  classical
  rw [co_apply, show τ c = C c from hc, MvPowerSeries.coeff_C, if_neg hβ]

theorem IsCst.co_mul {τ : A →+* MvPowerSeries σ A} {c : A} (hc : IsCst τ c) (β : σ →₀ ℕ) (x : A) :
    Tay.co τ β (c * x) = c * Tay.co τ β x := by
  classical
  rw [co_apply, co_apply, map_mul, show τ c = C c from hc, MvPowerSeries.coeff_C_mul]

theorem IsCst.dv {τ : A →+* MvPowerSeries σ A} {c : A} (hc : IsCst τ c) (p : σ) : Tay.dv τ p c = 0 := hc.co (Finsupp.single_ne_zero.mpr one_ne_zero)

theorem IsCst.iterAt {τ : A →+* MvPowerSeries σ A} {c : A} (hc : IsCst τ c) (p : σ) : IterAt τ p c := by
  classical
  unfold IterAt
  rw [show τ c = C c from hc]
  ext n
  rw [MvPowerSeries.coeff_pderiv, coeff_cw, MvPowerSeries.coeff_C, MvPowerSeries.coeff_C,
    if_neg (fun h0 => by have := DFunLike.congr_fun h0 p; simp at this), zero_mul]
  split_ifs
  · exact (hc.dv p).symm
  · exact (map_zero _).symm

section Loc
variable (M : Submonoid A) (B : Type*) [CommRing B] [Algebra A B] [IsLocalization M B]

theorem loc_isUnit {τ : A →+* MvPowerSeries σ A} (h : IsTay τ) (y : M) :
    IsUnit (((MvPowerSeries.map (algebraMap A B)).comp τ) y) := by
  rw [RingHom.comp_apply, MvPowerSeries.isUnit_iff_constantCoeff, MvPowerSeries.constantCoeff_map, h y]
  exact IsLocalization.map_units B y

def loc (τ : A →+* MvPowerSeries σ A) (h : IsTay τ) : B →+* MvPowerSeries σ B :=
  IsLocalization.lift (M := M) (g := (MvPowerSeries.map (algebraMap A B)).comp τ) (loc_isUnit M B h)

theorem loc_algebraMap (τ : A →+* MvPowerSeries σ A) (h : IsTay τ) (a : A) :
    loc M B τ h (algebraMap A B a) = MvPowerSeries.map (algebraMap A B) (τ a) := by
  exact IsLocalization.lift_eq (loc_isUnit M B h) a

theorem loc_isTay (τ : A →+* MvPowerSeries σ A) (h : IsTay τ) : IsTay (loc M B τ h) := by
  intro b
  have key : (MvPowerSeries.constantCoeff : MvPowerSeries σ B →+* B).comp (loc M B τ h) = RingHom.id B := by
    apply IsLocalization.ringHom_ext M
    ext a
    simp only [RingHom.comp_apply, loc_algebraMap, MvPowerSeries.constantCoeff_map, RingHom.id_apply, h a]
  exact RingHom.congr_fun key b

theorem loc_co (τ : A →+* MvPowerSeries σ A) (h : IsTay τ) (β : σ →₀ ℕ) (a : A) :
    co (loc M B τ h) β (algebraMap A B a) = algebraMap A B (co τ β a) := by
  rw [co_apply, co_apply, loc_algebraMap, MvPowerSeries.coeff_map]

theorem loc_dv (τ : A →+* MvPowerSeries σ A) (h : IsTay τ) (p : σ) (a : A) :
    dv (loc M B τ h) p (algebraMap A B a) = algebraMap A B (dv τ p a) := loc_co M B τ h (Finsupp.single p 1) a

theorem loc_isCst (τ : A →+* MvPowerSeries σ A) (h : IsTay τ) {c : A} (hc : IsCst τ c) :
    IsCst (loc M B τ h) (algebraMap A B c) := by
  show loc M B τ h (algebraMap A B c) = C (algebraMap A B c)
  rw [loc_algebraMap, show τ c = C c from hc, MvPowerSeries.map_C]

theorem loc_iterAt_algebraMap (τ : A →+* MvPowerSeries σ A) (h : IsTay τ) {p : σ} {a : A} (ha : IterAt τ p a) :
    IterAt (loc M B τ h) p (algebraMap A B a) := by
  rw [iterAt_iff] at ha ⊢
  intro β
  rw [loc_co, loc_co, loc_dv, ← ha β, map_nsmul]

theorem loc_iterAt (τ : A →+* MvPowerSeries σ A) (h : IsTay τ) {p : σ} (ha : ∀ a, IterAt τ p a) (b : B) :
    IterAt (loc M B τ h) p b := by
  obtain ⟨⟨x, y⟩, hxy⟩ := IsLocalization.surj M b
  dsimp only at hxy
  have hy := loc_iterAt_algebraMap M B τ h (ha (y : A))
  have hx := loc_iterAt_algebraMap M B τ h (ha x)
  refine IterAt.of_mul (loc_isTay M B τ h) hy ?_ (IsLocalization.map_units B y)
  rw [mul_comm, hxy]
  exact hx

end Loc

section Lin
variable (R : Type*) [CommRing R] [Algebra R A]

def hs (τ : A →+* MvPowerSeries σ A) (hR : ∀ r : R, IsCst τ (algebraMap R A r)) (β : σ →₀ ℕ) : A →ₗ[R] A where
  toFun := co τ β
  map_add' := map_add _
  map_smul' r x := by rw [Algebra.smul_def, (hR r).co_mul, RingHom.id_apply, Algebra.smul_def]

def der (τ : A →+* MvPowerSeries σ A) (h : IsTay τ) (hR : ∀ r : R, IsCst τ (algebraMap R A r)) (p : σ) :
    Derivation R A A :=
  Derivation.mk' (hs R τ hR (Finsupp.single p 1)) fun x y => by
    simp only [smul_eq_mul]
    exact dv_mul h p x y

theorem hs_apply (τ : A →+* MvPowerSeries σ A) (hR : ∀ r : R, IsCst τ (algebraMap R A r)) (β : σ →₀ ℕ) (x : A) :
    hs R τ hR β x = co τ β x := rfl

theorem der_apply (τ : A →+* MvPowerSeries σ A) (h : IsTay τ) (hR : ∀ r : R, IsCst τ (algebraMap R A r)) (p : σ)
    (x : A) : der R τ h hR p x = dv τ p x := rfl

end Lin

theorem cw_C (d : A →+ A) (a : A) : cw d (C a : MvPowerSeries σ A) = C (d a) := by
  classical
  ext n
  rw [coeff_cw, MvPowerSeries.coeff_C, MvPowerSeries.coeff_C]
  split_ifs <;> simp

theorem cw_X (d : A →+ A) (h1 : d 1 = 0) (q : σ) : cw d (X q : MvPowerSeries σ A) = 0 := by
  classical
  ext n
  rw [coeff_cw, MvPowerSeries.coeff_X]
  split_ifs <;> simp [h1]

section Poly
variable (σ) (R : Type*) [CommRing R]

def pol : MvPolynomial σ R →+* MvPowerSeries σ (MvPolynomial σ R) :=
  MvPolynomial.eval₂Hom ((C : MvPolynomial σ R →+* MvPowerSeries σ (MvPolynomial σ R)).comp MvPolynomial.C)
    (fun p => C (MvPolynomial.X p) + X p)

theorem pol_C (r : R) : pol σ R (MvPolynomial.C r) = C (MvPolynomial.C r) := by
  exact MvPolynomial.eval₂Hom_C _ _ r

theorem pol_X (p : σ) : pol σ R (MvPolynomial.X p) = C (MvPolynomial.X p) + X p := by
  exact MvPolynomial.eval₂_X _ _ p

theorem pol_isTay : IsTay (pol σ R) := by
  intro x
  have key : (MvPowerSeries.constantCoeff : MvPowerSeries σ (MvPolynomial σ R) →+* _).comp (pol σ R) = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [pol_C]
    · intro p; simp [pol_X]
  exact RingHom.congr_fun key x

theorem pol_isCst (r : R) : IsCst (pol σ R) (algebraMap R (MvPolynomial σ R) r) := by
  unfold IsCst
  rw [MvPolynomial.algebraMap_eq]
  exact pol_C σ R r

theorem pol_dv_X [DecidableEq σ] (p q : σ) : dv (pol σ R) p (MvPolynomial.X q) = if p = q then 1 else 0 := by
  rw [dv, co_apply, pol_X, map_add, MvPowerSeries.coeff_C, MvPowerSeries.coeff_X,
    if_neg (Finsupp.single_ne_zero.mpr one_ne_zero), zero_add]
  by_cases hpq : p = q
  · subst hpq; simp
  · rw [if_neg hpq, if_neg]; exact fun h => hpq (Finsupp.single_left_injective one_ne_zero h)

theorem pol_iterAt (p : σ) (x : MvPolynomial σ R) : IterAt (pol σ R) p x := by
  classical
  have h1 : dv (pol σ R) p 1 = 0 := by
    rw [dv, co_apply, map_one, MvPowerSeries.coeff_one, if_neg (Finsupp.single_ne_zero.mpr one_ne_zero)]
  have key : ∀ (n : σ) (γ : σ →₀ ℕ), co (pol σ R) γ (MvPolynomial.X n) =
      (if γ = 0 then MvPolynomial.X n else 0) + (if γ = Finsupp.single n 1 then 1 else 0) := by
    intro n γ
    rw [co_apply, pol_X, map_add, MvPowerSeries.coeff_C, MvPowerSeries.coeff_X]
  have hX : ∀ n, IterAt (pol σ R) p (MvPolynomial.X n) := by
    intro n
    rw [iterAt_iff]
    intro β
    by_cases hb : β = 0
    · subst hb
      simp only [co_zero (pol_isTay σ R), zero_add, Finsupp.coe_zero, Pi.zero_apply, one_smul] <;> rfl
    · have hne0 : β + Finsupp.single p 1 ≠ 0 := fun h => by
        have := DFunLike.congr_fun h p; simp at this
      have hne : β + Finsupp.single p 1 ≠ Finsupp.single n 1 := by
        intro h
        by_cases hpn : p = n
        · subst hpn; exact hb (add_right_cancel (h.trans (zero_add _).symm))
        · have := DFunLike.congr_fun h p
          simp [Finsupp.single_apply, hpn, Ne.symm hpn] at this
      rw [key, key, if_neg hne0, if_neg hne, if_neg hb, add_zero, smul_zero, zero_add]
      split_ifs
      · exact h1.symm
      · exact (map_zero _).symm
  refine MvPolynomial.induction_on x (fun a => ?_) (fun f g hf hg => ?_) (fun f n hf => ?_)
  · exact IsCst.iterAt (τ := pol σ R) (pol_C σ R a) p
  · exact hf.add hg
  · exact hf.mul (pol_isTay σ R) (hX n)

theorem pol_der (p : σ) : der R (pol σ R) (pol_isTay σ R) (pol_isCst σ R) p = MvPolynomial.pderiv p := by
  classical
  apply MvPolynomial.derivation_ext
  intro i
  rw [der_apply, pol_dv_X, MvPolynomial.pderiv_X]
  by_cases h : p = i
  · subst h; simp
  · simp [h, Pi.single_apply, Ne.symm h]

end Poly

section Tens
open TensorProduct
variable (R : Type*) {K : Type*} (V : Type*) [CommRing R] [CommRing K] [CommRing V] [Algebra R K] [Algebra R V]

def alg (τ : K →+* MvPowerSeries σ K) (hR : ∀ r : R, IsCst τ (algebraMap R K r)) : K →ₐ[R] MvPowerSeries σ K :=
  { τ with commutes' := fun r => by rw [MvPowerSeries.algebraMap_apply]; exact hR r }

def tens (τ : K →+* MvPowerSeries σ K) (hR : ∀ r : R, IsCst τ (algebraMap R K r)) :
    K ⊗[R] V →ₐ[R] MvPowerSeries σ (K ⊗[R] V) :=
  Algebra.TensorProduct.lift
    ((MvPowerSeries.mapAlgHom (Algebra.TensorProduct.includeLeft : K →ₐ[R] K ⊗[R] V)).comp (alg R τ hR))
    (((Algebra.ofId (K ⊗[R] V) (MvPowerSeries σ (K ⊗[R] V))).restrictScalars R).comp
      (Algebra.TensorProduct.includeRight : V →ₐ[R] K ⊗[R] V))
    (fun _ _ => Commute.all _ _)

theorem tens_tmul (τ : K →+* MvPowerSeries σ K) (hR : ∀ r : R, IsCst τ (algebraMap R K r)) (k : K) (v : V) :
    tens R V τ hR (k ⊗ₜ v) =
      MvPowerSeries.map (Algebra.TensorProduct.includeLeft : K →ₐ[R] K ⊗[R] V).toRingHom (τ k) * C (1 ⊗ₜ v) := by
  first
    | (rw [tens, Algebra.TensorProduct.lift_tmul]; rfl)
    | simp [tens, alg, MvPowerSeries.algebraMap_apply]

theorem tens_co_tmul (τ : K →+* MvPowerSeries σ K) (hR : ∀ r : R, IsCst τ (algebraMap R K r)) (β : σ →₀ ℕ)
    (k : K) (v : V) : co (tens R V τ hR).toRingHom β (k ⊗ₜ v) = co τ β k ⊗ₜ v := by
  show MvPowerSeries.coeff β (tens R V τ hR (k ⊗ₜ v)) = _
  rw [tens_tmul, MvPowerSeries.coeff_mul_C, MvPowerSeries.coeff_map]
  simp [co_apply, Algebra.TensorProduct.tmul_mul_tmul]

theorem tens_isTay (τ : K →+* MvPowerSeries σ K) (h : IsTay τ) (hR : ∀ r : R, IsCst τ (algebraMap R K r)) :
    IsTay (tens R V τ hR).toRingHom := by
  intro x
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, ← co_apply]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul k v => rw [tens_co_tmul, co_zero h]
  | add x y hx hy => rw [map_add, hx, hy]

theorem tens_isCst_right (τ : K →+* MvPowerSeries σ K) (hR : ∀ r : R, IsCst τ (algebraMap R K r)) (v : V) :
    IsCst (tens R V τ hR).toRingHom ((1 : K) ⊗ₜ[R] v) := by
  show tens R V τ hR ((1 : K) ⊗ₜ v) = C ((1 : K) ⊗ₜ v)
  rw [tens_tmul, map_one, map_one, one_mul]

theorem tens_isCst_left (τ : K →+* MvPowerSeries σ K) (hR : ∀ r : R, IsCst τ (algebraMap R K r)) {c : K}
    (hc : IsCst τ c) : IsCst (tens R V τ hR).toRingHom (c ⊗ₜ[R] (1 : V)) := by
  show tens R V τ hR (c ⊗ₜ (1 : V)) = C (c ⊗ₜ (1 : V))
  rw [tens_tmul, show τ c = C c from hc, MvPowerSeries.map_C, ← Algebra.TensorProduct.one_def, map_one, mul_one] <;> rfl

theorem tens_isCst_algebraMap (τ : K →+* MvPowerSeries σ K) (hR : ∀ r : R, IsCst τ (algebraMap R K r)) (r : R) :
    IsCst (tens R V τ hR).toRingHom (algebraMap R (K ⊗[R] V) r) := by
  rw [Algebra.TensorProduct.algebraMap_apply]
  exact tens_isCst_left R V τ hR (hR r)

theorem tens_iterAt (τ : K →+* MvPowerSeries σ K) (h : IsTay τ) (hR : ∀ r : R, IsCst τ (algebraMap R K r)) {p : σ}
    (hi : ∀ k, IterAt τ p k) (x : K ⊗[R] V) : IterAt (tens R V τ hR).toRingHom p x := by
  induction x using TensorProduct.induction_on with
  | zero => unfold IterAt; simp only [map_zero]
  | tmul k v =>
    rw [iterAt_iff]
    intro β
    have hk := (iterAt_iff τ p k).mp (hi k) β
    have e : ∀ a : K, a ⊗ₜ[R] v = (TensorProduct.mk R K V).flip v a := fun _ => rfl
    rw [tens_co_tmul, tens_co_tmul, dv, tens_co_tmul, e, e, ← map_nsmul, hk] <;> rfl
  | add x y hx hy => exact hx.add hy

end Tens

section Iter
variable {τ : A →+* MvPowerSeries σ A}

theorem dv_co (hi : ∀ p x, IterAt τ p x) (p : σ) (β : σ →₀ ℕ) (x : A) :
    dv τ p (co τ β x) = (β p + 1) • co τ (β + Finsupp.single p 1) x := ((iterAt_iff τ p x).mp (hi p x) β).symm

theorem dv_comm (hi : ∀ p x, IterAt τ p x) (p q : σ) (x : A) : dv τ p (dv τ q x) = dv τ q (dv τ p x) := by
  have hsym : (Finsupp.single q 1) p = (Finsupp.single p 1) q := by
    by_cases h : p = q
    · subst h; rfl
    · simp [Finsupp.single_apply, h, Ne.symm h]
  change dv τ p (co τ (Finsupp.single q 1) x) = dv τ q (co τ (Finsupp.single p 1) x)
  rw [dv_co hi p (Finsupp.single q 1) x, dv_co hi q (Finsupp.single p 1) x, add_comm (Finsupp.single q 1), hsym]

theorem dv_iterate_co (hi : ∀ p x, IterAt τ p x) (p : σ) (n : ℕ) (β : σ →₀ ℕ) (x : A) :
    (dv τ p)^[n] (co τ β x) = ((β p + 1).ascFactorial n) • co τ (β + Finsupp.single p n) x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, map_nsmul, dv_co hi, smul_smul, add_assoc, ← Finsupp.single_add]
    congr 1
    rw [Nat.ascFactorial_succ, Finsupp.add_apply, Finsupp.single_eq_same]
    ring

theorem IsCst.of_mul {s y : A} (hs : IsCst τ s) (hsy : IsCst τ (s * y)) (hu : IsUnit s) : IsCst τ y := by
  have hs' : τ s = C s := hs
  have hsy' : τ (s * y) = C (s * y) := hsy
  simp only [map_mul, hs'] at hsy'
  exact (hu.map (C : A →+* MvPowerSeries σ A)).mul_left_cancel hsy'

variable (R : Type*) [CommRing R] [Algebra R A]

theorem hs_commute (hi : ∀ p x, IterAt τ p x) (hR : ∀ r : R, IsCst τ (algebraMap R A r)) (p q : σ) :
    Commute (hs R τ hR (Finsupp.single p 1)) (hs R τ hR (Finsupp.single q 1)) := LinearMap.ext fun x => dv_comm hi p q x

theorem itD_pairwise (hi : ∀ p x, IterAt τ p x) (hR : ∀ r : R, IsCst τ (algebraMap R A r)) (s : Finset σ)
    (β : σ →₀ ℕ) : (s : Set σ).Pairwise (Function.onFun Commute fun p => hs R τ hR (Finsupp.single p 1) ^ β p) := fun p _ q _ _ => (hs_commute R hi hR p q).pow_pow _ _

def itD (hi : ∀ p x, IterAt τ p x) (hR : ∀ r : R, IsCst τ (algebraMap R A r)) (s : Finset σ) (β : σ →₀ ℕ) :
    Module.End R A :=
  s.noncommProd (fun p => hs R τ hR (Finsupp.single p 1) ^ β p) (itD_pairwise R hi hR s β)

theorem itD_empty (hi : ∀ p x, IterAt τ p x) (hR : ∀ r : R, IsCst τ (algebraMap R A r)) (β : σ →₀ ℕ) :
    itD R hi hR ∅ β = 1 := by
  rw [itD, Finset.noncommProd_empty]

theorem itD_insert [DecidableEq σ] (hi : ∀ p x, IterAt τ p x) (hR : ∀ r : R, IsCst τ (algebraMap R A r))
    {s : Finset σ} {a : σ} (ha : a ∉ s) (β : σ →₀ ℕ) :
    itD R hi hR (insert a s) β = hs R τ hR (Finsupp.single a 1) ^ β a * itD R hi hR s β := by
  unfold itD
  first
    | exact Finset.noncommProd_insert_of_notMem _ _ _ _ ha
    | exact Finset.noncommProd_insert_of_not_mem _ _ _ _ ha

theorem itD_co (hi : ∀ p x, IterAt τ p x) (hR : ∀ r : R, IsCst τ (algebraMap R A r)) (s : Finset σ)
    (β γ : σ →₀ ℕ) (x : A) : itD R hi hR s β (co τ γ x) =
      (∏ p ∈ s, (γ p + 1).ascFactorial (β p)) • co τ (γ + ∑ p ∈ s, Finsupp.single p (β p)) x := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [itD_empty]
  · intro a s ha ih
    have hS : (∑ p ∈ s, Finsupp.single p (β p)) a = 0 := by
      rw [Finsupp.finset_sum_apply]
      exact Finset.sum_eq_zero fun p hp => by
        rw [Finsupp.single_apply, if_neg]; rintro rfl; exact ha hp
    have hpow : ∀ (n : ℕ) (y : A), ((hs R τ hR (Finsupp.single a 1)) ^ n) y = (dv τ a)^[n] y := by
      intro n y
      first
        | (rw [Module.End.pow_apply]; rfl)
        | (rw [LinearMap.pow_apply]; rfl)
        | (induction n generalizing y with
            | zero => rfl
            | succ n ih2 => rw [pow_succ, Function.iterate_succ_apply, ← ih2]; rfl)
    rw [itD_insert R hi hR ha]
    first | rw [Module.End.mul_apply] | rw [LinearMap.mul_apply]
    rw [ih, map_nsmul, hpow, dv_iterate_co hi,
      smul_smul, Finset.prod_insert ha, Finset.sum_insert ha, Finsupp.add_apply, hS, add_zero,
      show γ + ∑ p ∈ s, Finsupp.single p (β p) + Finsupp.single a (β a) =
        γ + (Finsupp.single a (β a) + ∑ p ∈ s, Finsupp.single p (β p)) by abel, mul_comm]

theorem itD_apply (h : IsTay τ) (hi : ∀ p x, IterAt τ p x) (hR : ∀ r : R, IsCst τ (algebraMap R A r))
    (s : Finset σ) (β : σ →₀ ℕ) (hs : β.support ⊆ s) (x : A) :
    itD R hi hR s β x = (∏ p ∈ s, (β p).factorial) • co τ β x := by
  classical
  have hsum : ∑ p ∈ s, Finsupp.single p (β p) = β := by
    ext q
    rw [Finsupp.finset_sum_apply]
    simp only [Finsupp.single_apply, Finset.sum_ite_eq', Finset.sum_ite_eq]
    split_ifs with hq
    · rfl
    · by_contra hne
      exact hq (hs (Finsupp.mem_support_iff.mpr fun h' => hne h'.symm))
  have key := itD_co R hi hR s β 0 x
  simp only [co_zero h, zero_add, hsum] at key
  rw [key]
  congr 1
  exact Finset.prod_congr rfl fun p _ => by simp [Nat.one_ascFactorial]

end Iter

end Tay

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module TensorProduct

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

open Finset.HasAntidiagonal

section
variable (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ)

def tayPol : Pol X la N →+* MvPowerSeries (Idx D j N) (Pol X la N) := Tay.pol (Idx D j N) (X.Ol la)

theorem tayPol_isTay : Tay.IsTay (tayPol X la N) := Tay.pol_isTay (Idx D j N) (X.Ol la)

theorem tayPol_iterAt (p : Idx D j N) (x : Pol X la N) : Tay.IterAt (tayPol X la N) p x := Tay.pol_iterAt (Idx D j N) (X.Ol la) p x

def tayOp : Op X la N →+* MvPowerSeries (Idx D j N) (Op X la N) :=
  Tay.loc (gI X la N).primeCompl (Op X la N) (tayPol X la N) (tayPol_isTay X la N)

theorem tayOp_isTay : Tay.IsTay (tayOp X la N) := Tay.loc_isTay (gI X la N).primeCompl (Op X la N) (tayPol X la N) (tayPol_isTay X la N)

theorem tayOp_iterAt (p : Idx D j N) (x : Op X la N) : Tay.IterAt (tayOp X la N) p x := Tay.loc_iterAt (gI X la N).primeCompl (Op X la N) (tayPol X la N) (tayPol_isTay X la N)
    (tayPol_iterAt X la N p) x

theorem tayOp_isCst (a : X.Ol la) : Tay.IsCst (tayOp X la N) (algebraMap (X.Ol la) (Op X la N) a) := by
  have e : algebraMap (X.Ol la) (Op X la N) a = algebraMap (Pol X la N) (Op X la N) (algebraMap (X.Ol la) (Pol X la N) a) := by
    first | exact IsScalarTower.algebraMap_apply _ _ _ _ | rfl
  rw [e]
  exact Tay.loc_isCst (gI X la N).primeCompl (Op X la N) (tayPol X la N) (tayPol_isTay X la N)
    (Tay.pol_isCst (Idx D j N) (X.Ol la) a)

def tayKp : Kp X la N →+* MvPowerSeries (Idx D j N) (Kp X la N) :=
  Tay.loc (nonZeroDivisors (Op X la N)) (Kp X la N) (tayOp X la N) (tayOp_isTay X la N)

theorem tayKp_isTay : Tay.IsTay (tayKp X la N) := Tay.loc_isTay (nonZeroDivisors (Op X la N)) (Kp X la N) (tayOp X la N) (tayOp_isTay X la N)

theorem tayKp_iterAt (p : Idx D j N) (x : Kp X la N) : Tay.IterAt (tayKp X la N) p x := Tay.loc_iterAt (nonZeroDivisors (Op X la N)) (Kp X la N) (tayOp X la N) (tayOp_isTay X la N)
    (tayOp_iterAt X la N p) x

theorem tayKp_isCst_Ol (a : X.Ol la) : Tay.IsCst (tayKp X la N) (algebraMap (X.Ol la) (Kp X la N) a) := by
  have e : algebraMap (X.Ol la) (Kp X la N) a = algebraMap (Op X la N) (Kp X la N) (algebraMap (X.Ol la) (Op X la N) a) := by
    first | exact IsScalarTower.algebraMap_apply _ _ _ _ | rfl
  rw [e]
  exact Tay.loc_isCst (nonZeroDivisors (Op X la N)) (Kp X la N) (tayOp X la N) (tayOp_isTay X la N)
    (tayOp_isCst X la N a)

theorem tayKp_isCst (c : X.Kl la) : Tay.IsCst (tayKp X la N) (algebraMap (X.Kl la) (Kp X la N) c) := by
  have key : (tayKp X la N).comp (algebraMap (X.Kl la) (Kp X la N)) =
      (MvPowerSeries.C : Kp X la N →+* MvPowerSeries (Idx D j N) (Kp X la N)).comp (algebraMap (X.Kl la) (Kp X la N)) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (X.Ol la))
    refine RingHom.ext fun a => ?_
    simp only [RingHom.comp_apply]
    have e : algebraMap (X.Kl la) (Kp X la N) (algebraMap (X.Ol la) (X.Kl la) a) = algebraMap (X.Ol la) (Kp X la N) a := by
      first | exact IsFractionRing.lift_algebraMap _ _ | exact (IsScalarTower.algebraMap_apply _ _ _ _).symm
    rw [e]
    exact tayKp_isCst_Ol X la N a
  exact RingHom.congr_fun key c

def tayRp : Rp X la N →+* MvPowerSeries (Idx D j N) (Rp X la N) :=
  (Tay.tens (X.Kl la) (X.Vl la) (tayKp X la N) (tayKp_isCst X la N)).toRingHom

theorem tayRp_isTay : Tay.IsTay (tayRp X la N) := Tay.tens_isTay (X.Kl la) (X.Vl la) (tayKp X la N) (tayKp_isTay X la N) (tayKp_isCst X la N)

theorem tayRp_iterAt (p : Idx D j N) (x : Rp X la N) : Tay.IterAt (tayRp X la N) p x := Tay.tens_iterAt (X.Kl la) (X.Vl la) (tayKp X la N) (tayKp_isTay X la N) (tayKp_isCst X la N)
    (tayKp_iterAt X la N p) x

theorem tayRp_isCst (c : X.Kl la) : Tay.IsCst (tayRp X la N) (algebraMap (X.Kl la) (Rp X la N) c) := Tay.tens_isCst_algebraMap (X.Kl la) (X.Vl la) (tayKp X la N) (tayKp_isCst X la N) c

theorem tayRp_isCst_bcV (v : X.Vl la) : Tay.IsCst (tayRp X la N) (bcV X la N v) := Tay.tens_isCst_right (X.Kl la) (X.Vl la) (tayKp X la N) (tayKp_isCst X la N) v

end

section
variable (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) {N : ℕ} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)

abbrev Lc : Type := Localization.Away (sec X la w 0)

def tayLc : Lc X la w →+* MvPowerSeries (Idx D j N) (Lc X la w) :=
  Tay.loc (Submonoid.powers (sec X la w 0)) (Lc X la w) (tayRp X la N) (tayRp_isTay X la N)

theorem tayLc_isTay : Tay.IsTay (tayLc X la w) := Tay.loc_isTay (Submonoid.powers (sec X la w 0)) (Lc X la w) (tayRp X la N) (tayRp_isTay X la N)

theorem tayLc_iterAt (p : Idx D j N) (x : Lc X la w) : Tay.IterAt (tayLc X la w) p x := Tay.loc_iterAt (Submonoid.powers (sec X la w 0)) (Lc X la w) (tayRp X la N) (tayRp_isTay X la N)
    (tayRp_iterAt X la N p) x

theorem tayLc_isCst (c : X.Kl la) : Tay.IsCst (tayLc X la w) (algebraMap (X.Kl la) (Lc X la w) c) := by
  have e : algebraMap (X.Kl la) (Lc X la w) c = algebraMap (Rp X la N) (Lc X la w) (algebraMap (X.Kl la) (Rp X la N) c) := by
    first | exact IsScalarTower.algebraMap_apply _ _ _ _ | rfl
  rw [e]
  exact Tay.loc_isCst (Submonoid.powers (sec X la w 0)) (Lc X la w) (tayRp X la N) (tayRp_isTay X la N)
    (tayRp_isCst X la N c)

theorem tayLc_isCst_bcV (v : X.Vl la) : Tay.IsCst (tayLc X la w) (algebraMap (Rp X la N) (Lc X la w) (bcV X la N v)) := Tay.loc_isCst (Submonoid.powers (sec X la w 0)) (Lc X la w) (tayRp X la N) (tayRp_isTay X la N)
    (tayRp_isCst_bcV X la N v)

end

section
variable (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ)

def pdOp (p : Idx D j N) : Derivation (X.Ol la) (Op X la N) (Op X la N) :=
  Tay.der (X.Ol la) (tayOp X la N) (tayOp_isTay X la N) (tayOp_isCst X la N) p

def pdKp (p : Idx D j N) : Derivation (X.Kl la) (Kp X la N) (Kp X la N) :=
  Tay.der (X.Kl la) (tayKp X la N) (tayKp_isTay X la N) (tayKp_isCst X la N) p

def pdRp (p : Idx D j N) : Derivation (X.Kl la) (Rp X la N) (Rp X la N) :=
  Tay.der (X.Kl la) (tayRp X la N) (tayRp_isTay X la N) (tayRp_isCst X la N) p

def hasseOp (β : Idx D j N →₀ ℕ) : Op X la N →ₗ[X.Ol la] Op X la N :=
  Tay.hs (X.Ol la) (tayOp X la N) (tayOp_isCst X la N) β

def hasseKp (β : Idx D j N →₀ ℕ) : Kp X la N →ₗ[X.Kl la] Kp X la N :=
  Tay.hs (X.Kl la) (tayKp X la N) (tayKp_isCst X la N) β

def hasseRp (β : Idx D j N →₀ ℕ) : Rp X la N →ₗ[X.Kl la] Rp X la N :=
  Tay.hs (X.Kl la) (tayRp X la N) (tayRp_isCst X la N) β

variable {N}

theorem hasseOp_single (p : Idx D j N) (x : Op X la N) : hasseOp X la N (Finsupp.single p 1) x = pdOp X la N p x := rfl

theorem hasseOp_zero (x : Op X la N) : hasseOp X la N 0 x = x := Tay.co_zero (tayOp_isTay X la N) x

theorem hasseOp_mul (β : Idx D j N →₀ ℕ) (x y : Op X la N) : hasseOp X la N β (x * y) =
    ∑ q ∈ antidiagonal β, hasseOp X la N q.1 x * hasseOp X la N q.2 y := Tay.co_mul (tayOp X la N) β x y

theorem pdOp_hasseOp (p : Idx D j N) (β : Idx D j N →₀ ℕ) (x : Op X la N) :
    pdOp X la N p (hasseOp X la N β x) = (β p + 1) • hasseOp X la N (β + Finsupp.single p 1) x := Tay.dv_co (tayOp_iterAt X la N) p β x

theorem pdOp_algebraMap (p : Idx D j N) (f : Pol X la N) :
    pdOp X la N p (algebraMap (Pol X la N) (Op X la N) f) =
      algebraMap (Pol X la N) (Op X la N) (MvPolynomial.pderiv p f) := by
  rw [pdOp, Tay.der_apply, tayOp, Tay.loc_dv]
  exact congrArg _ (DFunLike.congr_fun (Tay.pol_der (Idx D j N) (X.Ol la) p) f)

theorem tayOp_Tv (q : Idx D j N) : tayOp X la N (Tv X la N q) = MvPowerSeries.C (Tv X la N q) + MvPowerSeries.X q := by
  show tayOp X la N (algebraMap (Pol X la N) (Op X la N) (MvPolynomial.X q)) = _
  rw [tayOp, Tay.loc_algebraMap, tayPol, Tay.pol_X, map_add, MvPowerSeries.map_C, MvPowerSeries.map_X] <;> rfl

theorem hasseOp_Tv (β : Idx D j N →₀ ℕ) (q : Idx D j N) : hasseOp X la N β (Tv X la N q) =
    if β = 0 then Tv X la N q else if β = Finsupp.single q 1 then 1 else 0 := by
  rw [hasseOp, Tay.hs_apply, Tay.co_apply, tayOp_Tv, map_add, MvPowerSeries.coeff_C, MvPowerSeries.coeff_X]
  by_cases h0 : β = 0
  · subst h0
    have h1 : (0 : Idx D j N →₀ ℕ) ≠ Finsupp.single q 1 := fun h => Finsupp.single_ne_zero.mpr one_ne_zero h.symm
    simp [h1]
  · simp [h0]

theorem pdOp_Tv (p q : Idx D j N) : pdOp X la N p (Tv X la N q) = if p = q then 1 else 0 := by
  rw [← hasseOp_single, hasseOp_Tv, if_neg (Finsupp.single_ne_zero.mpr one_ne_zero)]
  by_cases h : p = q
  · subst h; simp
  · rw [if_neg h, if_neg]; exact fun h' => h (Finsupp.single_left_injective one_ne_zero h')

theorem hasseKp_single (p : Idx D j N) (x : Kp X la N) : hasseKp X la N (Finsupp.single p 1) x = pdKp X la N p x := rfl

theorem hasseKp_zero (x : Kp X la N) : hasseKp X la N 0 x = x := Tay.co_zero (tayKp_isTay X la N) x

theorem hasseKp_mul (β : Idx D j N →₀ ℕ) (x y : Kp X la N) : hasseKp X la N β (x * y) =
    ∑ q ∈ antidiagonal β, hasseKp X la N q.1 x * hasseKp X la N q.2 y := Tay.co_mul (tayKp X la N) β x y

theorem pdKp_hasseKp (p : Idx D j N) (β : Idx D j N →₀ ℕ) (x : Kp X la N) :
    pdKp X la N p (hasseKp X la N β x) = (β p + 1) • hasseKp X la N (β + Finsupp.single p 1) x := Tay.dv_co (tayKp_iterAt X la N) p β x

theorem hasseKp_algebraMap (β : Idx D j N →₀ ℕ) (x : Op X la N) :
    hasseKp X la N β (algebraMap (Op X la N) (Kp X la N) x) =
      algebraMap (Op X la N) (Kp X la N) (hasseOp X la N β x) := Tay.loc_co (nonZeroDivisors (Op X la N)) (Kp X la N) (tayOp X la N) (tayOp_isTay X la N) β x

theorem pdKp_algebraMap (p : Idx D j N) (x : Op X la N) :
    pdKp X la N p (algebraMap (Op X la N) (Kp X la N) x) = algebraMap (Op X la N) (Kp X la N) (pdOp X la N p x) := Tay.loc_dv (nonZeroDivisors (Op X la N)) (Kp X la N) (tayOp X la N) (tayOp_isTay X la N) p x

theorem hasseKp_algebraMap_Kl {β : Idx D j N →₀ ℕ} (hβ : β ≠ 0) (c : X.Kl la) :
    hasseKp X la N β (algebraMap (X.Kl la) (Kp X la N) c) = 0 := (tayKp_isCst X la N c).co hβ

theorem hasseRp_single (p : Idx D j N) (x : Rp X la N) : hasseRp X la N (Finsupp.single p 1) x = pdRp X la N p x := rfl

theorem hasseRp_zero (x : Rp X la N) : hasseRp X la N 0 x = x := Tay.co_zero (tayRp_isTay X la N) x

theorem hasseRp_mul (β : Idx D j N →₀ ℕ) (x y : Rp X la N) : hasseRp X la N β (x * y) =
    ∑ q ∈ antidiagonal β, hasseRp X la N q.1 x * hasseRp X la N q.2 y := Tay.co_mul (tayRp X la N) β x y

theorem pdRp_hasseRp (p : Idx D j N) (β : Idx D j N →₀ ℕ) (x : Rp X la N) :
    pdRp X la N p (hasseRp X la N β x) = (β p + 1) • hasseRp X la N (β + Finsupp.single p 1) x := Tay.dv_co (tayRp_iterAt X la N) p β x

theorem hasseRp_tmul (β : Idx D j N →₀ ℕ) (k : Kp X la N) (v : X.Vl la) :
    hasseRp X la N β (k ⊗ₜ[X.Kl la] v : Kp X la N ⊗[X.Kl la] X.Vl la) =
      (hasseKp X la N β k ⊗ₜ[X.Kl la] v : Kp X la N ⊗[X.Kl la] X.Vl la) := Tay.tens_co_tmul (X.Kl la) (X.Vl la) (tayKp X la N) (tayKp_isCst X la N) β k v

theorem hasseRp_eq_rTensor (β : Idx D j N →₀ ℕ) :
    hasseRp X la N β = LinearMap.rTensor (X.Vl la) (hasseKp X la N β) := by
  refine TensorProduct.ext' fun k v => ?_
  exact hasseRp_tmul X la β k v

theorem hasseRp_smul_bcV (β : Idx D j N →₀ ℕ) (k : Kp X la N) (v : X.Vl la) :
    hasseRp X la N β (k • bcV X la N v) = hasseKp X la N β k • bcV X la N v := by
  have e : k • bcV X la N v = (k ⊗ₜ[X.Kl la] v : Kp X la N ⊗[X.Kl la] X.Vl la) := by
    first
      | (rw [Algebra.smul_def]; show (k ⊗ₜ[X.Kl la] (1 : X.Vl la)) * ((1 : Kp X la N) ⊗ₜ[X.Kl la] v) = _; simp)
      | (show k • ((1 : Kp X la N) ⊗ₜ[X.Kl la] v) = _; rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one])
      | rfl
  rw [e]
  refine (hasseRp_tmul X la β k v).trans ?_
  first
    | (rw [Algebra.smul_def]; show _ = (hasseKp X la N β k ⊗ₜ[X.Kl la] (1 : X.Vl la)) * ((1 : Kp X la N) ⊗ₜ[X.Kl la] v); simp)
    | (show _ = hasseKp X la N β k • ((1 : Kp X la N) ⊗ₜ[X.Kl la] v); rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one])
    | exact e.symm.trans rfl
    | rfl

theorem hasseRp_algebraMap (β : Idx D j N →₀ ℕ) (k : Kp X la N) :
    hasseRp X la N β (algebraMap (Kp X la N) (Rp X la N) k) =
      algebraMap (Kp X la N) (Rp X la N) (hasseKp X la N β k) := by
  first
    | exact hasseRp_tmul X la β k 1
    | (show hasseRp X la N β (k ⊗ₜ[X.Kl la] (1 : X.Vl la) : Kp X la N ⊗[X.Kl la] X.Vl la) =
        (hasseKp X la N β k ⊗ₜ[X.Kl la] (1 : X.Vl la) : Kp X la N ⊗[X.Kl la] X.Vl la)
       exact hasseRp_tmul X la β k 1)

theorem hasseRp_smul (β : Idx D j N →₀ ℕ) (k : Kp X la N) (x : Rp X la N) : hasseRp X la N β (k • x) =
    ∑ q ∈ antidiagonal β, hasseKp X la N q.1 k • hasseRp X la N q.2 x := by
  rw [Algebra.smul_def, hasseRp_mul]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [hasseRp_algebraMap, ← Algebra.smul_def]

theorem hasseRp_bcV {β : Idx D j N →₀ ℕ} (hβ : β ≠ 0) (v : X.Vl la) : hasseRp X la N β (bcV X la N v) = 0 := (tayRp_isCst_bcV X la N v).co hβ

theorem hasseRp_emb {β : Idx D j N →₀ ℕ} (hβ : β ≠ 0) (F : X.Forms) : hasseRp X la N β (emb X la N F) = 0 := by
  rw [show emb X la N F = bcV X la N ((1 : X.Kl la) ⊗ₜ[B.KO] F) from rfl]
  exact hasseRp_bcV X la hβ _

theorem hasseRp_bcV_mul (β : Idx D j N →₀ ℕ) (v : X.Vl la) (x : Rp X la N) :
    hasseRp X la N β (bcV X la N v * x) = bcV X la N v * hasseRp X la N β x := (tayRp_isCst_bcV X la N v).co_mul β x

theorem pdRp_bcV (p : Idx D j N) (v : X.Vl la) : pdRp X la N p (bcV X la N v) = 0 := (tayRp_isCst_bcV X la N v).dv p

theorem pdRp_emb (p : Idx D j N) (F : X.Forms) : pdRp X la N p (emb X la N F) = 0 := by
  rw [show emb X la N F = bcV X la N ((1 : X.Kl la) ⊗ₜ[B.KO] F) from rfl]
  exact pdRp_bcV X la p _

theorem pdRp_algebraMap (p : Idx D j N) (k : Kp X la N) :
    pdRp X la N p (algebraMap (Kp X la N) (Rp X la N) k) = algebraMap (Kp X la N) (Rp X la N) (pdKp X la N p k) := hasseRp_algebraMap X la (Finsupp.single p 1) k

end

section
variable (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) {N : ℕ}

theorem tayRp_isCst_emb (F : X.Forms) : Tay.IsCst (tayRp X la N) (emb X la N F) := by
  rw [show emb X la N F = bcV X la N ((1 : X.Kl la) ⊗ₜ[B.KO] F) from rfl]
  exact tayRp_isCst_bcV X la N _

theorem hasseRp_smul_Op (β : Idx D j N →₀ ℕ) (a : Op X la N) (x : Rp X la N) : hasseRp X la N β (a • x) =
    ∑ q ∈ antidiagonal β, hasseOp X la N q.1 a • hasseRp X la N q.2 x := by
  rw [← algebraMap_smul (Kp X la N) a x, hasseRp_smul]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [hasseKp_algebraMap, algebraMap_smul]

theorem hasseRp_of_isCst {t : Rp X la N} (ht : Tay.IsCst (tayRp X la N) t) (β : Idx D j N →₀ ℕ) :
    hasseRp X la N β t = if β = 0 then t else 0 := by
  split_ifs with h
  · subst h; exact hasseRp_zero X la t
  · exact ht.co h

theorem hasseRp_mem_span_Kp {T : Set (Rp X la N)} (hT : ∀ t ∈ T, Tay.IsCst (tayRp X la N) t) {x : Rp X la N}
    (hx : x ∈ Submodule.span (Kp X la N) T) (β : Idx D j N →₀ ℕ) :
    hasseRp X la N β x ∈ Submodule.span (Kp X la N) T := by
  induction hx using Submodule.span_induction generalizing β with
  | mem t ht =>
    rw [hasseRp_of_isCst X la (hT t ht)]
    split_ifs
    · exact Submodule.subset_span ht
    · exact zero_mem _
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem (hx β) (hy β)
  | smul k x _ hx =>
    rw [hasseRp_smul]
    exact Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (hx q.2)

theorem hasseRp_mem_span_Op {T : Set (Rp X la N)} (hT : ∀ t ∈ T, Tay.IsCst (tayRp X la N) t) {x : Rp X la N}
    (hx : x ∈ Submodule.span (Op X la N) T) (β : Idx D j N →₀ ℕ) :
    hasseRp X la N β x ∈ Submodule.span (Op X la N) T := by
  induction hx using Submodule.span_induction generalizing β with
  | mem t ht =>
    rw [hasseRp_of_isCst X la (hT t ht)]
    split_ifs
    · exact Submodule.subset_span ht
    · exact zero_mem _
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem (hx β) (hy β)
  | smul k x _ hx =>
    rw [hasseRp_smul_Op]
    exact Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (hx q.2)

theorem hasseRp_mem_Vw {u : WeightFamilies.Wt D j} {x : Rp X la N} (hx : x ∈ Vw X la N u) (β : Idx D j N →₀ ℕ) :
    hasseRp X la N β x ∈ Vw X la N u := by
  have hT : ∀ t ∈ Set.range (fun F : B.Cusp j u => emb X la N (X.inc u F)), Tay.IsCst (tayRp X la N) t := by
    rintro t ⟨F, rfl⟩
    exact tayRp_isCst_emb X la _
  exact hasseRp_mem_span_Kp X la hT hx β

end

section
variable (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) {N : ℕ} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)

theorem hasseRp_sec (β : Idx D j N →₀ ℕ) (i : Fin (WeightFamilies.dimY D j + 1)) : hasseRp X la N β (sec X la w i) =
    ∑ k, algebraMap (Op X la N) (Kp X la N) (hasseOp X la N β (Tv X la N (i, k))) • emb X la N (X.inc wL (w k)) := by
  show hasseRp X la N β (∑ k, algebraMap (Op X la N) (Kp X la N) (Tv X la N (i, k)) • emb X la N (X.inc wL (w k))) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show emb X la N (X.inc wL (w k)) = bcV X la N ((1 : X.Kl la) ⊗ₜ[B.KO] (X.inc wL (w k))) from rfl, hasseRp_smul_bcV, hasseKp_algebraMap]

theorem pdRp_sec (p : Idx D j N) (i : Fin (WeightFamilies.dimY D j + 1)) :
    pdRp X la N p (sec X la w i) = if p.1 = i then emb X la N (X.inc wL (w p.2)) else 0 := by
  rw [← hasseRp_single, hasseRp_sec]
  simp only [hasseOp_single, pdOp_Tv]
  obtain ⟨i', k'⟩ := p
  by_cases hi : i' = i
  · subst hi
    rw [Finset.sum_eq_single k']
    · simp
    · intro b _ hb; simp [Prod.ext_iff, Ne.symm hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  · simp [Prod.ext_iff, hi]

theorem hasseRp_sec_eq_zero {β : Idx D j N →₀ ℕ} (h0 : β ≠ 0) (h1 : ∀ p, β ≠ Finsupp.single p 1)
    (i : Fin (WeightFamilies.dimY D j + 1)) : hasseRp X la N β (sec X la w i) = 0 := by
  rw [hasseRp_sec]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [hasseOp_Tv, if_neg h0, if_neg (h1 _), map_zero, zero_smul]

def pdLc (p : Idx D j N) : Derivation (X.Kl la) (Lc X la w) (Lc X la w) :=
  Tay.der (X.Kl la) (tayLc X la w) (tayLc_isTay X la w) (tayLc_isCst X la w) p

def hasse (β : Idx D j N →₀ ℕ) : Lc X la w →ₗ[X.Kl la] Lc X la w :=
  Tay.hs (X.Kl la) (tayLc X la w) (tayLc_isCst X la w) β

theorem hasse_single (p : Idx D j N) (x : Lc X la w) : hasse X la w (Finsupp.single p 1) x = pdLc X la w p x := rfl

theorem hasse_zero (x : Lc X la w) : hasse X la w 0 x = x := Tay.co_zero (tayLc_isTay X la w) x

theorem hasse_zero' : hasse X la w 0 = LinearMap.id := LinearMap.ext (hasse_zero X la w)

theorem hasse_mul (β : Idx D j N →₀ ℕ) (x y : Lc X la w) : hasse X la w β (x * y) =
    ∑ q ∈ antidiagonal β, hasse X la w q.1 x * hasse X la w q.2 y := Tay.co_mul (tayLc X la w) β x y

theorem pdLc_hasse (p : Idx D j N) (β : Idx D j N →₀ ℕ) (x : Lc X la w) :
    pdLc X la w p (hasse X la w β x) = (β p + 1) • hasse X la w (β + Finsupp.single p 1) x := Tay.dv_co (tayLc_iterAt X la w) p β x

theorem pdLc_comm (p q : Idx D j N) (x : Lc X la w) :
    pdLc X la w p (pdLc X la w q x) = pdLc X la w q (pdLc X la w p x) := Tay.dv_comm (tayLc_iterAt X la w) p q x

theorem hasse_algebraMap (β : Idx D j N →₀ ℕ) (x : Rp X la N) :
    hasse X la w β (algebraMap (Rp X la N) (Lc X la w) x) = algebraMap (Rp X la N) (Lc X la w) (hasseRp X la N β x) := Tay.loc_co (Submonoid.powers (sec X la w 0)) (Lc X la w) (tayRp X la N) (tayRp_isTay X la N) β x

theorem pdLc_algebraMap (p : Idx D j N) (x : Rp X la N) :
    pdLc X la w p (algebraMap (Rp X la N) (Lc X la w) x) = algebraMap (Rp X la N) (Lc X la w) (pdRp X la N p x) := Tay.loc_dv (Submonoid.powers (sec X la w 0)) (Lc X la w) (tayRp X la N) (tayRp_isTay X la N) p x

theorem hasse_bcV {β : Idx D j N →₀ ℕ} (hβ : β ≠ 0) (v : X.Vl la) :
    hasse X la w β (algebraMap (Rp X la N) (Lc X la w) (bcV X la N v)) = 0 := by
  rw [hasse_algebraMap, hasseRp_bcV X la hβ, map_zero]

theorem hasse_emb {β : Idx D j N →₀ ℕ} (hβ : β ≠ 0) (F : X.Forms) :
    hasse X la w β (algebraMap (Rp X la N) (Lc X la w) (emb X la N F)) = 0 := by
  rw [hasse_algebraMap, hasseRp_emb X la hβ, map_zero]

theorem pdLc_emb (p : Idx D j N) (F : X.Forms) :
    pdLc X la w p (algebraMap (Rp X la N) (Lc X la w) (emb X la N F)) = 0 := by
  rw [pdLc_algebraMap, pdRp_emb, map_zero]

theorem hasse_bcV_mul (β : Idx D j N →₀ ℕ) (v : X.Vl la) (x : Lc X la w) :
    hasse X la w β (algebraMap (Rp X la N) (Lc X la w) (bcV X la N v) * x) =
      algebraMap (Rp X la N) (Lc X la w) (bcV X la N v) * hasse X la w β x := (tayLc_isCst_bcV X la w v).co_mul β x

theorem hasse_algebraMap_Op (β : Idx D j N →₀ ℕ) (x : Op X la N) :
    hasse X la w β (algebraMap (Rp X la N) (Lc X la w) (algebraMap (Op X la N) (Rp X la N) x)) =
      algebraMap (Rp X la N) (Lc X la w) (algebraMap (Op X la N) (Rp X la N) (hasseOp X la N β x)) := by
  rw [hasse_algebraMap, IsScalarTower.algebraMap_apply (Op X la N) (Kp X la N) (Rp X la N) x,
    hasseRp_algebraMap, hasseKp_algebraMap, ← IsScalarTower.algebraMap_apply (Op X la N) (Kp X la N) (Rp X la N)]

theorem hasse_of_mul_eq (β : Idx D j N →₀ ℕ) {s x : Rp X la N} {y : Lc X la w}
    (h : algebraMap (Rp X la N) (Lc X la w) s * y = algebraMap (Rp X la N) (Lc X la w) x) :
    ∑ q ∈ antidiagonal β, algebraMap (Rp X la N) (Lc X la w) (hasseRp X la N q.1 s) * hasse X la w q.2 y =
      algebraMap (Rp X la N) (Lc X la w) (hasseRp X la N β x) := by
  have key := congrArg (fun z => hasse X la w β z) h
  simp only [hasse_mul, hasse_algebraMap] at key
  exact key

@[instance_reducible] def Lc.algVl : Algebra (X.Vl la) (Lc X la w) :=
  ((algebraMap (Rp X la N) (Lc X la w)).comp (bcV X la N).toRingHom).toAlgebra

def hasseV (β : Idx D j N →₀ ℕ) :
    letI := Lc.algVl X la w
    Lc X la w →ₗ[X.Vl la] Lc X la w :=
  letI := Lc.algVl X la w
  Tay.hs (X.Vl la) (tayLc X la w) (tayLc_isCst_bcV X la w) β

theorem hasseV_apply (β : Idx D j N →₀ ℕ) (x : Lc X la w) :
    letI := Lc.algVl X la w
    hasseV X la w β x = hasse X la w β x := rfl

def iterPd (β : Idx D j N →₀ ℕ) : Module.End (X.Kl la) (Lc X la w) :=
  Tay.itD (X.Kl la) (tayLc_iterAt X la w) (tayLc_isCst X la w) Finset.univ β

theorem iterPd_eq (β : Idx D j N →₀ ℕ) : iterPd X la w β =
    Finset.univ.noncommProd (fun p => ((pdLc X la w p : Lc X la w →ₗ[X.Kl la] Lc X la w) :
      Module.End (X.Kl la) (Lc X la w)) ^ β p)
      (fun p _ q _ _ => Commute.pow_pow (LinearMap.ext fun x => pdLc_comm X la w p q x) _ _) := rfl

theorem iterPd_apply (β : Idx D j N →₀ ℕ) (x : Lc X la w) :
    iterPd X la w β x = (∏ p, (β p).factorial) • hasse X la w β x := Tay.itD_apply (X.Kl la) (tayLc_isTay X la w) (tayLc_iterAt X la w) (tayLc_isCst X la w)
    Finset.univ β (Finset.subset_univ _) x

theorem Kl_charZero : CharZero (X.Kl la) := by
  first
    | infer_instance
    | exact charZero_of_injective_algebraMap (algebraMap B.KO (X.Kl la)).injective

theorem hasse_eq (β : Idx D j N →₀ ℕ) (x : Lc X la w) :
    hasse X la w β x = ((∏ p, (β p).factorial : ℕ) : X.Kl la)⁻¹ • iterPd X la w β x := by
  haveI := Kl_charZero X la
  rw [iterPd_apply, ← Nat.cast_smul_eq_nsmul (X.Kl la), smul_smul, inv_mul_cancel₀, one_smul]
  exact Nat.cast_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun p _ => Nat.factorial_ne_zero (β p))

end

section
variable (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) {N : ℕ} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)

theorem pdLc_mk' (p : Idx D j N) (x : Rp X la N) (s : Submonoid.powers (sec X la w 0)) :
    algebraMap (Rp X la N) (Lc X la w) (s * s) * pdLc X la w p (IsLocalization.mk' (Lc X la w) x s) =
      algebraMap (Rp X la N) (Lc X la w) (s * pdRp X la N p x - x * pdRp X la N p s) := by
  have h1 : algebraMap (Rp X la N) (Lc X la w) s * IsLocalization.mk' (Lc X la w) x s =
      algebraMap (Rp X la N) (Lc X la w) x := IsLocalization.mk'_spec' _ _ _
  have h2 := congrArg (fun z => pdLc X la w p z) h1
  simp only [Derivation.leibniz, pdLc_algebraMap, smul_eq_mul] at h2
  simp only [map_mul, map_sub, Submonoid.coe_mul]
  linear_combination (algebraMap (Rp X la N) (Lc X la w) s) * h2 -
    (algebraMap (Rp X la N) (Lc X la w) (pdRp X la N p s)) * h1

end

end Formalism.MainNotions.Gaps.EtaleWeightGaps
