import Mathlib

namespace GlobalTheory.CMNorm

open Matrix

variable {A R Λ : Type} [CommRing A] [CommRing R] [CommRing Λ] [Algebra A R]

theorem span_ind (ι : Λ →+* R) (hspan : Submodule.span A (Set.range ι) = ⊤) {p : R → Prop}
    (h0 : p 0) (hadd : ∀ x y, p x → p y → p (x + y)) (hsmul : ∀ (a : A) x, p x → p (a • x))
    (hι : ∀ a, p (ι a)) (r : R) : p r := by
  let S : Submodule A R :=
    { carrier := {r | p r}
      add_mem' := fun {x y} hx hy => hadd x y hx hy
      zero_mem' := h0
      smul_mem' := fun a x hx => hsmul a x hx }
  have hle : Submodule.span A (Set.range ι) ≤ S :=
    Submodule.span_le.mpr (by rintro _ ⟨a, rfl⟩; exact hι a)
  exact hle (hspan ▸ Submodule.mem_top)

theorem map_smul_of_iota (ι : Λ →+* R) (hspan : Submodule.span A (Set.range ι) = ⊤)
    {X Y : Type} [AddCommGroup X] [Module A X] [Module R X] [IsScalarTower A R X]
    [AddCommGroup Y] [Module A Y] [Module R Y] [IsScalarTower A R Y]
    (F : X →ₗ[A] Y) (hF : ∀ a x, F (ι a • x) = ι a • F x) (r : R) (x : X) :
    F (r • x) = r • F x := by
  refine span_ind ι hspan (p := fun r => F (r • x) = r • F x) (by simp) ?_ ?_ (fun a => hF a x) r
  · intro u v hu hv; simp [add_smul, hu, hv]
  · intro a u hu; simp only [smul_assoc, map_smul, hu]

theorem invol (ι : Λ →+* R) (hspan : Submodule.span A (Set.range ι) = ⊤) (c : Λ →+* Λ)
    (cR : R →ₐ[A] R) (hc : ∀ a, cR (ι a) = ι (c a)) (hcc : ∀ a, c (c a) = a) (r : R) :
    cR (cR r) = r := by
  refine span_ind ι hspan (p := fun r => cR (cR r) = r) (by simp) ?_ ?_ ?_ r
  · intro u v hu hv; simp [hu, hv]
  · intro a u hu; simp [hu]
  · intro a; simp [hc, hcc]

theorem adj (ι : Λ →+* R) (hspan : Submodule.span A (Set.range ι) = ⊤) (c : Λ →+* Λ)
    (cR : R →ₐ[A] R) (hc : ∀ a, cR (ι a) = ι (c a))
    {κ T : Type} [AddCommGroup T] [Module A T] (ρ : Λ →+* Module.End A T)
    (e : LinearMap.BilinForm A T) (hadj : ∀ a x y, e (ρ a x) y = e x (ρ (c a) y))
    (f : (κ → R) ≃ₗ[A] T) (hf : ∀ a r, f (ι a • r) = ρ a (f r)) (r : R) (x y : κ → R) :
    e (f (r • x)) (f y) = e (f x) (f (cR r • y)) := by
  refine span_ind ι hspan (p := fun r => e (f (r • x)) (f y) = e (f x) (f (cR r • y)))
    (by simp) ?_ ?_ ?_ r
  · intro u v hu hv; simp [add_smul, hu, hv]
  · intro a u hu; simp [smul_assoc, hu]
  · intro a; rw [hf, hadj, hc, hf]

theorem unit_vec (x : Unit → R) : x = x () • (1 : Unit → R) := by
  funext u; cases u; simp

def lam {T₁ : Type} [AddCommGroup T₁] [Module A T₁] (e₁ : LinearMap.BilinForm A T₁)
    (f₁ : (Unit → R) ≃ₗ[A] T₁) : R →ₗ[A] A where
  toFun r := e₁ (f₁ (r • (1 : Unit → R))) (f₁ 1)
  map_add' x y := by simp [add_smul]
  map_smul' a x := by simp [smul_assoc]

theorem lam_apply {T₁ : Type} [AddCommGroup T₁] [Module A T₁] (e₁ : LinearMap.BilinForm A T₁)
    (f₁ : (Unit → R) ≃ₗ[A] T₁) (r : R) : lam e₁ f₁ r = e₁ (f₁ (r • (1 : Unit → R))) (f₁ 1) := rfl

end GlobalTheory.CMNorm

namespace GlobalTheory.CMNorm

variable {A R Λ : Type} [CommRing A] [CommRing R] [CommRing Λ] [Algebra A R]

section abelian₂
variable (ι : Λ →+* R) (hspan : Submodule.span A (Set.range ι) = ⊤) (c : Λ →+* Λ)
    (cR : R →ₐ[A] R) (hc : ∀ a, cR (ι a) = ι (c a)) (hcc : ∀ a, c (c a) = a)
    {T₁ : Type} [AddCommGroup T₁] [Module A T₁] (ρ₁ : Λ →+* Module.End A T₁)
    (e₁ : LinearMap.BilinForm A T₁) (he₁ : Function.Bijective e₁)
    (hadj₁ : ∀ a x y, e₁ (ρ₁ a x) y = e₁ x (ρ₁ (c a) y))
    (f₁ : (Unit → R) ≃ₗ[A] T₁) (hf₁ : ∀ a r, f₁ (ι a • r) = ρ₁ a (f₁ r))
include hspan hc hcc hadj₁ hf₁

theorem lam_pair (t s : R) :
    e₁ (f₁ (t • (1 : Unit → R))) (f₁ (s • 1)) = lam e₁ f₁ (cR s * t) := by
  rw [lam_apply, ← smul_smul, adj ι hspan c cR hc ρ₁ e₁ hadj₁ f₁ hf₁ (cR s) (t • 1) 1, invol ι hspan c cR hc hcc]

include he₁ in
theorem lam_inj (t : R) (h : ∀ r, lam e₁ f₁ (r * t) = 0) : t = 0 := by
  have h0 : e₁ (f₁ (t • (1 : Unit → R))) = 0 := by
    ext z
    rw [← f₁.apply_symm_apply z, unit_vec (f₁.symm z), lam_pair ι hspan c cR hc hcc ρ₁ e₁ hadj₁ f₁ hf₁, h]
    simp
  have h1 : f₁ (t • (1 : Unit → R)) = 0 := he₁.1 (by rw [h0, map_zero])
  have h2 : t • (1 : Unit → R) = 0 := by simpa using h1
  simpa using congrFun h2 ()

include he₁ in
theorem lam_onto (g : R →ₗ[A] A) : ∃ t, ∀ r, g r = lam e₁ f₁ (r * t) := by
  obtain ⟨x, hx⟩ := he₁.2 ((g.comp cR.toLinearMap).comp
    ((LinearMap.proj () : (Unit → R) →ₗ[A] R).comp f₁.symm.toLinearMap))
  refine ⟨f₁.symm x (), fun r => ?_⟩
  have hx' : x = f₁ (f₁.symm x () • (1 : Unit → R)) := by
    rw [← unit_vec, f₁.apply_symm_apply]
  have := LinearMap.congr_fun hx (f₁ (cR r • (1 : Unit → R)))
  rw [hx', lam_pair ι hspan c cR hc hcc ρ₁ e₁ hadj₁ f₁ hf₁, invol ι hspan c cR hc hcc] at this
  simpa [invol ι hspan c cR hc hcc] using this.symm

end abelian₂
end GlobalTheory.CMNorm

namespace GlobalTheory.CMNorm

variable {A R Λ : Type} [CommRing A] [CommRing R] [CommRing Λ] [Algebra A R]

theorem exists_gram (cR : R →ₐ[A] R) (hcc : ∀ r, cR (cR r) = r) (l : R →ₗ[A] A)
    (hinj : ∀ t, (∀ r, l (r * t) = 0) → t = 0)
    (honto : ∀ g : R →ₗ[A] A, ∃ t, ∀ r, g r = l (r * t))
    {κ T : Type} [Fintype κ] [DecidableEq κ] [AddCommGroup T] [Module A T]
    (e : LinearMap.BilinForm A T) (he : Function.Surjective e) (f : (κ → R) ≃ₗ[A] T)
    (hadj : ∀ (r : R) x y, e (f (r • x)) (f y) = e (f x) (f (cR r • y))) :
    ∃ H : Matrix κ κ R, IsUnit H.det ∧
      ∀ (r : R) x y, e (f (r • x)) (f y) = l (r * ∑ i, ∑ j, x i * H i j * cR (y j)) := by
  have hex : ∀ i j : κ, ∃ t, ∀ r : R,
      e (f (r • Pi.single i (1 : R))) (f (Pi.single j 1)) = l (r * t) := fun i j =>
    honto
      { toFun := fun r => e (f (r • Pi.single i (1 : R))) (f (Pi.single j 1))
        map_add' := fun x y => by simp [add_smul]
        map_smul' := fun a x => by simp [smul_assoc] }
  choose H hH using hex
  have hvec : ∀ x : κ → R, x = ∑ i, x i • (Pi.single i (1 : R) : κ → R) := by
    intro x; ext j; simp [Finset.sum_apply, Pi.single_apply]
  have hform : ∀ (r : R) x y, e (f (r • x)) (f y) = l (r * ∑ i, ∑ j, x i * H i j * cR (y j)) := by
    intro r x y
    conv_lhs => rw [hvec (r • x), hvec y]
    simp only [map_sum, LinearMap.sum_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← hcc (y j), ← hadj, smul_smul, hH, hcc]
    congr 1
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  refine ⟨Matrix.of H, ?_, hform⟩
  have hX : ∀ k : κ, ∃ x : κ → R, ∀ y, e (f x) (f y) = l (cR (y k)) := by
    intro k
    obtain ⟨z, hz⟩ := he ((l.comp cR.toLinearMap).comp
      ((LinearMap.proj k : (κ → R) →ₗ[A] R).comp f.symm.toLinearMap))
    exact ⟨f.symm z, fun y => by simp [hz]⟩
  choose X hX using hX
  refine Matrix.isUnit_det_of_left_inverse (B := Matrix.of X) ?_
  ext k j
  rw [← sub_eq_zero]
  refine hinj _ fun s => ?_
  have h1 := hform 1 (X k) (Pi.single j (cR s))
  rw [one_smul, hX, one_mul] at h1
  rw [mul_sub, map_sub, sub_eq_zero]
  have h2 : ∑ i, ∑ j', X k i * H i j' * cR ((Pi.single j (cR s) : κ → R) j') =
      s * (Matrix.of X * Matrix.of H) k j := by
    simp only [Matrix.mul_apply, Matrix.of_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single j]
    · simp [hcc, mul_comm]
    · intro b _ hb; simp [hb]
    · simp
  rw [← h2, ← h1]
  congr 1
  by_cases hkj : k = j
  · subst hkj; simp [hcc]
  · simp [hkj]

end GlobalTheory.CMNorm

namespace GlobalTheory.CMNorm

open Matrix

theorem frame_row {A R Λ : Type} [CommRing A] [CommRing R] [CommRing Λ] [Algebra A R]
    (ι : Λ →+* R) (hspan : Submodule.span A (Set.range ι) = ⊤)
    {κ T₁ T : Type} [AddCommGroup T₁] [Module A T₁] [AddCommGroup T] [Module A T]
    (ρ₁ : Λ →+* Module.End A T₁) (ρ : Λ →+* Module.End A T) (φ : T₁ →ₗ[A] T)
    (hφ : ∀ a x, φ (ρ₁ a x) = ρ a (φ x))
    (f₁ : (Unit → R) ≃ₗ[A] T₁) (f : (κ → R) ≃ₗ[A] T)
    (hf₁ : ∀ a r, f₁ (ι a • r) = ρ₁ a (f₁ r)) (hf : ∀ a r, f (ι a • r) = ρ a (f r))
    (v : κ → R) (hv : f v = φ (f₁ 1)) (r : R) : f (r • v) = φ (f₁ (r • 1)) := by
  have h := map_smul_of_iota ι hspan (f.symm.toLinearMap ∘ₗ φ ∘ₗ f₁.toLinearMap)
    (fun a x => f.injective (by simp [hf, hf₁, hφ])) r 1
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h
  rw [← hv, f.symm_apply_apply] at h
  rw [← h, f.apply_symm_apply]

theorem associated_det_mul_conj : ∀ (A R Λ : Type) [CommRing A] [CommRing R] [CommRing Λ] [Algebra A R] (ι : Λ →+* R),
    Submodule.span A (Set.range ι) = ⊤ → ∀ (c : Λ →+* Λ) (cR : R →ₐ[A] R), (∀ a, cR (ι a) = ι (c a)) →
    (∀ a, c (c a) = a) →
    ∀ (T₁ T₂ T : Type) [AddCommGroup T₁] [Module A T₁] [AddCommGroup T₂] [Module A T₂] [AddCommGroup T] [Module A T]
      (ρ₁ : Λ →+* Module.End A T₁) (ρ₂ : Λ →+* Module.End A T₂) (ρ : Λ →+* Module.End A T)
      (e₁ : LinearMap.BilinForm A T₁) (e₂ : LinearMap.BilinForm A T₂) (e : LinearMap.BilinForm A T),
      Function.Bijective e₁ → Function.Bijective e₂ → Function.Bijective e →
      (∀ a x y, e₁ (ρ₁ a x) y = e₁ x (ρ₁ (c a) y)) → (∀ a x y, e₂ (ρ₂ a x) y = e₂ x (ρ₂ (c a) y)) →
      (∀ a x y, e (ρ a x) y = e x (ρ (c a) y)) →
    ∀ (m n : Type) [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
      (φ₁ : m → (T₁ →ₗ[A] T)) (φ₂ : n → (T₂ →ₗ[A] T)) (g₁ : Matrix m m Λ) (g₂ : Matrix n n Λ),
      (∀ k a x, φ₁ k (ρ₁ a x) = ρ a (φ₁ k x)) → (∀ k a x, φ₂ k (ρ₂ a x) = ρ a (φ₂ k x)) →
      (∀ k l x y, e (φ₁ k x) (φ₁ l y) = e₁ (ρ₁ (g₁ k l) x) y) →
      (∀ k l x y, e (φ₂ k x) (φ₂ l y) = e₂ (ρ₂ (g₂ k l) x) y) →
      (∀ k l x y, e (φ₁ k x) (φ₂ l y) = 0) → (∀ k l x y, e (φ₂ k x) (φ₁ l y) = 0) →
    ∀ (f₁ : (Unit → R) ≃ₗ[A] T₁) (f₂ : (Unit → R) ≃ₗ[A] T₂) (f : (m ⊕ n → R) ≃ₗ[A] T),
      (∀ a r, f₁ (ι a • r) = ρ₁ a (f₁ r)) → (∀ a r, f₂ (ι a • r) = ρ₂ a (f₂ r)) →
      (∀ a r, f (ι a • r) = ρ a (f r)) →
    ∀ M : Matrix (m ⊕ n) (m ⊕ n) R, (∀ k, f (M (Sum.inl k)) = φ₁ k (f₁ 1)) →
      (∀ k, f (M (Sum.inr k)) = φ₂ k (f₂ 1)) →
      Associated (M.det * cR M.det) (ι (g₁.det * g₂.det)) := by
  intro A R Λ _ _ _ _ ι hspan c cR hc hcc T₁ T₂ T _ _ _ _ _ _ ρ₁ ρ₂ ρ e₁ e₂ e he₁ he₂ he
    ha₁ ha₂ ha m n _ _ _ _ φ₁ φ₂ g₁ g₂ hφ₁ hφ₂ hg₁ hg₂ h12 h21 f₁ f₂ f hf₁ hf₂ hf M hM₁ hM₂
  have hinv := invol ι hspan c cR hc hcc
  have hinj := lam_inj ι hspan c cR hc hcc ρ₁ e₁ he₁ ha₁ f₁ hf₁
  have honto := lam_onto ι hspan c cR hc hcc ρ₁ e₁ he₁ ha₁ f₁ hf₁
  obtain ⟨H, hH, hHf⟩ := exists_gram cR hinv _ hinj honto e he.2 f (adj ι hspan c cR hc ρ e ha f hf)
  obtain ⟨W, hW, hWf⟩ := exists_gram cR hinv _ hinj honto e₂ he₂.2 f₂
    (adj ι hspan c cR hc ρ₂ e₂ ha₂ f₂ hf₂)
  rw [Matrix.det_unique] at hW
  have hr₁ := fun k => frame_row ι hspan ρ₁ ρ (φ₁ k) (hφ₁ k) f₁ f hf₁ hf _ (hM₁ k)
  have hr₂ := fun k => frame_row ι hspan ρ₂ ρ (φ₂ k) (hφ₂ k) f₂ f hf₂ hf _ (hM₂ k)
  have hent : ∀ i j (b : R), (∀ r : R, e (f (r • M i)) (f (M j)) = lam e₁ f₁ (r * b)) →
      (M * H * (M.map cR)ᵀ) i j = b := by
    intro i j b hb
    rw [← sub_eq_zero]
    refine hinj _ fun r => ?_
    rw [mul_sub, map_sub, sub_eq_zero, ← hb, hHf]
    congr 2
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hmat : M * H * (M.map cR)ᵀ =
      Matrix.fromBlocks (g₁.map ι) 0 0 (W default default • g₂.map ι) := by
    ext i j
    refine hent i j _ fun r => ?_
    rcases i with i | i <;> rcases j with j | j
    · rw [hr₁, hM₁, hg₁, ← hf₁, smul_smul, lam_apply]
      simp [mul_comm]
    · rw [hr₁, hM₂, h12]; simp
    · rw [hr₂, hM₁, h21]; simp
    · rw [hr₂, hM₂, hg₂, ← hf₂, smul_smul, hWf]
      congr 1
      simp only [Finset.univ_unique, Finset.sum_singleton, Pi.one_apply, map_one,
        Matrix.fromBlocks_apply₂₂, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
      ring
  have hdet := congrArg Matrix.det hmat
  have hc' : (M.map cR).det = cR M.det := (AlgHom.map_det cR M).symm
  have hi₁ : (g₁.map ι).det = ι g₁.det := (RingHom.map_det ι g₁).symm
  have hi₂ : (g₂.map ι).det = ι g₂.det := (RingHom.map_det ι g₂).symm
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_smul, hc', hi₁, hi₂] at hdet
  have hfin : M.det * cR M.det * H.det =
      ι (g₁.det * g₂.det) * W default default ^ Fintype.card n := by
    rw [map_mul]; linear_combination hdet
  refine (associated_mul_unit_right _ _ hH).trans ?_
  rw [hfin]
  exact associated_mul_unit_left _ _ (hW.pow _)

end GlobalTheory.CMNorm
