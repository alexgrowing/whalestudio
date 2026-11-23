import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial

noncomputable section
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare.CoDiag

theorem rk_eq_of_conj {G : Type} [Group G] [Fintype G] {M : Type} [AddCommGroup M] [Module ℂ M]
    (ρ : Representation ℂ G M) (e e' : G → ℂ) (t : G) (h : ∀ u, e' (t * u * t⁻¹) = e u) :
    rk ρ e = rk ρ e' := by
  have h1 : op ρ e' = ρ t * op ρ e * ρ t⁻¹ := by
    unfold op
    rw [Finset.mul_sum, Finset.sum_mul, ← Equiv.sum_comp (MulAut.conj t).toEquiv]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp [h]
  let T : M ≃ₗ[ℂ] M := LinearEquiv.ofLinear (ρ t) (ρ t⁻¹)
    (by rw [← Module.End.mul_eq_comp, ← map_mul]; simp [Module.End.one_eq_id])
    (by rw [← Module.End.mul_eq_comp, ← map_mul]; simp [Module.End.one_eq_id])
  have h2 : LinearMap.range (op ρ e') = (LinearMap.range (op ρ e)).map (T : M →ₗ[ℂ] M) := by
    have : op ρ e' = (T : M →ₗ[ℂ] M) ∘ₗ (op ρ e ∘ₗ (T.symm : M →ₗ[ℂ] M)) := by
      rw [h1]; rfl
    rw [this, LinearMap.range_comp, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]
  unfold rk
  rw [h2, LinearEquiv.finrank_map_eq]

theorem exists_potential {N : ℕ} {A : Type} [Group A] (E : Fin N → Fin N → Prop)
    (hlt : ∀ a b, E a b → a < b) (huniq : ∀ a a' b, E a b → E a' b → a = a') (r : Fin N → A) :
    ∃ t : Fin N → A, ∀ a b, E a b → t b = t a * r a := by
  let F : ∀ b : Fin N, (∀ a, a < b → A) → A := fun b rec =>
    if h : ∃ a, E a b then rec h.choose (hlt _ _ h.choose_spec) * r h.choose else 1
  refine ⟨wellFounded_lt.fix F, fun a b hab => ?_⟩
  have h : ∃ a, E a b := ⟨a, hab⟩
  have ha : h.choose = a := huniq _ _ _ h.choose_spec hab
  rw [WellFounded.fix_eq]
  have : F b (fun y _ => wellFounded_lt.fix F y) = wellFounded_lt.fix F h.choose * r h.choose := dif_pos h
  rw [this, ha]

theorem exists_unit_shift (g : ℕ) [Fact g.Prime] (ψ ψ' : AddChar (ZMod g) ℂ) (h : ψ ≠ 1) (h' : ψ' ≠ 1) :
    ∃ c : (ZMod g)ˣ, ∀ x, ψ' x = ψ (c * x) := by
  have hp : ψ.IsPrimitive := AddChar.IsPrimitive.of_ne_one h
  have hinj := AddChar.to_mulShift_inj_of_isPrimitive hp
  have hbij : Function.Bijective ψ.mulShift :=
    (Fintype.bijective_iff_injective_and_card _).2 ⟨hinj, (AddChar.card_eq (α := ZMod g)).symm⟩
  obtain ⟨c, hc⟩ := hbij.2 ψ'
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact h' (by rw [← hc, AddChar.mulShift_zero])
  exact ⟨Units.mk0 c hc0, fun x => by rw [← hc]; simp⟩

variable {g : ℕ} [Fact g.Prime] {N : ℕ}

def diagUnit (t : Fin N → (ZMod g)ˣ) : GG g N where
  val := Matrix.diagonal fun a => (t a : ZMod g)
  inv := Matrix.diagonal fun a => (((t a)⁻¹ : (ZMod g)ˣ) : ZMod g)
  val_inv := by rw [Matrix.diagonal_mul_diagonal]; simp only [Units.mul_inv, Matrix.diagonal_one]
  inv_val := by rw [Matrix.diagonal_mul_diagonal]; simp only [Units.inv_mul, Matrix.diagonal_one]

theorem conj_diagUnit_apply (t : Fin N → (ZMod g)ˣ) (u : GG g N) (a b : Fin N) :
    (diagUnit t * u * (diagUnit t)⁻¹).val a b = (t a : ZMod g) * u.val a b * ((t b)⁻¹ : (ZMod g)ˣ) := by
  have : (diagUnit t * u * (diagUnit t)⁻¹).val
      = Matrix.diagonal (fun a => (t a : ZMod g)) * u.val * Matrix.diagonal (fun a => (((t a)⁻¹ : (ZMod g)ˣ) : ZMod g)) := rfl
  rw [this, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem mem_conj_diagUnit (L : Lev g N) (t : Fin N → (ZMod g)ˣ) (u : GG g N) :
    L.Mem (diagUnit t * u * (diagUnit t)⁻¹) ↔ L.Mem u := by
  have h0 : ∀ a b, (diagUnit t * u * (diagUnit t)⁻¹).val a b = 0 ↔ u.val a b = 0 := by
    intro a b
    rw [conj_diagUnit_apply, Units.mul_left_eq_zero, Units.mul_right_eq_zero]
  have h1 : ∀ a, (diagUnit t * u * (diagUnit t)⁻¹).val a a = u.val a a := by
    intro a
    rw [conj_diagUnit_apply, mul_right_comm, Units.mul_inv, one_mul]
  unfold Lev.Mem IsUp
  simp only [h0, h1]

theorem edge_lt (L : Lev g N) (a b : Fin N) (h : L.Edge a b) : a < b := by
  unfold Lev.Edge at h
  rw [Fin.lt_def]
  split_ifs at h <;> omega

theorem edge_unique (L : Lev g N) (a a' b : Fin N) (h : L.Edge a b) (h' : L.Edge a' b) : a = a' := by
  unfold Lev.Edge at h h'
  apply Fin.ext
  split_ifs at h h' <;> omega

theorem rk_e_eq : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    (ρ : Representation ℂ (GG g N) M), ∀ L L' : Lev g N, L.sharp = L'.sharp → L.s = L'.s → L.k = L'.k →
    rk ρ L.e = rk ρ L'.e := by
  intro g _ N M _ _ _ ρ L L' h1 h2 h3
  have hM : L'.Mem = L.Mem := by
    funext u
    unfold Lev.Mem
    rw [h1, h2, h3]
  have hE : L'.Edge = L.Edge := by
    funext a b
    unfold Lev.Edge
    rw [h1, h2, h3]
  obtain ⟨c, hc⟩ := exists_unit_shift g L.ψ L'.ψ L.hψ L'.hψ
  obtain ⟨t, ht⟩ := exists_potential L.Edge (edge_lt L) (edge_unique L) (fun a => c * L'.co a * (L.co a)⁻¹)
  refine rk_eq_of_conj ρ _ _ (diagUnit t) fun u => ?_
  have hchi : L'.chi (diagUnit t * u * (diagUnit t)⁻¹) = L.chi u := by
    unfold Lev.chi
    rw [hc, hE, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs with hab
    · rw [conj_diagUnit_apply, ht a b hab]
      simp only [Units.val_inv_eq_inv_val, Units.val_mul]
      have := (t a).ne_zero
      have := c.ne_zero
      have := (L.co a).ne_zero
      have := (L'.co a).ne_zero
      field_simp
    · simp
  unfold Lev.e eps
  rw [hchi, hM]
  simp only [mem_conj_diagUnit]

end GlobalTheory.BadShare.CoDiag
