import Mathlib
import Formalism.LocalToGlobal.GaloisLevelStructure.TiedHecke
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictRing

open Formalism.BasicNotions Formalism.L2 Formalism.L2.NG Formalism.AUTREP
open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.AlgFormsFin

section General

variable (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)

local notation3 "L⁺" => NumberField.maximalRealSubfield L

theorem ALint_le : ReciprocityTheory.Aut.ALint L ≤ Formalism.MainNotions.S.IntAf (L⁺) L := by
  rw [ReciprocityTheory.Aut.ALint, Subring.closure_le]
  rintro x (⟨y, rfl⟩ | ⟨a, ha, rfl⟩)
  · exact Subring.subset_closure (Or.inl ⟨⟨(y : L), y, rfl⟩, rfl⟩)
  · exact Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)

theorem le_ALint : Formalism.MainNotions.S.IntAf (L⁺) L ≤ ReciprocityTheory.Aut.ALint L := by
  show Subring.closure _ ≤ _
  rw [Subring.closure_le]
  rintro x (⟨⟨e, a, rfl⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
  · exact Subring.subset_closure (Or.inl ⟨a, rfl⟩)
  · exact Subring.subset_closure (Or.inr ⟨y, hy, rfl⟩)

theorem exists_approx {N : ℕ} (hN : 0 < N) {x : ReciprocityTheory.Aut.AL L} (hx : x ∈ ReciprocityTheory.Aut.ALint L) :
    ∃ a : 𝓞 L, ∃ r ∈ ReciprocityTheory.Aut.ALint L, x = ((a : L) ⊗ₜ[L⁺] (1 : ReciprocityTheory.Aut.AFplus L)) + (N : ReciprocityTheory.Aut.AL L) * r := by
  obtain ⟨a, r, hr, e⟩ := PIW.AdelClassFin.dual_dense (L⁺) L N hN x (ALint_le L hx)
  exact ⟨a, r, le_ALint L hr, e⟩

theorem exists_class {N : ℕ} (hN : 0 < N) : ∃ (Q : Type) (_ : Finite Q) (c : ReciprocityTheory.Aut.AL L → Q),
    ∀ x ∈ ReciprocityTheory.Aut.ALint L, ∀ y ∈ ReciprocityTheory.Aut.ALint L, c x = c y →
      ∃ r ∈ ReciprocityTheory.Aut.ALint L, x - y = (N : ReciprocityTheory.Aut.AL L) * r := by
  classical
  have hN0 : Ideal.span {(N : 𝓞 L)} ≠ ⊥ := by
    simp only [ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN.ne'
  have hfin : Finite (𝓞 L ⧸ Ideal.span {(N : 𝓞 L)}) := Ideal.finiteQuotientOfFreeOfNeBot _ hN0
  refine ⟨𝓞 L ⧸ Ideal.span {(N : 𝓞 L)}, hfin, fun x =>
    if h : x ∈ ReciprocityTheory.Aut.ALint L then Ideal.Quotient.mk _ (exists_approx L hN h).choose else 0, ?_⟩
  intro x hx y hy e
  simp only [dif_pos hx, dif_pos hy] at e
  obtain ⟨r, hr, ex⟩ := (exists_approx L hN hx).choose_spec
  obtain ⟨s, hs, ey⟩ := (exists_approx L hN hy).choose_spec
  set a := (exists_approx L hN hx).choose
  set b := (exists_approx L hN hy).choose
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at e
  obtain ⟨d, hd⟩ := e
  have hab : a = b + (N : 𝓞 L) * d := by rw [← hd]; ring
  have hi : ∀ z : 𝓞 L, ((z : L) ⊗ₜ[L⁺] (1 : ReciprocityTheory.Aut.AFplus L)) ∈ ReciprocityTheory.Aut.ALint L :=
    fun z => Subring.subset_closure (Or.inl ⟨z, rfl⟩)
  refine ⟨((d : L) ⊗ₜ[L⁺] (1 : ReciprocityTheory.Aut.AFplus L)) + r - s, sub_mem (add_mem (hi d) hr) hs, ?_⟩
  have hinc : ((a : L) ⊗ₜ[L⁺] (1 : ReciprocityTheory.Aut.AFplus L)) = ((b : L) ⊗ₜ[L⁺] (1 : ReciprocityTheory.Aut.AFplus L)) +
      (N : ReciprocityTheory.Aut.AL L) * ((d : L) ⊗ₜ[L⁺] (1 : ReciprocityTheory.Aut.AFplus L)) := by
    rw [hab, Algebra.TensorProduct.natCast_def, Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← TensorProduct.add_tmul]
    push_cast
    rfl
  rw [ex, ey, hinc]
  ring

theorem exists_cover {N : ℕ} (hN : 0 < N) : ∃ J : Finset (GAf L n), ∀ u ∈ ReciprocityTheory.Aut.Umax L n,
    ∃ j ∈ J, ∃ κ, Formalism.L2.NG.Cong L n N κ ∧ u = j * κ := by
  classical
  obtain ⟨Q, hQ, c, hc⟩ := exists_class L hN
  let φ : GAf L n → Fin n → Fin n → Q := fun g i j => c ((g.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) i j)
  let rep : (Fin n → Fin n → Q) → GAf L n := fun q =>
    if h : ∃ u ∈ ReciprocityTheory.Aut.Umax L n, φ u = q then h.choose else 1
  have hfin : Fintype (Fin n → Fin n → Q) := Fintype.ofFinite _
  refine ⟨Finset.univ.image rep, fun u hu => ?_⟩
  have hex : ∃ w ∈ ReciprocityTheory.Aut.Umax L n, φ w = φ u := ⟨u, hu, rfl⟩
  have hrep : rep (φ u) = hex.choose := dif_pos hex
  obtain ⟨hj, hφ⟩ := hex.choose_spec
  rw [← hrep] at hj hφ
  set j := rep (φ u) with hjdef
  refine ⟨j, Finset.mem_image.2 ⟨φ u, Finset.mem_univ _, rfl⟩, j⁻¹ * u, ⟨mul_mem (inv_mem hj) hu, ?_⟩, by simp⟩
  intro a b
  have hdiff : ∀ k, ∃ r ∈ ReciprocityTheory.Aut.ALint L, (u.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) k b -
      (j.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) k b = (N : ReciprocityTheory.Aut.AL L) * r := fun k =>
    hc _ (hu k b) _ (hj k b) (congrFun (congrFun hφ k) b).symm
  choose r hr e using hdiff
  have hinv : (((j⁻¹ : GAf L n)).1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) * (j.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]
    rfl
  have hmat : (((j⁻¹ * u : GAf L n)).1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) - 1 =
      (((j⁻¹ : GAf L n)).1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) *
        ((u.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) - (j.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L))) := by
    rw [Matrix.mul_sub, hinv, Subgroup.coe_mul, Units.val_mul]
  refine ⟨∑ k, (((j⁻¹ : GAf L n)).1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) a k * r k,
    sum_mem fun k _ => mul_mem (inv_mem hj a k) (hr k), ?_⟩
  have := congrFun (congrFun hmat a) b
  rw [Matrix.sub_apply, Matrix.mul_apply] at this
  rw [this, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.sub_apply, e k]
  ring

variable {W : Type} [AddCommGroup W] [Module ℂ W]

def fixedForms (ρ : Representation ℂ (ReciprocityTheory.Aut.GQ L n) W) (N : ℕ) : Submodule ℂ (GAf L n → W) where
  carrier := {f | (∀ (γ : ReciprocityTheory.Aut.GQ L n) (g : GAf L n), f ((γ : GAf L n) * g) = ρ γ (f g)) ∧
    ∀ κ, Formalism.L2.NG.Cong L n N κ → ∀ g, f (g * κ) = f g}
  zero_mem' := ⟨fun γ g => by simp, fun _ _ _ => rfl⟩
  add_mem' := by
    rintro f f' ⟨h1, h2⟩ ⟨h1', h2'⟩
    exact ⟨fun γ g => by simp [h1 γ g, h1' γ g], fun κ hκ g => by simp [h2 κ hκ g, h2' κ hκ g]⟩
  smul_mem' := by
    rintro c f ⟨h1, h2⟩
    exact ⟨fun γ g => by simp [h1 γ g], fun κ hκ g => by simp [h2 κ hκ g]⟩

theorem fixedForms_finite [FiniteDimensional ℂ W] (ρ : Representation ℂ (ReciprocityTheory.Aut.GQ L n) W)
    (hT : ∃ T : Finset (GAf L n), ∀ g : GAf L n, ∃ (γ : ReciprocityTheory.Aut.GQ L n) (t : GAf L n) (u : GAf L n),
      t ∈ T ∧ u ∈ ReciprocityTheory.Aut.Umax L n ∧ g = (γ : GAf L n) * t * u)
    {N : ℕ} (hN : 0 < N) : FiniteDimensional ℂ (fixedForms L n ρ N) := by
  classical
  obtain ⟨T, hT⟩ := hT
  obtain ⟨J, hJ⟩ := exists_cover L n hN
  let Φ : fixedForms L n ρ N →ₗ[ℂ] (↥(T ×ˢ J) → W) :=
    { toFun := fun f p => (f : GAf L n → W) (p.1.1 * p.1.2)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective Φ ((injective_iff_map_eq_zero Φ).2 fun f hf => ?_)
  refine Subtype.ext (funext fun g => ?_)
  obtain ⟨γ, t, u, ht, hu, rfl⟩ := hT g
  obtain ⟨j, hj, κ, hκ, rfl⟩ := hJ u hu
  have h0 : (f : GAf L n → W) (t * j) = 0 :=
    congrFun hf ⟨(t, j), Finset.mem_product.2 ⟨ht, hj⟩⟩
  have e : (γ : GAf L n) * t * (j * κ) = ((γ : GAf L n) * (t * j)) * κ := by simp only [mul_assoc]
  show (f : GAf L n → W) _ = 0
  rw [e, f.2.2 κ hκ, f.2.1 γ, h0, map_zero]

end General

theorem finiteDimensional_forms : ∀ (D : D7) (n : ℕ) (a : AlgWt D.host.E n), (∃ T : Finset (GAf D.host.E n), ∀ g : GAf D.host.E n, ∃ (γ : ReciprocityTheory.Aut.GQ D.host.E n) (t : GAf D.host.E n) (u : GAf D.host.E n), t ∈ T ∧ u ∈ ReciprocityTheory.Aut.Umax D.host.E n ∧ g = (γ : GAf D.host.E n) * t * u) → ∀ N : ℕ, 0 < N → FiniteDimensional ℂ ↥(Submodule.span ℂ {f | f ∈ AFall D.host.E n a.ρ ∧ ∀ κ, Cong D.host.E n N κ → ∀ g, f (g * κ) = f g}) := by
  intro D n a hT N hN
  have hW : FiniteDimensional ℂ a.W := a.alg.1
  have h := fixedForms_finite D.host.E n a.ρ hT hN
  refine Submodule.finiteDimensional_of_le (S₂ := fixedForms D.host.E n a.ρ N) (Submodule.span_le.2 ?_)
  rintro f ⟨hf, hκ⟩
  exact ⟨hf.1, hκ⟩

end GlobalTheory.AlgFormsFin

end
