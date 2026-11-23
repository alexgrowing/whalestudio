import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PhiCSt

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open NumberField Formalism.MainNotions.ModuliIntegralCharts

section Comparison₂

variable {E : Type} [Field E] [NumberField E] {Y : Type} [AddCommGroup Y] [Module (𝓞 E) Y]
  {ι : Type} [Fintype ι] (b : Module.Basis ι ℤ Y)

def coordT (x y : Y) : ι × ι → ℤ := fun p => b.repr x p.1 * b.repr y p.2

theorem coordT_add_left (x x' y : Y) : coordT b (x + x') y = coordT b x y + coordT b x' y := by
  funext p
  simp only [coordT, map_add, Finsupp.add_apply, Pi.add_apply, add_mul]

theorem coordT_add_right (x y y' : Y) : coordT b x (y + y') = coordT b x y + coordT b x y' := by
  funext p
  simp only [coordT, map_add, Finsupp.add_apply, Pi.add_apply, mul_add]

theorem coordT_smul_left (k : ℤ) (x y : Y) : coordT b (k • x) y = k • coordT b x y := by
  funext p
  simp only [coordT, map_zsmul, Finsupp.smul_apply, smul_eq_mul, Pi.smul_apply]
  ring

theorem coordT_smul_right (k : ℤ) (x y : Y) : coordT b x (k • y) = k • coordT b x y := by
  funext p
  simp only [coordT, map_zsmul, Finsupp.smul_apply, smul_eq_mul, Pi.smul_apply]
  ring

def evB (B : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) : (ι × ι → ℤ) →ₗ[ℤ] ℝ where
  toFun n := ∑ p, (n p : ℝ) * B (b p.1) (b p.2)
  map_add' n n' := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' k n := by simp [Finset.mul_sum, mul_assoc]

theorem evB_apply (B : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (n : ι × ι → ℤ) :
    evB b B n = ∑ p, (n p : ℝ) * B (b p.1) (b p.2) := rfl

theorem evB_coordT (B : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (x y : Y) : evB b B (coordT b x y) = B x y := by
  rw [evB_apply, Fintype.sum_prod_type]
  have hx := b.sum_repr x
  have hy := b.sum_repr y
  calc _ = ∑ i, ∑ j, ((b.repr x i : ℝ) * (b.repr y j : ℝ)) * B (b i) (b j) := by
          simp only [coordT, Int.cast_mul]
    _ = B x y := by
      conv_rhs => rw [← hx, ← hy]
      simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply, zsmul_eq_mul,
        Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring

def annS (cj : E → E) : Submodule ℤ (ι × ι → ℤ) :=
  ⨅ β : SymB cj Y, LinearMap.ker (evB b (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ))

theorem mem_annS (cj : E → E) (n : ι × ι → ℤ) :
    n ∈ annS b cj ↔ ∀ β : SymB cj Y, evB b (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) n = 0 := by
  simp only [annS, Submodule.mem_iInf, LinearMap.mem_ker]

theorem noZero_annS (cj : E → E) : NoZeroSMulDivisors ℤ ((ι × ι → ℤ) ⧸ annS b cj) := by
  refine ⟨fun {k} {q} h => ?_⟩
  obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  by_cases hk : k = 0
  · exact Or.inl hk
  right
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, mem_annS] at h
  rw [Submodule.Quotient.mk_eq_zero, mem_annS]
  intro β
  have h1 := h β
  rw [map_zsmul, zsmul_eq_mul, mul_eq_zero] at h1
  rcases h1 with h1 | h1
  · exact absurd (Int.cast_eq_zero.mp h1) hk
  · exact h1

def formOf (f : (ι × ι → ℤ) →ₗ[ℤ] ℤ) : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ :=
  LinearMap.mk₂ ℤ (fun x y => ((f (coordT b x y) : ℤ) : ℝ))
    (fun x x' y => by simp [coordT_add_left])
    (fun k x y => by rw [coordT_smul_left, map_zsmul]; simp [zsmul_eq_mul])
    (fun x y y' => by simp [coordT_add_right])
    (fun k x y => by rw [coordT_smul_right, map_zsmul]; simp [zsmul_eq_mul])

theorem formOf_apply (f : (ι × ι → ℤ) →ₗ[ℤ] ℤ) (x y : Y) :
    formOf b f x y = ((f (coordT b x y) : ℤ) : ℝ) := rfl

theorem formOf_mem (cj : E → E) (f : ((ι × ι → ℤ) ⧸ annS b cj) →ₗ[ℤ] ℤ) :
    formOf b (f ∘ₗ (annS b cj).mkQ) ∈ SymB cj Y := by
  have key : ∀ x y x' y' : Y, (∀ β : SymB cj Y, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) x y =
      (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) x' y') →
      formOf b (f ∘ₗ (annS b cj).mkQ) x y = formOf b (f ∘ₗ (annS b cj).mkQ) x' y' := by
    intro x y x' y' h
    rw [formOf_apply, formOf_apply, LinearMap.comp_apply, LinearMap.comp_apply]
    congr 2
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, mem_annS]
    intro β
    rw [map_sub, evB_coordT, evB_coordT, h β, sub_self]
  have mem : ∀ β : SymB cj Y, (∀ a d : Y, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a d = (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) d a) ∧
      ∀ (c c' : 𝓞 E), (c' : E) = cj c → ∀ (a d : Y),
        (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (c • a) d = (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a (c' • d) := fun β => β.2
  refine ⟨fun a d => key a d d a fun β => (mem β).1 a d,
    fun c c' hc a d => key _ _ _ _ fun β => (mem β).2 c c' hc a d⟩

end Comparison₂

theorem phiCTie_holds : PhiCTieStatement := by
  intro E _ _ cj Y _ _ _ _ l hl
  classical
  let b := Module.Free.chooseBasis ℤ Y
  let A := annS b cj
  have : NoZeroSMulDivisors ℤ ((_ × _ → ℤ) ⧸ A) := noZero_annS b cj
  have : Module.Free ℤ ((_ × _ → ℤ) ⧸ A) := Module.free_of_finite_type_torsion_free'
  let eb := Module.Free.chooseBasis ℤ ((_ × _ → ℤ) ⧸ A)
  let βk : Module.Free.ChooseBasisIndex ℤ ((_ × _ → ℤ) ⧸ A) → SymB cj Y := fun k =>
    ⟨formOf b (eb.coord k ∘ₗ A.mkQ), formOf_mem b cj _⟩
  have hint : ∀ k, ∃ z : ℤ, l (βk k) = z := fun k =>
    hl (βk k) (fun x y => ⟨_, formOf_apply b _ x y⟩)
  choose z hz using hint
  obtain ⟨n, hn⟩ := Submodule.Quotient.mk_surjective A (∑ k, z k • eb k)
  let e := (Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ Y × Module.Free.ChooseBasisIndex ℤ Y)).symm
  refine ⟨Fintype.card (Module.Free.ChooseBasisIndex ℤ Y × Module.Free.ChooseBasisIndex ℤ Y),
    fun t => n (e t) • b (e t).1, fun t => b (e t).2, fun β => ?_⟩
  have hR : ∑ t, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (n (e t) • b (e t).1) (b (e t).2) =
      evB b (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) n := by
    rw [e.sum_comp (fun p => (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (n p • b p.1) (b p.2)), evB_apply]
    simp [zsmul_eq_mul]
  rw [hR]
  have hle : A ≤ LinearMap.ker (evB b (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ)) := iInf_le _ β
  let ψ := A.liftQ (evB b (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ)) hle
  have hψ : ∀ m, ψ (Submodule.Quotient.mk m) = evB b (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) m := fun m =>
    Submodule.liftQ_apply _ _ _
  have hβ : β = ∑ k, ψ (eb k) • βk k := by
    apply Subtype.ext
    apply LinearMap.ext₂
    intro x y
    rw [Submodule.coe_sum, LinearMap.sum_apply, LinearMap.sum_apply]
    simp only [Submodule.coe_smul, LinearMap.smul_apply, βk, formOf_apply, LinearMap.comp_apply,
      Submodule.mkQ_apply, Module.Basis.coord_apply, smul_eq_mul]
    rw [← evB_coordT b (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) x y, ← hψ]
    conv_lhs => rw [← eb.sum_repr (Submodule.Quotient.mk (coordT b x y))]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul, zsmul_eq_mul, mul_comm]
  calc l β = l (∑ k, ψ (eb k) • βk k) := congrArg l hβ
    _ = ∑ k, ψ (eb k) * (z k : ℝ) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul, hz, smul_eq_mul]
    _ = evB b (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) n := by
      rw [← hψ, hn, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_zsmul, zsmul_eq_mul, mul_comm]

end Formalism.MainNotions.ModuliIntegralCharts.H1
