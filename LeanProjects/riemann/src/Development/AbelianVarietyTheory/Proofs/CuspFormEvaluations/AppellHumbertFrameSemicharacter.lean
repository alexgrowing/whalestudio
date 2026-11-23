import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

theorem semichar_herm_zero_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (w : Fin g → ℂ) : hermForm Hm 0 w = 0 := by
  simp [hermForm]

theorem semichar_herm_add_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z z' w : Fin g → ℂ) :
    hermForm Hm (z + z') w = hermForm Hm z w + hermForm Hm z' w := by
  simp [hermForm, add_dotProduct]

theorem semichar_herm_add_right {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w w' : Fin g → ℂ) :
    hermForm Hm z (w + w') = hermForm Hm z w + hermForm Hm z w' := by
  simp [hermForm, star_add, Matrix.mulVec_add, dotProduct_add]

theorem semichar_herm_swap {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (z w : Fin g → ℂ) :
    hermForm Hm w z = star (hermForm Hm z w) := by
  simp only [hermForm, dotProduct, Matrix.mulVec, star_sum, star_mul', Finset.mul_sum, Pi.star_apply, star_star]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hH.apply]
  ring

section

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)

theorem AnFr.exists_chart_lat : ∃ j, ∀ a ∈ Φ.lat, ⊤ ≤ (Φ.e a).left ⁻¹ᵁ L.L.U j := by
  obtain ⟨pt⟩ : Nonempty (Sp ℂ) := inferInstanceAs (Nonempty (PrimeSpectrum ℂ))
  obtain ⟨j, hj⟩ : ∃ j, (Φ.e 0).left pt ∈ L.L.U j :=
    TopologicalSpace.Opens.mem_iSup.1 (L.isLB.cover.ge (Set.mem_univ _))
  have hj0 : ⊤ ≤ (Φ.e 0).left ⁻¹ᵁ L.L.U j := fun z _ => by
    have hz : z = pt := Subsingleton.elim (α := PrimeSpectrum ℂ) z pt
    rw [hz]
    exact hj
  refine ⟨j, fun a ha => ?_⟩
  rw [(Φ.e_ker a).2 ha, ← (Φ.e_ker 0).2 Φ.lat.zero_mem]
  exact hj0

theorem AnFr.χ_add {a b : Fin g → ℂ} (ha : a ∈ Φ.lat) (hb : b ∈ Φ.lat) :
    Φ.χ (a + b) = Φ.χ a * Φ.χ b * Complex.exp (Real.pi * Complex.I * ((hermForm Φ.Hm a b).im : ℂ)) := by
  obtain ⟨j, hj⟩ := Φ.exists_chart_lat
  have hab := Φ.lat.add_mem ha hb
  have h1 := Φ.fr_per a ha j 0 (hj 0 Φ.lat.zero_mem)
  have h2 := Φ.fr_per b hb j a (hj a ha)
  have h3 := Φ.fr_per (a + b) hab j 0 (hj 0 Φ.lat.zero_mem)
  have hne : Φ.fr j (a + b) ≠ 0 := Φ.fr_ne j _ (hj _ hab)
  rw [zero_add, h2] at h1
  rw [zero_add] at h3
  simp only [semichar_herm_zero_left, mul_zero, zero_add] at h1 h3
  have key : Φ.χ (a + b) * Complex.exp (↑Real.pi / 2 * hermForm Φ.Hm (a + b) (a + b)) =
      Φ.χ a * Φ.χ b * (Complex.exp (↑Real.pi / 2 * hermForm Φ.Hm a a) *
        Complex.exp (↑Real.pi * hermForm Φ.Hm a b + ↑Real.pi / 2 * hermForm Φ.Hm b b)) := by
    have := h3.symm.trans h1
    apply mul_right_cancel₀ hne
    linear_combination this
  have hexp : Complex.exp (↑Real.pi / 2 * hermForm Φ.Hm a a) *
      Complex.exp (↑Real.pi * hermForm Φ.Hm a b + ↑Real.pi / 2 * hermForm Φ.Hm b b) =
      Complex.exp (↑Real.pi / 2 * hermForm Φ.Hm (a + b) (a + b)) *
        Complex.exp (Real.pi * Complex.I * ((hermForm Φ.Hm a b).im : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    rw [semichar_herm_add_left, semichar_herm_add_right, semichar_herm_add_right, semichar_herm_swap Φ.herm a b]
    have hsc : hermForm Φ.Hm a b - star (hermForm Φ.Hm a b) =
        2 * ((hermForm Φ.Hm a b).im : ℂ) * Complex.I := by
      rw [show star (hermForm Φ.Hm a b) = (starRingEnd ℂ) (hermForm Φ.Hm a b) from rfl, Complex.sub_conj]
      push_cast; ring
    linear_combination (↑Real.pi / 2 : ℂ) * hsc
  rw [hexp] at key
  have hE : Complex.exp (↑Real.pi / 2 * hermForm Φ.Hm (a + b) (a + b)) ≠ 0 := Complex.exp_ne_zero _
  apply mul_right_cancel₀ hE
  linear_combination key

theorem AnFr.χ_ne_zero {a : Fin g → ℂ} (ha : a ∈ Φ.lat) : Φ.χ a ≠ 0 := fun h => by
  have := Φ.χ_norm a ha
  rw [h, norm_zero] at this
  exact zero_ne_one this

theorem AnFr.herm_im_swap (a b : Fin g → ℂ) : (hermForm Φ.Hm b a).im = -(hermForm Φ.Hm a b).im := by
  rw [semichar_herm_swap Φ.herm a b]
  simp

theorem AnFr.herm_im_int {a b : Fin g → ℂ} (ha : a ∈ Φ.lat) (hb : b ∈ Φ.lat) :
    ∃ k : ℤ, (hermForm Φ.Hm a b).im = k := by
  have h1 := Φ.χ_add ha hb
  have h2 := Φ.χ_add hb ha
  rw [add_comm b a, h1, Φ.herm_im_swap a b, mul_comm (Φ.χ b)] at h2
  have h3 := mul_left_cancel₀ (mul_ne_zero (Φ.χ_ne_zero ha) (Φ.χ_ne_zero hb)) h2
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h3
  refine ⟨n, ?_⟩
  have hπ : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have : (((hermForm Φ.Hm a b).im : ℝ) : ℂ) = (n : ℂ) := by
    apply mul_left_cancel₀ hπ
    push_cast at hn
    linear_combination hn
  exact_mod_cast this

theorem AnFr.herm_im_self (a : Fin g → ℂ) : (hermForm Φ.Hm a a).im = 0 := by
  have := Φ.herm_im_swap a a
  linarith

theorem AnFr.χ_add_self {a : Fin g → ℂ} (ha : a ∈ Φ.lat) : Φ.χ (a + a) = Φ.χ a ^ 2 := by
  rw [Φ.χ_add ha ha, Φ.herm_im_self]
  simp [sq]

theorem AnFr.χ_zero : Φ.χ 0 = 1 := by
  have h := Φ.χ_add_self Φ.lat.zero_mem
  rw [add_zero] at h
  apply mul_left_cancel₀ (Φ.χ_ne_zero Φ.lat.zero_mem)
  linear_combination -h

end

theorem anFr_semichar : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), (∀ a ∈ Φ.lat, ∀ b ∈ Φ.lat, (∃ k : ℤ, (hermForm Φ.Hm a b).im = k) ∧ Φ.χ (a + b) = Φ.χ a * Φ.χ b * Complex.exp (Real.pi * Complex.I * ((hermForm Φ.Hm a b).im : ℂ))) ∧ Φ.χ 0 = 1 ∧ ((∀ a ∈ Φ.lat, Φ.χ a ^ 2 = 1) → ∀ a ∈ Φ.lat, Φ.χ ((2 : ℂ) • a) = 1) := by
  intro S A _ _ L x0 g Φ
  refine ⟨fun a ha b hb => ⟨Φ.herm_im_int ha hb, Φ.χ_add ha hb⟩, Φ.χ_zero, fun h a ha => ?_⟩
  rw [two_smul, Φ.χ_add_self ha, h a ha]

end GlobalTheory.AnVal
