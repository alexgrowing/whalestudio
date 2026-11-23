import Formalism.HermitianCurvature.HermitianCurvatureProofs.SecondDefectNonneg
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LenEqLenI

namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

section wts

variable {P : M.Par} (l0 : ℕ) (a : List C.Letter) (e : Wd.Ix (Fin a.length)) (ρ : M.Ty P) (Pv : ℝ → ℝ) (C : ℝ)

def RHyp : List ℝ → Prop
  | [] => True
  | y :: ys => (0 < (topR l0 (KB.plusW ys a) (KB.firstSt ys e) ρ y).re ∧
      (topR l0 (KB.plusW ys a) (KB.firstSt ys e) ρ y).im = 0 ∧
      |Pv y| ≤ C * (topR l0 (KB.plusW ys a) (KB.firstSt ys e) ρ y).re) ∧ RHyp ys

theorem prodR_props (hC : 0 ≤ C) : ∀ ys : List ℝ, RHyp l0 a e ρ Pv C ys →
    (topRprod l0 a e ρ ys).im = 0 ∧ 0 < (topRprod l0 a e ρ ys).re ∧
      (ys.map fun y => |Pv y|).prod ≤ C ^ ys.length * (topRprod l0 a e ρ ys).re
  | [], _ => by simp [topRprod]
  | y :: ys, ⟨⟨h1, h2, h3⟩, hr⟩ => by
    obtain ⟨i1, i2, i3⟩ := prodR_props hC ys hr
    simp only [topRprod, Complex.mul_im, Complex.mul_re, List.map_cons, List.prod_cons, List.length_cons]
    refine ⟨by rw [i1, h2]; ring, by rw [i1, h2]; simp only [mul_zero, zero_mul, sub_zero]; positivity, ?_⟩
    rw [i1, h2]
    simp only [mul_zero, sub_zero]
    have hp : 0 ≤ (ys.map fun y => |Pv y|).prod := List.prod_nonneg fun x hx => by
      obtain ⟨z, -, rfl⟩ := List.mem_map.1 hx; exact abs_nonneg _
    calc |Pv y| * (ys.map fun y => |Pv y|).prod ≤ (C * (topR l0 (KB.plusW ys a) (KB.firstSt ys e) ρ y).re) *
          (C ^ ys.length * (topRprod l0 a e ρ ys).re) := mul_le_mul h3 i3 hp (by positivity)
      _ = C ^ (ys.length + 1) * ((topRprod l0 a e ρ ys).re * (topR l0 (KB.plusW ys a) (KB.firstSt ys e) ρ y).re) := by
          ring

end wts

section wts2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

theorem second_defect_plus_word_le (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))) (v : Fin S.f)
    (a : List C.Letter) (e : Wd.Ix (Fin a.length)) (ρ : M.Ty (D.parOf S v)) (C : ℝ) (hC : 0 ≤ C) (ys : List ℝ)
    (hR : RHyp (p v).l0 a e ρ (S.P v) C ys) :
    del2 S p v a e ρ * (ys.map fun y => |S.P v y|).prod ≤
      C ^ ys.length * del2 S p v (KB.plusW ys a) (KB.firstSt ys e) ρ := by
  obtain ⟨i1, i2, i3⟩ := prodR_props (p v).l0 a e ρ (S.P v) C hC ys hR
  have hd : del2 S p v (KB.plusW ys a) (KB.firstSt ys e) ρ = del2 S p v a e ρ * (topRprod (p v).l0 a e ρ ys).re := by
    unfold del2
    rw [cW_plusW, Complex.mul_re, i1, mul_zero, sub_zero, Real.sqrt_mul' _ i2.le]
    rw [show √(Top.cW (D.parOf S v) (p v).l0 a e ρ).re * √(topRprod (p v).l0 a e ρ ys).re *
        (√(Top.cW (D.parOf S v) (p v).l0 a e ρ).re * √(topRprod (p v).l0 a e ρ ys).re) =
        √(Top.cW (D.parOf S v) (p v).l0 a e ρ).re * √(Top.cW (D.parOf S v) (p v).l0 a e ρ).re *
          (√(topRprod (p v).l0 a e ρ ys).re * √(topRprod (p v).l0 a e ρ ys).re) by ring,
      Real.mul_self_sqrt i2.le]
  rw [hd]
  have h0 := second_defect_nonneg S p v a e ρ
  calc del2 S p v a e ρ * (ys.map fun y => |S.P v y|).prod ≤
        del2 S p v a e ρ * (C ^ ys.length * (topRprod (p v).l0 a e ρ ys).re) := mul_le_mul_of_nonneg_left i3 h0
    _ = _ := by ring

end wts2

end

end Formalism.FourierDecayAlt.P.PBL
