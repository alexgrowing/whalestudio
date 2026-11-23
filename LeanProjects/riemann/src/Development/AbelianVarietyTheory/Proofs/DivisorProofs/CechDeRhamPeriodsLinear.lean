import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

open Opposite in

theorem periods_linear : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), (∀ x y q q', IsPer u.ex u.Λ x q → IsPer u.ex u.Λ y q' → IsPer u.ex u.Λ (x + y) (q + q') ∧ IsPer u.ex u.Λ (x - y) (q - q')) ∧ ∀ (a : ℂ) x q, IsPer u.ex u.Λ x q → IsPer u.ex u.Λ (a • x) (a • q) := by
  intro A _ g L u
  have hO : ∀ U : A.left.Opens, IsOpen (pre u.ex U) := fun U ↦ (u.hol U 0).1
  have vadd : ∀ (U : A.left.Opens) (b b' : Γ(A.left, U)) z, val u.ex U (b + b') z = val u.ex U b z + val u.ex U b' z :=
    fun U b b' z ↦ valAt'_add _ _ _ _
  have vsub : ∀ (U : A.left.Opens) (b b' : Γ(A.left, U)) z, val u.ex U (b - b') z = val u.ex U b z - val u.ex U b' z :=
    fun U b b' z ↦ valAt'_sub _ _ _ _
  have vsmul : ∀ (U : A.left.Opens) (a : ℂ) (b : Sec (str A) U), ∀ z ∈ pre u.ex U,
      val u.ex U (a • b) z = a * val u.ex U b z := by
    intro U a b z hz
    have e : (u.ex z).left ≫ str A = 𝟙 (Sp ℂ) := by
      rw [str, Category.comp_id]; exact Over.w (u.ex z)
    have k : valAt' (u.ex z).left U ((secMap (str A) U).hom a) = a :=
      (valAt'_appLE (u.ex z).left (str A) ⊤ U le_top _ hz).trans
        ((congrArg (fun p ↦ valAt' p ⊤ ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a)) e).trans (valAt'_id_top a))
    exact (valAt'_mul (u.ex z).left U ((secMap (str A) U).hom a) b).trans (congrArg (· * val u.ex U b z) k)
  have dA : ∀ (k : A.left.affineOpens → (Fin g → ℂ) → ℂ) (U : A.left.affineOpens),
      DifferentiableOn ℂ (k U) (pre u.ex U.1) → ∀ z ∈ pre u.ex U.1, DifferentiableAt ℂ (k U) z :=
    fun k U hk z hz ↦ hk.differentiableAt ((hO _).mem_nhds hz)
  refine ⟨fun x y q q' hx hy ↦ ?_, fun a x q hx ↦ ?_⟩
  · obtain ⟨c, h, rfl, ⟨h1, h2, h3⟩, hp⟩ := hx
    obtain ⟨c', h', rfl, ⟨h1', h2', h3'⟩, hp'⟩ := hy
    constructor
    · refine ⟨c + c', fun U z ↦ h U z + h' U z, map_add _ _ _,
        ⟨fun U ↦ (h1 U).add (h1' U), fun U V f z hz ↦ ?_, fun U z hz ↦ ?_⟩, fun U l z hz ↦ ?_⟩
      · change h V z + h' V z = (h U z + h' U z) + val u.ex V.1 (c.1.1 (op U) (op V) f + c'.1.1 (op U) (op V) f) z
        refine Eq.trans ?_ (congrArg _ (vadd V.1 _ _ z).symm)
        rw [h2 U V f z hz, h2' U V f z hz]; ring
      · change fderiv ℂ (fun z ↦ h U z + h' U z) z = evForm u.ex U.1 z (c.1.2 (op U) + c'.1.2 (op U))
        rw [fderiv_fun_add (dA h U (h1 U) z hz) (dA h' U (h1' U) z hz), map_add, h3 U z hz, h3' U z hz]
      · simp only [Pi.add_apply]
        rw [hp U l z hz, hp' U l z hz]; ring
    · refine ⟨c - c', fun U z ↦ h U z - h' U z, map_sub _ _ _,
        ⟨fun U ↦ (h1 U).sub (h1' U), fun U V f z hz ↦ ?_, fun U z hz ↦ ?_⟩, fun U l z hz ↦ ?_⟩
      · change h V z - h' V z = (h U z - h' U z) + val u.ex V.1 (c.1.1 (op U) (op V) f - c'.1.1 (op U) (op V) f) z
        refine Eq.trans ?_ (congrArg _ (vsub V.1 _ _ z).symm)
        rw [h2 U V f z hz, h2' U V f z hz]; ring
      · change fderiv ℂ (fun z ↦ h U z - h' U z) z = evForm u.ex U.1 z (c.1.2 (op U) - c'.1.2 (op U))
        rw [fderiv_fun_sub (dA h U (h1 U) z hz) (dA h' U (h1' U) z hz), map_sub, h3 U z hz, h3' U z hz]
      · simp only [Pi.sub_apply]
        rw [hp U l z hz, hp' U l z hz]; ring
  · obtain ⟨c, h, rfl, ⟨h1, h2, h3⟩, hp⟩ := hx
    refine ⟨a • c, fun U z ↦ a * h U z, map_smul _ _ _,
      ⟨fun U ↦ (h1 U).const_mul a, fun U V f z hz ↦ ?_, fun U z hz ↦ ?_⟩, fun U l z hz ↦ ?_⟩
    · change a * h V z = a * h U z + val u.ex V.1 (a • c.1.1 (op U) (op V) f) z
      refine Eq.trans ?_ (congrArg _ (vsmul V.1 a _ z hz).symm)
      rw [h2 U V f z hz]; ring
    · change fderiv ℂ (fun z ↦ a * h U z) z = evForm u.ex U.1 z (a • c.1.2 (op U))
      rw [fderiv_const_mul (dA h U (h1 U) z hz), map_smul, h3 U z hz]
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [hp U l z hz]; ring

end GlobalTheory.CechPer
