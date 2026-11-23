import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFramePullbackSections

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.FlagBundle GlobalTheory.ProjVar GlobalTheory.FlagCell GlobalTheory.FlagConnect GlobalTheory.CovTest GlobalTheory.FlagOverField
open scoped Classical

namespace GlobalTheory.FlagOverField

open GlobalTheory.Cartier

theorem exists_fnOf_family {X : Scheme.{0}} [IsIntegral X] {y : X} {κ : Type} [Finite κ] {f : κ → X.functionField}
    (hf : ∀ k, RegAt y (f k)) {U : X.Opens} (hU : y ∈ U) :
    ∃ (V : X.Opens) (hV : y ∈ V) (_ : V ≤ U) (a : κ → Γ(X, V)), ∀ k, fnOf V (gen_mem hV) (a k) = f k := by
  choose W hW a ha using fun k => (hf k).exists_fnOf
  let V : X.Opens := ⟨(U : Set X) ∩ ⋂ k, (W k : Set X), U.isOpen.inter (isOpen_iInter_of_finite fun k => (W k).isOpen)⟩
  have hle (k : κ) : V ≤ W k := fun x hx => Set.mem_iInter.1 hx.2 k
  refine ⟨V, ⟨hU, Set.mem_iInter.2 hW⟩, fun x hx => hx.1, fun k => resG X (hle k) (a k), fun k => ?_⟩
  rw [fnOf_resG, ha]

theorem adFrame_par_mul (F : Type) [Field F] (Y : Var F) (ι : Type) [Fintype ι] (r : ι → ℕ) (E : ι → (Sp F).Modules)
    (e : ∀ a, Fin (r a) → Γ(E a, ⊤))
    (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback Y.str).obj (E a)) (r a))
    (_ : ∀ a, IsVB (E a) (r a)) (_ : ∀ a, IsFrame (e a)) (y : Y.X) (A g : Mat r Y.Fn)
    (hA : AdFrame e fl y A) (hg : Par r ((ratOf Y).O y).toSubring g) : AdFrame e fl y (g * A) := by
  intro a
  obtain ⟨U, hy, M, hM, hAM⟩ := hA a
  obtain ⟨h₁, h₂, h₃, h₄⟩ := hg a
  obtain ⟨V, hV, hVU, s, hs⟩ := exists_fnOf_family (y := y) (κ := Option (Fin (r a) × Fin (r a)))
    (f := fun k => k.elim (g a).det⁻¹ fun p => g a p.2 p.1)
    (fun k => by
      cases k with
      | none => exact mem_O_ratOf.1 h₃
      | some p => exact mem_O_ratOf.1 (h₁ p.2 p.1)) hy
  let T : Matrix (Fin (r a)) (Fin (r a)) Γ(Y.X, V) := Matrix.of fun i j => s (some (i, j))
  have hT : T.map (fnOf V (gen_mem hV)) = (g a).transpose := by
    ext i j
    exact hs (some (i, j))
  have hinj := fnOf_injective V (gen_mem hV)
  have hu : T.BlockTriangular id := fun i j hij => hinj (by
    rw [map_zero]
    exact (hs (some (i, j))).trans (h₄ j i j.2 hij))
  have hd : IsUnit T.det := by
    refine IsUnit.of_mul_eq_one (s none) (hinj ?_)
    rw [map_mul, map_one, RingHom.map_det, RingHom.mapMatrix_apply, hT, Matrix.det_transpose, hs none]
    exact mul_inv_cancel₀ h₂
  refine ⟨V, hV, M.map (resG Y.X hVU) * T,
    spans_pullCol_mul Y.str (e a) le_top (spans_pullCol_res Y.str (e a) le_top hVU hM) hu hd, ?_⟩
  have hM' : (M.map (resG Y.X hVU)).map (fnOf V (gen_mem hV)) = M.map (fnOf U (gen_mem hy)) := by
    ext i j
    exact fnOf_resG hVU _ _
  rw [Matrix.map_mul, hT, hM', Matrix.transpose_mul, Matrix.transpose_transpose, ← hAM]
  rfl

end GlobalTheory.FlagOverField
