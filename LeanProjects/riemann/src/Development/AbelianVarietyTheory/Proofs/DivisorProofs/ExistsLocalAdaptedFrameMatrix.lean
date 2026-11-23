import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFramePullbackSections
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.FlagBundle GlobalTheory.ProjVar GlobalTheory.FlagCell GlobalTheory.FlagConnect GlobalTheory.CovTest GlobalTheory.FlagOverField
open GlobalTheory.Cartier
open scoped Classical
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.FlagOverField

theorem exists_adFrame_near : ∀ (F : Type) [Field F] (Y : Var F) (ι : Type) [Fintype ι] (r : ι → ℕ) (E : ι → (Sp F).Modules) (e : ∀ a, Fin (r a) → Γ(E a, ⊤)) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback Y.str).obj (E a)) (r a)), (∀ a, IsVB (E a) (r a)) → (∀ a, IsFrame (e a)) → ∀ y : Y.X, ∃ (U : Y.X.Opens) (A : Mat r Y.Fn), y ∈ U ∧ ∀ z ∈ U, AdFrame e fl z A := by
  intro F _ Y ι _ r E e fl hE he y
  haveI : ∀ a, (E a).IsQuasicoherent := fun a => (hE a).isQuasicoherent
  have hy : ∀ a, ∃ W : Y.X.Opens, y ∈ W ∧ ∃ M : Matrix (Fin (r a)) (Fin (r a)) Γ(Y.X, W),
      Spans (fl a) W (pullCol Y.str (e a) le_top M) := by
    intro a
    obtain ⟨W, hW, u, -, hs⟩ := GlobalTheory.FlagZ.Loc.exists_nested_frames (fl a) y (Fin.last (r a))
    obtain ⟨M, hM⟩ := exists_pullCol Y.str (he a) (le_top : W ≤ Y.str ⁻¹ᵁ ⊤)
      (fun j => ((fl a).ι (Fin.last _)).app W (u j))
    refine ⟨W, hW, M, ?_⟩
    have hsp : Spans (fl a) W (fun j => ((fl a).ι (Fin.last _)).app W (u j)) := fun l => hs l l.is_le
    convert hsp using 1
    funext j
    exact (hM j).symm
  choose W hyW M hM using hy
  refine ⟨Finset.univ.inf W, fun a => ((M a).map (fnOf (W a) (gen_mem (hyW a)))).transpose,
    by rw [← SetLike.mem_coe, TopologicalSpace.Opens.coe_finset_inf]; simpa using hyW, fun z hz a => ?_⟩
  have hzW : z ∈ W a := (Finset.inf_le (Finset.mem_univ a) : Finset.univ.inf W ≤ W a) hz
  exact ⟨W a, hzW, M a, hM a, rfl⟩

end GlobalTheory.FlagOverField
