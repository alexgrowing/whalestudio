import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsPullSnd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ScaleGenIsGen

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR

variable {X X' Y : Scheme.{0}} {K K' : Type} [Fintype K] [Fintype K']

theorem sec_of_units {M : LB X} {M' : LB X'} (hM : M.IsLB) (hM' : M'.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X')}
    {ε' : K' → ℤ} (u : ∀ p q, Γ(Y, LB.wchart M φ p ⊓ LB.wchart M' φ' q)ˣ)
    (hu : ∀ (y : Y) p p' q q', y ∈ LB.wchart M φ p → y ∈ LB.wchart M φ p' → y ∈ LB.wchart M' φ' q → y ∈ LB.wchart M' φ' q' →
      gm (𝟙 Y) y _ (u p q) * trF φ ε (𝟙 Y) y p p' = trF φ' ε' (𝟙 Y) y q q' * gm (𝟙 Y) y _ (u p' q'))
    (s : LB.Sec (LB.LinComb M φ ε)) : ∃ s' : LB.Sec (LB.LinComb M' φ' ε'), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) p q,
      r z ∈ LB.wchart M φ p → r z ∈ LB.wchart M' φ' q →
      gs r z (LB.wchart M' φ' q) (s'.f q) = (gm r z _ (u p q)).val * gs r z (LB.wchart M φ p) (s.f p) := by
  have ch : ∀ y : Y, ∃ p, y ∈ LB.wchart M φ p := fun y => by
    choose p hp using fun k => exists_chart hM (φ k y)
    exact ⟨p, Set.mem_iInter.2 hp⟩
  let sp : ∀ p q, Γ(Y, LB.wchart M φ p ⊓ LB.wchart M' φ' q) := fun p q =>
    (u p q).val * (Y.presheaf.map (homOfLE (inf_le_left : LB.wchart M φ p ⊓ LB.wchart M' φ' q ≤ LB.wchart M φ p)).op).hom (s.f p)
  have hv : ∀ {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) p q (h : r z ∈ LB.wchart M φ p ⊓ LB.wchart M' φ' q),
      gs r z _ (sp p q) =
        (gm r z _ (u p q)).val * gs r z (LB.wchart M φ p) (s.f p) := fun r z p q h =>
    (gs_mul r z _ h _ _).trans (congrArg₂ (· * ·) (gs_unit r z _ h _) (gs_res r z _ h _))
  have tr : ∀ (y : Y) p p' q q', y ∈ LB.wchart M φ p → y ∈ LB.wchart M φ p' → y ∈ LB.wchart M' φ' q → y ∈ LB.wchart M' φ' q' →
      (gm (𝟙 Y) y _ (u p q)).val * gs (𝟙 Y) y (LB.wchart M φ p) (s.f p) =
        (trF φ' ε' (𝟙 Y) y q q').val * ((gm (𝟙 Y) y _ (u p' q')).val * gs (𝟙 Y) y (LB.wchart M φ p') (s.f p')) :=
    fun y p p' q q' a b c d => by
      rw [sec_trans s (𝟙 Y) y a b, ← _root_.mul_assoc, ← Units.val_mul, hu y p p' q q' a b c d, Units.val_mul, _root_.mul_assoc]
  have glue : ∀ q, ∃ f : Γ(Y, LB.wchart M' φ' q), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) p, r z ∈ LB.wchart M φ p →
      r z ∈ LB.wchart M' φ' q → gs r z _ f = (gm r z _ (u p q)).val * gs r z (LB.wchart M φ p) (s.f p) := fun q => by
    obtain ⟨f, hf, -⟩ := Y.sheaf.existsUnique_gluing' (fun p => LB.wchart M φ p ⊓ LB.wchart M' φ' q) (LB.wchart M' φ' q)
      (fun _ => homOfLE inf_le_right) (fun y hy => let ⟨p, hp⟩ := ch y; TopologicalSpace.Opens.mem_iSup.2 ⟨p, hp, hy⟩)
      (fun p => sp p q) fun p p' => fn_ext fun y hy =>
        ((gs_res _ y inf_le_left hy _).trans ((hv _ y p q hy.1).trans ((tr y p p' q q hy.1.1 hy.2.1 hy.1.2 hy.1.2).trans (by
          rw [trF_self hM' _ _ (𝟙 Y) y hy.1.2, Units.val_one, _root_.one_mul])))).trans
          ((gs_res _ y inf_le_right hy _).trans (hv _ y p' q hy.2)).symm
    exact ⟨f, fun Z r z p a b => (gs_res r z inf_le_right (show r z ∈ LB.wchart M φ p ⊓ LB.wchart M' φ' q from ⟨a, b⟩) f).symm.trans
      ((congrArg _ (hf p)).trans (hv r z p q ⟨a, b⟩))⟩
  choose f hf using glue
  refine ⟨⟨f, fun q q' => fn_ext fun y hy => ?_⟩, fun Z r z p q => hf q Z r z p⟩
  obtain ⟨p, hp⟩ := ch y
  exact ((gs_res _ y _ hy _).trans ((hf q _ (𝟙 Y) y p hp hy.1).trans (tr y p p q q' hp hp hy.1 hy.2))).trans ((gs_mul _ y _ hy _ _).trans
    (congrArg₂ (· * ·) ((gs_unit _ y _ hy _).trans (congrArg Units.val (gm_linComb M' φ' ε' (𝟙 Y) y q q' hy.1 hy.2)))
      ((gs_res _ y _ hy _).trans (hf q' _ (𝟙 Y) y p hp hy.2)))).symm

variable {L : LB X} {L' : LB X'} {F : X' ⟶ X} {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB)
  {φ' : K → (Y ⟶ X')} {ε : K → ℤ}
include hw hL hL'

theorem sec_upK (s : LB.Sec (LB.LinComb L' φ' ε)) : ∃ s' : LB.Sec (LB.LinComb L (fun k => φ' k ≫ F) ε),
    ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) J J', Good L z J → Good L' z J' → sval s' r z J =
      (pw w φ' ε r z (fun k => J (r ≫ φ' k ≫ F)) fun k => J' (r ≫ φ' k)).val * sval s r z J' := by
  choose u hu using fun p q => exists_pw w φ' ε p q
  have e : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) p q, r z ∈ LB.wchart L' φ' q ⊓ LB.wchart L (fun k => φ' k ≫ F) p →
      gm r z _ (res (inf_comm _ _).le (u p q)) = pw w φ' ε r z p q := fun Z r z p q h =>
    (gm_res r z _ h _).trans (hu p q Z r z ⟨h.2, h.1⟩)
  obtain ⟨s', hs⟩ := sec_of_units hL' hL (ε' := ε) (fun q p => res (inf_comm _ _).le (u p q)) (fun y q q' p p' a b c d => by
    rw [e _ _ y p q ⟨a, c⟩, e _ _ y p' q' ⟨b, d⟩, pw_trans hw φ' ε (𝟙 Y) y c d a b, _root_.mul_assoc, _root_.mul_assoc,
      mul_left_comm (trF φ' ε (𝟙 Y) y q q')⁻¹, inv_mul_cancel, _root_.mul_one]) s
  exact ⟨s', fun Z r z J J' hJ hJ' => (hs Z r z _ _ (hJ'.mem _ r) (hJ.mem _ r)).trans
    (congrArg (·.val * _) (e Z r z _ _ ⟨hJ'.mem _ r, hJ.mem _ r⟩))⟩

omit hw

variable {Y₀ : Scheme.{0}} {f₁ : Y₀ ⟶ X'} {f₂ : Y₀ ⟶ X} {W : LB.Iso (L'.pull f₁) (L.pull f₂)} (hW : W.IsGen)
  (m : K → (Y ⟶ Y₀)) {ψ : K → (Y ⟶ X')} (e : ∀ k, m k ≫ f₁ = ψ k)
include hW e

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
