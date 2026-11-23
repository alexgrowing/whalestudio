import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw

namespace GlobalTheory.Div

theorem resG_eq_inv_mul_appLE {X X' : Scheme.{0}} {H : LB X} {H' : LB X'} {φ : X' ⟶ X}
    (w : LB.Iso H' (H.pull φ)) (k : H.ι) (k' : H'.ι) (a : Γ(X, H.U k)) (b : Γ(X', H'.U k'))
    (h : ∀ z, φ z ∈ H.U k → z ∈ H'.U k' →
      gs φ z _ a = (Geo.Tor.gw w (𝟙 _) z k k').val * gs (𝟙 _) z _ b) :
    resG X' (inf_le_right : (H.pull φ).U (fun _ => k) ⊓ H'.U k' ≤ H'.U k') b =
      ((@id (Γ(X', (H.pull φ).U (fun _ => k) ⊓ H'.U k')ˣ) (w.s (fun _ => k, k')))⁻¹).val *
        (φ.appLE (H.U k) ((H.pull φ).U (fun _ => k) ⊓ H'.U k')
          (inf_le_left.trans (GlobalTheory.Cartier.pull_U H φ _).le)).hom a := by
  apply fn_ext
  intro x hx
  have hk : φ x ∈ H.U k := (GlobalTheory.Cartier.pull_U H φ _).le hx.1
  have hx' : x ∈ H'.U k' := hx.2
  have e := h x hk hx'
  have h1 : gs (𝟙 X') x _ (resG X' (inf_le_right : (H.pull φ).U (fun _ => k) ⊓ H'.U k' ≤ H'.U k') b) =
      gs (𝟙 X') x _ b := gs_res (𝟙 X') x inf_le_right hx b
  have h2 : gs (𝟙 X') x _ ((φ.appLE (H.U k) ((H.pull φ).U (fun _ => k) ⊓ H'.U k')
      (inf_le_left.trans (GlobalTheory.Cartier.pull_U H φ _).le)).hom a) = gs φ x _ a := by
    have := gs_res (𝟙 X') x (inf_le_left.trans (GlobalTheory.Cartier.pull_U H φ _).le) hx ((φ.app (H.U k)).hom a)
    refine Eq.trans ?_ (this.trans ((gs_pull (𝟙 X') φ x (H.U k) hk a).trans (by rw [Category.id_comp])))
    rfl
  have h3 : gs (𝟙 X') x _ (((@id (Γ(X', (H.pull φ).U (fun _ => k) ⊓ H'.U k')ˣ) (w.s (fun _ => k, k')))⁻¹).val) =
      ((Geo.Tor.gw w (𝟙 _) x k k')⁻¹).val := by
    rw [gs_unit (𝟙 X') x _ hx, map_inv]
    rfl
  rw [h1, gs_mul (𝟙 X') x _ hx, h2, h3, e, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

theorem isClosedImmersion_of_veryAmpleBy_compat : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ (X' : Scheme.{0}) (f' : X' ⟶ Spec (CommRingCat.of R)) (H' : LB X') (s' : Fin (n + 1) → LB.Sec H') (φ : X' ⟶ X) (w : LB.Iso H' (H.pull φ)), H'.IsLB → VeryAmpleBy f' H' s' → φ ≫ f = f' → w.IsGen → (∀ j, (∀ z (k : (H).ι) (k' : (H').ι), (φ) z ∈ (H).U k → z ∈ (H').U k' → gs (φ) z _ ((s j).f k) = (Geo.Tor.gw (w) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s' j).f k'))) → IsClosedImmersion φ := by
  intro R _ X f H n s hH hs X' f' H' s' φ w hH' hs' hf _ hrel
  subst hf
  obtain ⟨hc, hci⟩ := (GlobalTheory.ProjSpace.veryAmpleBy_iff f s).1 hs
  obtain ⟨hc', hci'⟩ := (GlobalTheory.ProjSpace.veryAmpleBy_iff (φ ≫ f) s').1 hs'
  have heq : GlobalTheory.ProjSpace.toProj (φ ≫ f) s' hc' = φ ≫ GlobalTheory.ProjSpace.toProj f s hc := by
    refine GlobalTheory.ProjSpace.toProj_eq_comp_of_locally hc φ hc' fun z => ?_
    obtain ⟨k, hk⟩ := exists_chart hH (φ z)
    obtain ⟨k', hk'⟩ := exists_chart hH' z
    exact ⟨(H.pull φ).U (fun _ => k) ⊓ H'.U k', ⟨(GlobalTheory.Cartier.pull_U H φ _).ge hk, hk'⟩, k,
      inf_le_left.trans (GlobalTheory.Cartier.pull_U H φ _).le, k', inf_le_right, _,
      fun j => resG_eq_inv_mul_appLE w k k' _ _ fun y hy hy' => hrel j y k k' hy hy'⟩
  have : IsClosedImmersion (φ ≫ GlobalTheory.ProjSpace.toProj f s hc) := heq ▸ hci'
  exact IsClosedImmersion.of_comp_isClosedImmersion φ (GlobalTheory.ProjSpace.toProj f s hc)

end GlobalTheory.Div
