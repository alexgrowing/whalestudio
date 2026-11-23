import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.ProjectiveNotIsUnit
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

namespace GlobalTheory.FormalAlg

theorem gs_comp_stalkMap {Z Y X : Scheme.{0}} (r : Z ⟶ Y) (F : Y ⟶ X) (z : Z) (U : X.Opens) (h : F (r z) ∈ U)
    (a : Γ(X, U)) :
    gs (r ≫ F) z U a = (Scheme.Hom.stalkMap r z).hom (gs F (r z) U a) := by
  rw [← gs_pull r F z U h, gs_stalkMap r z _ h, gs_pull (𝟙 _) F (r z) U h, Category.id_comp]

theorem gm_val_stalkMap {Z Y : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (V : Y.Opens) (h : r z ∈ V) (u : Γ(Y, V)ˣ) :
    ((gm r z V u : (Z.presheaf.stalk z)ˣ) : Z.presheaf.stalk z) =
      (Scheme.Hom.stalkMap r z).hom ((gm (𝟙 Y) (r z) V u : (Y.presheaf.stalk (r z))ˣ) : Y.presheaf.stalk (r z)) := by
  rw [← gs_unit r z V h, ← gs_unit (𝟙 Y) (r z) V h, gs_stalkMap r z V h]

theorem gw_comp_of_rel : ∀ (X Y' Y : Scheme.{0}) (b' : Y' ⟶ X) (β : Y ⟶ Y') (b : Y ⟶ X), β ≫ b' = b → ∀ (A : LB X) (H' : LB Y') (H : LB Y) (w' : LB.Iso H' (A.pull b')) (v : LB.Iso H (H'.pull β)) (w : LB.Iso H (A.pull b)) (ι : Type) (s : ι → LB.Sec A) (s' : ι → LB.Sec H') (s'' : ι → LB.Sec H), (∀ j, Rel b' w' (s j) (s' j)) → (∀ j, Rel β v (s' j) (s'' j)) → (∀ j, Rel b w (s j) (s'' j)) → (⨆ j, nonzeroLocus (s'' j) = ⊤) → ∀ z k k' k'', b z ∈ A.U k → β z ∈ H'.U k' → z ∈ H.U k'' → Geo.Tor.gw w (𝟙 _) z k k'' = Geo.Tor.gw w' β z k k' * Geo.Tor.gw v (𝟙 _) z k' k'' := by
  intro X Y' Y b' β b hb A H' H w' v w ι s s' s'' h₁ h₂ h₃ hc z k k' k'' hk hk' hk''
  subst hb

  have hz : z ∈ ⨆ j, nonzeroLocus (s'' j) := by rw [hc]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
  obtain ⟨k₀, hk₀, hu₀⟩ := (mem_nonzeroLocus (s'' j) z).1 hj
  have hu : IsUnit (gs (𝟙 Y) z (H.U k'') ((s'' j).f k'')) := by
    rw [gs_compat (s'' j) (𝟙 Y) z hk'' hk₀]
    exact (Units.isUnit _).mul hu₀
  have hkb : b' (β z) ∈ A.U k := hk
  have e₁ := h₁ j (β z) k k' hkb hk'
  have e₂ := h₂ j z k' k'' hk' hk''
  have e₃ := h₃ j z k k'' hk hk''
  have hV : β z ∈ (A.pull b').U (fun _ => k) ⊓ H'.U k' := ⟨mem_pull.2 hkb, hk'⟩
  have e₁' := congrArg (Scheme.Hom.stalkMap β z).hom e₁
  rw [map_mul, ← gs_comp_stalkMap β b' z _ hkb, ← gs_stalkMap β z _ hk'] at e₁'
  have hw' : ((Geo.Tor.gw w' β z k k' : (Y.presheaf.stalk z)ˣ) : Y.presheaf.stalk z) =
      (Scheme.Hom.stalkMap β z).hom ((Geo.Tor.gw w' (𝟙 _) (β z) k k' : (Y'.presheaf.stalk (β z))ˣ) :
        Y'.presheaf.stalk (β z)) :=
    gm_val_stalkMap β z _ hV _
  rw [← hw', e₂] at e₁'
  rw [e₃, ← _root_.mul_assoc, ← Units.val_mul] at e₁'
  exact Units.ext (hu.mul_left_inj.1 e₁')

end GlobalTheory.FormalAlg
