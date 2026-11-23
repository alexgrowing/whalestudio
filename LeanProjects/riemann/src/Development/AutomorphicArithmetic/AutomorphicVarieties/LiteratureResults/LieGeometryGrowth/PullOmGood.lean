import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullOmApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullOmHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullOmEquiv
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullPbBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.DEquiv
open UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Dr

theorem UpperTheory.V.Lit.Geo.omGood :
    OmGood := by
  intro Γ V S _ _ _ _ d G W hW q
  have hsub : ∀ (q : ℕ) (w w' : G.Om q), (∀ s, RadBasic G.Y (w.1 s)) → (∀ s, RadBasic G.Y (w'.1 s)) →
      ∀ s, RadBasic G.Y ((w - w').1 s) := by
    intro q w w' h h' s p hp v i hi
    have e : (w - w').1 s p v = w.1 s p v - w'.1 s p v := rfl
    rw [e, h s p hp v i hi, h' s p hp v i hi, sub_self]
  have hpb : ∀ (q : ℕ) (w : G.Om q), (∀ s, RadBasic G.Y (w.1 s)) → ∀ s, RadBasic G.Y ((pbOm G W w).1 s) := by
    intro q w h s p hp v i hi
    rw [(omApply Γ V S d G W hW q).1 w s p hp]
    exact (pbBasic V _ G.Y G.isOpen (W s) (hW.field s) (hW.homog s) q).1 _ (h s) p hp v i hi
  have hhom : ∀ (q : ℕ) (w : G.Om (q + 1)), (∀ s, RadBasic G.Y (w.1 s)) →
      ∀ s, RadBasic G.Y ((homOm G W w).1 s) := by
    intro q w h s p hp v i hi
    rw [(omApply Γ V S d G W hW q).2 w s p hp]
    exact (pbBasic V _ G.Y G.isOpen (W s) (hW.field s) (hW.homog s) q).2 _ (w.2 s).1 (h s) p hp v i hi
  obtain ⟨h1, h2, -, h4⟩ := omHom Γ V S d G W hW
  refine ⟨fun w hw => ⟨⟨fun γ => ?_, hpb q w hw.basic, ?_⟩, ⟨fun γ => ?_, hw.dbasic, ?_⟩⟩,
    fun w w' hw hw' => ⟨fun γ => ?_, hsub q w w' hw.basic hw'.basic, ?_⟩,
    fun w hw => ⟨fun γ => ?_, hhom q w hw.basic, ?_⟩⟩
  · rw [(omEquiv Γ V S d G W hW q γ).1 w, hw.inv γ]
  · rw [h1]
    exact hpb _ _ hw.dbasic
  · rw [← dEquiv Γ V S d G q γ w, hw.inv γ]
  · rw [h2]
    intro s p _ v i _
    rfl
  · rw [map_sub, hw.inv γ, hw'.inv γ]
  · rw [map_sub]
    exact hsub _ _ _ hw.dbasic hw'.dbasic
  · rw [(omEquiv Γ V S d G W hW q γ).2 w, hw.inv γ]
  · rw [eq_sub_of_add_eq (h4 q w).symm]
    exact hsub _ _ _ (hsub _ _ _ (hpb _ _ hw.basic) hw.basic) (hhom _ _ hw.dbasic)
