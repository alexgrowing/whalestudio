import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelReps
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NontrivialDegenerationOutsideAbelianStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DvrArcExtensionMonoBaseStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DvrArcExtensionGenericFibreStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.TorRef
open ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.ArcExt

theorem exists_hasArcData_of_unif : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), Mono (spMap β) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (b : O →+* T.V) (y : Sp T.V ⟶ Y.X) (z : Sp T.Fr ⟶ Xo.XF c), (algebraMap T.V T.Fr).comp b = io.comp β → y ≫ Y.s = spMap b → z ≫ pullback.snd _ _ = spMap io → z ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ y → ∀ (t : SAB H (Sp T.V)) (_ : SABMap t Y.t y) (P : PELUnif (maximalIdeal T.V) t), P.TorsionIso → y (closedPoint T.V) ∉ abLocus Y.t.G → ∃ (T' : CDVR) (g : T.V →+* T'.V) (ϖ : T'.V) (a : ArcIn D l β T'.V (g.comp b)), Function.Injective g ∧ IsLocalHom g ∧ Irreducible ϖ ∧ Y.HasArcData a (Ideal.span {ϖ}) (RingHom.id T'.V) ϖ (spMap g ≫ y) := by
  intro E _ _ _ H D l Xo c O _ β Y hβ T io b y z hb hy hz hzj t m P hP hx
  obtain ⟨T', g, ϖ, io', z', t', m', P', hg, hloc, hϖ, hb', hz', hzj', hP', hdvd, hrep⟩ :=
    GlobalTheory.T.dvr_arc_extension_mono_base E H D l Xo c O β Y hβ T io b y z hb hy hz hzj t m P hP
  have hcl : (spMap g ≫ y) (closedPoint T'.V) ∉ abLocus Y.t.G := by
    have e : (spMap g) (closedPoint T'.V) = closedPoint T.V := IsLocalRing.comap_closedPoint g
    intro h
    apply hx
    rw [← e]
    exact h
  have hnt := GlobalTheory.T.nontrivial_degeneration_outside_abelian E H D l Xo c O β Y T' (spMap g ≫ y) t' m' P' hcl
  have hy' : (spMap g ≫ y) ≫ Y.s = spMap (g.comp b) := by
    rw [Category.assoc, hy]
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  obtain ⟨a, ha⟩ := GlobalTheory.T.dvr_arc_extension_generic_fibre E H D l Xo c O β Y T' io' (g.comp b) (spMap g ≫ y) z' hb' hy' hz' hzj' t' m' P' hP'
    hnt ϖ hϖ hdvd hrep
  exact ⟨T', g, ϖ, a, hg, hloc, hϖ, ha⟩

end GlobalTheory.ArcExt
