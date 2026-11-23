import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RealMoveOfParts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedStatesRationalFormsCorrespondCoordinatewisStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedStatesSupLatticeMemIffCoordinateImageStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedStatesCorrespondingFormsSameAdelicFunctionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedStatesGeometricActionsCorrespondStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedStatesFiniteGroupCharactersCorrespondStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
open GlobalTheory.HeightCounting.SerMove

namespace GlobalTheory.HeightCounting.SerMove.FormsMove

theorem coord_eq_iff {L L' : Type} [Field L] [Field L'] (ι : L →+* L') {n n' : ℕ} (hn : n = n') {a b : Fin n → L}
    {a' b' : Fin n' → L'} (ha : ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → a' k' = ι (a k))
    (hb : ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → b' k' = ι (b k)) : a = b ↔ a' = b' := by
  subst hn
  refine ⟨fun h => funext fun k => ?_, fun h => funext fun k => ι.injective ?_⟩
  · rw [ha k k rfl, hb k k rfl, h]
  · rw [← ha k k rfl, ← hb k k rfl, h]

theorem coord_smul {L L' F F' : Type} [Field L] [Field L'] [Field F] [Field F'] [Algebra F L] [Algebra F' L'] (ι : L →+* L')
    {n n' : ℕ} (hn : n = n') {W : Submodule F (Fin n → L)} {W' : Submodule F' (Fin n' → L')} (φ : W → W')
    (hφ : ∀ (y : W) (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → (φ y).1 k' = ι (y.1 k)) {c : F} {c' : F'}
    (hc : algebraMap F' L' c' = ι (algebraMap F L c)) (y : W) : φ (c • y) = c' • φ y := by
  subst hn
  refine Subtype.ext (funext fun k => ?_)
  rw [hφ _ k k rfl]
  change ι (c • y.1 k) = c' • (φ y).1 k
  rw [hφ _ k k rfl, Algebra.smul_def, Algebra.smul_def, map_mul, hc]

theorem formsCl_of_link : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'} (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0) (g : Geo x) (g' : Geo x'), Link x x' ι e g g' → ∀ (hg : GlobalTheory.RealGeo.InGeo g) (hg' : GlobalTheory.RealGeo.InGeo g') (a : BigHost (Dof x)) (a' : BigHost (Dof x')), ∀ (eK : ↥(sideAt x g hg a).core.Q.c.F ≃+* ↥(sideAt x' g' hg' a').core.Q.c.F) (γ : (sideAt x g hg a).Γ ≃* (sideAt x' g' hg' a').Γ), (∀ y, ((eK y : ↥(sideAt x' g' hg' a').core.Q.c.F) : ℂ) = (y : ℂ)) → (∀ u, HEq (γ u) u) → FormsCl (sideAt x g hg a) (sideAt x' g' hg' a') ι eK γ := by
  intro K B B' f f' T T' w w' P P' x x' ι e g g' l hg hg' a a' eK γ heK hγ
  have halg : ∀ c, algebraMap _ (Dof x').what₂.LL (eK c) = ι (algebraMap (sideAt x g hg a).core.Q.c.F (Dof x).what₂.LL c) := by
    intro c
    apply (Dof x').what₂.embLL.injective
    rw [l.cp.embLL]
    exact (x'.m.z.alg_eq (eK c)).trans ((heK c).trans (x.m.z.alg_eq c).symm)
  have hphi := fun j j' h => (GlobalTheory.T.linkedStates_rationalForms_correspond_coordinatewise x x' ι e g g' l hg hg' a a' j j' h)
  choose hn φ hφ using hphi
  refine ⟨fun j j' h => { φ := φ j j' h, alg := halg, smul := ?_, mk_iff := ?_, rho := ?_, chi := ?_ }, ?_⟩
  · intro c y
    exact coord_smul ι (hn j j' h) (φ j j' h) (hφ j j' h) (halg c) y
  · intro y
    exact GlobalTheory.T.linkedStates_supLattice_mem_iff_coordinateImage x x' ι e g g' l hg hg' a a' j j' h y.1 (φ j j' h y).1 (hφ j j' h y) y.2
  · intro u y z
    exact coord_eq_iff ι (hn j j' h)
      (GlobalTheory.T.linkedStates_geometricActions_correspond x x' ι e g g' l hg hg' a a' γ hγ j j' h y.1 (φ j j' h y).1 (hφ j j' h y) u) (hφ j j' h z)
  · intro u
    exact GlobalTheory.T.linkedStates_finiteGroupCharacters_correspond x x' ι e g g' l hg hg' a a' γ hγ j j' h u
  · intro j j' h y
    exact GlobalTheory.T.linkedStates_corresponding_forms_same_adelicFunctions x x' ι e g g' l hg hg' a a' j j' h y.1 (φ j j' h y).1 (hφ j j' h y)

end GlobalTheory.HeightCounting.SerMove.FormsMove
