import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsLocalExtension
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenOfRangeGenericSubset

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.TorRef
open scoped CategoryTheory.Obj

namespace GlobalTheory.MemberUnif

theorem exists_ext_unif_torsionIso : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : CDVR) (io : c.F →+* T.Fr) (b : O →+* T.V) (y : Sp T.V ⟶ Y.X) (z : Sp T.Fr ⟶ Xo.XF c), (algebraMap T.V T.Fr).comp b = io.comp β → y ≫ Y.s = spMap b → z ≫ pullback.snd _ _ = spMap io → z ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ y → ∃ (T' : CDVR) (g : T.V →+* T'.V) (t : SAB H (Sp T'.V)) (_ : SABMap t Y.t (spMap g ≫ y)) (P : PELUnif (maximalIdeal T'.V) t), Function.Injective g ∧ IsLocalHom g ∧ P.TorsionIso := by
  intro E _ _ _ H D l Xo c O _ β Y T io b y z _ _ _ hz

  obtain ⟨t₀, ⟨m₀⟩⟩ : ∃ t₀ : SAB H (Sp T.V), Nonempty (SABMap t₀ Y.t y) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull CubePf.cubePull y Y.t
    exact ⟨_, ⟨m⟩⟩

  let F := AlgebraicClosure (FractionRing T.V)
  have hF : Function.Injective (algebraMap T.V F) := by
    rw [IsScalarTower.algebraMap_eq T.V (FractionRing T.V) F]
    exact (algebraMap (FractionRing T.V) F).injective.comp (IsFractionRing.injective T.V _)
  have : FaithfulSMul T.V F := (faithfulSMul_iff_algebraMap_injective _ _).2 hF
  have : Algebra.IsAlgebraic T.V F := (IsFractionRing.comap_isAlgebraic_iff (K := FractionRing T.V)).2 inferInstance
  obtain ⟨W, hd, hc, hf, hs⟩ := GlobalTheory.Ex.UnifModel.exists_split T.V F t₀.G t₀.semi
  have hi : Function.Injective (algebraMap T.V W) := fun _ _ h => hF (congrArg (fun w : W => (w : F)) h)
  have hz0 : CharZero W := charZero_of_injective_ringHom hi
  have : FaithfulSMul T.V W := (faithfulSMul_iff_algebraMap_injective _ _).2 hi
  have hl : IsLocalHom (algebraMap T.V W) := inferInstance
  obtain ⟨_, _, _, _, _, m₁, -⟩ := sabPull CubePf.cubePull (spMap (algebraMap T.V W)) t₀
  obtain ⟨m, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m₀ m₁

  obtain ⟨_, _, _, _, _, mz, -⟩ := sabPull CubePf.cubePull z Y.oF.t
  obtain ⟨mK, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ Y.m mz
  obtain ⟨mx, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ Y.m0.toSABMap mz
  have j : Function.Injective ((algebraMap W (FractionRing W)).comp (algebraMap T.V W)) :=
    (IsFractionRing.injective W _).comp hi
  let gm : T.Fr →+* FractionRing W := IsFractionRing.lift j
  have hp : PolAt _ (jK W) := GlobalTheory.UnifAfterExt.polAt_of_sabMap m mK mx Xo.univ.proper Xo.univ.ample Xo.univ.ktriv
    (jK W) (spMap gm) (by
      have e : spMap gm ≫ spMap (algebraMap T.V T.Fr) = jK W ≫ spMap (algebraMap T.V W) := by
        exact (GlobalTheory.Ex.UnifModel.spMap_comp (IsFractionRing.lift_algebraMap j)).trans
          (GlobalTheory.Ex.UnifModel.spMap_comp fun _ => rfl).symm
      rw [← Category.assoc, ← e, Category.assoc]
      exact congrArg (spMap gm ≫ ·) hz.symm)
  obtain ⟨P, hP⟩ := GlobalTheory.LN.uDvrSt_holds E H W ⟨hd, hc, hz0⟩ _ hp hs
  exact ⟨{ V := W }, algebraMap T.V W, _, m, P, hi, hl, hP⟩

end GlobalTheory.MemberUnif
