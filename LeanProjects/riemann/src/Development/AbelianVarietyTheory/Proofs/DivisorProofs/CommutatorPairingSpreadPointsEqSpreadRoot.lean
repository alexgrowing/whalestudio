import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemePullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumPair

theorem weilIs_of_spread : ∀ (Ω T : Type) [Field Ω] [CommRing T] [IsDomain T] [IsNoetherianRing T] (jT : T →+* Ω), Function.Injective jT → ∀ (A : PolAV (Sp Ω)) (P : PolAV (Sp T)) (φ : A.A.left ⟶ P.A.left), IsGrpPullback A.A P.A (spMap jT) φ → LBIso A.L (P.L.pull φ) → ∀ (k : ℕ) (x x' : baseOver (Sp Ω) ⟶ A.A) (y y' : baseOver (Sp T) ⟶ P.A) (c : Tˣ), 1 ≤ k → x.left ≫ φ = spMap jT ≫ y.left → x'.left ≫ φ = spMap jT ≫ y'.left → y ^ k = 1 → y' ^ k = 1 → WeilIs A.A A.L k x x' (unitOn (Units.map jT.toMonoidHom c)) → WeilIs P.A P.L k y y' (unitOn c) := by
  intro Ω T _ _ _ _ jT hj A P φ hp hw k x x' y y' c hk hx hx' hy hy' hW
  obtain ⟨⟨hL, -⟩, -⟩ := GlobalTheory.lawsAndExpansions
  haveI : IsCommMonObj A.A := A.isAb.comm
  haveI : IsLocallyNoetherian (Sp T) := inferInstance
  haveI : IsLocallyNoetherian (Sp Ω) := inferInstance
  obtain ⟨c₀, hc₀, -⟩ := (hL.weil (Sp T) P k (baseOver _)).1 y y' hy hy'
  let h : Over.mk ((baseOver (Sp Ω)).hom ≫ spMap jT) ⟶ baseOver (Sp T) := Over.homMk (spMap jT) (by simp)
  have H1 := GlobalTheory.CommPairing.weilIs_pull hL.globalFns P.isAb P.isLB h hc₀
  have H2 := (GlobalTheory.weilIs_grpPullback_of_comm' (Sp T) (Sp Ω) P.A A.A (spMap jT) φ P.L A.L P.isLB A.isLB hp hw
    (baseOver (Sp Ω)) k x x' (h ≫ y) (h ≫ y') _ hx.symm hx'.symm).2 H1
  have inj : ∀ a b : baseOver (Sp Ω) ⟶ A.A, a.left ≫ φ = b.left ≫ φ → a = b := by
    intro a b e
    apply Over.OverMorphism.ext
    apply hp.1.hom_ext e
    rw [Over.w, Over.w]
  have tors : ∀ (a : baseOver (Sp Ω) ⟶ A.A) (b : baseOver (Sp T) ⟶ P.A), a.left ≫ φ = spMap jT ≫ b.left →
      b ^ k = 1 → a ^ k = 1 := by
    intro a b e hb
    apply inj
    have e1 : (ReciprocityTheory.ChartRestriction.G.Geo.Tor.pushHom hp (baseOver (Sp Ω)) (a ^ k)) = (h ≫ b) ^ k := by
      rw [map_pow]
      congr 1
      exact Over.OverMorphism.ext e
    have e2 : (ReciprocityTheory.ChartRestriction.G.Geo.Tor.pushHom hp (baseOver (Sp Ω)) 1) = (h ≫ b) ^ k := by
      rw [map_one, ← MonObj.comp_pow, hb, MonObj.comp_one]
    exact (congrArg (fun z => z.left) e1).trans (congrArg (fun z => z.left) e2).symm
  have hxk := tors x y hx hy
  have hxk' := tors x' y' hx' hy'
  have U := (hL.weil (Sp Ω) A k (baseOver _)).1 x x' hxk hxk'
  have e3 := U.unique H2 hW
  have nat : ∀ a : T, (spMap jT).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom a) =
      (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (jT a) := by
    intro a
    have := congrArg (fun f => f.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom jT))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
    exact this.symm
  have ginj : Function.Injective (spMap jT).appTop.hom := by
    intro a b e
    have ea : a = (Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of T)).hom.hom a) := by
      simp
    have eb : b = (Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of T)).hom.hom b) := by
      simp
    rw [ea, eb, nat, nat] at e
    have e' := congrArg (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom e
    have key : ∀ z, (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom z) = z :=
      fun z => by simp
    rw [key, key] at e'
    rw [ea, eb, hj e']
  have e4 : c₀ = unitOn c := by
    apply Units.ext
    apply ginj
    exact (congrArg Units.val e3).trans (nat (c : T)).symm
  rw [← e4]
  exact hc₀

end GlobalTheory.MumPair
