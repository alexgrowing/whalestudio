import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pExtGood :
    (∀ {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R) (L : Type) [Field L] [Algebra R L] {Z Y : Scheme.{0}} (p : Z ⟶ B) (q : Y ⟶ B) (s : Y ⟶ Z) (tr : T.H q →ₗ[R] T.H p), T.IsTr p q s tr → (T.ext L).IsTr p q s (tr.baseChange L)) → ExtGood.{u} := by
  intro htr B R _ T L _ _ hG
  refine ⟨?_, ?_⟩
  · intro Z W p r c hc G _ _ a hgal
    have hinj := hG.inj p r c hc G a hgal
    show Function.Injective (LinearMap.baseChange L (T.pull c hc))
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ hinj
  · intro Z Y p q s _ _ hs
    obtain ⟨tr, htr'⟩ := hG.tr p q s hs
    exact ⟨tr.baseChange L, htr T L p q s tr htr'⟩
