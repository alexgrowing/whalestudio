import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.CompatH
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.IsFirstChernClassOfLineBundle
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.RedGalBase
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.BetaGal

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem dd_twAcr (k : Bool) (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) (n : ℕ) :
    IsDPMorphism (DD k (tw σ A) n) (DD k A n) (twAcr σ A n) := by
  cases k
  exacts [dp_twAcr A σ n, dpP_twAcr A σ n]

theorem twAcr_fromBase (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) (n : ℕ) (r : (base l).Acr n) :
    twAcr σ A n (mapAcr (tw σ A).fromBase n r) = mapAcr A.fromBase n (galBase σ n r) := by
  have e : (tw σ A).fromBase = baseTw σ ≫ twMap σ A.fromBase := (fromBase_comp _ (twMap σ A.fromBase)).symm
  rw [e, mapAcr_comp, twAcr_mapAcr]
  rfl

theorem uJ_tw (k : Bool) (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) (n : ℕ) (h) (x : (tw σ A).U) :
    Ideal.quotientMap (JJ k A n) (twAcr σ A n) h (uJ k (tw σ A) n x) = uJ k A n (twU σ A x) := by
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.quotientMap (JJ k A n) (twAcr σ A n) h (uJ k (tw σ A) n ((tw σ A).th w)) = uJ k A n (twU σ A ((tw σ A).th w))
  rw [uJ_th, twU_th, uJ_th, Ideal.quotientMap_mk]
  exact congrArg (Ideal.Quotient.mk _) ((pdOk_twId σ A).acr_toAcr n w)

theorem map3 (P : CommRingCat.{0} ⥤ Type) {A B C D : Type} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    (f : A →+* B) (g : B →+* C) (h : C →+* D) (e : A →+* D) (he : ∀ x, h (g (f x)) = e x) (y : P.obj (CommRingCat.of A)) :
    P.map (CommRingCat.ofHom h) (P.map (CommRingCat.ofHom g) (P.map (CommRingCat.ofHom f) y)) = P.map (CommRingCat.ofHom e) y := by
  have e' : CommRingCat.ofHom f ≫ CommRingCat.ofHom g ≫ CommRingCat.ofHom h = CommRingCat.ofHom e :=
    CommRingCat.hom_ext (RingHom.ext he)
  rw [← e', Functor.map_comp_apply, Functor.map_comp_apply]

variable {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (σ : Gal(PadicAlgCl l/K))
  (hσ : ∀ x, galOC σ (κ x) = κ x) (k : Bool) (n : ℕ)

def etaGal (T : El (F.pt κ)) :
    (gT F κ k n).obj ((elTw σ (ptTw F κ σ hσ)).obj T) ⟶ (SH.galM F κ σ hσ k n).obj ((gT F κ k n).obj T) :=
  crHom (twAcr σ T.1.obj n) (twAcr_fromBase σ T.1.obj n) (dd_twAcr k σ T.1.obj n) fun h =>
    map3 F.Pt (twUEquiv σ T.1.obj).symm.toRingHom (uJ k (tw σ T.1.obj) n) (Ideal.quotientMap _ (twAcr σ T.1.obj n) h)
      (uJ k T.1.obj n) (fun x => (uJ_tw k σ T.1.obj n h _).trans
        (congrArg (uJ k T.1.obj n) ((twUEquiv σ T.1.obj).apply_symm_apply x))) T.2.1

theorem β_gal : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ x, galOC σ (κ x) = κ x) (k : Bool) (n j : ℕ) (x : Hc F κ k n j), β F κ k n j (galHc F κ σ hσ k n j x) = (galMor σ (ptTw F κ σ hσ) n).pull j (β F κ k n j x) := by
  intro l _ O _ F κ K σ hσ k n j x
  have h1 := pull_pull (ACris.galCris σ) (galMorC F κ σ hσ k n) (βMor F κ k n) j x
  have h2 := pull_pull (ACris.galCris σ) (βMor F κ k n) (galMor σ (ptTw F κ σ hσ) n) j x
  refine h1.trans (Eq.trans ?_ h2.symm)
  exact (cr_pull_eq ((βMor F κ k n).comp (σ'' := ACris.galCris σ) (galMor σ (ptTw F κ σ hσ) n))
    ((galMorC F κ σ hσ k n).comp (σ'' := ACris.galCris σ) (βMor F κ k n)) (etaGal F κ σ hσ k n)
    (fun f x => twAcr_mapAcr σ f.1.hom n x) (fun _ _ => rfl) j x).symm

end GlobalTheory.CompanionTheory.BetaGal
