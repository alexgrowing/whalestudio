import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PulledRead
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSimilitudeFixingPointEqOne

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.caseE_of :
    SameE → KerU → KerFromU → IsoOfKer → ImgEq → PulledRead → CaseE := by
  intro hSE hKU hKF hIK hIE hPR p _ D O _ _ _ _ f b N r w _ hstd M j c T κ _ _ x σ hxσ o₁ m₁ y y' hy hy'
    P P' d hR hR' hcard hiff
  have hw : w ≠ ⊤ := Ideal.IsMaximal.ne_top ‹_›
  obtain ⟨⟨k, hk⟩, hmon, hact, -, -, ψi, hmoni, h1, h2⟩ := P.isog
  obtain ⟨⟨k', hk'⟩, hmon', hact', -, -, ψi', hmoni', h1', h2'⟩ := P'.isog
  replace h1 : P.ψ ≫ ψi = 𝟙 o₁.A ^ p ^ k := h1.trans (by rw [hk])
  replace h2 : ψi ≫ P.ψ = 𝟙 P.o'.A ^ p ^ k := h2.trans (congrArg (fun n => 𝟙 P.o'.A ^ n) hk)
  have hS : IsSub o₁.A (UKer r o₁ P.ψ) :=
    (hKU p D O b N r w hw hstd.ule (Sp κ) σ o₁ P.o' P.ψ ψi k hmon hmoni hact h1 h2).2.1
  replace h1' : P'.ψ ≫ ψi' = 𝟙 o₁.A ^ p ^ k' := h1'.trans (by rw [hk'])
  replace h2' : ψi' ≫ P'.ψ = 𝟙 P'.o'.A ^ p ^ k' := h2'.trans (congrArg (fun n => 𝟙 P'.o'.A ^ n) hk')
  have hS' : IsSub o₁.A (UKer r o₁ P'.ψ) :=
    (hKU p D O b N r w hw hstd.ule (Sp κ) σ o₁ P'.o' P'.ψ ψi' k' hmon' hmoni' hact' h1' h2').2.1
  have hcard' : Nat.card { g // UKer r o₁ P'.ψ (𝟙_ (Over (Sp κ))) g } = d := by
    rw [← hcard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun g => (hiff g).symm)
  have e₁ := hSE p D O b N r κ σ o₁ P.o' P'.o' P.ψ P'.ψ hmon' hS d hR hcard
    (fun g hg => ((hiff g).1 hg).1)
  have e₂ := hSE p D O b N r κ σ o₁ P'.o' P.o' P'.ψ P.ψ hmon hS' d hR' hcard'
    (fun g hg => ((hiff g).2 hg).1)
  have hU : ∀ (U : Over (Sp κ)) (g : U ⟶ o₁.A), UKer r o₁ P.ψ U g ↔ UKer r o₁ P'.ψ U g :=
    fun U g => ⟨e₁ U g, e₂ U g⟩
  have hK : ∀ (U : Over (Sp κ)) (g : U ⟶ o₁.A), g ≫ P.ψ = 1 ↔ g ≫ P'.ψ = 1 := fun U g =>
    ⟨hKF p D O b N r w hw hstd.ule κ σ c o₁ P.o' P'.o' P.ψ P'.ψ P.isog P'.isog hU U g,
      hKF p D O b N r w hw hstd.ule κ σ c o₁ P'.o' P.o' P'.ψ P.ψ P'.isog P.isog
        (fun U g => (hU U g).symm) U g⟩
  obtain ⟨m, hm⟩ := hIK p D O b N κ σ c o₁ P.o' P'.o' P.ψ P'.ψ P.isog P'.isog hK
  obtain ⟨n₁, hn₁⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ P.m' T.mt
  obtain ⟨n₂, hn₂⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ P'.m' T.mt
  have hσ : ∀ z : Sp κ ⟶ T.Y, z ≫ T.s = x → (z ≫ T.t) ≫ M.s = σ := by
    intro z hz
    rw [Category.assoc, ← T.st, ← Category.assoc, hz, hxσ]
  obtain ⟨ht, hφ⟩ := hIE p D O b N hstd.three hstd.cop M (Sp κ) σ P.o' P'.o' (y ≫ T.t) (y' ≫ T.t)
    (hσ y hy) (hσ y' hy') n₁ n₂ m
  refine ⟨ht, ?_⟩
  intro a ha ha'
  obtain ⟨a', rfl⟩ : ∃ a' : 𝟙_ (Over (Sp κ)) ⟶ o₁.A, a'.left ≫ m₁.φ = a := by
    have hsq : a ≫ M.univ.A.hom = 𝟙 _ ≫ x := by rw [ha, hy, Category.id_comp]
    refine ⟨Over.homMk (m₁.cart.1.lift a (𝟙 _) hsq) ?_, m₁.cart.1.lift_fst _ _ _⟩
    rw [m₁.cart.1.lift_snd]
    rfl
  rw [(hPR p D O b N M r w j c T (Sp κ) x σ o₁ m₁ y hy P a').2 ha,
    (hPR p D O b N M r w j c T (Sp κ) x σ o₁ m₁ y' hy' P' a').2 ha', Over.comp_left, Over.comp_left,
    ← hm, ← hn₂]
  simp only [Category.assoc]
  rw [hφ, hn₁]
