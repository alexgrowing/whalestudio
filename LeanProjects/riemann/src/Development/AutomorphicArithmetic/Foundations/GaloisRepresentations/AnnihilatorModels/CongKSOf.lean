import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.IdealSplit

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field

namespace UpperTheory.Gal.crystallineComparison.Mod

open GlobalTheory.UPel.HT.EtLev

def CongKS : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (f : ℕ)
    (b : Base D O) (N : ℕ) (r : ℤ) (w : Ideal (𝓞 D.F)) [w.IsMaximal], Std f b N r w → ∀ (M : Model b N) (ϖ : O), Irreducible ϖ → ∀ (𝔞 : Ideal (𝓞 D.F)) (ρ : ℕ), 𝔞 ⊔ w = ⊤ → (∃ e : ℕ, uIdeal D r ^ e ≤ 𝔞) →
    ∀ (E : EtModel b N 𝔞 ρ) (π : E.X ⟶ M.X), π ≫ M.s = E.s → Flat π → ∀ (mπ : ObjMap E.univ M.univ π) (k : ℕ),
    ∃ (T : ∀ j : Fin (D.n + 1), TjD M r w j (p ^ (f * j))) (L : ∀ j, TjE E mπ (T j)) (d : Fin (D.n + 1) → ℕ)
      (h : ∀ j, KSOKE (L j) k (d j)), (∀ j, (h j).corr.r ≫ (GlobalTheory.KS.pow E.univ.A k).hom ≫ E.s = (h j).corr.p ≫ (GlobalTheory.KS.pow E.univ.A k).hom ≫ E.s) ∧
      PtId p (p ^ f) D.n (fn ((GlobalTheory.KS.pow E.univ.A k).hom ≫ E.s) ϖ) fun j => (h j).corr

theorem congKS_of (h1 : TjExF) (h2 : TjEEx) (h3 : OrdKSE) (h4 : PtIdOfOrd) : CongKS := by
  intro p _ D O _ _ _ _ f b N r w _ hs M ϖ hϖ 𝔞 ρ ha hu E π hπ hf mπ k
  choose T hT using fun j : Fin (D.n + 1) => h1 p D O f b N r w hs M j (Nat.lt_succ_iff.1 j.2)
  have L := fun j : Fin (D.n + 1) => (h2 p D O f b N r w hs M j _ (T j) (hT j) 𝔞 ρ ha hu E π hπ mπ).some
  obtain ⟨d, h, e, ho⟩ := h3 p D O f b N r w hs M ϖ hϖ T 𝔞 ρ E π hπ hf mπ L k
  exact ⟨T, L, d, h, e, h4 _ _ _ _ _ _ ho⟩

end UpperTheory.Gal.crystallineComparison.Mod
