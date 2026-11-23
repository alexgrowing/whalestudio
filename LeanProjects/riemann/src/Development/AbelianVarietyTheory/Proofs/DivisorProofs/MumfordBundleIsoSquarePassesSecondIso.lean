import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleBaseOfCompleteNormalLocalCharZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HalfBC GlobalTheory.PrimCocycle GlobalTheory.ArcPull
open GlobalTheory.PsiEvenPull (proj)
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.FactorPull

theorem lam_down_gen : ∀ {S S' : Scheme.{0}} {f : S' ⟶ S} {B C : Over S} {B₁ C₁ : Over S'} [GrpObj B] [IsCommMonObj B] [GrpObj C]
  [IsCommMonObj C] [GrpObj B₁] [IsCommMonObj B₁] [GrpObj C₁] [IsCommMonObj C₁] {δ : C₁.left ⟶ C.left} {M : LB B.left} {N : LB C.left} {M₁ : LB B₁.left} {N₁ : LB C₁.left}
  (gC : IsGrpPullback C₁ C f δ), M.IsLB → N.IsLB → M₁.IsLB → N₁.IsLB → ∀ (β₂ : (G2 B₁).left ⟶ (G2 B).left) (u : LB.Iso (abelian₂ B₁ M₁) ((abelian₂ B M).pull β₂)), u.IsGen →
  ∀ (v' : LB.Iso N₁ (N.pull δ)), v'.IsGen → ∀ {m : (G2 B).left ⟶ (G2 C).left} {m₁ : (G2 B₁).left ⟶ (G2 C₁).left},
    m₁ ≫ sqOf gC = β₂ ≫ m → ∀ (w : LB.Iso (abelian₂ B M) ((abelian₂ C N).pull m)), w.IsGen →
    ∃ w₁ : LB.Iso (abelian₂ B₁ M₁) ((abelian₂ C₁ N₁).pull m₁), w₁.IsGen ∧
      ∀ (Z : Scheme.{0}) (p : Z ⟶ (G2 B₁).left) (z : Z) I J I₁ J₁, Good N z I → Good M z J → Good N₁ z I₁ →
        Good M₁ z J₁ → (∏ k, om v' z I I₁ ((p ≫ m₁) ≫ lamφ C₁ k) ^ lamε k) * lamVal w₁ p z I₁ J₁ =
          lamVal w (p ≫ β₂) z I J * lamVal u p z J J₁ := by
  intro S S' f B C B₁ C₁ _ _ _ _ _ _ _ _ δ M N M₁ N₁ gC hM hN hM₁ hN₁ β₂ u hu v' hv' m m₁ hm w hw
  have lM : (abelian₂ B M).IsLB := DVR.linComb_isLB _ hM _ _
  have lN : (abelian₂ C N).IsLB := DVR.linComb_isLB _ hN _ _
  have lM₁ : (abelian₂ B₁ M₁).IsLB := DVR.linComb_isLB _ hM₁ _ _
  have lN₁ : (abelian₂ C₁ N₁).IsLB := DVR.linComb_isLB _ hN₁ _ _
  have pw := (isGen_iff _).1 hw
  have pu := (isGen_iff u).1 hu
  have pv' := pgen_lamIso gC v' ((isGen_iff v').1 hv')
  obtain ⟨w₂, T⟩ := exists_comp lM w u pw pu lN lM₁
  have p₂ := pgen_pullCongr hm.symm (T.pgen_comp lM pw pu)
  obtain ⟨w₁, T'⟩ := exists_cancel lN (lamIso gC v') (pullCongr hm.symm w₂) pv' p₂ lN₁ lM₁
  refine ⟨w₁, (isGen_iff _).2 (T'.pgen_cancel lN pv' p₂), fun Z p z I J I₁ J₁ hI hJ hI₁ hJ₁ => ?_⟩
  have e : (p ≫ m₁) ≫ sqOf gC = (p ≫ β₂) ≫ m := by rw [Category.assoc, hm, Category.assoc]
  have t := T Z p z (fun k => I (((p ≫ β₂) ≫ m) ≫ lamφ C k))
    (fun k => J ((p ≫ β₂) ≫ lamφ B k)) (fun k => J₁ (p ≫ lamφ B₁ k))
    (Set.mem_iInter.2 fun k => hI (((p ≫ β₂) ≫ m) ≫ lamφ C k))
    (Set.mem_iInter.2 fun k => hJ ((p ≫ β₂) ≫ lamφ B k))
    (Set.mem_iInter.2 fun k => hJ₁ (p ≫ lamφ B₁ k))
  have t' := T' Z p z (fun k => I (((p ≫ m₁) ≫ sqOf gC) ≫ lamφ C k))
    (fun k => I₁ ((p ≫ m₁) ≫ lamφ C₁ k)) (fun k => J₁ (p ≫ lamφ B₁ k))
    (Set.mem_iInter.2 fun k => hI (((p ≫ m₁) ≫ sqOf gC) ≫ lamφ C k))
    (Set.mem_iInter.2 fun k => hI₁ ((p ≫ m₁) ≫ lamφ C₁ k))
    (Set.mem_iInter.2 fun k => hJ₁ (p ≫ lamφ B₁ k))
  replace t' := (gw_pullCongr _ _ _ _ _ _).symm.trans (t'.trans (congrArg₂ (· * ·) (gw_lam gC v' (p ≫ m₁) z hI hI₁) rfl))
  rw [e] at t'
  replace t' := t.symm.trans t'
  refine Eq.trans (congrArg₂ (· * ·) rfl ?_) (t'.symm.trans (congrArg₂ (· * ·) ?_ ?_))
  · show Geo.Tor.gw w₁ p z (fun k => I₁ (p ≫ m₁ ≫ lamφ C₁ k)) (fun k => J₁ (p ≫ lamφ B₁ k)) = _
    simp only [Category.assoc]
  · show _ = Geo.Tor.gw w (p ≫ β₂) z (fun k => I ((p ≫ β₂) ≫ m ≫ lamφ C k))
      (fun k => J ((p ≫ β₂) ≫ lamφ B k))
    simp only [Category.assoc]
  · show _ = Geo.Tor.gw u p z (fun k => J (p ≫ β₂ ≫ lamφ B k)) (fun k => J₁ (p ≫ lamφ B₁ k))
    simp only [Category.assoc]

end GlobalTheory.FactorPull
