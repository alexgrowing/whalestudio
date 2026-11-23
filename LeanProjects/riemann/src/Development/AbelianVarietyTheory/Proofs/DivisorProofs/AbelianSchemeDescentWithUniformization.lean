import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsHolomorphicUniformisationPowerThetaKeyDatu
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsPowGrpBaseChange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SmoothIsMultiplicative
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
open CategoryTheory.Limits
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.EllPowModel

def isPowGrpIso {S : Scheme.{0}} {G' G H : Over S} [GrpObj G'] [GrpObj G] [GrpObj H] {j : ℕ}
    (p : Out.IsPowGrp G' G j) (e : G ≅ H) [IsMonHom e.hom] : Out.IsPowGrp G' H j where
  pr i := p.pr i ≫ e.hom
  hom i := by haveI := p.hom i; infer_instance
  lim := mkFanLimit _ (fun s => p.lim.lift (Fan.mk s.pt (fun i => s.proj i ≫ e.inv)))
    (fun s i => by
      have h : p.lim.lift (Fan.mk s.pt (fun i => s.proj i ≫ e.inv)) ≫ p.pr i = s.proj i ≫ e.inv :=
        p.lim.fac (Fan.mk s.pt (fun i => s.proj i ≫ e.inv)) ⟨i⟩
      show _ ≫ (p.pr i ≫ e.hom) = _
      rw [← Category.assoc, h, Category.assoc, e.inv_hom_id, Category.comp_id])
    (fun s m hm => p.lim.hom_ext fun ⟨i⟩ => by
      have h : p.lim.lift (Fan.mk s.pt (fun i => s.proj i ≫ e.inv)) ≫ p.pr i = s.proj i ≫ e.inv :=
        p.lim.fac (Fan.mk s.pt (fun i => s.proj i ≫ e.inv)) ⟨i⟩
      have hmi : m ≫ p.pr i ≫ e.hom = s.proj i := hm i
      show m ≫ p.pr i = p.lim.lift (Fan.mk s.pt (fun i => s.proj i ≫ e.inv)) ≫ p.pr i
      rw [h, ← hmi, Category.assoc, Category.assoc, e.hom_inv_id, Category.comp_id])

theorem main : ∀ (k : Type) [Field k] (σ : k →+* ℂ) (A₀ : Over (Sp k)) [GrpObj A₀] (A : Over (Sp ℂ)) [GrpObj A]
    (p : A.left ⟶ A₀.left) (L : LB A.left) (u : HolUnif A L 1), IsAbelianScheme A₀ → SmoothOfRelativeDimension 1 A₀.hom →
    IsGrpPullback A A₀ (spMap σ) p → L.IsLB → ∀ n : ℕ,
  ∃ (B₀ : Over (Sp k)) (_ : GrpObj B₀) (B : Over (Sp ℂ)) (_ : GrpObj B) (q : B.left ⟶ B₀.left) (M : LB B.left)
    (v : HolUnif B M n), IsAbelianScheme B₀ ∧ SmoothOfRelativeDimension n B₀.hom ∧ IsAbelianScheme B ∧
    SmoothOfRelativeDimension n B.hom ∧ IsGrpPullback B B₀ (spMap σ) q ∧ ∀ z ∈ v.Λ, ∀ j, (fun _ : Fin 1 ↦ z j) ∈ u.Λ := by
  intro k _ σ A₀ _ A _ p L u hA₀ hd hp hL n
  let B₀ : Over (Sp k) := Out.powObj A₀ n
  let B : Over (Sp ℂ) := (Over.pullback (spMap σ)).obj B₀
  have P := PowGrp.powers (Sp k) B₀ A₀ n (Out.powIsPowGrp A₀ n)
  have hB₀ : IsAbelianScheme B₀ := P.2.2.2.1 hA₀
  have hdB₀ : SmoothOfRelativeDimension n B₀.hom := by
    have := P.2.2.1 1 hd
    rwa [Nat.mul_one] at this
  have hB : IsAbelianScheme B := isAbelianScheme_pullback_obj (spMap σ) B₀ hB₀
  have hdB : SmoothOfRelativeDimension n B.hom := by
    have : SmoothOfRelativeDimension n (pullback.snd B₀.hom (spMap σ)) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
        (IsPullback.of_hasPullback _ _) hdB₀
    exact this
  obtain ⟨p', -⟩ := isPowGrp_baseChange (Sp k) (Sp ℂ) (spMap σ) B₀ A₀ n (Out.powIsPowGrp A₀ n)
  obtain ⟨e, he, -⟩ := grpPullback_iso (isGrpPullback_pullback A₀ (spMap σ)) hp
  let pw : Out.IsPowGrp B A n := isPowGrpIso p' e
  obtain ⟨w, hw⟩ := PolBaseChange.lbIso_refl (LB.isLB_linComb hL (fun i => (pw.pr i).left) (fun _ => (1 : ℤ)))
  obtain ⟨v, hv, -, -⟩ := PowUnif.exists_powUnif pw u hL (LB.isLB_linComb hL (fun i => (pw.pr i).left) (fun _ => (1 : ℤ)))
    w hw (Equiv.prodUnique (Fin n) (Fin 1))
  refine ⟨B₀, inferInstance, B, inferInstance, pullback.fst B₀.hom (spMap σ), _, v, hB₀, hdB₀, hB, hdB,
    isGrpPullback_pullback B₀ (spMap σ), fun z hz j => ?_⟩
  have := (hv z).1 hz j
  rw [PowUnif.blockPr_apply] at this
  convert this using 2 with a
  rw [Fin.fin_one_eq_zero a]
  rfl

end GlobalTheory.EllPowModel
