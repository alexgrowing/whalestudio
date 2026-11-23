import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTrivialityOfNoetherianDescent
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFibreAct

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem UpperTheory.quotient_moduli_iso : UpperTheory.Gal.Int.Geo.QIso := by
  intro q _ D R R' _ _ _ b gb N N' N₀ c c' X X₁ s s₁ o' o u f ψ hiso hmon hact hpol heta n
  obtain ⟨hP⟩ := hpol
  have hrefl : ∀ {Y : Scheme} (L : LB Y), L.IsLB → LBIso L L :=
    fun L hL => (GlobalTheory.CechPic.cls_eq_iff hL hL).mp rfl
  have h1 : (Hecke.lbPow o'.P 1).IsLB := DVR.linComb_isLB _ o'.isLB _ _
  have e1 : LBIso o'.P (Hecke.lbPow o'.P 1) :=
    (GlobalTheory.CechPic.cls_eq_iff o'.isLB h1).mp (by rw [GlobalTheory.LocTrivDescent.cls_lbPow_eq o'.isLB 1 h1, one_smul])
  have e3 : LBIso (o.P.pull (Hecke.sq2 ψ)) ((u.P.pull n.φ₂).pull (Hecke.sq2 ψ)) :=
    LBIso.chartPull (chartPullPull _ _ _ rfl) (chartPullPull _ _ _ rfl) n.pol
  have e4 : LBIso ((u.P.pull n.φ₂).pull (Hecke.sq2 ψ)) (u.P.pull (Hecke.sq2 ψ ≫ n.φ₂)) :=
    LBIso.chartPull (chartPullId _) (chartPullIn u.P (fun _ => n.φ₂) (fun _ => (1 : ℤ)) (Hecke.sq2 ψ))
      (hrefl _ (pull_isLB (pull_isLB u.isLB _) _))
  have pol : LBIso o'.P (u.P.pull (Hecke.sq2 ψ ≫ n.φ₂)) :=
    LBIso.trans o'.isLB (pull_isLB o.isLB _) (pull_isLB u.isLB _)
      (LBIso.trans o'.isLB h1 (pull_isLB o.isLB _) e1 hP)
      (LBIso.trans (pull_isLB o.isLB _) (pull_isLB (pull_isLB u.isLB _) _) (pull_isLB u.isLB _) e3 e4)
  refine ⟨⟨Over.Hom.left ψ ≫ n.φ, Hecke.sq2 ψ ≫ n.φ₂, ?_, ?_, ?_, pol, ?_⟩, rfl⟩
  · have hc := (GlobalTheory.FibreAct.isGrpPullback_of_iso ψ).comp n.cart
    simpa using hc
  · constructor
    · rw [Category.assoc, n.sq.1, ← Category.assoc, ← Category.assoc, Hecke.sq2, ← Over.comp_left,
        lift_fst, Over.comp_left]
    · rw [Category.assoc, n.sq.2, ← Category.assoc, ← Category.assoc, Hecke.sq2, ← Over.comp_left,
        lift_snd, Over.comp_left]
  · intro x
    rw [← Category.assoc, ← Over.comp_left, hact x, Over.comp_left, Category.assoc, n.act x,
      Category.assoc]
  · intro y
    rw [← Category.assoc, ← Over.comp_left, heta y, n.eta y]
