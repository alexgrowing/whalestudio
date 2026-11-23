import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.LiftHeckeOperators
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.ThmBFromScal

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem eEp3_eq (R : RealDat3 D A3 Ks)
    (hU : ∀ p c c', R.Carries p c → R.Carries p c' → R.EEc c = R.EEc c' ∧ ∀ i, R.Wc' i c = R.Wc' i c')
    {p : A3.fam3.base3.Ix} {c : Pl D.host.E → List ℤ → ℂ} (hc : R.Carries p c) :
    R.EEp3 p = R.EEc c ∧ ∀ i, R.Wp3 i p = R.Wc' i c := by
  refine ⟨le_antisymm (iSup₂_le fun c' hc' => ((hU p c c' hc hc').1).symm.le) (le_iSup₂ (f := fun c' (_ : R.Carries p c') => R.EEc c') c hc),
    fun i => le_antisymm (iSup₂_le fun c' hc' => (((hU p c c' hc hc').2 i)).symm.le)
      (le_iSup₂ (f := fun c' (_ : R.Carries p c') => R.Wc' i c') c hc)⟩

theorem exists_carries (R : RealDat3 D A3 Ks) {p : A3.fam3.base3.Ix} (h : R.EEp3 p ≠ ⊥) :
    ∃ c, R.Carries p c := by
  by_contra hn
  push_neg at hn
  apply h
  unfold RealDat3.EEp3
  exact iSup₂_eq_bot.2 fun c hc => absurd hc (hn c)

theorem wc_eq (R : RealDat3 D A3 Ks) (i : Fin D.R.m) (c : Pl D.host.E → List ℤ → ℂ) :
    R.Wc' i c = GlobalTheory.Hk3.Wcc R.toRealDat R.SF i c := rfl

theorem ec_eq (R : RealDat3 D A3 Ks) (c : Pl D.host.E → List ℤ → ℂ) :
    R.EEc c = GlobalTheory.Hk3.EEc R.toRealDat R.SF c := rfl

end GlobalTheory.ThmBFromScal

namespace GlobalTheory.ThmBFromScal

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem act_on_part (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : R.WeakCharacterisation F)
    {lam : Fin D.R.m → T → GlobalTheory.LiftRows.Eig D → ℝ} {κ : ℝ}
    (hW : ∀ i t c, ∀ x ∈ GlobalTheory.Hk3.Wcc R.toRealDat R.SF i c,
      R.thG i t (LinearMap.adjoint (R.thG i t) x) = ((lam i t c : ℝ) : ℂ) • x)
    (hE : ∀ t c, ∀ x ∈ GlobalTheory.Hk3.EEc R.toRealDat R.SF c,
      R.Th t (LinearMap.adjoint (R.Th t) x) = ((κ * ∏ i, lam i t c : ℝ) : ℂ) • x)
    (hM : GlobalTheory.LiftRows.MatchUp R.toRealDat R.SF)
    (hU : ∀ p c c', R.Carries p c → R.Carries p c' → R.EEc c = R.EEc c' ∧ ∀ i, R.Wc' i c = R.Wc' i c')
    {p : A3.fam3.base3.Ix} {c : Pl D.host.E → List ℤ → ℂ} (hc : R.Carries p c) (t : T) :
    (∀ i, R.lam3 i t p A3.A.v0 = lam i t c) ∧
      ∀ x ∈ R.EEp3 p, R.Th t (LinearMap.adjoint (R.Th t) x) =
        ((κ * ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN t j p : ℝ) : ℂ) • x := by
  have hEp := (eEp3_eq R hU hc).1
  have hWp := (eEp3_eq R hU hc).2
  have hl : ∀ i, R.lam3 i t p A3.A.v0 = lam i t c := by
    intro i
    refine hC.scal.lam0 i t p (lam i t c) ?_ ?_
    · rw [hWp i, wc_eq]
      exact hM c (by rw [← ec_eq]; exact hc.1) i
    · intro x hx
      rw [hWp i, wc_eq] at hx
      exact hW i t c x hx
  refine ⟨hl, fun x hx => ?_⟩
  rw [hEp] at hx
  rw [hE t c x hx, RealDat3.prod_lamN (R := R) t p]
  simp only [hl]

theorem pThmB {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ} :
    A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → GlobalTheory.LiftRows.Scal R.toRealDat R.SF →
    GlobalTheory.LiftRows.MatchUp R.toRealDat R.SF →
    (∀ p c c', R.Carries p c → R.Carries p c' → R.EEc c = R.EEc c' ∧ ∀ i, R.Wc' i c = R.Wc' i c') → R.PThmB := by
  intro _ hC _ hS hM hU
  classical
  unfold GlobalTheory.LiftRows.Scal at hS
  obtain ⟨lam, κ, hκ, hlpos, hW, hE⟩ := hS

  have hK : Lift.IsKap D.R.m (fun t => R.Th t ∘ₗ LinearMap.adjoint (R.Th t)) R.EEp3 R.lamN κ := by
    intro t p x hx
    rw [LinearMap.comp_apply]
    by_cases h0 : R.EEp3 p = ⊥
    · rw [h0, Submodule.mem_bot] at hx
      subst hx
      simp
    · exact (act_on_part R F hC hW hE hM hU (exists_carries R h0).choose_spec t).2 x hx
  by_cases hex : ∃ (_ : T) (p : A3.fam3.base3.Ix), R.EEp3 p ≠ ⊥
  · obtain ⟨t, p, hp⟩ := hex
    have hc := (exists_carries R hp).choose_spec
    have hl := (act_on_part R F hC hW hE hM hU hc t).1
    have hk : R.kap = κ := by
      refine hC.scal.kap κ hK ⟨t, p, hp, ?_⟩
      rw [RealDat3.prod_lamN (R := R) t p, Finset.prod_congr rfl fun i _ => hl i]
      exact (Finset.prod_pos fun i _ => hlpos i t _).ne'
    intro t' p' x hx
    exact (hK t' p' x hx).trans (by rw [hk])
  · push_neg at hex
    intro t p x hx
    rw [hex t p, Submodule.mem_bot] at hx
    subst hx
    simp

end GlobalTheory.ThmBFromScal
