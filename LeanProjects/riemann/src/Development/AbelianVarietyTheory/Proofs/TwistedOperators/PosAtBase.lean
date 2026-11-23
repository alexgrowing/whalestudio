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

namespace GlobalTheory.PosAtBase

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem Wp3_eq {R : RealDat3 D A3 Ks}
    (hU : ∀ p c c', R.Carries p c → R.Carries p c' → R.EEc c = R.EEc c' ∧ ∀ i, R.Wc' i c = R.Wc' i c')
    {p : A3.fam3.base3.Ix} {c0 : Pl D.host.E → List ℤ → ℂ} (h0 : R.Carries p c0) (i : Fin D.R.m) :
    R.Wp3 i p = R.Wc' i c0 := by
  apply le_antisymm
  · exact iSup₂_le fun c hc ↦ ((hU p c c0 hc h0).2 i).le
  · exact le_iSup₂_of_le (f := fun c (_ : R.Carries p c) ↦ R.Wc' i c) c0 h0 le_rfl

theorem EEp3_eq {R : RealDat3 D A3 Ks}
    (hU : ∀ p c c', R.Carries p c → R.Carries p c' → R.EEc c = R.EEc c' ∧ ∀ i, R.Wc' i c = R.Wc' i c')
    {p : A3.fam3.base3.Ix} {c0 : Pl D.host.E → List ℤ → ℂ} (h0 : R.Carries p c0) :
    R.EEp3 p = R.EEc c0 := by
  apply le_antisymm
  · exact iSup₂_le fun c hc ↦ (hU p c c0 hc h0).1.le
  · exact le_iSup₂_of_le (f := fun c (_ : R.Carries p c) ↦ R.EEc c) c0 h0 le_rfl

theorem Wp3_bot {R : RealDat3 D A3 Ks} {p : A3.fam3.base3.Ix} (h : ∀ c, ¬ R.Carries p c) (i : Fin D.R.m) :
    R.Wp3 i p = ⊥ := by
  unfold RealDat3.Wp3
  simp [h]

theorem EEp3_bot {R : RealDat3 D A3 Ks} {p : A3.fam3.base3.Ix} (h : ∀ c, ¬ R.Carries p c) :
    R.EEp3 p = ⊥ := by
  unfold RealDat3.EEp3
  simp [h]

example (R : RealDat3 D A3 Ks) c : R.EEc c = GlobalTheory.Hk3.EEc R.toRealDat R.SF c := rfl

end GlobalTheory.PosAtBase

namespace GlobalTheory.PosAtBase

set_option maxHeartbeats 1000000 in

theorem pos_at_base {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ} (_hOk : A3.fam3.Ok3 s) (hC : R.WeakCharacterisation F) (_hE : R.toRealDat.ExAt)
    (hS : Scal R.toRealDat R.SF) (hM : MatchUp R.toRealDat R.SF)
    (hU : ∀ p c c', R.Carries p c → R.Carries p c' → R.EEc c = R.EEc c' ∧ ∀ i, R.Wc' i c = R.Wc' i c')
    (hex : ∃ p, R.EEp3 p ≠ ⊥) :
    0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0 := by
  obtain ⟨lam, κ, hκ, hl, hA, hB⟩ := hS
  have hlam : ∀ i t p c, R.Carries p c → R.Wc' i c ≠ ⊥ → R.lam3 i t p A3.A.v0 = lam i t c := by
    intro i t p c hc hne
    have hW := Wp3_eq hU hc i
    refine hC.scal.lam0 i t p _ (by rw [hW]; exact hne) fun x hx ↦ hA i t c x ?_
    rw [hW] at hx
    exact hx
  have hpos : ∀ i t p, 0 < R.lam3 i t p A3.A.v0 := by
    intro i t p
    by_cases hW : R.Wp3 i p = ⊥
    · rw [hC.scal.abs0 i t p hW]
      exact Real.exp_pos _
    · by_cases hc : ∃ c, R.Carries p c
      · obtain ⟨c, hc⟩ := hc
        rw [hlam i t p c hc (by rw [← Wp3_eq hU hc i]; exact hW)]
        exact hl i t c
      · exact absurd (Wp3_bot (not_exists.1 hc) i) hW
  refine ⟨?_, hpos⟩
  have hK : Lift.IsKap D.R.m (fun t ↦ R.Th t ∘ₗ LinearMap.adjoint (R.Th t)) R.EEp3 R.lamN κ := by
    intro t p x hx
    by_cases hc : ∃ c, R.Carries p c
    · obtain ⟨c, hc⟩ := hc
      have hx' : x ∈ R.EEc c := EEp3_eq hU hc ▸ hx
      have hpr : ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN t j p = ∏ j, lam j t c :=
        (RealDat3.prod_lamN t p).trans (Finset.prod_congr rfl fun j _ ↦ hlam j t p c hc (hM c hc.1 j))
      have h1 := hB t c x hx'
      calc (R.Th t ∘ₗ LinearMap.adjoint (R.Th t)) x = R.Th t (LinearMap.adjoint (R.Th t) x) := rfl
        _ = ((κ * ∏ i, lam i t c : ℝ) : ℂ) • x := h1
        _ = ((κ * ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN t j p : ℝ) : ℂ) • x := by rw [hpr]
    · have hb : R.EEp3 p = ⊥ := EEp3_bot (not_exists.1 hc)
      have hx0 : x = 0 := (Submodule.mem_bot ℂ).1 (hb ▸ hx)
      subst hx0
      rw [map_zero, smul_zero]
  obtain ⟨p, hp⟩ := hex
  rw [hC.scal.kap κ hK ⟨A3.A.μ0, p, hp, ?_⟩]
  · exact hκ
  · rw [RealDat3.prod_lamN]
    exact (Finset.prod_pos fun j _ ↦ hpos j _ p).ne'

end GlobalTheory.PosAtBase
