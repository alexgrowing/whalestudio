import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ScalarsZeroPartConventionFixedPlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section
namespace GlobalTheory.Mem.R3
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem lamN_zeroLam (R : RealDat3 D A3 Ks) (F : Face3 D A3) (c : Fin D.R.m → ℝ) (kap : ℝ)
    (hZ : ∀ p, R.EEp3 p ≠ ⊥ → ∀ i, R.Wp3 i p ≠ ⊥ ∧ ∀ v, v ≠ A3.A.v0 → R.PartAt F i p v) {p} (hp : R.EEp3 p ≠ ⊥) (t j) :
    (R.updS kap (zeroLam R F c)).lamN t j p = R.lamN t j p := by
  unfold RealDat3.lamN
  split_ifs with h
  · exact scalarsZeroPartConvention_fixedPlace R F c ((hZ p hp _).1)
  · rfl

theorem isKap_congr {N Tup Sig : Type} [AddCommGroup N] [Module ℂ N] {m : ℕ} {dnup : Tup → N →ₗ[ℂ] N} {partE : Sig → Submodule ℂ N}
    {lam lam' : Tup → ℕ → Sig → ℝ} {κ : ℝ} (h : Lift.IsKap m dnup partE lam κ)
    (hl : ∀ μ j σ, partE σ ≠ ⊥ → lam' μ j σ = lam μ j σ) : Lift.IsKap m dnup partE lam' κ := by
  intro μ σ x hx
  by_cases hσ : partE σ = ⊥
  · rw [hσ, Submodule.mem_bot] at hx
    subst hx
    simp
  · rw [Finset.prod_congr rfl fun j _ => hl μ j σ hσ]
    exact h μ σ x hx

theorem isLamP_congr {A Amb Sig : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup Amb] [Module ℂ Amb] {thW : A →ₗ[ℂ] Amb}
    {adj : Amb →ₗ[ℂ] A} {part : Sig → Submodule ℂ Amb} {lam lam' : Sig → ℝ} (h : Lift.IsLamP thW adj part lam)
    (hl : ∀ σ, part σ ≠ ⊥ → lam' σ = lam σ) : Lift.IsLamP thW adj part lam' := by
  intro σ x hx
  by_cases hσ : part σ = ⊥
  · rw [hσ, Submodule.mem_bot] at hx
    subst hx
    simp
  · rw [hl σ hσ]
    exact h σ x hx

set_option maxHeartbeats 1000000 in

theorem thmB_zeroLam (R : RealDat3 D A3 Ks) (F : Face3 D A3) (c : Fin D.R.m → ℝ) (hZ : ∀ p, R.EEp3 p ≠ ⊥ → ∀ i, R.Wp3 i p ≠ ⊥ ∧ ∀ v, v ≠ A3.A.v0 → R.PartAt F i p v)
    (hB : R.PThmB) : (R.updS R.kap (zeroLam R F c)).PThmB := by
  have h := isKap_congr (lam' := (R.updS R.kap (zeroLam R F c)).lamN) hB
    fun μ j σ hσ => lamN_zeroLam R F c R.kap hZ hσ μ j
  exact (by with_unfolding_all exact (h :))

set_option maxHeartbeats 1000000 in

theorem thmA_zeroLam (R : RealDat3 D A3 Ks) (F : Face3 D A3) (c : Fin D.R.m → ℝ)
    (hA : R.PThmA) : (R.updS R.kap (zeroLam R F c)).PThmA := by
  have h := fun i t => isLamP_congr (lam' := fun p => zeroLam R F c i t p A3.A.v0) (hA i t)
    fun σ hσ => scalarsZeroPartConvention_fixedPlace R F c hσ
  exact (by with_unfolding_all exact (h :))

set_option maxHeartbeats 1000000 in

theorem galD_zeroLam (R : RealDat3 D A3 Ks) (F : Face3 D A3) (c : Fin D.R.m → ℝ)
    (hG : (R.toCx3 F).GalD F.cr false) : ((R.updS R.kap (zeroLam R F c)).toCx3 F).GalD F.cr false := by
  have h := cx_galD_scal (R.toCx3 F) F.cr (fun _ => R.kap) (zeroLam R F c) (fun j p v hv hp => zeroLam_off R F c hv hp) hG
  exact (by with_unfolding_all exact (h :))

theorem partAt_updS_reFace (R : RealDat3 D A3 Ks) (F : Face3 D A3) (kap lam)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (i p v) :
    (R.updS kap lam).PartAt (reFace F Dc Sp Zsc) i p v ↔ R.PartAt F i p v :=
  (RealDat3.partAt_updS kap lam i p v).trans Iff.rfl

set_option maxHeartbeats 4000000 in

theorem scal_zeroLam (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3)
    (hZ : ∀ p, R.EEp3 p ≠ ⊥ → ∀ i, R.Wp3 i p ≠ ⊥ ∧ ∀ v, v ≠ A3.A.v0 → R.PartAt F i p v)
    (hs : R.IsScal F) :
    (R.updS R.kap (zeroLam R F (Zsc (R.toCx3 F).zs).l6m)).IsScal (reFace F Dc Sp Zsc) := by
  refine ⟨fun i t p l hp hl => ?_, fun κ hk hne => ?_, fun i p v l hv hp he => ?_, fun i t p hp => ?_,
    fun i p v hv hp => ?_, fun i t p v hv => ?_⟩
  · exact (scalarsZeroPartConvention_fixedPlace R F _ hp).trans (hs.lam0 i t p l hp hl)
  · refine hs.kap κ (fun μ σ x hx => ?_) ?_
    · by_cases hσ : R.EEp3 σ = ⊥
      · rw [hσ, Submodule.mem_bot] at hx
        subst hx
        simp
      · have e := hk μ σ x hx
        rw [Finset.prod_congr rfl fun j _ => lamN_zeroLam R F _ R.kap hZ hσ μ j] at e
        exact e
    · obtain ⟨t, p, hp, hne⟩ := hne
      exact ⟨t, p, hp, by rwa [Finset.prod_congr rfl fun j _ => lamN_zeroLam R F _ R.kap hZ hp t j] at hne⟩
  · have hp' : R.PartAt F i p v := (partAt_updS_reFace R F _ _ Dc Sp Zsc i p v).1 hp
    exact (zeroLam_off R F _ hv hp').trans (hs.off i p v l hv hp' he)
  · exact zeroLam_of_zero R F _ (Or.inl ⟨rfl, hp⟩)
  · exact zeroLam_of_zero R F _ (Or.inr ⟨hv, fun h => hp ((partAt_updS_reFace R F _ _ Dc Sp Zsc i p v).2 h)⟩)
  · show zeroLam R F _ i t p v = zeroLam R F _ i A3.A.μ0 p v
    unfold zeroLam
    split_ifs with h
    · rfl
    · exact hs.tup i t p v hv

end GlobalTheory.Mem.R3

end
