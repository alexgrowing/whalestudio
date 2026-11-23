import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducibleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityPos
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.JacquetModuleFiniteLength
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicInductionFiniteLength
import GroundTheory.AutomorphicForms.CuspidalSplitting
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClass

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.CuspNotInd

open GroundTheory.Automorphic.Parabolic (levi parabolicInd)
open GroundTheory.Automorphic.Iwasawa (blockUpper)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem unipotentRadical_ne_bot {n : ℕ} {γ : Fin n → ℕ} (hγ : ∃ i j, γ i ≠ γ j) :
    GroundTheory.Automorphic.Parabolic.unipotentRadical k n γ ≠ ⊥ := by
  have h : ∃ i j, γ i < γ j := by
    obtain ⟨i, j, hij⟩ := hγ
    rcases lt_or_gt_of_ne hij with h | h
    · exact ⟨i, j, h⟩
    · exact ⟨j, i, h⟩
  obtain ⟨i, j, hij⟩ := h
  have hne : i ≠ j := fun e => hij.ne (congrArg γ e)
  let g : GL (Fin n) k := Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.transvection i j 1)
    (by rw [Matrix.det_transvection_of_ne _ _ hne]; exact one_ne_zero)
  have hg : ∀ a b, (g : Matrix (Fin n) (Fin n) k) a b = (1 : Matrix (Fin n) (Fin n) k) a b +
      Matrix.single i j (1 : k) a b := fun a b => rfl
  intro hbot
  have hmem : g ∈ GroundTheory.Automorphic.Parabolic.unipotentRadical k n γ := by
    rw [GroundTheory.Automorphic.Parabolic.mem_unipotentRadical, GroundTheory.Automorphic.Iwasawa.mem_blockUpper]
    refine ⟨fun a b hab => ?_, fun a b hab => ?_⟩
    · rw [hg, Matrix.one_apply_ne (fun e => hab.ne (by rw [e])), Matrix.single_apply_of_ne, add_zero]
      rintro ⟨rfl, rfl⟩
      exact absurd hab hij.not_gt
    · rw [hg, Matrix.single_apply_of_ne, add_zero]
      rintro ⟨rfl, rfl⟩
      exact hij.ne hab
  rw [hbot, Subgroup.mem_bot] at hmem
  have h3 := congrArg (fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k) i j) hmem
  simp only [hg, Matrix.one_apply_ne hne, Matrix.single_apply_same, zero_add, Units.val_one] at h3
  exact one_ne_zero h3

theorem isSupercuspidal_of_isCuspidal {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin n) k) V} (h : IsCuspidal π) :
    GroundTheory.Automorphic.Parabolic.IsSupercuspidal π := by
  intro γ hγ
  classical
  let s : ℕ := Finset.univ.sup γ + 1
  let r : Fin n → Fin s := fun i => ⟨γ i, Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ i))⟩
  let d : Fin s → ℕ := fun a => Fintype.card {i // r i = a}
  let e : (Σ a, Fin (d a)) ≃ Fin n :=
    (Equiv.sigmaCongrRight fun a => (Fintype.equivFin {i // r i = a}).symm).trans (Equiv.sigmaFiberEquiv r)
  have hblk : ∀ i, GlobalTheory.SmGL.blk e i = r i := fun i => by
    show (e.symm i).1 = r i
    rfl
  have hβ : ∀ i j, γ i < γ j ↔ GlobalTheory.SmGL.blk e i < GlobalTheory.SmGL.blk e j := fun i j => by
    rw [hblk, hblk]; exact Iff.rfl
  have hN : ∀ g, g ∈ GroundTheory.Automorphic.Parabolic.unipotentRadical k n γ ↔ g ∈ unipRad k e :=
    GlobalTheory.CompanionTheory.JacquetBridge.mem_unipotentRadical_iff e hβ
  have hne : unipRad k e ≠ ⊥ := fun hb => unipotentRadical_ne_bot (k := k) hγ
    (by rw [eq_bot_iff]; intro g hg; rw [← hb]; exact (hN g).1 hg)
  have htop := Submodule.Quotient.subsingleton_iff.1 (h.2 s d e hne)
  let ρ' := π.comp (GroundTheory.Automorphic.Parabolic.unipotentRadical k n γ).subtype
  have hle : twKer π (unipRad k e) 1 ≤ LinearMap.ker (Representation.Coinvariants.mk ρ') := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, v, rfl⟩
    have : Representation.Coinvariants.mk ρ' (ρ' ⟨u, (hN _).2 u.2⟩ v) = Representation.Coinvariants.mk ρ' v :=
      Representation.Coinvariants.mk_self_apply _ _ _
    simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, MonoidHom.one_apply, Units.val_one, one_smul]
    exact sub_eq_zero.2 this
  have hz : ∀ y : Representation.Coinvariants ρ', y = 0 := fun y => by
    obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective ρ' y
    exact hle (htop ▸ Submodule.mem_top)
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩

theorem isSubquotient_carry {r : ℕ} {d : Fin r → ℕ} {W V : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup V]
    [Module ℂ V] {π : Representation ℂ (GL (Fin (∑ a, d a)) k) V}
    (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W) (e : (Σ a, Fin (d a)) ≃ Fin (∑ a, d a))
    (he : e = GlobalTheory.CompanionTheory.BZInd.stdE d) (h : IsSubquotient π (parInd e ρ)) :
    IsSubquotient π (parabolicInd k (∑ a, d a) (GlobalTheory.CompanionTheory.BZInd.pos d) (GlobalTheory.CompanionTheory.BZInd.carry ρ)) := by
  subst he
  exact h.trans (.of_injective _ (GlobalTheory.CompanionTheory.BZInd.toIndMap_injective ρ))

theorem isIrreducible_carry {r : ℕ} {d : Fin r → ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W) (h : ρ.IsIrreducible) :
    (GlobalTheory.CompanionTheory.BZInd.carry ρ).IsIrreducible :=
  isIrreducible_twist (GlobalTheory.LocCompSplit.isIrreducible_comp_of_surjective ρ _ GlobalTheory.CompanionTheory.BZInd.leviTo_surjective h) _

theorem isSmooth_carry {r : ℕ} {d : Fin r → ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W) (h : IsSmooth ρ) :
    IsSmooth (GlobalTheory.CompanionTheory.BZInd.carry ρ) :=
  isSmooth_twist (isSmooth_comp h _ GlobalTheory.CompanionTheory.BZInd.continuous_leviTo) GlobalTheory.CompanionTheory.BZInd.isSmoothChar_adj

theorem exists_pos_ne {r : ℕ} {d : Fin r → ℕ} (h2 : 2 ≤ r) (hd : ∀ a, 0 < d a) :
    ∃ i j, GlobalTheory.CompanionTheory.BZInd.pos d i ≠ GlobalTheory.CompanionTheory.BZInd.pos d j := by
  let a : Fin r := ⟨0, by omega⟩
  let b : Fin r := ⟨1, by omega⟩
  refine ⟨GlobalTheory.CompanionTheory.BZInd.stdE d ⟨a, ⟨0, hd a⟩⟩, GlobalTheory.CompanionTheory.BZInd.stdE d ⟨b, ⟨0, hd b⟩⟩, ?_⟩
  rw [GlobalTheory.CompanionTheory.BZInd.pos_stdE, GlobalTheory.CompanionTheory.BZInd.pos_stdE]
  simp [a, b]

theorem jhMult_eq_zero_of_isCusp : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ (ρ : IrrGL k) {h : ℕ}
    (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = ρ.1), ρ.IsCusp → 2 ≤ h → (∀ a, 0 < (x a).1) →
    jhMult ρ.rep (prodIrr x hd) = 0 := by
  intro k _ _ _ _ hA ρ h x hd hc h2 hpos
  obtain ⟨N, c⟩ := ρ
  dsimp only at hd
  subst hd
  by_contra hne
  have hsub := jhMult_ne_zero_iff.1 hne
  let ρ₀ : IrrGL k := ⟨_, c⟩
  have hs2 := isSubquotient_carry (d := fun a => (x a).1) (piTensor fun a => (x a).rep) _
    (Equiv.ext fun y => by simp [stdBlocks, GlobalTheory.CompanionTheory.BZInd.stdE]) hsub
  obtain ⟨A, p, hp⟩ := hs2
  haveI : ρ₀.rep.IsIrreducible := ρ₀.2.rep.irr
  haveI := isIrreducible_carry (d := fun a => (x a).1) _ (GlobalTheory.CompanionTheory.FrobJm.piTensor_rep_isIrreducible hA x)
  exact GroundTheory.Automorphic.Parabolic.not_surjective_of_isIrreducible (π := ρ₀.rep) ρ₀.2.rep.smooth
    (isSupercuspidal_of_isCuspidal hc.2) (exists_pos_ne h2 hpos)
    (isSmooth_carry _ (isSmooth_piTensor fun a => (x a).2.rep.smooth)) A p hp

end GlobalTheory.CompanionTheory.CuspNotInd

end
