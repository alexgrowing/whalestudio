import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.CasselmanSuffTemp
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInSupportOfMultiProd

open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas

namespace UpperTheory.Lit.Cas.TSplit

private theorem subQuot_apply_of_smul {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (S T : Subrepresentation ρ) {g : G} {c : ℂ}
    (h : ∀ v, ρ g v = c • v) (y : S.toSubmodule ⧸ T.toSubmodule.comap S.toSubmodule.subtype) :
    subQuot S T g y = c • y := by
  obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have hs : S.toRepresentation g s = c • s := Subtype.ext (h s)
  show Submodule.Quotient.mk (S.toRepresentation g s) = _
  rw [hs, Submodule.Quotient.mk_smul]

private theorem exists_step_of_jhMult_ne_zero {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ G W} {ρ : Representation ℂ G V}
    (h : jhMult σ ρ ≠ 0) :
    ∃ S T : Subrepresentation ρ, Nonempty ((subQuot S T).Equiv σ) := by
  by_contra hne
  apply h
  unfold jhMult
  refine nonpos_iff_eq_zero.mp (iSup_le fun r => iSup_le fun hr => ?_)
  obtain ⟨S, T, -, -, hST⟩ := hr
  cases r with
  | zero => simp
  | succ n => exact (hne ⟨S 0, T 0, hST 0⟩).elim

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem leviEmb_scalar {s N : ℕ} (d : Fin s → ℕ) (hd : ∑ a, d a = N) (t : kˣ) :
    leviEmb k (stdBlocks d hd) (fun a => Matrix.GeneralLinearGroup.scalar (Fin (d a)) t) =
      Matrix.GeneralLinearGroup.scalar (Fin N) t := by
  ext i j
  obtain ⟨⟨a, i⟩, rfl⟩ := (stdBlocks d hd).surjective i
  obtain ⟨⟨b, j⟩, rfl⟩ := (stdBlocks d hd).surjective j
  by_cases hab : a = b
  · subst hab
    rw [leviEmb_apply_same]
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.diagonal_apply]
  · rw [leviEmb_apply_ne _ _ _ hab]
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.diagonal_apply]
    exact fun h => absurd h hab

private theorem nabs_det_scalar (n : ℕ) (t : kˣ) :
    nabs k (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin n) t)) =
      nabs k t ^ n := by
  have : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin n) t) = t ^ n := by
    ext; simp [Matrix.GeneralLinearGroup.scalar]
  rw [this]
  simp [nabs]

private theorem deltaHalf_scalar (d : Fin 2 → ℕ) (t : kˣ) :
    deltaHalf k (fun a => Fin (d a))
      (fun a => Matrix.GeneralLinearGroup.scalar (Fin (d a)) t) = 1 := by
  ext
  rw [val_deltaHalf]
  have hm : modulus k (fun a => Fin (d a))
      (fun a => Matrix.GeneralLinearGroup.scalar (Fin (d a)) t) = 1 := by
    simp only [modulus, Fin.prod_univ_two, nabs_det_scalar, modExp]
    simp only [Finset.sum_filter, Fin.sum_univ_two]
    simp
    have hp : nabs k t ≠ 0 := ne_of_gt (nabs_pos' k t)
    have he : (nabs k t ^ d 1) ^ d 0 = nabs k t ^ (((d 0 : ℕ) : ℤ) * ((d 1 : ℕ) : ℤ)) := by
      rw [mul_comm, zpow_mul, zpow_natCast, zpow_natCast]
    have he' : (nabs k t ^ d 0) ^ d 1 = nabs k t ^ (((d 0 : ℕ) : ℤ) * ((d 1 : ℕ) : ℤ)) := by
      rw [zpow_mul, zpow_natCast, zpow_natCast]
    rw [he, he']
    exact mul_inv_cancel₀ (zpow_ne_zero _ hp)
  rw [hm]
  simp

private theorem piTensor_apply_of_smul {h : ℕ} (x : Fin h → IrrGL k) (g : ∀ a, GL (Fin (x a).1) k)
    (c : Fin h → ℂ) (hc : ∀ a v, (x a).rep (g a) v = c a • v)
    (w : PiTensorProduct ℂ (fun a => (x a).2.rep.V)) :
    piTensor (fun a => (x a).rep) g w = (∏ a, c a) • w := by
  induction w using PiTensorProduct.induction_on with
  | add y z hy hz => rw [map_add, hy, hz, smul_add]
  | smul_tprod r y =>
    rw [map_smul, piTensor_tprod, smul_comm]
    congr 1
    simp only [hc]
    exact MultilinearMap.map_smul_univ _ _ _

private theorem smul_eq_of_equiv {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] [Nontrivial W] {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (E : ρ.Equiv σ) {g : G} {c c' : ℂ} (hρ : ∀ v, ρ g v = c • v) (hσ : ∀ w, σ g w = c' • w) :
    c' = c := by
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  have key : E.toLinearEquiv (ρ g (E.toLinearEquiv.symm w)) =
      σ g (E.toLinearEquiv (E.toLinearEquiv.symm w)) :=
    Representation.IntertwiningMap.isIntertwining ρ σ E.toIntertwiningMap g _
  simp only [hρ, hσ, map_smul, LinearEquiv.apply_symm_apply] at key
  have h0 : (c' - c) • w = 0 := by rw [sub_smul, key, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp h0).resolve_right hw)

end UpperTheory.Lit.Cas.TSplit

open UpperTheory.Lit.Cas.TSplit in
theorem UpperTheory.Lit.Cas.split :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (x : Fin 2 → IrrGL k) (hd : ∑ a, (x a).1 = N), jm x hd π ≠ 0 → ∀ (t : kˣ) (c c0 c1 : ℂ), (∀ v, π (Matrix.GeneralLinearGroup.scalar (Fin N) t) v = c • v) → ScalarBy (x 0) t c0 → ScalarBy (x 1) t c1 → c0 * c1 = c := by
  intro k _ _ _ _ N V _ _ π x hd hj t c c0 c1 hπ h0 h1
  obtain ⟨S, T, ⟨E⟩⟩ := exists_step_of_jhMult_ne_zero hj
  set g : Levi k (fun a => Fin (x a).1) := fun a => Matrix.GeneralLinearGroup.scalar (Fin (x a).1) t
  have hjac : ∀ v, jac (stdBlocks (fun a => (x a).1) hd) π g v = c • v := by
    intro v
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    rw [jac_mk, leviEmb_scalar, deltaHalf_scalar, hπ, inv_one, Units.val_one, one_smul,
      Submodule.Quotient.mk_smul]
  have hsub := subQuot_apply_of_smul S T hjac
  have hpi := piTensor_apply_of_smul x g ![c0, c1] (by
    intro a v
    fin_cases a
    · exact h0 v
    · exact h1 v)
  haveI : Nontrivial (PiTensorProduct ℂ (fun a => (x a).2.rep.V)) :=
    GlobalTheory.ProdSupport.nontrivial_piTensor _ (fun a => Model.nontrivial_of_isIrreducible (x a).2.rep.irr)
  have := smul_eq_of_equiv E hsub hpi
  simpa [Fin.prod_univ_two] using this
