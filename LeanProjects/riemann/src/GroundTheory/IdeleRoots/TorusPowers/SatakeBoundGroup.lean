import Mathlib
import GroundTheory.AutomorphicForms.MacdonaldHecke
import GroundTheory.IdeleRoots.TorusPowers.SatakeBoundGauss
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.BlockD

namespace SatakeBound

open GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GLnLocal Iwasawa Finset Matrix
open scoped ValuativeRel

attribute [local instance] GroundTheory.Automorphic.Spherical.fintypeResidue

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem exists_perm_mem_iff {N : ℕ} {A B : Finset (Fin N)} (h : A.card = B.card) :
    ∃ σ : Equiv.Perm (Fin N), ∀ x, σ x ∈ B ↔ x ∈ A := by
  classical
  have e1 : {x // x ∈ A} ≃ {x // x ∈ B} := Fintype.equivOfCardEq (by simp [h])
  have e2 : {x // x ∉ A} ≃ {x // x ∉ B} :=
    Fintype.equivOfCardEq (by rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl]; simp [h])
  refine ⟨(Equiv.sumCompl (· ∈ A)).symm.trans ((Equiv.sumCongr e1 e2).trans (Equiv.sumCompl (· ∈ B))),
    fun x => ?_⟩
  by_cases hx : x ∈ A
  · rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_pos hx, Equiv.sumCongr_apply,
      Sum.map_inl, Equiv.sumCompl_apply_inl]
    exact ⟨fun _ => hx, fun _ => (e1 ⟨x, hx⟩).2⟩
  · rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_neg hx, Equiv.sumCongr_apply,
      Sum.map_inr, Equiv.sumCompl_apply_inr]
    exact ⟨fun h' => absurd h' (e2 ⟨x, hx⟩).2, fun h' => absurd h' hx⟩

theorem lamS_comp_of_mem_iff {N : ℕ} {A B : Finset (Fin N)} {σ : Equiv.Perm (Fin N)}
    (hσ : ∀ x, σ x ∈ B ↔ x ∈ A) : lamS B ∘ σ = lamS A := by
  funext x
  simp only [Function.comp_apply, lamS, hσ]

def lowSet (N k : ℕ) : Finset (Fin N) := univ.filter fun i => (i : ℕ) < k

def famW (N m k : ℕ) : Fin (N + 1) → ℤ := Fin.cons (m : ℤ) (lamS (lowSet N k))

section Values

variable {n : ℕ} {ω : GL (Fin n) F → ℂ}
  (hR : ∀ g, ∀ k ∈ integralGL F n, ω (g * k) = ω g)
  (hL : ∀ g, ∀ k ∈ integralGL F n, ω (k * g) = ω g)
include hR hL

end Values

section ValuesCons

variable {N : ℕ} {ω : GL (Fin (N + 1)) F → ℂ}
  (hR : ∀ g, ∀ k ∈ integralGL F (N + 1), ω (g * k) = ω g)
  (hL : ∀ g, ∀ k ∈ integralGL F (N + 1), ω (k * g) = ω g)
include hR hL

end ValuesCons

variable {n : ℕ} [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]

omit [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] in

def heckeEig (ω : GL (Fin n) F → ℂ) (r : ℕ) : ℂ :=
  ∑ S ∈ powersetCard r (univ : Finset (Fin n)), ∑ c : Pairs S → 𝓀[F], ω (gMat S c)

end SatakeBound

end GroundTheory.BlockD
