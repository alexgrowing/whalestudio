import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.OnePlusPowerAssembly
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModelSupStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModelObjAndAbcStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiGammaLatticeFamiliesShiftInclusionStatement

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.Models

theorem exists_greatest_of_sup_closed {S V ι : Type} [CommRing S] [IsNoetherianRing S] [AddCommGroup V]
    [Module S V] [Finite ι] (C : (ι → Submodule S V) → Prop) (P N₀ : ι → Submodule S V) (h₀ : C N₀)
    (hP : ∀ i, (P i).FG) (hle : ∀ N, C N → ∀ i, N i ≤ P i)
    (hsup : ∀ N N', C N → C N' → C (fun i => N i ⊔ N' i)) :
    ∃ N, C N ∧ ∀ N', C N' → ∀ i, N' i ≤ N i := by
  classical
  have one : ∀ i, ∃ N, C N ∧ ∀ N', C N' → N' i ≤ N i := by
    intro i
    haveI : IsNoetherian S (P i) := isNoetherian_of_fg_of_noetherian _ (hP i)
    obtain ⟨_, ⟨N, hN, rfl⟩, hmax⟩ := set_has_maximal_iff_noetherian.2 this
      {Q : Submodule S (P i) | ∃ N, C N ∧ (N i).comap (P i).subtype = Q} ⟨_, N₀, h₀, rfl⟩
    refine ⟨N, hN, fun N' hN' x hx => ?_⟩
    have h1 := hmax _ ⟨_, hsup N N' hN hN', rfl⟩
    have h2 : (N i).comap (P i).subtype = (N i ⊔ N' i).comap (P i).subtype :=
      (Submodule.comap_mono le_sup_left).eq_of_not_lt h1
    have h3 : (⟨x, hle N' hN' i hx⟩ : P i) ∈ (N i ⊔ N' i).comap (P i).subtype :=
      Submodule.mem_sup_right hx
    rw [← h2] at h3
    exact h3
  have all : ∀ s : Finset ι, ∃ N, C N ∧ ∀ N', C N' → ∀ i ∈ s, N' i ≤ N i := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨N₀, h₀, fun _ _ i hi => absurd hi (Finset.notMem_empty i)⟩
    | insert a s _ ih =>
      obtain ⟨N, hN, h⟩ := ih
      obtain ⟨N₁, hN₁, h₁⟩ := one a
      refine ⟨_, hsup N N₁ hN hN₁, fun N' hN' i hi => ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact le_sup_of_le_right (h₁ N' hN')
      · exact le_sup_of_le_left (h N' hN' i hi)
  haveI := Fintype.ofFinite ι
  obtain ⟨N, hN, h⟩ := all Finset.univ
  exact ⟨N, hN, fun N' hN' i => h N' hN' i (Finset.mem_univ i)⟩

theorem exists_largest_model : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (A : Ob k G) (N₀ : Lats k n A.m), M.Model A N₀ → ∃ N, M.Model A N ∧ ∀ N', M.Model A N' → ∀ i, N' i ≤ N i := by
  intro k G _ _ l n _ _ _ R F r Dt M A N₀ h₀
  obtain ⟨-, hl₀, hab₀, -⟩ := GlobalTheory.T.obj_and_abc_of_model F M A N₀ h₀
  refine exists_greatest_of_sup_closed (fun N => M.Model A N)
    (fun i => sh (-(sg l Dt.h i : ℤ)) (N₀ i)) N₀ h₀ (fun i => ((hl₀ i).shift _).1) (fun N hN i => ?_)
    (fun N N' => GlobalTheory.T.model_sup_alt F M A N N')
  obtain ⟨-, hl, hab, -⟩ := GlobalTheory.T.obj_and_abc_of_model F M A N hN
  have h := sh_le_sh (-(sg l Dt.h i : ℤ)) (GlobalTheory.T.phiGamma_lattice_families_shift_inclusion (F.D A) Dt.h Dt.w N N₀ hl hl₀ hab hab₀ i)
  rwa [sh_sh_eq, neg_add_cancel, sh_zero_eq] at h

end GlobalTheory.Models
