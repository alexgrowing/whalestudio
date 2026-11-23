import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv

open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries
noncomputable section
namespace GlobalTheory.PhiGam.GmultAdd

variable {k U : Type} [Field k] [AddCommGroup U] [Module k U]

def quotEquiv (A B S : Submodule k U) (hSB : S ≤ B) :
    (↥A ⧸ B.submoduleOf A) ≃ₗ[k] (↥(A.map S.mkQ) ⧸ (B.map S.mkQ).submoduleOf (A.map S.mkQ)) :=
  (Submodule.quotEquivOfEq _ _ (by
      ext a
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      change (a : U) ∈ B ↔ S.mkQ a ∈ B.map S.mkQ
      have h : (B.map S.mkQ).comap S.mkQ = B := by
        rw [Submodule.comap_map_mkQ]; exact sup_eq_right.2 hSB
      constructor
      · intro ha
        exact Submodule.mem_map_of_mem (f := S.mkQ) ha
      · intro ha
        rw [← h]
        exact ha)).trans
    (LinearMap.quotKerEquivOfSurjective
      (((B.map S.mkQ).submoduleOf (A.map S.mkQ)).mkQ ∘ₗ (S.mkQ.submoduleMap A))
      ((Submodule.mkQ_surjective _).comp (LinearMap.submoduleMap_surjective _ _)))

theorem map_self (S : Submodule k U) : S.map S.mkQ = ⊥ := by
  simp

theorem fin_map (A S : Submodule k U) (h : FiniteDimensional k (↥A ⧸ S.submoduleOf A)) :
    FiniteDimensional k (A.map S.mkQ) := by
  have e := quotEquiv A S S le_rfl
  have h2 : (S.map S.mkQ).submoduleOf (A.map S.mkQ) = ⊥ := by
    rw [map_self]; simp [Submodule.submoduleOf]
  have e2 := e.trans (Submodule.quotEquivOfEqBot _ h2)
  exact e2.finiteDimensional

theorem finrank_quot (A B S : Submodule k U) (hSB : S ≤ B) (hBA : B ≤ A)
    [FiniteDimensional k (A.map S.mkQ)] :
    Module.finrank k (↥A ⧸ B.submoduleOf A) + Module.finrank k (B.map S.mkQ)
      = Module.finrank k (A.map S.mkQ) := by
  rw [(quotEquiv A B S hSB).finrank_eq,
    ← Submodule.finrank_quotient_add_finrank ((B.map S.mkQ).submoduleOf (A.map S.mkQ)),
    (Submodule.submoduleOfEquivOfLe (Submodule.map_mono hBA)).finrank_eq]

theorem map_inf_mkQ (A B S : Submodule k U) (hA : S ≤ A) :
    (A ⊓ B).map S.mkQ = A.map S.mkQ ⊓ B.map S.mkQ := by
  apply le_antisymm (Submodule.map_inf_le _)
  rintro y ⟨⟨a, ha, rfl⟩, b, hb, hab⟩
  refine ⟨b, ⟨?_, hb⟩, hab⟩
  have : b - a ∈ S := by
    simpa [Submodule.Quotient.eq] using hab
  simpa using A.add_mem (hA this) ha

theorem pow_mem (N : Module.End k U) (Q : Submodule k U) (hQ : ∀ y ∈ Q, N y ∈ Q) (m : ℕ) :
    ∀ y ∈ Q, (N ^ m) y ∈ Q := by
  induction m with
  | zero => intro y hy; simpa using hy
  | succ m ih => intro y hy; rw [pow_succ', Module.End.mul_apply]; exact hQ _ (ih y hy)

theorem mem_gen (N : Module.End k U) (Q : Submodule k U) (hQ : ∀ y ∈ Q, N y ∈ Q) (y : U) :
    y ∈ (⨆ m : ℕ, Q.comap (N ^ m)) ↔ ∃ m : ℕ, (N ^ m) y ∈ Q := by
  have hmono : Monotone (fun m : ℕ => Q.comap (N ^ m)) := by
    apply monotone_nat_of_le_succ
    intro m z hz
    simp only [Submodule.mem_comap] at hz ⊢
    rw [pow_succ', Module.End.mul_apply]; exact hQ _ hz
  rw [Submodule.mem_iSup_of_directed _ hmono.directed_le]
  rfl

theorem stab (N : Module.End k U) (Q S : Submodule k U) (hQ : ∀ y ∈ Q, N y ∈ Q)
    [FiniteDimensional k (Q.map S.mkQ)] :
    ∃ M : ℕ, ∀ m : ℕ, (Q.map (N ^ M)).map S.mkQ ≤ (Q.map (N ^ (M + m))).map S.mkQ := by
  have hle : ∀ j : ℕ, (Q.map (N ^ j)).map S.mkQ ≤ Q.map S.mkQ := fun j =>
    Submodule.map_mono (by rintro _ ⟨y, hy, rfl⟩; exact pow_mem N Q hQ j y hy)
  have hfin : ∀ j : ℕ, FiniteDimensional k ((Q.map (N ^ j)).map S.mkQ) := fun j =>
    Submodule.finiteDimensional_of_le (hle j)
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ j : ℕ, Module.finrank k ((Q.map (N ^ M)).map S.mkQ)
      ≤ Module.finrank k ((Q.map (N ^ j)).map S.mkQ) :=
    ⟨Function.argmin (fun j : ℕ => Module.finrank k ((Q.map (N ^ j)).map S.mkQ)),
      fun j => Function.argmin_le (fun j : ℕ => Module.finrank k ((Q.map (N ^ j)).map S.mkQ)) j⟩
  refine ⟨M, fun m => ?_⟩
  have h1 : (Q.map (N ^ (M + m))).map S.mkQ ≤ (Q.map (N ^ M)).map S.mkQ := by
    apply Submodule.map_mono
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨(N ^ m) y, pow_mem N Q hQ m y hy, by rw [pow_add, Module.End.mul_apply]⟩
  haveI := hfin M
  exact (Submodule.eq_of_le_of_finrank_le h1 (hM _)).ge

theorem gen_sup (N : Module.End k U) (P Q S : Submodule k U) (hSQ : S ≤ Q) (hQP : Q ≤ P)
    (hQ : ∀ y ∈ Q, N y ∈ Q) (hS : ∀ y ∈ S, N y ∈ S) [FiniteDimensional k (Q.map S.mkQ)] :
    P ⊓ (⨆ m : ℕ, Q.comap (N ^ m)) = (P ⊓ ⨆ m : ℕ, S.comap (N ^ m)) ⊔ Q := by
  apply le_antisymm
  · rintro u ⟨huP, hu⟩
    obtain ⟨m, hm⟩ := (mem_gen N Q hQ u).1 hu
    obtain ⟨M, hM⟩ := stab N Q S hQ
    obtain ⟨_, ⟨q, hq, rfl⟩, h⟩ := hM m
      (Submodule.mem_map_of_mem (Submodule.mem_map_of_mem (f := N ^ M) hm))
    have h' : (N ^ M) ((N ^ m) u) - (N ^ (M + m)) q ∈ S := by
      simpa [Submodule.Quotient.eq] using h.symm
    have hu' : u = (u - q) + q := by abel
    rw [hu']
    refine Submodule.add_mem_sup ⟨P.sub_mem huP (hQP hq), (mem_gen N S hS _).2 ⟨M + m, ?_⟩⟩ hq
    rw [map_sub]
    convert h' using 2
    rw [pow_add, Module.End.mul_apply]
  · refine sup_le (inf_le_inf_left _ (iSup_mono fun m => Submodule.comap_mono hSQ)) (le_inf hQP ?_)
    intro y hy
    exact (mem_gen N Q hQ y).2 ⟨0, by simpa using hy⟩

theorem main : ∀ {k U : Type} [Field k] [AddCommGroup U] [Module k U] (T : Module.End k U) (P Q S : Submodule k U), S ≤ Q → Q ≤ P → (∀ x ∈ P, T x ∈ P) → (∀ x ∈ Q, T x ∈ Q) → (∀ x ∈ S, T x ∈ S) → FiniteDimensional k (↥P ⧸ S.submoduleOf P) → ∀ x : k, gmult T P S x = gmult T P Q x + gmult T Q S x := by
  intro k U _ _ _ T P Q S hSQ hQP _ hQ hS hfin x
  unfold gmult
  set N := T - algebraMap k (Module.End k U) x with hN
  have hst : ∀ A : Submodule k U, (∀ y ∈ A, T y ∈ A) → ∀ y ∈ A, N y ∈ A := by
    intro A hA y hy
    have : N y = T y - x • y := by simp [hN, Module.algebraMap_end_apply]
    rw [this]
    exact A.sub_mem (hA y hy) (A.smul_mem x hy)
  haveI hP := fin_map P S hfin
  have hf : ∀ A : Submodule k U, A ≤ P → FiniteDimensional k (A.map S.mkQ) := fun A hA =>
    Submodule.finiteDimensional_of_le (Submodule.map_mono hA)
  haveI := hf Q hQP
  have hSG : S ≤ ⨆ m : ℕ, S.comap (N ^ m) := fun y hy =>
    (mem_gen N S (hst S hS) y).2 ⟨0, by simpa using hy⟩
  have h1 := gen_sup N P Q S hSQ hQP (hst Q hQ) (hst S hS)
  set G := ⨆ m : ℕ, S.comap (N ^ m) with hG
  have h2 : Q ⊓ G = (P ⊓ G) ⊓ Q := by
    rw [inf_right_comm, inf_eq_right.2 hQP]
  rw [h1, h2]
  set A := P ⊓ G with hA
  have hSA : S ≤ A := le_inf (hSQ.trans hQP) hSG
  haveI := hf A inf_le_left
  haveI := hf (A ⊔ Q) (sup_le inf_le_left hQP)
  haveI := hf (A ⊓ Q) (inf_le_right.trans hQP)
  have e1 := finrank_quot A S S le_rfl hSA
  have e2 := finrank_quot (A ⊔ Q) Q S hSQ le_sup_right
  have e3 := finrank_quot (A ⊓ Q) S S le_rfl (le_inf hSA hSQ)
  have e4 := Submodule.finrank_sup_add_finrank_inf_eq (A.map S.mkQ) (Q.map S.mkQ)
  rw [← Submodule.map_sup, ← map_inf_mkQ A Q S hSA] at e4
  rw [map_self, finrank_bot] at e1 e3
  omega

end GlobalTheory.PhiGam.GmultAdd
