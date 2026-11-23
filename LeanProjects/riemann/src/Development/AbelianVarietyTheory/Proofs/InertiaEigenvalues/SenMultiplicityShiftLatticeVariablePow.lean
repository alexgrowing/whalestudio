import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NabBijectiveWindow

noncomputable section
namespace GlobalTheory.PhiGam.SenShift
open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries

theorem mem_iSup_comap_pow {k U : Type} [Field k] [AddCommGroup U] [Module k U] (S : Module.End k U)
    (Q : Submodule k U) (hQ : ∀ p ∈ Q, S p ∈ Q) (u : U) :
    u ∈ (⨆ m : ℕ, Q.comap (S ^ m)) ↔ ∃ m : ℕ, (S ^ m) u ∈ Q := by
  have hmono : Monotone fun m : ℕ => Q.comap (S ^ m) := by
    refine monotone_nat_of_le_succ fun m p hp => ?_
    rw [Submodule.mem_comap] at hp ⊢
    rw [pow_succ', Module.End.mul_apply]
    exact hQ _ hp
  exact Submodule.mem_iSup_of_directed _ hmono.directed_le

theorem gmult_transport {k U : Type} [Field k] [AddCommGroup U] [Module k U] (T T' : Module.End k U)
    (P Q P' Q' : Submodule k U) (e : U ≃ₗ[k] U) (x y : k)
    (heP : ∀ u, e u ∈ P' ↔ u ∈ P) (heQ : ∀ u, e u ∈ Q' ↔ u ∈ Q)
    (hP : ∀ p ∈ P, T p ∈ P) (hQ : ∀ p ∈ Q, T p ∈ Q) (hQ' : ∀ p ∈ Q', T' p ∈ Q')
    (h : ∀ p ∈ P, T' (e p) - x • e p - e (T p - y • p) ∈ Q') :
    gmult T' P' Q' x = gmult T P Q y := by
  unfold gmult
  set S := T - algebraMap k (Module.End k U) y with hSdef
  set S' := T' - algebraMap k (Module.End k U) x with hS'def
  have hS : ∀ u, S u = T u - y • u := fun u => by simp [hSdef, Module.algebraMap_end_apply]
  have hS' : ∀ u, S' u = T' u - x • u := fun u => by simp [hS'def, Module.algebraMap_end_apply]
  have hSP : ∀ p ∈ P, S p ∈ P := fun p hp => by rw [hS]; exact P.sub_mem (hP p hp) (P.smul_mem _ hp)
  have hSQ : ∀ p ∈ Q, S p ∈ Q := fun p hp => by rw [hS]; exact Q.sub_mem (hQ p hp) (Q.smul_mem _ hp)
  have hSQ' : ∀ p ∈ Q', S' p ∈ Q' := fun p hp => by
    rw [hS']; exact Q'.sub_mem (hQ' p hp) (Q'.smul_mem _ hp)
  have hpow : ∀ m : ℕ, ∀ p ∈ P, (S ^ m) p ∈ P ∧ (S' ^ m) (e p) - e ((S ^ m) p) ∈ Q' := by
    intro m p hp
    induction m with
    | zero => simpa using hp
    | succ m ih =>
      obtain ⟨h1, h2⟩ := ih
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply]
      refine ⟨hSP _ h1, ?_⟩
      have h3 := h _ h1
      rw [← hS, ← hS'] at h3
      have h4 := Q'.add_mem (hSQ' _ h2) h3
      rw [map_sub] at h4
      simpa using h4
  set A := P ⊓ ⨆ m : ℕ, Q.comap (S ^ m) with hA
  set A' := P' ⊓ ⨆ m : ℕ, Q'.comap (S' ^ m) with hA'
  have heA : ∀ u, e u ∈ A' ↔ u ∈ A := by
    intro u
    rw [hA, hA', Submodule.mem_inf, Submodule.mem_inf, heP, mem_iSup_comap_pow S Q hSQ,
      mem_iSup_comap_pow S' Q' hSQ']
    refine and_congr_right fun hu => exists_congr fun m => ?_
    rw [← heQ]
    have h2 := (hpow m u hu).2
    constructor
    · intro h1; simpa using Q'.sub_mem h1 h2
    · intro h1; simpa using Q'.add_mem h2 h1
  have hmap : A.map (e : U →ₗ[k] U) = A' := by
    ext u
    obtain ⟨u, rfl⟩ := e.surjective u
    rw [heA]
    exact Submodule.mem_map_equiv A |>.trans (by simp)
  let E : A ≃ₗ[k] A' := e.ofSubmodules A A' hmap
  have hE : ∀ z : A, ((E z : A') : U) = e z := fun z => rfl
  refine (Submodule.Quotient.equiv (Q.submoduleOf A) (Q'.submoduleOf A') E ?_).finrank_eq.symm
  ext z
  obtain ⟨z, rfl⟩ := E.surjective z
  refine (Submodule.mem_map_equiv _).trans ?_
  rw [LinearEquiv.symm_apply_apply]
  change (z : U) ∈ Q ↔ ((E z : A') : U) ∈ Q'
  rw [hE, heQ]

theorem sen_sh : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (g : V →ₗ[k] V), Semi R.γ g → ∀ N : Submodule k⟦X⟧ V, IsLat N → CondC g N → ∀ (a : ℤ) (x : k), sen g (sh a N) x = sen g N (x + a) := by
  intro k _ l _ _ R V _ _ _ _ _ _ _ _ g hg N _ hC a x
  have hv : vv k ≠ 0 := vv_ne_zero k
  let e : V ≃ₗ[k] V :=
    (LinearEquiv.smulOfNeZero k⸨X⸩ V (vv k ^ a) (zpow_ne_zero a hv)).restrictScalars k
  have he : ∀ u, e u = vv k ^ a • u := fun u => rfl
  have hmem : ∀ (M : Submodule k⟦X⟧ V) (u : V), e u ∈ sh a M ↔ u ∈ M := fun M u => by
    rw [he, mem_sh_iff_smul_mem, smul_smul, ← zpow_add₀ hv, neg_add_cancel, zpow_zero, one_smul]
  have hsh : sh 1 (sh a N) = sh a (sh 1 N) := by rw [sh_sh_eq, sh_sh_eq, add_comm]
  unfold sen qmult
  refine gmult_transport (nab g) (nab g) _ _ _ _ e x (x + a) (fun u => hmem N u) (fun u => ?_)
    (fun p hp => Window.nab_mem hC hp) (fun p hp => Window.nab_mem_sh R hg hC 1 hp) (fun p hp => ?_)
    (fun p hp => ?_)
  · rw [hsh]; exact hmem _ u
  · rw [sh_sh_eq] at hp ⊢
    exact Window.nab_mem_sh R hg hC _ hp
  · obtain ⟨n', hn', h⟩ := Window.nab_shift R hg hC a hp
    rw [← he, ← he] at h
    rw [hsh, h, ← map_smul, ← map_sub, ← map_sub]
    refine (hmem _ _).2 (mem_sh_iff_exists.2 ⟨n', hn', ?_⟩)
    rw [zpow_one, add_smul]
    abel

end GlobalTheory.PhiGam.SenShift
