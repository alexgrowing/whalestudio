import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzCliff

open Module Polynomial

set_option linter.all false

namespace DiscreteGroups.sglob.DzCliff

variable {W V : Type*} [Group W] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem conj_pow (ρ : Representation ℂ W V) (I : Subgroup W) [hI : I.Normal] (φ : W) (q : ℕ)
    (hfrob : ∀ t ∈ I, ρ (φ * t * φ⁻¹) = ρ t ^ q) (j : ℕ) :
    ∀ t ∈ I, ρ (φ ^ j * t * (φ ^ j)⁻¹) = ρ t ^ q ^ j := by
  induction j with
  | zero => intro t _; simp
  | succ j ih =>
    intro t ht
    have hmem : φ ^ j * t * (φ ^ j)⁻¹ ∈ I := hI.conj_mem t ht (φ ^ j)
    have e : φ ^ (j + 1) * t * (φ ^ (j + 1))⁻¹ = φ * (φ ^ j * t * (φ ^ j)⁻¹) * φ⁻¹ := by group
    rw [e, hfrob _ hmem, ih t ht, ← pow_mul, pow_succ]

theorem eig_translate (ρ : Representation ℂ W V) (I : Subgroup W) [I.Normal] (φ : W) (q : ℕ)
    (hfrob : ∀ t ∈ I, ρ (φ * t * φ⁻¹) = ρ t ^ q) {η : W → ℂ} {v : V} (hv : ∀ t ∈ I, ρ t v = η t • v) (j : ℕ) :
    ∀ t ∈ I, ρ t (ρ (φ ^ j)⁻¹ v) = η t ^ q ^ j • ρ (φ ^ j)⁻¹ v := by
  intro t ht
  have e : t * (φ ^ j)⁻¹ = (φ ^ j)⁻¹ * (φ ^ j * t * (φ ^ j)⁻¹) := by group
  rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, conj_pow ρ I φ q hfrob j t ht,
    pow_apply_of_eig (hv t ht), map_smul]

theorem clifford (ρ : Representation ℂ W V) (hρ : ρ.IsIrreducible) (I : Subgroup W) [hI : I.Normal] (φ : W)
    (q n : ℕ) (hn : finrank ℂ V = n) (hpos : 0 < n)
    (hgen : ∀ σ : W, ∃ k : ℤ, ∃ t ∈ I, σ = φ ^ k * t)
    (hcomm : ∀ s ∈ I, ∀ t ∈ I, ρ s * ρ t = ρ t * ρ s)
    (hfrob : ∀ t ∈ I, ρ (φ * t * φ⁻¹) = ρ t ^ q) :
    ∃ (η : W → ℂ) (u : V) (c : ℂ), u ≠ 0 ∧ (∀ t ∈ I, ρ t u = η t • u) ∧ ρ (φ ^ n) u = c • u ∧
      (∀ t ∈ I, (ρ t).charpoly = ∏ j ∈ Finset.range n, (X - C (η t ^ q ^ j))) ∧
      (∀ t ∈ I, η t ^ q ^ n = η t) ∧
      (∀ k, 0 < k → k < n → ∃ t ∈ I, η t ^ q ^ k ≠ η t) := by
  classical
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (hn ▸ hpos)
  obtain ⟨u0, -, hu0, hu0e⟩ := exists_common_eigenvector (ρ '' (I : Set W))
    (by rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩; exact hcomm s hs t ht) ⊤ top_ne_bot (fun _ _ _ _ => trivial)
  have hex0 : ∀ t : W, t ∈ I → ∃ c : ℂ, ρ t u0 = c • u0 := fun t ht => hu0e _ ⟨t, ht, rfl⟩
  choose! η hη using hex0
  have hsurj : ∀ k : ℕ, ∀ t ∈ I, ∃ s ∈ I, η t = η s ^ q ^ k := by
    intro k t ht
    have hs : (φ ^ k)⁻¹ * t * φ ^ k ∈ I := by
      simpa using hI.conj_mem t ht (φ ^ k)⁻¹
    refine ⟨_, hs, ?_⟩
    have e : φ ^ k * ((φ ^ k)⁻¹ * t * φ ^ k) * (φ ^ k)⁻¹ = t := by group
    have h1 := conj_pow ρ I φ q hfrob k _ hs
    rw [e] at h1
    exact eig_unique hu0 (hη t ht) (by rw [h1, pow_apply_of_eig (hη _ hs)])
  have hper_ex : ∃ d, (0 < d ∧ ∀ t ∈ I, η t ^ q ^ d = η t) ∧ d ≤ n := by
    by_contra hcon
    push Not at hcon
    let χ : Fin (n + 1) → (I → ℂ) := fun j t => η t ^ q ^ (j : ℕ)
    have hinj : Function.Injective χ := by
      intro i j hij
      by_contra hne
      wlog hlt : (i : ℕ) < j generalizing i j
      · exact this hij.symm (Ne.symm hne) (lt_of_le_of_ne (not_lt.mp hlt) (fun h => hne (Fin.ext h.symm)))
      have key : 0 < (j : ℕ) - i ∧ ∀ t ∈ I, η t ^ q ^ ((j : ℕ) - i) = η t := by
        refine ⟨Nat.sub_pos_of_lt hlt, fun t ht => ?_⟩
        obtain ⟨s, hs, hts⟩ := hsurj i t ht
        have hij' := congrFun hij ⟨s, hs⟩
        simp only [χ] at hij'
        rw [hts, ← pow_mul, ← pow_add, Nat.add_sub_cancel' hlt.le]
        exact hij'.symm
      have h2 := hcon _ key
      have hj := j.2
      omega
    let f : I → End ℂ V := fun t => ρ t
    have hind := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f
      (fun i j φ' => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j j.2 i i.2) φ')
    let v : Fin (n + 1) → V := fun j => ρ (φ ^ (j : ℕ))⁻¹ u0
    have hli : LinearIndependent ℂ v := by
      refine (hind.comp hinj).linearIndependent _ (fun j => ?_) (fun j => rho_ne_zero ρ _ hu0)
      simp only [Function.comp, Submodule.mem_iInf]
      intro t
      exact Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.mpr
        (eig_translate ρ I φ q hfrob hη j t t.2))
    have := hli.fintype_card_le_finrank
    simp [hn] at this
  set d := Nat.find hper_ex with hd
  obtain ⟨hdper, hdn⟩ := Nat.find_spec hper_ex
  have hdmin : ∀ k, 0 < k → k < d → ∃ t ∈ I, η t ^ q ^ k ≠ η t := by
    intro k hk hkd
    by_contra hcon
    push Not at hcon
    exact Nat.find_min hper_ex hkd ⟨⟨hk, hcon⟩, by omega⟩
  let Vη : Submodule ℂ V := ⨅ t : I, Module.End.eigenspace (ρ t) (η t)
  have memVη : ∀ v, v ∈ Vη ↔ ∀ t ∈ I, ρ t v = η t • v := by
    intro v
    simp only [Vη, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
    exact ⟨fun h t ht => h ⟨t, ht⟩, fun h t => h t t.2⟩
  have hu0η : u0 ∈ Vη := (memVη u0).mpr hη
  have hstab : ∀ v ∈ Vη, ρ (φ ^ d)⁻¹ v ∈ Vη := by
    intro v hv
    rw [memVη] at hv ⊢
    intro t ht
    rw [eig_translate ρ I φ q hfrob hv d t ht, hdper.2 t ht]
  have hVη : Vη ≠ ⊥ := by
    intro h
    rw [h] at hu0η
    exact hu0 ((Submodule.mem_bot ℂ).mp hu0η)
  obtain ⟨u, huη, hu, hue⟩ := exists_common_eigenvector {ρ (φ ^ d)⁻¹}
    (fun f hf g hg => by rw [Set.mem_singleton_iff.mp hf, Set.mem_singleton_iff.mp hg]) Vη hVη
    (fun f hf v hv => by rw [Set.mem_singleton_iff.mp hf]; exact hstab v hv)
  obtain ⟨c, hc⟩ := hue _ (Set.mem_singleton _)
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact rho_ne_zero ρ _ hu (by rw [hc, zero_smul])
  have hcinv : ρ (φ ^ d) u = c⁻¹ • u := by
    have h1 := rho_apply_inv ρ (φ ^ d) u
    rw [hc, map_smul] at h1
    calc ρ (φ ^ d) u = c⁻¹ • (c • ρ (φ ^ d) u) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
      _ = c⁻¹ • u := by rw [h1]
  have hz : ∀ m : ℤ, ρ ((φ ^ d)⁻¹ ^ m) u = c ^ m • u := by
    intro m
    induction m using Int.induction_on with
    | zero => simp
    | succ k ih =>
      rw [zpow_add_one, map_mul, Module.End.mul_apply, hc, map_smul, ih, smul_smul, zpow_add_one₀ hc0, mul_comm]
    | pred k ih =>
      rw [zpow_sub_one, map_mul, Module.End.mul_apply, inv_inv, hcinv, map_smul, ih, smul_smul,
        zpow_sub_one₀ hc0, mul_comm]
  have huI : ∀ t ∈ I, ρ t u = η t • u := (memVη u).mp huη
  have hbη : ∀ j : ℕ, ∀ t ∈ I, ρ t (ρ (φ ^ j)⁻¹ u) = η t ^ q ^ j • ρ (φ ^ j)⁻¹ u :=
    fun j => eig_translate ρ I φ q hfrob huI j
  let b : Fin d → V := fun j => ρ (φ ^ (j : ℕ))⁻¹ u
  let S : Submodule ℂ V := Submodule.span ℂ (Set.range b)
  have hbS : ∀ j : Fin d, ρ (φ ^ (j : ℕ))⁻¹ u ∈ S := fun j => Submodule.subset_span ⟨j, rfl⟩
  have hpowmem : ∀ e : ℤ, ρ (φ ^ e) u ∈ S := by
    intro e
    have hd0 : (0 : ℤ) < d := by exact_mod_cast hdper.1
    have hr0 : 0 ≤ (-e) % (d : ℤ) := Int.emod_nonneg _ hd0.ne'
    have hrd : (-e) % (d : ℤ) < d := Int.emod_lt_of_pos _ hd0
    have hdec := Int.mul_ediv_add_emod (-e) d
    have hdecomp : φ ^ e = (φ ^ ((-e) % (d : ℤ)).toNat)⁻¹ * (φ ^ d)⁻¹ ^ ((-e) / (d : ℤ)) := by
      have h1 : e = -(((-e) % (d : ℤ)).toNat : ℤ) + -((d : ℤ) * ((-e) / (d : ℤ))) := by
        rw [Int.toNat_of_nonneg hr0]; omega
      conv_lhs => rw [h1]
      rw [zpow_add, zpow_neg, zpow_natCast, zpow_neg, zpow_mul, zpow_natCast, inv_zpow]
    have htn : ((-e) % (d : ℤ)).toNat < d := by omega
    rw [hdecomp, map_mul, Module.End.mul_apply, hz, map_smul]
    exact S.smul_mem _ (hbS ⟨_, htn⟩)
  have hSst : ∀ σ : W, ∀ v ∈ S, ρ σ v ∈ S := by
    intro σ v hv
    obtain ⟨k, t, ht, rfl⟩ := hgen σ
    have hle : S ≤ S.comap (ρ (φ ^ k * t)) := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      show ρ (φ ^ k * t) (ρ (φ ^ (j : ℕ))⁻¹ u) ∈ S
      rw [map_mul, Module.End.mul_apply, hbη j t ht, map_smul, ← Module.End.mul_apply, ← map_mul]
      refine S.smul_mem _ ?_
      have e2 : φ ^ k * (φ ^ (j : ℕ))⁻¹ = φ ^ (k - (j : ℕ)) := by group
      rw [e2]
      exact hpowmem _
    exact hle hv
  have hS0 : S ≠ ⊥ := by
    intro h
    have := hbS ⟨0, hdper.1⟩
    rw [h, Submodule.mem_bot] at this
    simp at this
    exact hu this
  have hStop : S = ⊤ := eq_top_of_stable ρ hρ S hS0 hSst
  have hnd : n ≤ d := by
    have h1 := finrank_range_le_card (R := ℂ) (b := b)
    rw [Set.finrank, show Submodule.span ℂ (Set.range b) = ⊤ from hStop, finrank_top, hn] at h1
    simpa using h1
  have hdn' : d = n := le_antisymm hdn hnd
  have hcard : Fintype.card (Fin d) = finrank ℂ V := by simp [hn, hdn']
  let B := basisOfTopLeSpanOfCardEqFinrank b hStop.ge hcard
  have hB : ∀ j, B j = b j := fun j => by simp [B]
  have hchar : ∀ t ∈ I, (ρ t).charpoly = ∏ j ∈ Finset.range d, (X - C (η t ^ q ^ j)) := by
    intro t ht
    rw [← LinearMap.charpoly_toMatrix (ρ t) B]
    have hM : LinearMap.toMatrix B B (ρ t) = Matrix.diagonal (fun j : Fin d => η t ^ q ^ (j : ℕ)) := by
      ext i j
      rw [LinearMap.toMatrix_apply, Matrix.diagonal_apply, hB j]
      show B.repr (ρ t (ρ (φ ^ (j : ℕ))⁻¹ u)) i = _
      rw [hbη j t ht, map_smul]
      have hBj : ρ (φ ^ (j : ℕ))⁻¹ u = B j := (hB j).symm
      rw [hBj, B.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij, Ne.symm hij]
    rw [hM, Matrix.charpoly_diagonal, Fin.prod_univ_eq_prod_range (fun j => X - C (η t ^ q ^ j)) d]
  refine ⟨η, u, c⁻¹, hu, huI, by rw [← hdn']; exact hcinv, fun t ht => by rw [← hdn']; exact hchar t ht,
    fun t ht => by rw [← hdn']; exact hdper.2 t ht, fun k hk hkn => hdmin k hk (by omega)⟩

end DiscreteGroups.sglob.DzCliff
