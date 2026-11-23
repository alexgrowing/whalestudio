import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.SuperlatticeRatio
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PClassMean
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PPhScale
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open UpperHalfPlane ModularForm GroundTheory.Global.Elliptic

noncomputable section

namespace SuperlatticeRatio

theorem eq_of_le_of_relIndex {A B C : Submodule ℤ ℂ} {p : ℕ} (hp : p.Prime) (hAB : A ≤ B)
    (hBC : B ≤ C) (hidx : A.toAddSubgroup.relIndex C.toAddSubgroup = p) (hne : ¬ B ≤ A) :
    B = C := by
  have h := AddSubgroup.relIndex_mul_relIndex (H := A.toAddSubgroup) (K := B.toAddSubgroup)
    (L := C.toAddSubgroup) (fun _ hx ↦ hAB hx) (fun _ hx ↦ hBC hx)
  rw [hidx] at h
  rcases Nat.prime_mul_iff.1 (h ▸ hp) with ⟨-, h1⟩ | ⟨-, h1⟩
  · have h2 := AddSubgroup.relIndex_eq_one.1 h1
    exact le_antisymm hBC (fun x hx ↦ h2 hx)
  · have h2 := AddSubgroup.relIndex_eq_one.1 h1
    exact absurd (fun x hx ↦ h2 hx) hne

theorem mem_span_pair_iff {α β x : ℂ} :
    x ∈ Submodule.span ℤ ({α, β} : Set ℂ) ↔ ∃ m n : ℤ, (m : ℂ) * α + n * β = x := by
  simp [Submodule.mem_span_pair, zsmul_eq_mul]

theorem latticeDiscr_scale_latticeOfTau {c : ℂ} (hc : c ≠ 0) (σ : ℍ) :
    latticeDiscr (scaleLattice c (latticeOfTau σ).lattice) =
      (c ^ 12)⁻¹ * ((2 * Real.pi) ^ 12 * discriminant σ) := by
  rw [PhScale.latticeDiscr_scaleLattice _ hc, latticeDiscr_lattice, discr_latticeOfTau]

theorem proof : SuperlatticeRatio.Statement := by
  intro L L' p hp hle hidx
  obtain ⟨τ, c, hc, hL⟩ := ClassMean.exists_eq_scaleLattice L
  have hLs : L.lattice = Submodule.span ℤ {c * τ, c} := by
    rw [hL, ClassMean.scaleLattice_latticeOfTau]
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hτ : (τ : ℂ).im ≠ 0 := τ.im_pos.ne'
  have hcτ : c * τ ∈ L'.lattice := hle (hLs ▸ Submodule.subset_span (by simp))
  have hc' : c ∈ L'.lattice := hle (hLs ▸ Submodule.subset_span (by simp))

  refine ⟨τ, ?_, ?_⟩
  · rw [← weierstrassCurve_latticeOfTau_j, eq_comm, weierstrassCurve_j_eq_iff]
    refine ⟨c, hc, ?_⟩
    rw [hL, scaleLattice, Submodule.map_coe]
    rfl

  have hne : ¬ L'.lattice ≤ L.lattice := fun h ↦
    hp.one_lt.ne' (hidx ▸ AddSubgroup.relIndex_eq_one.2 (fun x hx ↦ h hx))
  obtain ⟨v, hvL', hvL⟩ := SetLike.not_le_iff_exists.1 hne
  have hpv : (p : ℂ) * v ∈ L.lattice := by
    have := AddSubgroup.nsmul_relIndex_mem L.lattice.toAddSubgroup
      (K := L'.lattice.toAddSubgroup) (g := v) hvL'
    rw [hidx, nsmul_eq_mul] at this
    exact this
  rw [hLs, mem_span_pair_iff] at hpv
  obtain ⟨m, n, hmn⟩ := hpv
  have hLdiscr : latticeDiscr L.lattice = (c ^ 12)⁻¹ * ((2 * Real.pi) ^ 12 * discriminant τ) := by
    rw [hL, latticeDiscr_scale_latticeOfTau hc]
  have hπ : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.2 Real.pi_ne_zero)
  have hz : ∀ (z : ℤ) {x : ℂ}, x ∈ L'.lattice → (z : ℂ) * x ∈ L'.lattice := fun z x hx ↦ by
    rw [← zsmul_eq_mul]; exact zsmul_mem hx z
  by_cases hm : (p : ℤ) ∣ m
  ·
    obtain ⟨k, rfl⟩ := hm
    have hn : ¬ (p : ℤ) ∣ n := by
      rintro ⟨l, rfl⟩
      apply hvL
      rw [hLs, mem_span_pair_iff]
      refine ⟨k, l, mul_left_cancel₀ hp0 ?_⟩
      rw [← hmn]; push_cast; ring
    obtain ⟨u, w, huw⟩ := (hpZ.coprime_iff_not_dvd.2 hn).symm
    set σ := mulPoint ⟨p, hp.pos⟩ τ
    have hσ : (σ : ℂ) = p * τ := coe_mulPoint _ _
    have hcp : c / p ≠ 0 := div_ne_zero hc hp0
    have hM : scaleLattice (c / p) (latticeOfTau σ).lattice = Submodule.span ℤ {c * τ, c / p} := by
      rw [ClassMean.scaleLattice_latticeOfTau, hσ, show c / p * (p * τ) = c * τ by field_simp]
    have heq : scaleLattice (c / p) (latticeOfTau σ).lattice = L'.lattice := by
      refine eq_of_le_of_relIndex hp ?_ ?_ hidx ?_
      · rw [hLs, hM, Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
        refine ⟨?_, ?_⟩ <;> rw [SetLike.mem_coe, mem_span_pair_iff]
        · exact ⟨1, 0, by simp⟩
        · have key2 : (p : ℂ) * (c / p) = c := by field_simp
          exact ⟨0, p, by push_cast; linear_combination key2⟩
      · rw [hM, Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
        refine ⟨?_, ?_⟩
        · exact hcτ
        · have e : c / p = (u : ℂ) * v + ((-(u * k) : ℤ) : ℂ) * (c * τ) + (w : ℂ) * c := by
            have hmn' : (p : ℂ) * v = p * k * (c * τ) + n * c := by rw [← hmn]; push_cast; ring
            have huw' : (u : ℂ) * n + w * p = 1 := by exact_mod_cast huw
            push_cast
            rw [div_eq_iff hp0]
            linear_combination (-(u : ℂ)) * hmn' - c * huw'
          rw [SetLike.mem_coe, e]
          exact add_mem (add_mem (hz u hvL') (hz _ hcτ)) (hz w hc')
      · intro h
        have : c / p ∈ L.lattice := h (hM ▸ Submodule.subset_span (by simp))
        rw [hLs, mem_span_pair_iff] at this
        obtain ⟨m', n', e⟩ := this
        have e2 : c * ((m' : ℂ) * τ + n' - 1 / p) = 0 := by linear_combination e
        have e' : (m' : ℂ) * τ + n' = 1 / p := sub_eq_zero.1 ((mul_eq_zero.1 e2).resolve_left hc)
        have him : (m' : ℝ) * (τ : ℂ).im = 0 := by
          have := congrArg Complex.im e'
          simpa using this
        have hm0 : m' = 0 := by
          rcases mul_eq_zero.1 him with h0 | h0
          · exact_mod_cast h0
          · exact absurd h0 hτ
        subst hm0
        have hre : (n' : ℂ) * p = 1 := by
          have e3 : (n' : ℂ) = 1 / p := by simpa using e'
          rw [e3]; field_simp
        have : (p * n' : ℤ) = 1 := by rw [mul_comm]; exact_mod_cast hre
        exact hpZ.not_dvd_one ⟨n', this.symm⟩
    refine Multiset.mem_cons.2 (Or.inl ?_)
    rw [← heq, latticeDiscr_scale_latticeOfTau hcp, hLdiscr]
    have hΔ := discriminant_ne_zero τ
    simp only [PNat.mk_coe]
    field_simp
    rfl
  ·
    obtain ⟨u, w, huw⟩ := (hpZ.coprime_iff_not_dvd.2 hm).symm
    have hpz : (0 : ℤ) < p := by exact_mod_cast hp.pos
    set r := u * n % p with hr
    set q := u * n / p
    have hr0 : 0 ≤ r := Int.emod_nonneg _ hpz.ne'
    have hrp : r < p := Int.emod_lt_of_pos _ hpz
    have hrq : r + q * p = u * n := Int.emod_add_ediv_mul _ _
    set a := r.toNat
    have ha : (a : ℤ) = r := Int.toNat_of_nonneg hr0
    have hap : a < p := by omega
    have haC : (a : ℂ) = r := by exact_mod_cast ha
    set σ := divPoint ⟨p, hp.pos⟩ a τ
    have hσ : (σ : ℂ) = (a + τ) / p := coe_divPoint _ _ _
    have hM : scaleLattice c (latticeOfTau σ).lattice =
        Submodule.span ℤ {c * ((a + τ) / p), c} := by
      rw [ClassMean.scaleLattice_latticeOfTau, hσ]
    have heq : scaleLattice c (latticeOfTau σ).lattice = L'.lattice := by
      refine eq_of_le_of_relIndex hp ?_ ?_ hidx ?_
      · rw [hLs, hM, Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
        refine ⟨?_, ?_⟩ <;> rw [SetLike.mem_coe, mem_span_pair_iff]
        · have key : (p : ℂ) * (c * ((a + τ) / p)) = c * (a + τ) := by field_simp
          exact ⟨p, -(a : ℤ), by push_cast; linear_combination key⟩
        · exact ⟨0, 1, by simp⟩
      · rw [hM, Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
        refine ⟨?_, ?_⟩
        · have e : c * ((a + τ) / p) = (u : ℂ) * v + (w : ℂ) * (c * τ) + ((-q : ℤ) : ℂ) * c := by
            have hmn' : (p : ℂ) * v = m * (c * τ) + n * c := hmn.symm
            have huw' : (u : ℂ) * m + w * p = 1 := by exact_mod_cast huw
            have hrq' : (r : ℂ) + q * p = u * n := by exact_mod_cast hrq
            have haC' : (a : ℂ) - r = 0 := by rw [haC]; ring
            push_cast
            rw [mul_div_assoc', div_eq_iff hp0]
            linear_combination (-(u : ℂ)) * hmn' - c * τ * huw' + c * hrq' + c * haC'
          rw [SetLike.mem_coe, e]
          exact add_mem (add_mem (hz u hvL') (hz w hcτ)) (hz _ hc')
        · exact hc'
      · intro h
        have : c * ((a + τ) / p) ∈ L.lattice := h (hM ▸ Submodule.subset_span (by simp))
        rw [hLs, mem_span_pair_iff] at this
        obtain ⟨m', n', e⟩ := this
        have hdiv : c * ((a + τ) / p) * p = c * (a + τ) := by field_simp
        have e2 : c * ((a + τ) - p * (m' * τ + n')) = 0 := by
          linear_combination (-(p : ℂ)) * e - hdiv
        have e' : (a : ℂ) + τ - p * (m' * τ + n') = 0 := (mul_eq_zero.1 e2).resolve_left hc
        have him : τ.im * (1 - p * m') = 0 := by
          have := congrArg Complex.im e'
          simp at this
          linear_combination this
        have h1 : ((p * m' : ℤ) : ℝ) = 1 := by
          push_cast
          linarith [(mul_eq_zero.1 him).resolve_left τ.im_pos.ne']
        have h1' : (p * m' : ℤ) = 1 := by exact_mod_cast h1
        exact hpZ.not_dvd_one ⟨m', h1'.symm⟩
    refine Multiset.mem_cons_of_mem (Multiset.mem_map.2 ⟨a, Multiset.mem_range.2 hap, ?_⟩)
    rw [← heq, latticeDiscr_scale_latticeOfTau hc, hLdiscr]
    have hΔ := discriminant_ne_zero τ
    field_simp
    rfl

end SuperlatticeRatio

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
