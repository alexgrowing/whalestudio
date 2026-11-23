import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ArithmeticGapBounds.Arith
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ArithmeticGapBounds.PDensG
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ArithmeticGapBounds.PDensM

noncomputable section

open NumberField Matrix

namespace PositivityTheory.KB.SpectralGap

namespace WordTransvectionCongruences

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

theorem exists_third {N : ℕ} (hN : 3 ≤ N) (i j : Fin N) : ∃ k : Fin N, k ≠ i ∧ k ≠ j := by
  by_contra hc
  push_neg at hc
  have hsub : (Finset.univ : Finset (Fin N)) ⊆ {i, j} := by
    intro k _
    by_cases hk : k = i
    · simp [hk]
    · simp [hc k hk]
  have h1 := Finset.card_le_card hsub
  have h2 : ({i, j} : Finset (Fin N)).card ≤ 2 := by
    calc ({i, j} : Finset (Fin N)).card ≤ ({j} : Finset (Fin N)).card + 1 := Finset.card_insert_le _ _
      _ = 2 := by simp
  rw [Finset.card_univ, Fintype.card_fin] at h1
  omega

theorem mo_tv {i j : Fin N} (h : i ≠ j) (t : 𝓞 L) :
    mo L N (SpecialLinearGroup.transvection h t) = transvection i j (t : L) := by
  ext a b
  simp [mo, mt, SpecialLinearGroup.transvection_coe, Matrix.transvection, Matrix.one_apply, Matrix.single_apply]
  split_ifs <;> simp

theorem integral_transvection_mem_slIntegers_conjugate_zero (π : 𝓞 L) {i j : Fin N} (h : i ≠ j) (t : 𝓞 L) :
    SpecialLinearGroup.transvection h (t : L) ∈ Kg L N π 0 := by
  show ∃ γ, dg L N π 0 * (mt L N) (SpecialLinearGroup.transvection h (t : L)) = (mo L N) γ * dg L N π 0
  refine ⟨SpecialLinearGroup.transvection h t, ?_⟩
  have hd : dg L N π 0 = 1 := by
    ext a b
    simp [dg, Matrix.diagonal, Matrix.one_apply]
  rw [hd, mo_tv]
  simp [mt, SpecialLinearGroup.transvection_coe, Matrix.transvection]

theorem mem_parahoricTimesPrincipalCongruence_iff (π : 𝓞 L) (hπ : (π : L) ≠ 0) {i j : Fin N} (h : i ≠ j) (hi : (i : ℕ) = 0) (t : 𝓞 L) :
    SpecialLinearGroup.transvection h ((t : L) / π) ∈ Kg L N π 1 := by
  show ∃ γ, dg L N π 1 * (mt L N) (SpecialLinearGroup.transvection h ((t : L) / π)) = (mo L N) γ * dg L N π 1
  refine ⟨SpecialLinearGroup.transvection h t, ?_⟩
  rw [mo_tv]
  have hj : ¬ ((j : ℕ) < 1) := by
    intro hj
    apply h
    ext
    omega
  have hi' : (i : ℕ) < 1 := by omega
  ext a b
  simp only [mt, dg, SpecialLinearGroup.coeMonoidHom_apply, SpecialLinearGroup.transvection_coe,
    Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.transvection, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply]
  by_cases hab : i = a ∧ j = b
  · obtain ⟨rfl, rfl⟩ := hab
    simp [h, hi', hj]
    field_simp
  · simp only [hab, if_false, add_zero]
    split_ifs <;> simp_all

theorem comm_mem {G : Subgroup (SpecialLinearGroup (Fin N) L)} {i j k : Fin N} (hik : i ≠ k) (hkj : k ≠ j)
    (hij : i ≠ j) {a b : L} (ha : SpecialLinearGroup.transvection hik a ∈ G)
    (hb : SpecialLinearGroup.transvection hkj b ∈ G) : SpecialLinearGroup.transvection hij (a * b) ∈ G := by
  have hn : ∀ (p q : Fin N) (x : L), Matrix.single p q (-x) = -Matrix.single p q x := by
    intro p q x
    ext r s
    simp [Matrix.single_apply]
    split_ifs <;> simp
  have m1 : ∀ {p q : Fin N} (hpq : p ≠ q) (x : L),
      (1 + Matrix.single p q x) * (1 + Matrix.single p q (-x)) = (1 : Matrix (Fin N) (Fin N) L) := by
    intro p q hpq x
    have z : Matrix.single p q x * Matrix.single p q (-x) = (0 : Matrix (Fin N) (Fin N) L) :=
      Matrix.single_mul_single_of_ne (h := hpq.symm) ..
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, z, Matrix.one_mul, Matrix.one_mul, Matrix.mul_one, hn]
    abel
  have hinv : ∀ {p q : Fin N} (hpq : p ≠ q) (x : L),
      (SpecialLinearGroup.transvection hpq x)⁻¹ = SpecialLinearGroup.transvection hpq (-x) := by
    intro p q hpq x
    rw [inv_eq_iff_mul_eq_one]
    exact Subtype.ext (m1 hpq x)
  have m : (1 + Matrix.single i k a) * (1 + Matrix.single k j b) * (1 + Matrix.single i k (-a)) *
      (1 + Matrix.single k j (-b)) = (1 + Matrix.single i j (a * b) : Matrix (Fin N) (Fin N) L) := by
    simp [Matrix.add_mul, Matrix.mul_add, Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, hik, hkj, hij, hik.symm, hkj.symm, hij.symm]
    simp only [hn]
    abel
  have hx := G.mul_mem (G.mul_mem (G.mul_mem ha hb) (G.inv_mem ha)) (G.inv_mem hb)
  rw [hinv, hinv] at hx
  convert hx using 1
  exact Subtype.ext m.symm

theorem mem_sup (π : 𝓞 L) (hπ : (π : L) ≠ 0) (hN : 3 ≤ N) (m : ℕ) :
    ∀ {i j : Fin N} (h : i ≠ j) (t : 𝓞 L),
      SpecialLinearGroup.transvection h ((t : L) / (π : L) ^ m) ∈ Kg L N π 0 ⊔ Kg L N π 1 := by
  obtain ⟨z, hz⟩ : ∃ z : Fin N, (z : ℕ) = 0 := ⟨⟨0, by omega⟩, rfl⟩
  induction m with
  | zero =>
    intro i j h t
    simpa using Subgroup.mem_sup_left (S := Kg L N π 0) (T := Kg L N π 1) (integral_transvection_mem_slIntegers_conjugate_zero π h t)
  | succ m ih =>
    have hK1 : ∀ {j : Fin N} (hzj : z ≠ j),
        SpecialLinearGroup.transvection hzj (((1 : 𝓞 L) : L) / π) ∈ Kg L N π 0 ⊔ Kg L N π 1 :=
      fun hzj => Subgroup.mem_sup_right (mem_parahoricTimesPrincipalCongruence_iff π hπ hzj hz 1)
    have hK0 : ∀ {i j : Fin N} (hij : i ≠ j),
        SpecialLinearGroup.transvection hij (((1 : 𝓞 L) : L)) ∈ Kg L N π 0 ⊔ Kg L N π 1 :=
      fun hij => Subgroup.mem_sup_left (integral_transvection_mem_slIntegers_conjugate_zero π hij 1)
    have c1 : ∀ {i j : Fin N} (h : i ≠ j) (t : 𝓞 L), i ≠ z → j ≠ z →
        SpecialLinearGroup.transvection h ((t : L) / (π : L) ^ (m + 1)) ∈ Kg L N π 0 ⊔ Kg L N π 1 := by
      intro i j h t hiz hjz
      have := comm_mem hiz (Ne.symm hjz) h (ih hiz t) (hK1 (Ne.symm hjz))
      convert this using 2
      push_cast
      field_simp
      ring
    have c0 : ∀ {j : Fin N} (h : z ≠ j) (t : 𝓞 L),
        SpecialLinearGroup.transvection h ((t : L) / (π : L) ^ (m + 1)) ∈ Kg L N π 0 ⊔ Kg L N π 1 := by
      intro j h t
      obtain ⟨k, hkz, hkj⟩ := exists_third hN z j
      have := comm_mem (Ne.symm hkz) hkj h (hK1 (Ne.symm hkz)) (ih hkj t)
      convert this using 2
      push_cast
      field_simp
      ring
    have c2 : ∀ {i : Fin N} (h : i ≠ z) (t : 𝓞 L),
        SpecialLinearGroup.transvection h ((t : L) / (π : L) ^ (m + 1)) ∈ Kg L N π 0 ⊔ Kg L N π 1 := by
      intro i h t
      obtain ⟨k, hki, hkz⟩ := exists_third hN i z
      have := comm_mem (Ne.symm hki) hkz h (c1 (Ne.symm hki) t h hkz) (hK0 hkz)
      convert this using 2
      push_cast
      ring
    intro i j h t
    by_cases hi : i = z
    · subst hi
      exact c0 h t
    · by_cases hj : j = z
      · subst hj
        exact c2 h t
      · exact c1 h t hi hj

theorem jS_tv {i j : Fin N} (h : i ≠ j) (c : L) :
    jS L N (SpecialLinearGroup.transvection h c) = fun w => SpecialLinearGroup.transvection h (w.embedding c) := by
  funext w
  ext a b
  simp [jS, SpecialLinearGroup.transvection_coe, Matrix.one_apply, Matrix.single_apply]
  split_ifs <;> simp

theorem continuous_tv {ι : Type} [Fintype ι] [DecidableEq ι] {i j : ι} (h : i ≠ j) :
    Continuous fun c : ℂ => SpecialLinearGroup.transvection h c := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro a
  apply continuous_pi
  intro b
  simp only [Matrix.transvection, Matrix.add_apply, Matrix.single_apply]
  split_ifs <;> fun_prop

end WordTransvectionCongruences

open WordTransvectionCongruences in
theorem dens_holds : Dens := by
  classical
  intro L _ _ hL π hp N hN
  haveI : Nontrivial (Fin N) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hπ : (π : L) ≠ 0 := by exact_mod_cast hp.ne_zero
  set H := Subgroup.map (jS L N) (Kg L N π 0 ⊔ Kg L N π 1) with hH
  have hv : ∀ {i j : Fin N} (h : i ≠ j) (v : InfinitePlace L → ℂ),
      (fun w => SpecialLinearGroup.transvection h (v w)) ∈ H.topologicalClosure := by
    intro i j h v
    have hc : Continuous fun u : InfinitePlace L → ℂ => (fun w => SpecialLinearGroup.transvection h (u w) : Sp L N) :=
      continuous_pi fun w => (continuous_tv h).comp (continuous_apply w)
    have hd := WordTransvectionCongruences.dense_pow π hp.not_unit hp.ne_zero
    have hr := hc.range_subset_closure_image_dense hd ⟨v, rfl⟩
    rw [← SetLike.mem_coe, Subgroup.topologicalClosure_coe]
    refine closure_mono ?_ hr
    rintro _ ⟨z, ⟨t, k, rfl⟩, rfl⟩
    refine ⟨_, mem_sup π hπ hN k h t, ?_⟩
    rw [jS_tv]
  have htop : H.topologicalClosure = ⊤ := by
    rw [eq_top_iff, ← Subgroup.pi_top Set.univ, Subgroup.pi_le_iff]
    intro w₀
    rw [Subgroup.map_le_iff_le_comap]
    have hs := WordTransvectionCongruences.sl_top (Subgroup.comap
        (MonoidHom.mulSingle (fun _ : InfinitePlace L => Matrix.SpecialLinearGroup (Fin N) ℂ) w₀)
        H.topologicalClosure) (by
      intro i j h c
      rw [Subgroup.mem_comap]
      convert hv h (Pi.single w₀ c) using 1
      funext w
      rw [MonoidHom.mulSingle_apply]
      by_cases hw : w = w₀
      · subst hw
        simp
      · rw [Pi.mulSingle_eq_of_ne hw, Pi.single_eq_of_ne hw]
        ext a b
        simp [SpecialLinearGroup.transvection_coe, Matrix.transvection])
    rw [hs]
  rw [dense_iff_closure_eq, ← Subgroup.topologicalClosure_coe, htop, Subgroup.coe_top]

end PositivityTheory.KB.SpectralGap
