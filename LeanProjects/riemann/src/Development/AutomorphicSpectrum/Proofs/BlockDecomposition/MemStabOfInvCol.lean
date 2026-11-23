import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.UnitTestFunctions.LiftUnit

noncomputable section

open NumberField IsDedekindDomain Matrix Topology
open scoped NumberField.AdeleRing Nat

namespace GlobalTheory.CompanionTheory.RgEisSupp

open PositivityTheory.RgEis PositivityTheory.RgEis.TF

theorem inM_of_dvd {k : Type} [Field k] [NumberField k] {M N : ℕ} (h : M ∣ N)
    {x : FiniteAdeleRing (𝓞 k) k} (hx : InM N x) : InM M x := by
  obtain ⟨c, rfl⟩ := h
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨(c : FiniteAdeleRing (𝓞 k) k) * y, (OH k).mul_mem (natCast_mem _ c) hy, ?_⟩
  push_cast
  ring

theorem col_apply {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]
    (i₀ : ι) (κ : GL ι 𝔸[k]) (r : ι) :
    TF.col i₀ κ r = ((κ⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) r i₀ := by
  rw [TF.col, Matrix.mulVec_single_one]
  rfl

theorem mem_stab_of_inv_col {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
    (g : GL ι R) (i₀ : ι) (h : ∀ j, j ≠ i₀ → ((g⁻¹ : GL ι R) : Matrix ι ι R) j i₀ = 0) :
    g ∈ stab R ({i₀} : Set ι) := by
  have key : ∀ r, (g : Matrix ι ι R) r i₀ * ((g⁻¹ : GL ι R) : Matrix ι ι R) i₀ i₀ = (1 : Matrix ι ι R) r i₀ := by
    intro r
    have e : ((g : Matrix ι ι R) * ((g⁻¹ : GL ι R) : Matrix ι ι R)) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [← e, Matrix.mul_apply]
    exact (Finset.sum_eq_single (f := fun m => (g : Matrix ι ι R) r m * ((g⁻¹ : GL ι R) : Matrix ι ι R) m i₀) i₀
      (fun m _ hm => by simp only [h m hm, mul_zero]) (fun hi => absurd (Finset.mem_univ _) hi)).symm
  show ∀ r ∉ ({i₀} : Set ι), ∀ c ∈ ({i₀} : Set ι),
    (g : Matrix ι ι R) r c = 0 ∧ ((g⁻¹ : GL ι R) : Matrix ι ι R) r c = 0
  intro r hr c hc
  obtain rfl : c = i₀ := hc
  have hr' : r ≠ c := hr
  refine ⟨?_, h r hr'⟩
  have h0 := key r
  have h1 := key c
  rw [Matrix.one_apply_ne hr'] at h0
  rw [Matrix.one_apply_eq] at h1
  calc (g : Matrix ι ι R) r c
      = (g : Matrix ι ι R) r c * ((g : Matrix ι ι R) c c * ((g⁻¹ : GL ι R) : Matrix ι ι R) c c) := by rw [h1, mul_one]
    _ = ((g : Matrix ι ι R) r c * ((g⁻¹ : GL ι R) : Matrix ι ι R) c c) * (g : Matrix ι ι R) c c := by ring
    _ = 0 := by rw [h0, zero_mul]

theorem supp : ColLaw → InMTop → Supp := by
  intro hCol hTop k _ _ ι _ _ i₀ hK U hU M₀ hM₀
  obtain ⟨hmem, hcont, -, -⟩ := hCol k ι i₀
  obtain ⟨hclop, hzero⟩ := hTop k
  have : CompactSpace ((adStd k).kGL ι) := isCompact_iff_compactSpace.mp hK

  set O : Set ((adStd k).kGL ι) :=
    {κ | ∃ p : (adStd k).kGL ι, p.1 ∈ stab 𝔸[k] ({i₀} : Set ι) ∧ ∃ u ∈ interior U, κ = p * u} with hOdef
  have hO : IsOpen O := by
    have e : O = ⋃ p : {p : (adStd k).kGL ι // p.1 ∈ stab 𝔸[k] ({i₀} : Set ι)},
        (fun x => (p.1)⁻¹ * x) ⁻¹' interior U := by
      ext κ
      simp only [hOdef, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_preimage]
      constructor
      · rintro ⟨p, hp, u, hu, rfl⟩
        exact ⟨⟨p, hp⟩, by simpa using hu⟩
      · rintro ⟨⟨p, hp⟩, h⟩
        exact ⟨p, hp, _, h, by simp⟩
    rw [e]
    exact isOpen_iUnion fun p => isOpen_interior.preimage (continuous_const.mul continuous_id)
  have hfc : Continuous fun κ : (adStd k).kGL ι => TF.col i₀ κ.1 := hcont.comp continuous_subtype_val

  set C : ℕ → Set ((adStd k).kGL ι) := fun n =>
    {κ | (∀ j, j ≠ i₀ → InM (n ! * M₀) (TF.col i₀ κ.1 j).2) ∧
      ∀ w, 1 - 1 / ((n : ℝ) + 1) ≤ ‖(TF.col i₀ κ.1 i₀).1 w‖ ^ 2} with hCdef
  have hne : ∀ n : ℕ, n ! * M₀ ≠ 0 := fun n => Nat.mul_ne_zero (Nat.factorial_ne_zero n) hM₀
  have hCcl : ∀ n, IsClosed (C n) := by
    intro n
    simp only [hCdef, Set.setOf_and, Set.setOf_forall]
    refine IsClosed.inter (isClosed_iInter fun j => isClosed_iInter fun _ => ?_) (isClosed_iInter fun w => ?_)
    · have c2 : Continuous fun κ : (adStd k).kGL ι => (TF.col i₀ κ.1 j).2 :=
        continuous_snd.comp ((continuous_apply j).comp hfc)
      exact (hclop _ (hne n)).2.preimage c2
    · have c1 : Continuous fun κ : (adStd k).kGL ι => ‖(TF.col i₀ κ.1 i₀).1 w‖ ^ 2 :=
        (((continuous_apply w).comp (continuous_fst.comp ((continuous_apply i₀).comp hfc))).norm).pow 2
      exact isClosed_le continuous_const c1
  have hanti : ∀ n, C (n + 1) ⊆ C n := by
    intro n κ hκ
    refine ⟨fun j hj => inM_of_dvd (Nat.mul_dvd_mul_right (Nat.factorial_dvd_factorial (Nat.le_succ n)) M₀) (hκ.1 j hj), fun w => ?_⟩
    refine le_trans ?_ (hκ.2 w)
    have : (1 : ℝ) / (((n + 1 : ℕ) : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      push_cast
      linarith
    linarith
  have hex : ∃ n, C n ⊆ O := by
    by_contra hno
    push_neg at hno
    obtain ⟨κ, hκ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      (fun n => C n \ O) (fun n => Set.diff_subset_diff_left (hanti n))
      (fun n => Set.nonempty_of_not_subset (hno n)) ((hCcl 0).sdiff hO).isCompact
      (fun n => (hCcl n).sdiff hO)
    have hall : ∀ n, κ ∈ C n := fun n => (Set.mem_iInter.1 hκ n).1
    have hκO : κ ∉ O := (Set.mem_iInter.1 hκ 0).2
    have hfin : ∀ j, j ≠ i₀ → (TF.col i₀ κ.1 j).2 = 0 := fun j hj =>
      hzero _ fun M hM => inM_of_dvd
        ((Nat.dvd_factorial (Nat.pos_of_ne_zero hM) le_rfl).mul_right M₀) ((hall M).1 j hj)
    have hone : ∀ w, 1 ≤ ‖(TF.col i₀ κ.1 i₀).1 w‖ ^ 2 := by
      intro w
      refine le_of_forall_pos_le_add fun ε hε => ?_
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
      have := (hall n).2 w
      linarith
    have hinf : ∀ j, j ≠ i₀ → (TF.col i₀ κ.1 j).1 = 0 := by
      intro j hj
      funext w
      have hs := (hmem κ.1 κ.2).1 w
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)] at hs
      have hle : ‖(TF.col i₀ κ.1 j).1 w‖ ^ 2 ≤
          ∑ x ∈ Finset.univ.erase i₀, ‖(TF.col i₀ κ.1 x).1 w‖ ^ 2 :=
        Finset.single_le_sum (f := fun x => ‖(TF.col i₀ κ.1 x).1 w‖ ^ 2) (fun _ _ => by positivity)
          (Finset.mem_erase.2 ⟨hj, Finset.mem_univ j⟩)
      have h0 : ‖(TF.col i₀ κ.1 j).1 w‖ ^ 2 ≤ 0 := by
        have := hone w
        linarith
      have h1 : ‖(TF.col i₀ κ.1 j).1 w‖ = 0 := by
        have h2 := sq_nonneg ‖(TF.col i₀ κ.1 j).1 w‖
        exact pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm h0 h2)
      exact norm_eq_zero.1 h1
    have hst : κ.1 ∈ stab 𝔸[k] ({i₀} : Set ι) := by
      refine mem_stab_of_inv_col κ.1 i₀ fun j hj => ?_
      rw [← col_apply]
      exact Prod.ext (hinf j hj) (hfin j hj)
    exact hκO ⟨κ, hst, 1, mem_interior_iff_mem_nhds.2 hU, (mul_one κ).symm⟩
  obtain ⟨n, hn⟩ := hex
  refine ⟨n ! * M₀, 1 / ((n : ℝ) + 1), hne n, Dvd.intro_left _ rfl, by positivity, fun κ h1 h2 => ?_⟩
  obtain ⟨p, hp, u, hu, e⟩ := hn (show κ ∈ C n from ⟨h1, fun w => (h2 w).le⟩)
  exact ⟨p, hp, u, interior_subset hu, e⟩

end GlobalTheory.CompanionTheory.RgEisSupp
