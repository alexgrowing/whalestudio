import Mathlib

noncomputable def UpperTheory.Reformulated.B.PlacewiseToOutsideS.cubeSign :
    {ι : Type} → [LinearOrder ι] → Finset ι → ι → ℤ :=
    fun {ι : Type} [LinearOrder ι] (t : Finset ι) (i : ι) ↦ (-1 : ℤ) ^ {x ∈ t | x < i}.card

noncomputable def UpperTheory.Reformulated.B.PlacewiseToOutsideS.wd :
    {k : Type} →
      [inst : Field k] →
        {ι : Type} →
          [LinearOrder ι] →
            {E : Type} →
              [inst_2 : AddCommGroup E] →
                [inst_3 : _root_.Module k E] → (ι → Module.End k E) → (Finset ι → E) →ₗ[k] Finset ι → E :=
    fun {k : Type} [Field k] {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E] [_root_.Module k E]
        (w : ι → Module.End k E) ↦
      LinearMap.pi fun (t : Finset ι) ↦ ∑ i ∈ t, UpperTheory.Reformulated.B.PlacewiseToOutsideS.cubeSign t i • w i ∘ₗ LinearMap.proj (t.erase i)

private theorem UpperTheory.Reformulated.B.PlacewiseToOutsideS.sign_lt {ι : Type} [LinearOrder ι] (t : Finset ι) (i j : ι)
    (hi : i ∈ t) (hij : i < j) :
    UpperTheory.Reformulated.B.PlacewiseToOutsideS.cubeSign t i * UpperTheory.Reformulated.B.PlacewiseToOutsideS.cubeSign (t.erase i) j =
      -(UpperTheory.Reformulated.B.PlacewiseToOutsideS.cubeSign t j * UpperTheory.Reformulated.B.PlacewiseToOutsideS.cubeSign (t.erase j) i) := by
  have h1 : (t.erase j).filter (fun x => x < i) = t.filter (fun x => x < i) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨_, h⟩, h'⟩
      exact ⟨h, h'⟩
    · rintro ⟨h, h'⟩
      exact ⟨⟨(h'.trans hij).ne, h⟩, h'⟩
  have h2 : (t.filter (fun x => x < j)).card = ((t.erase i).filter (fun x => x < j)).card + 1 := by
    rw [Finset.filter_erase, Finset.card_erase_add_one]
    exact Finset.mem_filter.2 ⟨hi, hij⟩
  simp only [UpperTheory.Reformulated.B.PlacewiseToOutsideS.cubeSign]
  rw [h1, h2, pow_succ]
  ring

private theorem UpperTheory.Reformulated.B.PlacewiseToOutsideS.sign_ne {ι : Type} [LinearOrder ι] (t : Finset ι) (i j : ι)
    (hi : i ∈ t) (hj : j ∈ t) (hij : i ≠ j) :
    UpperTheory.Reformulated.B.PlacewiseToOutsideS.cubeSign t i * UpperTheory.Reformulated.B.PlacewiseToOutsideS.cubeSign (t.erase i) j =
      -(UpperTheory.Reformulated.B.PlacewiseToOutsideS.cubeSign t j * UpperTheory.Reformulated.B.PlacewiseToOutsideS.cubeSign (t.erase j) i) := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact UpperTheory.Reformulated.B.PlacewiseToOutsideS.sign_lt t i j hi h
  · rw [UpperTheory.Reformulated.B.PlacewiseToOutsideS.sign_lt t j i hj h, neg_neg]

private theorem UpperTheory.Reformulated.B.PlacewiseToOutsideS.wd_apply {σ E : Type} [LinearOrder σ] [AddCommGroup E]
    [_root_.Module ℂ E] (w : σ → Module.End ℂ E) (c : Finset σ → E) (t : Finset σ) :
    UpperTheory.Reformulated.B.PlacewiseToOutsideS.wd w c t = ∑ i ∈ t, UpperTheory.Reformulated.B.PlacewiseToOutsideS.cubeSign t i • w i (c (t.erase i)) := by
  simp [UpperTheory.Reformulated.B.PlacewiseToOutsideS.wd, LinearMap.sum_apply]

theorem UpperTheory.Reformulated.B.PlacewiseToOutsideS.wd_wd :
    ∀ {σ E : Type} [inst : LinearOrder σ] [inst_1 : AddCommGroup E] [inst_2 : _root_.Module ℂ E] (w : σ → Module.End ℂ E),
      (∀ (i j : σ), Commute (w i) (w j)) →
        ∀ (c : Finset σ → E),
          (UpperTheory.Reformulated.B.PlacewiseToOutsideS.wd w : (Finset σ → E) → Finset σ → E) ((UpperTheory.Reformulated.B.PlacewiseToOutsideS.wd w : (Finset σ → E) → Finset σ → E) c) =
            (0 : Finset σ → E) := by
  intro σ E _ _ _ w hw c
  funext t
  rw [UpperTheory.Reformulated.B.PlacewiseToOutsideS.wd_apply, Pi.zero_apply]
  simp only [UpperTheory.Reformulated.B.PlacewiseToOutsideS.wd_apply, map_sum, map_zsmul, Finset.smul_sum, smul_smul]
  set f : σ → σ → E := fun i j =>
    (UpperTheory.Reformulated.B.PlacewiseToOutsideS.cubeSign t i * UpperTheory.Reformulated.B.PlacewiseToOutsideS.cubeSign (t.erase i) j) •
      w i (w j (c ((t.erase i).erase j))) with hf
  change ∑ i ∈ t, ∑ j ∈ t.erase i, f i j = 0
  have hanti : ∀ i ∈ t, ∀ j ∈ t.erase i, f j i = - f i j := by
    intro i hi j hj
    obtain ⟨hne, hj⟩ := Finset.mem_erase.1 hj
    simp only [hf]
    rw [UpperTheory.Reformulated.B.PlacewiseToOutsideS.sign_ne t j i hj hi hne, neg_smul, Finset.erase_right_comm,
      ← Module.End.mul_apply, (hw j i).eq, Module.End.mul_apply]
  have hswap : ∑ i ∈ t, ∑ j ∈ t.erase i, f i j = ∑ j ∈ t, ∑ i ∈ t.erase j, f i j := by
    apply Finset.sum_comm'
    intro x y
    simp only [Finset.mem_erase]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h2.symm, h1⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h2, h1.symm, h3⟩
  have hneg : ∑ j ∈ t, ∑ i ∈ t.erase j, f i j = -∑ i ∈ t, ∑ j ∈ t.erase i, f i j := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j hj => hanti i hi j hj
  have h2 : (2 : ℂ) • ∑ i ∈ t, ∑ j ∈ t.erase i, f i j = 0 := by
    rw [two_smul]
    exact add_eq_zero_iff_eq_neg.2 (hswap.trans hneg)
  exact (smul_eq_zero.1 h2).resolve_left two_ne_zero
