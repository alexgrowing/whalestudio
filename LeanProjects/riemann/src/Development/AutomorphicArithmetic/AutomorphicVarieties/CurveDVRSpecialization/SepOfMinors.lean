import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne

namespace UpperTheory.V.Pr

open Matrix Polynomial

section

variable {κ : Type} [Field κ]

private lemma exists_weight {ι : Type} [Finite ι] (x : ι → κˣ) (hx : ∀ i, ∀ m : ℕ, 0 < m → x i ^ m ≠ 1) :
    ∃ v : Additive κˣ →+ ℚ, ∀ i, v (Additive.ofMul (x i)) ≠ 0 := by
  classical
  have hne : ∀ i, (LocalizedModule.mk (Additive.ofMul (x i)) 1 :
      LocalizedModule (nonZeroDivisors ℤ) (Additive κˣ)) ≠ 0 := by
    intro i h
    rw [← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq] at h
    obtain ⟨⟨c, hc⟩, hc0⟩ := h
    have hc' : c ≠ 0 := nonZeroDivisors.ne_zero hc
    simp only [one_smul, smul_zero] at hc0
    rw [Submonoid.smul_def] at hc0
    simp only at hc0
    rw [← ofMul_zpow] at hc0
    have h1 : x i ^ c = 1 := by
      have := congrArg Additive.toMul hc0
      simpa using this
    rcases Int.natAbs_eq c with h | h
    · apply hx i c.natAbs (Int.natAbs_pos.mpr hc')
      rw [h, zpow_natCast] at h1
      exact h1
    · apply hx i c.natAbs (Int.natAbs_pos.mpr hc')
      rw [h, _root_.zpow_neg, inv_eq_one, zpow_natCast] at h1
      exact h1
  haveI : Infinite (FractionRing ℤ) :=
    Infinite.of_injective (algebraMap ℤ (FractionRing ℤ)) (IsFractionRing.injective ℤ _)
  obtain ⟨f, hf⟩ := Module.exists_dual_forall_apply_ne_zero (K := FractionRing ℤ)
    (fun i => (LocalizedModule.mk (Additive.ofMul (x i)) 1 :
      LocalizedModule (nonZeroDivisors ℤ) (Additive κˣ))) hne
  let φ := FractionRing.algEquiv ℤ ℚ
  refine ⟨AddMonoidHom.mk' (fun m => φ (f (LocalizedModule.mk m 1))) ?_, fun i => ?_⟩
  · intro a b
    rw [← map_add, ← map_add]
    congr 2
    rw [LocalizedModule.mk_add_mk, one_smul, one_smul, mul_one]
  · intro h
    apply hf i
    exact (map_eq_zero_iff φ φ.injective).mp h

private def ch (β : κˣ) : ℕ → κ := fun m => (β : κ) ^ m

private lemma ch_mul (β γ : κˣ) : ch (β * γ) = ch β * ch γ := by
  funext m; simp [ch, mul_pow]

private lemma ch_li : LinearIndependent κ (ch : κˣ → ℕ → κ) := by
  have h := (linearIndependent_monoidHom (Multiplicative ℕ) κ).comp
    (fun β : κˣ => powersHom κ (β : κ)) (fun a b hab => Units.ext ((powersHom κ).injective hab))
  exact h

variable (v : κˣ → ℚ)

private def Lt (w : ℚ) : Submodule κ (ℕ → κ) := Submodule.span κ (ch '' {β | v β < w})
private def Le (w : ℚ) : Submodule κ (ℕ → κ) := Submodule.span κ (ch '' {β | v β ≤ w})

variable {v}

private lemma Lt_le_Le (w : ℚ) : Lt v w ≤ Le v w := by
  apply Submodule.span_mono
  exact Set.image_mono fun β (hβ : v β < w) => hβ.le

private lemma Le_le_Lt {w w' : ℚ} (h : w < w') : Le v w ≤ Lt v w' := by
  apply Submodule.span_mono
  exact Set.image_mono fun β (hβ : v β ≤ w) => lt_of_le_of_lt hβ h

private lemma ch_Lt {β : κˣ} {w : ℚ} (h : v β < w) : ch β ∈ Lt v w := Submodule.subset_span ⟨β, h, rfl⟩
private lemma ch_Le {β : κˣ} {w : ℚ} (h : v β ≤ w) : ch β ∈ Le v w := Submodule.subset_span ⟨β, h, rfl⟩

private lemma mul_LeLe (hv : ∀ a b, v (a * b) = v a + v b) {w w' : ℚ} {f g : ℕ → κ} (hf : f ∈ Le v w)
    (hg : g ∈ Le v w') : f * g ∈ Le v (w + w') := by
  have h1 : f * g ∈ Le v w * Le v w' := Submodule.mul_mem_mul hf hg
  rw [Le, Le, Submodule.span_mul_span] at h1
  refine (Submodule.span_le.mpr ?_) h1
  rintro _ ⟨_, ⟨β, hβ, rfl⟩, _, ⟨γ, hγ, rfl⟩, rfl⟩
  refine Submodule.subset_span ⟨β * γ, ?_, ch_mul β γ⟩
  show v (β * γ) ≤ w + w'
  rw [hv]
  exact add_le_add hβ hγ

private lemma mul_LtLe (hv : ∀ a b, v (a * b) = v a + v b) {w w' : ℚ} {f g : ℕ → κ} (hf : f ∈ Lt v w)
    (hg : g ∈ Le v w') : f * g ∈ Lt v (w + w') := by
  have h1 : f * g ∈ Lt v w * Le v w' := Submodule.mul_mem_mul hf hg
  rw [Lt, Le, Submodule.span_mul_span] at h1
  refine (Submodule.span_le.mpr ?_) h1
  rintro _ ⟨_, ⟨β, hβ, rfl⟩, _, ⟨γ, hγ, rfl⟩, rfl⟩
  refine Submodule.subset_span ⟨β * γ, ?_, ch_mul β γ⟩
  show v (β * γ) < w + w'
  rw [hv]
  exact add_lt_add_of_lt_of_le hβ hγ

private def Lead (v : κˣ → ℚ) (f : ℕ → κ) (β : κˣ) : Prop :=
  ∃ c : κ, c ≠ 0 ∧ ∃ g ∈ Lt v (v β), f = c • ch β + g

private lemma Lead.le {f : ℕ → κ} {β : κˣ} (h : Lead v f β) : f ∈ Le v (v β) := by
  obtain ⟨c, -, g, hg, rfl⟩ := h
  exact add_mem (Submodule.smul_mem _ _ (ch_Le le_rfl)) (Lt_le_Le _ hg)

private lemma Lead.add {f g : ℕ → κ} {β : κˣ} (h : Lead v f β) (hg : g ∈ Lt v (v β)) : Lead v (f + g) β := by
  obtain ⟨c, hc, g', hg', rfl⟩ := h
  exact ⟨c, hc, g' + g, add_mem hg' hg, by rw [add_assoc]⟩

private lemma Lead.mul (hv : ∀ a b, v (a * b) = v a + v b) {f g : ℕ → κ} {β γ : κˣ} (h : Lead v f β)
    (h' : Lead v g γ) : Lead v (f * g) (β * γ) := by
  obtain ⟨c, hc, g1, hg1, rfl⟩ := h
  obtain ⟨c', hc', g2, hg2, rfl⟩ := h'
  have hw : v (β * γ) = v β + v γ := hv β γ
  have hb : c • ch β ∈ Le v (v β) := Submodule.smul_mem _ _ (ch_Le le_rfl)
  have hg' : c' • ch γ ∈ Le v (v γ) := Submodule.smul_mem _ _ (ch_Le le_rfl)
  refine ⟨c * c', mul_ne_zero hc hc', (c • ch β) * g2 + g1 * (c' • ch γ) + g1 * g2, ?_, ?_⟩
  · rw [hw]
    refine add_mem (add_mem ?_ ?_) ?_
    · rw [mul_comm, add_comm]
      exact mul_LtLe hv hg2 hb
    · exact mul_LtLe hv hg1 hg'
    · exact mul_LtLe hv hg1 (Lt_le_Le _ hg2)
  · rw [ch_mul]
    funext m
    simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    ring

private lemma Lead.ne {f : ℕ → κ} {β : κˣ} (h : Lead v f β) : ∃ m, f m ≠ 0 := by
  obtain ⟨c, hc, g, hg, rfl⟩ := h
  by_contra hne
  push_neg at hne
  have h0 : c • ch β + g = 0 := funext hne
  have hm : ch β ∈ Lt v (v β) := by
    have h1 : c • ch β ∈ Lt v (v β) := by
      rw [eq_neg_of_add_eq_zero_left h0]
      exact neg_mem hg
    have h2 := Submodule.smul_mem _ c⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h2
  exact ch_li.notMem_span_image (s := {β' | v β' < v β}) (lt_irrefl (v β)) hm

private lemma core2 (hv : ∀ a b, v (a * b) = v a + v b) {α β : κˣ} (h : v β < v α) (a b c : κ) (ha : a ≠ 0) :
    ∃ m : ℕ, (a * (α : κ) ^ m + b * (β : κ) ^ m) ^ 2 - 4 * (c * (α : κ) ^ m * (β : κ) ^ m) ≠ 0 := by
  have h1 : v (α * β) < v (α * α) := by
    rw [hv, hv]
    linarith
  have h2 : v (β * β) < v (α * α) := by
    rw [hv, hv]
    linarith
  have hL : Lead v (a ^ 2 • ch (α * α) + ((2 * a * b - 4 * c) • ch (α * β) + b ^ 2 • ch (β * β)))
      (α * α) :=
    ⟨a ^ 2, pow_ne_zero 2 ha, _,
      add_mem (Submodule.smul_mem _ _ (ch_Lt h1)) (Submodule.smul_mem _ _ (ch_Lt h2)), rfl⟩
  obtain ⟨m, hm⟩ := hL.ne
  refine ⟨m, ?_⟩
  convert hm using 1
  simp only [ch, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Units.val_mul, mul_pow]
  ring

private def disc3 (a b c : κ) : κ := a ^ 2 * b ^ 2 - 4 * b ^ 3 - 4 * a ^ 3 * c + 18 * a * b * c - 27 * c ^ 2

private lemma core3 (hv : ∀ a b, v (a * b) = v a + v b) {α β γ : κˣ} (h : v β < v α) (h' : v γ < v β)
    (a b c p q r d : κ) (ha : a ≠ 0) (hp : p ≠ 0) :
    ∃ m : ℕ, disc3 (a * (α : κ) ^ m + b * (β : κ) ^ m + c * (γ : κ) ^ m)
      (p * (α : κ) ^ m * (β : κ) ^ m + q * (α : κ) ^ m * (γ : κ) ^ m + r * (β : κ) ^ m * (γ : κ) ^ m)
      (d * (α : κ) ^ m * (β : κ) ^ m * (γ : κ) ^ m) ≠ 0 := by
  have hT : v (α * α * (α * β * (α * β))) = 4 * v α + 2 * v β := by
    simp only [hv]
    ring
  have hE1 : Lead v (a • ch α + (b • ch β + c • ch γ)) α :=
    ⟨a, ha, _,
      add_mem (Submodule.smul_mem _ _ (ch_Lt h)) (Submodule.smul_mem _ _ (ch_Lt (h'.trans h))), rfl⟩
  have hE2 : Lead v (p • ch (α * β) + (q • ch (α * γ) + r • ch (β * γ))) (α * β) := by
    refine ⟨p, hp, _, add_mem (Submodule.smul_mem _ _ (ch_Lt ?_)) (Submodule.smul_mem _ _ (ch_Lt ?_)), rfl⟩
    · rw [hv, hv]
      linarith
    · rw [hv, hv]
      linarith
  have hE3 : d • ch (α * β * γ) ∈ Le v (v α + v β + v γ) := by
    refine Submodule.smul_mem _ _ (ch_Le ?_)
    rw [hv, hv]
  have l1 : a • ch α + (b • ch β + c • ch γ) ∈ Le v (v α) := hE1.le
  have l2 : p • ch (α * β) + (q • ch (α * γ) + r • ch (β * γ)) ∈ Le v (v α + v β) := by
    have hl := hE2.le
    rwa [hv] at hl
  set E1 := a • ch α + (b • ch β + c • ch γ) with hE1d
  set E2 := p • ch (α * β) + (q • ch (α * γ) + r • ch (β * γ)) with hE2d
  set E3 := d • ch (α * β * γ) with hE3d
  have r1 : E2 * E2 * E2 ∈ Lt v (v (α * α * (α * β * (α * β)))) := by
    rw [hT]
    exact Le_le_Lt (by linarith) (mul_LeLe hv (mul_LeLe hv l2 l2) l2)
  have r2 : E1 * E1 * E1 * E3 ∈ Lt v (v (α * α * (α * β * (α * β)))) := by
    rw [hT]
    exact Le_le_Lt (by linarith) (mul_LeLe hv (mul_LeLe hv (mul_LeLe hv l1 l1) l1) hE3)
  have r3 : E1 * E2 * E3 ∈ Lt v (v (α * α * (α * β * (α * β)))) := by
    rw [hT]
    exact Le_le_Lt (by linarith) (mul_LeLe hv (mul_LeLe hv l1 l2) hE3)
  have r4 : E3 * E3 ∈ Lt v (v (α * α * (α * β * (α * β)))) := by
    rw [hT]
    exact Le_le_Lt (by linarith) (mul_LeLe hv hE3 hE3)
  have hrest : (-4 : κ) • (E2 * E2 * E2) + ((-4 : κ) • (E1 * E1 * E1 * E3) +
      ((18 : κ) • (E1 * E2 * E3) + (-27 : κ) • (E3 * E3))) ∈ Lt v (v (α * α * (α * β * (α * β)))) :=
    add_mem (Submodule.smul_mem _ _ r1) (add_mem (Submodule.smul_mem _ _ r2)
      (add_mem (Submodule.smul_mem _ _ r3) (Submodule.smul_mem _ _ r4)))
  obtain ⟨m, hm⟩ := (Lead.add (Lead.mul hv (Lead.mul hv hE1 hE1) (Lead.mul hv hE2 hE2)) hrest).ne
  refine ⟨m, ?_⟩
  convert hm using 1
  simp only [hE1d, hE2d, hE3d, disc3, ch, Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul,
    Units.val_mul, mul_pow]
  ring

private lemma core3' (hv : ∀ a b, v (a * b) = v a + v b) {α β γ : κˣ} (h1 : v α ≠ v β) (h2 : v α ≠ v γ)
    (h3 : v β ≠ v γ) (a b c p q r d : κ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hp : p ≠ 0) (hq : q ≠ 0)
    (hr : r ≠ 0) :
    ∃ m : ℕ, disc3 (a * (α : κ) ^ m + b * (β : κ) ^ m + c * (γ : κ) ^ m)
      (p * (α : κ) ^ m * (β : κ) ^ m + q * (α : κ) ^ m * (γ : κ) ^ m + r * (β : κ) ^ m * (γ : κ) ^ m)
      (d * (α : κ) ^ m * (β : κ) ^ m * (γ : κ) ^ m) ≠ 0 := by
  rcases lt_or_gt_of_ne h1 with g1 | g1 <;> rcases lt_or_gt_of_ne h2 with g2 | g2 <;>
    rcases lt_or_gt_of_ne h3 with g3 | g3
  · obtain ⟨m, hm⟩ := core3 hv g3 g1 c b a r q p d hc hr
    exact ⟨m, by convert hm using 2 <;> ring⟩
  · obtain ⟨m, hm⟩ := core3 hv g3 g2 b c a r p q d hb hr
    exact ⟨m, by convert hm using 2 <;> ring⟩
  · linarith
  · obtain ⟨m, hm⟩ := core3 hv g1 g2 b a c p r q d hb hp
    exact ⟨m, by convert hm using 2 <;> ring⟩
  · obtain ⟨m, hm⟩ := core3 hv g2 g1 c a b q r p d hc hq
    exact ⟨m, by convert hm using 2 <;> ring⟩
  · linarith
  · obtain ⟨m, hm⟩ := core3 hv g2 g3 a c b q p r d ha hq
    exact ⟨m, by convert hm using 2 <;> ring⟩
  · exact core3 hv g1 g3 a b c p q r d ha hp

private lemma sep2 (a b : κ) (h : a ^ 2 - 4 * b ≠ 0) : (X ^ 2 - C a * X + C b : κ[X]).Separable := by
  have hd : derivative (X ^ 2 - C a * X + C b : κ[X]) = 2 * X - C a := by
    simp [derivative_pow]; norm_num; rfl
  rw [separable_def, hd]
  have hu : C (a ^ 2 - 4 * b)⁻¹ * (C a ^ 2 - 4 * C b) = (1 : κ[X]) := by
    rw [← C_1, ← inv_mul_cancel₀ h]; simp [map_ofNat]
  refine ⟨C (a ^ 2 - 4 * b)⁻¹ * (-4), C (a ^ 2 - 4 * b)⁻¹ * (2 * X - C a), ?_⟩
  linear_combination hu

private lemma sep3 (a b c : κ) (h : disc3 a b c ≠ 0) :
    (X ^ 3 - C a * X ^ 2 + C b * X - C c : κ[X]).Separable := by
  have h2 : (C 2 : κ[X]) = 2 := map_ofNat C 2
  have hd : derivative (X ^ 3 - C a * X ^ 2 + C b * X - C c : κ[X]) =
      3 * X ^ 2 - 2 * C a * X + C b := by
    simp [h2]
    ring
  have h4 : (C 4 : κ[X]) = 4 := map_ofNat C 4
  have h18 : (C 18 : κ[X]) = 18 := map_ofNat C 18
  have h27 : (C 27 : κ[X]) = 27 := map_ofNat C 27
  have hD : C (disc3 a b c) = C a ^ 2 * C b ^ 2 - 4 * C b ^ 3 - 4 * C a ^ 3 * C c +
      18 * C a * C b * C c - 27 * C c ^ 2 := by
    simp [disc3, h4, h18, h27]
  have hu : C (disc3 a b c)⁻¹ * C (disc3 a b c) = 1 := by
    rw [← C_mul, inv_mul_cancel₀ h, C_1]
  rw [hD] at hu
  unfold Polynomial.Separable
  rw [hd]
  refine ⟨-C (disc3 a b c)⁻¹ * ((6 * C a ^ 2 - 18 * C b) * X +
      (-4 * C a ^ 3 + 15 * C a * C b - 27 * C c)),
    -C (disc3 a b c)⁻¹ * ((6 * C b - 2 * C a ^ 2) * X ^ 2 +
      (-7 * C a * C b + 9 * C c + 2 * C a ^ 3) * X + (4 * C b ^ 2 - C a ^ 2 * C b - 3 * C a * C c)),
    ?_⟩
  linear_combination hu

private lemma charpoly3 (M : Matrix (Fin 3) (Fin 3) κ) :
    M.charpoly = X ^ 3 - C (M 0 0 + M 1 1 + M 2 2) * X ^ 2 +
      C ((M 0 0 * M 1 1 - M 0 1 * M 1 0) + (M 0 0 * M 2 2 - M 0 2 * M 2 0) + (M 1 1 * M 2 2 - M 1 2 * M 2 1)) * X
      - C M.det := by
  rw [Matrix.charpoly, det_fin_three, det_fin_three]
  simp [charmatrix_apply]
  ring

private lemma minor_ne {n k : ℕ} (y : Matrix (Fin n) (Fin n) κ)
    (hy : ∀ S : Finset (Fin n), (y.submatrix (Subtype.val : S → Fin n) Subtype.val).det ≠ 0)
    (f : Fin k → Fin n) (hf : Function.Injective f) : (y.submatrix f f).det ≠ 0 := by
  classical
  let S : Finset (Fin n) := Finset.univ.map ⟨f, hf⟩
  let e : Fin k ≃ S := Equiv.ofBijective (fun i => ⟨f i, Finset.mem_map_of_mem ⟨f, hf⟩ (Finset.mem_univ i)⟩)
    ⟨fun i j hij => hf (congrArg Subtype.val hij), fun x => by
      obtain ⟨i, -, hi⟩ := Finset.mem_map.mp x.2
      exact ⟨i, Subtype.ext hi⟩⟩
  have hM : y.submatrix f f = (y.submatrix (Subtype.val : S → Fin n) Subtype.val).submatrix e e := by
    ext i j
    rfl
  rw [hM, Matrix.det_submatrix_equiv_self]
  exact hy S

private lemma weights {n : ℕ} (α : Fin n → κˣ) (h : FreeRatios α) :
    ∃ v : κˣ → ℚ, (∀ a b, v (a * b) = v a + v b) ∧ ∀ i j, i ≠ j → v (α i) ≠ v (α j) := by
  obtain ⟨w, hw⟩ := exists_weight (ι := {p : Fin n × Fin n // p.1 ≠ p.2})
    (fun p => α p.1.1 / α p.1.2) (by
      rintro ⟨⟨i, j⟩, hij⟩ m hm h1
      apply h i j hij m hm
      rw [div_pow, div_eq_one] at h1
      exact h1)
  refine ⟨fun u => w (Additive.ofMul u), fun a b => ?_, fun i j hij => ?_⟩
  · show w (Additive.ofMul (a * b)) = w (Additive.ofMul a) + w (Additive.ofMul b)
    rw [ofMul_mul, map_add]
  · intro he
    have he' : w (Additive.ofMul (α i)) = w (Additive.ofMul (α j)) := he
    apply hw ⟨(i, j), hij⟩
    simp only
    rw [ofMul_div, map_sub, he', sub_self]

end

end UpperTheory.V.Pr

open Matrix Polynomial in
theorem UpperTheory.V.Pr.sepOfMinors :
    UpperTheory.V.Pr.SepOfMinors := by
  intro κ _ n hn y α hα hy
  obtain ⟨v, hv, hvne⟩ := weights α hα
  have hM : ∀ m : ℕ, y * (Matrix.diagonal fun i => (α i : κ)) ^ m =
      Matrix.of fun i j => y i j * (α j : κ) ^ m := by
    intro m
    ext i j
    rw [Matrix.diagonal_pow, Matrix.mul_diagonal]
    simp
  have h1 : ∀ i : Fin n, y i i ≠ 0 := by
    intro i
    have h := minor_ne y hy ![i] (Function.injective_of_subsingleton _)
    rw [Matrix.det_fin_one] at h
    simpa using h
  have hdet : y.det ≠ 0 := by
    have h := minor_ne y hy id Function.injective_id
    rwa [Matrix.submatrix_id_id] at h
  interval_cases n
  · exact ⟨0, by rw [Matrix.charpoly_isEmpty]; exact separable_one⟩
  · refine ⟨0, ?_⟩
    rw [Matrix.charpoly, Matrix.det_fin_one, Matrix.charmatrix_apply_eq]
    exact separable_X_sub_C
  · have key : ∃ m : ℕ, (y 0 0 * (α 0 : κ) ^ m + y 1 1 * (α 1 : κ) ^ m) ^ 2 -
        4 * (y.det * (α 0 : κ) ^ m * (α 1 : κ) ^ m) ≠ 0 := by
      rcases lt_or_gt_of_ne (hvne 0 1 (by decide)) with h | h
      · obtain ⟨m, hm⟩ := core2 hv h (y 1 1) (y 0 0) y.det (h1 1)
        exact ⟨m, by convert hm using 1; ring⟩
      · exact core2 hv h (y 0 0) (y 1 1) y.det (h1 0)
    obtain ⟨m, hm⟩ := key
    refine ⟨m, ?_⟩
    rw [hM, Matrix.charpoly_fin_two]
    apply sep2
    convert hm using 1
    rw [Matrix.trace_fin_two, Matrix.det_fin_two, Matrix.det_fin_two]
    simp only [Matrix.of_apply]
    ring
  · have hp01 : y 0 0 * y 1 1 - y 0 1 * y 1 0 ≠ 0 := by
      have h := minor_ne y hy ![(0 : Fin 3), 1] (by decide)
      rw [Matrix.det_fin_two] at h
      simpa using h
    have hp02 : y 0 0 * y 2 2 - y 0 2 * y 2 0 ≠ 0 := by
      have h := minor_ne y hy ![(0 : Fin 3), 2] (by decide)
      rw [Matrix.det_fin_two] at h
      simpa using h
    have hp12 : y 1 1 * y 2 2 - y 1 2 * y 2 1 ≠ 0 := by
      have h := minor_ne y hy ![(1 : Fin 3), 2] (by decide)
      rw [Matrix.det_fin_two] at h
      simpa using h
    obtain ⟨m, hm⟩ := core3' hv (hvne 0 1 (by decide)) (hvne 0 2 (by decide)) (hvne 1 2 (by decide))
      (y 0 0) (y 1 1) (y 2 2) _ _ _ y.det (h1 0) (h1 1) (h1 2) hp01 hp02 hp12
    refine ⟨m, ?_⟩
    rw [hM, charpoly3]
    apply sep3
    convert hm using 2
    all_goals
      simp only [Matrix.of_apply, Matrix.det_fin_three]
      try ring
