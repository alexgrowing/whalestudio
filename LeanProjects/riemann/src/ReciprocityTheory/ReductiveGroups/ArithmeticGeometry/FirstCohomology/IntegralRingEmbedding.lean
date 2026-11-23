import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.NakayamaChar

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.H1.IntegralRingEmbedding

open Module

variable {F : Type} [Field F] (v : AddValuation F (WithTop ℚ))

lemma wt_zero_of_add {a b : WithTop ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a + b = 0) : a = 0 := by
  refine le_antisymm ?_ ha
  rw [← h]
  exact le_add_of_nonneg_right hb

lemma wt_inv_nonneg {a b : WithTop ℚ} (h : a + b = 0) (ha : a < 0) : 0 ≤ b := by
  have ha' : a ≠ ⊤ := ne_top_of_lt ha
  lift a to ℚ using ha'
  induction b using WithTop.recTopCoe with
  | top => exact le_top
  | coe q =>
    have h1 : (a : ℚ) + q = 0 := by exact_mod_cast h
    have h2 : (a : ℚ) < 0 := by exact_mod_cast ha
    exact_mod_cast (show (0 : ℚ) ≤ q by linarith)

def intRing : ValuationSubring F where
  carrier := {a | 0 ≤ v a}
  mul_mem' := fun {a b} ha hb => by
    show 0 ≤ v (a * b)
    rw [AddValuation.map_mul]; exact add_nonneg ha hb
  one_mem' := by show 0 ≤ v 1; rw [AddValuation.map_one]
  add_mem' := fun {a b} ha hb => le_trans (le_min ha hb) (AddValuation.map_add v a b)
  zero_mem' := by show 0 ≤ v 0; rw [AddValuation.map_zero]; exact le_top
  neg_mem' := fun {a} ha => by show 0 ≤ v (-a); rw [AddValuation.map_neg]; exact ha
  mem_or_inv_mem' := by
    intro a
    by_cases ha : 0 ≤ v a
    · exact Or.inl ha
    · right
      push Not at ha
      have ha0 : a ≠ 0 := by
        rintro rfl; rw [AddValuation.map_zero] at ha; exact absurd ha (not_lt.mpr le_top)
      show 0 ≤ v a⁻¹
      have : v a + v a⁻¹ = 0 := by
        rw [← AddValuation.map_mul, mul_inv_cancel₀ ha0, AddValuation.map_one]
      exact wt_inv_nonneg this ha

lemma mem_intRing {a : F} : a ∈ intRing v ↔ 0 ≤ v a := Iff.rfl

lemma isUnit_of_val_zero (x : intRing v) (hx : v (x : F) = 0) : IsUnit x := by
  have hx0 : (x : F) ≠ 0 := by
    intro h0
    rw [h0, AddValuation.map_zero] at hx
    simp at hx
  have hinv : 0 ≤ v (x : F)⁻¹ := by
    have h1 : v (x : F) + v (x : F)⁻¹ = 0 := by
      rw [← AddValuation.map_mul, mul_inv_cancel₀ hx0, AddValuation.map_one]
    rw [hx, zero_add] at h1
    rw [h1]
  refine isUnit_iff_exists_inv.2 ⟨⟨(x : F)⁻¹, (mem_intRing v).2 hinv⟩, ?_⟩
  apply Subtype.ext
  exact mul_inv_cancel₀ hx0

lemma val_pos_of_mem_max (x : intRing v) (hx : x ∈ IsLocalRing.maximalIdeal (intRing v)) :
    0 < v (x : F) := by
  have hnu : ¬ IsUnit x := (IsLocalRing.mem_maximalIdeal x).1 hx
  have h0 : 0 ≤ v (x : F) := (mem_intRing v).1 x.2
  exact lt_of_le_of_ne h0 (fun h => hnu (isUnit_of_val_zero v x h.symm))

lemma val_root_unity {N : ℕ} (hN : 1 ≤ N) {z : F} (hz : z ^ N = 1) : v z = 0 := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hz
    exact zero_ne_one hz
  have h1 : v (z ^ N) = N • v z := AddValuation.map_pow v z N
  rw [hz, AddValuation.map_one] at h1
  have h2 : v z + v z⁻¹ = 0 := by
    rw [← AddValuation.map_mul, mul_inv_cancel₀ hz0, AddValuation.map_one]
  generalize v z = w at h1 h2 ⊢
  induction w using WithTop.recTopCoe with
  | top => simp at h2
  | coe q =>
    have h3 : ((N • q : ℚ) : WithTop ℚ) = 0 := by
      rw [WithTop.coe_nsmul]
      exact h1.symm
    have h4 : N • q = 0 := by exact_mod_cast h3
    rw [nsmul_eq_mul] at h4
    have h5 : q = 0 := (mul_eq_zero.1 h4).resolve_left (by exact_mod_cast (show N ≠ 0 by omega))
    simp [h5]

lemma val_sub_roots {N : ℕ} (hN : 1 ≤ N) (hvN : v (N : F) = 0) {z z' : F} (hz : z ^ N = 1)
    (hz' : z' ^ N = 1) (hne : z ≠ z') : v (z - z') = 0 := by
  have hvz := val_root_unity v hN hz
  have hvz' := val_root_unity v hN hz'
  have hnn : 0 ≤ v (z - z') :=
    le_trans (le_of_eq (by rw [hvz, hvz', min_self])) (AddValuation.map_sub v z z')
  by_contra hne0
  obtain ⟨Z, rfl⟩ : ∃ Z : intRing v, (Z : F) = z := ⟨⟨z, (mem_intRing v).2 (le_of_eq hvz.symm)⟩, rfl⟩
  obtain ⟨Z', rfl⟩ : ∃ Z' : intRing v, (Z' : F) = z' :=
    ⟨⟨z', (mem_intRing v).2 (le_of_eq hvz'.symm)⟩, rfl⟩
  have hZN : Z ^ N = 1 := Subtype.ext (by simpa using hz)
  have hZ'N : Z' ^ N = 1 := Subtype.ext (by simpa using hz')
  have hmax : Z - Z' ∈ IsLocalRing.maximalIdeal (intRing v) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨w, hw⟩ := hu.exists_right_inv
    have h3 : ((Z : F) - Z') * (w : F) = 1 := by
      have := congrArg Subtype.val hw
      simpa using this
    have h1 : v ((Z : F) - Z') + v (w : F) = 0 := by
      rw [← AddValuation.map_mul, h3, AddValuation.map_one]
    exact hne0 (wt_zero_of_add hnn ((mem_intRing v).1 w.2) h1)
  have hres : IsLocalRing.residue (intRing v) Z = IsLocalRing.residue (intRing v) Z' := by
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact hmax
  have hsum0 : ∑ i ∈ Finset.range N, Z ^ i * Z' ^ (N - 1 - i) = 0 := by
    have h1 := geom_sum₂_mul Z Z' N
    rw [hZN, hZ'N, sub_self] at h1
    have hne' : Z - Z' ≠ 0 := by
      intro h
      apply hne
      rw [sub_eq_zero] at h
      rw [h]
    exact (mul_eq_zero.1 h1).resolve_right hne'
  have hmap := congrArg (IsLocalRing.residue (intRing v)) hsum0
  rw [map_sum, map_zero] at hmap
  simp only [map_mul, map_pow, ← hres] at hmap
  rw [geom_sum₂_self] at hmap
  have hres0 : IsLocalRing.residue (intRing v) Z ≠ 0 :=
    ((isUnit_of_val_zero v Z hvz).map (IsLocalRing.residue (intRing v))).ne_zero
  have hN0 : ((N : ℕ) : IsLocalRing.ResidueField (intRing v)) = 0 :=
    (mul_eq_zero.1 hmap).resolve_right (pow_ne_zero _ hres0)
  rw [← map_natCast (IsLocalRing.residue (intRing v)) N, IsLocalRing.residue_eq_zero_iff] at hN0
  have hpos := val_pos_of_mem_max v (N : intRing v) hN0
  have hc : ((N : intRing v) : F) = (N : F) := by simp
  rw [hc, hvN] at hpos
  exact lt_irrefl _ hpos

section Core

variable {W : Type} [AddCommGroup W] [Module F W] {n : ℕ} (b : Fin n → W)

def emb : (Fin n → intRing v) →+ W where
  toFun c := ∑ i, ((c i : intRing v) : F) • b i
  map_zero' := by simp
  map_add' c d := by simp [add_smul, Finset.sum_add_distrib]

theorem span_of_eigen (UU Pos : W → Prop) (hb : LinearIndependent F b)
    (hUU : ∀ s, UU s ↔ ∃ c : Fin n → F, (∀ i, 0 ≤ v (c i)) ∧ s = ∑ i, c i • b i)
    (hPos : ∀ s, UU s → ∀ ζ : F, ∀ s', 0 < v ζ → UU s' → s = ζ • s' → Pos s)
    (hπ : ∃ π : F, 0 < v π)
    {ι Γ : Type} [Fintype ι] (hcard : Fintype.card ι = n) (sv : ι → W)
    (hsv : ∀ i, UU (sv i)) (hsvp : ∀ i, ¬ Pos (sv i))
    (T : Γ → W →ₗ[F] W) (hT : ∀ γ s, UU s → UU (T γ s))
    {N : ℕ} (hN : 1 ≤ N) (hvN : v (N : F) = 0) (χ : ι → Γ → F)
    (hχN : ∀ i γ, χ i γ ^ N = 1) (heig : ∀ i γ, T γ (sv i) = χ i γ • sv i)
    (hsep : ∀ i j, i ≠ j → ∃ γ, χ i γ ≠ χ j γ) :
    ∀ s, UU s → ∃ a : ι → F, (∀ i, 0 ≤ v (a i)) ∧ s = ∑ i, a i • sv i := by
  classical
  have hUU0 : UU 0 := (hUU 0).2 ⟨0, fun i => by simp, by simp⟩
  have hUUsub : ∀ s t, UU s → UU t → UU (s - t) := by
    intro s t hs ht
    obtain ⟨c, hc, rfl⟩ := (hUU s).1 hs
    obtain ⟨d, hd, rfl⟩ := (hUU _).1 ht
    refine (hUU _).2 ⟨c - d, fun i => ?_, ?_⟩
    · exact le_trans (le_min (hc i) (hd i)) (AddValuation.map_sub v (c i) (d i))
    · simp [sub_smul, Finset.sum_sub_distrib]
  have hUUsmul : ∀ r s, 0 ≤ v r → UU s → UU (r • s) := by
    intro r s hr hs
    obtain ⟨c, hc, rfl⟩ := (hUU s).1 hs
    refine (hUU _).2 ⟨fun i => r * c i, fun i => ?_, ?_⟩
    · show 0 ≤ v (r * c i)
      rw [AddValuation.map_mul]
      exact add_nonneg hr (hc i)
    · simp [Finset.smul_sum, mul_smul]
  have hsv0 : ∀ i, sv i ≠ 0 := by
    intro i h
    apply hsvp i
    exact hPos (sv i) (hsv i) 0 0 (by simp) hUU0 (by rw [h, zero_smul])
  have hχv : ∀ i γ, v (χ i γ) = 0 := fun i γ => val_root_unity v hN (hχN i γ)
  have hχd : ∀ i j γ, χ i γ ≠ χ j γ → v (χ i γ - χ j γ) = 0 :=
    fun i j γ h => val_sub_roots v hN hvN (hχN i γ) (hχN j γ) h

  have hred : ∀ (S : Finset ι) (a : ι → F) (j : ι) (γ : Γ), j ∈ S →
      T γ (∑ i ∈ S, a i • sv i) - χ j γ • ∑ i ∈ S, a i • sv i =
        ∑ i ∈ S.erase j, (a i * (χ i γ - χ j γ)) • sv i := by
    intro S a j γ hj
    rw [map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
    have hterm : ∀ i, T γ (a i • sv i) - χ j γ • (a i • sv i) = (a i * (χ i γ - χ j γ)) • sv i := by
      intro i
      rw [map_smul, heig, smul_smul, smul_smul, ← sub_smul]
      congr 1
      ring
    simp_rw [hterm]
    rw [← Finset.sum_erase_add _ _ hj, sub_self, mul_zero, zero_smul, add_zero]

  have indep : ∀ S : Finset ι, ∀ a : ι → F, ∑ i ∈ S, a i • sv i = 0 → ∀ k ∈ S, a k = 0 := by
    intro S
    induction S using Finset.strongInduction
    rename_i S ih
    intro a ha k hk
    by_cases hex : ∃ j ∈ S, j ≠ k
    · obtain ⟨j, hj, hjk⟩ := hex
      obtain ⟨γ, hγ⟩ := hsep k j (Ne.symm hjk)
      have hz : ∑ i ∈ S.erase j, (a i * (χ i γ - χ j γ)) • sv i = 0 := by
        rw [← hred S a j γ hj, ha, map_zero, smul_zero, sub_zero]
      have h1 : a k * (χ k γ - χ j γ) = 0 :=
        ih (S.erase j) (Finset.erase_ssubset hj) (fun i => a i * (χ i γ - χ j γ)) hz k
          (Finset.mem_erase.2 ⟨Ne.symm hjk, hk⟩)
      exact (mul_eq_zero.1 h1).resolve_right (sub_ne_zero.2 hγ)
    · rw [Finset.sum_eq_single k (fun j hj hjk => absurd ⟨j, hj, hjk⟩ hex)
        (fun h => absurd hk h)] at ha
      exact (smul_eq_zero.1 ha).resolve_right (hsv0 k)

  have key : ∀ S : Finset ι, ∀ a : ι → F, UU (∑ i ∈ S, a i • sv i) → ∀ k ∈ S, 0 ≤ v (a k) := by
    intro S
    induction S using Finset.strongInduction
    rename_i S ih
    intro a ha k hk
    by_cases hex : ∃ j ∈ S, j ≠ k
    · obtain ⟨j, hj, hjk⟩ := hex
      obtain ⟨γ, hγ⟩ := hsep k j (Ne.symm hjk)
      have hmem : UU (∑ i ∈ S.erase j, (a i * (χ i γ - χ j γ)) • sv i) := by
        rw [← hred S a j γ hj]
        exact hUUsub _ _ (hT γ _ ha) (hUUsmul _ _ (le_of_eq (hχv j γ).symm) ha)
      have h1 : 0 ≤ v (a k * (χ k γ - χ j γ)) :=
        ih (S.erase j) (Finset.erase_ssubset hj) (fun i => a i * (χ i γ - χ j γ)) hmem k
          (Finset.mem_erase.2 ⟨Ne.symm hjk, hk⟩)
      rw [AddValuation.map_mul, hχd k j γ hγ, add_zero] at h1
      exact h1
    · rw [Finset.sum_eq_single k (fun j hj hjk => absurd ⟨j, hj, hjk⟩ hex)
        (fun h => absurd hk h)] at ha
      by_contra hneg
      have hneg' : v (a k) < 0 := not_le.1 hneg
      have hak : a k ≠ 0 := by
        intro h0
        rw [h0, AddValuation.map_zero] at hneg'
        exact absurd hneg' (not_lt.2 le_top)
      have hsum : v (a k) + v (a k)⁻¹ = 0 := by
        rw [← AddValuation.map_mul, mul_inv_cancel₀ hak, AddValuation.map_one]
      have hpos : 0 < v (a k)⁻¹ := by
        refine lt_of_le_of_ne (wt_inv_nonneg hsum hneg') ?_
        intro h0
        rw [← h0, add_zero] at hsum
        rw [hsum] at hneg'
        exact lt_irrefl _ hneg'
      exact hsvp k (hPos (sv k) (hsv k) (a k)⁻¹ (a k • sv k) hpos ha
        (by rw [smul_smul, inv_mul_cancel₀ hak, one_smul]))
  have hli : LinearIndependent F sv := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    exact indep Finset.univ g hg i (Finset.mem_univ i)
  have hmemb : ∀ s, UU s → s ∈ Submodule.span F (Set.range b) := by
    intro s hs
    obtain ⟨c, -, rfl⟩ := (hUU s).1 hs
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
  haveI : FiniteDimensional F (Submodule.span F (Set.range b)) :=
    FiniteDimensional.span_of_finite F (Set.finite_range b)
  have hspan : Submodule.span F (Set.range sv) = Submodule.span F (Set.range b) := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hmemb _ (hsv i)
    · rw [finrank_span_eq_card hli, finrank_span_eq_card hb, hcard, Fintype.card_fin]
  intro s hs
  have hs' : s ∈ Submodule.span F (Set.range sv) := by
    rw [hspan]
    exact hmemb s hs
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun F).1 hs'
  refine ⟨a, fun i => key Finset.univ a ?_ i (Finset.mem_univ i), ha.symm⟩
  rw [ha]
  exact hs

end Core

end ReciprocityTheory.ChartRestriction.G.H1.IntegralRingEmbedding
