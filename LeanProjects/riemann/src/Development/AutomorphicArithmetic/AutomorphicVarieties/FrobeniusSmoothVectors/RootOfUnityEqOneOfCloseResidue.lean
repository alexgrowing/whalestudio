import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrobeniusSplitPrimeDatum
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

private theorem aux_one {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {m : ℕ} (hm : m ≠ 0) {ζ : Ω}
    (h : ζ ^ m = 1) : A.valuation ζ = 1 := by
  have h1 : A.valuation ζ ^ m = 1 := by rw [← map_pow, h, map_one]
  exact (pow_eq_one_iff_left hm).1 h1

private theorem vg_ne {Γ : Type} [LinearOrderedCommGroupWithZero Γ] : (0 : Γ) < 1 := by
  refine lt_of_le_of_ne zero_le' fun h => ?_
  obtain ⟨x, y, hxy⟩ := (GroupWithZero.toNontrivial (G₀ := Γ)).exists_pair_ne
  exact hxy (by rw [← mul_one x, ← mul_one y, ← h, mul_zero, mul_zero])

private theorem power_bounds_of_between {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {η : Ω} (h1 : A.valuation η = 1)
    (h : A.valuation (η - 1) < 1) (i : ℕ) : A.valuation (1 - η ^ i) < 1 := by
  induction i with
  | zero => rw [pow_zero, sub_self, map_zero]; exact vg_ne
  | succ i ih =>
    have e : 1 - η ^ (i + 1) = η * (1 - η ^ i) - (η - 1) := by ring
    rw [e]
    refine A.valuation.map_sub_lt ?_ h
    rw [map_mul, h1, one_mul]; exact ih

private theorem root_of_unity_eq_one_of_close_residue {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {m : ℕ} (hm : m ≠ 0)
    (hv : ¬ A.valuation (m : Ω) < 1) {η : Ω} (hη : η ^ m = 1) (h : A.valuation (η - 1) < 1) : η = 1 := by
  by_contra hne
  apply hv
  have hs : ∑ i ∈ Finset.range m, η ^ i = 0 := by
    have := mul_geom_sum η m
    rw [hη, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)
  have e : (m : Ω) = ∑ i ∈ Finset.range m, (1 - η ^ i) := by
    rw [Finset.sum_sub_distrib, hs]; simp
  rw [e]
  have h10 : (1 : A.ValueGroup) ≠ 0 := vg_ne.ne'
  exact A.valuation.map_sum_lt h10 fun i _ => power_bounds_of_between A (aux_one A hm hη) h i

private theorem ine_fix {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω) {m : ℕ} (hm : m ≠ 0)
    (hv : ¬ A.valuation (m : Ω) < 1) {g : G ℚ Ω} (hg : g ∈ Ine (F := ℚ) A) (ζ : Ω) (hζ : ζ ^ m = 1) : g ζ = ζ := by
  have h1 := aux_one A hm hζ
  have h0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hm] at hζ
    exact zero_ne_one hζ
  have e : g ζ / ζ - 1 = (g ζ - ζ) / ζ := by field_simp
  have : g ζ / ζ = 1 := by
    refine root_of_unity_eq_one_of_close_residue A hm hv (by rw [div_pow, ← map_pow, hζ, map_one, div_one]) ?_
    rw [e, map_div₀, h1, div_one]; exact hg.2 ζ h1.le
  exact (div_eq_one_iff_eq h0).1 this

private theorem val_nat_le {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (n : ℕ) : A.valuation (n : Ω) ≤ 1 :=
  (A.valuation_le_one_iff _).2 (natCast_mem A n)

private theorem act_pow {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {w : ℕ} (hw : w ≠ 0) (n : ℕ) (s : G ℚ Ω) :
    ∃ a : ℕ, ∀ ζ : Ω, ζ ^ w = 1 → (s ^ n) ζ = ζ ^ a ^ n := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : NeZero w := ⟨hw⟩
  haveI : NeZero (w : Ω) := ⟨Nat.cast_ne_zero.2 hw⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω w
  obtain ⟨a, -, ha⟩ := hz.eq_pow_of_pow_eq_one (ξ := s z) (by rw [← map_pow, hz.pow_eq_one, map_one])
  have h1 : ∀ ζ : Ω, ζ ^ w = 1 → s ζ = ζ ^ a := fun ζ h => by
    obtain ⟨b, -, rfl⟩ := hz.eq_pow_of_pow_eq_one h
    rw [map_pow, ← ha, ← pow_mul, ← pow_mul, mul_comm]
  refine ⟨a, fun ζ h => ?_⟩
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, h1 ζ h, ← pow_mul, pow_succ']

private theorem pow_mem_Upl {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime]
    {Hb H₀ : Subgroup (G ℚ Ω)} {w : ℕ} (hw : w ≠ 0) (hab : commutator (G ℚ Ω) ≤ Hb) (hidx : ∃ a : ℕ, Hb.index = l ^ a) (m : ℕ) :
    ∃ N : ℕ, ∀ s ∈ H₀, s ^ l ^ N ∈ Upl l Hb H₀ w m := by
  obtain ⟨a, ha⟩ := hidx
  haveI : Hb.Normal := ⟨fun n hn g => by
    have : g * n * g⁻¹ = g * n * g⁻¹ * n⁻¹ * n := by group
    rw [this]
    exact Hb.mul_mem (hab (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top n))) hn⟩
  refine ⟨1 + a + m, fun s hs => ⟨⟨⟨H₀.pow_mem hs _, ?_⟩, ?_⟩, ?_⟩⟩
  · have : s ^ l ∈ Hth Ω l w := ⟨act_pow hw l s, by
      show ∃ a : ℕ, ∀ ζ : Ω, ζ ^ w = 1 → (s ^ l)⁻¹ ζ = ζ ^ a ^ l
      rw [← inv_pow]; exact act_pow hw l s⁻¹⟩
    rw [add_assoc, pow_add, pow_one, pow_mul]
    exact Subgroup.pow_mem _ this _
  · have : s ^ l ^ a ∈ Hb := ha ▸ Hb.pow_index_mem s
    rw [add_comm 1 a, add_assoc, pow_add, pow_mul]
    exact Subgroup.pow_mem _ this _
  · have : s ^ l ^ m ∈ Hlay Ω l m := by
      have hl : l.Prime := Fact.out
      haveI : NeZero (l ^ (m + 1)) := ⟨pow_ne_zero _ hl.ne_zero⟩
      show (cycMod ℚ Ω l (m + 1) ^ (l - 1)) (s ^ l ^ m) = 1
      rw [MonoidHom.pow_apply, map_pow, ← pow_mul, ← Nat.totient_prime_pow_succ hl, ← ZMod.card_units_eq_totient]
      exact pow_card_eq_one
    rw [add_comm (1 + a) m, pow_add, pow_mul]
    exact Subgroup.pow_mem _ this _

private theorem core {Γ k : Type} [Group Γ] [Field k] (l : ℕ) [Fact l.Prime] [CharP k l] (κ : Γ →* kˣ)
    (U H₀ E : Subgroup Γ) (hU : ∃ N : ℕ, ∀ s ∈ H₀, s ^ l ^ N ∈ U) (h2 : H₀.index = 2) (t : Γ) (ht : t ∉ H₀) (htE : t ∈ E)
    (hκ : κ t = 1) (h : ∀ s ∈ U ⊓ E, κ s = 1) : ∀ s ∈ E, κ s = 1 := by
  obtain ⟨N, hN⟩ := hU
  have h0 : ∀ s ∈ H₀, s ∈ E → κ s = 1 := fun s hs hE => by
    have h1 := h _ ⟨hN s hs, E.pow_mem hE _⟩
    rw [map_pow] at h1
    have h3 : (κ s : k) ^ l ^ N = 1 := by rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
    have h4 : ((κ s : k) - 1) ^ l ^ N = 0 := by rw [sub_pow_char_pow, h3, one_pow, sub_self]
    exact Units.ext (sub_eq_zero.1 (pow_eq_zero_iff (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) |>.1 h4))
  intro s hs
  by_cases hH : s ∈ H₀
  · exact h0 s hH hs
  · have := h0 (s * t) ((Subgroup.mul_mem_iff_of_index_two h2).2 (by simp [hH, ht])) (E.mul_mem hs htE)
    rwa [map_mul, hκ, mul_one] at this

theorem UpperTheory.V.Fr.l15 :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [CharP (ResidueField O) l] (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* Oˣ) (σ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ) (Hb : Subgroup (G ℚ Ω)), Gen l η Ψ σ B M Hb → ∀ (H₀ : Subgroup (G ℚ Ω)) (w : ℕ), FrobeniusSplitPrimeDatum η M H₀ → FrobeniusWitnessPrime l η Ψ M w → ∀ (m : ℕ) (i j : ℤ), ((∀ s ∈ Upl l Hb H₀ w m, omO Ω l O s ^ i * barChar O Ψ s ^ j = 1) → ∀ s, omO Ω l O s ^ i * barChar O Ψ s ^ j = 1) ∧ ((∀ s ∈ Upl l Hb H₀ w m, omO Ω l O s ^ i * barChar O Ψ s ^ j = etaO O η s) → ∀ s, omO Ω l O s ^ i * barChar O Ψ s ^ j = etaO O η s) ∧ ((∀ s ∈ Upl l Hb H₀ w m ⊓ η.ker, omO Ω l O s ^ i * barChar O Ψ s ^ j = 1) → ∀ s ∈ η.ker, omO Ω l O s ^ i * barChar O Ψ s ^ j = 1) := by
  intro Ω _ _ _ l hl O _ _ _ η Ψ σ B M Hb hG H₀ w h0 hW m i j
  have hU := pow_mem_Upl l (H₀ := H₀) hW.prime.ne_zero hG.Hb_ab hG.Hb_idx m
  obtain ⟨A, hA, hI⟩ := h0.ram
  obtain ⟨t, ht, htH⟩ := SetLike.not_le_iff_exists.1 hI
  obtain ⟨a, ka, kb⟩ := hG.cyc
  have hM1 : A.valuation (M : Ω) = 1 := le_antisymm (val_nat_le A M) (not_lt.1 hA)
  have hMa : ¬ A.valuation ((M ^ a : ℕ) : Ω) < 1 := by
    rw [Nat.cast_pow, map_pow, hM1, one_pow]; exact lt_irrefl _
  have hfix := ine_fix A (pow_ne_zero a hG.M_ne) hMa ht
  have hη : η t = 1 := ka t hfix
  have hΨ : barChar O Ψ t = 1 := kb t hfix
  have hlv : ¬ A.valuation (l : Ω) < 1 := fun h => hA (by
    obtain ⟨c, rfl⟩ := hG.l_dvd
    rw [Nat.cast_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (val_nat_le A c)) h)
  have hω : omO Ω l O t = 1 := by
    have h1 : cycZ ℚ Ω l t = 1 := (UpperTheory.V.Base.places ℚ Ω l A).2.2.2 hlv ht
    simp [GC.cycF, cycMod, h1]
  have he : etaO O η t = 1 := by simp [hη]
  let κ : G ℚ Ω →* (ResidueField O)ˣ := omO Ω l O ^ i * barChar O Ψ ^ j
  have hκ : ∀ s, κ s = omO Ω l O s ^ i * barChar O Ψ s ^ j := fun s => by simp [κ]
  have hκt : κ t = 1 := by rw [hκ, hω, hΨ]; simp
  refine ⟨fun h s => ?_, fun h s => ?_, fun h s hs => ?_⟩
  · rw [← hκ]
    exact core l κ _ H₀ ⊤ hU h0.idx t htH trivial hκt (fun s hs => by rw [hκ]; exact h s hs.1) s trivial
  · have := core l (κ * (etaO O η)⁻¹) _ H₀ ⊤ hU h0.idx t htH trivial
      (by rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hκt, he]; simp)
      (fun s hs => by rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hκ, h s hs.1, mul_inv_cancel]) s trivial
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hκ] at this
    exact mul_inv_eq_one.1 this
  · rw [← hκ]
    exact core l κ _ H₀ η.ker hU h0.idx t htH hη hκt (fun s hs => by rw [hκ]; exact h s hs) s hs
