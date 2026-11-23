import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrobeniusSplitPrimeDatum
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.HthPlace
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.HlayPlace
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.RootOfUnityEqOneOfCloseResidue
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PlaceBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsSign

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V
open scoped Pointwise

private theorem uf_pow {Γ : Type} [Group Γ] {H : Subgroup Γ} (h : commutator Γ ≤ H) {l a b : ℕ} (hi : H.index = l ^ a)
    (hab : a ≤ b) (t : Γ) : t ^ l ^ b ∈ H := by
  haveI : H.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hc : g * n * g⁻¹ * n⁻¹ ∈ H :=
      h (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top n))
    have := H.mul_mem hc hn
    simpa [mul_assoc] using this
  have h1 := H.pow_index_mem (t ^ l ^ (b - a))
  rw [hi, ← pow_mul, ← pow_add, Nat.sub_add_cancel hab] at h1
  exact h1

private theorem uf_comm {Γ : Type} [Group Γ] {H : Subgroup Γ} (hi : H.index = 2) : commutator Γ ≤ H := by
  rw [commutator_def, Subgroup.commutator_le]
  intro a _ b _
  rw [commutatorElement_def, mul_assoc (a * b), Subgroup.mul_mem_iff_of_index_two hi,
    Subgroup.mul_mem_iff_of_index_two hi, Subgroup.mul_mem_iff_of_index_two hi, inv_mem_iff, inv_mem_iff]

private theorem uf_frob {k : Type} [Field k] (l : ℕ) [Fact l.Prime] [CharP k l] {x : kˣ} {a : ℕ} (h : x ^ l ^ a = 1) :
    x = 1 := by
  have h1 : ((x : k) - 1) ^ l ^ a = 0 := by
    rw [sub_pow_char_pow, one_pow, ← Units.val_pow_eq_pow_val, h, Units.val_one, sub_self]
  exact Units.ext (sub_eq_zero.1 (pow_eq_zero_iff (pow_ne_zero a (Fact.out : l.Prime).ne_zero) |>.1 h1))

private theorem uf_neg {k : Type} [Field k] (l : ℕ) [Fact l.Prime] [CharP k l] (hl : l ≠ 2) : (-1 : kˣ) ≠ 1 := by
  intro h
  have h1 : (-1 : k) = 1 := by simpa using congrArg Units.val h
  have h2 : ((2 : ℕ) : k) = 0 := by
    rw [Nat.cast_ofNat, ← sub_eq_zero.2 h1.symm]
    ring
  rw [CharP.cast_eq_zero_iff k l] at h2
  exact hl ((Nat.prime_dvd_prime_iff_eq (Fact.out : l.Prime) Nat.prime_two).1 h2)

section

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O]
  [CharP (ResidueField O) l]

private theorem uf_om {s : G ℚ Ω} (h : cycMod ℚ Ω l 1 s = -1) : omO Ω l O s = -1 := by
  simp [omO, GC.cycF, h]

private theorem omega_eq_one_of_cyclotomic_one {s : G ℚ Ω} (h : cycMod ℚ Ω l 1 s = 1) : omO Ω l O s = 1 := by
  simp [omO, GC.cycF, h]

private theorem uf_cc {σ : G ℚ Ω} (h : IsCC σ) : cycMod ℚ Ω l 1 σ = -1 := by
  obtain ⟨j, hj⟩ := h
  have hc : IsConjOm (σ : Ω ≃+* Ω) := ⟨j, hj⟩
  have h1 := IsConjOm.cyc (E := ℚ) (l := l) hc
  have hr : MulSemiringAction.toRingAut (G ℚ Ω) Ω σ = (σ : Ω ≃+* Ω) := RingEquiv.ext fun _ => rfl
  have h2 : cycZ ℚ Ω l σ = -1 := by
    show cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G ℚ Ω) Ω σ) = -1
    rw [hr, h1]
  show Units.map _ (cycZ ℚ Ω l σ) = -1
  rw [h2]
  ext
  simp

omit [IsAlgClosure ℚ Ω] in
private theorem uf_sq {σ : G ℚ Ω} (h : IsCC σ) : σ ^ 2 = 1 := by
  obtain ⟨j, hj⟩ := h
  ext x
  apply j.injective
  rw [pow_two, AlgEquiv.mul_apply, hj, hj, AlgEquiv.one_apply]
  simp

end

theorem UpperTheory.V.Fr.ufacts :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [CharP (ResidueField O) l] (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* Oˣ) (σ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ) (Hb : Subgroup (G ℚ Ω)), Gen l η Ψ σ B M Hb → ∀ (H₀ : Subgroup (G ℚ Ω)) (w : ℕ), FrobeniusSplitPrimeDatum η M H₀ → FrobeniusWitnessPrime l η Ψ M w → ∀ m, UFacts l η Ψ M m (Upl l Hb H₀ w m) := by
  intro Ω _ _ _ l _ O _ _ _ η Ψ σ B M Hb hG H₀ w h0 hW m
  have hl : l.Prime := Fact.out
  obtain ⟨thO, thA, thI, thU, thR⟩ := hth Ω l w hW.prime hW.one
  obtain ⟨lyO, lyA, lyI, lyK, lyU, lyR⟩ := hlay Ω l m hG.odd
  obtain ⟨pb1, pb2, pb3, pb4, pb5, pb6, pb7, pb8, pb9, pb10⟩ := ML.placeBasic Ω
  obtain ⟨a, ha⟩ := hG.Hb_idx
  have hU : Upl l Hb H₀ w m = H₀ ⊓ Hth Ω l w ⊓ Hb ⊓ Hlay Ω l m := rfl
  have hoddpow : ∀ (H : Subgroup (G ℚ Ω)) (b : ℕ), commutator (G ℚ Ω) ≤ H → H.index = l ^ b →
      ∀ τ : G ℚ Ω, τ ^ 2 = 1 → τ ∈ H := by
    intro H b hc hi τ hτ
    have h1 := uf_pow hc hi le_rfl τ
    obtain ⟨k, hk⟩ : Odd (l ^ b) := (hl.odd_of_ne_two hG.odd).pow
    rw [hk, pow_succ, pow_mul, hτ, one_pow, one_mul] at h1
    exact h1
  have hMl : ∀ B' : ValuationSubring Ω, B'.valuation (l : Ω) < 1 → B'.valuation (M : Ω) < 1 := by
    intro B' hB'
    obtain ⟨c, hc⟩ := hG.l_dvd
    have := (pb3 B' l c).2 (Or.inl hB')
    simpa [ML.Over, hc] using this
  have hσom : omO Ω l O σ = -1 := uf_om l (uf_cc l hG.cc)
  have hσb := hG.even
  have hneg : (-1 : (ResidueField O)ˣ) ≠ 1 := uf_neg l hG.odd
  obtain ⟨s', hs'η, hs'om, hs'b⟩ : ∃ s', η s' = 1 ∧ omO Ω l O s' = -1 ∧ barChar O Ψ s' = 1 := by
    obtain ⟨t, ⟨ht1, ht2⟩, ht3⟩ := SetLike.not_le_iff_exists.1 hG.g4
    by_cases hησ : η σ = 1
    · exact ⟨σ, hησ, hσom, hσb⟩
    · refine ⟨t * σ, ?_, ?_, ?_⟩
      · have e1 := (Int.units_eq_one_or (η t)).resolve_left ht3
        have e2 := (Int.units_eq_one_or (η σ)).resolve_left hησ
        rw [map_mul, e1, e2]
        rfl
      · rw [map_mul, MonoidHom.mem_ker.1 ht1, hσom, one_mul]
      · rw [map_mul, MonoidHom.mem_ker.1 ht2, hσb, one_mul]
  rw [hU]
  refine ⟨?isOpen, ?ab, ?real, ?unr, ?split, ?teich, ?mu, ?deg, ?f2b, ?f2c, ?f3, ?f5⟩
  case isOpen =>
    simp only [Subgroup.coe_inf]
    exact ((h0.isOpen.inter thO).inter hG.Hb_open).inter lyO
  case ab => exact le_inf (le_inf (le_inf (uf_comm h0.idx) thA) hG.Hb_ab) lyA
  case real =>
    intro τ hτ
    have h2 := uf_sq hτ
    exact ⟨⟨⟨h0.real τ hτ, hoddpow _ 1 thA (by rw [thI, pow_one]) τ h2⟩, hoddpow _ a hG.Hb_ab ha τ h2⟩,
      hoddpow _ m lyA lyI τ h2⟩
  case unr =>
    intro B' s hs
    by_cases hB' : B'.valuation (M : Ω) < 1
    · have h1 : s ∈ Dec B' ⊓ H₀ := ⟨Ine_le_Dec B' hs.1, hs.2.1.1.1⟩
      rw [h0.loc B' hB'] at h1
      exact h1.2
    · obtain ⟨c, hc1, -⟩ := hG.cyc
      have hno : ∀ e : ℕ, ¬ ML.Over B' (M ^ e) := by
        intro e
        induction e with
        | zero => simp [ML.Over]
        | succ e ih =>
          rw [pow_succ, pb3]
          rintro (h | h)
          · exact ih h
          · exact hB' h
      exact MonoidHom.mem_ker.2 (hc1 s fun ζ hζ => pb5 B' (M ^ c) (hno c) hs.1 ζ hζ)
  case split =>
    intro B' hB' s hs
    have h1 : s ∈ Dec B' ⊓ H₀ := ⟨hs.1, hs.2.1.1.1⟩
    rw [h0.loc B' hB'] at h1
    exact h1.2
  case teich =>
    intro B' hB' s hs hb
    exact hG.teich B' hB' s ⟨hs.1, hs.2.1.2⟩ hb
  case mu =>
    intro B' hB'
    have hm1 : (-1 : (ZMod (l ^ (m + 1)))ˣ) ∈ Subgroup.map (cycMod ℚ Ω l (m + 1)) (Ine B') := by
      rw [(lyR B' hB').2 (m + 1)]
      trivial
    obtain ⟨s, hsI, hs⟩ := Subgroup.mem_map.1 hm1
    have hsLay : s ∈ Hlay Ω l m := by
      show (cycMod ℚ Ω l (m + 1) ^ (l - 1)) s = 1
      rw [MonoidHom.pow_apply, hs]
      exact (hl.even_sub_one hG.odd).neg_one_pow
    have hsH0 : s ∈ H₀ := by
      have h1 : s ∈ Dec B' ⊓ η.ker := ⟨Ine_le_Dec B' hsI, hG.η_l B' hB' hsI⟩
      rw [← h0.loc B' (hMl B' hB')] at h1
      exact h1.2
    have hlw : l ≠ w := by
      intro hlw
      have h1 := hW.one
      rw [← hlw] at h1
      unfold Nat.ModEq at h1
      rw [Nat.mod_self, Nat.mod_eq_of_lt hl.one_lt] at h1
      exact zero_ne_one h1
    have hsTh : s ∈ Hth Ω l w :=
      thU B' (pb4 B' l w ((Nat.coprime_primes hl hW.prime).2 hlw) hB') hsI
    refine ⟨s, ⟨hsI, ⟨⟨⟨hsH0, hsTh⟩, hG.Hb_l B' hB' hsI⟩, hsLay⟩⟩, fun h1 => ?_⟩
    have h2 : s ∈ Hlay Ω l m ⊓ (cycMod ℚ Ω l 1).ker := ⟨hsLay, h1⟩
    rw [lyK, MonoidHom.mem_ker, hs] at h2
    haveI : Fact (2 < l ^ (m + 1)) := ⟨by
      calc 2 < l := lt_of_le_of_ne hl.two_le (Ne.symm hG.odd)
        _ = l ^ 1 := (pow_one l).symm
        _ ≤ l ^ (m + 1) := Nat.pow_le_pow_right hl.pos (by omega)⟩
    exact ZMod.neg_one_ne_one (congrArg Units.val h2)
  case deg =>
    intro B' hB'
    have hfi : (H₀ ⊓ Hth Ω l w ⊓ Hb ⊓ Hlay Ω l m).index ≠ 0 := by
      refine Subgroup.index_inf_ne_zero (Subgroup.index_inf_ne_zero (Subgroup.index_inf_ne_zero ?_ ?_) ?_) ?_
      · rw [h0.idx]; norm_num
      · rw [thI]; exact hl.ne_zero
      · rw [ha]; exact pow_ne_zero _ hl.ne_zero
      · rw [lyI]; exact pow_ne_zero _ hl.ne_zero
    have hrel : ∀ H : Subgroup (G ℚ Ω), H.index ≠ 0 → ∀ L : Subgroup (G ℚ Ω), H.relIndex L ≠ 0 :=
      fun H hH L => Subgroup.relIndex_ne_zero_trans (K := ⊤) (by rw [Subgroup.relIndex_top_right]; exact hH)
        (by rw [Subgroup.relIndex_top_left]; exact one_ne_zero)
    have hlayi : (Hlay Ω l m).index ≠ 0 := by rw [lyI]; exact pow_ne_zero _ hl.ne_zero
    calc l ^ m = (Hlay Ω l m).relIndex (Ine B') := ((lyR B' hB').1).symm
      _ ≤ (Hlay Ω l m).relIndex (Dec B') :=
        Subgroup.relIndex_le_of_le_right (Ine_le_Dec B') (hrel _ hlayi _)
      _ ≤ (H₀ ⊓ Hth Ω l w ⊓ Hb ⊓ Hlay Ω l m).relIndex (Dec B') :=
        Subgroup.relIndex_le_of_le_left inf_le_right (hrel _ hfi _)
  case f2b =>
    intro j _
    by_contra hc
    push_neg at hc
    have h1 := (l15 l η Ψ σ B M Hb hG H₀ w h0 hW m 1 j).2.2 (fun s hs => by rw [zpow_one]; exact hc s hs) s'
      (MonoidHom.mem_ker.2 hs'η)
    rw [zpow_one, hs'om, hs'b, one_zpow, mul_one] at h1
    exact hneg h1
  case f2c =>
    intro j _
    by_contra hc
    push_neg at hc
    have h1 := (l15 l η Ψ σ B M Hb hG H₀ w h0 hW m 1 j).2.2 (fun s hs => by rw [zpow_one]; exact hc s hs) s'
      (MonoidHom.mem_ker.2 hs'η)
    rw [zpow_one, hs'om, hs'b, one_zpow, mul_one] at h1
    exact hneg h1
  case f3 =>
    intro B' hB'
    obtain ⟨t, htD, htη, htb⟩ := hG.g5
    obtain ⟨g, hg⟩ := pb8 B B' l hl hG.over_l hB'
    have ht'D : g * t * g⁻¹ ∈ Dec B' := by
      rw [hg, (pb10 B g).1]
      convert htD using 1
      group
    have ht'η : η (g * t * g⁻¹) = 1 := by
      rw [map_mul, map_mul, map_inv, htη, mul_one, mul_inv_cancel]
    have ht'b : barChar O Ψ (g * t * g⁻¹) = barChar O Ψ t := by
      rw [map_mul, map_mul, map_inv, mul_comm (barChar O Ψ g), mul_assoc, mul_inv_cancel, mul_one]
    have ht'H0 : g * t * g⁻¹ ∈ H₀ := by
      have h1 : g * t * g⁻¹ ∈ Dec B' ⊓ η.ker := ⟨ht'D, ht'η⟩
      rw [← h0.loc B' (hMl B' hB')] at h1
      exact h1.2
    refine ⟨(g * t * g⁻¹) ^ l ^ (a + m + 1), ⟨pow_mem ht'D _, ⟨⟨⟨pow_mem ht'H0 _,
      uf_pow thA (by rw [thI, pow_one]) (by omega) _⟩, uf_pow hG.Hb_ab ha (by omega) _⟩,
      uf_pow lyA lyI (by omega) _⟩⟩, fun h1 => htb ?_⟩
    rw [← ht'b]
    apply uf_frob l (a := a + m + 1)
    rw [map_pow, ← pow_mul, mul_comm, pow_mul] at h1
    exact h1
  case f5 =>
    rintro ⟨j, hj⟩
    have h1 := (l15 l η Ψ σ B M Hb hG H₀ w h0 hW m 1 (-j)).2.2
      (fun s hs => by rw [zpow_one, hj s hs, ← zpow_add, add_neg_cancel, zpow_zero]) s' (MonoidHom.mem_ker.2 hs'η)
    rw [zpow_one, hs'om, hs'b, one_zpow, mul_one] at h1
    exact hneg h1
