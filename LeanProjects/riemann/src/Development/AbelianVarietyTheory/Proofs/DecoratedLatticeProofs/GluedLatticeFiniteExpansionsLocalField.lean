import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsClopenIsCompactQLat

open GlobalTheory.FinPl GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData ValuativeRel IsLocalRing Matrix
open GlobalTheory.LastSteps (exists_dual dual_ext finsum_split finsum_ofDual exists_lifts lifts_unique cosetInd_eq
  inDual_of_lifts term_ne_zero term_zero datum_eq lastPair_hasVal)

noncomputable section

namespace GlobalTheory.GluedExp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type}

theorem card_dual (L : Submodule 𝒪[k] (n → k)) [Fintype n] [L.IsLattice k] :
    Nat.card (Module.Dual 𝓀[k] (Red L)) = resCard k ^ Fintype.card n := by
  rw [Module.natCard_eq_pow_finrank (K := 𝓀[k]), Subspace.dual_finrank_eq, ← Module.natCard_eq_pow_finrank,
    Red.card_eq]

open Classical in

theorem finsum_char (χ : AddChar 𝓀[k] ℂ) (hχ : χ ≠ 1) (L : Submodule 𝒪[k] (n → k)) [Fintype n] [L.IsLattice k]
    (z : Red L) : ∑ᶠ f : Module.Dual 𝓀[k] (Red L), χ (-f z) =
      if z = 0 then ((resCard k : ℂ) ^ Fintype.card n) else 0 := by
  classical
  letI := Fintype.ofFinite (Module.Dual 𝓀[k] (Red L))
  rw [finsum_eq_sum_of_fintype]
  split_ifs with hz
  · subst hz
    simp only [map_zero, neg_zero, AddChar.map_zero_eq_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one]
    rw [Fintype.card_eq_nat_card, card_dual]
    push_cast
    rfl
  · obtain ⟨f₁, hf₁⟩ : ∃ f₁ : Module.Dual 𝓀[k] (Red L), f₁ z ≠ 0 := by
      by_contra h
      push_neg at h
      exact hz ((Module.forall_dual_apply_eq_zero_iff 𝓀[k] z).1 h)
    obtain ⟨a, ha⟩ : ∃ a, χ a ≠ 1 := by
      by_contra h
      push_neg at h
      exact hχ (by ext a; rw [h a, AddChar.one_apply])
    set g : Module.Dual 𝓀[k] (Red L) := (-(a * (f₁ z)⁻¹)) • f₁
    have hg : g z = -a := by simp [g, hf₁]
    set S := ∑ f : Module.Dual 𝓀[k] (Red L), χ (-f z)
    have hS : S = χ a * S := by
      conv_lhs => rw [show S = ∑ f : Module.Dual 𝓀[k] (Red L), χ (-(f + g) z) from
        (Fintype.sum_equiv (Equiv.addRight g) _ _ fun _ => rfl).symm]
      simp only [LinearMap.add_apply, hg, neg_add, neg_neg, AddChar.map_add_eq_mul, S, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    have : (1 - χ a) * S = 0 := by rw [sub_mul, one_mul, ← hS, sub_self]
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 (Ne.symm ha))

end GlobalTheory.GluedExp

namespace GlobalTheory.GluedExp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type}
  [Fintype n] [Fintype n']

theorem card_ne_zero (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] : ((resCard k : ℂ) ^ Fintype.card n) ≠ 0 := by
  have h : Nat.card (Module.Dual 𝓀[k] (Red L)) ≠ 0 := Nat.card_pos.ne'
  rw [card_dual] at h
  exact_mod_cast h

omit [Fintype n] in

theorem withCol_split (x : Matrix n (n' ⊕ Fin 1) k) :
    withCol (x.submatrix id Sum.inl) (fun i => x i (Sum.inr 0)) = x := by
  ext i (j | j)
  · rfl
  · fin_cases j
    rfl

def imgE (q : Unif k) (P : Pair k n') {L : Submodule 𝒪[k] (n → k)} {x₀ : Matrix n n' k}
    (h0 : ∀ z ∈ P.ker, x₀ *ᵥ z ∈ L) : L :=
  ⟨x₀ *ᵥ (q.1 • P.vec), h0 _ (Pair.smul_mem_ker q.mem_max P.hasVal_vec.mem)⟩

theorem term_pos (q : Unif k) (χ : AddChar 𝓀[k] ℂ) (P : Pair k n') {L : Submodule 𝒪[k] (n → k)}
    {x₀ : Matrix n n' k} (h0 : ∀ z ∈ P.ker, x₀ *ᵥ z ∈ L) (f : Module.Dual 𝓀[k] (Red L)) :
    term q χ 1 P L f x₀ = χ (-f (Red.mk L (imgE q P h0))) := by
  rw [term, dif_pos h0, Units.val_one, one_mul]
  rfl

theorem term_neg (q : Unif k) (χ : AddChar 𝓀[k] ℂ) (P : Pair k n') {L : Submodule 𝒪[k] (n → k)}
    {x₀ : Matrix n n' k} (h0 : ¬ ∀ z ∈ P.ker, x₀ *ᵥ z ∈ L) (f : Module.Dual 𝓀[k] (Red L)) :
    term q χ 1 P L f x₀ = 0 := by
  rw [term, dif_neg h0]

open Classical in

theorem datum_expand (q : Unif k) (χ : AddChar 𝓀[k] ℂ) (hχ : χ ≠ 1) (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k]
    (P : Pair k n') (x₀ : Matrix n n' k) (y : n → k) :
    datum q P L x₀ y = ((resCard k : ℂ) ^ Fintype.card n)⁻¹ *
      ∑ᶠ f : Module.Dual 𝓀[k] (Red L), term q χ 1 P L f x₀ *
        (if h : y ∈ L then χ (-f (Red.mk L ⟨y, h⟩)) else 0) := by
  classical
  by_cases h0 : ∀ z ∈ P.ker, x₀ *ᵥ z ∈ L
  · by_cases hy : y ∈ L
    · have key : ∀ f : Module.Dual 𝓀[k] (Red L), term q χ 1 P L f x₀ *
          (if h : y ∈ L then χ (-f (Red.mk L ⟨y, h⟩)) else 0) =
          χ (-f (Red.mk L (⟨y, hy⟩ + imgE q P h0))) := fun f => by
        rw [term_pos q χ P h0, dif_pos hy, map_add, map_add, neg_add, AddChar.map_add_eq_mul, mul_comm]
      rw [finsum_congr key, finsum_char χ hχ, Red.mk_eq_zero q]
      have hc : q.inv • ((⟨y, hy⟩ + imgE q P h0 : L) : n → k) = q.inv • y + x₀ *ᵥ P.vec := by
        simp only [imgE, Submodule.coe_add, smul_add, mulVec_smul, q.inv_smul_smul]
      rw [hc, datum]
      split_ifs with h1 h2 h2
      · exact (inv_mul_cancel₀ (card_ne_zero L)).symm
      · exact absurd h1.2 h2
      · exact absurd ⟨h0, h2⟩ h1
      · rw [mul_zero]
    · rw [datum, if_neg, finsum_eq_zero_of_forall_eq_zero fun f => by rw [dif_neg hy, mul_zero], mul_zero]
      rintro ⟨-, h2⟩
      apply hy
      have h3 := sub_mem (L.smul_mem q.1 h2) (h0 _ (Pair.smul_mem_ker q.mem_max P.hasVal_vec.mem))
      rwa [smul_add, q.smul_inv_smul, ← mulVec_smul, add_sub_cancel_right] at h3
  · rw [datum, if_neg fun h => h0 h.1, finsum_eq_zero_of_forall_eq_zero fun f => by rw [term_neg q χ P h0, zero_mul],
      mul_zero]

end GlobalTheory.GluedExp

namespace GlobalTheory.GluedExp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type}
  [Fintype n] [Fintype n']

open Classical in

theorem glued_col (q : Unif k) (χ : AddChar 𝓀[k] ℂ) (hχ : χ ≠ 1) (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k]
    (P : Pair k n') :
    latInd (gluedS q 1 P.ker P.vec) L = ((resCard k : ℂ) ^ Fintype.card n)⁻¹ •
      (tensCol (latInd P.ker L) (vecInd L) +
        ∑ Q ∈ withLat L, tensCol (latInd P.ker Q.ker + mainDatum q χ 1 P Q) (charInd χ Q)) := by
  funext x
  conv_lhs => rw [← withCol_split x]
  rw [← datum_eq, datum_expand q χ hχ, Pi.smul_apply, smul_eq_mul, Pi.add_apply, Finset.sum_apply, finsum_split]
  congr 2
  · rw [term_zero, tensCol, vecInd]
    by_cases hy : (fun i => x i (Sum.inr 0)) ∈ L
    · rw [dif_pos hy, if_pos hy, LinearMap.zero_apply, neg_zero, AddChar.map_zero_eq_one]
    · rw [dif_neg hy, if_neg hy]
  · rw [← finsum_ofDual L (fun Q => tensCol (latInd P.ker Q.ker + mainDatum q χ 1 P Q) (charInd χ Q) x)]
    refine finsum_congr fun f => ?_
    rw [term_ne_zero, tensCol, charInd, vecInd, ofDual_lat]
    by_cases hy : (fun i => x i (Sum.inr 0)) ∈ L
    · rw [dif_pos hy, if_pos hy, mul_one, (ofDual_hasVal L f ⟨_, hy⟩).ev_eq]
    · simp only [dif_neg hy, if_neg hy, mul_zero]

theorem glued_sum (q : Unif k) (χ : AddChar 𝓀[k] ℂ) (hχ : χ ≠ 1) (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k]
    (P : Pair k n') :
    latInd P.ker L + ∑ Q ∈ withLat L, (latInd P.ker Q.ker + mainDatum q χ 1 P Q) =
      ((resCard k : ℂ) ^ Fintype.card n) • latInd P.lat L := by
  classical
  funext x₀
  have hL : latInd P.ker L x₀ + ∑ Q ∈ withLat L, (latInd P.ker Q.ker + mainDatum q χ 1 P Q) x₀ =
      ∑ᶠ f : Module.Dual 𝓀[k] (Red L), term q χ 1 P L f x₀ := by
    rw [finsum_split, term_zero, ← finsum_ofDual L (fun Q => (latInd P.ker Q.ker + mainDatum q χ 1 P Q) x₀)]
    congr 1
    refine finsum_congr fun f => ?_
    rw [term_ne_zero]
  rw [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hL]
  by_cases h0 : ∀ z ∈ P.ker, x₀ *ᵥ z ∈ L
  · rw [finsum_congr (term_pos q χ P h0), finsum_char χ hχ, Red.mk_eq_zero q, latInd]
    have he : q.inv • (imgE q P h0 : n → k) = x₀ *ᵥ P.vec := by
      simp only [imgE, mulVec_smul, q.inv_smul_smul]
    rw [he]
    split_ifs with h1 h2 h2
    · rw [mul_one]
    · refine absurd (fun z hz => ?_) h2
      obtain ⟨s, -, hs⟩ := (Pair.hasVal_iff P.hasVal_vec).1 (P.hasVal_fn ⟨z, hz⟩)
      have := add_mem (h0 _ hs) (L.smul_mem s h1)
      rwa [mulVec_sub, mulVec_smul, sub_add_cancel] at this
    · exact absurd (h2 _ P.hasVal_vec.mem) h1
    · rw [mul_zero]
  · rw [finsum_eq_zero_of_forall_eq_zero (term_neg q χ P h0), latInd,
      if_neg (fun h => h0 fun z hz => h z (P.ker_le hz)), mul_zero]

omit [Fintype n'] in
open Classical in

theorem dualInd_eq (q : Unif k) (L : Submodule 𝒪[k] (n → k)) (η : n → k) :
    dualInd L η = if Lifts L (q.1 • η) 0 then 1 else 0 := by
  refine if_congr ⟨fun h y => ⟨q.1 * ⟨_, h y y.2⟩, ?_, ?_⟩, fun h y hy => ?_⟩ rfl rfl
  · rw [smul_dotProduct]
    rfl
  · rw [map_mul, (residue_eq_zero_iff _).2 q.mem_max, zero_mul, LinearMap.zero_apply]
  · obtain ⟨s, hs, hr⟩ := h ⟨y, hy⟩
    rw [LinearMap.zero_apply] at hr
    obtain ⟨t, rfl⟩ := q.mem_max_iff.1 ((residue_eq_zero_iff s).1 hr)
    rw [smul_dotProduct] at hs
    have : ((t : 𝒪[k]) : k) = η ⬝ᵥ y := mul_left_cancel₀ q.ne_zero hs
    exact this ▸ t.2

omit [Fintype n'] in
open Classical in

theorem cosetInd_pair (q : Unif k) (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k]
    (f : {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0}) (η : n → k) :
    cosetInd q (ofDual L f).lat (ofDual L f).red η = if Lifts L (q.1 • η) f.1 then 1 else 0 := by
  have h : (ofDual L f).red = f.1 := dual_ext fun z => rfl
  show cosetInd q L (ofDual L f).red η = _
  rw [h, cosetInd_eq]

omit [Fintype n'] in
open Classical in

theorem finsum_lifts (q : Unif k) (L : Submodule 𝒪[k] (n → k)) (η : n → k) (A : Module.Dual 𝓀[k] (Red L) → ℂ) :
    ∑ᶠ f : Module.Dual 𝓀[k] (Red L), A f * (if Lifts L (q.1 • η) f then 1 else 0) =
      if h : InDual L (q.1 • η) then A (exists_lifts h).choose else 0 := by
  split_ifs with h
  · rw [finsum_eq_single _ (exists_lifts h).choose fun f hf => by
      rw [if_neg fun h' => hf (lifts_unique h' (exists_lifts h).choose_spec), mul_zero],
      if_pos (exists_lifts h).choose_spec, mul_one]
  · exact finsum_eq_zero_of_forall_eq_zero fun f => by
      rw [if_neg fun h' => h (inDual_of_lifts h'), mul_zero]

omit [Fintype n'] in
open Classical in

theorem coset_total (q : Unif k) (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] (η : n → k) :
    (dualInd L + ∑ Q ∈ withLat L, cosetInd q Q.lat Q.red) η = if InDual L (q.1 • η) then 1 else 0 := by
  have hs := finsum_lifts q L η (fun _ => 1)
  rw [finsum_split] at hs
  simp only [one_mul, dite_eq_ite] at hs
  rw [Pi.add_apply, Finset.sum_apply, dualInd_eq q, ← finsum_ofDual L (fun Q => cosetInd q Q.lat Q.red η)]
  simp only [cosetInd_pair]
  exact hs

end GlobalTheory.GluedExp

namespace GlobalTheory.GluedExp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type}
  [Fintype n] [Fintype n']

theorem glued_row (q : Unif k) (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] (R : Pair k n') :
    latInd L (gluedS q 1 R.ker R.vec) = tensRow (latInd L R.ker) (dualInd L) +
      ∑ Q ∈ withLat L, tensRow (phiOne Q R) (cosetInd q Q.lat Q.red) := by
  classical
  funext x
  set x' : Matrix n' n k := x.submatrix Sum.inl id
  set η : n → k := x (Sum.inr 0)
  let A : Module.Dual 𝓀[k] (Red L) → ℂ := fun f =>
    if ∀ y : L, R.HasVal (x' *ᵥ (y : n → k)) (f (Red.mk L y)) then 1 else 0
  have hR : (tensRow (latInd L R.ker) (dualInd L) + ∑ Q ∈ withLat L, tensRow (phiOne Q R) (cosetInd q Q.lat Q.red)) x =
      ∑ᶠ f, A f * (if Lifts L (q.1 • η) f then 1 else 0) := by
    rw [Pi.add_apply, Finset.sum_apply, finsum_split,
      ← finsum_ofDual L (fun Q => tensRow (phiOne Q R) (cosetInd q Q.lat Q.red) x)]
    congr 1
    · rw [tensRow, dualInd_eq q]
      congr 1
      exact if_congr ⟨fun h y => Pair.mem_ker.1 (h y y.2), fun h y hy => Pair.mem_ker.2 (h ⟨y, hy⟩)⟩ rfl rfl
    · refine finsum_congr fun f => ?_
      rw [tensRow, cosetInd_pair]
      congr 1
      exact if_congr (maps_iff_hasVal.trans ⟨fun h y => h y _ (ofDual_hasVal L f y),
        fun h y a ⟨hy, ha⟩ => ha ▸ h ⟨y, hy⟩⟩) rfl rfl
  have hm : ∀ y : n → k, x *ᵥ y ∈ gluedS q 1 R.ker R.vec ↔
      ∃ s : 𝒪[k], x' *ᵥ y - s • R.vec ∈ R.ker ∧ η ⬝ᵥ y = q.inv * (s : k) := by
    intro y
    rw [← gluedLat_one, mem_gluedLat]
    refine exists_congr fun s => and_congr Iff.rfl ?_
    simp [Fin.forall_fin_one]
    rfl
  have hq : ∀ a : k, (q.1 : k) * (q.inv * a) = a := fun a => by
    rw [Unif.inv, ← mul_assoc, mul_inv_cancel₀ q.ne_zero, one_mul]
  rw [hR, finsum_lifts, latInd]
  by_cases hD : InDual L (q.1 • η)
  · rw [dif_pos hD]
    have hf₀ := (exists_lifts hD).choose_spec
    set f₀ := (exists_lifts hD).choose
    refine if_congr ⟨fun h y => ?_, fun h y hy => ?_⟩ rfl rfl
    · obtain ⟨s, hs, hr⟩ := hf₀ y
      obtain ⟨s', h1, h2⟩ := (hm y).1 (h y y.2)
      have hss : s' = s := Subtype.ext (by
        rw [hs, smul_dotProduct, h2]
        exact (hq _).symm)
      rw [← hr, ← hss]
      exact (Pair.hasVal_iff R.hasVal_vec).2 ⟨s', rfl, h1⟩
    · obtain ⟨s, hs, hr⟩ := hf₀ ⟨y, hy⟩
      refine (hm y).2 ⟨s, ?_, ?_⟩
      · have h3 := h ⟨y, hy⟩
        rw [← hr] at h3
        obtain ⟨t, ht, hker⟩ := (Pair.hasVal_iff R.hasVal_vec).1 h3
        have hts : t - s ∈ maximalIdeal 𝒪[k] := (residue_eq_zero_iff _).1 (by rw [map_sub, ht, sub_self])
        have h4 := add_mem hker (Pair.smul_mem_ker hts R.hasVal_vec.mem)
        convert h4 using 1
        rw [sub_smul]
        abel
      · rw [smul_dotProduct] at hs
        change (s : k) = (q.1 : k) * (η ⬝ᵥ y) at hs
        rw [hs, Unif.inv, ← mul_assoc, inv_mul_cancel₀ q.ne_zero, one_mul]
  · rw [dif_neg hD, if_neg]
    intro h
    apply hD
    intro y hy
    obtain ⟨s, -, h2⟩ := (hm y).1 (h y hy)
    rw [smul_dotProduct, h2]
    change (q.1 : k) * (q.inv * s) ∈ 𝒪[k]
    rw [hq]
    exact s.2

theorem last_ker (L : Submodule 𝒪[k] (n → k)) (L' : Submodule 𝒪[k] (n' → k)) :
    latInd L (lastKer L') = tensRow (latInd L L') (dualInd L) := by
  classical
  funext x
  rw [tensRow, latInd, latInd, dualInd, ite_zero_mul_ite_zero, mul_one]
  exact if_congr ⟨fun h => ⟨fun y hy => (mem_lastKer.1 (h y hy)).1, fun y hy => (mem_lastKer.1 (h y hy)).2⟩,
    fun h y hy => mem_lastKer.2 ⟨h.1 y hy, h.2 y hy⟩⟩ rfl rfl

theorem last_lat (q : Unif k) (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] (L' : Submodule 𝒪[k] (n' → k))
    [L'.IsLattice k] :
    latInd L (lastPair q L').lat = tensRow (latInd L L') (dualInd L + ∑ Q ∈ withLat L, cosetInd q Q.lat Q.red) := by
  classical
  funext x
  rw [tensRow, coset_total, latInd, latInd, ite_zero_mul_ite_zero, mul_one]
  have hm : ∀ v : n' ⊕ Fin 1 → k, v ∈ (lastPair q L').lat ↔ v ∘ Sum.inl ∈ L' ∧ q.1 • v (Sum.inr 0) ∈ 𝒪[k] :=
    fun v => by
      rw [Pair.mem_lat_iff]
      simp only [lastPair_hasVal]
      constructor
      · rintro ⟨a, h, s, hs, -⟩
        exact ⟨h, hs ▸ s.2⟩
      · rintro ⟨h, hs⟩
        exact ⟨_, h, ⟨_, hs⟩, rfl, rfl⟩
  refine if_congr ⟨fun h => ⟨fun y hy => ((hm _).1 (h y hy)).1, fun y hy => ?_⟩,
    fun h y hy => (hm _).2 ⟨h.1 y hy, ?_⟩⟩ rfl rfl
  · have h1 := ((hm _).1 (h y hy)).2
    rw [smul_dotProduct]
    exact h1
  · have h1 := h.2 y hy
    rw [smul_dotProduct] at h1
    exact h1

end GlobalTheory.GluedExp

namespace GlobalTheory.GluedExp

theorem finite_expansions : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (q : Unif k) (χ : AddChar 𝓀[k] ℂ), χ ≠ 1 → ∀ (Λ : Submodule 𝒪[k] (n → k)) [Λ.IsLattice k], (∀ P : Pair k n', latInd (gluedS q 1 P.ker P.vec) Λ = ((resCard k : ℂ) ^ Fintype.card n)⁻¹ • (tensCol (latInd P.ker Λ) (vecInd Λ) + ∑ Q ∈ withLat Λ, tensCol (latInd P.ker Q.ker + mainDatum q χ 1 P Q) (charInd χ Q)) ∧ latInd P.ker Λ + ∑ Q ∈ withLat Λ, (latInd P.ker Q.ker + mainDatum q χ 1 P Q) = ((resCard k : ℂ) ^ Fintype.card n) • latInd P.lat Λ) ∧ (∀ R : Pair k n', latInd Λ (gluedS q 1 R.ker R.vec) = tensRow (latInd Λ R.ker) (dualInd Λ) + ∑ Q ∈ withLat Λ, tensRow (phiOne Q R) (cosetInd q Q.lat Q.red)) ∧ ∀ (L : Submodule 𝒪[k] (n' → k)) [L.IsLattice k], latInd Λ (lastKer L) = tensRow (latInd Λ L) (dualInd Λ) ∧ latInd Λ (lastPair q L).lat = tensRow (latInd Λ L) (dualInd Λ + ∑ Q ∈ withLat Λ, cosetInd q Q.lat Q.red) := by
  intro k _ _ _ _ n n' _ _ _ _ q χ hχ Λ _
  exact ⟨fun P => ⟨glued_col q χ hχ Λ P, glued_sum q χ hχ Λ P⟩, fun R => glued_row q Λ R,
    fun L _ => ⟨last_ker Λ L, last_lat q Λ L⟩⟩

end GlobalTheory.GluedExp
