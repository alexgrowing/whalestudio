import Formalism.GaussJetBounds.StatementN
import Formalism.GaussJetBounds.GaussJetProofs.ConstantCoeffAevalLinP
import Formalism.FormalGroupLog.FormalGroupLogProofs.ChainRule

noncomputable section
open scoped BigOperators

universe u

namespace Formalism.DworkPowerSeriesWeights

section Analytic

variable {K : Type u} [Field K] {ι : Type} [Fintype ι]

def dirD (L : ι → K) : Derivation K (MvPowerSeries ι K) (MvPowerSeries ι K) :=
  ∑ x, L x • MvPowerSeries.pderiv K x

lemma dirD_apply (L : ι → K) (F : MvPowerSeries ι K) :
    dirD L F = ∑ x, MvPowerSeries.C (L x) * MvPowerSeries.pderiv K x F := by
  unfold dirD
  have h := congrFun (map_sum (Derivation.coeFnAddMonoidHom (R := K) (A := MvPowerSeries ι K)
    (M := MvPowerSeries ι K)) (fun x => L x • MvPowerSeries.pderiv K x) Finset.univ) F
  rw [Derivation.coeFnAddMonoidHom_apply, Finset.sum_apply] at h
  rw [h]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Derivation.coeFnAddMonoidHom_apply, Derivation.smul_apply, MvPowerSeries.smul_eq_C_mul]

lemma jetPair_mul_linForm (P : MvPolynomial ι K) (L : ι → K) (F : MvPowerSeries ι K) :
    jetPair (P * linForm L) F = jetPair P (dirD L F) := by
  unfold linForm
  rw [Finset.mul_sum, jetPair_sum_left, dirD_apply, jetPair_sum_right]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [jetPair_C_mul_right, ← jetPair_mul_X, ← jetPair_C_mul_left]
  congr 1
  ring

lemma jetPair_one_left (F : MvPowerSeries ι K) :
    jetPair (1 : MvPolynomial ι K) F = MvPowerSeries.constantCoeff F := by
  rw [← MvPolynomial.C_1, jetPair_C_left, one_mul]

lemma dirD_X (L : ι → K) (x : ι) : dirD L (MvPowerSeries.X x) = MvPowerSeries.C (L x) := by
  classical
  rw [dirD_apply, Finset.sum_eq_single x]
  · rw [MvPowerSeries.pderiv_X_self, mul_one]
  · intro y _ hy
    rw [MvPowerSeries.pderiv_X_of_ne hy.symm, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ x) h

lemma dirD_C (L : ι → K) (a : K) : dirD L (MvPowerSeries.C a : MvPowerSeries ι K) = 0 := by
  rw [dirD_apply]
  simp

def linSer (c : ι → ι → K) (L : ι → K) : MvPowerSeries ι K :=
  ∑ x, ∑ y, MvPowerSeries.C (c x y) *
    (MvPowerSeries.C (L x) * MvPowerSeries.X y + MvPowerSeries.C (L y) * MvPowerSeries.X x)

lemma dirD_quadSer (c : ι → ι → K) (L : ι → K) : dirD L (quadSer c) = linSer c L := by
  unfold quadSer linSer
  rw [map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Derivation.leibniz, dirD_X, dirD_C, smul_eq_mul]
  ring

lemma dirD_linSer (c : ι → ι → K) (L L' : ι → K) :
    dirD L' (linSer c L) = MvPowerSeries.C (polar c L L') := by
  unfold linSer polar
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Derivation.leibniz, dirD_X, dirD_C, smul_eq_mul, map_add, map_mul]
  ring

lemma constantCoeff_linSer (c : ι → ι → K) (L : ι → K) :
    MvPowerSeries.constantCoeff (linSer c L) = 0 := by
  simp [linSer]

lemma constantCoeff_quadSer (c : ι → ι → K) :
    MvPowerSeries.constantCoeff (quadSer c) = 0 := by
  simp [quadSer]

lemma polar_comm (c : ι → ι → K) (L L' : ι → K) : polar c L L' = polar c L' L := by
  unfold polar
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

lemma jetPair_prod_lin_mul {α : Type} [DecidableEq α] (L : α → ι → K) (ℓ : MvPowerSeries ι K)
    (cst : α → K) (h0 : MvPowerSeries.constantCoeff ℓ = 0)
    (hd : ∀ a, dirD (L a) ℓ = MvPowerSeries.C (cst a)) (s : Finset α) :
    ∀ G : MvPowerSeries ι K, jetPair (∏ i ∈ s, linForm (L i)) (ℓ * G) =
      ∑ b ∈ s, cst b * jetPair (∏ i ∈ s.erase b, linForm (L i)) G := by
  induction s using Finset.induction_on with
  | empty =>
    intro G
    simp [jetPair_one_left, h0]
  | insert a s ha ih =>
    intro G
    rw [Finset.prod_insert ha, mul_comm, jetPair_mul_linForm, Derivation.leibniz, hd, smul_eq_mul,
      smul_eq_mul, jetPair_add_right, ih, mul_comm G, jetPair_C_mul_right, Finset.sum_insert ha,
      Finset.erase_insert ha, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun b hb => ?_
    have hab : a ≠ b := fun h => ha (h ▸ hb)
    rw [Finset.erase_insert_of_ne hab, Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h)),
      mul_comm (linForm (L a)), jetPair_mul_linForm]

end Analytic

section Exp

variable {K : Type u} [NormedField K] [CharZero K] {ι : Type} [Fintype ι]

lemma dirD_mvExp (L : ι → K) (f : MvPowerSeries ι K) (hf : MvPowerSeries.constantCoeff f = 0) :
    dirD L (mvExp f) = dirD L f * mvExp f := by
  rw [dirD_apply, dirD_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  unfold mvExp
  rw [Formalism.G.LogCR.pderiv_psubst hf, PowerSeries.derivative_exp]
  ring

lemma constantCoeff_mvExp (f : MvPowerSeries ι K) (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (mvExp f) = 1 := by
  unfold mvExp
  rw [PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hf),
    finsum_eq_single _ 0]
  · simp
  · intro n hn
    simp [hf, hn]

lemma jet_insert {α : Type} [DecidableEq α] (c : ι → ι → K) (S : K) (L : α → ι → K) (a : α)
    (s : Finset α) (ha : a ∉ s) (h : MvPowerSeries ι K) :
    jetPair (∏ i ∈ insert a s, linForm (L i)) (mvExp ((-S) • quadSer c) * h) =
      jetPair (∏ i ∈ s, linForm (L i)) (mvExp ((-S) • quadSer c) * dirD (L a) h) +
        ∑ b ∈ s, (-S * polar c (L a) (L b)) *
          jetPair (∏ i ∈ s.erase b, linForm (L i)) (mvExp ((-S) • quadSer c) * h) := by
  have h0 : MvPowerSeries.constantCoeff ((-S) • quadSer c) = 0 := by
    rw [MvPowerSeries.smul_eq_C_mul, map_mul, constantCoeff_quadSer, mul_zero]
  rw [Finset.prod_insert ha, mul_comm, jetPair_mul_linForm, Derivation.leibniz, dirD_mvExp _ _ h0,
    Derivation.map_smul, dirD_quadSer, smul_eq_mul, smul_eq_mul, jetPair_add_right]
  congr 1
  rw [show h * ((-S) • linSer c (L a) * mvExp ((-S) • quadSer c)) =
      MvPowerSeries.C (-S) * (linSer c (L a) * (mvExp ((-S) • quadSer c) * h)) by
    rw [MvPowerSeries.smul_eq_C_mul]; ring]
  rw [jetPair_C_mul_right, jetPair_prod_lin_mul L (linSer c (L a)) (fun b => polar c (L a) (L b))
    (constantCoeff_linSer _ _) (fun b => dirD_linSer _ _ _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

end Exp

section Comb

variable {n : ℕ}

def invOn (s : Finset (Fin n)) : Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => σ * σ = 1 ∧ ∀ i, i ∉ s → σ i = i)

lemma mem_invOn {s : Finset (Fin n)} {σ : Equiv.Perm (Fin n)} :
    σ ∈ invOn s ↔ σ * σ = 1 ∧ ∀ i, i ∉ s → σ i = i := by
  simp [invOn]

lemma swap_mul_apply_of_ne {a b : Fin n} {τ : Equiv.Perm (Fin n)} (hτa : τ a = a) (hτb : τ b = b)
    {i : Fin n} (hia : i ≠ a) (hib : i ≠ b) : (Equiv.swap a b * τ) i = τ i := by
  rw [Equiv.Perm.mul_apply]
  refine Equiv.swap_apply_of_ne_of_ne (fun h => hia ?_) (fun h => hib ?_)
  · exact τ.injective (h.trans hτa.symm)
  · exact τ.injective (h.trans hτb.symm)

lemma swap_mul_apply_left {a b : Fin n} {τ : Equiv.Perm (Fin n)} (hτa : τ a = a) :
    (Equiv.swap a b * τ) a = b := by
  rw [Equiv.Perm.mul_apply, hτa, Equiv.swap_apply_left]

lemma swap_mul_apply_right {a b : Fin n} {τ : Equiv.Perm (Fin n)} (hτb : τ b = b) :
    (Equiv.swap a b * τ) b = a := by
  rw [Equiv.Perm.mul_apply, hτb, Equiv.swap_apply_right]

variable {R : Type u} [CommRing R]

def edgeW (w : Fin n → Fin n → R) (σ : Equiv.Perm (Fin n)) : R :=
  ∏ i ∈ Finset.univ.filter (fun i => i < σ i), w i (σ i)

lemma edgeW_swap_lt (w : Fin n → Fin n → R) {a b : Fin n} (hab : a < b) {τ : Equiv.Perm (Fin n)}
    (hτa : τ a = a) (hτb : τ b = b) : edgeW w (Equiv.swap a b * τ) = w a b * edgeW w τ := by
  unfold edgeW
  have hset : Finset.univ.filter (fun i => i < (Equiv.swap a b * τ) i) =
      insert a (Finset.univ.filter (fun i => i < τ i)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    by_cases hia : i = a
    · subst hia
      simp [swap_mul_apply_left hτa, hab]
    · by_cases hib : i = b
      · subst hib
        simp [swap_mul_apply_right hτb, hτb, hia, hab.le]
      · simp [swap_mul_apply_of_ne hτa hτb hia hib, hia]
  have hna : a ∉ Finset.univ.filter (fun i => i < τ i) := by
    simp [hτa]
  rw [hset, Finset.prod_insert hna, swap_mul_apply_left hτa]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  have hi' : i < τ i := (Finset.mem_filter.mp hi).2
  have hia : i ≠ a := fun h => by rw [h, hτa] at hi'; exact lt_irrefl _ hi'
  have hib : i ≠ b := fun h => by rw [h, hτb] at hi'; exact lt_irrefl _ hi'
  rw [swap_mul_apply_of_ne hτa hτb hia hib]

lemma edgeW_swap (w : Fin n → Fin n → R) (hw : ∀ i j, w i j = w j i) {a b : Fin n} (hab : a ≠ b)
    {τ : Equiv.Perm (Fin n)} (hτa : τ a = a) (hτb : τ b = b) :
    edgeW w (Equiv.swap a b * τ) = w a b * edgeW w τ := by
  rcases lt_or_gt_of_ne hab with h | h
  · exact edgeW_swap_lt w h hτa hτb
  · rw [Equiv.swap_comm, hw a b]
    exact edgeW_swap_lt w h hτb hτa

lemma edgeW_one (w : Fin n → Fin n → R) : edgeW w 1 = 1 := by
  simp [edgeW]

lemma invOn_empty : invOn (∅ : Finset (Fin n)) = {1} := by
  ext σ
  rw [mem_invOn, Finset.mem_singleton]
  constructor
  · rintro ⟨_, h⟩
    exact Equiv.ext fun i => h i (Finset.notMem_empty i)
  · rintro rfl
    simp

lemma swap_mul_sq {a b : Fin n} {τ : Equiv.Perm (Fin n)} (hτ : τ * τ = 1)
    (h : Equiv.swap (τ a) (τ b) = Equiv.swap a b) :
    (Equiv.swap a b * τ) * (Equiv.swap a b * τ) = 1 := by
  have hc : τ * Equiv.swap a b = Equiv.swap a b * τ := by
    rw [Equiv.mul_swap_eq_swap_mul, h]
  calc (Equiv.swap a b * τ) * (Equiv.swap a b * τ)
      = Equiv.swap a b * (τ * Equiv.swap a b) * τ := by simp only [mul_assoc]
    _ = (Equiv.swap a b * Equiv.swap a b) * (τ * τ) := by rw [hc]; simp only [mul_assoc]
    _ = 1 := by rw [hτ, Equiv.swap_mul_self, one_mul]

lemma sum_invOn_insert (w : Fin n → Fin n → R) (hw : ∀ i j, w i j = w j i)
    (g : Finset (Fin n) → R) (a : Fin n) (s : Finset (Fin n)) (ha : a ∉ s) :
    ∑ σ ∈ invOn (insert a s), edgeW w σ * g ((insert a s).filter (fun i => σ i = i)) =
      ∑ σ ∈ invOn s, edgeW w σ * g (insert a (s.filter (fun i => σ i = i))) +
        ∑ b ∈ s, w a b * ∑ σ ∈ invOn (s.erase b),
          edgeW w σ * g ((s.erase b).filter (fun i => σ i = i)) := by
  have hmaps : ∀ σ ∈ invOn (insert a s), σ a ∈ insert a s := by
    intro σ hσ
    by_contra hn
    have h1 := (mem_invOn.mp hσ).2 _ hn
    exact hn (by rw [σ.injective h1]; exact Finset.mem_insert_self _ _)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.sum_insert ha]
  congr 1
  · have hset : (invOn (insert a s)).filter (fun σ => σ a = a) = invOn s := by
      ext σ
      rw [Finset.mem_filter, mem_invOn, mem_invOn]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨h1, fun i hi => ?_⟩
        by_cases hia : i = a
        · rw [hia, h3]
        · exact h2 i (by simp [hia, hi])
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, fun i hi => h2 i fun h => hi (Finset.mem_insert_of_mem h)⟩, h2 a ha⟩
    rw [hset]
    refine Finset.sum_congr rfl fun σ hσ => ?_
    rw [Finset.filter_insert, if_pos ((mem_invOn.mp hσ).2 a ha)]
  · refine Finset.sum_congr rfl fun b hb => ?_
    have hab : a ≠ b := fun h => ha (h ▸ hb)
    rw [Finset.mul_sum]
    symm
    refine Finset.sum_nbij' (fun τ => Equiv.swap a b * τ) (fun σ => Equiv.swap a b * σ) ?_ ?_ ?_ ?_ ?_
    · intro τ hτ
      obtain ⟨h1, h2⟩ := mem_invOn.mp hτ
      have hτa : τ a = a := h2 a fun h => ha (Finset.mem_of_mem_erase h)
      have hτb : τ b = b := h2 b (Finset.notMem_erase b s)
      rw [Finset.mem_filter, mem_invOn]
      refine ⟨⟨swap_mul_sq h1 (by rw [hτa, hτb]), fun i hi => ?_⟩, swap_mul_apply_left hτa⟩
      have hia : i ≠ a := fun h => hi (h ▸ Finset.mem_insert_self _ _)
      have his : i ∉ s := fun h => hi (Finset.mem_insert_of_mem h)
      have hib : i ≠ b := fun h => his (h ▸ hb)
      rw [swap_mul_apply_of_ne hτa hτb hia hib]
      exact h2 i fun h => his (Finset.mem_of_mem_erase h)
    · intro σ hσ
      obtain ⟨hσ1, hσa⟩ := Finset.mem_filter.mp hσ
      obtain ⟨h1, h2⟩ := mem_invOn.mp hσ1
      have hσb : σ b = a := by
        have := congrArg (fun f : Equiv.Perm (Fin n) => f a) h1
        simpa [hσa] using this
      rw [mem_invOn]
      refine ⟨swap_mul_sq h1 (by rw [hσa, hσb, Equiv.swap_comm]), fun i hi => ?_⟩
      by_cases hia : i = a
      · rw [hia, Equiv.Perm.mul_apply, hσa, Equiv.swap_apply_right]
      · by_cases hib : i = b
        · rw [hib, Equiv.Perm.mul_apply, hσb, Equiv.swap_apply_left]
        · have his : i ∉ insert a s := by
            simp only [Finset.mem_insert, not_or]
            exact ⟨hia, fun h => hi (Finset.mem_erase.mpr ⟨hib, h⟩)⟩
          rw [Equiv.Perm.mul_apply, h2 i his, Equiv.swap_apply_of_ne_of_ne hia hib]
    · intro τ _
      simp [← mul_assoc]
    · intro σ _
      simp [← mul_assoc]
    · intro τ hτ
      obtain ⟨h1, h2⟩ := mem_invOn.mp hτ
      have hτa : τ a = a := h2 a fun h => ha (Finset.mem_of_mem_erase h)
      have hτb : τ b = b := h2 b (Finset.notMem_erase b s)
      have hset : (insert a s).filter (fun i => (Equiv.swap a b * τ) i = i) =
          (s.erase b).filter (fun i => τ i = i) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_erase]
        by_cases hia : i = a
        · subst hia
          simp [swap_mul_apply_left hτa, ha, hab.symm]
        · by_cases hib : i = b
          · subst hib
            simp [swap_mul_apply_right hτb, hab]
          · simp [swap_mul_apply_of_ne hτa hτb hia hib, hia, hib]
      rw [hset, edgeW_swap w hw hab hτa hτb, mul_assoc]

end Comb

section Main

variable {K : Type u} [NormedField K] [CharZero K] {ι : Type} [Fintype ι]

lemma matchings_on (c : ι → ι → K) (S : K) {n : ℕ} (L : Fin n → ι → K) (s : Finset (Fin n)) :
    ∀ h : MvPowerSeries ι K,
      jetPair (∏ i ∈ s, linForm (L i)) (mvExp ((-S) • quadSer c) * h) =
        ∑ σ ∈ invOn s, edgeW (fun i j => -S * polar c (L i) (L j)) σ *
          jetPair (∏ i ∈ s.filter (fun i => σ i = i), linForm (L i)) h := by
  induction s using Finset.strongInduction with
  | H s ih =>
    intro h
    rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · have h0 : MvPowerSeries.constantCoeff ((-S) • quadSer c) = 0 := by
        rw [MvPowerSeries.smul_eq_C_mul, map_mul, constantCoeff_quadSer, mul_zero]
      rw [invOn_empty, Finset.sum_singleton, edgeW_one, Finset.filter_empty, Finset.prod_empty,
        jetPair_one_left, jetPair_one_left, map_mul, constantCoeff_mvExp _ h0]
    · obtain ⟨t, hat, rfl⟩ : ∃ t, a ∉ t ∧ insert a t = s :=
        ⟨s.erase a, Finset.notMem_erase a s, Finset.insert_erase ha⟩
      rw [jet_insert c S L a t hat h,
        sum_invOn_insert (fun i j => -S * polar c (L i) (L j))
          (fun i j => by rw [polar_comm]) (fun F => jetPair (∏ i ∈ F, linForm (L i)) h) a t hat,
        ih t (Finset.ssubset_insert hat)]
      congr 1
      · refine Finset.sum_congr rfl fun σ _ => ?_
        rw [Finset.prod_insert (fun hh => hat (Finset.mem_of_mem_filter a hh)),
          mul_comm (linForm (L a)), jetPair_mul_linForm]
      · refine Finset.sum_congr rfl fun b hb => ?_
        rw [ih (t.erase b) ((Finset.erase_subset b t).trans_ssubset (Finset.ssubset_insert hat))]

end Main

theorem matching_existence : Matchings.{u} := by
  intro K _ _ ι _ c S sg n L
  rw [matchings_on c S L Finset.univ sg]
  have hset : invOn (Finset.univ : Finset (Fin n)) =
      Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => σ * σ = 1) := by
    ext σ
    simp [mem_invOn]
  rw [hset]
  rfl

end Formalism.DworkPowerSeriesWeights
