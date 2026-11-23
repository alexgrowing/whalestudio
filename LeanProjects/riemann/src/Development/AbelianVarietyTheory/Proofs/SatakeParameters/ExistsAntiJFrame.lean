import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.InertPlaceSetting
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.SphericalThetaInertPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPlaceHeckeDoubleCosetsInverseRepsLabel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryDivisorDualLabel

noncomputable section

open Formalism.UG Formalism.IndefR.Mult

namespace GlobalTheory.InertThetaCompare

def Good (n : ℕ) (d : List ℤ) : Prop := d.length = n ∧ d.Pairwise (fun a b => b ≤ a) ∧ dualLab d = d

theorem anti_getD {n : ℕ} {d : List ℤ} (h1 : d.length = n) (h2 : d.Pairwise (fun a b => b ≤ a)) :
    Antitone fun i : Fin n => d.getD i.1 0 := by
  subst h1
  intro i j hij
  simp only [List.getD_eq_getElem _ _ i.2, List.getD_eq_getElem _ _ j.2]
  rcases hij.eq_or_lt with rfl | h
  · exact le_rfl
  · exact List.pairwise_iff_getElem.1 h2 _ _ i.2 j.2 h

theorem eq_of_getD {n : ℕ} {d d' : List ℤ} (h1 : d.length = n) (h2 : d'.length = n)
    (h : ∀ i : Fin n, d.getD i.1 0 = d'.getD i.1 0) : d = d' := by
  refine List.ext_getElem (h1.trans h2.symm) fun i a b => ?_
  have := h ⟨i, h1 ▸ a⟩
  rwa [List.getD_eq_getElem _ _ a, List.getD_eq_getElem _ _ b] at this

theorem Good.rev {n : ℕ} {d : List ℤ} (h : Good n d) (i : Fin n) : d.getD i.rev.1 0 = -d.getD i.1 0 := by
  have := GlobalTheory.DualDivU.getD_dualLab d h.1 i
  rw [h.2.2] at this
  rw [this, neg_neg]

theorem sum_Ici_le {n : ℕ} {μ : Fin n → ℤ} (hμ : Antitone μ) (k : Fin n) (S : Finset (Fin n))
    (hS : (Finset.Ici k).card = S.card) : ∑ i ∈ Finset.Ici k, μ i ≤ ∑ i ∈ S, μ i := by
  rw [← Finset.sum_inter_add_sum_sdiff (Finset.Ici k) S, ← Finset.sum_inter_add_sum_sdiff S (Finset.Ici k),
    Finset.inter_comm S]
  have h1 := Finset.sum_le_card_nsmul (Finset.Ici k \ S) μ (μ k) fun i hi =>
    hμ (Finset.mem_Ici.1 (Finset.mem_sdiff.1 hi).1)
  have h2 := Finset.card_nsmul_le_sum (S \ Finset.Ici k) μ (μ k) fun i hi =>
    hμ (le_of_not_ge fun h => (Finset.mem_sdiff.1 hi).2 (Finset.mem_Ici.2 h))
  rw [Finset.card_sdiff_comm hS] at h1
  linarith

theorem eq_of_tails {n : ℕ} {a b : Fin n → ℤ} (h : ∀ k, ∑ i ∈ Finset.Ici k, a i = ∑ i ∈ Finset.Ici k, b i) :
    a = b := by
  funext k
  induction k using WellFoundedGT.induction with
  | ind k ih =>
    have := h k
    rw [← Finset.Ioi_insert, Finset.sum_insert (by simp), Finset.sum_insert (by simp),
      Finset.sum_congr rfl fun i hi => ih i (Finset.mem_Ioi.1 hi)] at this
    exact add_right_cancel this

section Local

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

theorem val_prod_zpow {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) {ι : Type} (s : Finset ι) (f : ι → ℤ) :
    Valued.v (∏ i ∈ s, ϖ ^ f i) = WithZero.exp (-∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, map_mul, ih, map_zpow₀, hϖ, ← WithZero.exp_zsmul,
      ← WithZero.exp_add]
    congr 1
    simp only [smul_eq_mul]
    ring

theorem tail_le {ϖ ϖ' : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (hϖ' : Valued.v ϖ' = WithZero.exp (-1 : ℤ))
    {a μ : Fin n → ℤ} (hμ : Antitone μ)
    {b k₁ k₂ : Matrix (Fin n) (Fin n) L} (hb : b.BlockTriangular id) (hd : ∀ i, b i i = ϖ' ^ a i)
    (h₁ : ∀ i j, k₁ i j ∈ intL L) (h₂ : ∀ i j, k₂ i j ∈ intL L)
    (e : b = k₁ * Matrix.diagonal (fun i => ϖ ^ μ i) * k₂) (k : Fin n) :
    ∑ i ∈ Finset.Ici k, μ i ≤ ∑ i ∈ Finset.Ici k, a i := by
  let ι := {i // i ∈ Finset.Ici k}
  let B : Matrix ι ι L := b.submatrix Subtype.val Subtype.val
  have hB : B.det = ∏ i ∈ Finset.Ici k, ϖ' ^ a i := by
    rw [Matrix.det_of_upperTriangular (M := B) (fun i j hij => hb hij), ← Finset.prod_coe_sort (Finset.Ici k)]
    exact Finset.prod_congr rfl fun i _ => hd i
  have hE : B.det = ∑ p : ι → Fin n, (k₁.submatrix Subtype.val p).det * ((∏ i, ϖ ^ μ (p i)) * ∏ i : ι, k₂ (p i) i) := by
    have hij : ∀ i j : ι, B i j = ∑ l, k₁ i l * (ϖ ^ μ l * k₂ l j) := fun i j => by
      show b i j = _
      rw [e, Matrix.mul_assoc, Matrix.mul_apply]
      simp only [Matrix.diagonal_mul]
    simp only [Matrix.det_apply', hij, Finset.prod_univ_sum, Finset.mul_sum, Fintype.piFinset_univ, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun τ _ => ?_
    simp only [Finset.prod_mul_distrib, Matrix.submatrix_apply, mul_assoc]
    rfl
  have hle : Valued.v B.det ≤ WithZero.exp (-∑ i ∈ Finset.Ici k, μ i) := by
    rw [hE]
    refine Valuation.map_sum_le _ fun p _ => ?_
    by_cases hp : Function.Injective p
    · have h3 : Valued.v (k₁.submatrix Subtype.val p : Matrix ι ι L).det ≤ 1 :=
        Formalism.UG.P.cartan_det_mem (intL L) _ fun i j => h₁ _ _
      have h4 : Valued.v (∏ i : ι, k₂ (p i) i) ≤ 1 := (intL L).prod_mem fun i _ => h₂ _ _
      rw [map_mul, map_mul, val_prod_zpow hϖ]
      refine (mul_le_of_le_one_left' h3).trans ((mul_le_of_le_one_right' h4).trans ?_)
      rw [WithZero.exp_le_exp, neg_le_neg_iff, ← Finset.sum_image (s := Finset.univ) (g := p) (f := μ) hp.injOn]
      exact sum_Ici_le hμ k _ (by rw [Finset.card_image_of_injective _ hp]; simp [ι])
    · obtain ⟨i, j, h1, h2⟩ := Function.not_injective_iff.1 hp
      rw [Matrix.det_zero_of_column_eq h2 (fun l => by simp [h1]), zero_mul, map_zero]
      exact zero_le
  rw [hB, val_prod_zpow hϖ', WithZero.exp_le_exp, neg_le_neg_iff] at hle
  exact hle

end Local

section Satake

open GlobalTheory.IndefiniteRowSideFullHecke.InertPlaceSetting

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n q : ℕ} {ϖ : L}

local notation "⟪" b "⟫" => (((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)

theorem unif_ne_zero (hU : IsUnramInv ϖ σ q) : ϖ ≠ 0 := by
  intro h
  have := hU.2.2.2.1
  rw [h, Valuation.map_zero] at this
  exact absurd this WithZero.zero_ne_coe

def tExp (n m : ℕ) (a : Fin m → ℤ) (i : Fin n) : ℤ :=
  if h : i.val < m then a ⟨i.val, h⟩
  else if h' : n - m ≤ i.val ∧ n - 1 - i.val < m then -(a ⟨n - 1 - i.val, h'.2⟩) else 0

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem tMat_eq (m : ℕ) (a : Fin m → ℤ) : tMat ϖ n m a = Matrix.diagonal fun i => ϖ ^ tExp n m a i := by
  unfold tMat tExp
  congr 1
  funext i
  split_ifs <;> simp

theorem tExp_good {d : List ℤ} (h : Good n d) (i : Fin n) :
    tExp n (n / 2) (fun j => d.getD j.1 0) i = d.getD i.1 0 := by
  have h1 := h.rev i
  have h2 : (i.rev : ℕ) = n - 1 - i := by rw [Fin.val_rev]; omega
  have h3 := i.2
  unfold tExp
  split_ifs with a b
  · rfl
  · simp only [← h2, h1, neg_neg]
  · have : (i.rev : ℕ) = i := by omega
    rw [this] at h1
    omega

theorem exists_diag (hU : IsUnramInv ϖ σ q) {d : List ℤ} (h : Good n d) :
    ∃ t : GU σ n, ⟪t⟫ = Matrix.diagonal fun i : Fin n => ϖ ^ d.getD i.1 0 := by
  obtain ⟨t, ht, -⟩ := P.fSatake_diag_exists (σ := σ) (fun i : Fin n => ϖ ^ d.getD i.1 0) fun i => by
    rw [map_zpow₀, hU.2.2.1, h.rev, ← zpow_add₀ (unif_ne_zero hU), add_neg_cancel, zpow_zero]
  exact ⟨t, ht⟩

def Cell (ϖ : L) (a : Fin (n / 2) → ℤ) (x : GU σ n ⧸ KU σ n) : Prop :=
  ∃ u : GU σ n, IsUnipU u ∧ ∃ k ∈ KU σ n, ⟪x.out⟫ = tMat ϖ n (n / 2) a * ⟪u⟫ * ⟪k⟫

def InLab (ϖ : L) (d : List ℤ) (x : GU σ n ⧸ KU σ n) : Prop :=
  ∃ k₁ ∈ KU σ n, ∃ k₂ ∈ KU σ n, ⟪x.out⟫ = ⟪k₁⟫ * Matrix.diagonal (fun i : Fin n => ϖ ^ d.getD i.1 0) * ⟪k₂⟫

theorem finite_inLab (hU : IsUnramInv ϖ σ q) {d : List ℤ} (h : Good n d) :
    {x : GU σ n ⧸ KU σ n | InLab ϖ d x}.Finite := by
  obtain ⟨t, ht⟩ := exists_diag hU h
  refine (P.finite_cosets_in_doset (P.isCommensurated_integral_unitary_of_unramified hU n) t).subset ?_
  rintro x ⟨k₁, h₁, k₂, h₂, e⟩
  refine ⟨⟨k₁, h₁⟩, ⟨k₂, h₂⟩, Subtype.ext (Units.ext ?_)⟩
  simp only [Subgroup.coe_mul, Units.val_mul, ht]
  exact e

def cnt (σ : L →+* L) (n : ℕ) (ϖ : L) (d : List ℤ) (a : Fin (n / 2) → ℤ) : ℕ :=
  {x : GU σ n ⧸ KU σ n | Cell ϖ a x ∧ InLab ϖ d x}.ncard

theorem satU_labInd (hU : IsUnramInv ϖ σ q) {d : List ℤ} (h : Good n d) (α : Fin (n / 2) → ℂ) :
    SatU ϖ q (labInd σ n ϖ d) α = ∑ᶠ a : Fin (n / 2) → ℤ,
      (∏ i, α i ^ (a i) * (q : ℂ) ^ (-(a i) * ((n : ℤ) - 1 - 2 * (i.val : ℤ)))) * (cnt σ n ϖ d a : ℂ) := by
  classical
  unfold SatU
  refine finsum_congr fun a => ?_
  congr 1
  have hf : {x : GU σ n ⧸ KU σ n | Cell ϖ a x ∧ InLab ϖ d x}.Finite := (finite_inLab hU h).subset fun x hx => hx.2
  have key : ∀ x : GU σ n ⧸ KU σ n, ∀ [Decidable (Cell ϖ a x)], (if Cell ϖ a x then labInd σ n ϖ d x.out else 0) =
      if x ∈ hf.toFinset then 1 else 0 := by
    intro x _
    simp only [Set.Finite.mem_toFinset]
    by_cases h1 : Cell ϖ a x
    · by_cases h2 : InLab ϖ d x
      · rw [if_pos h1, if_pos (show x ∈ {x | Cell ϖ a x ∧ InLab ϖ d x} from ⟨h1, h2⟩)]
        unfold labInd
        exact Set.indicator_of_mem (f := (1 : GU σ n → ℂ)) (a := x.out) (by exact h2)
      · rw [if_pos h1, if_neg (show x ∉ {x | Cell ϖ a x ∧ InLab ϖ d x} from fun h => h2 h.2)]
        unfold labInd
        exact Set.indicator_of_notMem (a := x.out) (by exact h2) _
    · rw [if_neg h1, if_neg (show x ∉ {x | Cell ϖ a x ∧ InLab ϖ d x} from fun h => h1 h.1)]
  refine (finsum_congr fun x => @key x _).trans ?_
  rw [finsum_eq_sum_of_support_subset (s := hf.toFinset) _ (fun x hx => by
    by_contra h
    exact hx (if_neg h)), Finset.sum_congr rfl fun x hx => if_pos hx, cnt, Set.ncard_eq_toFinset_card _ hf]
  simp

theorem finite_cnt (hU : IsUnramInv ϖ σ q) {d : List ℤ} (h : Good n d) : {a | cnt σ n ϖ d a ≠ 0}.Finite := by
  refine ((finite_inLab hU h).biUnion (t := fun x => {a | Cell ϖ a x}) fun x _ => Set.Subsingleton.finite ?_).subset ?_
  · rintro a ⟨u, hu, k, hk, e⟩ a' ⟨u', hu', k', hk', e'⟩
    exact P.fSatake_cell_unique hU (Nat.mul_div_le n 2) hu hu' hk hk' (e.symm.trans e')
  · intro a ha
    obtain ⟨x, hx⟩ := Set.nonempty_of_ncard_ne_zero ha
    exact Set.mem_biUnion hx.2 hx.1

theorem cnt_self (hU : IsUnramInv ϖ σ q) {d : List ℤ} (h : Good n d) :
    cnt σ n ϖ d (fun j => d.getD j.1 0) ≠ 0 := by
  obtain ⟨t, ht⟩ := exists_diag hU h
  refine Set.ncard_ne_zero_of_mem (a := (QuotientGroup.mk t : GU σ n ⧸ KU σ n)) ?_
    ((finite_inLab hU h).subset fun x hx => hx.2)
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (KU σ n) t
  refine ⟨⟨1, ⟨P.fSatake_borel_one, fun i => by simp⟩, k, k.2, ?_⟩, 1, one_mem _, k, k.2, ?_⟩
  · rw [hk, tMat_eq]
    simp only [tExp_good h, Subgroup.coe_mul, Units.val_mul, ht, OneMemClass.coe_one, Units.val_one, Matrix.mul_one]
  · rw [hk]
    simp only [Subgroup.coe_mul, Units.val_mul, ht, OneMemClass.coe_one, Units.val_one, Matrix.one_mul]

theorem tail_of_cnt (hU : IsUnramInv ϖ σ q) {d μ : List ℤ} (h : Good n d) (h' : Good n μ)
    (hc : cnt σ n ϖ μ (fun j => d.getD j.1 0) ≠ 0) (k : Fin n) :
    ∑ i ∈ Finset.Ici k, μ.getD i.1 0 ≤ ∑ i ∈ Finset.Ici k, d.getD i.1 0 := by
  obtain ⟨x, ⟨u, hu, k₀, hk₀, e⟩, k₁, h₁, k₂, h₂, e'⟩ := Set.nonempty_of_ncard_ne_zero hc
  rw [tMat_eq] at e
  simp only [tExp_good h] at e
  have hub := (P.fSatake_borel_iff u).1 hu.1
  have hD : (Matrix.diagonal fun i : Fin n => ϖ ^ d.getD i.1 0).BlockTriangular id := Matrix.blockTriangular_diagonal _
  refine tail_le (ϖ := ϖ) (ϖ' := ϖ) hU.2.2.2.1 hU.2.2.2.1 (anti_getD h'.1 h'.2.1) (hD.mul hub)
    (fun i => by rw [Matrix.diagonal_mul, hu.2, mul_one]) (P.fSatake_K_int h₁)
    (P.fSatake_K_int (mul_mem h₂ (inv_mem hk₀))) ?_ k
  simp only [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_inv]
  rw [← Matrix.mul_assoc, ← e', e, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

def mono {m : ℕ} (a : Fin m → ℤ) : (Fin m → ℂˣ) →* ℂ where
  toFun α := ∏ i, (α i : ℂ) ^ a i
  map_one' := by simp
  map_mul' α β := by simp [mul_zpow, Finset.prod_mul_distrib]

theorem mono_injective {m : ℕ} : Function.Injective (mono (m := m)) := by
  intro a b h
  funext i
  have := DFunLike.congr_fun h (Pi.mulSingle i (Units.mk0 (2 : ℂ) two_ne_zero))
  have e : ∀ c : Fin m → ℤ, mono c (Pi.mulSingle i (Units.mk0 (2 : ℂ) two_ne_zero)) = (2 : ℂ) ^ c i := fun c => by
    show ∏ j : Fin m, _ = _
    rw [Finset.prod_eq_single i (fun j _ hj => by rw [Pi.mulSingle_eq_of_ne hj]; simp) (by simp)]
    simp
  rw [e, e] at this
  have h2 : ((2 : ℝ) : ℂ) ^ a i = ((2 : ℝ) : ℂ) ^ b i := by
    rw [Complex.ofReal_ofNat]; exact this
  rw [← Complex.ofReal_zpow, ← Complex.ofReal_zpow, Complex.ofReal_inj] at h2
  exact zpow_right_injective₀ (by norm_num) (by norm_num) h2

theorem satU_indep (hU : IsUnramInv ϖ σ q) (s : Finset (List ℤ)) (c : List ℤ → ℂ) (hs : ∀ d ∈ s, Good n d)
    (h : ∀ α : Fin (n / 2) → ℂ, (∀ l, α l ≠ 0) → ∑ d ∈ s, c d * SatU ϖ q (labInd σ n ϖ d) α = 0) :
    ∀ d ∈ s, c d = 0 := by
  classical
  have hq : (q : ℂ) ≠ 0 := by
    have := hU.2.2.2.2.2.1
    exact_mod_cast (by omega : q ≠ 0)
  have hA : (⋃ d ∈ (s : Set (List ℤ)), {a | cnt σ n ϖ d a ≠ 0}).Finite :=
    s.finite_toSet.biUnion fun d hd => finite_cnt hU (hs d hd)
  have hz : ∀ a ∈ hA.toFinset, (∏ i : Fin (n / 2), (q : ℂ) ^ (-(a i) * ((n : ℤ) - 1 - 2 * (i.val : ℤ)))) *
      ∑ d ∈ s, c d * (cnt σ n ϖ d a : ℂ) = 0 := by
    refine linearIndependent_iff'.1 ((linearIndependent_monoidHom (Fin (n / 2) → ℂˣ) ℂ).comp _ mono_injective)
      hA.toFinset _ (funext fun α => ?_)
    have := h (fun i => α i) fun i => (α i).ne_zero
    rw [Finset.sum_congr rfl fun d hd => by
      rw [satU_labInd hU (hs d hd), finsum_eq_sum_of_support_subset (s := hA.toFinset) _ (fun a ha => by
        rw [Finset.mem_coe, Set.Finite.mem_toFinset]
        exact Set.mem_biUnion hd fun h0 => ha (by simp [h0])), Finset.mul_sum], Finset.sum_comm] at this
    rw [Finset.sum_apply, Pi.zero_apply, ← this]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Function.comp, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul, Finset.prod_mul_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    show _ * ∏ i, (α i : ℂ) ^ a i = _
    ring
  by_contra hne
  push Not at hne
  obtain ⟨d₀, hd₀, hmin⟩ := (s.filter fun d => c d ≠ 0).exists_min_image
    (fun d => ∑ k : Fin n, ∑ i ∈ Finset.Ici k, d.getD i.1 0)
    (by obtain ⟨d, h1, h2⟩ := hne; exact ⟨d, Finset.mem_filter.2 ⟨h1, h2⟩⟩)
  obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hd₀
  have h3 := hz (fun j => d₀.getD j.1 0) (by
    rw [Set.Finite.mem_toFinset]
    exact Set.mem_biUnion h1 (cnt_self hU (hs _ h1)))
  rw [mul_eq_zero, Finset.sum_eq_single d₀ ?_ (fun h => absurd h1 h)] at h3
  · rcases h3 with h3 | h3
    · exact Finset.prod_ne_zero_iff.2 (fun i _ => zpow_ne_zero _ hq) h3
    · exact mul_ne_zero h2 (by exact_mod_cast cnt_self hU (hs _ h1)) h3
  · intro μ hμ hne'
    by_contra h0
    have h4 : c μ ≠ 0 := left_ne_zero_of_mul h0
    have h5 : cnt σ n ϖ μ (fun j => d₀.getD j.1 0) ≠ 0 := fun h => h0 (by rw [h, Nat.cast_zero, mul_zero])
    have h6 := tail_of_cnt hU (hs _ h1) (hs _ hμ) h5
    have h7 := (Finset.sum_eq_sum_iff_of_le fun k _ => h6 k).1
      (le_antisymm (Finset.sum_le_sum fun k _ => h6 k) (hmin μ (Finset.mem_filter.2 ⟨hμ, h4⟩)))
    exact hne' (eq_of_getD (hs _ hμ).1 (hs _ h1).1
      (congrFun (eq_of_tails fun k => h7 k (Finset.mem_univ k))))

end Satake

section Completion

open IsDedekindDomain NumberField GlobalTheory.InertDoubleCoset GlobalTheory.SelfDualGenus

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}
  {σ : v.adicCompletion K →+* v.adicCompletion K} {n q : ℕ} {ϖ : v.adicCompletion K}

theorem exists_antiJ_frame (hU : IsUnramInv ϖ σ q) (n : ℕ) :
    ∃ h ∈ GLint (Fin n) (intL (v.adicCompletion K)), cT σ h.1 * 1 * h.1 = antiJ (v.adicCompletion K) n := by
  obtain ⟨hσσ, hσ, -, -, ⟨x, hx1, hx2⟩, -⟩ := hU
  have := isAdicComplete_adicCompletionIntegers v
  have : Finite (v.adicCompletionIntegers K ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) :=
    finite_residueField_adicCompletionIntegers v
  let c : v.adicCompletionIntegers K →+* v.adicCompletionIntegers K :=
    (σ.comp (v.adicCompletionIntegers K).subtype).codRestrict (v.adicCompletionIntegers K) fun x => by
      show Valued.v (σ x) ≤ 1
      rw [hσ]; exact x.2
  have hc : ∀ x, c (c x) = x := fun x => Subtype.ext (hσσ x)
  have hI : ∀ x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K),
      c x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
    intro x hx hu
    exact hx (by simpa [hc] using hu.map c)
  have hω : ∃ ω, IsUnit (ω - c ω) := by
    refine ⟨⟨x, hx1⟩, ?_⟩
    rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    show Valued.v (x - σ x) = 1
    rw [Valuation.map_sub_swap, hx2]
  let ι := (v.adicCompletionIntegers K).subtype
  let B : Matrix (Fin n) (Fin n) (v.adicCompletionIntegers K) := fun i j => if i.val + j.val + 1 = n then 1 else 0
  have hBι : B.map ι = antiJ (v.adicCompletion K) n := by
    refine Matrix.ext fun i j => ?_
    show ι (if i.val + j.val + 1 = n then 1 else 0) = if i.val + j.val + 1 = n then 1 else 0
    rw [apply_ite ι, map_one, map_zero]
  have hB : cT c B = B := by
    refine Matrix.ext fun i j => ?_
    show c (if j.val + i.val + 1 = n then 1 else 0) = if i.val + j.val + 1 = n then 1 else 0
    rw [apply_ite c, map_one, map_zero, add_comm j.val]
  have hBB : B * B = 1 := Matrix.map_injective (f := ι) Subtype.val_injective (by
    show (B * B).map ι = (1 : Matrix _ _ _).map ι
    rw [Matrix.map_mul, hBι, GlobalTheory.DualDivU.antiJ_sq, Matrix.map_one _ (map_zero ι) (map_one ι)])
  obtain ⟨p, hp⟩ := GlobalTheory.UnitaryDoubleCoset.exists_poly_norm hc
    (GlobalTheory.T.exists_norm_eq_X_mod_monic_of_adicComplete_involution (v.adicCompletionIntegers K) _ c hc hI hω) hB (IsUnit.of_mul_eq_one _ hBB)
  have h1 : (B * cT c (Polynomial.aeval B p)) * Polynomial.aeval B p = 1 := by rw [Matrix.mul_assoc, hp, hBB]
  refine ⟨bc ι ⟨Polynomial.aeval B p, _, mul_eq_one_comm.1 h1, h1⟩, ⟨_, rfl⟩, ?_⟩
  show cT σ ((Polynomial.aeval B p).map ι) * 1 * (Polynomial.aeval B p).map ι = _
  rw [Matrix.mul_one, GlobalTheory.UnitaryDoubleCoset.cT_map ι (c := c) (fun _ => rfl), ← Matrix.map_mul, hp, hBι]

theorem dc_GU (hU : IsUnramInv ϖ σ q) {g g' : GU σ n} {a b : GL (Fin n) (v.adicCompletion K)}
    (ha : a ∈ GLint (Fin n) (intL (v.adicCompletion K))) (hb : b ∈ GLint (Fin n) (intL (v.adicCompletion K)))
    (e : (g' : GL (Fin n) (v.adicCompletion K)) = a * g * b) : ∃ k₁ ∈ KU σ n, ∃ k₂ ∈ KU σ n, g' = k₁ * g * k₂ := by
  obtain ⟨h, hh, eh⟩ := exists_antiJ_frame hU n
  obtain ⟨k₁, h₁, k₂, h₂, e'⟩ := GlobalTheory.T.unitary_mem_integralUnitary_doubleCoset_of_GLn_doubleCoset K v σ n hU.1 hU.2.1 hU.2.2.2.2.1 _
    (conj_mem_UJ σ (inv_frame σ eh) g.2) _ (conj_mem_UJ σ (inv_frame σ eh) g'.2) (h * a * h⁻¹)
    (mul_mem (mul_mem hh ha) (inv_mem hh)) (h * b * h⁻¹) (mul_mem (mul_mem hh hb) (inv_mem hh)) (by rw [e]; group)
  have m : ∀ k ∈ UJ σ (1 : Matrix (Fin n) (Fin n) (v.adicCompletion K)) ⊓ GLint (Fin n) (Ov K v),
      ∃ k' ∈ KU σ n, (k' : GL (Fin n) (v.adicCompletion K)) = h⁻¹ * k * h := fun k hk =>
    ⟨⟨_, conj_mem_UJ σ eh hk.1⟩, ⟨conj_mem_UJ σ eh hk.1,
      mul_mem (s := GLint (Fin n) (intL (v.adicCompletion K))) (mul_mem (inv_mem hh) hk.2) hh⟩, rfl⟩
  obtain ⟨l₁, m₁, e₁⟩ := m k₁ h₁
  obtain ⟨l₂, m₂, e₂⟩ := m k₂ h₂
  refine ⟨l₁, m₁, l₂, m₂, Subtype.ext ?_⟩
  simp only [Subgroup.coe_mul, e₁, e₂]
  calc (g' : GL (Fin n) (v.adicCompletion K)) = h⁻¹ * (h⁻¹⁻¹ * g' * h⁻¹) * h := by group
    _ = _ := by rw [e']; group

theorem divInd_eq_labInd (hU : IsUnramInv ϖ σ q) {d : List ℤ} (h : Good n d) :
    GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlaces.divInd σ n ϖ d = GlobalTheory.IndefiniteRowSideFullHecke.InertPlaceSetting.labInd σ n ϖ d := by
  funext g
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlaces.divInd GlobalTheory.IndefiniteRowSideFullHecke.InertPlaceSetting.labInd
  split_ifs with hg
  · obtain ⟨k₁, k₂, e⟩ := hg
    obtain ⟨t, ht⟩ := exists_diag hU h
    obtain ⟨l₁, m₁, l₂, m₂, e'⟩ := dc_GU hU (g := t) (g' := g) (a := bc (intL _).subtype k₁)
      (b := bc (intL _).subtype k₂) ⟨k₁, rfl⟩ ⟨k₂, rfl⟩ (Units.ext (by
        simp only [Units.val_mul, ht]
        exact e))
    refine (Set.indicator_of_mem (f := (1 : GU σ n → ℂ)) ?_).symm
    refine ⟨l₁, m₁, l₂, m₂, ?_⟩
    rw [e']
    simp only [Subgroup.coe_mul, Units.val_mul, ht]
  · refine (Set.indicator_of_notMem ?_ _).symm
    rintro ⟨l₁, ⟨-, k₁, e₁⟩, l₂, ⟨-, k₂, e₂⟩, e⟩
    refine hg ⟨k₁, k₂, e.trans ?_⟩
    congr 2
    · exact congrArg Units.val e₁.symm
    · exact congrArg Units.val e₂.symm

theorem good_of_unitary (hU : IsUnramInv ϖ σ q) {π : v.adicCompletion K} (hπ : Valued.v π = WithZero.exp (-1 : ℤ))
    {d : List ℤ} (h1 : d.length = n) (h2 : d.Pairwise fun a b => b ≤ a) {g : GL (Fin n) (v.adicCompletion K)}
    (hg : g ∈ UJ σ (1 : Matrix (Fin n) (Fin n) (v.adicCompletion K)))
    (hd : ∃ k₁ ∈ GLint (Fin n) (Ov K v), ∃ k₂ ∈ GLint (Fin n) (Ov K v),
      g.1 = k₁.1 * Matrix.diagonal (fun i : Fin n => π ^ d.getD i.1 0) * k₂.1) : Good n d := by
  obtain ⟨h, hh, eh⟩ := exists_antiJ_frame hU n
  obtain ⟨k₁, h₁, k₂, h₂, e⟩ := hd
  have h₁' : k₁ ∈ GLint (Fin n) (intL (v.adicCompletion K)) := h₁
  have h₂' : k₂ ∈ GLint (Fin n) (intL (v.adicCompletion K)) := h₂
  obtain ⟨π', hπ', a, ha, b, hb, e'⟩ := GlobalTheory.DualDivU.hasDiv_dualLab _ σ n d _ hU.2.1 h1 (conj_mem_UJ σ eh hg)
    ⟨π, hπ, h⁻¹ * k₁, mul_mem (inv_mem hh) h₁', k₂ * h, mul_mem h₂' hh, by
      simp only [Units.val_mul, e, Matrix.mul_assoc]⟩
  have l1 : (dualLab d).length = n := by simpa [dualLab] using h1
  have l2 : (dualLab d).Pairwise fun a b => b ≤ a := by
    rw [dualLab, List.pairwise_reverse, List.pairwise_map]
    exact h2.imp fun h => neg_le_neg h
  simp only [Units.val_mul, e] at e'
  have ent := fun {x} (hx : x ∈ GLint (Fin n) (intL (v.adicCompletion K))) => GlobalTheory.DualDivU.entry_mem _ hx
  refine ⟨h1, h2, eq_of_getD l1 h1 (congrFun (eq_of_tails fun k => le_antisymm ?_ ?_))⟩
  · refine tail_le hπ' hπ (anti_getD l1 l2) (Matrix.blockTriangular_diagonal _) (fun i => Matrix.diagonal_apply_eq _ _)
      (ent (mul_mem (mul_mem (inv_mem h₁') hh) ha)) (ent (mul_mem (mul_mem hb (inv_mem hh)) (inv_mem h₂'))) ?_ k
    calc _ = (k₁⁻¹).1 * h.1 * ((h⁻¹).1 * (k₁.1 * Matrix.diagonal (fun i : Fin n => π ^ d.getD i.1 0) * k₂.1) * h.1) *
          (h⁻¹).1 * (k₂⁻¹).1 := by
          simp only [Matrix.mul_assoc, Units.inv_mul_cancel_left, Units.mul_inv_cancel_left, Units.mul_inv, Matrix.mul_one]
      _ = _ := by rw [e']; simp only [Units.val_mul, Matrix.mul_assoc]
  · refine tail_le hπ hπ' (anti_getD h1 h2) (Matrix.blockTriangular_diagonal _) (fun i => Matrix.diagonal_apply_eq _ _)
      (ent (mul_mem (mul_mem (inv_mem ha) (inv_mem hh)) h₁')) (ent (mul_mem (mul_mem h₂' hh) (inv_mem hb))) ?_ k
    calc _ = (a⁻¹).1 * (a.1 * Matrix.diagonal (fun i : Fin n => π' ^ (dualLab d).getD i.1 0) * b.1) * (b⁻¹).1 := by
          simp only [Matrix.mul_assoc, Units.inv_mul_cancel_left, Units.mul_inv, Matrix.mul_one]
      _ = _ := by rw [← e']; simp only [Units.val_mul, Matrix.mul_assoc]

end Completion

section Par

open GlobalTheory.IndefiniteRowSideFullHecke.InertPlaceSetting

theorem exists_fun_of_card {m : ℕ} (M : Multiset ℂ) (h : M.card = m) :
    ∃ β : Fin m → ℂ, Finset.univ.val.map β = M := by
  induction M using Quotient.inductionOn with
  | h l =>
    obtain rfl : l.length = m := h
    exact ⟨l.get, by rw [Fin.univ_val_map, List.ofFn_get]; rfl⟩

theorem strPar_eq (q t : ℕ) : strPar q t = GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlaces.strPar q t := by
  simp only [strPar, GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlaces.strPar, Multiset.bind_def, Multiset.pure_def, Multiset.bind_singleton,
    Multiset.map_map, Function.comp_def]

theorem strPar_add_two (q t : ℕ) :
    strPar q (t + 2) = strPar q t + {(q : ℂ) ^ ((t : ℤ) + 1)} + {((q : ℂ) ^ ((t : ℤ) + 1))⁻¹} := by
  rw [strPar_eq, strPar_eq]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlaces.strPar
  have e : Multiset.range (t + 1) = 0 ::ₘ (Multiset.range t).map (· + 1) := by
    show ((List.range (t + 1) : List ℕ) : Multiset ℕ) = _
    rw [List.range_succ_eq_map]
    rfl
  rw [Multiset.range_succ, e, Multiset.map_cons, Multiset.map_cons, Multiset.map_map, ← zpow_neg,
    ← Multiset.singleton_add, ← Multiset.singleton_add]
  have e1 : -(((t + 2 : ℕ) : ℤ) - 1 - 2 * ((t + 1 : ℕ) : ℤ)) = (t : ℤ) + 1 := by push_cast; ring
  have e2 : -(((t + 2 : ℕ) : ℤ) - 1 - 2 * ((0 : ℕ) : ℤ)) = -((t : ℤ) + 1) := by push_cast; ring
  rw [e1, e2, Multiset.map_congr rfl (g := fun l : ℕ => (q : ℂ) ^ (-((t : ℤ) - 1 - 2 * (l : ℤ)))) fun l _ => by
    simp only [Function.comp]
    congr 1
    push_cast
    ring]
  abel

theorem strPar_split {q : ℕ} (hq : q ≠ 0) (t : ℕ) : ∃ H : Multiset ℂ, H.card = t / 2 ∧ (0 : ℂ) ∉ H ∧
    strPar q t = H + H.map (·⁻¹) + if Odd t then {1} else 0 := by
  induction t using Nat.twoStepInduction with
  | zero => exact ⟨0, rfl, by simp, by simp [strPar]⟩
  | one => exact ⟨0, rfl, by simp, by simp [strPar]⟩
  | more t ih _ =>
    obtain ⟨H, h1, h2, h3⟩ := ih
    refine ⟨H + {(q : ℂ) ^ ((t : ℤ) + 1)}, by simp [h1], ?_, ?_⟩
    · rw [Multiset.mem_add, Multiset.mem_singleton]
      exact fun h => h.elim h2 (zpow_ne_zero _ (Nat.cast_ne_zero.2 hq)).symm
    · rw [strPar_add_two, h3, Multiset.map_add, Multiset.map_singleton]
      simp only [Nat.odd_add, Nat.not_odd_iff_even.2 even_two, even_two, iff_true]
      abel

theorem exists_partner {q : ℕ} (hq : q ≠ 0) (a t : ℕ) (α : Fin (a / 2) → ℂ) (hα : ∀ l, α l ≠ 0) :
    ∃ β : Fin ((a + t) / 2) → ℂ, (∀ l, β l ≠ 0) ∧ twPar (a + t) a β = twPar a (a + t) α + strPar q t := by
  obtain ⟨H, h1, h2, h3⟩ := strPar_split hq t
  obtain ⟨β, hβ⟩ := exists_fun_of_card (m := (a + t) / 2)
    ((Finset.univ.val.map α).map (fun z => (-1) ^ t * z) + H.map (fun z => (-1) ^ a * z) +
      if Odd a ∧ Odd t then {-1} else 0) (by
    simp only [Multiset.card_add, Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin, h1,
      Nat.odd_iff]
    split_ifs with h
    · rw [Multiset.card_singleton]; omega
    · rw [Multiset.card_zero]; omega)
  refine ⟨β, fun l h0 => ?_, ?_⟩
  · have : (0 : ℂ) ∈ Finset.univ.val.map β := Multiset.mem_map.2 ⟨l, Finset.mem_univ_val l, h0⟩
    rw [hβ] at this
    simp only [Multiset.mem_add, Multiset.mem_map, mul_eq_zero, pow_eq_zero_iff', neg_eq_zero, one_ne_zero,
      false_and, false_or] at this
    rcases this with (⟨_, ⟨l, -, rfl⟩, h⟩ | ⟨_, h, rfl⟩) | h
    · exact hα l h
    · exact h2 h
    · split_ifs at h <;> simp at h
  · have e : ∀ {m : ℕ} (γ : Fin m → ℂ),
        Finset.univ.val.map (fun l => (γ l)⁻¹) = (Finset.univ.val.map γ).map (·⁻¹) := fun γ => by
      rw [Multiset.map_map]; rfl
    unfold twPar bcPar
    rw [e, e, hβ, h3]
    generalize Finset.univ.val.map α = A
    rcases Nat.even_or_odd a with ha | ha <;> rcases Nat.even_or_odd t with ht | ht <;>
      simp [pow_add, ha, ht, Nat.odd_add, Nat.not_odd_iff_even.2, Nat.not_even_iff_odd.2, Even.neg_one_pow,
        Odd.neg_one_pow, Multiset.map_map, inv_neg] <;>
      (try simp only [← Multiset.singleton_add]) <;> abel

end Par

end GlobalTheory.InertThetaCompare

end
