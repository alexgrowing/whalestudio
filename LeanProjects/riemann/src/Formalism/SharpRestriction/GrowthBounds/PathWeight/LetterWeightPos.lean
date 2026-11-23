import Formalism.SharpRestriction.GrowthBounds.PathWeight.GeneratorImageIsSymbol

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.G.symbolGeneratorData

open Formalism.MainNotions.G Formalism.MainNotions.SourceCleaning Formalism.MainNotions.G.WittFrameLocaliserOrders

section Low

variable {R σ : Type*} [CommRing R] (wt : σ → ℕ)

theorem weighted_component_mul_lowest {f g : MvPolynomial σ R} {a b : ℕ}
    (hf : ∀ m ∈ f.support, a ≤ Finsupp.weight wt m) (hg : ∀ m ∈ g.support, b ≤ Finsupp.weight wt m) :
    weightedHomogeneousComponent wt (a + b) (f * g) =
      weightedHomogeneousComponent wt a f * weightedHomogeneousComponent wt b g := by
  ext m
  rw [coeff_weightedHomogeneousComponent, coeff_mul, coeff_mul]
  split_ifs with h
  · refine Finset.sum_congr rfl fun x hx => ?_
    rw [coeff_weightedHomogeneousComponent, coeff_weightedHomogeneousComponent]
    have hx' : x.1 + x.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
    have hw : Finsupp.weight wt x.1 + Finsupp.weight wt x.2 = a + b := by rw [← map_add, hx', h]
    by_cases h1 : coeff x.1 f = 0
    · simp [h1]
    by_cases h2 : coeff x.2 g = 0
    · simp [h2]
    have e1 := hf x.1 (mem_support_iff.2 h1)
    have e2 := hg x.2 (mem_support_iff.2 h2)
    rw [if_pos (by omega), if_pos (by omega)]
  · symm
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [coeff_weightedHomogeneousComponent, coeff_weightedHomogeneousComponent]
    have hx' : x.1 + x.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
    by_cases h1 : Finsupp.weight wt x.1 = a
    · by_cases h2 : Finsupp.weight wt x.2 = b
      · exact absurd (by rw [← hx', map_add, h1, h2]) h
      · simp [h2]
    · simp [h1]

theorem support_weight_mul_lower {f g : MvPolynomial σ R} {a b : ℕ}
    (hf : ∀ m ∈ f.support, a ≤ Finsupp.weight wt m) (hg : ∀ m ∈ g.support, b ≤ Finsupp.weight wt m) :
    ∀ m ∈ (f * g).support, a + b ≤ Finsupp.weight wt m := by
  intro m hm
  obtain ⟨m1, h1, m2, h2, rfl⟩ := Finset.mem_add.1 (MvPolynomial.support_mul f g hm)
  rw [map_add]
  exact Nat.add_le_add (hf m1 h1) (hg m2 h2)

theorem weighted_component_prod_lowest {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ R) (o : ι → ℕ)
    (hf : ∀ c ∈ s, ∀ m ∈ (f c).support, o c ≤ Finsupp.weight wt m) :
    (∀ m ∈ (∏ c ∈ s, f c).support, ∑ c ∈ s, o c ≤ Finsupp.weight wt m) ∧
    weightedHomogeneousComponent wt (∑ c ∈ s, o c) (∏ c ∈ s, f c) =
      ∏ c ∈ s, weightedHomogeneousComponent wt (o c) (f c) := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨fun m _ => by simp, ?_⟩
    simp only [Finset.sum_empty, Finset.prod_empty]
    exact (isWeightedHomogeneous_one R wt).weightedHomogeneousComponent_same
  | insert c s hc ih =>
    obtain ⟨ih1, ih2⟩ := ih fun c' hc' => hf c' (Finset.mem_insert_of_mem hc')
    have h0 := hf c (Finset.mem_insert_self c s)
    rw [Finset.sum_insert hc, Finset.prod_insert hc, Finset.prod_insert hc]
    exact ⟨support_weight_mul_lower wt h0 ih1, by rw [weighted_component_mul_lowest wt h0 ih1, ih2]⟩

end Low

theorem depth_filtration_rename {O : Type*} [CommRing O] [IsDomain O] {σ τ : Type*} {w : O} (f : σ → τ)
    {P : MvPolynomial σ (KK O)} {j : ℕ} (hP : InWj w P j) : InWj w (rename f P) j := by
  have h : rename f P = ∑ m ∈ P.support, rename f (monomial m (coeff m P)) := by
    conv_lhs => rw [P.as_sum]
    rw [map_sum]
  rw [h]
  refine inWj_sum _ _ fun m _ => ?_
  rw [rename_monomial]
  intro m'
  obtain ⟨c, hc⟩ := hP m
  rw [coeff_monomial]
  split_ifs
  · exact ⟨c, hc⟩
  · exact ⟨0, by simp⟩

section Rho

variable {n' r : ℕ} [NeZero n'] (F : Frames n' r) (j : ℤ)

def rho (k : ℕ) : Fin (Mj F j) × Fin k → TV n' k := fun v => (posOf n' (eL F j v.1), v.2)

theorem letter_enum_mem_letters (i : Fin (Mj F j)) : eL F j i ∈ F.letters j := Finset.orderEmbOfFin_mem _ _ _

theorem letter_enum_position_top (i : Fin (Mj F j)) : posOf n' (eL F j i) ∈ F.TT :=
  (Finset.mem_filter.1 (letter_enum_mem_letters F j i)).2

theorem letter_enum_lower_bound (i : Fin (Mj F j)) : F.fr (j - 1) 0 ≤ eL F j i :=
  (Finset.mem_Icc.1 (Finset.mem_filter.1 (letter_enum_mem_letters F j i)).1).1

theorem letter_enum_upper_bound (i : Fin (Mj F j)) : eL F j i ≤ F.fr j (r - 1) :=
  (Finset.mem_Icc.1 (Finset.mem_filter.1 (letter_enum_mem_letters F j i)).1).2

theorem letter_enum_strictMono : StrictMono (eL F j) := (Finset.orderEmbOfFin (F.letters j) rfl).strictMono

theorem rename_supported_tops {R : Type*} [CommRing R] {k : ℕ} (P : MvPolynomial (Fin (Mj F j) × Fin k) R) :
    OnTops F (rename (rho F j k) P) := by
  intro v hv
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.1 (vars_rename (rho F j k) P hv)
  exact letter_enum_position_top F j u.1

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [Algebra (WF p n') O] {k : ℕ}

theorem substitution_rename_lift (w : O) (hn : Even n') (g : Matrix (Fin k) (Fin k) (WF p n'))
    (P : MvPolynomial (Fin (Mj F j) × Fin k) (KK O)) :
    subst p n' O w n' r g (rename (rho F j k) P) = rename (rho F j k) (liftSubst p n' O w r (LLs F j) g P) := by
  have h : (subst p n' O w n' r g).comp (rename (rho F j k)) =
      (rename (rho F j k)).comp (liftSubst p n' O w r (LLs F j) g) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [AlgHom.comp_apply, rename_X]
    unfold subst liftSubst
    rw [aeval_X, aeval_X]
    have hs : sigMat p n' O g ((LLT n').pos (rho F j k v).1) = sigMat p n' O g ((LLs F j).pos v.1) :=
      sigMat_posOf g (eL F j v.1)
    rw [hs]
    by_cases hE : Even (eL F j v.1)
    · have hE' : Even (posOf n' (eL F j v.1)).val := (posOf_even hn _).2 hE
      have h1 : (LLT n').vec (rho F j k v).1 = true := by simp [LLT, rho, hE']
      have h2 : (LLs F j).vec v.1 = true := by simp [LLs, hE]
      rw [if_pos h1, if_pos h2, map_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [map_mul, rename_C]
      split_ifs <;> simp [rho]
    · have hE' : ¬ Even (posOf n' (eL F j v.1)).val := fun h => hE ((posOf_even hn _).1 h)
      have h1 : ¬ (LLT n').vec (rho F j k v).1 = true := by simp [LLT, rho, hE']
      have h2 : ¬ (LLs F j).vec v.1 = true := by simp [LLs, hE]
      rw [if_neg h1, if_neg h2, map_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [map_mul, rename_C]
      split_ifs <;> simp [rho]
  exact AlgHom.congr_fun h P

end Rho

section Ph

variable {n' r : ℕ} [NeZero n'] (F : Frames n' r) (j : ℤ) (p : ℕ)

def omL (i : Fin (Mj F j)) : ℕ := p ^ (F.fr j (r - 1) - eL F j i).toNat

theorem letter_weight_strictAnti (hp : 1 < p) : StrictAnti (omL F j p) := by
  intro a b hab
  unfold omL
  apply Nat.pow_lt_pow_right hp
  have h1 := letter_enum_strictMono F j hab
  have h2 := letter_enum_upper_bound F j b
  omega

theorem letter_weight_pos (hp : 1 < p) (i : Fin (Mj F j)) : 0 < omL F j p i := pow_pos (by omega) _

variable (K : ℕ)

theorem normal_iff_letter_column (hn : Even n') (v : Fin (Mj F j) × Fin (r + K)) :
    (((LLs F j).toLetters.vec v.1 = true ∧ r ≤ v.2.val) ∨ ((LLs F j).toLetters.vec v.1 = false ∧ v.2.val < r)) ↔
      IsNormal r (rho F j (r + K) v) := by
  by_cases hE : Even (eL F j v.1)
  · have hE' : Even (posOf n' (eL F j v.1)).val := (posOf_even hn _).2 hE
    have h2 : (LLs F j).toLetters.vec v.1 = true := by simp [LLs, hE]
    have h3 : IsNormal r (rho F j (r + K) v) ↔ r ≤ v.2.val := by
      show (if Even (posOf n' (eL F j v.1)).val then r ≤ v.2.val else v.2.val < r) ↔ _
      rw [if_pos hE']
    rw [h3, h2]
    simp
  · have hE' : ¬ Even (posOf n' (eL F j v.1)).val := fun h => hE ((posOf_even hn _).1 h)
    have h2 : (LLs F j).toLetters.vec v.1 = false := by simp [LLs, hE]
    have h3 : IsNormal r (rho F j (r + K) v) ↔ v.2.val < r := by
      show (if Even (posOf n' (eL F j v.1)).val then r ≤ v.2.val else v.2.val < r) ↔ _
      rw [if_neg hE']
    rw [h3, h2]
    simp

theorem symbol_weight_factor (hn : Even n') (v : Fin (Mj F j) × Fin (r + K)) :
    symWt (r := r) (K := K) (LLs F j).toLetters (omL F j p) v =
      omL F j p v.1 * normalVariableWeight n' (r + K) r (rho F j (r + K) v) := by
  unfold symWt normalVariableWeight
  by_cases hN : IsNormal r (rho F j (r + K) v)
  · rw [if_pos ((normal_iff_letter_column F j K hn v).2 hN), if_pos hN, mul_one]
  · rw [if_neg (fun h => hN ((normal_iff_letter_column F j K hn v).1 h)), if_neg hN, mul_zero]

variable (O : Type) [CommRing O]

theorem segment_substitution_aeval (Y : MvPolynomial (Fin (Mj F j) × Fin (r + K)) O) :
    phSeg O K p F j (plnm F j O K Y) =
      aeval (fun v => (X (rho F j (r + K) v) : RRing O n' (r + K)) ^ omL F j p v.1) Y := by
  unfold phSeg plnm
  rw [aeval_rename]
  rfl

theorem segment_substitution_weighted_homog (hn : Even n') (Y : MvPolynomial (Fin (Mj F j) × Fin (r + K)) O) (o : ℕ)
    (hY : IsWeightedHomogeneous (symWt (r := r) (K := K) (LLs F j).toLetters (omL F j p)) Y o) :
    IsWeightedHomogeneous (normalVariableWeight n' (r + K) r) (phSeg O K p F j (plnm F j O K Y)) o := by
  rw [segment_substitution_aeval]
  have h : aeval (fun v => (X (rho F j (r + K) v) : RRing O n' (r + K)) ^ omL F j p v.1) Y =
      ∑ m ∈ Y.support,
        aeval (fun v => (X (rho F j (r + K) v) : RRing O n' (r + K)) ^ omL F j p v.1) (monomial m (coeff m Y)) := by
    conv_lhs => rw [Y.as_sum]
    rw [map_sum]
  rw [h]
  refine IsWeightedHomogeneous.sum _ _ _ fun m hm => ?_
  rw [aeval_monomial]
  have hw : Finsupp.weight (symWt (r := r) (K := K) (LLs F j).toLetters (omL F j p)) m = o :=
    hY (mem_support_iff.1 hm)
  have hC : algebraMap O (RRing O n' (r + K)) (coeff m Y) = C (coeff m Y) := rfl
  rw [hC]
  apply IsWeightedHomogeneous.C_mul
  rw [← hw, Finsupp.weight_apply, Finsupp.sum, Finsupp.prod]
  refine IsWeightedHomogeneous.prod _ _ _ fun v _ => ?_
  have h1 := ((isWeightedHomogeneous_X O (normalVariableWeight n' (r + K) r) (rho F j (r + K) v)).pow (omL F j p v.1)).pow (m v)
  have e : m v • symWt (r := r) (K := K) (LLs F j).toLetters (omL F j p) v =
      m v • (omL F j p v.1 • normalVariableWeight n' (r + K) r (rho F j (r + K) v)) := by
    rw [symbol_weight_factor F j p K hn v]; rfl
  rw [e]
  exact h1

variable {O} [IsDomain O] [Fact p.Prime]

theorem segment_substitution_eq_rename (Y : MvPolynomial (Fin (Mj F j) × Fin (r + K)) O) :
    MvPolynomial.map (algebraMap O (KK O)) (phSeg O K p F j (plnm F j O K Y)) =
      rename (rho F j (r + K)) (powSubst p (LLs F j) (F.fr j (r - 1)) Y) := by
  rw [segment_substitution_aeval]
  induction Y using MvPolynomial.induction_on with
  | C a =>
    have e1 : aeval (fun v => (X (rho F j (r + K) v) : RRing O n' (r + K)) ^ omL F j p v.1)
        (C a : MvPolynomial (Fin (Mj F j) × Fin (r + K)) O) = C a := by
      rw [aeval_C]; rfl
    have e2 : powSubst p (LLs F j) (F.fr j (r - 1)) (C a : MvPolynomial (Fin (Mj F j) × Fin (r + K)) O) =
        C (algebraMap O (KK O) a) := by
      unfold powSubst; rw [aeval_C]; rfl
    rw [e1, e2, map_C, rename_C]
  | add P Q hP hQ =>
    simp only [map_add, hP, hQ]
  | mul_X P v hP =>
    simp only [map_mul]
    rw [hP]
    congr 1
    have e2 : powSubst p (LLs F j) (F.fr j (r - 1)) (X v : MvPolynomial (Fin (Mj F j) × Fin (r + K)) O) =
        X v ^ omL F j p v.1 := by
      unfold powSubst; rw [aeval_X]; rfl
    rw [aeval_X, e2, map_pow, map_pow, map_X, rename_X]

end Ph

section Main

variable {p n' r K : ℕ} [Fact p.Prime] [NeZero n'] [NeZero r] [NeZero K] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra (WF p n') O] (Cx : Ctx p n' r K O) (j : ℤ)

theorem segment_letter_count_pos : 0 < Mj Cx.Fr j := by
  have hr : 1 ≤ r := NeZero.one_le
  apply Finset.card_pos.2
  refine ⟨Cx.Fr.fr j (r - 1), Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨?_, le_rfl⟩,
    (Cx.hV.2.2.2.2.1 j (r - 1) (by omega)).1⟩⟩
  have h1 := frame_row_monotone Cx.Fr Cx.L₁ Cx.N₁ Cx.hV (j - 1) (r - 1) (by omega)
  have h2 := Cx.hV.2.2.2.1 (j - 1)
  have h3 := frame_row_monotone Cx.Fr Cx.L₁ Cx.N₁ Cx.hV j (r - 1) (by omega)
  rw [sub_add_cancel] at h2
  omega

theorem segment_count_add_rank_le : Mj Cx.Fr j + r ≤ K := by
  have h1 : (Cx.Fr.letters j).card ≤ Cx.N₁ := Cx.hV.2.2.2.2.2.2.2.1 j
  have h2 := Cx.hK
  show (Cx.Fr.letters j).card + r ≤ K
  omega

include Cx in
theorem one_lt_prime : 1 < p := by
  have := Cx.hH.1
  omega

def keyLeadingPart (mu : Fin (Mj Cx.Fr j + 1) → Fin (r + K) → ℤ) (c : ℤ) (J : Finset (Fin (r + K))) :
    MvPolynomial (TV n' (r + K)) (KK O) :=
  C (algebraMap O (KK O) (Cx.S.w ^ oc (omL Cx.Fr j p) mu c)) *
    MvPolynomial.map (algebraMap O (KK O)) (phSeg O K p Cx.Fr j (plnm Cx.Fr j O K (plTanCol O mu c J)))

theorem key_column_leading_bound (D : Formalism.BasicNotions.D7) (hB2 : admB2 D) (hC1 : CoefficientValuationLemma D) (B : Fin (Mj Cx.Fr j) → ℕ)
    (Pth : PPath (r + K) (Mj Cx.Fr j) (LLs Cx.Fr j).toLetters B) (c : ℤ) (J : Finset (Fin (r + K))) :
    bc_KP Cx.S.w Cx.Fr Cx.Q Cx.g (keyLeadingPart Cx j Pth.mu c J) (oc (omL Cx.Fr j p) Pth.mu c) := by
  have : NeZero (Mj Cx.Fr j) := ⟨(segment_letter_count_pos Cx j).ne'⟩
  have hn : Even n' := Cx.hH.2.2.2.2
  have hp5 : 5 ≤ p := by have := Cx.hH.1; omega
  have hn1 : 1 ≤ n' := NeZero.one_le
  obtain ⟨hA, _, hord, htail, hle⟩ := hC1 p n' O Cx.S hp5 hn1 Cx.hO.1 (Mj Cx.Fr j) r K (LLs Cx.Fr j) B
    (Cx.Fr.fr j (r - 1)) (segment_count_add_rank_le Cx j) (letter_enum_strictMono Cx.Fr j).monotone (letter_enum_upper_bound Cx.Fr j) Pth Cx.g Cx.hg c
    (fun i i' hii _ _ => letter_enum_strictMono Cx.Fr j hii) J
  obtain ⟨_, hcomp⟩ := hB2 p O Cx.S (Mj Cx.Fr j) r K (LLs Cx.Fr j).toLetters B (omL Cx.Fr j p) (segment_count_add_rank_le Cx j)
    (letter_weight_strictAnti Cx.Fr j p (one_lt_prime Cx)) (letter_weight_pos Cx.Fr j p (one_lt_prime Cx)) Pth c J
  have hWH : IsWeightedHomogeneous (symWt (r := r) (K := K) (LLs Cx.Fr j).toLetters (omL Cx.Fr j p))
      (plTanCol O Pth.mu c J) (oc (omL Cx.Fr j p) Pth.mu c) := by
    rw [← hcomp]; exact weightedHomogeneousComponent_isWeightedHomogeneous _ _
  have htail' : InWj Cx.S.w (liftSubst p n' O Cx.S.w r (LLs Cx.Fr j) Cx.g
      (KKc p n' (O := O) (LLs Cx.Fr j) Cx.g (Cx.Fr.fr j (r - 1)) Pth.mu c J) -
        C (algebraMap O (KK O) Cx.S.w ^ oc (omL Cx.Fr j p) Pth.mu c) *
          powSubst p (LLs Cx.Fr j) (Cx.Fr.fr j (r - 1)) (plTanCol O Pth.mu c J))
      (oc (omL Cx.Fr j p) Pth.mu c + 1) := htail
  have hle' : oc (omL Cx.Fr j p) Pth.mu c ≤ 2 * p ^ (Cx.Fr.fr j (r - 1) - eL Cx.Fr j 0).toNat := hle
  have hord' : ∀ g' : Matrix (Fin (r + K)) (Fin (r + K)) (WF p n'), IsGLW g' →
      InWj Cx.S.w (liftSubst p n' O Cx.S.w r (LLs Cx.Fr j) g'
        (KKc p n' (O := O) (LLs Cx.Fr j) Cx.g (Cx.Fr.fr j (r - 1)) Pth.mu c J)) (oc (omL Cx.Fr j p) Pth.mu c) :=
    fun g' hg' => hord g' hg'
  have hka0 : keyLeadingPart Cx j Pth.mu c J = rename (rho Cx.Fr j (r + K))
      (C (algebraMap O (KK O) Cx.S.w ^ oc (omL Cx.Fr j p) Pth.mu c) *
          powSubst p (LLs Cx.Fr j) (Cx.Fr.fr j (r - 1)) (plTanCol O Pth.mu c J)) := by
    unfold keyLeadingPart
    rw [map_mul (rename (rho Cx.Fr j (r + K))), rename_C, segment_substitution_eq_rename, map_pow]
  refine isKeyProduct_of_isKey Cx.S.w Cx.Fr Cx.Q Cx.g
    (ka := rename (rho Cx.Fr j (r + K)) (KKc p n' (O := O) (LLs Cx.Fr j) Cx.g (Cx.Fr.fr j (r - 1)) Pth.mu c J))
    ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ (rename_supported_tops Cx.Fr j _) ?_
  · exact (inA_iff_inWj0 (w := Cx.S.w) _).2 (depth_filtration_rename _ ((inA_iff_inWj0 (w := Cx.S.w) _).1 hA))
  · have h1 := Cx.hG j
    unfold zF at h1
    have h2 := letter_enum_lower_bound Cx.Fr j 0
    have h3 : (Cx.Fr.fr j (r - 1) - eL Cx.Fr j 0).toNat ≤ Cx.G' := by omega
    have h4 : p ^ (Cx.Fr.fr j (r - 1) - eL Cx.Fr j 0).toNat ≤ p ^ Cx.G' :=
      Nat.pow_le_pow_right (by have := one_lt_prime Cx; omega) h3
    unfold Ctx.Q
    omega
  · exact leading_part_normal_degree r _ _ _ (segment_substitution_weighted_homog Cx.Fr j p K O hn _ _ hWH)
  · have h1 := inWj_mul (inWj_Cpow (σ := TV n' (r + K)) (w := Cx.S.w) (oc (omL Cx.Fr j p) Pth.mu c))
      (inWj_map (w := Cx.S.w) (phSeg O K p Cx.Fr j (plnm Cx.Fr j O K (plTanCol O Pth.mu c J))))
    rw [add_zero] at h1
    exact h1
  · rw [hka0, substitution_rename_lift Cx.Fr j Cx.S.w hn, ← map_sub]
    exact depth_filtration_rename _ htail'
  · intro g' hg'
    show InWj Cx.S.w (subst p n' O Cx.S.w n' r g' _) _
    rw [substitution_rename_lift Cx.Fr j Cx.S.w hn]
    exact depth_filtration_rename _ (hord' g' hg')
  · rw [hka0]
    exact rename_supported_tops Cx.Fr j _

theorem key_polynomial_leading_part (D : Formalism.BasicNotions.D7) (hB2 : admB2 D) (hC1 : CoefficientValuationLemma D) (B : Fin (Mj Cx.Fr j) → ℕ)
    (Pth : PPath (r + K) (Mj Cx.Fr j) (LLs Cx.Fr j).toLetters B) (I : ℤ → Finset (Fin (r + K))) (s : Finset ℤ) :
    bc_KP Cx.S.w Cx.Fr Cx.Q Cx.g
      (C (algebraMap O (KK O) (Cx.S.w ^ ∑ c ∈ s, oc (omL Cx.Fr j p) Pth.mu c)) *
        MvPolynomial.map (algebraMap O (KK O))
          (phSeg O K p Cx.Fr j (plnm Cx.Fr j O K (∏ c ∈ s, plTanCol O Pth.mu c (I c)))))
      (∑ c ∈ s, oc (omL Cx.Fr j p) Pth.mu c) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, Finset.prod_empty, pow_zero, map_one, mul_one]
    exact isKeyProduct_one Cx.S.w Cx.Fr Cx.Q Cx.g
  | insert c s hc ih =>
    rw [Finset.sum_insert hc, Finset.prod_insert hc]
    have e : C (algebraMap O (KK O) (Cx.S.w ^ (oc (omL Cx.Fr j p) Pth.mu c + ∑ c ∈ s, oc (omL Cx.Fr j p) Pth.mu c))) *
        MvPolynomial.map (algebraMap O (KK O))
          (phSeg O K p Cx.Fr j (plnm Cx.Fr j O K (plTanCol O Pth.mu c (I c) * ∏ c ∈ s, plTanCol O Pth.mu c (I c)))) =
        keyLeadingPart Cx j Pth.mu c (I c) *
        (C (algebraMap O (KK O) (Cx.S.w ^ ∑ c ∈ s, oc (omL Cx.Fr j p) Pth.mu c)) *
        MvPolynomial.map (algebraMap O (KK O))
          (phSeg O K p Cx.Fr j (plnm Cx.Fr j O K (∏ c ∈ s, plTanCol O Pth.mu c (I c))))) := by
      unfold keyLeadingPart
      rw [pow_add]
      simp only [map_mul]
      ring
    rw [e]
    exact isKeyProduct_mul (key_column_leading_bound Cx j D hB2 hC1 B Pth c (I c)) ih

end Main

theorem generator_path_homogeneous_holds (D : Formalism.BasicNotions.D7) (hB2 : Formalism.MainNotions.SourceCleaning.admB2 D) (hB3 : Formalism.MainNotions.SourceCleaning.admB3 D)
    (hC1 : Formalism.MainNotions.SourceCleaning.CoefficientValuationLemma D) : GeneratorImageIsSymbol := by
  intro p n' r K _ _ _ _ O _ _ _ _ Cx j P hP
  obtain ⟨B, Pth, nu, ka, I', I'', hmu, hI', hI'', rfl⟩ := hP
  have hn : Even n' := Cx.hH.2.2.2.2
  obtain ⟨_, h3, _⟩ := hB3 p O Cx.S (Mj Cx.Fr j) r K (LLs Cx.Fr j).toLetters B (omL Cx.Fr j p) (segment_count_add_rank_le Cx j)
    (letter_weight_strictAnti Cx.Fr j p (one_lt_prime Cx)) (letter_weight_pos Cx.Fr j p (one_lt_prime Cx)) {(nu, ka)}
    (by
      intro q hq
      rw [Set.mem_singleton_iff] at hq
      subst hq
      exact ⟨Pth, hmu⟩)
  obtain ⟨I, _, hI⟩ := h3 (nu, ka) (Set.mem_singleton _) I' I'' hI' hI''
  have hI2 : weightedHomogeneousComponent (symWt (r := r) (K := K) (LLs Cx.Fr j).toLetters (omL Cx.Fr j p))
      (∑ c ∈ colRange Pth.mu, oc (omL Cx.Fr j p) Pth.mu c) (Psi O Pth.mu I) =
        PsiPl O nu I' * PsiTan O ka I'' := by
    rw [hmu]; exact hI
  have hb2 := fun c : ℤ => hB2 p O Cx.S (Mj Cx.Fr j) r K (LLs Cx.Fr j).toLetters B (omL Cx.Fr j p) (segment_count_add_rank_le Cx j)
    (letter_weight_strictAnti Cx.Fr j p (one_lt_prime Cx)) (letter_weight_pos Cx.Fr j p (one_lt_prime Cx)) Pth c (I c)
  have hprod := (weighted_component_prod_lowest (symWt (r := r) (K := K) (LLs Cx.Fr j).toLetters (omL Cx.Fr j p)) (colRange Pth.mu)
    (fun c => Kcol O Pth.mu c (Mj Cx.Fr j) (I c)) (fun c => oc (omL Cx.Fr j p) Pth.mu c)
    (fun c _ => (hb2 c).1)).2
  have hPsi : PsiPl O nu I' * PsiTan O ka I'' = ∏ c ∈ colRange Pth.mu, plTanCol O Pth.mu c (I c) := by
    rw [← hI2]
    unfold Psi
    rw [hprod]
    exact Finset.prod_congr rfl fun c _ => (hb2 c).2
  refine ⟨∑ c ∈ colRange Pth.mu, oc (omL Cx.Fr j p) Pth.mu c, ?_, ?_⟩
  · have hWH : IsWeightedHomogeneous (symWt (r := r) (K := K) (LLs Cx.Fr j).toLetters (omL Cx.Fr j p))
        (PsiPl O nu I' * PsiTan O ka I'') (∑ c ∈ colRange Pth.mu, oc (omL Cx.Fr j p) Pth.mu c) := by
      rw [← hI2]; exact weightedHomogeneousComponent_isWeightedHomogeneous _ _
    have h1 := leading_part_normal_degree r _ (1 : KK O) _ (segment_substitution_weighted_homog Cx.Fr j p K O hn _ _ hWH)
    rw [C_1, one_mul] at h1
    exact h1
  · rw [hPsi]
    exact AddSubmonoid.subset_closure
      ⟨_, 1, key_polynomial_leading_part Cx j D hB2 hC1 B Pth I (colRange Pth.mu), bc_IT_one, (mul_one _).symm⟩

end Formalism.MainNotions.G.symbolGeneratorData
