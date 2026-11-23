import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyCN
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialQuotDim
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMinimalPrimeMultiHomog
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSupSpanMultiHomog
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PLocCyclePos

namespace BaseChangeColon.BC

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

theorem dim_mono {A : Type} [CommRing A] {I I' : Ideal A} (h : I ≤ I') :
    ringKrullDim (A ⧸ I') ≤ ringKrullDim (A ⧸ I) :=
  ringKrullDim_le_of_surjective (Ideal.Quotient.factor h) (Ideal.Quotient.factor_surjective h)

theorem dim_drop {A : Type} [CommRing A] {P : Ideal A} (hP : P.IsPrime) {f : A} (hf : f ∉ P) :
    ringKrullDim (A ⧸ (P ⊔ Ideal.span {f})) + 1 ≤ ringKrullDim (A ⧸ P) :=
  ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor le_sup_left)
    (Ideal.Quotient.factor_surjective le_sup_left) (r := Ideal.Quotient.mk P f)
    (mem_nonZeroDivisors_of_ne_zero fun h => hf (Ideal.Quotient.eq_zero_iff_mem.1 h))
    (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f)))

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in
theorem of_idealCycle_ne {R : Type} [CommRing R] {J W : Ideal (MRing ι R)} (h : idealCycle J W ≠ 0) :
    W ∈ J.minimalPrimes ∧ IsRelevant W := by
  by_contra h'
  exact h (dif_neg h')

omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in
theorem cycEval_eq_zero {R : Type} [CommRing R] {J : Ideal (MRing ι R)} {n : Ideal (MRing ι R) → ℤ}
    (h : ∀ W ∈ J.minimalPrimes, n W = 0) : cycEval n (idealCycle J) = 0 := by
  refine finsum_eq_zero_of_forall_eq_zero fun W => ?_
  by_cases h0 : idealCycle J W = 0
  · rw [h0, zero_mul]
  · rw [h W (of_idealCycle_ne h0).1, mul_zero]

theorem lt_succ_dim {a : WithBot ℕ∞} {d c : ℕ} (h : a < ((d + c : ℕ) : WithBot ℕ∞)) :
    a < ((d + 1 + c : ℕ) : WithBot ℕ∞) :=
  lt_of_lt_of_le h (by exact_mod_cast (by omega : d + c ≤ d + 1 + c))

theorem intNum_small {F : Type} [Field F] {d : ℕ} {I : Ideal (MRing ι F)} (hI : IsMultiHomogIdeal I)
    (hd : ringKrullDim (MRing ι F ⧸ I) < ((d + Fintype.card K : ℕ) : WithBot ℕ∞))
    (bs : Fin d → K → ℤ) : intNum F I bs = 0 := by
  rw [IntNumAssoc.full F K ι d I hI (lt_succ_dim hd) bs]
  exact cycEval_eq_zero fun W hW => IntNumVanish.full F K ι d W hW.1.1
    (MinimalPrimeMultiHomog.proof F K ι I W hI hW) (Or.inr ((dim_mono hW.1.2).trans_lt hd)) bs

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}

def NN (J : Ideal (MRing ι O)) {d : ℕ} (bs : Fin d → K → ℤ) : ℤ :=
  cycEval (fun W => vNum W bs) (idealCycle J)

omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in
theorem special_sup (hϖ : Irreducible ϖ) (J : Ideal (MRing ι O)) :
    specialIdeal (J ⊔ Ideal.span {C ϖ}) = specialIdeal J := by
  unfold specialIdeal
  rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, map_C,
    (IsLocalRing.residue_eq_zero_iff ϖ).2 hϖ.not_isUnit, C_0, Ideal.span_singleton_zero, sup_bot_eq]

theorem homog_C (c : O) : IsMultiHomog (C c : MRing ι O) 0 := isWeightedHomogeneous_C _ _

theorem NN_vert (hϖ : Irreducible ϖ) {d : ℕ} {J : Ideal (MRing ι O)} (hJ : IsMultiHomogIdeal J)
    (hd : ringKrullDim (MRing ι O ⧸ J) < ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞))
    (hm : C ϖ ∈ J) (bs : Fin d → K → ℤ) :
    NN J bs = intNum (IsLocalRing.ResidueField O) (specialIdeal J) bs := by
  have h1 := SpecialCycleEval.full O ϖ hϖ K ι J
    (fun V => intNum (IsLocalRing.ResidueField O) V bs)
  rw [divCycle_eq_idealCycle, sup_eq_left.2 ((Ideal.span_singleton_le_iff_mem _).2 hm)] at h1
  rw [IntNumAssoc.full _ K ι d _ (SpecialIdealMultiHomog.full O K ι J hJ)
    (by rw [SpecialQuotDim.proof O ϖ hϖ K ι J hm]; exact hd) bs, ← h1]
  rfl

theorem key (hϖ : Irreducible ϖ) {d : ℕ} {W : Ideal (MRing ι O)} (hW : W.IsPrime)
    (hh : IsMultiHomogIdeal W)
    (hd : ringKrullDim (MRing ι O ⧸ W) < ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞))
    {bs : Fin d → K → ℤ} (hn : vNum W bs ≠ 0) :
    C ϖ ∈ W ∧ ¬ ringKrullDim (MRing ι O ⧸ W) < ((d + Fintype.card K : ℕ) : WithBot ℕ∞) := by
  have h1 : ¬ ringKrullDim (MRing ι O ⧸ (W ⊔ Ideal.span {C ϖ})) <
      ((d + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    intro h
    apply hn
    unfold vNum
    refine intNum_small (SpecialIdealMultiHomog.full O K ι W hh) ?_ bs
    rw [← special_sup hϖ, SpecialQuotDim.proof O ϖ hϖ K ι _
      (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))]
    exact h
  refine ⟨?_, fun h => h1 ((dim_mono le_sup_left).trans_lt h)⟩
  by_contra hm
  have h2 := (dim_drop hW hm).trans_lt hd
  have h3 := add_le_add_left (not_lt.1 h1) 1
  have h4 := h3.trans_lt h2
  have h5 : d + Fintype.card K + 1 < d + 1 + Fintype.card K := by exact_mod_cast h4
  omega

theorem NN_nzd (hϖ : Irreducible ϖ) {d : ℕ} {J : Ideal (MRing ι O)} (hJ : IsMultiHomogIdeal J)
    (hd : ringKrullDim (MRing ι O ⧸ J) < ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞))
    (x : MRing ι O) (hx : ∀ W : Ideal (MRing ι O), C ϖ ∈ W → x ∈ W) (hc : J.colon {x} = J)
    (bs : Fin d → K → ℤ) : NN J bs = 0 := by
  refine cycEval_eq_zero fun W hW => ?_
  by_contra hn
  have h1 := (key hϖ hW.1.1 (MinimalPrimeMultiHomog.proof O K ι J W hJ hW)
    ((dim_mono hW.1.2).trans_lt hd) hn).1
  obtain ⟨y, hy, hxy⟩ := Ideal.exists_mul_mem_of_mem_minimalPrimes hW (hx W h1)
  apply hy
  rw [← hc, Submodule.mem_colon_singleton, smul_eq_mul, mul_comm]
  exact hxy

omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in
theorem multAt_zero {R : Type} [CommRing R] {I W : Ideal (MRing ι R)} [W.IsPrime] (h : ¬ I ≤ W) :
    multAt I W = 0 := by
  obtain ⟨q, hq, hqW⟩ := SetLike.not_le_iff_exists.1 h
  haveI : Subsingleton (LocalizedModule W.primeCompl (MRing ι R ⧸ I)) := by
    rw [LocalizedModule.subsingleton_iff]
    intro y
    refine ⟨q, hqW, ?_⟩
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.2 hq, zero_mul]
  exact Module.length_eq_zero

theorem le_colon {A : Type} [CommRing A] (J : Ideal A) (x : A) : J ≤ J.colon {x} := fun y hy => by
  rw [Submodule.mem_colon_singleton, smul_eq_mul]
  exact J.mul_mem_right x hy

theorem NN_add (hϖ : Irreducible ϖ) {d : ℕ} {J : Ideal (MRing ι O)} (hJ : IsMultiHomogIdeal J)
    (hd : ringKrullDim (MRing ι O ⧸ J) < ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞))
    {x : MRing ι O} {s : K → ℕ} (hx : IsMultiHomog x s) (bs : Fin d → K → ℤ) :
    NN J bs = NN (J ⊔ Ideal.span {x}) bs + NN (J.colon {x}) bs := by
  have hfin : ∀ I : Ideal (MRing ι O),
      (Function.support fun W => idealCycle I W * vNum W bs).Finite := fun I =>
    (Ideal.finite_minimalPrimes_of_isNoetherianRing _ I).subset fun W hW =>
      (of_idealCycle_ne (left_ne_zero_of_mul hW)).1
  unfold NN cycEval
  rw [← finsum_add_distrib (hfin _) (hfin _)]
  refine finsum_congr fun W => ?_
  by_cases hn : vNum W bs = 0
  · simp [hn]
  rw [← add_mul]
  congr 1
  by_cases hW : W ∈ J.minimalPrimes ∧ IsRelevant W
  · haveI : W.IsPrime := hW.1.1.1
    have h1 : ∀ I : Ideal (MRing ι O), J ≤ I → idealCycle I W = ((multAt I W).toNat : ℤ) := by
      intro I hI
      by_cases hIW : I ≤ W
      · have h2 : W ∈ I.minimalPrimes :=
          ⟨⟨hW.1.1.1, hIW⟩, fun Q hQ hQW => hW.1.2 ⟨hQ.1, hI.trans hQ.2⟩ hQW⟩
        exact dif_pos ⟨h2, hW.2⟩
      · rw [multAt_zero hIW]
        exact dif_neg fun h => hIW h.1.1.2
    have h2 : multAt J W ≠ ⊤ := ReciprocityTheory.ChartRestriction.G.AI.I1.locLen_ne_top hW.1
    have h3 := FiltrationStepLength.full O K ι J W x
    rw [h1 J le_rfl, h1 _ le_sup_left, h1 _ (le_colon J x), h3]
    rw [h3] at h2
    rw [ENat.toNat_add (WithTop.add_ne_top.1 h2).1 (WithTop.add_ne_top.1 h2).2, Nat.cast_add]
  · have h1 : ∀ I : Ideal (MRing ι O), J ≤ I → IsMultiHomogIdeal I → idealCycle I W = 0 := by
      intro I hI hh
      by_contra h
      obtain ⟨h2, h3⟩ := of_idealCycle_ne h
      haveI : W.IsPrime := h2.1.1
      have hJW : J ≤ W := hI.trans h2.1.2
      have h4 := (key hϖ h2.1.1 (MinimalPrimeMultiHomog.proof O K ι I W hh h2)
        ((dim_mono hJW).trans_lt hd) hn).2
      refine hW ⟨TopDimMinimal.full _ J W (d + Fintype.card K) hJW ?_ h4, h3⟩
      rwa [show d + Fintype.card K + 1 = d + 1 + Fintype.card K by omega]
    rw [h1 J le_rfl hJ, h1 _ le_sup_left (SupSpanMultiHomog.proof O K ι J x s hJ hx),
      h1 _ (le_colon J x) (ColonMultiHomog.full O K ι J x s hJ hx), add_zero]

theorem NN_pow (hϖ : Irreducible ϖ) {d : ℕ} {J : Ideal (MRing ι O)} (hJ : IsMultiHomogIdeal J)
    (hd : ringKrullDim (MRing ι O ⧸ J) < ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞)) (e : ℕ)
    (he : C ϖ ^ e ∈ J)
    (hk : ∀ k < e, ∀ g, C ϖ ^ k * g ∈ J → g ∈ J ⊔ Ideal.span {C ϖ}) (bs : Fin d → K → ℤ) :
    NN J bs = e * NN (J ⊔ Ideal.span {C ϖ}) bs := by
  have h : ∀ j ≤ e, NN J bs = j * NN (J ⊔ Ideal.span {C ϖ}) bs + NN (J.colon {C ϖ ^ j}) bs := by
    intro j hj
    induction j with
    | zero =>
      have : J.colon {C ϖ ^ 0} = J := by
        ext y; rw [Submodule.mem_colon_singleton]; simp
      rw [this]; simp
    | succ j ih =>
      have hh : IsMultiHomogIdeal (J.colon {C ϖ ^ j}) :=
        ColonMultiHomog.full O K ι J _ 0 hJ (by rw [← C_pow]; exact homog_C _)
      have h1 := NN_add hϖ hh ((dim_mono (le_colon J _)).trans_lt hd) (homog_C ϖ) bs
      have h2 : J.colon {C ϖ ^ j} ⊔ Ideal.span {C ϖ} = J ⊔ Ideal.span {C ϖ} := by
        refine le_antisymm (sup_le (fun y hy => ?_) le_sup_right) (sup_le_sup_right (le_colon J _) _)
        rw [Submodule.mem_colon_singleton, smul_eq_mul, mul_comm] at hy
        exact hk j (by omega) y hy
      have h3 : (J.colon {C ϖ ^ j}).colon {C ϖ} = J.colon {C ϖ ^ (j + 1)} := by
        ext y
        simp only [Submodule.mem_colon_singleton, smul_eq_mul, mul_assoc, pow_succ']
      rw [ih (by omega), h1, h2, h3]
      push_cast
      ring
  have h1 : J.colon {C ϖ ^ e} = ⊤ := by
    rw [Ideal.eq_top_iff_one, Submodule.mem_colon_singleton, one_smul]
    exact he
  have h2 : NN (⊤ : Ideal (MRing ι O)) bs = 0 :=
    cycEval_eq_zero fun W hW => absurd (top_le_iff.1 hW.1.2) hW.1.1.ne_top
  rw [h e le_rfl, h1, h2, add_zero]

end

end BaseChangeColon.BC
