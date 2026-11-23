import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.SharpRestriction.LevelLetterCocycles.LargeLevelLemmas
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
import Formalism.SharpRestriction.LevelLetterCocycles.UsedConclusionOfUsedInputs
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsCrystallineJumpsOfIsIsoMatrixGaloisRepresentat
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.RowBoundB

open Module

theorem good_one {l : ℕ} [Fact l.Prime] {K LL : FinExt l} {s : ℕ} (hl : l ≠ 2) (h : Good K s LL)
    (hK : K.1 ≤ Ks K 1) : Good K 1 LL := by
  obtain ⟨hs, -, -, hτ⟩ := h
  refine ⟨le_rfl, fun h2 => absurd h2 hl, hK, fun τ x => ?_⟩
  have hle : Ks K 1 ≤ Ks K s := by
    refine sup_le_sup_left (IntermediateField.adjoin.mono _ _ _ ?_) _
    intro y hy
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hs
    simp only [Set.mem_setOf_eq] at hy ⊢
    rw [pow_add, pow_mul, hy, one_pow]
  obtain ⟨φ, hφ⟩ := IsAlgClosed.surjective_restrictDomain_of_isAlgebraic (K := ℚ_[l]) (L := ↥(Ks K 1))
    (M := Om l) (E := Om l) τ
  have := hτ (φ.comp (Ks K s).val) ⟨x.1, hle x.2⟩
  rw [← hφ]
  exact this

theorem jump_windows (η Sc b : ℝ) (t : ℕ) (hη : 0 < η) (hS : 0 < Sc) (ht : 1 ≤ (t : ℝ))
    (hpar : Sc + η + t + 2 ≤ b) (s : ℤ) (Jc Jl : Finset ℤ)
    (h1 : η + t + 1 < (s : ℝ)) (h2 : (s : ℝ) ≤ b + η + t + 1)
    (hl : ∀ a ∈ Jl, ((-η + ((t : ℝ) - 1) / 2 ≤ (a : ℝ) ∧ a ≤ -2) ∨
            ((t : ℤ) + 1 ≤ a ∧ (a : ℝ) ≤ η + ((t : ℝ) - 1) / 2)))
    (hc : (∀ a ∈ Jc, s ≤ a ∧ (a : ℝ) ≤ s + Sc) ∨ (∀ a ∈ Jc, -((s : ℝ) + Sc) ≤ a ∧ a ≤ -s)) :
    ∃ (up : Bool) (bτ : ℕ), ⌊η⌋₊ + t < bτ ∧
      (∀ a : ℤ, (-a - 1 ∈ Jc ∨ -a - 1 ∈ Jl ∨ (0 ≤ -a - 1 ∧ -a - 1 < t)) →
        a ∈ ElementDenominator.deep up bτ ⌊Sc⌋₊ ∪ Set.Icc (-((⌊η⌋₊ + t : ℕ) : ℤ)) ((⌊η⌋₊ + t : ℕ) : ℤ) ∧
        a ∈ Set.Icc (-((⌊2 * b⌋₊ : ℕ) : ℤ)) ((⌊2 * b⌋₊ : ℕ) : ℤ)) ∧
      ∀ a ∈ Finset.Icc (-((⌊η⌋₊ + t : ℕ) : ℤ)) ((⌊η⌋₊ + t : ℕ) : ℤ), -a - 1 ∉ Jc := by
  have key : ∀ (x : ℝ) (n : ℤ), 0 ≤ x → (n : ℝ) ≤ x → n ≤ ((⌊x⌋₊ : ℕ) : ℤ) := by
    intro x n hx hn
    rw [Int.natCast_floor_eq_floor hx]
    exact Int.le_floor.2 hn
  have e1 : ((⌊η⌋₊ : ℕ) : ℝ) ≤ η := Nat.floor_le hη.le
  have e2 : ((⌊Sc⌋₊ : ℕ) : ℝ) ≤ Sc := Nat.floor_le hS.le
  have ht' : (1 : ℤ) ≤ t := by exact_mod_cast ht
  have hs1 : ((⌊η⌋₊ : ℕ) : ℤ) + t + 1 < s := by
    have : (((⌊η⌋₊ : ℕ) : ℤ) : ℝ) + ((t : ℤ) : ℝ) + 1 < (s : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have hb : s + 1 + ((⌊Sc⌋₊ : ℕ) : ℤ) ≤ ((⌊2 * b⌋₊ : ℕ) : ℤ) := by
    apply key _ _ (by linarith)
    push_cast; linarith
  have hlow : ∀ a : ℤ, -a - 1 ∈ Jl → -(((⌊η⌋₊ : ℕ) : ℤ) + t) ≤ a ∧ a ≤ ((⌊η⌋₊ : ℕ) : ℤ) + t := by
    intro a ha
    rcases hl _ ha with ⟨p, q⟩ | ⟨p, q⟩
    · have : a ≤ ((⌊η⌋₊ : ℕ) : ℤ) := by
        apply key _ _ hη.le
        push_cast at p; linarith
      omega
    · have : -a - t ≤ ((⌊η⌋₊ : ℕ) : ℤ) := by
        apply key _ _ hη.le
        push_cast at q ⊢; linarith
      omega
  rcases hc with hc | hc
  · have hc' : ∀ a : ℤ, -a - 1 ∈ Jc → s ≤ -a - 1 ∧ -a - 1 - s ≤ ((⌊Sc⌋₊ : ℕ) : ℤ) := by
      intro a ha
      obtain ⟨p, q⟩ := hc _ ha
      refine ⟨p, key _ _ hS.le ?_⟩
      push_cast at q ⊢; linarith
    refine ⟨false, (s + 1).toNat, by omega, fun a ha => ?_, fun a ha hj => ?_⟩
    · simp only [ElementDenominator.deep, Bool.false_eq_true, if_false, Set.mem_union, Set.mem_Icc]
      rcases ha with ha | ha | ha
      · have := hc' a ha
        omega
      · have := hlow a ha
        omega
      · omega
    · have := hc' a hj
      rw [Finset.mem_Icc] at ha
      omega
  · have hc' : ∀ a : ℤ, -a - 1 ∈ Jc → -a - 1 ≤ -s ∧ a + 1 - s ≤ ((⌊Sc⌋₊ : ℕ) : ℤ) := by
      intro a ha
      obtain ⟨p, q⟩ := hc _ ha
      refine ⟨q, key _ _ hS.le ?_⟩
      push_cast at p ⊢; linarith
    refine ⟨true, (s - 1).toNat, by omega, fun a ha => ?_, fun a ha hj => ?_⟩
    · simp only [ElementDenominator.deep, if_true, Set.mem_union, Set.mem_Icc]
      rcases ha with ha | ha | ha
      · have := hc' a ha
        omega
      · have := hlow a ha
        omega
      · omega
    · have := hc' a hj
      rw [Finset.mem_Icc] at ha
      omega

theorem sum_le_card (I Jl : Finset ℤ) (f : ℤ → ℤ) (h1 : ∀ a ∈ I, f a ≤ 1)
    (h0 : ∀ a ∈ I, -a - 1 ∉ Jl → f a = 0) : ∑ a ∈ I, f a ≤ Jl.card := by
  classical
  have e : ∑ a ∈ I, f a ≤ ∑ a ∈ I, (if -a - 1 ∈ Jl then (1 : ℤ) else 0) := by
    refine Finset.sum_le_sum fun a ha => ?_
    split_ifs with h
    · exact h1 a ha
    · exact (h0 a ha h).le
  refine e.trans ?_
  rw [Finset.sum_boole]
  have : (I.filter fun a => -a - 1 ∈ Jl).card ≤ Jl.card := by
    refine Finset.card_le_card_of_injOn (fun a => -a - 1) (fun a ha => (Finset.mem_filter.1 ha).2) ?_
    intro a _ b _ hab
    simp only at hab
    omega
  exact_mod_cast this

theorem boundA_le (CA η Sc b : ℝ) (l n r t m f : ℕ) (hl : 2 ≤ l) (hη : 0 < η) (hS : 0 < Sc) (hb : 1 ≤ b)
    (hf : f = n * 2) :
    ElementDenominator.boundA CA l n 2 r ⌊Sc⌋₊ (⌊η⌋₊ + t) m ⌊2 * b⌋₊ ≤
      max CA 0 * (((f : ℕ) + 1 : ℝ) * (r : ℝ) * (4 * b / (l : ℝ) + 2 * Sc + 2 * Real.logb (l : ℝ) (2 * b) + 1 + η + (t : ℝ)) + 3 * ((f : ℕ) : ℝ) * (m : ℝ) * (2 * b + 1)) := by
  have e1 : ((⌊η⌋₊ : ℕ) : ℝ) ≤ η := Nat.floor_le hη.le
  have e2 : ((⌊Sc⌋₊ : ℕ) : ℝ) ≤ Sc := Nat.floor_le hS.le
  have e3 : ((⌊2 * b⌋₊ : ℕ) : ℝ) ≤ 2 * b := Nat.floor_le (by linarith)
  have e4 : (1 : ℝ) ≤ ((⌊2 * b⌋₊ : ℕ) : ℝ) := by
    have : 1 ≤ ⌊2 * b⌋₊ := Nat.le_floor (by push_cast; linarith)
    exact_mod_cast this
  have hl' : (1 : ℝ) < l := by exact_mod_cast (by omega : 1 < l)
  have e5 : 0 ≤ Real.logb (l : ℝ) ((⌊2 * b⌋₊ : ℕ) : ℝ) := Real.logb_nonneg hl' e4
  have e6 : Real.logb (l : ℝ) ((⌊2 * b⌋₊ : ℕ) : ℝ) ≤ Real.logb (l : ℝ) (2 * b) :=
    Real.logb_le_logb_of_le hl' (by linarith) e3
  have e7 : 2 * ((⌊2 * b⌋₊ : ℕ) : ℝ) / (l : ℝ) ≤ 4 * b / (l : ℝ) :=
    div_le_div_of_nonneg_right (by linarith) (by linarith)
  have hQ : ElementDenominator.boundA CA l n 2 r ⌊Sc⌋₊ (⌊η⌋₊ + t) m ⌊2 * b⌋₊ =
      CA * (((f : ℕ) + 1 : ℝ) * (r : ℝ) * (2 * ((⌊2 * b⌋₊ : ℕ) : ℝ) / (l : ℝ) + 2 * ((⌊Sc⌋₊ : ℕ) : ℝ) +
        2 * Real.logb (l : ℝ) ((⌊2 * b⌋₊ : ℕ) : ℝ) + 1 + ((⌊η⌋₊ : ℕ) : ℝ) + (t : ℝ)) +
        3 * ((f : ℕ) : ℝ) * (m : ℝ) * (((⌊2 * b⌋₊ : ℕ) : ℝ) + 1)) := by
    simp only [ElementDenominator.boundA, hf]
    push_cast
    ring
  rw [hQ]
  refine (mul_le_mul_of_nonneg_right (le_max_left CA 0) (by positivity)).trans ?_
  gcongr

theorem rowAt_of_thmA {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (CA : ℝ)
    (hT : ElementDenominator.thmA P K LL CA) (he : finrank ↥(K0 K) ↥K.1 = 2) {ι : Type} {k r : ℕ}
    (Ms : ι → ↥(GK K) → Matrix (Fin k) (Fin k) ↥LL.1) (M2 : ↥(GK K) →* Matrix (Fin r) (Fin r) ↥LL.1)
    (S η m h : ℕ) (up : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → Bool) (b : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℕ) (q : ℚ)
    (h1 : ∀ (V1 : Type) [AddCommGroup V1] [Module ↥LL.1 V1] [Module ℚ_[l] V1]
          [IsScalarTower ℚ_[l] ↥LL.1 V1] [FiniteDimensional ↥LL.1 V1]
          (ρ1 : Representation ↥LL.1 ↥(GK K) V1), IsSubOfSums ρ1 Ms → IsCrys (P.PD K) ρ1 ∧
          ∀ τ a, IsJumpV (P.PD K) ρ1 τ a →
            a ∈ ElementDenominator.deep (up τ) (b τ) S ∪ Set.Icc (-(η : ℤ)) η ∧ a ∈ Set.Icc (-(h : ℤ)) h)
    (h2 : IsCrys (P.PD K) (matRep M2)) (hb : ∀ τ, η < b τ)
    (hsum : ∀ τ, ∑ a ∈ Finset.Icc (-(η : ℤ)) η, multV (P.PD K) (matRep M2) τ a ≤ m)
    (hq : ElementDenominator.boundA CA l (finrank ℚ_[l] ↥(K0 K)) 2 r S η m h ≤ q) :
    RowAt (P.PD K) (O := ↥(OL LL)) Ms ⇑M2 q := by
  intro V2 _ _ _ _ _ _ _ _ _ _ _ ρ2 T2 hc2 hmat V1 _ _ _ _ _ _ _ _ _ _ _ ρ1 T1 hc1 hsub F hFo
  obtain ⟨c1, c2⟩ := h1 V1 ρ1 hsub
  obtain ⟨e, heg, -⟩ := hmat
  have he' : ∀ g v, e (ρ2 g v) = matRep M2 g (e v) := by
    intro g v
    rw [heg]
    simp [matRep, Matrix.toLinAlgEquiv'_apply]
  have hr : finrank ↥LL.1 V2 = r := by simpa using e.finrank_eq
  have hs2 : ∀ τ, ∑ a ∈ Finset.Icc (-(η : ℤ)) η, multV (P.PD K) ρ2 τ a ≤ m := by
    intro τ
    simp only [GlobalTheory.HTW.Rec.multV_eq_of_equiv _ e he']
    exact hsum τ
  obtain ⟨mm, k, hm, hk, hle⟩ := hT { V := V1, ρ := ρ1, cont := hc1, L := T1 }
    { V := V2, ρ := ρ2, cont := hc2, L := T2 } F r S η m h up b c1
    (GlobalTheory.HTW.Rec.isCrys_of_equiv _ e he' h2) hFo hr
    (fun τ a ha => (c2 τ a ha).1) hb hs2 (fun τ a ha => (c2 τ a ha).2) (Or.inl he)
  refine ⟨mm, k, hm, hk, ?_⟩
  rw [he] at hle
  have h3 := hle.trans (mul_le_mul_of_nonneg_right hq (Nat.cast_nonneg k))
  exact_mod_cast h3

theorem row_bound : ∀ (D : D7) (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (large₂ : SizeData₂ D) (ep : Bool) (CA : ℝ), EmbeddingTypeJumps.Conclusion0 D → EmbeddingTypeJumps.Conclusion1 D → EmbeddingTypeJumps.admA (D := D) CA → EmbeddingTypeJumps.HodgeJumpWindowsAtDistinguishedPrimes r ep large₂ → EmbeddingTypeJumps.FontaineSubOfSumsAtDistinguishedPrimes r ρ → EmbeddingTypeJumps.admG2 r ρ → EmbeddingTypeJumps.iwahoriAdmissibleSet r ρ → EmbeddingTypeJumps.LiteratureHypotheses (D := D) → EmbeddingTypeJumps.ParametersPolynomiallyBounded large₂ → ∀ i : D.nd.Loc, EmbeddingTypeJumps.AtQD i → ∀ π ∈ D.nd.Zgood i, ∀ dc : TruncatedSeriesCountingIdentities.Decl D i, ∃ lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ, TruncatedSeriesCountingIdentities.LengthBoundAtPlaces i (r i) (ρ i) π dc lenRow ∧ ∀ w ∈ dc.row, (lenRow w : ℝ) ≤ max CA 0 * (((locDeg D.host.E w : ℕ) + 1 : ℝ) * (D.R.r : ℝ) * (4 * large₂.sc.b / (D.nd.l i : ℝ) + 2 * large₂.Sc + 2 * Real.logb (D.nd.l i : ℝ) (2 * large₂.sc.b) + 1 + large₂.etaSz + (D.R.t : ℝ)) + 3 * ((locDeg D.host.E w : ℕ) : ℝ) * (D.R.m : ℝ) * (2 * large₂.sc.b + 1)) + 1 := by
  intro D r ρ large₂ ep CA h0 h1 hA hJ hF _ _ hLit hPar i hi π hπ dc
  refine ⟨fun w => ((⌈max CA 0 * (((locDeg D.host.E w : ℕ) + 1 : ℝ) * (D.R.r : ℝ) * (4 * large₂.sc.b / (D.nd.l i : ℝ) + 2 * large₂.Sc + 2 * Real.logb (D.nd.l i : ℝ) (2 * large₂.sc.b) + 1 + large₂.etaSz + (D.R.t : ℝ)) + 3 * ((locDeg D.host.E w : ℕ) : ℝ) * (D.R.m : ℝ) * (2 * large₂.sc.b + 1))⌉ : ℤ) : ℚ), ?_, fun w _ => ?_⟩
  swap
  · rw [Rat.cast_intCast]
    exact (Int.ceil_lt_add_one _).le
  intro w hw _ C hC
  have hl4 : D.nd.l i % 4 = 3 := (h1 (D.nd.l i) (by simpa using hi.1.1)).1
  have hl2 : D.nd.l i ≠ 2 := by omega
  obtain ⟨-, hK1, he, -⟩ := h0 i hi.1.1 w hw
  have hG : Good (D.nbr i w hw).Kw 1 C.LL := hC.good_one hl2 hK1
  have hdeg : locDeg D.host.E w = finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw) * 2 := by
    have h := ((hLit i hi).2.2.1 w hw).2.2
    unfold Br.DegW at h
    rw [← h, ← he]
    exact (Module.finrank_mul_finrank _ _ _).symm
  have hT := hA (D.nd.l i) hl2 _ _ hG
  have hη := large₂.etaSz_pos
  have hS := large₂.Sc_pos
  have ht := large₂.t_win.1
  have hb : 1 ≤ large₂.sc.b := by unfold EmbeddingTypeJumps.ParametersPolynomiallyBounded at hPar; linarith
  choose s Jc Jl j1 j2 _ j4 j5 j6 _ _ j9 using hJ i hi w hw C
  choose up bτ w1 w2 w3 using fun τ => jump_windows large₂.etaSz large₂.Sc large₂.sc.b D.R.t hη hS ht hPar (s τ) (Jc τ) (Jl τ)
    (j1 τ) (j2 τ) (fun a ha => (j5 τ a ha).1) (j6 τ)
  obtain ⟨f1, f2⟩ := hF i hi w hw C
  obtain ⟨g1, g2⟩ := f2 π hπ
  have hbd := boundA_le CA large₂.etaSz large₂.Sc large₂.sc.b (D.nd.l i) _ D.R.r D.R.t D.R.m _ (by omega) hη hS hb hdeg
  refine rowAt_of_thmA (D.loc (D.nd.l i)) (D.nbr i w hw).Kw C.LL CA hT he _ _
    ⌊large₂.Sc⌋₊ (⌊large₂.etaSz⌋₊ + D.R.t) D.R.m ⌊2 * large₂.sc.b⌋₊ up bτ _ ?_ g1 w1 ?_ ?_
  · intro V1 _ _ _ _ _ ρ1 hsub
    obtain ⟨c1, c2⟩ := f1 V1 ρ1 hsub
    refine ⟨c1, fun τ a ha => ?_⟩
    obtain ⟨x, hx⟩ := c2 τ a ha
    exact w2 τ a ((j9 τ x _).1 hx)
  · intro τ
    rw [← j4 τ]
    apply sum_le_card
    · intro a _
      by_cases hh : (IsJumpV (Br.PD D.loc D.nbr i w hw)
                (matRep (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (r i) π))) τ (-a - 1) ∧
                ¬ (0 ≤ -a - 1 ∧ -a - 1 < (D.R.t : ℤ)))
      · exact ((g2 τ a).1 hh).le
      · exact ((g2 τ a).2 hh).le.trans zero_le_one
    · intro a ha hn
      refine (g2 τ a).2 ?_
      rintro ⟨p, q⟩
      rcases (j9 τ π _).1 p with h | h | h
      · exact w3 τ a ha h
      · exact hn h
      · exact q h
  · rw [Rat.cast_intCast]
    exact hbd.trans (Int.le_ceil _)

end GlobalTheory.RowBoundB
