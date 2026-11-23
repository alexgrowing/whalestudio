import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalDoublePointsGeneric
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology ComplexSets

noncomputable section

namespace NormalDoublePointsGeneric

theorem ringKrullDim_quotient_le_of_primes {R : Type*} [CommRing R] (I : Ideal R) (k : WithBot ℕ∞)
    (h : ∀ W : Ideal R, W.IsPrime → I ≤ W → ∃ K : Ideal R, K ≤ W ∧ ringKrullDim (R ⧸ K) ≤ k) :
    ringKrullDim (R ⧸ I) ≤ k := by
  rw [ringKrullDim_quotient]
  refine iSup_le fun l => ?_
  obtain ⟨K, hKW, hK⟩ := h l.head.1.asIdeal l.head.1.isPrime l.head.2
  let l' : LTSeries (PrimeSpectrum.zeroLocus (R := R) K) :=
    ⟨l.length, fun i => ⟨(l i).1, show (K : Set R) ⊆ (l i).1.asIdeal from hKW.trans (l.head_le i)⟩,
      fun i => l.step i⟩
  calc (l.length : WithBot ℕ∞) = l'.length := rfl
    _ ≤ Order.krullDim (PrimeSpectrum.zeroLocus (R := R) K) := Order.LTSeries.length_le_krullDim l'
    _ = ringKrullDim (R ⧸ K) := (ringKrullDim_quotient K).symm
    _ ≤ k := hK

theorem ringKrullDim_quotient_anti {R : Type*} [CommRing R] {K K' : Ideal R} (h : K ≤ K') :
    ringKrullDim (R ⧸ K') ≤ ringKrullDim (R ⧸ K) :=
  ringKrullDim_le_of_surjective (Ideal.Quotient.factor h) (Ideal.Quotient.factor_surjective h)

theorem ringKrullDim_quot_sup_span_add_one_le {n : ℕ} (p : Ideal (MvPolynomial (Fin n) ℂ)) [p.IsPrime]
    {g : MvPolynomial (Fin n) ℂ} (hg : g ∉ p) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (p ⊔ Ideal.span {g})) + 1 ≤
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ p) := by
  have hne : Ideal.Quotient.mk p g ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have h := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hne)
  have e : ((MvPolynomial (Fin n) ℂ ⧸ p) ⧸ Ideal.span {Ideal.Quotient.mk p g}) ≃+*
      MvPolynomial (Fin n) ℂ ⧸ (p ⊔ Ideal.span {g}) :=
    (Ideal.quotEquivOfEq (by rw [Ideal.map_span, Set.image_singleton])).trans
      (DoubleQuot.quotQuotEquivQuotSup p (Ideal.span {g}))
  rwa [ringKrullDim_eq_of_ringEquiv e] at h

def belowNat : ℕ → WithBot ℕ∞
  | 0 => ⊥
  | e + 1 => (e : WithBot ℕ∞)

theorem belowNat_lt (d : ℕ) : belowNat d < (d : WithBot ℕ∞) := by
  cases d with
  | zero => exact WithBot.bot_lt_coe _
  | succ e =>
    show ((e : ℕ) : WithBot ℕ∞) < ((e + 1 : ℕ) : WithBot ℕ∞)
    exact_mod_cast Nat.lt_succ_self e

theorem le_belowNat_of_add_two_le {x : WithBot ℕ∞} {d : ℕ}
    (h : x + 1 + 1 ≤ ((d + 1 : ℕ) : WithBot ℕ∞)) : x ≤ belowNat d := by
  induction x using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      exfalso
      have h2 : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ (((d + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
        rw [← WithBot.coe_one, ← WithBot.coe_add, top_add, ← WithBot.coe_add, top_add] at h
        exact_mod_cast h
      exact absurd (WithBot.coe_le_coe.1 h2) (by simp)
    | coe k =>
      have h2 : k + 1 + 1 ≤ d + 1 := by exact_mod_cast h
      cases d with
      | zero => omega
      | succ e => show ((k : ℕ∞) : WithBot ℕ∞) ≤ ((e : ℕ) : WithBot ℕ∞); exact_mod_cast (by omega : k ≤ e)

theorem proof : NormalDoublePointsGeneric.Statement := by
  intro n d J u M hJ hdim hu
  classical
  choose a b hbJ hab using M.birational
  set bb : MvPolynomial (Fin n) ℂ := ∏ i, b i with hbb
  have hbbJ : bb ∉ J := fun h => by
    obtain ⟨i, -, hi⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hJ)).1 h
    exact hbJ i hi
  set K : Ideal (MvPolynomial (Fin n) ℂ) := J ⊔ Ideal.span {bb} with hK
  have hfin : K.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ K
  set S : Finset (Ideal (MvPolynomial (Fin n) ℂ)) := hfin.toFinset.filter (fun P => linForm u ∉ P) with hS
  have memS : ∀ P, P ∈ S ↔ P ∈ K.minimalPrimes ∧ linForm u ∉ P := fun P => by
    simp [hS]
  refine ⟨S.inf (fun P => P ⊔ Ideal.span {linForm u}), ?_, ?_, ?_⟩
  · refine Finset.le_inf fun P hP => sup_le_sup_right ?_ _
    exact le_sup_left.trans ((memS P).1 hP).1.1.2
  · have := hJ
    have hdimK : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ K) + 1 ≤ ((d + 1 : ℕ) : WithBot ℕ∞) :=
      hdim ▸ ringKrullDim_quot_sup_span_add_one_le J hbbJ
    refine lt_of_le_of_lt (ringKrullDim_quotient_le_of_primes _ (belowNat d) fun W hW hIW => ?_) (belowNat_lt d)
    obtain ⟨P, hPS, hPW⟩ := (hW.inf_le').1 hIW
    refine ⟨_, hPW, le_belowNat_of_add_two_le ?_⟩
    obtain ⟨hPm, huP⟩ := (memS P).1 hPS
    have := hPm.1.1
    have h1 := ringKrullDim_quot_sup_span_add_one_le P huP
    have h2 : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ P) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ K) :=
      ringKrullDim_quotient_anti hPm.1.2
    calc ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (P ⊔ Ideal.span {linForm u})) + 1 + 1
        ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ K) + 1 := by gcongr; exact h1.trans h2
      _ ≤ _ := hdimK
  · intro q _ hqu hqI
    have evu : ∀ x, eval x (linForm u) = linEval u x := fun x => by simp [linForm, linEval]
    have hqP : ∀ P ∈ S, q ∉ zeroSet P := by
      intro P hP hqP
      apply hqI
      intro f hf
      have hf' : f ∈ P ⊔ Ideal.span {linForm u} := (Finset.inf_le (f := fun P => P ⊔ Ideal.span {linForm u}) hP) hf
      obtain ⟨p, hp, r, hr, rfl⟩ := Submodule.mem_sup.1 hf'
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hr
      simp [hqP p hp, evu, hqu]
    have hclosed : ∀ P : Ideal (MvPolynomial (Fin n) ℂ), IsClosed (zeroSet P) := fun P => by
      have : zeroSet P = ⋂ f ∈ P, {x : Fin n → ℂ | eval x f = 0} := by
        ext x; simp [zeroSet]
      rw [this]
      exact isClosed_biInter fun f _ => isClosed_eq (MvPolynomial.continuous_eval f) continuous_const
    refine ⟨⋂ P ∈ S, (zeroSet P)ᶜ, (Filter.biInter_finset_mem S).2 fun P hP =>
      (hclosed P).isOpen_compl.mem_nhds (hqP P hP), ?_⟩
    intro w hw w' hw' hww hxN hne
    set x := IndefiniteRowSideFullHecke.ComplexSets.firstCoords w with hx
    have hwx : (w ∘ Sum.inl) = x := rfl
    have hw'x : (w' ∘ Sum.inl) = x := by rw [hww]; rfl
    have hxJ : ∀ f ∈ J, eval x f = 0 := fun f hf => by
      have hf' : rename Sum.inl f ∈ M.ideal := by
        rw [← M.comap_eq] at hf; exact hf
      have := hw _ hf'
      rwa [eval_rename, hwx] at this
    have hbx : eval x bb = 0 := by
      by_contra hb
      apply hne
      funext s
      rcases s with i | i
      · exact congrFun hww i
      · have hbi : eval x (b i) ≠ 0 := fun h0 => hb (by
          rw [hbb, map_prod]; exact Finset.prod_eq_zero (Finset.mem_univ i) h0)
        have e1 := hw _ (hab i)
        have e2 := hw' _ (hab i)
        simp only [map_sub, map_mul, eval_rename, eval_X, hwx, hw'x] at e1 e2
        exact mul_left_cancel₀ hbi (by linear_combination e1 - e2)
    have hKx : K ≤ RingHom.ker (eval x) := sup_le (fun f hf => RingHom.mem_ker.2 (hxJ f hf))
      (Ideal.span_le.2 (Set.singleton_subset_iff.2 (RingHom.mem_ker.2 hbx)))
    have : (RingHom.ker (eval x)).IsPrime := RingHom.ker_isPrime _
    obtain ⟨P, hPm, hPx⟩ := Ideal.exists_minimalPrimes_le hKx
    by_cases huP : linForm u ∈ P
    · rw [← evu]; exact RingHom.mem_ker.1 (hPx huP)
    · exfalso
      have hPS : P ∈ S := (memS P).2 ⟨hPm, huP⟩
      have hxP : x ∈ zeroSet P := fun f hf => RingHom.mem_ker.1 (hPx hf)
      exact (Set.mem_iInter₂.1 hxN P hPS) hxP

end NormalDoublePointsGeneric

end

end GroundTheory.Heights₂.Heights
