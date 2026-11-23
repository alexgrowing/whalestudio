import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemOfLpCharLpSpEqSumList
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DirectSumCancelRight
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.WeilDeligne.SpUnique

open SpSummand

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

section Rep

variable {V U U' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U] [AddCommGroup U'] [Module ℂ U']
  [FiniteDimensional ℂ U'] {ρ : Representation ℂ (Weil h) V} {k : ℕ} {c : Weil h → ℂ}

theorem hasCopy_sum_left {b : WDRep h U} (b' : WDRep h U') (H : HasCopy ρ k c b) :
    HasCopy ρ k c (b.sum b') := by
  obtain ⟨f, g, hf, hc, rfl⟩ := H
  refine ⟨LinearMap.inl ℂ U U' ∘ₗ ((b.N ^ k) ∘ₗ g), LinearMap.inl ℂ U U' ∘ₗ g, ?_, fun σ v => ?_, ?_⟩
  · intro h0
    apply hf
    refine LinearMap.ext fun v => ?_
    have := congrArg Prod.fst (LinearMap.congr_fun h0 v)
    simpa using this
  · have := hc σ v
    refine Prod.ext ?_ ?_
    · simpa using this
    · simp
  · refine LinearMap.ext fun v => ?_
    rw [LinearMap.comp_apply, sum_N_pow]
    refine Prod.ext ?_ ?_ <;> simp

theorem hasCopy_sum_right (b : WDRep h U) {b' : WDRep h U'} (H : HasCopy ρ k c b') :
    HasCopy ρ k c (b.sum b') := by
  obtain ⟨f, g, hf, hc, rfl⟩ := H
  refine ⟨LinearMap.inr ℂ U U' ∘ₗ ((b'.N ^ k) ∘ₗ g), LinearMap.inr ℂ U U' ∘ₗ g, ?_, fun σ v => ?_, ?_⟩
  · intro h0
    apply hf
    refine LinearMap.ext fun v => ?_
    have := congrArg Prod.snd (LinearMap.congr_fun h0 v)
    simpa using this
  · have := hc σ v
    refine Prod.ext ?_ ?_
    · simp
    · simpa using this
  · refine LinearMap.ext fun v => ?_
    rw [LinearMap.comp_apply, sum_N_pow]
    refine Prod.ext ?_ ?_ <;> simp

theorem powZero_sum {b : WDRep h U} {b' : WDRep h U'} (H : PowZero k b) (H' : PowZero k b') :
    PowZero k (b.sum b') := by
  unfold PowZero at *
  rw [sum_N_pow, H, H', LinearMap.prodMap_zero]

theorem powZero_of_le (a : WDRep h U) (ha : a.ρ.IsIrreducible) {m : ℕ} (hmk : m ≤ k) :
    PowZero k (a.tensor (WDRep.sp h (m + 1))) := by
  unfold PowZero
  rw [tensor_sp_N_pow a (N_eq_zero_of_irr a ha), shiftEnd_pow_eq_zero (by omega),
    LinearMap.lTensor_zero]

theorem hasCopyW_lpSum_left (x y : WD h) (H : HasCopyW ρ k c x) : HasCopyW ρ k c (x.lpSum y) := by
  induction x using WD.ind with
  | hP n a =>
    induction y using WD.ind with
    | hP n' b =>
      rw [WD.lpSum_mk, hasCopyW_mk]
      rw [hasCopyW_mk] at H
      exact hasCopy_sum_left b H

theorem hasCopyW_lpSum_right (x y : WD h) (H : HasCopyW ρ k c y) : HasCopyW ρ k c (x.lpSum y) := by
  induction x using WD.ind with
  | hP n a =>
    induction y using WD.ind with
    | hP n' b =>
      rw [WD.lpSum_mk, hasCopyW_mk]
      rw [hasCopyW_mk] at H
      exact hasCopy_sum_right a H

theorem powZeroW_lpSum_of (x y : WD h) (H : PowZeroW k x) (H' : PowZeroW k y) :
    PowZeroW k (x.lpSum y) := by
  induction x using WD.ind with
  | hP n a =>
    induction y using WD.ind with
    | hP n' b =>
      rw [WD.lpSum_mk, powZeroW_mk]
      rw [powZeroW_mk] at H H'
      exact powZero_sum H H'

theorem powZeroW_lpZero : PowZeroW k (WD.lpZero h) := by
  rw [WD.lpZero, powZeroW_mk]
  show (WDRep.diag h _).N ^ (k + 1) = 0
  rw [WDRep.diag_N, zero_pow (Nat.succ_ne_zero k)]

theorem hasCopyW_sumList {α : Type} (F : α → WD h) (l : List α) (p : α) (hp : p ∈ l)
    (H : HasCopyW ρ k c (F p)) : HasCopyW ρ k c (sumList (l.map F)) := by
  induction l with
  | nil => cases hp
  | cons q l ih =>
    change HasCopyW ρ k c ((F q).lpSum (sumList (l.map F)))
    rcases List.mem_cons.1 hp with rfl | hp
    · exact hasCopyW_lpSum_left _ _ H
    · exact hasCopyW_lpSum_right _ _ (ih hp)

theorem powZeroW_sumList {α : Type} (F : α → WD h) (l : List α) (H : ∀ p ∈ l, PowZeroW k (F p)) :
    PowZeroW k (sumList (l.map F)) := by
  induction l with
  | nil => exact powZeroW_lpZero
  | cons q l ih =>
    change PowZeroW k ((F q).lpSum (sumList (l.map F)))
    exact powZeroW_lpSum_of _ _ (H q List.mem_cons_self) (ih fun p hp => H p (List.mem_cons_of_mem _ hp))

end Rep

theorem sumList_perm {l l' : List (WD h)} (hp : l.Perm l') : sumList l = sumList l' := by
  induction hp with
  | nil => rfl
  | cons x _ ih =>
    show WD.lpSum x (sumList _) = WD.lpSum x (sumList _)
    rw [ih]
  | swap x y l =>
    show WD.lpSum y (WD.lpSum x (sumList l)) = WD.lpSum x (WD.lpSum y (sumList l))
    rw [← WD.lpSum_assoc, ← WD.lpSum_assoc, WD.lpSum_comm x y]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem lpDim_pos (p : WD h × ℕ) (hp : IsIrrWD p.1) :
    0 < WD.lpDim (p.1.lpChar (WD.lpSp h (p.2 + 1))) := by
  obtain ⟨n, a, ha, hirr⟩ := hp
  rw [WD.lpDim_tensor, WD.lpDim_lpSp, ← ha, WD.lpDim_mk, Module.finrank_fin_fun]
  obtain ⟨v, hv⟩ := exists_ne_zero hirr
  have hn : n ≠ 0 := by
    rintro rfl
    exact hv (Subsingleton.elim _ _)
  exact Nat.mul_pos (Nat.pos_of_ne_zero hn) (Nat.succ_pos _)

theorem perm_of_sumList_lpChar_lpSp_eq : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (l l' : List (WD h × ℕ)), (∀ p ∈ l, IsIrrWD p.1) → (∀ p ∈ l', IsIrrWD p.1) → sumList (l.map (fun p : WD h × ℕ => p.1.lpChar (WD.lpSp h (p.2 + 1)))) = sumList (l'.map (fun p : WD h × ℕ => p.1.lpChar (WD.lpSp h (p.2 + 1)))) → l.Perm l' := by
  intro E Ω _ _ _ _ _ A w h l l'
  classical
  suffices H : ∀ n (l l' : List (WD h × ℕ)), l.length = n → (∀ p ∈ l, IsIrrWD p.1) →
      (∀ p ∈ l', IsIrrWD p.1) →
      sumList (l.map (fun p : WD h × ℕ => p.1.lpChar (WD.lpSp h (p.2 + 1)))) =
        sumList (l'.map (fun p : WD h × ℕ => p.1.lpChar (WD.lpSp h (p.2 + 1)))) → l.Perm l' from
    H _ l l' rfl
  intro n
  induction n with
  | zero =>
    intro l l' hn hl hl' heq
    obtain rfl := List.length_eq_zero_iff.1 hn
    cases l' with
    | nil => exact List.Perm.nil
    | cons q l'' =>
      exfalso
      have hd := congrArg WD.lpDim heq
      change WD.lpDim (WD.lpZero h) = WD.lpDim (WD.lpSum _ (sumList _)) at hd
      rw [WD.lpDim_zero, WD.lpDim_sum] at hd
      have := lpDim_pos q (hl' q List.mem_cons_self)
      beta_reduce at hd
      omega
  | succ n ih =>
    intro l l' hn hl hl' heq
    have hne : l ≠ [] := by
      rintro rfl
      simp at hn
    obtain ⟨⟨y, k⟩, hp, hmax⟩ : ∃ p ∈ l, ∀ q ∈ l, q.2 ≤ p.2 := by
      obtain ⟨p, hp, hmax⟩ := l.toFinset.exists_max_image Prod.snd
        (by obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil l hne; exact ⟨x, List.mem_toFinset.2 hx⟩)
      exact ⟨p, List.mem_toFinset.1 hp, fun q hq => hmax q (List.mem_toFinset.2 hq)⟩
    obtain ⟨m, a, rfl, ha⟩ := hl _ hp

    have hQ : HasCopyW a.ρ k (lastEig h k)
        (sumList (l.map (fun p : WD h × ℕ => p.1.lpChar (WD.lpSp h (p.2 + 1))))) := by
      refine hasCopyW_sumList _ l _ hp ?_
      show HasCopyW a.ρ k (lastEig h k) ((WD.mk a).lpChar (WD.lpSp h (k + 1)))
      rw [WD.lpSp, WD.lpChar_mk, hasCopyW_mk]
      exact hasCopy_self a ha k
    have hZ : PowZeroW k
        (sumList (l.map (fun p : WD h × ℕ => p.1.lpChar (WD.lpSp h (p.2 + 1))))) := by
      refine powZeroW_sumList _ l fun q hq => ?_
      rcases q with ⟨y', k'⟩
      obtain ⟨m', a', rfl, ha'⟩ := hl _ hq
      show PowZeroW k ((WD.mk a').lpChar (WD.lpSp h (k' + 1)))
      rw [WD.lpSp, WD.lpChar_mk, powZeroW_mk]
      exact powZero_of_le a' ha' (hmax _ hq)
    rw [heq] at hQ hZ
    obtain ⟨⟨y', k'⟩, hq', hqQ, hqZ⟩ := exists_mem_of_sumList _ l' hQ hZ
    obtain ⟨n', a', rfl, ha'⟩ := hl' _ hq'
    dsimp only at hqQ hqZ
    rw [WD.lpSp, WD.lpChar_mk, hasCopyW_mk] at hqQ
    rw [WD.lpSp, WD.lpChar_mk, powZeroW_mk] at hqZ
    obtain ⟨hm, hiso⟩ := eq_of_hasCopy a ha a' ha' k' k hqQ hqZ
    have hp' : (WD.mk a, k) ∈ l' := by
      have : ((WD.mk a', k') : WD h × ℕ) = (WD.mk a, k) := Prod.ext (WD.sound hiso).symm hm
      rw [← this]
      exact hq'

    set p : WD h × ℕ := (WD.mk a, k) with hpdef
    set F : WD h × ℕ → WD h := fun p => p.1.lpChar (WD.lpSp h (p.2 + 1)) with hF
    have e1 : sumList (l.map F) = (F p).lpSum (sumList ((l.erase p).map F)) :=
      sumList_perm ((List.perm_cons_erase hp).map F)
    have e2 : sumList (l'.map F) = (F p).lpSum (sumList ((l'.erase p).map F)) :=
      sumList_perm ((List.perm_cons_erase hp').map F)
    have hc : sumList ((l.erase p).map F) = sumList ((l'.erase p).map F) := by
      refine WD.lpSum_cancel_right E Ω A w h _ _ (F p) ?_
      rw [WD.lpSum_comm, ← e1, WD.lpSum_comm, ← e2]
      exact heq
    have hlen : (l.erase p).length = n := by
      rw [List.length_erase_of_mem hp, hn]
      rfl
    have := ih (l.erase p) (l'.erase p) hlen (fun q hq => hl q (List.mem_of_mem_erase hq))
      (fun q hq => hl' q (List.mem_of_mem_erase hq)) hc
    exact ((List.perm_cons_erase hp).trans (this.cons p)).trans (List.perm_cons_erase hp').symm

end GlobalTheory.WeilDeligne.SpUnique
