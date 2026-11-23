import Formalism.SharpRestriction.GrowthBounds.AevalValuation.PlDefs
import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.RestPlOf
import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.ProdRangeZmod
import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.RenameMemSupported
import Formalism.SharpRestriction.GrowthBounds.PolynomialLevels.FrRevInj
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.PosULeIff
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.ValuationOneEqZero
import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.MemLin
import Formalism.SharpRestriction.GrowthBounds.ValuationLowestDegreeMapFractionField

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.TraceSpectra

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.PairMembershipBlocks
open Formalism.MainNotions.TestSideWords.TwistedFiltration.G3 Formalism.MainNotions.G.GLWeightTheory

theorem ceil_le_of_geZ {x : WithTop ℤ} {t : ℝ} (h : geZ x t) : ((⌈t⌉ : ℤ) : WithTop ℤ) ≤ x := by
  cases x with
  | top => exact le_top
  | coe k => exact WithTop.coe_le_coe.2 (Int.ceil_le.2 (h k rfl))

theorem geZ_of_ceil_le {x : WithTop ℤ} {t : ℝ} (h : ((⌈t⌉ : ℤ) : WithTop ℤ) ≤ x) : geZ x t := by
  intro k hk
  subst hk
  exact Int.ceil_le.1 (WithTop.coe_le_coe.1 h)

theorem le_valS_sum {Kf : Type} [Field Kf] {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι) {α : Type}
    (s : Finset α) (f : α → MvPolynomial (ι × Fin n) Kf) (a : WithTop ℤ) (h : ∀ i ∈ s, a ≤ valS LL S (f i)) :
    a ≤ valS LL S (∑ i ∈ s, f i) := by
  refine Finset.sum_induction f (fun F => a ≤ valS LL S F) (fun F G hF hG => ?_) ?_ h
  · exact le_trans (le_min hF hG) (flt_valS_add LL S F G)
  · rw [valS_zero_eq_top]; exact le_top

theorem mem_supported_of {R σ : Type*} [CommSemiring R] (F : MvPolynomial σ R) (s : Set σ)
    (h : ∀ mo ∈ F.support, ∀ v ∈ mo.support, v ∈ s) : F ∈ supported R s := by
  rw [mem_supported]
  intro v hv
  obtain ⟨mo, hmo, hv'⟩ := (mem_vars_iff_mem_support v).1 (Finset.mem_coe.1 hv)
  exact h mo hmo v hv'

theorem of_mem_supported {R σ : Type*} [CommSemiring R] {F : MvPolynomial σ R} {s : Set σ} (hF : F ∈ supported R s)
    {mo : σ →₀ ℕ} (hmo : mo ∈ F.support) {v : σ} (hv : v ∈ mo.support) : v ∈ s :=
  (mem_supported.1 hF) (Finset.mem_coe.2 ((mem_vars_iff_mem_support v).2 ⟨mo, hmo, hv⟩))

theorem coeff_filtQ {Kf : Type} [Field Kf] {ι : Type} {n : ℕ} (Q : (ι → ℕ) → Prop) (F : MvPolynomial (ι × Fin n) Kf)
    (mo : ι × Fin n →₀ ℕ) : (filtQ Q F).coeff mo = if Q (fun i => multideg mo i) then F.coeff mo else 0 := by
  unfold filtQ
  rw [MvPolynomial.coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  by_cases hq : Q (fun i => multideg mo i)
  · by_cases hs : mo ∈ F.support
    · simp [Finset.mem_filter, hs, hq]
    · simp [Finset.mem_filter, hs, hq, notMem_support_iff.1 hs]
  · simp [Finset.mem_filter, hq]

theorem support_filtQ {Kf : Type} [Field Kf] {ι : Type} {n : ℕ} (Q : (ι → ℕ) → Prop) (F : MvPolynomial (ι × Fin n) Kf)
    {mo : ι × Fin n →₀ ℕ} (h : mo ∈ (filtQ Q F).support) : mo ∈ F.support := by
  rw [mem_support_iff, coeff_filtQ] at h
  rw [mem_support_iff]
  split_ifs at h
  · exact h
  · exact absurd rfl h

section Geo

variable {n' r : ℕ} [NeZero n'] [NeZero r] {Fr : Frames n' r} {L₁ N₁ : ℕ} {p : ℕ} {O : Type} [CommRing O]
  [IsDomain O] [IsDiscreteValuationRing O] {J : ℕ} [NeZero J] (Dt : SignedChainData p O r J)

theorem mlOf_ne_tp (j : ZMod J) (y : ℤ) (j' : ZMod J) (m : Fin r) (h : 1 ≤ m.val) :
    mlOf Fr Dt.nL j y ≠ ML.tp j' m h := by
  unfold mlOf
  split_ifs <;> simp

theorem chain_mem (hT : TieS Fr Dt) (j : ZMod J) (i : Fin (Dt.nch j)) (x : ML J Dt.nL r) :
    x ∈ Dt.chainML j i ↔ (∃ m : Fin r, x = ML.wc (j - 1) m) ∨
      (∃ l : Fin (Dt.nL j), x = ML.ll j l ∧ l.val < i.val) := by
  unfold SignedChainData.chainML
  rw [hT.2.2.2.2.2 j i]
  constructor
  · rintro ⟨y, hy, rfl⟩
    cases y with
    | inl l =>
      rcases hy with hy | ⟨l', hl', hlt⟩
      · simp at hy
      · have e := Sum.inl_injective hl'
        subst e
        exact Or.inr ⟨_, rfl, hlt⟩
    | inr m => exact Or.inl ⟨m, rfl⟩
  · rintro (⟨m, rfl⟩ | ⟨l, rfl, hlt⟩)
    · exact ⟨Sum.inr m, Or.inl (by simp), rfl⟩
    · exact ⟨Sum.inl l, Or.inr ⟨l, rfl, hlt⟩, rfl⟩

theorem posU_bounds (hV : Fr.Valid L₁ N₁) (hT : TieS Fr Dt) (j : ZMod J) (i : Fin (Dt.nch j)) :
    Fr.fr (segZ j - 1) (r - 1) < posU Fr (Dt.nL j) (segZ j) i.val ∧
      posU Fr (Dt.nL j) (segZ j) i.val ≤ Fr.fr (segZ j) 0 := by
  have hi : i.val < Dt.nL j + 1 := by have := i.isLt; have h2 := hT.2.2.2.2.1 j; omega
  unfold posU
  split_ifs with h
  · have := Formalism.MainNotions.NormalSetCounting.ll_between (Fr := Fr) (nL := Dt.nL) hT.2.1 j ⟨i.val, h⟩
    exact ⟨this.1, this.2.le⟩
  · rw [show i.val - Dt.nL j = 0 by omega]
    exact ⟨Formalism.MainNotions.Proposition5Numerics.frame_end_lt_next_start hV (segZ j), le_rfl⟩

theorem geo_chain (hV : Fr.Valid L₁ N₁) (hT : TieS Fr Dt) (j : ZMod J) (i : Fin (Dt.nch j)) (y : ℤ)
    (hy : y ∈ Fr.letters (segZ j)) :
    (y < posU Fr (Dt.nL j) (segZ j) i.val ↔ mlOf Fr Dt.nL j y ∈ Dt.chainML j i) ∧
      Dt.modelLet.vec (mlOf Fr Dt.nL j y) = LZ.vec y := by
  have hi : i.val < Dt.nL j + 1 := by have := i.isLt; have h2 := hT.2.2.2.2.1 j; omega
  have hpU := posU_bounds Dt hV hT j i
  have hcard := hT.2.1 j
  rcases restSpec n' r Fr L₁ N₁ hV J Dt.nL hT.2.1 j y hy with ⟨l, rfl, hm⟩ | ⟨m, rfl, hm⟩ | ⟨m, rfl, hm⟩
  · rw [hm, chain_mem Dt hT]
    have hl := l.isLt
    refine ⟨⟨fun h => Or.inr ⟨l, rfl, ?_⟩, ?_⟩, ?_⟩
    · by_contra hc
      push_neg at hc
      have hi' : i.val < Dt.nL j := lt_of_le_of_lt hc hl
      rw [Formalism.MainNotions.Proposition5Numerics.posU_ll' (Fr := Fr) (segZ j) (Dt.nL j) i.val hi'] at h
      rcases Nat.eq_or_lt_of_le hc with he | hlt
      · rw [he] at h
        exact lt_irrefl _ h
      · exact lt_asymm h (Formalism.MainNotions.Proposition5Numerics.llPos_lt (Fr := Fr) (segZ j) i.val l.val hlt (by rw [← hcard]; exact hl))
    · rintro (⟨m, hm'⟩ | ⟨l', hl', hlt⟩)
      · cases hm'
      · have hll : l = l' := eq_of_heq (ML.ll.inj hl').2
        subst hll
        by_cases hi' : i.val < Dt.nL j
        · rw [Formalism.MainNotions.Proposition5Numerics.posU_ll' (Fr := Fr) (segZ j) (Dt.nL j) i.val hi']
          exact Formalism.MainNotions.Proposition5Numerics.llPos_lt (Fr := Fr) (segZ j) l.val i.val hlt (by rw [← hcard]; exact hi')
        · have he : posU Fr (Dt.nL j) (segZ j) i.val = Fr.fr (segZ j) 0 := by
            unfold posU
            rw [if_neg hi', show i.val - Dt.nL j = 0 by omega]
          rw [he]
          exact (Formalism.MainNotions.NormalSetCounting.ll_between (Fr := Fr) (nL := Dt.nL) hT.2.1 j l).2
    · show Dt.sgn j l = decide (Even (llPos Fr (segZ j) l.val))
      exact hT.2.2.1 j l
  · rw [hm, chain_mem Dt hT]
    have hmr := m.isLt
    refine ⟨⟨fun h => absurd h (not_lt.2 ?_), fun h => ?_⟩, ?_⟩
    · exact le_trans hpU.2 (Formalism.MainNotions.Proposition5Numerics.dg_fr_le hV (segZ j) (Nat.zero_le _) (by omega))
    · rcases h with ⟨m', h'⟩ | ⟨l', h', _⟩ <;> cases h'
    · show true = decide (Even (Fr.fr (segZ j) (r - 1 - m.val)))
      exact (decide_eq_true (hV.2.2.2.2.1 _ _ (by omega)).2).symm
  · rw [hm, chain_mem Dt hT]
    have hmr := m.isLt
    refine ⟨⟨fun _ => Or.inl ⟨m, rfl⟩, fun _ => ?_⟩, ?_⟩
    · exact lt_of_le_of_lt (Formalism.MainNotions.Proposition5Numerics.dg_fr_le hV (segZ j - 1) (by omega) (by omega)) hpU.1
    · show true = decide (Even (Fr.fr (segZ j - 1) (r - 1 - m.val)))
      exact (decide_eq_true (hV.2.2.2.2.1 _ _ (by omega)).2).symm

theorem chi_out (hV : Fr.Valid L₁ N₁) (hT : TieS Fr Dt) (j j' : ZMod J) (hj : j' ≠ j) (i : Fin (Dt.nch j)) (y : ℤ)
    (hy : y ∈ Fr.letters (segZ j')) : mlOf Fr Dt.nL j' y ∉ Dt.chainML j i := by
  rw [chain_mem Dt hT]
  rcases restSpec n' r Fr L₁ N₁ hV J Dt.nL hT.2.1 j' y hy with ⟨l, _, hm⟩ | ⟨m, _, hm⟩ | ⟨m, _, hm⟩ <;> rw [hm]
  · rintro (⟨m', h⟩ | ⟨l', h, _⟩)
    · cases h
    · exact hj (ML.ll.inj h).1
  · rintro (⟨m', h⟩ | ⟨l', h, _⟩) <;> cases h
  · rintro (⟨m', h⟩ | ⟨l', h, _⟩)
    · exact hj (sub_left_inj.1 (ML.wc.inj h).1)
    · cases h

theorem chi_supp (j' : ZMod J) (F : MvPolynomial (ℤ × Fin r) (KK O)) (s : Set (ML J Dt.nL r × Fin r))
    (h : ∀ y ∈ Fr.letters (segZ j'), ∀ a : Fin r, (mlOf Fr Dt.nL j' y, a) ∈ s) :
    chi Fr Dt.nL (KK O) j' F ∈ supported (KK O) s := by
  refine Formalism.MainNotions.PairMembershipBlocks.T5.algHom_mem_supported _ s (fun v => ?_) F
  unfold chi
  rw [aeval_X]
  split_ifs with hv
  · exact X_mem_supported.2 (h v.1 hv v.2)
  · exact Subalgebra.zero_mem _

theorem val_chi (hVA : ValAeval) (hV : Fr.Valid L₁ N₁) (hT : TieS Fr Dt) (j : ZMod J) (i : Fin (Dt.nch j))
    (F : MvPolynomial (ℤ × Fin r) (KK O))
    (hF : F ∈ supported (KK O) {v : ℤ × Fin r | v.1 ∈ Fr.letters (segZ j)}) :
    valS LZ {y | y < posU Fr (Dt.nL j) (segZ j) i.val} F ≤
      valS Dt.modelLet (Dt.chainML j i) (chi Fr Dt.nL (KK O) j F) := by
  unfold chi
  refine hVA (KK O) ℤ (ML J Dt.nL r) r LZ Dt.modelLet {y | y < posU Fr (Dt.nL j) (segZ j) i.val}
    {y | y ∈ Fr.letters (segZ j)} (Dt.chainML j i) (mlOf Fr Dt.nL j) _ F hF ?_ ?_
  · intro v hvL hvS
    have hvL' : v.1 ∈ Fr.letters (segZ j) := hvL
    have hg := geo_chain Dt hV hT j i v.1 hvL'
    exact ⟨if_pos hvL', hg.1.1 hvS, hg.2⟩
  · intro v hvL hvS
    have hvL' : v.1 ∈ Fr.letters (segZ j) := hvL
    rw [if_pos hvL']
    exact X_mem_supported.2 (fun h => hvS ((geo_chain Dt hV hT j i v.1 hvL').1.2 h))

end Geo

section Core

variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {r J : ℕ} [NeZero J] [NeZero r]
  (Dt : SignedChainData p O r J)

theorem chain_core (hNN : ValNN) (hPM : PhMon) (hFP : FdigPh) (hFS : FdigSum) (hP : ∀ j m, 0 < Dt.P j m)
    (j : ZMod J) (i : Fin (Dt.nch j))
    (hch : ∀ x, x ∈ Dt.chainML j i ↔ (∃ m : Fin r, x = ML.wc (j - 1) m) ∨
      (∃ l : Fin (Dt.nL j), x = ML.ll j l ∧ l.val < i.val))
    (rho : (ZMod J × Fin r) × Fin r → ℕ) (b : TL J Dt.nL r × Fin r →₀ ℕ)
    (hb : ∀ (l : Fin (Dt.nL j)) (a : Fin r), Dt.sgn j l = false → b (⟨j, Sum.inl l⟩, a) = 0)
    (Pi' : MvPolynomial (ML J Dt.nL r × Fin r) (KK O))
    (hsupp : Pi' ∈ supported (KK O) {v | ∀ (j' : ZMod J) (m : Fin r) (h : 1 ≤ m.val), v.1 ≠ ML.tp j' m h})
    (T : WithTop ℤ) (hval : T ≤ valS Dt.modelLet (Dt.chainML j i) Pi') :
    T ≤ valS Dt.modelLet (Dt.chainML j i) (Dt.Fdig rho (monomial b 1 * Dt.ph Pi')) := by
  obtain ⟨w, hw⟩ : ∃ w : Set (ML J Dt.nL r), w = {x | ∃ (j' : ZMod J) (m : Fin r), x = ML.lab j' m} := ⟨_, rfl⟩
  have hdisj : Disjoint (Dt.chainML j i) w := by
    rw [Set.disjoint_left]
    intro x hx hxw
    rw [hw] at hxw
    obtain ⟨j', m', rfl⟩ := hxw
    rcases (hch _).1 hx with ⟨m, h⟩ | ⟨l, h, _⟩ <;> cases h
  have e1 : Dt.ph Pi' = ∑ M ∈ Pi'.support.image (fun μ => μ.filter (fun v => v.1 ∈ w)),
      Dt.ph (monomial M 1) * Dt.ph (wCoeff w M Pi') := by
    conv_lhs => rw [sum_wCoeff w Pi']
    rw [map_sum]
    exact Finset.sum_congr rfl fun M _ => map_mul _ _ _
  rw [e1, Finset.mul_sum, hFS]
  refine le_valS_sum _ _ _ _ _ fun M hM => ?_
  have hsM : wCoeff w M Pi' ∈ supported (KK O) {v | IsLW v.1} := by
    refine mem_supported_of _ _ fun ν hν v hv => ?_
    rw [mem_support_iff, coeff_wCoeff] at hν
    split_ifs at hν with hc
    · have hnw : v.1 ∉ w := by
        intro hvw
        have h1 : (ν.filter (fun v => v.1 ∈ w)) v = ν v := Finsupp.filter_apply_pos _ _ hvw
        rw [hc.1] at h1
        exact (Finsupp.mem_support_iff.1 hv) h1.symm
      have hMν : M + ν ∈ Pi'.support := mem_support_iff.2 hν
      have hvM : v ∈ (M + ν).support := by
        rw [Finsupp.mem_support_iff, Finsupp.add_apply]
        have := Finsupp.mem_support_iff.1 hv
        omega
      have htp := of_mem_supported hsupp hMν hvM
      obtain ⟨x, a⟩ := v
      cases x with
      | ll j' l => trivial
      | lab j' m => exact absurd (show ML.lab j' m ∈ w by rw [hw]; exact ⟨j', m, rfl⟩) hnw
      | wc j' m => trivial
      | tp j' m h => exact absurd rfl (htp j' m h)
    · exact absurd rfl hν
  rw [hPM, ← mul_assoc, monomial_mul, one_mul, hFP p O r J Dt hP rho _ _ _ hsM]
  split_ifs with hd
  · refine le_trans ?_ (flt_valS_mul_ge _ _ _ _)
    have h0 : (0 : WithTop ℤ) ≤
        valS Dt.modelLet (Dt.chainML j i) (monomial (liftMon Dt (b + phExp Dt M)) (1 : KK O)) := by
      refine hNN (KK O) _ r Dt.modelLet _ _ fun v hv hvS => ?_
      rw [vars_monomial one_ne_zero] at hv
      obtain ⟨x, a⟩ := v
      rcases (hch x).1 hvS with ⟨m, rfl⟩ | ⟨l, rfl, _⟩
      · rfl
      · show Dt.sgn j l = true
        by_contra hs
        have hs' : Dt.sgn j l = false := by simpa using hs
        have h1 := liftMon_w Dt (b + phExp Dt M) (⟨j, Sum.inl l⟩, a)
        have h2 : Dt.liftVar (⟨j, Sum.inl l⟩, a) = (ML.ll j l, a) := rfl
        have h3 : Pof Dt (⟨j, Sum.inl l⟩, a) = 1 := rfl
        have h4 : phExp Dt M (⟨j, Sum.inl l⟩, a) = M (ML.ll j l, a) := rfl
        have h5 : M (ML.ll j l, a) = 0 := by
          obtain ⟨μ, _, rfl⟩ := Finset.mem_image.1 hM
          refine Finsupp.filter_apply_neg _ _ ?_
          rw [hw]
          rintro ⟨j', m', h⟩
          cases h
        rw [h2, h3, Nat.div_one, Finsupp.add_apply, h4, h5, hb l a hs', add_zero] at h1
        exact (Finsupp.mem_support_iff.1 hv) h1
    have h1 : T ≤ valS Dt.modelLet (Dt.chainML j i) (wCoeff w M Pi') :=
      le_trans hval (valS_wCoeff_of_disj _ _ w hdisj Pi' M)
    calc T = 0 + T := (zero_add T).symm
      _ ≤ _ := add_le_add h0 h1
  · rw [valS_zero_eq_top]; exact le_top

end Core

theorem restChain_of (hVA : ValAeval) (hVF : ValFilt) (hNN : ValNN) (hPM : PhMon) (hCP : CompPh)
    (hFP : FdigPh) (hFS : FdigSum) : RestChain := by
  intro p _ n' r K m _ _ _ O _ _ _ _ hk Fr L₁ N₁ hV hn J _ Dt hT hJ A hA l hl ga hga t ht dPl rho' j i
  have hr : 1 ≤ r := NeZero.one_le
  obtain ⟨hTr1, hTr2⟩ := restTr p n' r K m O hk Fr L₁ N₁ hV hn J Dt hT A hA l hl ga hga
  obtain ⟨b, hb⟩ : ∃ b, b = plMon Fr p hk Dt.nL (l.mapDomain (castV hk) + ga) := ⟨_, rfl⟩
  rw [← hb] at hTr1 hTr2
  obtain ⟨Pi, hPi⟩ : ∃ Pi, Pi = ∏ j' : ZMod J,
      chi Fr Dt.nL (KK O) j' (MvPolynomial.map (algebraMap O (KK O)) (A (segZ j'))) := ⟨_, rfl⟩
  have hH : levP Fr p hk Dt.nL (zPl p O hk Fr A l ga) = monomial b 1 * Dt.ph Pi := by
    rw [hTr1, hPi, map_prod]
  rw [hH, hCP p O r J Dt dPl b 1 Pi]
  have hJF : J = Fr.J := hT.1
  have hsuppA : ∀ j' : ZMod J, MvPolynomial.map (algebraMap O (KK O)) (A (segZ j')) ∈
      supported (KK O) {v : ℤ × Fin r | v.1 ∈ Fr.letters (segZ j')} := by
    intro j'
    have hlt : j'.val < Fr.J := by rw [← hJF]; exact ZMod.val_lt j'
    have h1 : A (segZ j') ∈ supported O {v : ℤ × Fin r | v.1 ∈ Fr.letters (segZ j')} := hA j'.val hlt
    rw [mem_supported] at h1 ⊢
    intro v hv
    exact h1 (Finset.mem_coe.2 ((vars_map _ _) (Finset.mem_coe.1 hv)))
  have hPisupp : Pi ∈ supported (KK O) {v | ∀ (j' : ZMod J) (m : Fin r) (h : 1 ≤ m.val), v.1 ≠ ML.tp j' m h} := by
    rw [hPi]
    exact Subalgebra.prod_mem _ fun j' _ => chi_supp (Fr := Fr) Dt j' _ _ fun y _ a =>
      show ∀ (j'' : ZMod J) (m : Fin r) (h : 1 ≤ m.val), (mlOf Fr Dt.nL j' y, a).1 ≠ ML.tp j'' m h from
        fun j'' m h => mlOf_ne_tp (Fr := Fr) Dt j' y j'' m h
  have hu : i.val < Dt.nL j + r := by
    have := i.isLt
    have h2 := hT.2.2.2.2.1 j
    omega
  have hPival : ((⌈t j i.val⌉ : ℤ) : WithTop ℤ) ≤ valS Dt.modelLet (Dt.chainML j i) Pi := by
    rw [hPi, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
    refine le_trans ?_ (flt_valS_mul_ge _ _ _ _)
    have h1 : ((⌈t j i.val⌉ : ℤ) : WithTop ℤ) ≤ valS Dt.modelLet (Dt.chainML j i)
        (chi Fr Dt.nL (KK O) j (MvPolynomial.map (algebraMap O (KK O)) (A (segZ j)))) := by
      refine le_trans (ceil_le_of_geZ (ht j i.val hu)) ?_
      rw [← Formalism.MainNotions.G.Joints.StandardMonomialSpace.valS_map (algebraMap O (KK O)) (IsFractionRing.injective O (KK O))]
      exact val_chi Dt hVA hV hT j i _ (hsuppA j)
    have h2 : (0 : WithTop ℤ) ≤ valS Dt.modelLet (Dt.chainML j i) (∏ j' ∈ Finset.univ.erase j,
        chi Fr Dt.nL (KK O) j' (MvPolynomial.map (algebraMap O (KK O)) (A (segZ j')))) := by
      have hs : (∏ j' ∈ Finset.univ.erase j,
          chi Fr Dt.nL (KK O) j' (MvPolynomial.map (algebraMap O (KK O)) (A (segZ j')))) ∈
          supported (KK O) {v : ML J Dt.nL r × Fin r | v.1 ∉ Dt.chainML j i} :=
        Subalgebra.prod_mem _ fun j' hj' => chi_supp Dt j' _ _ fun y hy a =>
          chi_out Dt hV hT j j' (Finset.ne_of_mem_erase hj') i y hy
      refine hNN (KK O) _ r Dt.modelLet _ _ fun v hv hvS => ?_
      exact absurd hvS ((mem_supported.1 hs) (Finset.mem_coe.2 hv))
    calc ((⌈t j i.val⌉ : ℤ) : WithTop ℤ) = ((⌈t j i.val⌉ : ℤ) : WithTop ℤ) + 0 := (add_zero _).symm
      _ ≤ _ := add_le_add h1 h2
  refine geZ_of_ceil_le (chain_core Dt hNN hPM hFP hFS ?_ j i (chain_mem Dt hT j i) rho' b
    (fun l a h => hTr2 j l a h) _ ?_ _ (le_trans hPival (hVF _ _ _ _ _ _ _)))
  · intro j' m'
    show 0 < p ^ Dt.gP j' m'
    exact pow_pos (Fact.out : p.Prime).pos _
  · exact mem_supported_of _ _ fun mo hmo v hv => of_mem_supported hPisupp (support_filtQ _ _ hmo) hv

end Formalism.MainNotions.TraceSpectra
