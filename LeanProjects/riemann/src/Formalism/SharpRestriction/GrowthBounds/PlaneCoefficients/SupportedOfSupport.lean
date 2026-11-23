import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.RestPlOf
import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.TensZeroRight
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MemSupportSumMonomial
import Formalism.SharpRestriction.GrowthBounds.ValuationLowestDegreeMapFractionField

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.Proposition5Numerics Formalism.MainNotions.TraceSpectra
open Formalism.MainNotions.TestSideWords.TwistedFiltration.G3 Formalism.MainNotions.G.GLWeightTheory

namespace Lk

theorem homComp_eq {ι : Type} {s : ℕ} {Kf : Type} [Field Kf] (d : ι → ℕ) (H : MvPolynomial (ι × Fin s) Kf) :
    homComp d H = compD d H := rfl

theorem compD_support {ι : Type} {s : ℕ} {Kf : Type} [Field Kf] (d : ι → ℕ) (H : MvPolynomial (ι × Fin s) Kf)
    (mo : ι × Fin s →₀ ℕ) (hmo : mo ∈ (compD d H).support) : mo ∈ H.support ∧ ∀ x, multideg mo x = d x := by
  unfold compD at hmo
  obtain ⟨a, ha, hmo'⟩ := Finset.mem_biUnion.1 (support_sum hmo)
  have := support_monomial_subset hmo'
  rw [Finset.mem_singleton] at this
  subst this
  exact ⟨(Finset.mem_filter.1 ha).1, (Finset.mem_filter.1 ha).2⟩

theorem compD_sum {ι κ : Type} {s : ℕ} {Kf : Type} [Field Kf] (d : ι → ℕ) (T : Finset κ)
    (f : κ → MvPolynomial (ι × Fin s) Kf) : compD d (∑ i ∈ T, f i) = ∑ i ∈ T, compD d (f i) :=
  map_sum (AddMonoidHom.mk ⟨compD d, T5.compD_zero d⟩ (T5.compD_add d)) f T

theorem compD_eq_zero {ι : Type} {s : ℕ} {Kf : Type} [Field Kf] (d : ι → ℕ) (H : MvPolynomial (ι × Fin s) Kf)
    (h : ∀ mo ∈ H.support, ∃ x, multideg mo x ≠ d x) : compD d H = 0 := by
  unfold compD
  refine Finset.sum_eq_zero fun mo hmo => ?_
  obtain ⟨x, hx⟩ := h mo (Finset.mem_filter.1 hmo).1
  exact absurd ((Finset.mem_filter.1 hmo).2 x) hx

theorem supported_of_support {τ R : Type*} [CommSemiring R] {s : Set τ} {P Q : MvPolynomial τ R}
    (h : P.support ⊆ Q.support) (hQ : Q ∈ supported R s) : P ∈ supported R s := by
  rw [mem_supported] at hQ ⊢
  intro v hv
  obtain ⟨d, hd, hvd⟩ := (mem_vars_iff_mem_support v).1 (Finset.mem_coe.1 hv)
  exact hQ (Finset.mem_coe.2 ((mem_vars_iff_mem_support v).2 ⟨d, h hd, hvd⟩))

theorem multideg_add {ι : Type} {s : ℕ} (a b : ι × Fin s →₀ ℕ) (x : ι) :
    multideg (a + b) x = multideg a x + multideg b x := by
  unfold multideg
  simp only [Finsupp.add_apply, Finset.sum_add_distrib]

theorem geZ_sum {Kf : Type} [Field Kf] {ι κ : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι) (T : Finset κ)
    (f : κ → MvPolynomial (ι × Fin n) Kf) (t : ℝ) (h : ∀ i ∈ T, geZ (valS LL S (f i)) t) :
    geZ (valS LL S (∑ i ∈ T, f i)) t := by
  induction T using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, valS_zero_eq_top]
    exact geZ_top _
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact geZ_mono (mul_valS_add _ _ _ _) (geZ_min (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem le_of_geZ {x : WithTop ℤ} {t : ℝ} (h : geZ x t) : ((⌈t⌉ : ℤ) : WithTop ℤ) ≤ x := by
  induction x using WithTop.recTopCoe with
  | top => exact le_top
  | coe k => exact WithTop.coe_le_coe.2 (Int.ceil_le.2 (h k rfl))

theorem geZ_coe {k : ℤ} {t : ℝ} (h : t ≤ (k : ℝ)) : geZ ((k : ℤ) : WithTop ℤ) t := by
  intro k' hk'
  have : k = k' := WithTop.coe_injective hk'
  rw [← this]
  exact h

end Lk

theorem restLink_of (hNN : ValNN) (hHD : HomDec) (hLL : LinkL) (hDg : LkDeg) (hVr : LkVars) (hTr : RestTr)
    (hW : ∀ {n' r : ℕ} (Fr : Frames n' r) (jz : ℤ) (μ : ℤ × Fin r →₀ ℕ),
      wDeg (wSet Fr jz) μ ≤ ∑ m' : Fin r, multideg μ (Fr.fr (jz - 1) (r - 1 - m'.val))) : RestLink := by
  intro p _ n' r K m _ _ _ O _ _ _ _ hk Fr L₁ N₁ hV hn J _ Dt hT hJ A hA l hl ga hga t ht dPl j mm hm
  obtain ⟨hEq, hcov⟩ := hTr p n' r K m O hk Fr L₁ N₁ hV hn J Dt hT A hA l hl ga hga
  have hp : 0 < p := (Fact.out : p.Prime).pos
  set μ0 := plMon Fr p hk Dt.nL (l.mapDomain (castV hk) + ga) with hμ0
  set u := Dt.nL j + (r - 1 - mm.val) with hu
  have hur : u < Dt.nL j + r := by omega
  set Ab : ZMod J → MvPolynomial (ℤ × Fin r) (KK O) :=
    fun j' => MvPolynomial.map (algebraMap O (KK O)) (A (segZ j')) with hAb
  set Rst : MvPolynomial (TL J Dt.nL r × Fin r) (KK O) :=
    monomial μ0 1 * ∏ j' ∈ Finset.univ.erase j, PhiJ Fr Dt j' (Ab j') with hRst
  have e1 : levP Fr p hk Dt.nL (zPl p O hk Fr A l ga) = Rst * PhiJ Fr Dt j (Ab j) := by
    rw [hEq, hRst]
    have : ∏ j' : ZMod J, Dt.ph (chi Fr Dt.nL (KK O) j' (MvPolynomial.map (algebraMap O (KK O)) (A (segZ j')))) =
        PhiJ Fr Dt j (Ab j) * ∏ j' ∈ Finset.univ.erase j, PhiJ Fr Dt j' (Ab j') :=
      (Finset.mul_prod_erase Finset.univ (fun j' => PhiJ Fr Dt j' (Ab j')) (Finset.mem_univ j)).symm
    rw [this]
    ring

  have hR0 : 0 ≤ valS Dt.trueLet (Dt.TSet j mm) Rst := by
    apply hNN
    intro v hv hvT
    rcases Finset.mem_union.1 (vars_mul _ _ hv) with h1 | h1
    · rw [vars_monomial one_ne_zero] at h1
      have h2 : μ0 v ≠ 0 := Finsupp.mem_support_iff.1 h1
      obtain ⟨⟨j'', s⟩, a⟩ := v
      cases s with
      | inl ll =>
        by_contra hs
        have hs' : Dt.sgn j'' ll = false := by
          have : Dt.trueLet.vec ⟨j'', Sum.inl ll⟩ = Dt.sgn j'' ll := rfl
          rw [this] at hs
          simpa using hs
        exact h2 (hcov j'' ll a hs')
      | inr m' => rfl
    · obtain ⟨j', hj', h2⟩ := Finset.mem_biUnion.1 (vars_prod _ h1)
      have hne : j' ≠ j := (Finset.mem_erase.1 hj').1
      rcases hVr p n' r O Fr J Dt j' (Ab j') v h2 with ⟨ll, h3⟩ | ⟨j'', m', h3⟩
      · exfalso
        rw [h3] at hvT
        rcases hvT with ⟨l', h4⟩ | ⟨m', _, h4⟩
        · exact hne (congrArg Sigma.fst h4)
        · exact hne (congrArg Sigma.fst h4)
      · rw [h3]
        rfl

  obtain ⟨Dl, hDl⟩ := hHD (KK O) ℤ r (Ab j)
  have e2 : compD dPl (Rst * PhiJ Fr Dt j (Ab j)) =
      ∑ δ ∈ Dl, compD dPl (Rst * PhiJ Fr Dt j (compD δ (Ab j))) := by
    conv_lhs => rw [hDl]
    rw [map_sum, Finset.mul_sum, Lk.compD_sum]
    rfl
  rw [e1, e2]
  refine Lk.geZ_sum _ _ _ _ _ fun δ _ => ?_
  set F := compD δ (Ab j) with hF
  have hjv : j.val < Fr.J := by
    rw [← hT.1]
    exact ZMod.val_lt j
  have hAbS : Ab j ∈ supported (KK O) {v : ℤ × Fin r | v.1 ∈ Fr.letters (segZ j)} := by
    have h1 := hA j.val hjv
    rw [mem_supported] at h1 ⊢
    exact fun v hv => h1 (Finset.mem_coe.2 (vars_map (A (segZ j)) (algebraMap O (KK O)) (Finset.mem_coe.1 hv)))
  have hFS : F ∈ supported (KK O) {v : ℤ × Fin r | v.1 ∈ Fr.letters (segZ j)} :=
    Lk.supported_of_support (fun mo hmo => (Lk.compD_support δ (Ab j) mo hmo).1) hAbS
  have hFd : ∀ μ ∈ F.support, ∀ y, multideg μ y = δ y := fun μ hμ => (Lk.compD_support δ (Ab j) μ hμ).2
  have hdeg := hDg p n' r O Fr L₁ N₁ hV J Dt hT hJ j F hFS δ hFd
  by_cases hbig : ∃ m' : Fin r, dPl ⟨j - 1, Sum.inr m'⟩ <
      multideg μ0 ⟨j - 1, Sum.inr m'⟩ + Dt.P (j - 1) m' * δ (Fr.fr (segZ j - 1) (r - 1 - m'.val))
  ·
    obtain ⟨m', hm'⟩ := hbig
    rw [Lk.compD_eq_zero, valS_zero_eq_top]
    · exact geZ_top _
    · intro mo hmo
      refine ⟨⟨j - 1, Sum.inr m'⟩, ?_⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 (support_mul _ _ hmo)
      obtain ⟨a0, ha0, c, _, rfl⟩ := Finset.mem_add.1 (support_mul _ _ ha)
      have h0 := support_monomial_subset ha0
      rw [Finset.mem_singleton] at h0
      subst h0
      rw [Lk.multideg_add, Lk.multideg_add, hdeg b hb m']
      omega
  · push Not at hbig
    set dw : ℕ := ∑ m' : Fin r, δ (Fr.fr (segZ j - 1) (r - 1 - m'.val)) with hdw
    have hwd : ∀ μ ∈ F.support, wDeg (wSet Fr (segZ j)) μ ≤ dw := by
      intro μ hμ
      refine le_trans (hW Fr (segZ j) μ) (le_of_eq ?_)
      exact Finset.sum_congr rfl fun m' _ => hFd μ hμ _
    have hdwB : (dw : ℝ) ≤ dwB Fr hk Dt dPl (l.mapDomain (castV hk) + ga) j := by
      unfold dwB
      rw [hdw]
      push_cast
      refine Finset.sum_le_sum fun m' _ => ?_
      have hP : (0 : ℝ) < (Dt.P (j - 1) m' : ℝ) := by
        have : 0 < Dt.P (j - 1) m' := pow_pos hp _
        exact_mod_cast this
      rw [le_div_iff₀ hP]
      have h1 := hbig m'
      have h2 : δ (Fr.fr (segZ j - 1) (r - 1 - m'.val)) * Dt.P (j - 1) m' ≤
          dPl ⟨j - 1, Sum.inr m'⟩ - multideg μ0 ⟨j - 1, Sum.inr m'⟩ := by
        rw [mul_comm]
        omega
      exact_mod_cast h2
    have h1 : ((⌈t j u⌉ : ℤ) : WithTop ℤ) ≤ valS LZ {y | y < posU Fr (Dt.nL j) (segZ j) u} F := by
      refine le_trans (Lk.le_of_geZ (ht j u hur)) ?_
      have h2 := (valComp (KK O) ℤ r LZ {y | y < posU Fr (Dt.nL j) (segZ j) u} (Ab j) δ).1
      rw [Lk.homComp_eq] at h2
      refine le_trans (le_of_eq ?_) h2
      exact (Formalism.MainNotions.G.Joints.StandardMonomialSpace.valS_map (algebraMap O (KK O)) (IsFractionRing.injective O (KK O)) LZ _ _).symm
    have h3 := hLL p n' r O Fr L₁ N₁ hV hn J Dt hT hJ j mm hm F hFS dw hwd ⌈t j u⌉ h1
    have h4 : ((⌈t j u⌉ - dw : ℤ) : WithTop ℤ) ≤
        valS Dt.trueLet (Dt.TSet j mm) (compD dPl (Rst * PhiJ Fr Dt j F)) := by
      have h5 := (valComp (KK O) _ r Dt.trueLet (Dt.TSet j mm) (Rst * PhiJ Fr Dt j F) dPl).1
      rw [Lk.homComp_eq] at h5
      refine le_trans ?_ h5
      rw [mul_valS_mul]
      calc ((⌈t j u⌉ - dw : ℤ) : WithTop ℤ) = 0 + ((⌈t j u⌉ - dw : ℤ) : WithTop ℤ) := (zero_add _).symm
        _ ≤ _ := add_le_add hR0 h3
    refine geZ_mono h4 (Lk.geZ_coe ?_)
    have := Int.le_ceil (t j u)
    push_cast
    linarith

end Formalism.MainNotions.PairMembershipBlocks
