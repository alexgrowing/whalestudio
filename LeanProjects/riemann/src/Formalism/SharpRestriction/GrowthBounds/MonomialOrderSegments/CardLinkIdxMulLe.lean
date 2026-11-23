import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.CgeZeroIffIntegral
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.ProjKeepsLetter
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.AddMemSupportOfMemSupportCoefOut
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.SlopeOfBinomCombGen
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.DigitPartMonomial

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

namespace TwistData

variable {K : Type} [Field K] (D : TwistData K)

theorem mem_Tset (j : Fin D.J) (m : Fin D.r) (z : D.OL) :
    z ∈ D.Tset j m ↔ (∃ b, D.seg b = j ∧ z = Sum.inl b) ∨ (∃ m', m < m' ∧ z = Sum.inr (j, m')) := by
  simp only [Tset, LLj, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (⟨b, hb, rfl⟩ | ⟨m', hm', rfl⟩)
    · exact Or.inl ⟨b, hb, rfl⟩
    · exact Or.inr ⟨m', hm', rfl⟩
  · rintro (⟨b, hb, rfl⟩ | ⟨m', hm', rfl⟩)
    · exact Or.inl ⟨b, hb, rfl⟩
    · exact Or.inr ⟨m', hm', rfl⟩

theorem Tset_mono (j : Fin D.J) {m m' : Fin D.r} (h : m ≤ m') : D.Tset j m' ⊆ D.Tset j m := by
  intro z hz
  rw [mem_Tset] at hz ⊢
  rcases hz with hz | ⟨m'', hm'', rfl⟩
  · exact Or.inl hz
  · exact Or.inr ⟨m'', lt_of_le_of_lt h hm'', rfl⟩

theorem Tset_disjoint {j j' : Fin D.J} (h : j ≠ j') (m m' : Fin D.r) :
    Disjoint (D.Tset j m) (D.Tset j' m') := by
  rw [Finset.disjoint_left]
  intro z hz hz'
  rw [mem_Tset] at hz hz'
  rcases hz with ⟨b, hb, rfl⟩ | ⟨m1, -, rfl⟩
  · rcases hz' with ⟨b', hb', e⟩ | ⟨m2, -, e⟩
    · have : b = b' := Sum.inl.inj e
      subst this
      exact h (hb.symm.trans hb')
    · cases e
  · rcases hz' with ⟨b', -, e⟩ | ⟨m2, -, e⟩
    · cases e
    · have := Sum.inr.inj e
      exact h (congrArg Prod.fst this)

theorem Tset_pair (x y : Fin D.J × Fin D.r) :
    D.Tset x.1 x.2 ⊆ D.Tset y.1 y.2 ∨ D.Tset y.1 y.2 ⊆ D.Tset x.1 x.2 ∨
      Disjoint (D.Tset x.1 x.2) (D.Tset y.1 y.2) := by
  obtain ⟨j, m⟩ := x
  obtain ⟨j', m'⟩ := y
  by_cases h : j = j'
  · subst h
    rcases le_total m m' with h | h
    · exact Or.inr (Or.inl (D.Tset_mono j h))
    · exact Or.inl (D.Tset_mono j h)
  · exact Or.inr (Or.inr (D.Tset_disjoint h m m'))

def linkIdx : Finset (Fin D.J × Fin D.r) := univ.filter fun x => x.2.val + 2 ≤ D.r

theorem card_linkIdx_le : D.linkIdx.card ≤ D.J * (D.r - 1) := by
  classical
  have h1 : D.linkIdx ⊆ (univ : Finset (Fin D.J)) ×ˢ (univ.filter fun m : Fin D.r => m.val + 2 ≤ D.r) := by
    intro x hx
    simp only [linkIdx, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp [hx]
  have h2 : (univ.filter fun m : Fin D.r => m.val + 2 ≤ D.r).card ≤ D.r - 1 := by
    have := Finset.card_le_card_of_injOn (s := univ.filter fun m : Fin D.r => m.val + 2 ≤ D.r)
      (t := Finset.range (D.r - 1)) (fun m => m.val)
      (by
        intro m hm
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hm
        simp only [Finset.coe_range, Set.mem_Iio]
        omega)
      (by intro a _ b _ hab; exact Fin.ext hab)
    simpa using this
  calc D.linkIdx.card ≤ _ := Finset.card_le_card h1
    _ = D.J * (univ.filter fun m : Fin D.r => m.val + 2 ≤ D.r).card := by
        rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
    _ ≤ D.J * (D.r - 1) := Nat.mul_le_mul_left _ h2

theorem eC_nonneg' {p : ℕ} (hp : 2 ≤ p) (hr : 1 ≤ D.r) {C0 : ℝ} (h1 : 1 ≤ C0) : 0 ≤ D.eC p C0 := by
  unfold eC
  have := lg_ge_one hp hr (2 * D.totDeg)
  positivity

theorem Dm_nonneg' {p : ℕ} (hp : 2 ≤ p) (hr : 1 ≤ D.r) {C0 : ℝ} (h1 : 1 ≤ C0) : 0 ≤ D.Dm p C0 := by
  unfold Dm
  have := D.eC_nonneg' hp hr h1
  exact Finset.sum_nonneg fun j _ => by positivity

theorem Dl_nonneg' {p : ℕ} (hp : 2 ≤ p) (hr : 1 ≤ D.r) {C0 : ℝ} (h1 : 1 ≤ C0) : 0 ≤ D.Dl p C0 := by
  unfold Dl
  have := D.eC_nonneg' hp hr h1
  have h2 : (0 : ℝ) ≤ (D.r : ℝ) - 1 := by
    have : (1 : ℝ) ≤ D.r := by exact_mod_cast hr
    linarith
  positivity

theorem kapD_nonneg' {p : ℕ} (hp : 2 ≤ p) (hr : 1 ≤ D.r) : 0 ≤ D.kapD p := by
  unfold kapD
  refine le_trans ?_ (kap_ge_card hp hr D.dO)
  positivity

theorem card_linkIdx_mul_le {p : ℕ} (hp : 2 ≤ p) (hr : 1 ≤ D.r) {C0 : ℝ} (h1 : 1 ≤ C0) :
    (D.linkIdx.card : ℝ) * ((D.r : ℝ) ^ 2 * lg p D.r (2 * ∑ i, D.dO i)) ≤ D.Dl p C0 := by
  have he : (D.r : ℝ) ^ 2 * lg p D.r (2 * ∑ i, D.dO i) = D.eC p C0 := rfl
  rw [he]
  unfold Dl
  have h2 : (D.linkIdx.card : ℝ) ≤ (D.J : ℝ) * ((D.r : ℝ) - 1) := by
    have := D.card_linkIdx_le
    have h3 : ((D.linkIdx.card : ℕ) : ℝ) ≤ ((D.J * (D.r - 1) : ℕ) : ℝ) := by exact_mod_cast this
    rw [Nat.cast_mul, Nat.cast_sub hr, Nat.cast_one] at h3
    exact h3
  exact mul_le_mul_of_nonneg_right h2 (D.eC_nonneg' hp hr h1)

end TwistData

section StepB

variable {K : Type} [Field K] [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ} {C0 : ℝ}

theorem stepB_of (h1 : 1 ≤ C0) (hV2 : V2 K) (hP : PROJ K v p C0) : StepB K v p C0 := by
  classical
  intro hD D hV hc F hF hF0
  obtain ⟨hr, hJ, hc1, -, -, hthl, hga, hgaε⟩ := hV
  haveI : NeZero D.r := ⟨by omega⟩
  have hp : 2 ≤ p := two_le_p hD
  have hr1 : 1 ≤ D.r := hr
  obtain ⟨⟨α0, hα0, hge0, hle0⟩, hbF⟩ := exists_of_vBB_zero v F hF0
  obtain ⟨hFP, -, hFl⟩ := hF
  obtain ⟨Pr, p1, p2, p3, p4, -, -⟩ := prodProj (r := D.r) D.osg D.dO hP hD D.linkIdx
    (fun x => D.Tset x.1 x.2) (fun x => ⌈D.thl x.1 x.2⌉) (fun x _ y _ => D.Tset_pair x y)
  have hα0d : ∀ i, ldeg α0 i = D.dO i := (mem_PolK_iff _ _).mp hFP α0 hα0
  have hmon : (monomial α0 (1 : K)) ∈ PolK K D.r D.dO := by
    rw [mem_PolK_iff]
    intro β hβ
    have := support_monomial_subset hβ
    rw [Finset.mem_singleton] at this
    rw [this]; exact hα0d
  have hDm := D.Dm_nonneg' hp hr1 h1
  have hDl := D.Dl_nonneg' hp hr1 h1
  have hkap := D.kapD_nonneg' hp hr1
  have hcc : 4 * (D.Dm p C0 + D.Dl p C0 + 3 * D.kapD p) < D.c := hc

  have hY1 : Pr (monomial α0 1) ∈ PolK K D.r D.dO := p1 _ hmon
  have hY2 : ∀ (j : Fin D.J) (m : Fin D.r), m.val + 2 ≤ D.r →
      vala D.osg (D.Tset j m) (D.thl j m) (Pr (monomial α0 1)) := fun j m hm =>
    (vala_iff_Aset _ _ _ _).mpr (p2 _ hmon (j, m) (by simp [TwistData.linkIdx, hm]))
  have hY3 : fock F (Pr (monomial α0 1)) = F.coeff α0 * 1 * (fact α0 : K) := by
    rw [p3 F hFP (fun x hx => ?_) _ hmon, fock_monomial_right]
    have hx' : x.2.val + 2 ≤ D.r := by simpa [TwistData.linkIdx] using hx
    exact (vala_iff_Aset _ _ _ _).mp (hFl x.1 x.2 hx')
  have hY4 : bge v (vN v (fact α0) / 2 - D.Dl p C0) (Pr (monomial α0 1)) := by
    have h := p4 _ hmon _ (bge_monomial v α0 (vge_one v))
    refine bge_mono v ?_ h
    have := D.card_linkIdx_mul_le hp hr1 h1
    linarith
  have hY5 : vle v (vN v (fact α0) / 2) (fock F (Pr (monomial α0 1))) := by
    rw [hY3, mul_one]
    have := vle_mul v hle0 (vle_vN hD (fact_ne_zero α0))
    exact vle_mono v (by linarith) this

  obtain ⟨T, lam, hlam, hT⟩ := hgaε (-1) (Or.inr rfl)
  have hC : CostOK (CostV (K := K) (r := D.r) D.osg Set.univ) :=
    costV_ok _ _ (fun S _ θ F G => vala_add) (fun S _ θ a F => vala_smul a)
  have hch : ∀ (x : D.OL × Fin D.r) (k : ℕ),
      CostV D.osg Set.univ k (fun α : D.OL × Fin D.r →₀ ℕ => ((α x).choose k : K)) :=
    fun x k S _ θ F h => vala_dg_choose hV2 x k h
  obtain ⟨g, hg0, hgc, hgC⟩ := approx_of_trunc (v := v) hC hch T lam hlam (fun α => D.ga α ^ (-1 : ℤ)) hT

  have hsplit : D.gaAct (dg g (Pr (monomial α0 1))) =
      Pr (monomial α0 1) + dg (fun α => D.ga α * g α - 1) (Pr (monomial α0 1)) := by
    rw [gaAct_eq_dg]
    ext α
    rw [coeff_add, coeff_dg, coeff_dg, coeff_dg]
    ring
  have herr : ∀ α, vge v (D.c : ℝ) (D.ga α * g α - 1) := by
    intro α
    have hne : D.ga α ≠ 0 := by
      intro h0
      have := hga α
      rw [h0, AddValuation.map_zero] at this
      exact absurd this (by simp)
    have e : D.ga α * g α - 1 = -(D.ga α * (D.ga α ^ (-1 : ℤ) - g α)) := by
      rw [zpow_neg_one]; field_simp; ring
    rw [e]
    have h2 := vge_mul v (vge_unit v (hga α)).1 ((vge_natCast_bound v D.c _).mpr (hgc α))
    rw [zero_add] at h2
    exact vge_neg v h2
  have hpair : vle v (vN v (fact α0) / 2) (fock F (D.gaAct (dg g (Pr (monomial α0 1))))) := by
    rw [hsplit, fock_add_right]
    refine vle_add_of_lt v hY5 (vge_fock v hbF (bge_dg v herr hY4)) ?_
    linarith

  have ha0 : vN v (fact α0) / 2 ≤ D.n0 v := by
    have := fact_upper hD hα0d
    have h4 : D.n0 v = vN v (∏ i : D.OL, (D.dO i).factorial) / 2 := rfl
    rw [h4]; linarith
  have hx0 : 0 ≤ D.n0 v + D.Dl p C0 - vN v (fact α0) / 2 := by linarith
  have hG2P : dg g (Pr (monomial α0 1)) ∈ PolK K D.r D.dO := by
    rw [mem_PolK_iff]
    intro β hβ
    exact (mem_PolK_iff _ _).mp hY1 β (support_dg_subset g _ hβ)
  have hG2b : bge v (0 + (vN v (fact α0) / 2 - D.Dl p C0)) (dg g (Pr (monomial α0 1))) :=
    bge_dg v (fun α => (vge_zero_iff v _).mpr (hg0 α)) hY4
  refine ⟨((p : K) ^ ⌈D.n0 v + D.Dl p C0 - vN v (fact α0) / 2⌉₊) • dg g (Pr (monomial α0 1)),
    ⟨Submodule.smul_mem _ _ hG2P, ?_⟩, ?_, ?_⟩
  · rw [← cge_zero_iff_Integral]
    have h5 := cge_smul v (vge_p_pow hD ⌈D.n0 v + D.Dl p C0 - vN v (fact α0) / 2⌉₊)
      (cge_of_bge hD hG2P hG2b)
    refine cge_mono v ?_ h5
    have h6 := Nat.le_ceil (D.n0 v + D.Dl p C0 - vN v (fact α0) / 2)
    have h4 : D.n0 v = vN v (∏ i : D.OL, (D.dO i).factorial) / 2 := rfl
    linarith
  · intro j m hm
    have h7 := hgC (D.Tset j m) (Set.mem_univ _) _ _ (hY2 j m hm)
    have e : D.thl j m - ((6 * D.c : ℕ) : ℝ) = D.thl j m - 6 * D.c := by push_cast; ring
    rw [e] at h7
    exact vala_smul _ h7
  · have e1 : fock F (D.gaAct (((p : K) ^ ⌈D.n0 v + D.Dl p C0 - vN v (fact α0) / 2⌉₊) •
        dg g (Pr (monomial α0 1)))) =
        (p : K) ^ ⌈D.n0 v + D.Dl p C0 - vN v (fact α0) / 2⌉₊ *
          fock F (D.gaAct (dg g (Pr (monomial α0 1)))) := by
      simp only [gaAct_eq_dg, map_smul, fock_smul_right]
    rw [e1]
    refine vle_mono v ?_ (vle_pow_p hD _ hpair)
    have h8 := Nat.ceil_lt_add_one hx0
    linarith

end StepB

end Formalism.MainNotions.PlaneGram
