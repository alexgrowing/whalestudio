import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.EulerAdditivityDegreeZero
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleGr
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleFin
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleIso
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleShift
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.EulerAdditivityExactSequence
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.EulerAdditivityInSection
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.SumPowersetFinSucc

noncomputable section

namespace Formalism.MainNotions.V.Pf.V2.Calc

open IsLocalRing Filter Finset

namespace Sm

section Gen

variable {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R]

def hdiff (ts : List (Deg k × R)) (F : GMod B R k) (m : Deg k) : ℤ :=
  ∑ I ∈ (Finset.univ : Finset (Fin ts.length)).powerset,
    (-1 : ℤ) ^ I.card * ((Module.length B (F.gr (m - ∑ i ∈ I, (ts.get i).1))).toNat : ℤ)

theorem hdiff_nil (F : GMod B R k) (m : Deg k) :
    hdiff ([] : List (Deg k × R)) F m = ((Module.length B (F.gr m)).toNat : ℤ) := by
  have : (Finset.univ : Finset (Fin ([] : List (Deg k × R)).length)) = ∅ := rfl
  rw [hdiff, this, Finset.powerset_empty, Finset.sum_singleton, Finset.sum_empty, sub_zero,
    Finset.card_empty, pow_zero, one_mul]

theorem hdiff_cons (d : Deg k) (s : R) (ts : List (Deg k × R)) (F : GMod B R k) (m : Deg k) :
    hdiff ((d, s) :: ts) F m = hdiff ts F m - hdiff ts F (m - d) := by
  show ∑ I ∈ (Finset.univ : Finset (Fin (ts.length + 1))).powerset,
        (-1 : ℤ) ^ I.card *
          ((Module.length B (F.gr (m - ∑ i ∈ I, (((d, s) :: ts).get i).1))).toNat : ℤ) = _
  rw [hdiff, hdiff, sum_powerset_fin_succ, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  have hsum : ∀ J : Finset (Fin ts.length),
      ∑ i ∈ J.image Fin.succ, (((d, s) :: ts).get i).1 = ∑ j ∈ J, (ts.get j).1 := fun J => by
    rw [Finset.sum_image (fun a _ b _ hab => Fin.succ_injective _ hab)]
    rfl
  have h0 : ∀ J : Finset (Fin ts.length), (0 : Fin (ts.length + 1)) ∉ J.image Fin.succ :=
    fun J => by
      simp only [mem_image, not_exists, not_and]
      exact fun j _ => Fin.succ_ne_zero j
  congr 1
  · refine Finset.sum_congr rfl fun J _ => ?_
    rw [hsum, Finset.card_image_of_injective _ (Fin.succ_injective _)]
  · refine Finset.sum_congr rfl fun J _ => ?_
    rw [Finset.sum_insert (h0 J), Finset.card_insert_of_notMem (h0 J), hsum,
      Finset.card_image_of_injective _ (Fin.succ_injective _), pow_succ]
    have : m - d - ∑ j ∈ J, (ts.get j).1
        = m - ((((d, s) :: ts).get (0 : Fin (ts.length + 1))).1 + ∑ j ∈ J, (ts.get j).1) := by
      show _ = m - (d + _)
      rw [sub_sub]
    rw [this]
    ring

theorem ev_shift {p : Deg k → Prop} (d : Deg k) (h : ∀ᶠ m in atTop, p m) :
    ∀ᶠ m in atTop, p (m - d) := by
  rw [eventually_atTop] at h ⊢
  obtain ⟨a, ha⟩ := h
  exact ⟨a + d, fun b hb => ha _ (le_sub_iff_add_le.mpr hb)⟩

theorem admissible_of_admissible_nil [IsLocalRing B] (𝒜 : Deg k → Submodule B R) {J : Ideal R}
    (ts : List (Deg k × R)) (h : admitted 𝒜 [] J) : admitted 𝒜 ts J := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, hN.trans (sup_le_sup_left ?_ _)⟩
  rw [secs, Ideal.span_le]
  rintro x ⟨d, hd⟩
  exact absurd hd List.not_mem_nil

def sesSubQuo (F : GMod B R k) (N : Submodule R F.M) : SES (F.sub N) F (F.quo N) where
  f := N.subtype
  g := N.mkQ
  inj := N.injective_subtype
  surj := N.mkQ_surjective
  exact y := by
    constructor
    · intro h
      exact ⟨⟨y, (Submodule.Quotient.mk_eq_zero N).1 h⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact (Submodule.Quotient.mk_eq_zero N).2 x.2
  f_gr _ := rfl
  g_gr _ := rfl

def mulS (F : GMod B R k) (s : R) (d : Deg k) : (F.shift d).M →ₗ[R] F.M := LinearMap.lsmul R F.M s

theorem mulS_gr (𝒜 : Deg k → Submodule B R) {F : GMod B R k} (hF : F.IsGr 𝒜) {s : R} {d : Deg k}
    (hs : s ∈ 𝒜 d) : E7.IsGrHom (F.shift d) F (mulS F s d) := by
  intro m x hx
  have hx' : x ∈ F.gr (m - d) := hx
  have h := hF.smul_mem hs hx'
  rwa [show d + (m - d) = m by abel] at h

end Gen

theorem step (hE1 : EulerAdditivityExactSequence) (hGr : RuleGr) {k : ℕ} (X : HidaSetting k) (ts : List (Deg k × X.R))
    (F : X.Mod) (d : Deg k) (s : X.R) (hV : Valid X.𝒜 ts) (hs : s ∈ X.𝒜 d) (hF : F.IsGr X.𝒜)
    (hA : admitted X.𝒜 [] F.Ann) :
    ∀ᶠ m in atTop, chi ((d, s) :: ts) F m = chi ts F m - chi ts F (m - d) := by
  have hFd := (hGr k X F hF).2.1 d
  obtain ⟨hq, ha⟩ := (hGr k X F hF).2.2 d s hs
  have g := mulS_gr X.𝒜 hF hs
  have hI := ((hGr k X F hF).1 _ (g.range_hom hFd.internal)).1
  have hAt : admitted X.𝒜 ts F.Ann := admissible_of_admissible_nil X.𝒜 ts hA
  have e1 := hE1 k X ts (F.ann s d) (F.shift d) _ hV ha hFd hI
    (E7.sesOfKer (G := F.shift d) (H := F) (LinearMap.ker (LinearMap.lsmul X.R F.M s)) (mulS F s d)
      (fun _ => Iff.rfl) g hFd.internal hF.internal) hAt
  have e2 := hE1 k X ts _ F (F.quot s) hV hI hF hq
    (sesSubQuo F (LinearMap.range (LinearMap.lsmul X.R F.M s))) hAt
  filter_upwards [e1, e2] with m h1 h2
  rw [chi_shift] at h1
  show chi ts (F.quot s) m - chi ts (F.ann s d) m = _
  have h2' : chi ts F m = chi ts (F.sub (LinearMap.range (mulS F s d))) m + chi ts (F.quot s) m := h2
  linarith

end Sm

open Sm in

theorem ruleSmall : RuleSmall := by
  intro k X ts
  induction ts with
  | nil =>
    intro F _ _ _
    refine Eventually.of_forall fun m => ?_
    exact (hdiff_nil F m).symm
  | cons p ts ih =>
    obtain ⟨d, s⟩ := p
    intro F hV hF hA
    have hs : s ∈ X.𝒜 d := (hV (d, s) List.mem_cons_self).2
    have hV' : Valid X.𝒜 ts := fun p hp => hV p (List.mem_cons_of_mem _ hp)
    have h0 : ∀ᶠ m in atTop, chi ts F m = hdiff ts F m := ih F hV' hF hA
    filter_upwards [step (euler_additivity_of_rules ruleGr ruleFin ruleIso) ruleGr X ts F d s hV' hs hF hA, h0,
      ev_shift d h0] with m h1 h2 h3
    rw [h1, h2, h3]
    exact (hdiff_cons d s ts F m).symm

end Formalism.MainNotions.V.Pf.V2.Calc
