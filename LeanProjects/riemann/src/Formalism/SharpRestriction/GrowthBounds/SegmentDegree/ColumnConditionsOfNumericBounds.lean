import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.ValuationLambdaFieldProperties

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

def LateIndexInjective : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r), X.Hyp p K → ∀ j, ∀ x ∈ X.toLate j,
    Function.Injective (X.row j x) ∧ ∀ i, X.row j x i ∈ X.F.letters j ∧ Even (X.row j x i) ∧ X.row j x i < x

def EllDegreeLePowerBound : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r), X.Hyp p K → ∀ j e, X.IsEll p K j e →
    X.dS K j e + X.dV K j e ≤ (r + K) * X.Ns * p ^ X.Rj p K j

def PowerExceedsMaxMultiplicity (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r), X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ j, X.mStar < p ^ X.Rj p K j

def ThresholdPowerLowerBound (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r), X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ j b, X.Step2 p K j b → ∀ x ∈ X.toLate j,
      X.th p j x ≤ ((p ^ X.Rj p K j : ℕ) : ℝ) * (X.thc p K j b x - (((r + K) * X.Ns : ℕ) : ℝ))

theorem mem_late {n' r : ℕ} [NeZero n'] (X : Dat n' r) (j x : ℤ) :
    x ∈ X.toLate j ↔ x ∈ X.F.letters j ∧ ¬ X.F.IsW j x := by
  simp only [Dat.toLate, Finset.mem_filter]

section AG

variable (D : Formalism.BasicNotions.D7) (hV : Formalism.MainNotions.CovariantDegrees.ValuationsAdditive D) {n' r : ℕ} [NeZero n'] [NeZero r] (X : Dat n' r) (p K : ℕ)
  [NeZero K] {R : Type} [Field R] (j : ℤ) (e : ℤ × Fin (r + K) →₀ ℕ) (S : Set ℤ)

include hV

theorem vg_ellP : ((-(X.dS K j e : ℤ) : ℤ) : WithTop ℤ) ≤ valS LZ S (X.ellP K R j e) := by
  have h := vg_prod D hV (R := R) S (X.toLate j)
    (fun x => ∏ c : Fin r, (MvPolynomial.X (x, c) : MvPolynomial (ℤ × Fin r) R) ^ e (x, Fin.castAdd K c))
    (fun x => ∑ c : Fin r, (e (x, Fin.castAdd K c) : ℤ) * (if Even x then 0 else -1))
    (fun x _ => vg_prod D hV S Finset.univ _ _ (fun c _ => vg_pow D hV S (vg_X (R := R) S (x, c)) _))
  have e1 : (∑ x ∈ X.toLate j, ∑ c : Fin r, (e (x, Fin.castAdd K c) : ℤ) * (if Even x then 0 else -1)) =
      -(X.dS K j e : ℤ) := by
    unfold Dat.dS
    push_cast
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> simp
  rw [e1] at h
  exact h

theorem lg_ellN : lam1S LZ S (X.ellN K R j e) ≤ (((X.dV K j e : ℤ) : ℤ) : WithBot ℤ) := by
  have h := lg_prod D hV (R := R) S (X.toLate j)
    (fun x => ∏ c : Fin K, (MvPolynomial.X (x, c) : MvPolynomial (ℤ × Fin K) R) ^ e (x, Fin.natAdd r c))
    (fun x => ∑ c : Fin K, (e (x, Fin.natAdd r c) : ℤ) * (if Even x then 1 else 0))
    (fun x _ => lg_prod D hV S Finset.univ _ _ (fun c _ => lg_pow D hV S (lg_X (R := R) S (x, c)) _))
  have e1 : (∑ x ∈ X.toLate j, ∑ c : Fin K, (e (x, Fin.natAdd r c) : ℤ) * (if Even x then 1 else 0)) =
      (X.dV K j e : ℤ) := by
    unfold Dat.dV
    push_cast
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> simp
  rw [e1] at h
  exact h

theorem vg_DlSeg (hev : ∀ x' ∈ X.toLate j, ∀ i, Even (X.row j x' i)) (x : ℤ) (hx : x ∈ X.toLate j)
    (hinj : Function.Injective (X.row j x)) (hS : ∀ i, X.row j x i ∈ S) :
    (((X.sg p K j x : ℤ) : ℤ) : WithTop ℤ) ≤ valS LZ S (X.DlSeg p K R j) := by
  classical
  have h := vg_prod D hV (R := R) S (X.toLate j) (fun x' => X.detPl R j x' ^ X.sg p K j x')
    (fun x' => if x' = x then (X.sg p K j x : ℤ) else 0) (fun x' hx' => by
      by_cases hxx : x' = x
      · subst hxx
        rw [if_pos rfl]
        have h1 : ((1 : ℤ) : WithTop ℤ) ≤ valS LZ S (X.detPl R j x') := by
          unfold Dat.detPl valS
          rw [sDegs_det LZ S _ (X.row j x') hinj (fun i => ⟨hS i, by simp [LZ, hev x' hx' i]⟩)]
          simp
        have := vg_pow D hV S h1 (X.sg p K j x')
        simpa using this
      · rw [if_neg hxx]
        have := vg_pow D hV S (vg_det D hV (R := R) S (X.row j x') (hev x' hx')) (X.sg p K j x')
        simpa [Dat.detPl] using this)
  rw [Finset.sum_ite_eq' (X.toLate j) x, if_pos hx] at h
  exact h

theorem vg_Aw (hev : ∀ x' ∈ X.toLate j, ∀ i, Even (X.row j x' i)) (x : ℤ) (hx : x ∈ X.toLate j)
    (hinj : Function.Injective (X.row j x)) (hS : ∀ i, X.row j x i ∈ S)
    (nu : Fin (segN X.F j + 1) → Fin r → ℤ) (I' : ℤ → Finset (Fin r)) (a : ℤ)
    (ha : (a : WithTop ℤ) ≤ valS LZ S (segRen X.F j R r (Psi R nu I'))) :
    ((((p ^ X.Rj p K j : ℕ) : ℤ) * a + -(X.dS K j e : ℤ) + (X.sg p K j x : ℤ) : ℤ) : WithTop ℤ) ≤
      valS LZ S (X.Aw p K R j e nu I') := by
  unfold Dat.Aw
  exact vg_mul D hV S (vg_mul D hV S (vg_pow D hV S ha _) (vg_ellP D hV X K j e S))
    (vg_DlSeg D hV X p K j S hev x hx hinj hS)

theorem lg_Gw (ka : Fin (segN X.F j + 1) → Fin K → ℤ) (I'' : ℤ → Finset (Fin K)) (a : ℤ)
    (ha : lam1S LZ S (segRen X.F j R K (Psi R ka I'')) ≤ (a : WithBot ℤ)) :
    lam1S LZ S (X.Gw p K R j e ka I'') ≤ ((((p ^ X.Rj p K j : ℕ) : ℤ) * a + (X.dV K j e : ℤ) : ℤ) : WithBot ℤ) := by
  unfold Dat.Gw
  exact lg_mul D hV S (lg_pow D hV S ha _) (lg_ellN D hV X K j e S)

end AG

theorem int_ineq (Q κ ν dS dV s mS kN : ℤ) (hQ : 0 ≤ Q) (h : κ + (kN + 1) ≤ ν) (hd : dS + dV ≤ kN * Q)
    (hm : mS < Q) : Q * κ + dV + (mS + s) ≤ Q * ν + -dS + s := by
  nlinarith [mul_le_mul_of_nonneg_left h hQ]

theorem geR_of_le {v : WithTop ℤ} {a : ℤ} {t : ℝ} (h : (a : WithTop ℤ) ≤ v) (ht : t ≤ (a : ℝ)) : geR v t := by
  unfold geR
  intro z hz
  rw [hz] at h
  have h' : a ≤ z := WithTop.coe_le_coe.mp h
  exact ht.trans (by exact_mod_cast h')

theorem column_conditions_of_numeric_bounds (D : Formalism.BasicNotions.D7) (hV : Formalism.MainNotions.CovariantDegrees.ValuationsAdditive D) (hA3 : Formalism.MainNotions.CovariantDegrees.DefiniteRankOne D) (C₀ : ℝ)
    (hRow : LateIndexInjective) (hN0 : EllDegreeLePowerBound) (hN1 : PowerExceedsMaxMultiplicity C₀) (hN2 : ThresholdPowerLowerBound C₀) : ColumnConditionsWithMargin C₀ := by
  intro p n' r K _ _ _ X O _ _ _ S j b e q I' I'' hc x hx hW
  have : Fact p.Prime := ⟨hc.hX.prime⟩
  obtain ⟨i, rfl⟩ := segE_surj X.F j hx
  obtain ⟨nu, ka⟩ := q
  obtain ⟨b', b'', ⟨P1, h1⟩, ⟨P2, h2⟩, hcond⟩ := hc.hq
  have hI' := hc.hI'
  have hI'' := hc.hI''
  simp only at h1 h2 hcond hI' hI'' ⊢
  have hF3 : ∀ (N n : ℕ) [NeZero n] (LL : Letters (Fin N)) (B : Fin N → ℕ) (th M : Fin N → ℤ),
      Formalism.MainNotions.CovariantDegrees.A3at (FF O) N n LL B th M := fun N n _ LL B th M => (hA3 p O S N n LL B th M).2
  rw [← h1] at hI' hcond ⊢
  rw [← h2] at hI'' hcond ⊢
  have u1 := standard_polynomial_mem_bounds (segLL X.F j) b' (hF3 _ r _ b') P1 I' hI'
  have u2 := standard_polynomial_mem_bounds (segLL X.F j) b'' (hF3 _ K _ b'') P2 I'' hI''
  obtain ⟨sA1, sA2, -, -⟩ := seg_val X.F j (Psi (FF O) P1.mu I') i
  obtain ⟨-, -, sG3, sG4⟩ := seg_val X.F j (Psi (FF O) P2.mu I'') i
  obtain ⟨cE, cO, cR⟩ := (hcond i).2 hW
  have hxl : segE X.F j i ∈ X.toLate j := (mem_late X j _).mpr ⟨hx, hW⟩
  have hM : X.Mw p K j e P2.mu (segE X.F j i) = ((p ^ X.Rj p K j : ℕ) : ℤ) *
      (if Even (segE X.F j i) then P2.mu i.succ 0 else P2.mu i.castSucc 0) + (X.dV K j e : ℤ) :=
    (segE_strictMono X.F j).injective.extend_apply _ _ i
  have hrows := hRow p n' r K X hc.hX j
  have hev : ∀ x' ∈ X.toLate j, ∀ i, Even (X.row j x' i) := fun x' hx' i => ((hrows x' hx').2 i).2.1
  have hinj := (hrows _ hxl).1
  have hlt : ∀ a, X.row j (segE X.F j i) a < segE X.F j i := fun a => ((hrows _ hxl).2 a).2.2
  have n0 := hN0 p n' r K X hc.hX j e hc.he
  have n1 := hN1 p n' r K X hc.hX hc.hLa hc.hk j
  have n2 := hN2 p n' r K X hc.hX hc.hLa hc.hk j b hc.h2 _ hxl
  have n0' : (X.dS K j e : ℤ) + (X.dV K j e : ℤ) ≤ (((r + K) * X.Ns : ℕ) : ℤ) * ((p ^ X.Rj p K j : ℕ) : ℤ) := by
    exact_mod_cast n0
  have n1' : (X.mStar : ℤ) < ((p ^ X.Rj p K j : ℕ) : ℤ) := by exact_mod_cast n1
  have hm0 : (X.m0 K : ℤ) = (((r + K) * X.Ns : ℕ) : ℤ) + 1 := by unfold Dat.m0; push_cast; ring
  have vlt := vg_Aw D hV X p K (R := FF O) j e {y | y < segE X.F j i} hev _ hxl hinj hlt P1.mu I'
    (P1.mu i.castSucc (lastIdx r)) (by rw [sA2]; exact (u1.2 i.castSucc).1)
  have vle := vg_Aw D hV X p K (R := FF O) j e {y | y ≤ segE X.F j i} hev _ hxl hinj (fun a => (hlt a).le) P1.mu I'
    (P1.mu i.succ (lastIdx r)) (by rw [sA1]; exact (u1.2 i.succ).1)
  refine ⟨fun he => ⟨?_, ?_⟩, fun he => ⟨?_, ?_⟩, ?_⟩
  · rw [hM, if_pos he]
    exact lg_Gw D hV X p K j e _ P2.mu I'' _ (by rw [sG3]; exact (u2.2 i.succ).2)
  · refine le_trans (WithTop.coe_le_coe.mpr ?_) vlt
    rw [hM, if_pos he]
    unfold Dat.mg
    have hce := (cE he).1
    rw [hm0] at hce
    exact int_ineq _ _ _ _ _ _ _ _ (Int.natCast_nonneg _) hce n0' n1'
  · rw [hM, if_neg he]
    exact lg_Gw D hV X p K j e _ P2.mu I'' _ (by rw [sG4]; exact (u2.2 i.castSucc).2)
  · refine le_trans (WithTop.coe_le_coe.mpr ?_) vle
    rw [hM, if_neg he]
    unfold Dat.mg
    have hce := (cO he).1
    rw [hm0] at hce
    exact int_ineq _ _ _ _ _ _ _ _ (Int.natCast_nonneg _) hce n0' n1'
  · refine geR_of_le vlt ?_
    push_cast
    have hQ : (0 : ℝ) ≤ ((p : ℝ) ^ X.Rj p K j) := by positivity
    have n0r : (X.dS K j e : ℝ) + (X.dV K j e : ℝ) ≤ (((r : ℝ) + K) * X.Ns) * (p : ℝ) ^ X.Rj p K j := by
      exact_mod_cast n0
    have hdV : (0 : ℝ) ≤ (X.dV K j e : ℝ) := Nat.cast_nonneg _
    have hs : (0 : ℝ) ≤ (X.sg p K j (segE X.F j i) : ℝ) := Nat.cast_nonneg _
    push_cast at n2
    have := mul_le_mul_of_nonneg_left cR hQ
    nlinarith

end Formalism.MainNotions.SelectionLemmas.Pf
