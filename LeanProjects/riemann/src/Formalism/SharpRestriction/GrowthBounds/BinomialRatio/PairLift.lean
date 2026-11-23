import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.FactorsOfPerturb

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory

def FamOK (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (C0 CE1 CE2 Cm : ℝ) (X : Loc) [NeZero X.m]
    (β : ∀ j : Fin (numSeg X.TT), SegBlock (segS X.TT j) X.m)
    (u : ∀ j : Fin (numSeg X.TT), SegVs O X.m (segS X.TT j) (X.seg C0 CE1 CE2 j).t) : Prop :=
  ∀ j, u j ∈ Lj O C0 CE1 CE2 Cm X j ∧ ∀ b, b ≠ β j → u j b = 0

open Classical in

def PairLiftAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ct Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (jO : W →+* O) (w : O),
    UnramifiedQuadraticSetting X.p X.n' W Qq O Kf ι σ jO w → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X → 1 ≤ X.c →
    ∀ e : Edge W Qq (X.m + 1), IsEdge X.p X.n' 1 e →
      ∃ (κ : (∀ j : Fin (numSeg X.TT), SegBlock (segS X.TT j) X.m) → O)
        (F : (∀ j : Fin (numSeg X.TT), SegBlock (segS X.TT j) X.m) →
          (∀ j : Fin (numSeg X.TT), SegVs O X.m (segS X.TT j) (X.seg C0 CE1 CE2 j).t) →
          VHH (m := X.m) Kf X.TT X.aT X.bT)
        (G : (∀ j : Fin (numSeg X.TT), SegBlock (segS X.TT j) X.m) →
          (∀ j : Fin (numSeg X.TT), SegVs O X.m (segS X.TT j) (X.seg C0 CE1 CE2 j).t) →
          Module.Dual Kf (VHH (m := X.m) Kf X.TT X.aT X.bT)),
        (∀ β, κ β ≠ 0 ∧ vLEO X.p (κ β) (4 * X.kap0)) ∧
        (∀ β u, FamOK O C0 CE1 CE2 Cm X β u →
          F β u ∈ CCe X.p ι σ w X.TT X.aT X.bT ⌊X.t0 C0 Ct⌋₊ X.c e ∧
          G β u ∈ CCe' X.p ι σ w X.TT X.aT X.bT ⌊X.t0 C0 Ct⌋₊ X.c e) ∧
        ∀ β u β' u', FamOK O C0 CE1 CE2 Cm X β u → FamOK O C0 CE1 CE2 Cm X β' u' →
          ∀ a : Fin (numSeg X.TT) → O,
            (∀ j, segForm O X.p X.m (X.seg C0 CE1 CE2 j) (u j) (u' j) = algebraMap O (KK O) (a j)) →
            ∃ ν : O, beHH (m := X.m) X.p X.TT X.aT X.bT (F β u) (G β' u') =
              algebraMap O Kf ((if β = β' then κ β * ∏ j, a j else 0) + w ^ X.c * ν)

private theorem addVal_toNat_mul_of_ne_zero {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {a b : O} (ha : a ≠ 0) (hb : b ≠ 0) :
    (IsDiscreteValuationRing.addVal O (a * b)).toNat =
      (IsDiscreteValuationRing.addVal O a).toNat + (IsDiscreteValuationRing.addVal O b).toNat := by
  have ha' : IsDiscreteValuationRing.addVal O a ≠ ⊤ := by
    rwa [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
  have hb' : IsDiscreteValuationRing.addVal O b ≠ ⊤ := by
    rwa [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
  rw [AddValuation.map_mul, ENat.toNat_add ha' hb']

private theorem vO_eq_addVal_div_ramE_of_ne_zero' {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) {z : O}
    (hz : z ≠ 0) :
    vO p z = ((((IsDiscreteValuationRing.addVal O z).toNat : ℚ) / (ramE p O : ℚ) : ℚ) : WithTop ℚ) := by
  have hz' : algebraMap O (KK O) z ≠ 0 := by
    intro h
    exact hz ((IsFractionRing.to_map_eq_zero_iff).mp h)
  have hspec := Classical.choose_spec (IsLocalization.surj (nonZeroDivisors O) (algebraMap O (KK O) z))
  simp only [vO, vK, ordW, if_neg hz']
  generalize Classical.choose (IsLocalization.surj (nonZeroDivisors O) (algebraMap O (KK O) z)) = ab at hspec ⊢
  rw [← map_mul] at hspec
  have hmul : z * (ab.2 : O) = ab.1 := IsFractionRing.injective O (KK O) hspec
  have hb : (ab.2 : O) ≠ 0 := nonZeroDivisors.coe_ne_zero ab.2
  rw [← hmul, addVal_toNat_mul_of_ne_zero hz hb]
  simp only [WithTop.map_coe]
  congr 1
  push_cast
  ring

theorem vLEO_mul {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p : ℕ} {w : O} (hw : Irreducible w)
    (h2 : w ^ 2 = (p : O)) {x y : O} (hx : x ≠ 0) (hy : y ≠ 0) {D E : ℝ} (h : vLEO p x D) (h' : vLEO p y E) :
    vLEO p (x * y) (D + E) := by
  obtain ⟨q, hq, hqD⟩ := h
  obtain ⟨q', hq', hqE⟩ := h'
  rw [vO_eq_addVal_div_ramE_of_ne_zero' p hx] at hq
  rw [vO_eq_addVal_div_ramE_of_ne_zero' p hy] at hq'
  have e1 := WithTop.coe_eq_coe.mp hq
  have e2 := WithTop.coe_eq_coe.mp hq'
  refine ⟨q + q', ?_, ?_⟩
  · rw [vO_eq_addVal_div_ramE_of_ne_zero' p (mul_ne_zero hx hy), addVal_toNat_mul_of_ne_zero hx hy, ← e1, ← e2]
    congr 1
    push_cast
    ring
  · push_cast
    linarith

theorem vLEO_prod {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p : ℕ} {w : O} (hw : Irreducible w)
    (h2 : w ^ 2 = (p : O)) {ι : Type} (s : Finset ι) (z : ι → O) (D : ι → ℝ)
    (h : ∀ i ∈ s, z i ≠ 0 ∧ vLEO p (z i) (D i)) : (∏ i ∈ s, z i) ≠ 0 ∧ vLEO p (∏ i ∈ s, z i) (∑ i ∈ s, D i) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    rw [Finset.prod_empty, Finset.sum_empty]
    refine ⟨one_ne_zero, 0, ?_, by simp⟩
    rw [vO_eq_addVal_div_ramE_of_ne_zero' p one_ne_zero]
    simp
  · intro a s ha ih hh
    have hs : ∀ i ∈ s, z i ≠ 0 ∧ vLEO p (z i) (D i) := fun i hi => hh i (Finset.mem_insert_of_mem hi)
    obtain ⟨h1, h1'⟩ := ih hs
    obtain ⟨ha0, ha1⟩ := hh a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact ⟨mul_ne_zero ha0 h1, vLEO_mul hw h2 ha0 h1 ha1 h1'⟩

theorem liftVecAt_of {C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ct Cc H : ℝ}
    (hstd : ∀ X : Loc, D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X → Std C0 Cde CE1 CE2 H X)
    (h : PairLiftAt C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ct Cc) : LiftVecAt C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ct Cc := by
  classical
  intro X _ W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ jO w hS hH hc Dj g hD hBD hcD e he
  have hD1 : D1num X := ⟨hS.1.prime, hS.1.five_le, hS.1.two_le, hS.1.even⟩
  have hs := hstd X hD1 hH hc
  have hw : Irreducible w := hS.2.1
  have h2 : w ^ 2 = (X.p : O) := hS.1.w_sq
  have hkap : 0 ≤ X.kap0 := by
    have hk : 0 ≤ X.k := by unfold Loc.k; positivity
    have hN : 0 ≤ X.N := by unfold Loc.N; positivity
    have hp : (1 : ℝ) < (X.p : ℝ) := by have := hs.p5; exact_mod_cast (by omega : 1 < X.p)
    have hl : 0 ≤ Real.logb X.p X.a := by
      unfold Real.logb
      exact div_nonneg (le_trans zero_le_one hs.loga) (Real.log_nonneg hp.le)
    unfold Loc.kap0 kap0G4
    positivity
  have hc1 : 1 ≤ X.c := by
    have hsum : 0 ≤ ∑ j, Dj j := Finset.sum_nonneg fun j _ => hD j
    have : (0 : ℝ) < (X.c : ℝ) := by linarith
    exact_mod_cast this
  obtain ⟨κ, F, G, hκ, hmem, hpair⟩ := h X W Qq O Kf ι σ jO w hS hH hc hc1 e he
  choose x y β z hxy hsupp hz hform using hBD
  have hfx : ∀ I : (∀ j, Fin (g j)), FamOK O C0 CE1 CE2 Cm X (fun j => β j (I j)) (fun j => x j (I j)) :=
    fun I j => ⟨(hxy j (I j)).1, fun b hb => (hsupp j (I j) b hb).1⟩
  have hfy : ∀ I : (∀ j, Fin (g j)), FamOK O C0 CE1 CE2 Cm X (fun j => β j (I j)) (fun j => y j (I j)) :=
    fun I j => ⟨(hxy j (I j)).2, fun b hb => (hsupp j (I j) b hb).2⟩
  refine ⟨fun I => F (fun j => β j (I j)) (fun j => x j (I j)), fun I => G (fun j => β j (I j)) (fun j => y j (I j)),
    fun I => κ (fun j => β j (I j)) * ∏ j, z j (I j), fun I => (hmem _ _ (hfx I)).1, fun I => (hmem _ _ (hfy I)).2, ?_, ?_⟩
  · intro I
    have hp := vLEO_prod hw h2 Finset.univ (fun j => z j (I j)) Dj fun j _ => hz j (I j)
    refine ⟨mul_ne_zero (hκ _).1 hp.1, ?_⟩
    have := vLEO_mul hw h2 (hκ _).1 hp.1 (hκ (fun j => β j (I j))).2 hp.2
    rwa [add_comm] at this
  · intro I J
    obtain ⟨ν, hν⟩ := hpair _ _ _ _ (hfx I) (hfy J) (fun j => if I j = J j then z j (I j) else 0) (fun j => by
      rw [hform j (I j) (J j)]
      split_ifs <;> simp)
    refine ⟨ν, ?_⟩
    rw [hν]
    congr 2
    by_cases hIJ : I = J
    · subst hIJ
      simp
    · rw [if_neg hIJ]
      obtain ⟨j0, hj0⟩ := Function.ne_iff.mp hIJ
      have h0 : (∏ j, if I j = J j then z j (I j) else 0) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ j0) (if_neg hj0)
      rw [h0, mul_zero]
      simp

def RestPairLift : Prop :=
  TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc => ∃ Ct0 : ℝ, 0 < Ct0 ∧ ∀ Ct : ℝ, Ct0 ≤ Ct →
    PairLiftAt C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ct Cc

theorem restLiftVec_of (h : RestPairLift) : RestLiftVec := by
  unfold RestPairLift at h
  unfold RestLiftVec
  refine TransportedAlt.mono ?_ (TransportedAlt.and thr_std h)
  intro C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc hh
  obtain ⟨⟨_, hstd⟩, Ct0, hCt0, hall⟩ := hh
  exact ⟨Ct0, hCt0, fun Ct hCt => liftVecAt_of hstd (hall Ct hCt)⟩

end Formalism.MainNotions.ColumnSystems.Pf
