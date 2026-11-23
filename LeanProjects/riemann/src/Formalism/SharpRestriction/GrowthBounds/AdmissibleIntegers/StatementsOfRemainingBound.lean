import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
import Formalism.SharpRestriction.GrowthBounds.TopChoiceBounds

noncomputable section

open scoped BigOperators
open NumberField IsDedekindDomain Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G Formalism.MainNotions Formalism.MainNotions.WeilJacquetShalikaLaw

namespace Formalism.MainNotions.WeilJacquetShalikaLaw.Proof

variable {D : D7} {L : SizeData₂ D} {X : Inst D L} {Y : LatInst D} {K : Consts} {c : LatCmp D} {Dx : DivX D} {T : TwForms D}
  {lev : LevelData D} {Xe : ErrX D} {ce : ErrC} {sp : ℝ}

def RestElse (D : D7) (Dx : DivX D) (T : TwForms D) (sp : ℝ) : Prop :=
  ∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w ≠ (D.mem u).A.T →
    D.what₂.places.resChar w ≠ D.host.d → D.what₂.places.resChar w ∉ ({D.host.g 0, D.host.g 1} : Finset ℕ) →
    ∀ μ, DV.Used D μ → D.what₂.places.resChar w ∉ Dx.Qp μ → ∀ x ∈ LT.Sram D u w,
      ColGe T u μ w x (-(((SizeData₂.lifts D).card : ℝ) - sp) * vDG D u w)

theorem notInert_of' (p : ℕ) (hp : p.Prime) (h3 : p ∣ D.host.condN) : ¬ (IsResidueClassZero D p ∨ IsSg D p) := by
  rintro (h | h)
  · exact not_dvd_conductor_of_inert hp h h3
  · exact not_dvd_of_signal hp h h3

theorem first_clause_cases
    (hNo : OrbitsWithoutOperator D L X K Dx T lev Xe ce sp) (hC : MediumInertPrimeLengthBound D L K Dx T lev Xe ce sp)
    (hD : LossAtDiscriminant D L K Dx T lev Xe ce sp)
    (hElse : DGamDef D → RestElse D Dx T sp) :
    ColumnValuationAwayFromTypePrimes D L K Dx T lev Xe ce sp := by
  intro hF hE u w hw hg μ hUs hμ x hx
  have hp := D.what₂.places.resChar_prime w
  have h0 : D.what₂.places.resChar w ≠ D.host.g 0 := fun h => hg (by simp [h])
  have h1 : D.what₂.places.resChar w ≠ D.host.g 1 := fun h => hg (by simp [h])
  by_cases h2 : D.host.cls (D.what₂.places.resChar w) = PrimeClass.ramD
  · have h := hD hF hE u w hw h2 μ hUs hμ x hx
    have e : lowS L Xe K ce sp u w =
        (∑ j ∈ SizeData₂.lifts D, (L.F j w - EatD D j - vDG D u w)) + sp * vDG D u w := by
      unfold lowS ES Eval vDG
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [if_neg hw, if_neg h0, if_neg h1, if_pos h2]
      ring
    rw [e]; exact h
  by_cases h3 : (IsResidueClassZero D (D.what₂.places.resChar w) ∨ IsSg D (D.what₂.places.resChar w)) ∧
      (D.what₂.places.resChar w : ℝ) ≤ L.sc.X'' D.R.n
  · have hExc : ¬ Exc D (D.what₂.places.resChar w) := by
      intro hE'
      unfold Exc at hE'
      rcases (Nat.Prime.dvd_mul hp).1 hE' with h | h
      · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
        · exact notInert_of' _ hp h h3.1
        · exact h0 ((Nat.prime_dvd_prime_iff_eq hp (D.host.g_prime 0)).1 h)
      · exact h1 ((Nat.prime_dvd_prime_iff_eq hp (D.host.g_prime 1)).1 h)
    by_cases h4 : IsResidueClassZero D (D.what₂.places.resChar w) ∧ hP D (D.what₂.places.resChar w) = 0
    · have h := hC hF hE u w hw h4.1 h4.2 hExc h3.2 μ hUs hμ x hx
      have e : lowS L Xe K ce sp u w =
          (∑ j ∈ SizeData₂.lifts D, (L.F j w - EatC L ce j (D.what₂.places.resChar w) - vDG D u w)) + sp * vDG D u w := by
        unfold lowS ES Eval vDG
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [if_neg hw, if_neg h0, if_neg h1, if_neg h2, if_pos h3, if_pos h4]
        ring
      rw [e]; exact h
    · have hcl : (IsResidueClassZero D (D.what₂.places.resChar w) ∧ hP D (D.what₂.places.resChar w) ≠ 0) ∨
          IsSg D (D.what₂.places.resChar w) := by
        rcases h3.1 with h | h
        · exact Or.inl ⟨h, fun h' => h4 ⟨h, h'⟩⟩
        · exact Or.inr h
      have h := hNo hF hE u w hw hcl hExc h3.2 μ hUs hμ x hx
      refine ColGe_mono ?_ h
      have : 0 ≤ ∑ j ∈ SizeData₂.lifts D, g0S X K (D.what₂.places.resChar w) j :=
        Finset.sum_nonneg fun _ _ => by
          unfold g0S
          split_ifs
          · exact le_rfl
          · exact Finset.sum_nonneg fun _ _ => le_max_right _ _
      linarith
  · have hd : D.what₂.places.resChar w ≠ D.host.d := by
      intro hd
      apply h2
      rw [hd]
      exact primeClass_d D.host.toHostRaw
    have h := hElse hE.dgam u w hw hd hg μ hUs hμ x hx
    have e : lowS L Xe K ce sp u w = -(((SizeData₂.lifts D).card : ℝ) - sp) * vDG D u w := by
      unfold lowS ES Eval vDG
      have : ∀ j ∈ SizeData₂.lifts D, L.F j w = 0 := by
        intro j hj
        rw [hF j hj w]
        unfold Fval FvalP SizeData₂.gTypes
        rw [if_neg hg, if_neg h2, if_neg h3]
      rw [Finset.sum_congr rfl fun j hj => by rw [this j hj]]
      simp only [if_neg hw, if_neg h0, if_neg h1, if_neg h2, if_neg h3]
      simp [Finset.sum_const]
      ring
    rw [e]; exact h

theorem not_exc_of_inert {p : ℕ} (hp : p.Prime) (hin : IsResidueClassZero D p ∨ IsSg D p) (h0 : p ≠ D.host.g 0) (h1 : p ≠ D.host.g 1) :
    ¬ Exc D p := by
  intro hE'
  unfold Exc at hE'
  rcases (Nat.Prime.dvd_mul hp).1 hE' with h | h
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact notInert_of' _ hp h hin
    · exact h0 ((Nat.prime_dvd_prime_iff_eq hp (D.host.g_prime 0)).1 h)
  · exact h1 ((Nat.prime_dvd_prime_iff_eq hp (D.host.g_prime 1)).1 h)

theorem not_exc_of_gIdx {Tu p : ℕ} (hg : GIdx D.host Tu p) : ¬ Exc D p :=
  not_exc_of_inert hg.1 (Or.inl hg.2.2.1) (fun h => hg.2.2.2.2.1 (h ▸ D.host.g_level 0))
    (fun h => hg.2.2.2.2.1 (h ▸ D.host.g_level 1))

theorem first_in_local_models (W : TwLoc D Y) (hU : unitBoundAtTwistedPlaces D L X Y K Dx W lev Xe ce sp) : TupleLatticeValuation D L X Y K Dx W lev Xe ce sp := by
  classical
  intro hE μ hUs hT hTied u w hg hμ
  have hU1 := hU hE μ hUs hT hTied u w hg hμ
  set Y' := W.Yt μ with hY'
  set p := D.what₂.places.resChar w with hp
  set G := D.gat u w hg with hG
  have hsub := TopChoiceBounds.bg_VV_sub X K (aL L) (bL L) p
  have hne : (reps X p).Nonempty := by
    unfold reps
    exact (Finset.univ_nonempty (α := HH D)).image _
  obtain ⟨t1, _⟩ := hne
  have hfr : IsFractionRing G.O G.Kf := (G.P.setting (Y'.vOf u w hg t1)).frac_O
  have hp0 : (p : G.O) ≠ 0 := by
    intro h0
    exact LatticeSystems.kp_p_ne_zero G (Y'.vOf u w hg t1) (by rw [h0, map_zero])
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible G.O
  have kz : (Y'.Ch u w hg).chainK D.R.m (0 : G.Fn) = 0 := map_zero ((Y'.Ch u w hg).chainK D.R.m)
  have ka : ∀ A B : G.Fn, (Y'.Ch u w hg).chainK D.R.m (A + B) =
      (Y'.Ch u w hg).chainK D.R.m A + (Y'.Ch u w hg).chainK D.R.m B :=
    fun A B => map_add ((Y'.Ch u w hg).chainK D.R.m) A B
  have ks : ∀ (c : G.O) (A : G.Fn), (Y'.Ch u w hg).chainK D.R.m (c • A) = c • (Y'.Ch u w hg).chainK D.R.m A :=
    fun c A => LinearMap.map_smul_of_tower ((Y'.Ch u w hg).chainK D.R.m) c A
  intro F hF
  have hF1 := hF.1.1
  clear hF
  unfold LatInst.vKge
  rw [TopChoiceBounds.bg_vGe_iff G hϖ]
  induction hF1 using Submodule.span_induction with
  | mem F' h' =>
    obtain ⟨VV', hV', F0, hF0, rfl⟩ := h'
    rw [← TopChoiceBounds.bg_vGe_iff G hϖ, TopChoiceBounds.bg_yProd_smul, ks]
    have h1 := hU1 _ VV' hsub hV' F0 hF0
    have h2 := TopChoiceBounds.bg_vGe_smul G hp0 _ _ _
      (∑ t0 ∈ VV X K (aL L) (bL L) p \ VV', ⌈Sv X K (aL L) (bL L) p t0⌉.toNat) h1
    refine TopChoiceBounds.bg_vGe_mono G _ _ ?_ h2
    have := TopChoiceBounds.bg_gain_le X K (aL L) (bL L) p VV' hV'
    linarith
  | zero => rw [kz]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [ka]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [ks]; exact Submodule.smul_mem _ c ha

theorem totS_eq (u : D.what₂.Word) (w : D.what₂.places.Pl) :
    totS X K Xe ce sp u w =
      (∑ j ∈ SizeData₂.lifts D, gainS X K (D.what₂.places.resChar w) j) + lowS L Xe K ce sp u w := by
  unfold totS lowS
  have h : ∀ j ∈ SizeData₂.lifts D, gainS X K (D.what₂.places.resChar w) j + L.F j w - ES L Xe K ce u j w =
      gainS X K (D.what₂.places.resChar w) j + (L.F j w - ES L Xe K ce u j w) := fun j _ => by ring
  rw [Finset.sum_congr rfl h, Finset.sum_add_distrib]
  ring

theorem baseChange_preserves_unitary_of (W : TwLoc D Y) (hV : CmpV c Dx T W) (hG : TupleLatticeValuation D L X Y K Dx W lev Xe ce sp)
    (hNo : OrbitsWithoutOperator D L X K Dx T lev Xe ce sp) (hc : ColumnValuationAwayFromTypePrimes D L K Dx T lev Xe ce sp) :
    Conclusion1 D L X Y K c Dx T lev Xe ce sp := by
  classical
  intro ht hE u w hw hg' μ hUs hμ x hin
  rcases hin with ⟨hg, hx⟩ | ⟨hVV, hx⟩
  · exact kernel_valuation_served W hV hG ht hE u w hg (not_exc_of_gIdx hg) μ hUs hμ x hx
  · have hlow := hc ht.fdef hE u w hw hg' μ hUs hμ x hx
    rw [totS_eq]
    by_cases h1 : (IsResidueClassZero D (D.what₂.places.resChar w) ∨ IsSg D (D.what₂.places.resChar w)) ∧ ¬ Exc D (D.what₂.places.resChar w)
    swap
    · have : ∑ j ∈ SizeData₂.lifts D, gainS X K (D.what₂.places.resChar w) j = 0 :=
        Finset.sum_eq_zero fun j _ => by rw [gainS, if_neg h1]
      rw [this, zero_add]; exact hlow
    by_cases h2 : (IsResidueClassZero D (D.what₂.places.resChar w) ∧ hP D (D.what₂.places.resChar w) = 0) ∨
        L.sc.X'' D.R.n < (D.what₂.places.resChar w : ℝ)
    · have : ∑ j ∈ SizeData₂.lifts D, gainS X K (D.what₂.places.resChar w) j = 0 :=
        Finset.sum_eq_zero fun j _ => by rw [gainS, if_pos h1, gainP, if_pos h2, ite_self]
      rw [this, zero_add]; exact hlow
    · have hcl : (IsResidueClassZero D (D.what₂.places.resChar w) ∧ hP D (D.what₂.places.resChar w) ≠ 0) ∨
          IsSg D (D.what₂.places.resChar w) := by
        rcases h1.1 with h | h
        · exact Or.inl ⟨h, fun h' => h2 (Or.inl ⟨h, h'⟩)⟩
        · exact Or.inr h
      have hX : (D.what₂.places.resChar w : ℝ) ≤ L.sc.X'' D.R.n := not_lt.1 fun h => h2 (Or.inr h)
      have h := hNo ht.fdef hE u w hw hcl h1.2 hX μ hUs hμ x hx
      have e : ∑ j ∈ SizeData₂.lifts D, gainS X K (D.what₂.places.resChar w) j =
          ∑ j ∈ SizeData₂.lifts D, g0S X K (D.what₂.places.resChar w) j :=
        Finset.sum_congr rfl fun j _ => by
          rw [gainS, if_pos h1, g0S, gainP, if_neg h2, hVV, Finset.sum_empty, zero_add, Finset.sdiff_empty]
      rw [e]; exact h

theorem statements_of_remaining_bound (W : TwLoc D Y) (hV : CmpV c Dx T W) (hA : admitted D L X Y K Dx T W lev Xe ce sp)
    (hR : DGamDef D → RestElse D Dx T sp) : Conclusion₂ D L X Y K c Dx T W lev Xe ce sp := by
  obtain ⟨hU, _, _, hNo, hC, hD⟩ := hA
  have hc := first_clause_cases hNo hC hD hR
  have hGt := first_in_local_models W hU
  exact ⟨baseChange_preserves_unitary_of W hV hGt hNo hc, zero_gain_of_no_served_orbit hc, hc, hGt⟩

def RestComp : Prop :=
  ∀ (D : D7) (Dx : DivX D) (T : TwForms D) (sp : ℝ), IsotypicPartsInternalDirectSum D Dx T sp → DGamDef D → RestElse D Dx T sp

def RestSz (C : ℝ) : Prop := ∀ (D : D7) (L : SizeData₂ D), ErrorFirstTermSize D L C

theorem stmt_of_rest (hR : RestComp) (D : D7) (L : SizeData₂ D) (X : Inst D L) (Y : LatInst D) (K : Consts) (c : LatCmp D)
    (Dx : DivX D) : Stmt D L X Y K c Dx := by
  intro T W lev Xe ce hV sp _ hA
  exact statements_of_remaining_bound W hV hA (fun hG => hR D Dx T sp hA.2.2.1 hG)

theorem stmtE_of_rest (hR : RestComp) {C : ℝ} (hC : 0 ≤ C) (hS : RestSz C) (D : D7) (L : SizeData₂ D) (X : Inst D L)
    (Y : LatInst D) (K : Consts) (c : LatCmp D) (Dx : DivX D) : ClosedFormOfAdmitted D L X Y K c Dx :=
  ⟨stmt_of_rest hR D L X Y K c Dx, C, hC, hS D L⟩

theorem stmtF_of_rest (hR : RestComp) {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : KudlaFamilyStatement Fm :=
  ⟨0, fun _ _ _ _ => stmt_of_rest hR _ _ _ _ _ _ _⟩

theorem stmtEF_of_rest (hR : RestComp) {C : ℝ} (hC : 0 ≤ C) (hS : RestSz C) {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) :
    FamilyClosedForm Fm :=
  ⟨stmtF_of_rest hR Fm, C, hC, 0, fun _ _ _ _ => hS _ _⟩

end Formalism.MainNotions.WeilJacquetShalikaLaw.Proof

end
