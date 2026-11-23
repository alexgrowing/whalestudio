import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ScaleZeroComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumSetBLogDivLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightComparisonLocalGreenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSetResidueLogBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumValuationLogLeLogDiscriminantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogGreenDifferenceDeterminantLeStatement

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier AlgebraicGeometry CategoryTheory
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.PlaceBd

theorem abs_ht_sub_le {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F} (A : Adl C Y)
    (g : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ) (x : Y.X) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (b : HeightOneSpectrum (𝓞 F) → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hS : ∀ v ∉ S, ∀ e y, A.lg v e y = g v e y) (hb : ∀ v e y, |A.lg v e y - g v e y| ≤ b v)
    (hsum : ∑ v ∈ S, b v ≤ ((A.n : ℕ) : ℝ) * (Module.finrank ℚ F : ℝ) * K) :
    |A.ht x - ({ A with lg := g } : Adl C Y).ht x| ≤ K :=
  GlobalTheory.T.height_comparison_local_green A g x S b K hK hS hb hsum

theorem places_over {F : Type} [Field F] [NumberField F] (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime) (g : ℕ → ℝ)
    (hg : ∀ p, 0 ≤ g p) :
    (∀ v : HeightOneSpectrum (𝓞 F), NumberField.HeightOneSpectrum.adicAbv F v (resP v : F) ≤ 1) ∧
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), (∀ v, v ∈ S ↔ resP v ∈ T) ∧
      ∑ v ∈ S, (-Real.log (NumberField.HeightOneSpectrum.adicAbv F v (resP v : F)) / Real.log (resP v)) * g (resP v) ≤
        (Module.finrank ℚ F : ℝ) * ∑ p ∈ T, g p :=
  GlobalTheory.T.exists_finite_set_residue_log_bound T hT g hg

theorem sum_vDiff_le (D : D7) (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime) :
    ∑ p ∈ T, vDiff D.host.E p * Real.log p ≤ Real.log D.host.rdE :=
  GlobalTheory.T.sum_valuation_log_le_log_discriminant D T hT

theorem abs_lgOf_detSym_sub_le (hB : HTBoundSt) {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A}
    {s : FinalTheorems S κ} (fl : s.Flag) (k : s.Comp) (τ : D.host.E →+* ℂ) (T : Finset ℕ)
    (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (ε : Ext v) (y : AlgPt (fl.C k).Y) :
    |lgOf (fl.C k) (detSym S.Dw (ArIn.ind T) none τ) v ε y -
        lgOf (fl.C k) (detSym S.Dw (fun _ => false) none τ) v ε y| ≤
      if resP v ∈ T then |Real.log (ε.w (resP v)) / Real.log (resP v)| *
        (N * (Real.log (resP v) / ((resP v : ℝ) - 1) + vDiff D.host.E (resP v) * Real.log (resP v))) else 0 :=
  GlobalTheory.T.log_green_difference_determinant_le hB fl k τ T v ε y

end GlobalTheory.PlaceBd

namespace GlobalTheory.PlaceBd
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier

section
variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} (fl : s.Flag) (k : s.Comp)

theorem expo_detSym (a a' : ℕ → Bool) (R : Option ℝ) (τ : D.host.E →+* ℂ) :
    expo S.Dw (detSym S.Dw a R τ) = expo S.Dw (detSym S.Dw a' R τ) := by
  funext x
  have h (b : ℕ → Bool) : expo S.Dw (detSym S.Dw b R τ) x =
      ∑ i ∈ Finset.range (S.Dw.p + S.Dw.q), expo S.Dw (rootSym S.Dw b R τ i) x := by
    unfold detSym expo
    rw [Finsupp.sum_finset_sum_index (fun _ => by simp) (fun _ _ _ => by split_ifs <;> simp)]
  rw [h, h]
  simp only [expo_rootSym]

theorem parOf_detSym (a : ℕ → Bool) (τ : D.host.E →+* ℂ) : parOf (detSym S.Dw a none τ) = none := by
  unfold parOf
  split_ifs with h
  · have hm := h.choose_spec
    have hs := Finsupp.support_finset_sum hm
    simp only [Finset.mem_biUnion, Finset.mem_range] at hs
    obtain ⟨i, -, hi⟩ := hs
    unfold rootSym at hi
    split_ifs at hi
    · have := Finsupp.support_single_subset hi
      rw [Finset.mem_singleton] at this
      rw [this]
    · have := Finsupp.support_single_subset hi
      rw [Finset.mem_singleton] at this
      rw [this]
  · rfl

theorem adlOf_detSym {C : CxSt D.what₂.LL} (hm : Mets (fl.C k) C) (a a' : ℕ → Bool) (τ : D.host.E →+* ℂ) :
    adlOf (fl.C k) hm (detSym S.Dw a' none τ) =
      { adlOf (fl.C k) hm (detSym S.Dw a none τ) with lg := lgOf (fl.C k) (detSym S.Dw a' none τ) } := by
  have e1 := expo_detSym (S := S) a' a none τ
  have e2 := (parOf_detSym (S := S) a' τ).trans (parOf_detSym (S := S) a τ).symm
  unfold adlOf
  rw [e1, e2]

end

open GlobalTheory.Mean4 GlobalTheory.Mean4O in

theorem placeBd : Hypotheses2 → HypothesesH → ∃ C₂ : ℝ, OnObj fun D O _ _ _ _ => FewBad O.Y →
    ∀ B : ℝ, 48 ≤ B → ∀ (c : O.Y.Comp) (τ : D.what₂.Tau),
      |O.Y.htDetT B c τ - GlobalTheory.ShFam.Pad.degFrame O.s O.Φ O.met.hm c τ| ≤
        C₂ * O.Y.N * (Real.log B + Real.log D.host.rdE) := by
  intro _ _
  refine ⟨4, fun D O _ _ _ _ _ _ hF B hB c τ => ?_⟩
  have e1 : O.Y.htDetT B c τ = (adlOf (O.Φ.C c) (O.met.hm c)
      (detSym O.S.Dw (ArIn.ind (Pad.setB O.κ B)) none (DV.tauEmb D τ))).ht (innerPt O.s O.Φ c) := rfl
  have e2 : degFrame O.s O.Φ O.met.hm c τ = ({ adlOf (O.Φ.C c) (O.met.hm c)
      (detSym O.S.Dw (ArIn.ind (Pad.setB O.κ B)) none (DV.tauEmb D τ)) with
        lg := lgOf (O.Φ.C c) (detSym O.S.Dw (fun _ => false) none (DV.tauEmb D τ)) } : Adl _ _).ht
          (innerPt O.s O.Φ c) := by
    unfold degFrame
    rw [adlOf_detSym O.Φ c (O.met.hm c) (ArIn.ind (Pad.setB O.κ B)) (fun _ => false)]
  have eN : O.Y.N = O.N := rfl
  rw [e1, e2, eN]
  obtain ⟨hp, hm⟩ := sum_setB_log_div_le O.Y hF B hB
  rw [O.setB_eq] at hp hm
  have hv := sum_vDiff_le D _ hp
  have hv0 : 0 ≤ Real.log D.host.rdE := by simpa using sum_vDiff_le D ∅ (by simp)
  have hlB : 0 ≤ Real.log B := Real.log_nonneg (by linarith)
  set T := Pad.setB O.κ B
  set g : ℕ → ℝ := fun p => (O.N : ℝ) * (Real.log p / ((p : ℝ) - 1) + vDiff D.host.E p * Real.log p) with hg
  have hg0 : ∀ p, 0 ≤ g p := by
    intro p
    refine mul_nonneg (Nat.cast_nonneg _) (add_nonneg ?_ (mul_nonneg ?_ (Real.log_natCast_nonneg p)))
    · rcases Nat.lt_or_ge p 2 with h | h
      · interval_cases p <;> simp
      · have : (1 : ℝ) < p := by exact_mod_cast h
        exact div_nonneg (Real.log_natCast_nonneg p) (by linarith)
    · unfold vDiff; positivity
  obtain ⟨hle, S, hS, hsum⟩ := places_over (F := D.what₂.LL) T hp g hg0
  have hw : ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (ε : Ext v),
      ε.w (resP v : AlgebraicClosure D.what₂.LL) = NumberField.HeightOneSpectrum.adicAbv D.what₂.LL v (resP v : D.what₂.LL) := by
    intro v ε
    rw [← map_natCast (algebraMap D.what₂.LL (AlgebraicClosure D.what₂.LL)), ε.w_alg]
  refine abs_ht_sub_le _ _ _ S
    (fun v => (-Real.log (NumberField.HeightOneSpectrum.adicAbv D.what₂.LL v (resP v : D.what₂.LL)) / Real.log (resP v)) *
      g (resP v)) _ (by positivity) ?_ ?_ ?_
  · intro v hv e y
    have h := abs_lgOf_detSym_sub_le GlobalTheory.ShFam.Pad.HTBound.htBound O.Φ c (DV.tauEmb D τ) T v e y
    rw [if_neg (fun h' => hv ((hS v).2 h'))] at h
    exact sub_eq_zero.1 (abs_nonpos_iff.1 h)
  · intro v e y
    have h := abs_lgOf_detSym_sub_le GlobalTheory.ShFam.Pad.HTBound.htBound O.Φ c (DV.tauEmb D τ) T v e y
    refine h.trans ?_
    split_ifs with hT
    · rw [hw, abs_div, abs_of_nonpos (Real.log_nonpos (AbsoluteValue.nonneg _ _) (hle v)),
        abs_of_nonneg (Real.log_natCast_nonneg _)]
    · have hc : 0 ≤ -Real.log (NumberField.HeightOneSpectrum.adicAbv D.what₂.LL v (resP v : D.what₂.LL)) / Real.log (resP v) :=
        div_nonneg (neg_nonneg.2 (Real.log_nonpos (AbsoluteValue.nonneg _ _) (hle v))) (Real.log_natCast_nonneg _)
      exact mul_nonneg hc (hg0 _)
  · refine hsum.trans ?_
    have : ∑ p ∈ T, g p ≤ 4 * O.N * (Real.log B + Real.log D.host.rdE) := by
      simp only [hg, ← Finset.mul_sum, Finset.sum_add_distrib]
      have hN : (0 : ℝ) ≤ O.N := Nat.cast_nonneg _
      nlinarith
    have hF0 : (0 : ℝ) ≤ Module.finrank ℚ D.what₂.LL := Nat.cast_nonneg _
    simp only [adlOf, PNat.one_coe, Nat.cast_one, one_mul]
    exact mul_le_mul_of_nonneg_left this hF0

end GlobalTheory.PlaceBd
