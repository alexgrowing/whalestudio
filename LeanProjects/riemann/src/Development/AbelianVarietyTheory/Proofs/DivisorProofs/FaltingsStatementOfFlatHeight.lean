import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdmissibleRepresentationFactorisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightAdditiveInSymbolsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LetterHeightDifferenceBoundedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LetterSumEqTauSumStatement

open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.HalfFalt

theorem sum_range_ite_lt (f : ℕ → ℝ) {j N : ℕ} (h : j ≤ N) :
    ∑ i ∈ Finset.range N, (if i < j then f i else 0) = ∑ i ∈ Finset.range j, f i := by
  rw [← Finset.sum_range_add_sum_Ico _ h,
    Finset.sum_congr rfl (fun i hi => if_pos (Finset.mem_range.1 hi)),
    Finset.sum_eq_zero (fun i hi => if_neg (by rw [Finset.mem_Ico] at hi; omega)), add_zero]

open Classical in

theorem faltSt : Hypotheses2 → HypothesesH → FlatHt → FaltSt := by
  intro _ _ hF D O hC hN A T H h
  obtain ⟨C1, hC1⟩ := hF D O hC hN A T H h
  obtain ⟨C2, hC2⟩ := GlobalTheory.T.letter_height_difference_bounded D O
  refine ⟨((letters O.S.Dw).length * C2 + Fintype.card D.what₂.Tau * C1) / 2, fun y hy => ?_⟩
  set c := compPt O.s y with hc
  set z := basePt O.Φ y with hz
  have hind0 : ArIn.ind ∅ = fun _ => false := by funext q; simp [ArIn.ind]
  let ℓ : Sym D.host.E → ℝ := fun a => (adlOf (O.Φ.C c) (O.met.hm c) (Finsupp.single a 1)).ht z
  have hneg : ∀ a : Sym D.host.E, a.1 = (fun _ => false) → a.2.1 = none →
      (adlOf (O.Φ.C c) (O.met.hm c) (Finsupp.single a (-1))).ht z = -ℓ a := by
    intro a ha hb
    have := GlobalTheory.T.height_additive_in_symbols D O hC A T H h c z (Finset.univ : Finset Unit) (fun _ => a) (fun _ => -1) (fun _ _ => ⟨ha, hb⟩)
    simpa using this

  have hfalt : H.falt y = -∑ k ∈ Finset.range (letters O.S.Dw).length, ℓ ((fun _ => false), none, .inr k) := by
    rw [h.ht.falt y hy]
    change (adlOf (O.Φ.C c) (O.met.hm c) (detOmSym D.host.E (D.R.f * O.N))).ht z = _
    have e : detOmSym D.host.E (D.R.f * O.N) = ∑ k : Fin (D.R.f * O.N),
        Finsupp.single (((fun _ => false), none, .inr ((Fin.rev k : Fin _) : ℕ)) : Sym D.host.E) (-1) := rfl
    rw [e, GlobalTheory.T.height_additive_in_symbols D O hC A T H h c z _ _ _ (fun _ _ => ⟨rfl, rfl⟩), length_letters]
    rw [← Fin.sum_univ_eq_sum_range (fun k => ℓ ((fun _ => false), none, .inr k)), ← Finset.sum_neg_distrib]
    rw [← Equiv.sum_comp Fin.revPerm]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [ℓ]

  let e : (D.host.E →+* ℂ) × ℕ → ℝ := fun p => ℓ ((fun _ => false), none, .inl p)
  have hjN : O.j ≤ O.N := O.indef.2.le
  have hp : O.S.Dw.p = O.j := O.S.p_eq
  have hpq : O.S.Dw.p + O.S.Dw.q = O.N := O.S.rank_eq
  have hroot : ∀ (τ : D.what₂.Tau) (i : Fin O.N), (O.rootH c (τ, i)).ht z =
      if (i : ℕ) < O.j then e (DV.tauEmb D τ, i)
      else -e (conjEmb (DV.tauEmb D τ), O.N - O.j - 1 - ((i : ℕ) - O.j)) := by
    intro τ i
    change (adlOf (O.Φ.C c) (O.met.hm c) (rootSym O.S.Dw (ArIn.ind ∅) none (DV.tauEmb D τ) i)).ht z = _
    rw [hind0]
    unfold rootSym
    split_ifs with h1 h2 h2
    · rfl
    · omega
    · omega
    · rw [hneg _ rfl rfl]
      have : O.S.Dw.p + O.S.Dw.q - 1 - (i : ℕ) = O.N - O.j - 1 - ((i : ℕ) - O.j) := by omega
      rw [this]
  let Aτ : D.what₂.Tau → ℝ := fun τ => ∑ i ∈ Finset.range O.j, e (DV.tauEmb D τ, i)
  let Bτ : D.what₂.Tau → ℝ := fun τ => ∑ i ∈ Finset.range (O.N - O.j), e (conjEmb (DV.tauEmb D τ), i)
  have hmid : H.hH (midWt O.Y) y = -∑ τ, Aτ τ := by
    rw [h.ht.hH _ y hy]
    change -∑ x : DV.Rt D.what₂.Tau O.N, midWt O.Y x.1 x.2 * (O.rootH c x).ht z = _
    rw [Fintype.sum_prod_type]
    congr 1
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [show ∑ i : Fin O.N, midWt O.Y τ i * (O.rootH c (τ, i)).ht z =
        ∑ i : Fin O.N, (fun k : ℕ => if k < O.j then e (DV.tauEmb D τ, k) else 0) (i : ℕ) from
      Finset.sum_congr rfl fun i _ => by
        rw [hroot]
        change (if (i : ℕ) < O.j then (1 : ℝ) else 0) * _ = if (i : ℕ) < O.j then _ else _
        split_ifs <;> simp]
    rw [Fin.sum_univ_eq_sum_range (fun k => if k < O.j then e (DV.tauEmb D τ, k) else 0) O.N,
      sum_range_ite_lt _ hjN]
  have hind : ∀ τ, H.hH (fun τ' _ => if τ' = τ then 1 else 0) y = -Aτ τ + Bτ τ := by
    intro τ
    rw [h.ht.hH _ y hy]
    change -∑ x : DV.Rt D.what₂.Tau O.N, (if x.1 = τ then (1 : ℝ) else 0) * (O.rootH c x).ht z = _
    rw [Fintype.sum_prod_type, Finset.sum_eq_single τ (fun b _ hb => by simp [hb]) (by simp)]
    simp only [if_true, one_mul]
    have h1 : ∑ i : Fin O.N, (O.rootH c (τ, i)).ht z = ∑ i ∈ Finset.range O.N, (if i < O.j then e (DV.tauEmb D τ, i)
        else -e (conjEmb (DV.tauEmb D τ), O.N - O.j - 1 - (i - O.j))) := by
      rw [← Fin.sum_univ_eq_sum_range (fun i => if i < O.j then e (DV.tauEmb D τ, i)
        else -e (conjEmb (DV.tauEmb D τ), O.N - O.j - 1 - (i - O.j))) O.N]
      exact Finset.sum_congr rfl fun i _ => hroot τ i
    have h3 : ∑ i ∈ Finset.range O.j, (if i < O.j then e (DV.tauEmb D τ, i)
        else -e (conjEmb (DV.tauEmb D τ), O.N - O.j - 1 - (i - O.j))) = Aτ τ :=
      Finset.sum_congr rfl fun i hi => if_pos (Finset.mem_range.1 hi)
    have h4 : ∑ k ∈ Finset.range (O.N - O.j), (if O.j + k < O.j then e (DV.tauEmb D τ, O.j + k)
        else -e (conjEmb (DV.tauEmb D τ), O.N - O.j - 1 - (O.j + k - O.j))) = -Bτ τ := by
      have h5 : ∀ k ∈ Finset.range (O.N - O.j), (if O.j + k < O.j then e (DV.tauEmb D τ, O.j + k)
          else -e (conjEmb (DV.tauEmb D τ), O.N - O.j - 1 - (O.j + k - O.j))) =
            -e (conjEmb (DV.tauEmb D τ), O.N - O.j - 1 - k) := by
        intro k _
        rw [if_neg (by omega), show O.j + k - O.j = k by omega]
      rw [Finset.sum_congr rfl h5, Finset.sum_neg_distrib,
        Finset.sum_range_reflect (fun k => e (conjEmb (DV.tauEmb D τ), k)) (O.N - O.j)]
    rw [h1, ← Finset.sum_range_add_sum_Ico _ hjN, Finset.sum_Ico_eq_sum_range, h3, h4]
    ring

  have hS : |∑ k ∈ Finset.range (letters O.S.Dw).length, ℓ ((fun _ => false), none, .inr k) -
      ∑ τ, (Aτ τ + Bτ τ)| ≤ (letters O.S.Dw).length * C2 := by
    rw [← GlobalTheory.T.letter_sum_eq_tau_sum D O e, ← Fin.sum_univ_eq_sum_range (fun k => ℓ ((fun _ => false), none, .inr k)),
      ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun j _ => hC2 c z j).trans ?_
    simp
  have hI : |∑ τ, H.hH (fun τ' _ => if τ' = τ then 1 else 0) y| ≤ Fintype.card D.what₂.Tau * C1 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun τ _ => (hC1 τ y).2 hy).trans ?_
    simp
  have hsum : ∑ τ, H.hH (fun τ' _ => if τ' = τ then 1 else 0) y = -∑ τ, Aτ τ + ∑ τ, Bτ τ := by
    rw [Finset.sum_congr rfl fun τ _ => hind τ, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  have hAB : ∑ τ, (Aτ τ + Bτ τ) = ∑ τ, Aτ τ + ∑ τ, Bτ τ := Finset.sum_add_distrib
  rw [hmid, hfalt]
  rw [hAB] at hS
  rw [hsum] at hI
  set S := ∑ k ∈ Finset.range (letters O.S.Dw).length, ℓ ((fun _ => false), none, .inr k)
  set A' := ∑ τ, Aτ τ
  set B' := ∑ τ, Bτ τ
  have e2 : -A' - (-S) / 2 = (S - (A' + B')) / 2 + (-A' + B') / 2 := by ring
  rw [e2]
  refine (abs_add_le _ _).trans ?_
  rw [abs_div, abs_div, abs_two]
  linarith

end GlobalTheory.HalfFalt
