import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPointsLieOverDistinctPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceMatrixEqOfAgreeWithFramedGLStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GeneratorMemSplitPrimeLevelPrimeMemPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelColumnSubOneMemBaseLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPointBaseLatticeCoordsIntegralLastInPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardPairFrameCoordinatesIntegralAndFunctionaStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

theorem GlobalTheory.AdForm.CompFix.intMat_keeps {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : Type} [Fintype n] [DecidableEq n] (M M' : Matrix n n k) (hMM : M * M' = 1) (hM : ∀ r s, M r s ∈ 𝒪[k])
    (hM' : ∀ r s, M' r s ∈ 𝒪[k]) (r₀ : n) (hr : ∀ s, valuation k (M' r₀ s - (1 : Matrix n n k) r₀ s) < 1) (z : n → k) :
    ((∀ r, (M' *ᵥ z) r ∈ 𝒪[k]) ↔ ∀ r, z r ∈ 𝒪[k]) ∧ ((∀ r, z r ∈ 𝒪[k]) → valuation k ((M' *ᵥ z) r₀ - z r₀) < 1) := by
  have hint : ∀ (N : Matrix n n k), (∀ r s, N r s ∈ 𝒪[k]) → ∀ w : n → k, (∀ r, w r ∈ 𝒪[k]) → ∀ r, (N *ᵥ w) r ∈ 𝒪[k] :=
    fun N hN w hw r => Subring.sum_mem _ fun s _ => Subring.mul_mem _ (hN r s) (hw s)
  refine ⟨⟨fun h r => ?_, fun h => hint M' hM' z h⟩, fun h => ?_⟩
  · have e : M *ᵥ (M' *ᵥ z) = z := by rw [Matrix.mulVec_mulVec, hMM, Matrix.one_mulVec]
    rw [← e]
    exact hint M hM _ h r
  · have e : (M' *ᵥ z) r₀ - z r₀ = ∑ s, (M' r₀ s - (1 : Matrix n n k) r₀ s) * z s := by
      have : z r₀ = ∑ s, (1 : Matrix n n k) r₀ s * z s := by simp [Matrix.one_apply]
      rw [this]
      simp only [Matrix.mulVec, dotProduct]
      rw [← Finset.sum_sub_distrib]
      simp_rw [sub_mul]
    rw [e]
    refine Valuation.map_sum_lt _ one_ne_zero fun s _ => ?_
    rw [Valuation.map_mul]
    have h1 := hr s
    have h2 : valuation k (z s) ≤ 1 := (Valuation.mem_integer_iff _ _).1 (h s)
    calc valuation k (M' r₀ s - (1 : Matrix n n k) r₀ s) * valuation k (z s) ≤ valuation k (M' r₀ s - (1 : Matrix n n k) r₀ s) * 1 :=
          mul_le_mul' le_rfl h2
      _ < 1 := by rw [mul_one]; exact h1

set_option maxHeartbeats 2000000 in

theorem GlobalTheory.AdForm.comp_fixes_stdPair : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    GlobalTheory.AdForm.StdT I l Z u p β Q L → ∀ j, j ≤ B.R.m → ∀ b, ∀ κ ∈ A.U j b, ∀ i (g : GL (Fin ((I.rec7 l Z).sp.X j).rank) k), κ * ((β j i).gl g)⁻¹ ∈ grpOff ((I.rec7 l Z).sp.X j) (· = (p i).v) → g • Q j i = Q j i := by
  intro B X I hOk hPins l Z u a Ch A hA k _ _ _ _ ι p β Q L hS j hj b κ hκ i g hg

  obtain ⟨e, he⟩ := hS.1
  obtain ⟨hpi, hT⟩ := GlobalTheory.T.generator_mem_split_prime_level_prime_mem_place I hOk l Z u k (p i) (e i) (he i)
  have key : ∀ κ₀ ∈ A.U j b, ∀ r s : Fin ((I.rec7 l Z).sp.X j).rank,
      ((mt _ κ₀).map (p i).pr) r s ∈ 𝒪[k] ∧ (r.1 + 1 = ((I.rec7 l Z).sp.X j).rank →
        valuation k (((mt _ κ₀).map (p i).pr) r s - (1 : Matrix (Fin ((I.rec7 l Z).sp.X j).rank) (Fin ((I.rec7 l Z).sp.X j).rank) k) r s) < 1) := by
    intro κ₀ hκ₀ r s
    have hn := rankN (I.rec7 l Z) j hj
    have h3 := GlobalTheory.T.chartLevel_column_sub_one_mem_baseLattice I hOk hPins l Z u a Ch A hA j hj b κ₀ hκ₀ (p i).v hT (Fin.cast hn s)
    let y : Fin ((I.rec7 l Z).R.N j) → AE (I.rec7 l Z) := fun r' =>
      mt _ κ₀ (Fin.cast hn.symm r') s - (1 : Matrix (Fin ((I.rec7 l Z).sp.X j).rank) (Fin ((I.rec7 l Z).sp.X j).rank) (AE (I.rec7 l Z))) (Fin.cast hn.symm r') s
    have hy : (fun r' => Formalism.UG.prV (E := (I.rec7 l Z).host.E) (p i).v (toEAf (I.rec7 l Z) (y r'))) =
        (fun r' => Formalism.UG.prV (E := (I.rec7 l Z).host.E) (p i).v (GlobalTheory.AdForm.finM _ hn κ₀ r' (Fin.cast hn s)) -
          (1 : Matrix (Fin ((I.rec7 l Z).R.N j)) (Fin ((I.rec7 l Z).R.N j)) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] (p i).v.adicCompletion (I.rec7 l Z).host.F)) r' (Fin.cast hn s)) := by
      funext r'
      simp only [y]
      rw [RingHom.map_sub, RingHom.map_sub]
      congr 1
      by_cases h : r' = Fin.cast hn s
      · subst h
        have : Fin.cast hn.symm (Fin.cast hn s) = s := Fin.ext rfl
        rw [this, Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one, RingHom.map_one]
      · have h' : Fin.cast hn.symm r' ≠ s := fun h2 => h (Fin.ext (by rw [← h2]; rfl))
        rw [Matrix.one_apply_ne h', Matrix.one_apply_ne h, RingHom.map_zero, RingHom.map_zero]
    have hLb : ∀ x, x ∈ (A.K j hj b).lev.Lb ↔ ∀ j' : Fin ((I.rec7 l Z).R.N j), ∃ r : 𝓞 (I.rec7 l Z).host.E, x j' = (r : (I.rec7 l Z).host.E) ∧ (j'.1 + 1 = (I.rec7 l Z).R.N j → X.piT u ∣ r) :=
      fun x => (hA.reads j hj).lb b x
    have h4 := GlobalTheory.T.splitPoint_baseLattice_coords_integral_last_in_prime (I.rec7 l Z) k (p i) (e i).1 (he i) _ (X.piT u) hpi _ hLb y (hy ▸ h3) (Fin.cast hn r)
    have hyr : y (Fin.cast hn r) = mt _ κ₀ r s - (1 : Matrix (Fin ((I.rec7 l Z).sp.X j).rank) (Fin ((I.rec7 l Z).sp.X j).rank) (AE (I.rec7 l Z))) r s := rfl
    rw [hyr] at h4
    have h1 : (p i).pr ((1 : Matrix (Fin ((I.rec7 l Z).sp.X j).rank) (Fin ((I.rec7 l Z).sp.X j).rank) (AE (I.rec7 l Z))) r s) =
        (1 : Matrix (Fin ((I.rec7 l Z).sp.X j).rank) (Fin ((I.rec7 l Z).sp.X j).rank) k) r s := by
      simp only [Matrix.one_apply]; split_ifs <;> simp
    rw [map_sub, h1] at h4
    refine ⟨?_, fun hr => ?_⟩
    · have := Subring.add_mem _ h4.1 (show (1 : Matrix (Fin ((I.rec7 l Z).sp.X j).rank) (Fin ((I.rec7 l Z).sp.X j).rank) k) r s ∈ 𝒪[k] by
        simp only [Matrix.one_apply]; split_ifs
        · exact Subring.one_mem _
        · exact Subring.zero_mem _)
      rwa [sub_add_cancel] at this
    · exact h4.2 (by rw [Fin.coe_cast, ← hn]; exact hr)

  set M := (mt _ κ).map (p i).pr with hMdef
  set M' := (mt _ κ⁻¹).map (p i).pr with hM'def
  have hmt : ∀ x y : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j), mt _ (x * y) = mt _ x * mt _ y := fun x y => by
    simp only [Formalism.L2.Theta.mt, map_mul, Units.val_mul]
  have hMM : M * M' = 1 := by
    rw [hMdef, hM'def, ← Matrix.map_mul, ← hmt, mul_inv_cancel]
    simp only [Formalism.L2.Theta.mt, map_one, Units.val_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hM'M : M' * M = 1 := by
    rw [hMdef, hM'def, ← Matrix.map_mul, ← hmt, inv_mul_cancel]
    simp only [Formalism.L2.Theta.mt, map_one, Units.val_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hM := GlobalTheory.T.splitPlace_matrix_eq_of_agree_with_framedGL (I.rec7 l Z) k (p i) _ _ (β j i) κ g hg
  rw [← hMdef] at hM
  rcases Nat.eq_zero_or_pos ((I.rec7 l Z).sp.X j).rank with h0 | hpos
  · have : g = 1 := by
      exact Units.ext (Matrix.ext fun a _ => absurd a.2 (by omega))
    rw [this, one_smul]
  let r₀ : Fin ((I.rec7 l Z).sp.X j).rank := ⟨((I.rec7 l Z).sp.X j).rank - 1, by omega⟩
  have hr₀ : r₀.1 + 1 = ((I.rec7 l Z).sp.X j).rank := by simp only [r₀]; omega
  have hK := GlobalTheory.AdForm.CompFix.intMat_keeps M M' hMM (fun r s => (key κ hκ r s).1) (fun r s => (key κ⁻¹ (inv_mem hκ) r s).1) r₀
    (fun s => (key κ⁻¹ (inv_mem hκ) r₀ s).2 hr₀)

  have hbg : ∀ x : Fin ((I.rec7 l Z).sp.X j).rank → k, (β j i).b *ᵥ (g⁻¹ • x) = M' *ᵥ ((β j i).b *ᵥ x) := by
    intro x
    have e1 : (β j i).b * g.val = M * (β j i).b := by
      rw [hM, Matrix.mul_assoc, Matrix.mul_assoc, (β j i).b'b, Matrix.mul_one]
    have e2 : (β j i).b *ᵥ x = M *ᵥ ((β j i).b *ᵥ (g⁻¹ • x)) := by
      have e3 : x = g.val *ᵥ (g⁻¹ • x) := by
        change x = g.val *ᵥ ((g⁻¹).val *ᵥ x)
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
      conv_lhs => rw [e3]
      rw [Matrix.mulVec_mulVec, e1, ← Matrix.mulVec_mulVec]
    rw [e2, Matrix.mulVec_mulVec, hM'M, Matrix.one_mulVec]
  refine Pair.ext fun x a' => ?_
  rw [Pair.smul_hasVal, GlobalTheory.T.standardPair_frameCoordinates_integral_and_functional I l Z u k ι p β Q L hS j hj i r₀ hr₀, GlobalTheory.T.standardPair_frameCoordinates_integral_and_functional I l Z u k ι p β Q L hS j hj i r₀ hr₀, hbg]
  have hres : ∀ (s y₁ y₂ : 𝒪[k]), valuation k ((y₁ : k) - y₂) < 1 → residue 𝒪[k] (s * y₁) = residue 𝒪[k] (s * y₂) := by
    intro s y₁ y₂ h
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, ← mul_sub]
    refine Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 ?_)
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.2 (by simpa using h)
  obtain ⟨hiff, hlast⟩ := hK ((β j i).b *ᵥ x)
  constructor
  · rintro ⟨y, hy, s, hs, ha⟩
    have hz : ∀ r, ((β j i).b *ᵥ x) r ∈ 𝒪[k] := hiff.1 fun r => hy r ▸ (y r).2
    refine ⟨fun r => ⟨_, hz r⟩, fun r => rfl, s, hs, ?_⟩
    rw [ha]
    refine hres s _ _ ?_
    rw [hy r₀]
    exact hlast hz
  · rintro ⟨y, hy, s, hs, ha⟩
    have hz : ∀ r, ((β j i).b *ᵥ x) r ∈ 𝒪[k] := fun r => hy r ▸ (y r).2
    refine ⟨fun r => ⟨_, hiff.2 hz r⟩, fun r => rfl, s, hs, ?_⟩
    rw [ha]
    refine (hres s _ _ ?_).symm
    rw [hy r₀]
    exact hlast hz

end
