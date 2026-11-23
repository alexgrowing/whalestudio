import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType
import Formalism.LocalToGlobal.Columns.HeckeSp
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumRepsDatumEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerDiagonalBlockAsGLMemIntegralGeneralLinear
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeIdentityIntegral
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GenValAddSegL
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsParahoricAndIntegralGLDoubleCosetReps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InSuppMulLeft
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OmTwoTorusLeft
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumNegIndic
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumEqGenVal
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section

namespace GlobalTheory.ParHeckeTransfer

theorem transfer : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D D' : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ t : ℕ, Fintype.card D' = Fintype.card D + t → ∀ (ξ μS μT : kˣ →* ℂˣ), IsTame ξ → IsUnram (μS * ξ⁻¹) → IsUnram (μT * ξ⁻¹) → ∀ (W : Submodule ℂ (Matrix (A ⊕ D') (A ⊕ D) k → ℂ)) (hW : ∀ g h, ∀ u ∈ W, omTwo μS μT g h u ∈ W) (hΦ : datum ξ⁻¹ ∈ W) (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (GL (A ⊕ D) k) X) (x : X) (B : Multiset ℂˣ), IsGen ρ ξ ϖ B x → ∀ (X' : Type) [AddCommGroup X'] [Module ℂ X'] (ρ' : Representation ℂ (GL (A ⊕ D') k) X') (b : W →ₗ[ℂ] X →ₗ[ℂ] X'), (∀ g h (u : W) y, b ⟨omTwo μS μT g h u, hW g h u u.2⟩ (ρ g y) = ρ' h (b u y)) → IsGen ρ' ξ ϖ (B.map (· * (μS ϖ * (μT ϖ)⁻¹)) + segL ϖ (μS ϖ) t) (b ⟨datum ξ⁻¹, hΦ⟩ x) := by
  intro k _ _ _ _ A D D' _ _ _ _ _ _ ϖ hϖ t hD' ξ μS μT hξ hS hT W hW hΦ X _ _ ρ x B hx X' _ _ ρ' b hb
  have hξi : IsTame ξ⁻¹ := fun y hy => by rw [MonoidHom.inv_apply, hξ y hy, inv_one]
  have hρ1 : ∀ y : X, ρ 1 y = y := fun y => by rw [map_one, Module.End.one_apply]
  obtain ⟨hx1, hx2, hx3⟩ := hx
  refine ⟨?_, ?_, fun s => ?_⟩
  · intro j hj d hd
    have h1 := hb 1 j ⟨datum ξ⁻¹, hΦ⟩ x
    rw [hρ1] at h1
    rw [← h1]
    have e : (⟨omTwo μS μT 1 j (datum ξ⁻¹), hW 1 j _ hΦ⟩ : W) = (ξ d : ℂ) • (⟨datum ξ⁻¹, hΦ⟩ : W) :=
      Subtype.ext (GlobalTheory.DatumEigenLeft.omTwo_datum_inv k A D D' ξ μS μT hξ hS j hj d hd)
    rw [e, map_smul, LinearMap.smul_apply]
  · simp [segL, hx2, hD']

  · intro R' d' hR'
    obtain ⟨hr1, hr2⟩ := GlobalTheory.ParHeckeReps.exists_reps_both k A D
    obtain ⟨-, hr2'⟩ := GlobalTheory.ParHeckeReps.exists_reps_both k A D'
    choose RR dd hRR using hr1
    choose RK hRK using hr2
    obtain ⟨RK', hRK'⟩ := hr2' (torusElt k D' ϖ (indic s))
    have hsn : ∀ n : ℕ, ∃ s : Finset D, n ≤ Fintype.card D → s.card = n := fun n => by
      by_cases h : n ≤ Fintype.card D
      · obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset D)) (by simpa using h)
        exact ⟨s, fun _ => hs⟩
      · exact ⟨∅, fun h' => absurd h' h⟩
    choose sn hsn using hsn
    have hq : (0 : ℝ) < (resCard k : ℝ) := by
      have : 0 < Nat.card 𝓀[k] := Nat.card_pos
      unfold resCard; exact_mod_cast this
    have hsq : ((Real.sqrt (resCard k) : ℝ) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]; exact (Real.sqrt_pos.2 hq).ne'
    set Φw : W := ⟨datum ξ⁻¹, hΦ⟩ with hΦw
    set C : ℂ := (μS ϖ : ℂ) ^ s.card * ((Real.sqrt (resCard k) : ℝ) : ℂ) ^ (s.card * (Fintype.card A + Fintype.card D)) with hC
    set cn : ℕ → ℂ := fun n => if n ≤ s.card then ((resCard k ^ (n * (t - (s.card - n))) * Formalism.L2.Col.gaussBin (resCard k) t (s.card - n) : ℕ) : ℂ) else 0 with hcn
    set den : ℕ → ℂ := fun n => (μT ϖ : ℂ) ^ n * ((Real.sqrt (resCard k) : ℝ) : ℂ) ^ (n * (Fintype.card A + Fintype.card D')) with hden
    have hden0 : ∀ n, den n ≠ 0 := fun n => mul_ne_zero (pow_ne_zero _ (Units.ne_zero _)) (pow_ne_zero _ hsq)
    have key : ∑ j ∈ R', (((ξ (d' j))⁻¹ : ℂˣ) : ℂ) • (⟨omTwo μS μT 1 (j * mtor ϖ (indic s)) (datum ξ⁻¹), hW _ _ _ hΦ⟩ : W) =
        C • ∑ n ∈ Finset.range (Fintype.card D + 1), (cn n * (den n)⁻¹) •
            ∑ j ∈ RR (mtor ϖ (-indic (sn n))), (ξ (dd (mtor ϖ (-indic (sn n))) j) : ℂ) •
              (⟨omTwo μS μT (j * mtor ϖ (-indic (sn n))) 1 (datum ξ⁻¹), hW _ _ _ hΦ⟩ : W) := by
      apply Subtype.ext
      funext y
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      have hT1 := GlobalTheory.ParHeckeTarget.sum_reps_datum_eq k A D D' ϖ hϖ ξ⁻¹ hξi s R' d' hR' RK' hRK' y
      have hU := GlobalTheory.ParHecke.heckeIdentity_integral k D D' ϖ hϖ t hD' s RK' hRK' sn (fun n => RK (torusElt k D ϖ (-indic (sn n))))
        (fun n hn => ⟨hsn n hn, hRK _⟩) (schur y)
      have hL : ∑ j ∈ R', (((ξ (d' j))⁻¹ : ℂˣ) : ℂ) * omTwo μS μT 1 (j * mtor ϖ (indic s)) (datum ξ⁻¹) y =
          C * (datum ξ⁻¹ y * ∑ g ∈ RK', intInd (((g⁻¹ : GL D' k)).1 * schur y)) := by
        have e2 : datum ξ⁻¹ y * ∑ g ∈ RK', intInd (((g⁻¹ : GL D' k)).1 * schur y) =
            ∑ g ∈ RK', liftS ξ⁻¹ (fun z => intInd ((g⁻¹).1 * z)) y := by
          rw [Finset.mul_sum]; rfl
        rw [e2, ← hT1, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [GlobalTheory.TorusLeft.omTwo_torusLeft k A D D' ϖ hϖ ξ μS μT hS s j (hR'.1 j hj).1]
        simp only [MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val, hC]
        field_simp
      have hR : ∀ n ∈ Finset.range (Fintype.card D + 1),
          (cn n * (den n)⁻¹) * ∑ j ∈ RR (mtor ϖ (-indic (sn n))), (ξ (dd (mtor ϖ (-indic (sn n))) j) : ℂ) *
              omTwo μS μT (j * mtor ϖ (-indic (sn n))) 1 (datum ξ⁻¹) y =
            cn n * (datum ξ⁻¹ y * ∑ g ∈ RK (torusElt k D ϖ (-indic (sn n))), intInd (schur y * g.1)) := by
        intro n hn
        have hc := hsn n (Nat.lt_succ_iff.1 (Finset.mem_range.1 hn))
        have e2 : datum ξ⁻¹ y * ∑ g ∈ RK (torusElt k D ϖ (-indic (sn n))), intInd (schur y * g.1) =
            ∑ g ∈ RK (torusElt k D ϖ (-indic (sn n))), liftS ξ⁻¹ (fun z => intInd (z * g.1)) y := by
          rw [Finset.mul_sum]; rfl
        rw [e2, ← GlobalTheory.ParHeckeSource.sum_reps_datum_eq k A D D' ϖ hϖ ξ⁻¹ hξi (sn n) _ _ (hRR _) _ (hRK _) y, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [GlobalTheory.TorusRightScalar.torusRight k A D D' ϖ hϖ ξ μS μT hT (sn n) j ((hRR _).1 j hj).1, hc]
        have := hden0 n
        simp only [MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val, hden] at this ⊢
        field_simp
      rw [hL, hU, Finset.sum_congr rfl hR]
      congr 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      ring
    have lhs : ∑ j ∈ R', (((ξ (d' j))⁻¹ : ℂˣ) : ℂ) • ρ' (j * mtor ϖ (indic s)) (b Φw x) =
        b (∑ j ∈ R', (((ξ (d' j))⁻¹ : ℂˣ) : ℂ) • (⟨omTwo μS μT 1 (j * mtor ϖ (indic s)) (datum ξ⁻¹), hW _ _ _ hΦ⟩ : W)) x := by
      rw [map_sum, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, LinearMap.smul_apply, ← hb 1 _ Φw x, hρ1]
    have e4 : ∀ n ∈ Finset.range (Fintype.card D + 1),
        b ((cn n * (den n)⁻¹) • ∑ j ∈ RR (mtor ϖ (-indic (sn n))), (ξ (dd (mtor ϖ (-indic (sn n))) j) : ℂ) •
              (⟨omTwo μS μT (j * mtor ϖ (-indic (sn n))) 1 (datum ξ⁻¹), hW _ _ _ hΦ⟩ : W)) x =
          (cn n * (den n)⁻¹ * genVal (resCard k) (Fintype.card A) (Fintype.card D) B n) • b Φw x := by
      intro n hn
      have hc := hsn n (Nat.lt_succ_iff.1 (Finset.mem_range.1 hn))
      rw [map_smul, LinearMap.smul_apply, map_sum, LinearMap.sum_apply]
      simp_rw [map_smul, LinearMap.smul_apply]
      rw [GlobalTheory.ParHeckeTransfer.sum_eq_genVal k A D D' ϖ ξ μS μT hξ hT W hW hΦ X ρ x B ⟨hx1, hx2, hx3⟩ X' ρ' b hb (sn n) _ _ (hRR _), hc, smul_smul]
    rw [lhs, key, map_smul, LinearMap.smul_apply, map_sum, LinearMap.sum_apply, Finset.sum_congr rfl e4,
      ← Finset.sum_smul, smul_smul]
    congr 1
    have hN := GlobalTheory.ParHecke.StringEig.genVal_add_segL k ϖ hϖ (Fintype.card A) (Fintype.card D) t s.card B (μS ϖ) (μT ϖ) hx2
      (by rw [← hD']; exact Finset.card_le_univ s)
    rw [show Fintype.card D' = Fintype.card D + t from hD']
    rw [hN, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [hC, hcn, hden, hD']
    ring

end GlobalTheory.ParHeckeTransfer
