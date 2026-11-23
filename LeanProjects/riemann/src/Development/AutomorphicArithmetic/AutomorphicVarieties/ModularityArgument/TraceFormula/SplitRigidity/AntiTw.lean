import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.SplitRigidity.SplitRigidAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.MuInf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.QuadraticCharacterNorms.QuadCharNorm
import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.AbsoluteCharacterNorms.UnitExponentHolds
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousIdeleCharLocalFactorization
open PositivityTheory.RgJS UpperTheory.V.Z.Tf.GOne UpperTheory.V.Z.Tf.SR
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryBC

private theorem val_pow' {F : Type} [Field F] [NumberField F] (ω : HChar F) (w : HeightOneSpectrum (𝓞 F)) (k : ℕ) :
    (ω ^ k).val w = ω.val w ^ k := by
  induction k with
  | zero => simp [HChar.val, HChar.locK, HChar.loc]
  | succ k ih => rw [pow_succ, pow_succ, HChar.val_mul, ih]

private theorem norm_val_one {F : Type} [Field F] [NumberField F] (ω : HChar F) (h : ω.IsUnitary)
    (w : HeightOneSpectrum (𝓞 F)) : ‖((ω.val w : ℂˣ) : ℂ)‖ = 1 := h _

private theorem unitary_pow {F : Type} [Field F] [NumberField F] (ω : HChar F) (h : ω.IsUnitary) (k : ℕ) :
    (ω ^ k).IsUnitary := fun x => by
  have e : (ω ^ k).1 x = ω.1 x ^ k := MonoidHom.pow_apply ω.1 k x
  rw [e, Units.val_pow_eq_pow_val, norm_pow, h x, one_pow]

private theorem unitary_twist {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ} {π : CG E n}
    (h : π.IsUnitary) {χ : HChar E} (hχ : χ.IsUnitary) : (π.twist χ).IsUnitary := by
  obtain ⟨ω, hω, hc⟩ := h
  refine ⟨ω * χ ^ n, fun x => ?_, hc.twist χ⟩
  have e : (ω * χ ^ n).1 x = ω.1 x * (χ ^ n).1 x := rfl
  rw [e, Units.val_mul, norm_mul, hω x, unitary_pow χ hχ n x, one_mul]

theorem UpperTheory.V.Z.Tf.SR.antiTw :
    AntiTw := by
  intro E _ _ _ hU
  obtain ⟨μ, e, hμ⟩ := PositivityTheory.Rg.BcB.F.Fok.Mu3.muExists E hU
  obtain ⟨hv, hinf⟩ := UpperTheory.V.Z.Tf.GaloisFromTraceFormula.muInf E μ e hμ
  have hu : (μ ^ 2).IsUnitary := unitary_pow μ hμ.1 2
  refine ⟨μ ^ 2, ?_, fun n π hn hπ => ⟨fun i => unitary_twist hπ (unitary_pow _ hu i), fun i j hij => ?_⟩⟩
  · filter_upwards [GlobalTheory.HeckeSplit.eventually_unrAt (μ ^ 2).1 (μ ^ 2).2.1] with w hw
    refine ⟨hw, norm_val_one _ hu w, fun hs => ?_⟩
    rw [val_pow', hv w hs]
    simp
  · have hij' : π.twist (μ ^ (2 * i)) = π.twist (μ ^ (2 * j)) := by
      simpa only [pow_mul] using hij
    let v : InfinitePlace E := Classical.arbitrary _
    have h := congrArg (fun P : CG E n => (P.infChar v.embedding).sum) hij'
    simp only [(hinf n _ π v).1, Multiset.sum_map_add, Multiset.map_const', Multiset.sum_replicate,
      Multiset.map_id', Multiset.card_map, CG.card_infChar, nsmul_eq_mul] at h
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    have he0 : (e v : ℂ) ≠ 0 := by
      have : e v ≠ 0 := fun h0 => by
        have := hμ.2.2.2.1 v
        rw [h0] at this
        exact absurd this (by decide)
      exact_mod_cast this
    have h2 : (i : ℂ) = j := by
      have h3 := add_left_cancel h
      have h4 := mul_left_cancel₀ hn0 h3
      push_cast at h4
      field_simp at h4
      simpa using h4
    exact_mod_cast h2
