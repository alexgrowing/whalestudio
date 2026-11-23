import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.ProdDiagonalShiftOneMinus

noncomputable section

namespace PI.OmVg

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  NumberField IsDedekindDomain Matrix PI.OmLocU Formalism.L2.SG.Pf.NcVal.OmVSt Formalism.L2.SG.Pf.NcVal.OmVSt.OmW
open scoped TensorProduct

theorem natCast_val_lt {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (t : ℕ)
    (ht : ((t : 𝓞 F)) ∈ v.asIdeal) : Valued.v ((t : ℕ) : Fv F v) < 1 := by
  have h1 : ((t : ℕ) : Fv F v) = algebraMap (𝓞 F) (Fv F v) (t : 𝓞 F) := by simp
  rw [h1]
  refine (HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v (t : 𝓞 F)).trans_lt ?_
  erw [HeightOneSpectrum.valuation_of_algebraMap]
  exact (HeightOneSpectrum.intValuation_lt_one_iff_mem v _).2 ht

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)

theorem localGramMatrixFrame_apply (v : PlX X) (a b : Fin (D.R.rS + 1 + D.R.rS)) :
    localGramMatrixFrame X u' v a b = inclR (Fv X.B.I.F v) (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) a b) := rfl

theorem negT_mem (v : PlX X) (hv : ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal) {ϖ : Fv X.B.I.F v}
    (hϖ : IsUnif v ϖ) : inclR (Fv X.B.I.F v) (-((Tw u' : ℕ) : X.B.I.E)) ∈ PO (E := X.B.I.E) v ϖ := by
  obtain ⟨h0, -, -⟩ := unif_spec v ϖ hϖ
  have hm := natCast_div_mem v (Tw u') hv hϖ
  refine ⟨sc (E := X.B.I.E) v (-(((Tw u' : ℕ) : Fv X.B.I.F v) * ϖ⁻¹)), ?_, ?_⟩
  · simpa using sc_mul_mem_oEv v (neg_mem hm) (Orb.oSub (E := X.B.I.E) v).1
  · rw [sc_mul]
    have e : ϖ * -(((Tw u' : ℕ) : Fv X.B.I.F v) * ϖ⁻¹) = -((Tw u' : ℕ) : Fv X.B.I.F v) := by field_simp
    rw [e, show sc (E := X.B.I.E) v (-((Tw u' : ℕ) : Fv X.B.I.F v)) =
      algebraMap (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) (-((Tw u' : ℕ) : Fv X.B.I.F v)) from rfl,
      map_neg, map_neg, map_natCast, map_natCast]

theorem local_gram_matrix_corank_one (v : PlX X) (hv : ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal) {ϖ : Fv X.B.I.F v}
    (hϖ : IsUnif v ϖ) : GramCor v ϖ (localGramMatrixFrame X u' v) := by
  have hN := negT_mem X u' v hv hϖ
  have h0 : (0 : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) ∈ PO (E := X.B.I.E) v ϖ :=
    ⟨0, Orb.oev_zero v, by rw [mul_zero]⟩
  refine ⟨iz, fun j => ?_, fun j => ?_, ?_⟩
  · rw [localGramMatrixFrame_apply, gramE_apply, piv_iz]
    split_ifs with h
    · rw [cD_iz]; exact hN
    · rw [map_zero]; exact h0
  · rw [localGramMatrixFrame_apply, gramE_apply]
    split_ifs with h
    · rw [eq_iz_of_piv h, cD_iz]; exact hN
    · rw [map_zero]; exact h0
  · set P := (Function.Involutive.toPerm _ (piv_invol D.R.rS)).permMatrix X.B.I.E with hPdef
    have hM : localGramMatrixFrame X u' v + Matrix.single iz iz 1 = (diagonal (diagonalShiftOneMinus X u') * P).map (inclR (Fv X.B.I.F v)) := by
      ext a b
      rw [Matrix.add_apply, localGramMatrixFrame_apply, gramE_apply, Matrix.map_apply, diagonal_mul, Matrix.single_apply]
      simp only [hPdef, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
        Option.some.injEq, Function.Involutive.coe_toPerm]
      by_cases ha : a = iz
      · subst ha
        rw [piv_iz]
        by_cases hb : iz = b
        · subst hb
          rw [cD_iz]
          simp [diagonalShiftOneMinus, iz]
          ring
        · simp [hb]
      · have hav : a.val ≠ D.R.rS := fun e => ha (Fin.ext e)
        have h1 : ¬ (iz = a ∧ iz = b) := fun h => ha h.1.symm
        simp [cD, diagonalShiftOneMinus, hav, h1]
    obtain ⟨s, hs, hPd⟩ : ∃ s : ℤ, s * s = 1 ∧ P.det = (s : X.B.I.E) :=
      ⟨((Equiv.Perm.sign (Function.Involutive.toPerm _ (piv_invol D.R.rS)) : ℤˣ) : ℤ),
        by rw [← Units.val_mul, Int.units_mul_self, Units.val_one], by rw [hPdef, det_permutation]⟩
    have hdet : (localGramMatrixFrame X u' v + Matrix.single iz iz 1).det =
        inclR (Fv X.B.I.F v) ((1 - ((Tw u' : ℕ) : X.B.I.E)) * (s : X.B.I.E)) := by
      rw [hM, ← RingHom.mapMatrix_apply, ← RingHom.map_det, det_mul, det_diagonal, prod_diagonalShiftOneMinus, hPd]
    set t : Fv X.B.I.F v := 1 - ((Tw u' : ℕ) : Fv X.B.I.F v) with htdef
    have hv1 : Valued.v t = 1 := Valuation.map_one_sub_of_lt _ (natCast_val_lt v _ hv)
    have ht0 : t ≠ 0 := fun h => by rw [h, map_zero] at hv1; exact zero_ne_one hv1
    have hti : t⁻¹ ∈ v.adicCompletionIntegers X.B.I.F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hv1, inv_one]
    refine ⟨sc (E := X.B.I.E) v t⁻¹ * inclR (Fv X.B.I.F v) (((s : 𝓞 X.B.I.E)) : X.B.I.E),
      sc_mul_mem_oEv v hti (inclR_mem_OEv X v _), ?_⟩
    rw [hdet]
    have e1 : inclR (Fv X.B.I.F v) (1 - ((Tw u' : ℕ) : X.B.I.E)) = sc (E := X.B.I.E) v t := by
      rw [htdef, show sc (E := X.B.I.E) v (1 - ((Tw u' : ℕ) : Fv X.B.I.F v)) =
        algebraMap (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) (1 - ((Tw u' : ℕ) : Fv X.B.I.F v)) from rfl,
        map_sub, map_sub, map_one, map_one, map_natCast, map_natCast]
    have e2 : (((s : 𝓞 X.B.I.E)) : X.B.I.E) = (s : X.B.I.E) := by simp
    rw [e2, map_mul, e1]
    calc sc (E := X.B.I.E) v t * inclR (Fv X.B.I.F v) (s : X.B.I.E) *
          (sc (E := X.B.I.E) v t⁻¹ * inclR (Fv X.B.I.F v) (s : X.B.I.E))
        = (sc (E := X.B.I.E) v t * sc (E := X.B.I.E) v t⁻¹) * inclR (Fv X.B.I.F v) ((s : X.B.I.E) * s) := by
          rw [map_mul]; ring
      _ = 1 := by
          rw [sc_mul, mul_inv_cancel₀ ht0, sc_one, ← Int.cast_mul, hs, Int.cast_one, map_one, mul_one]

end PI.OmVg
