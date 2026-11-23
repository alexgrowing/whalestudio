import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Definitions.Foundations.VanishOrdL
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ZetaUr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.RepNewform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoefficientRingFiniteExtensionPadicStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompactGroupRepDefinedOverFiniteExtension
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ImportsExtra
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUpperTriangularConjIntegralCompactStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnramifiedOfLevelAwayInertiaCharactersStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterPowPredEqOneOfKillsPrimeRootsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IrreducibleRestrictionOfIsoStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SrcOfRepIso
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.NfSrc

theorem upper_triangular_conj_lower_right_entry_eq {k : Type} [Field k] (B : GL (Fin 2) k) (X : Matrix (Fin 2) (Fin 2) k)
    (hB : (B : Matrix (Fin 2) (Fin 2) k) 1 0 = 0) (hX : X 1 0 = 0) :
    ((B : Matrix (Fin 2) (Fin 2) k) * X * ((B⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)) 1 1 = X 1 1 := by
  have hinv := GlobalTheory.NfEx.inv_up B hB
  have h1 : ((B⁻¹ * B : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = 1 := by simp
  have a11 := congrFun (congrFun h1 1) 1
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hinv.1, zero_mul, zero_add, Matrix.one_apply_eq] at a11
  simp only [Matrix.mul_apply, Fin.sum_univ_two, hB, hX, zero_mul, zero_add, mul_zero]
  calc _ = X 1 1 * ((B⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) 1 1 * (B : Matrix (Fin 2) (Fin 2) k) 1 1 := by ring
    _ = _ := by rw [mul_assoc, a11, mul_one]

end GlobalTheory.NfSrc

theorem GlobalTheory.Ord2.exists_nf_srcUr : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (W : R2 Ω l), l ≠ 2 → 1 ≤ e → admitted ι e W → SrcL ι e W → ∃ (S : Finset Pl) (A : ValuationSubring Ω) (W' : R2 Ω l) (g : Newform (2 * e + 1)), RepIso W W' ∧ Nf e S A W' ∧ SrcUr ι e A W' g := by
  intro l _ Ω _ _ _ ι e W hl he hW hS
  obtain ⟨⟨g0, χ, A, κ, hM0, ha0, hχ, hatt, hA, hfl, hin⟩, hne⟩ := hS
  obtain ⟨g, hg⟩ := hfl
  obtain ⟨M, hM, hMa⟩ := hW.away
  obtain ⟨S, hSa, hSu⟩ := GlobalTheory.T.unramified_of_levelAway_inertia_characters l Ω W M hM hMa
  let r : G ℚ Ω →* GL (Fin 2) (Qbar l) := (MulAut.conj g).toMonoidHom.comp W
  have hrc : Continuous r := by
    show Continuous fun s => g * W s * g⁻¹
    exact (continuous_const.mul hW.cont).mul continuous_const
  obtain ⟨E, hE, hEm⟩ := GlobalTheory.CompactRepField.exists_finiteDimensional_entries_mem l (G ℚ Ω) 2 r
    (fun i j => ((Units.continuous_val.comp hrc).matrix_elem i j))
  obtain ⟨B, hB10, hBint⟩ := GlobalTheory.T.exists_upperTriangular_conj_integral_compact l (G ℚ Ω) E r hE hrc hEm
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_coefficientRing_finiteExtension_padic l E hE
  let h : GL (Fin 2) (Qbar l) := B * g
  let W' : R2 Ω l := (MulAut.conj h).toMonoidHom.comp W
  have hh : ∀ s, W' s = h * W s * h⁻¹ := fun s => rfl
  have hW' : ∀ s, W' s = B * r s * B⁻¹ := fun s => by
    show h * W s * h⁻¹ = B * (g * W s * g⁻¹) * B⁻¹
    simp only [h, mul_inv_rev]; group
  have hiso : RepIso W W' := ⟨h, hh⟩
  have hdt : dt W' = dt W := by
    ext s
    rw [GlobalTheory.Ord2.TwDet.dt_coe, GlobalTheory.Ord2.TwDet.dt_conj W h s]
    rfl
  have hdet : ∀ s, (dt W' s : Qbar l) = (mat W' s).det := fun s => rfl
  have hker : ∀ s, W' s = 1 ↔ W s = 1 := fun s => by
    show h * W s * h⁻¹ = 1 ↔ W s = 1
    constructor
    · intro hh; rw [mul_inv_eq_one, mul_eq_left] at hh; exact hh
    · intro hh; rw [hh]; simp
  have hinv := GlobalTheory.NfEx.inv_up B hB10
  have hup : ∀ (s : G ℚ Ω) (hs : s ∈ Dec (F := ℚ) A), mat W' s 1 0 = 0 ∧ mat W' s 0 0 = (κ 0 ⟨s, hs⟩ : Qbar l) ∧
      mat W' s 1 1 = (κ 1 ⟨s, hs⟩ : Qbar l) := by
    intro s hs
    have h1 := (hg ⟨s, hs⟩).1 1 0 (by decide)
    have h2 := (hg ⟨s, hs⟩).2 0
    have h3 := (hg ⟨s, hs⟩).2 1
    have := GlobalTheory.NfEx.up2 (B : Matrix (Fin 2) (Fin 2) (Qbar l)) ((r s : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l))
      ((B⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) hB10 h1 hinv.1
    have e1 : mat W' s = (B : Matrix (Fin 2) (Fin 2) (Qbar l)) * ((r s : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) * ((B⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) := by
      simp only [mat, hW', Units.val_mul]
    refine ⟨by rw [e1]; exact this.1, ?_, ?_⟩
    · rw [e1, this.2, ← h2]
      change _ = ((r s : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) 0 0
      calc _ = (B : Matrix (Fin 2) (Fin 2) (Qbar l)) 0 0 * ((B⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) 0 0 * ((r s : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) 0 0 := by ring
        _ = _ := by rw [hinv.2, one_mul]
    · rw [e1, GlobalTheory.NfSrc.upper_triangular_conj_lower_right_entry_eq B ((r s : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) hB10 h1]
      exact h3

  have hline : ∀ (s : G ℚ Ω) (hs : s ∈ Ine (F := ℚ) A),
      mat W' s 0 0 = eps l s ^ e * (χ s : Qbar l) := by
    intro s hs
    have hd : s ∈ Dec (F := ℚ) A := Ine_le_Dec A hs
    obtain ⟨u10, u00, u11⟩ := hup s hd
    have hi := hin ⟨s, hd⟩ hs
    have hD : (dt W s : Qbar l) = mat W' s 0 0 * mat W' s 1 1 := by
      rw [← hdt, hdet, Matrix.det_fin_two, u10, mul_zero, sub_zero]
    have hdne : (dt W s : Qbar l) ≠ 0 := Units.ne_zero _
    simp only [zpow_natCast] at hi
    rw [← u11] at hi
    simp only [eps]
    calc mat W' s 0 0 = mat W' s 0 0 * (mat W' s 1 1 * (cycBar ℚ Ω l s : Qbar l) ^ e * ((dt W s : Qbar l)⁻¹ * (χ s : Qbar l))) := by
          rw [hi, mul_one]
      _ = (mat W' s 0 0 * mat W' s 1 1) * (dt W s : Qbar l)⁻¹ * ((cycBar ℚ Ω l s : Qbar l) ^ e * (χ s : Qbar l)) := by ring
      _ = _ := by rw [← hD, mul_inv_cancel₀ hdne, one_mul]
  refine ⟨S, A, W', g0, hiso, ?_, ?_⟩
  · refine
      { l_odd := hl
        e_pos := he
        cont := ?_
        int := ⟨c, fun s i j => (hc _).2 ⟨?_, ?_⟩⟩
        above := hSa
        unr := ?_
        det2 := by rw [hdt]; exact hW.det2
        odd := by rw [hdt]; exact hW.odd
        irr := GlobalTheory.T.irreducible_restriction_of_iso Ω l W W' hiso hW.irr
        atL := hA
        upper := fun s hs => (hup s hs).1
        wt := ?_
        ne := ?_ }
    · show Continuous fun s => h * W s * h⁻¹
      exact (continuous_const.mul hW.cont).mul continuous_const
    · have := (hBint s i j).1; simpa only [mat, hW'] using this
    · have := (hBint s i j).2; simpa only [mat, hW'] using this
    · intro w hw B' hB' s hs
      exact (hker s).2 (hSu w hw B' hB' hs)
    · refine ⟨l - 1, ?_, fun s hs => ?_⟩
      · have := (Fact.out : l.Prime).two_le; omega
      · rw [hline s hs, mul_pow, ← pow_mul]
        have hχ1 := GlobalTheory.T.character_pow_pred_eq_one_of_killsPrimeRoots Ω l _ χ s hχ
        rw [← Units.val_pow_eq_pow_val (χ s), hχ1, Units.val_one, mul_one]
    · obtain ⟨s, hs⟩ := hne A κ hA ⟨g, hg⟩
      refine ⟨s, s.2, ?_⟩
      rw [(hup s s.2).2.1]
      intro hh
      exact hs (Units.ext hh)
  · refine ⟨hM0, ha0, χ, hχ, ?_, ?_⟩
    · rw [hdt]
      exact SrcConj.att_conj ι g0 _ _ h (SrcConj.tw_conj W W' _ h hh) hatt
    · intro s hs
      have hd : s ∈ Dec (F := ℚ) A := Ine_le_Dec A hs
      rw [(hup s hd).2.2, hdt]
      exact hin ⟨s, hd⟩ hs

end
