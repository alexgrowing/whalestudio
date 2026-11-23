import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoefficientRingFiniteExtensionPadicStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompactGroupRepDefinedOverFiniteExtension
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ImportsExtra
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUpperTriangularConjIntegralCompactStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnramifiedOfLevelAwayInertiaCharactersStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterPowPredEqOneOfKillsPrimeRootsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IrreducibleRestrictionOfIsoStatement

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.NfEx

theorem up2 {k : Type} [Field k] (X Y Z : Matrix (Fin 2) (Fin 2) k) (hX : X 1 0 = 0) (hY : Y 1 0 = 0) (hZ : Z 1 0 = 0) :
    (X * Y * Z) 1 0 = 0 ∧ (X * Y * Z) 0 0 = X 0 0 * Y 0 0 * Z 0 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two, hX, hY, hZ]

theorem inv_up {k : Type} [Field k] (B : GL (Fin 2) k) (hB : (B : Matrix (Fin 2) (Fin 2) k) 1 0 = 0) :
    ((B⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) 1 0 = 0 ∧
    (B : Matrix (Fin 2) (Fin 2) k) 0 0 * ((B⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) 0 0 = 1 := by
  have key : ∀ i j, ∑ x, (B : Matrix (Fin 2) (Fin 2) k) i x * ((B⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) x j =
      (1 : Matrix (Fin 2) (Fin 2) k) i j := fun i j => by
    rw [← Matrix.mul_apply, B.mul_inv]
  have e10 := key 1 0
  have e11 := key 1 1
  have e00 := key 0 0
  rw [Fin.sum_univ_two, hB, zero_mul, zero_add] at e10 e11
  rw [Fin.sum_univ_two] at e00
  rw [Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at e10
  rw [Matrix.one_apply_eq] at e11 e00
  have hN : ((B⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) 1 0 = 0 := by
    rcases mul_eq_zero.1 e10 with h | h
    · rw [h, zero_mul] at e11
      exact absurd e11 zero_ne_one
    · exact h
  refine ⟨hN, ?_⟩
  rw [hN, mul_zero, add_zero] at e00
  exact e00

theorem exists_nf : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (W : R2 Ω l), l ≠ 2 → 1 ≤ e → admitted ι e W → (∀ (A : ValuationSubring Ω) (κ : Fin 2 → ↥(Dec (F := ℚ) A) →* (Qbar l)ˣ), OverL l A → IsFlagOn W (Dec (F := ℚ) A) κ → ∃ s : ↥(Dec (F := ℚ) A), κ 0 s ≠ cycBar ℚ Ω l s) → ∃ (S : Finset Pl) (A : ValuationSubring Ω) (W' : R2 Ω l), RepIso W W' ∧ Nf e S A W' := by
  intro l _ Ω _ _ _ ι e W hl he hW hne
  obtain ⟨A, χ, κ, hA, hχ, hfl, -, hIne⟩ := hW.flag
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
  have hW' : ∀ s, W' s = B * r s * B⁻¹ := fun s => by
    show h * W s * h⁻¹ = B * (g * W s * g⁻¹) * B⁻¹
    simp only [h, mul_inv_rev]; group
  have hiso : RepIso W W' := ⟨h, fun s => rfl⟩
  have hdt : dt W' = dt W := by
    ext s
    rw [GlobalTheory.Ord2.TwDet.dt_coe, GlobalTheory.Ord2.TwDet.dt_conj W h s]
    rfl
  have hker : ∀ s, W' s = 1 ↔ W s = 1 := fun s => by
    show h * W s * h⁻¹ = 1 ↔ W s = 1
    constructor
    · intro hh; rw [mul_inv_eq_one, mul_eq_left] at hh; exact hh
    · intro hh; rw [hh]; simp
  have hinv := inv_up B hB10
  have hup : ∀ (s : G ℚ Ω) (hs : s ∈ Dec (F := ℚ) A), mat W' s 1 0 = 0 ∧ mat W' s 0 0 = (κ 0 ⟨s, hs⟩ : Qbar l) := by
    intro s hs
    have h1 := (hg ⟨s, hs⟩).1 1 0 (by decide)
    have h2 := (hg ⟨s, hs⟩).2 0
    have := up2 (B : Matrix (Fin 2) (Fin 2) (Qbar l)) ((r s : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l))
      ((B⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) hB10 h1 hinv.1
    have e1 : mat W' s = (B : Matrix (Fin 2) (Fin 2) (Qbar l)) * ((r s : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) * ((B⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) := by
      simp only [mat, hW', Units.val_mul]
    refine ⟨by rw [e1]; exact this.1, ?_⟩
    rw [e1, this.2, ← h2]
    change _ = ((r s : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) 0 0
    calc _ = (B : Matrix (Fin 2) (Fin 2) (Qbar l)) 0 0 * ((B⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) 0 0 * ((r s : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) 0 0 := by ring
      _ = _ := by rw [hinv.2, one_mul]
  refine ⟨S, A, W', hiso, ?_⟩
  refine
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
    · have hd : s ∈ Dec (F := ℚ) A := Ine_le_Dec A hs
      rw [(hup s hd).2, (hIne ⟨s, hd⟩ hs).1]
      have hχ1 := GlobalTheory.T.character_pow_pred_eq_one_of_killsPrimeRoots Ω l _ χ s hχ
      simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, zpow_natCast, mul_pow, eps]
      rw [← Units.val_pow_eq_pow_val (χ s), hχ1, Units.val_one, mul_one, Units.val_pow_eq_pow_val, ← pow_mul]
  · obtain ⟨s, hs⟩ := hne A κ hA ⟨g, hg⟩
    refine ⟨s, s.2, ?_⟩
    rw [(hup s s.2).2]
    intro hh
    exact hs (Units.ext hh)

end GlobalTheory.NfEx

end
