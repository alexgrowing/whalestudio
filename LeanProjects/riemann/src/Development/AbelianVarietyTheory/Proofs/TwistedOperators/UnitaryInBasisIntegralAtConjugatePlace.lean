import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCO
import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemGLintOfEntries
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlacesApart
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjPlaceIntegerMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PadOneMemSecondBlockTriangular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AuxiliaryVectorDecompositionEqZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

noncomputable section

namespace GlobalTheory.ConjPlaceUnitary

open GlobalTheory.AdIsom
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents (cjA inc)

variable {D : D7}

theorem entries_of_mem_GLint {L : Type} [Field L] {n : ℕ} (O : Subring L) {g : GL (Fin n) L}
    (hg : g ∈ Formalism.UG.GLint (Fin n) O) (i j : Fin n) : g.1 i j ∈ O ∧ (g⁻¹).1 i j ∈ O := by
  obtain ⟨h, rfl⟩ := hg
  exact ⟨(h.1 i j).2, by rw [← map_inv]; exact ((h⁻¹).1 i j).2⟩

theorem frame_change {n : ℕ} {β β' : GL (Fin n) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (h : IsFrame β Λ) (h' : IsFrame β' Λ) (i j : Fin n) : (β⁻¹ * β').1 i j ∈ OA D := by
  have h1 : β'.1 *ᵥ Pi.single j 1 ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := (h' _).2 fun k => by
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Pi.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have h2 := (h _).1 h1 i
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at h2
  exact h2

theorem dual_frame {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hβ : IsFrame β Λ) (hd : Formalism.L2.Herm.dualL D.sp.cm V Λ = Λ) :
    ∃ β' : GL (Fin V.rank) (Lev.EAf D), Formalism.UG.cT (cjA D) β.val * V.gram.map (inc D) * β'.val = 1 ∧
      (∀ i j, (β⁻¹ * β').1 i j ∈ OA D) ∧ (∀ i j, (β'⁻¹ * β).1 i j ∈ OA D) := by
  have hL := GlobalTheory.DiagLiftFix.isLattice_of_isFrame hβ
  have hΛ := GlobalTheory.StdFrames.eq_lat hβ hL
  obtain ⟨β', h1, -⟩ := exists_dual_frame V β
  have e : GlobalTheory.NormSum.AdLattice.lat β' = Λ := by rw [← dualL_lat_eq h1, ← hΛ, hd]
  have h' : IsFrame β' Λ := e ▸ GlobalTheory.StdFrames.isFrame_lat β'
  exact ⟨β', h1, frame_change hβ h', frame_change h' hβ⟩

end GlobalTheory.ConjPlaceUnitary

namespace GlobalTheory.ConjPlaceUnitary

open GlobalTheory.AdIsom
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents (cjA inc)

theorem conj_formula_gen {A : Type} [CommRing A] (σ : A →+* A) {n : ℕ}
    (J B Bi B' B'i Z Zi : Matrix (Fin n) (Fin n) A) (hB : B * Bi = 1) (hB' : B' * B'i = 1) (hZ : Z * Zi = 1)
    (h1 : Formalism.UG.cT σ B * J * B' = 1) (hz : Formalism.UG.cT σ Z * J * Z = J) :
    Bi * Z * B = Bi * B' * Formalism.UG.cT σ (Bi * Zi * B) * (B'i * B) := by
  have hcBi : Formalism.UG.cT σ Bi * Formalism.UG.cT σ B = 1 := by
    rw [← GlobalTheory.StdFrames.cT_mul', hB, GlobalTheory.StdFrames.cT_one']
  have hzi : Formalism.UG.cT σ Zi * Formalism.UG.cT σ Z = 1 := by
    rw [← GlobalTheory.StdFrames.cT_mul', hZ, GlobalTheory.StdFrames.cT_one']
  have hM : Formalism.UG.cT σ B * J = B'i := by
    calc Formalism.UG.cT σ B * J = Formalism.UG.cT σ B * J * (B' * B'i) := by rw [hB', Matrix.mul_one]
      _ = B'i := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have h1' : B' * (Formalism.UG.cT σ B * J) = 1 := by rw [hM, hB']
  have hz' : Formalism.UG.cT σ Zi * (Formalism.UG.cT σ Z * J * Z) = J * Z := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hzi, Matrix.one_mul]
  rw [GlobalTheory.StdFrames.cT_mul', GlobalTheory.StdFrames.cT_mul', ← hM]
  calc Bi * Z * B = Bi * (B' * (Formalism.UG.cT σ B * J)) * Z * B := by rw [h1', Matrix.mul_one]
    _ = Bi * B' * Formalism.UG.cT σ B * (Formalism.UG.cT σ Zi * (Formalism.UG.cT σ Z * J * Z)) * B := by
        rw [hz']
        simp only [Matrix.mul_assoc]
    _ = Bi * B' * Formalism.UG.cT σ B * (Formalism.UG.cT σ Zi * (Formalism.UG.cT σ Bi * Formalism.UG.cT σ B) * J) * B := by
        rw [hz, hcBi, Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]

variable {D : D7}

theorem conj_formula {n : ℕ} (J : Matrix (Fin n) (Fin n) (Lev.EAf D)) (β β' z : GL (Fin n) (Lev.EAf D))
    (h1 : Formalism.UG.cT (cjA D) β.val * J * β'.val = 1) (hz : Formalism.UG.cT (cjA D) z.val * J * z.val = J) :
    (β⁻¹ * z * β).val = (β⁻¹ * β').val * Formalism.UG.cT (cjA D) (β⁻¹ * z⁻¹ * β).val * (β'⁻¹ * β).val := by
  simp only [Units.val_mul]
  exact conj_formula_gen (cjA D) J β.val (β⁻¹).val β'.val (β'⁻¹).val z.val (z⁻¹).val
    (Units.mul_inv β) (Units.mul_inv β') (Units.mul_inv z) h1 hz

end GlobalTheory.ConjPlaceUnitary

namespace GlobalTheory.ConjPlaceUnitary

open GlobalTheory.AdIsom
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents (cjA inc)

variable {D : D7}

theorem cpt_conj_mem {n : ℕ} (w : Pl D.host.E) (P C M : Matrix (Fin n) (Fin n) (Lev.EAf D))
    (hP : ∀ i j, P i j ∈ OA D) (hM : ∀ i j, M i j ∈ OA D)
    (hC : ∀ i j, cpt w (C i j) ∈ w.adicCompletionIntegers D.host.E) (i j : Fin n) :
    cpt (Formalism.DivisionValues.conjPl w) ((P * Formalism.UG.cT (cjA D) C * M) i j) ∈
      (Formalism.DivisionValues.conjPl w).adicCompletionIntegers D.host.E := by
  rw [GlobalTheory.FunObj.conjPl_eq_cP]
  simp only [Matrix.mul_apply, map_sum, map_mul]
  refine sum_mem fun l _ => mul_mem (sum_mem fun k _ => mul_mem ?_ ?_) ?_
  · exact (mem_OA_iff _).1 (hP i k) _
  · exact ConjugatePlaceIntegrality.GlobalTheory.CompanionTheory.ConjPlaceInt.cpt_sg_mem_integers w (C l k) (hC l k)
  · exact (mem_OA_iff _).1 (hM l j) _

end GlobalTheory.ConjPlaceUnitary

namespace GlobalTheory.ConjPlaceUnitary

open GlobalTheory.AdIsom
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents (cjA inc)

theorem inBasis_conjPl_mem_KO : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsFrame β Λ → Formalism.L2.Herm.dualL D.sp.cm V Λ = Λ → ∀ x ∈ UA D.sp.cm V.gram, ∀ w : Pl D.host.E, inBasis rfl β w x ∈ GlobalTheory.SplitWeil.KO (Kw w) (Fin V.rank) → inBasis rfl β (Formalism.DivisionValues.conjPl w) x ∈ GlobalTheory.SplitWeil.KO (Kw (Formalism.DivisionValues.conjPl w)) (Fin V.rank) := by
  intro D V β Λ hβ hd x hx w hw
  obtain ⟨β', h1, hP, hM⟩ := dual_frame hβ hd
  have hu : ∀ z ∈ UA D.sp.cm V.gram, Formalism.UG.cT (cjA D) z.val * V.gram.map (inc D) * z.val = V.gram.map (inc D) :=
    fun z hz => hz
  rw [GlobalTheory.SmGL.SphCompletion.KO_completion] at hw ⊢
  have hC : ∀ a b, cpt w ((β⁻¹ * x * β).val a b) ∈ w.adicCompletionIntegers D.host.E := fun a b =>
    (entries_of_mem_GLint _ hw a b).1
  have hC' : ∀ a b, cpt w ((β⁻¹ * x⁻¹ * β).val a b) ∈ w.adicCompletionIntegers D.host.E := fun a b => by
    have := (entries_of_mem_GLint _ hw a b).2
    rw [← map_inv] at this
    exact this
  refine GlobalTheory.FunObj.mem_GLint_of_entries _ _ (fun i j => ?_) (fun i j => ?_)
  · rw [GlobalTheory.FunObj.inBasis_apply, conj_formula _ β β' x h1 (hu x hx)]
    exact cpt_conj_mem w _ _ _ hP hM hC' _ _
  · rw [← map_inv, GlobalTheory.FunObj.inBasis_apply]
    have e := conj_formula _ β β' x⁻¹ h1 (hu _ (inv_mem hx))
    rw [inv_inv] at e
    rw [e]
    exact cpt_conj_mem w _ _ _ hP hM hC _ _

end GlobalTheory.ConjPlaceUnitary
