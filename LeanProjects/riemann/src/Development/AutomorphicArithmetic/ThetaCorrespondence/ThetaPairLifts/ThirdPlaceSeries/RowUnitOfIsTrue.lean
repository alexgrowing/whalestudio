import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPlaceEq
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.RowUnitProof
end GlobalTheory.RowUnitProof
namespace GlobalTheory.RowUnitProof
theorem rowUnit_of_isTrue_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D),
    (∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i))) → ∀ S : Reading P.T, _root_.GlobalTheory.NPin.IsFaithfulReading P S → RowUnit S := by
  intro hL D P hX S hS i w hw σ hσ
  obtain ⟨X⟩ := hX i
  obtain ⟨s, rfl⟩ := exists_splitPlace_eq D w hw
  have hB00 : X.B 0 0 = 0 := by
    have h := X.lin 0 X.C.zero_mem 0 X.C.zero_mem 0 X.C.zero_mem 1
    rw [one_smul, add_zero, one_mul] at h
    linear_combination -h
  have hne : Formalism.IndefR.principalLevelFrame.isotIn (D := D) X.ρ X.C (P.rep σ) ≠ ⊥ := by
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hσ
    have hmem := (X.isot σ y).1 hy
    intro hbot
    rw [hbot, Submodule.mem_bot] at hmem
    apply hy0
    have h := X.φ_inner y y
    rw [hmem, hB00] at h
    exact inner_self_eq_zero.1 h
  obtain ⟨B', hlin, hherm, hpos, hinv⟩ := GlobalTheory.finTyp_invariant_form_of_isotIn D D.R.r X.A X.ρ X.C X.B X.lin X.herm
    X.pos X.stab X.inv (P.rep σ) hne
  obtain ⟨ι, T, -, -, hTinj, hTS, hTeq⟩ := hS.row i s hw σ hσ
  have hadd : ∀ x y z, B' x (y + z) = B' x y + B' x z := fun x y z => by
    simpa using hlin x y z 1
  have h0 : ∀ x, B' x 0 = 0 := fun x => by
    have h := hadd x 0 0
    rw [add_zero] at h
    linear_combination -h
  have hsmul : ∀ x (c : ℂ) y, B' x (c • y) = c * B' x y := fun x c y => by
    simpa [h0] using hlin x 0 y c
  have hadd' : ∀ x y z, B' (x + y) z = B' x z + B' y z := fun x y z => by
    rw [hherm, hadd, map_add, ← hherm, ← hherm]
  have hsmul' : ∀ (c : ℂ) x y, B' (c • x) y = starRingEnd ℂ c * B' x y := fun c x y => by
    rw [hherm, hsmul, map_mul, ← hherm]
  let Tm := LinearMap.codRestrict (P.rep σ).S T hTS
  have hTm : ∀ a, ((Tm a : (P.rep σ).S) : GAf D.host.E D.R.r → ℂ) = T a := fun _ => rfl
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun v u => B' (Tm u) (Tm v))
    (fun _ _ _ => by simp only [map_add, hadd]) (fun _ _ _ => by simp only [map_smul, hsmul, smul_eq_mul, RingHom.id_apply])
    (fun _ _ _ => by simp only [map_add, hadd']) (fun _ _ _ => by simp only [map_smul, hsmul', smul_eq_mul]), ?_, ?_, ?_⟩
  · intro v u
    simp only [LinearMap.mk₂'ₛₗ_apply]
    exact hherm _ _
  · intro v hv
    simp only [LinearMap.mk₂'ₛₗ_apply]
    refine hpos _ fun h => hv (hTinj ?_)
    rw [map_zero]
    exact congrArg Subtype.val h
  · intro g v u
    simp only [LinearMap.mk₂'ₛₗ_apply]
    obtain ⟨x, ⟨hx, hxg⟩, -⟩ := (GlobalTheory.SplitAdelic.main D.host.E D.R.r s).2.2
      (Matrix.GeneralLinearGroup.map ι.symm.toRingHom g)
    have hg : Matrix.GeneralLinearGroup.map ι.toRingHom (s.loc D.R.r x) = g := by
      rw [hxg]
      exact Units.ext (Matrix.ext fun a b => ι.apply_symm_apply _)
    have key : ∀ a, T (((S i s.w hw).row σ).π g a) = NG.rt D.host.E D.R.r x (T a) := fun a => by
      have := hTeq x hx a
      rw [hg] at this
      exact this
    exact hinv x (Tm u) (Tm v) _ _ (key u) (key v)
end GlobalTheory.RowUnitProof
end
end
