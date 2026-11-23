import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinTypInvariantFormOfIsotIn
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryFiniteAdelesSplitPlaceDecomposition
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RowUnitProof

theorem exists_splitPlace_eq (D : D7) (w : PlE D.host) (hw : IsSplitPl D.host w) :
    ∃ s : SplitPlace D.host.E, s.w = w := by
  have hstar : ∀ x : D.host.E, D.host.conj x = IsCMField.complexConj D.host.E x := fun _ =>
    D.host.φ₀.injective (by
      rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply])
  obtain ⟨x, hx, hy⟩ := hw
  have hc : IsSplitPl D.host (GlobalTheory.SplitConjPlace.conjPlE w) := by
    refine ⟨IsCMField.ringOfIntegersComplexConj D.host.E x, ?_, fun y hy' => ?_⟩
    · rw [GlobalTheory.SplitConjPlace.mem_conjPlE, GlobalTheory.SplitConjPlace.cO_cO]; exact hx
    · rw [GlobalTheory.SplitConjPlace.mem_conjPlE]
      apply hy
      rw [hstar, IsCMField.coe_ringOfIntegersComplexConj, hy', hstar, IsCMField.coe_ringOfIntegersComplexConj,
        IsCMField.complexConj_apply_apply]
  obtain ⟨s, -, hs, -⟩ := GlobalTheory.SplitConjPlace.splitEx_all D _ hc
  refine ⟨s, HeightOneSpectrum.ext (Ideal.ext fun y => ?_)⟩
  have h1 := hs (IsCMField.ringOfIntegersComplexConj D.host.E y) y (by
    rw [hstar, IsCMField.coe_ringOfIntegersComplexConj, IsCMField.complexConj_apply_apply])
  rw [GlobalTheory.SplitConjPlace.mem_conjPlE, GlobalTheory.SplitConjPlace.cO_cO] at h1
  exact h1.symm

end GlobalTheory.RowUnitProof

namespace GlobalTheory.RowUnitProof

theorem rowUnit_of_isTrue : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D),
    (∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i))) → ∀ S : Reading P.T, IsTrue P S → RowUnit S := by
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
