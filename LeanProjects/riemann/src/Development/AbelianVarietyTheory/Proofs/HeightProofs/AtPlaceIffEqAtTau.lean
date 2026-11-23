import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactExponentialSurjective
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.IsotypicSignedParameters
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsBlockOrd
import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryExistsWithPrescribedParts
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.OrthonormalBaseFrameNeg

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.RealPar Matrix MeasureTheory
open scoped TensorProduct

namespace GlobalTheory.PointAtPlace

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice NumberField

variable {D : D7}

theorem tauE_injective : Function.Injective (tauE D) := fun _ _ h =>
  D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem tauE_cm (σ : D.host.E →+* ℂ) :
    (∃ ρ, tauE D ρ = σ) ↔ ¬ ∃ ρ, tauE D ρ = ComplexEmbedding.conjugate σ := by
  obtain ⟨g, rfl⟩ := (factEmb D.R D.host).1.2 σ
  have hc : ComplexEmbedding.conjugate (D.host.emb g) = D.host.emb (g * D.R.cc) := by
    rw [Formalism.L2.Geo.emb_mul_cc_comp]
    refine RingHom.ext fun x => ?_
    letI := D.host.cmStar
    haveI : IsCMField D.host.E := D.host.isCMField_hostE
    have h1 : star x = D.host.conj x := bridge_star_holds D.R D.host x
    have h2 : D.host.emb g (star x) = starRingEnd ℂ (D.host.emb g x) :=
      IsCMField.complexEmbedding_complexConj D.host.E (D.host.emb g) x
    rw [h1] at h2
    exact h2.symm
  have key : ∀ g', (∃ ρ, tauE D ρ = D.host.emb g') ↔ g' ∈ D.R.Psi := fun g' => by
    rw [← Formalism.L2.Geo.exists_tauEmb_iff D g']
    exact exists_congr fun ρ => eq_comm
  rw [hc, key, key]
  exact Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem g

theorem infMat_eq (V : HSp D) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (h : GA D V) :
    letI := D.host.cmStar
    infMat D.sp.cm.sig V.gram θ h = Formalism.L2.Pj.archM V θ h := rfl

theorem archM_mul (V : HSp D) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (a b : GA D V) :
    Formalism.L2.Pj.archM V θ (a * b) = Formalism.L2.Pj.archM V θ a * Formalism.L2.Pj.archM V θ b := by
  unfold Formalism.L2.Pj.archM
  rw [map_mul, Units.val_mul, Matrix.map_mul]

theorem archM_one (V : HSp D) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) :
    Formalism.L2.Pj.archM V θ 1 = 1 := by
  unfold Formalism.L2.Pj.archM
  rw [map_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem eq_one_of_mem (V : HSp D) (k : GA D V) (h1 : k ∈ GfC V) (h2 : k ∈ GinfC V) : k = 1 := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have a1 : (infHom V k).1 = (infHom V 1).1 := by rw [map_one]; exact congrArg Units.val h1
  have a2 : (finHom V k).1 = (finHom V 1).1 := by rw [map_one]; exact congrArg Units.val h2
  refine Subtype.ext (Units.ext (Matrix.ext fun a b => e.injective (Prod.ext ?_ ?_)))
  · rw [(he _).1, (he _).1]; exact congrFun (congrFun a1 a) b
  · rw [(he _).2, (he _).2]; exact congrFun (congrFun a2 a) b

theorem existsUnique_isAtTau (V : HSp D) (τ : D.what₂.Tau)
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : IsInfFam θ)
    (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.BasicNotions.TH.gramAt D V τ)) :
    ∃! h : GA D V, IsAtTau θ V τ g h := by
  classical
  let Ψ : Finset (D.host.E →+* ℂ) := Finset.univ.filter fun σ => ∃ ρ, tauE D ρ = σ
  have hmem : ∀ σ, σ ∈ Ψ ↔ ∃ ρ, tauE D ρ = σ := fun σ => by simp [Ψ]
  choose r hr using fun σ : Ψ => (hmem σ.1).1 σ.2
  have hsurj : ∀ ρ, r ⟨tauE D ρ, (hmem _).2 ⟨ρ, rfl⟩⟩ = ρ := fun ρ => tauE_injective (hr _)
  obtain ⟨h1, -, -, h2⟩ := (GlobalTheory.UnitaryGlue.adelic_glue D V).2 Ψ (fun σ => θ (r σ))
    (fun σ => by rw [hmem, hmem]; exact tauE_cm σ) (fun σ => by rw [← hr σ]; exact hθ _)
  obtain ⟨h, hh, hu⟩ := h2 (fun σ => if r σ = τ then g else 1) (fun σ => by
    by_cases c : r σ = τ
    · rw [if_pos c, ← hr σ, c]
      exact hg
    · rw [if_neg c, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.one_mul,
        Matrix.mul_one])
  have hu' : ∀ ρ, Formalism.L2.Pj.archM V (θ ρ) h = if ρ = τ then g else 1 := fun ρ => by
    have := hu ⟨tauE D ρ, (hmem _).2 ⟨ρ, rfl⟩⟩
    simp only [hsurj] at this
    exact this
  refine ⟨h, ⟨hh, (hu' τ).trans (if_pos rfl), fun ρ c => (hu' ρ).trans (if_neg c)⟩, fun h' hh' => ?_⟩
  have e : ∀ ρ, Formalism.L2.Pj.archM V (θ ρ) h' = Formalism.L2.Pj.archM V (θ ρ) h := fun ρ => by
    rw [hu']
    by_cases c : ρ = τ
    · rw [if_pos c, c]; exact hh'.2.1
    · rw [if_neg c]; exact hh'.2.2 ρ c
  refine mul_inv_eq_one.1 (eq_one_of_mem V _ (h1 _ fun σ => ?_) (mul_mem hh'.1 (inv_mem hh)))
  rw [archM_mul, e, ← archM_mul, mul_inv_cancel, archM_one]

end GlobalTheory.PointAtPlace
