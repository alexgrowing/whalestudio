import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.TubeSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureTranslateLevelRealBoxLeIndexMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivalenceGeneratedTorusRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLeHermitianRankAndHostDegreeEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeNegTransposeGramStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StrongApproximationDecomposition
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace MainStatements.Tam.T2

theorem meas_transl (D : D7) (V : HSp D) (θ : InfFam D) (A : Frames V) (rp : GA D V →* (∀ ρ, Upq V ρ))
    (hV : V.SigOK) (hA : IsFrames V A) (hrp : IsRealPart V θ A rp) (μ : Measure (GA D V)) [μ.IsMulLeftInvariant]
    (g : GA D V) (hg : g ∈ GfC V) (S : Set (GA D V)) (B : Set (∀ ρ, Upq V ρ)) :
    μ {y | g⁻¹ * y ∈ S ∧ rp y ∈ B} = μ {z | z ∈ S ∧ rp z ∈ B} := by
  have : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have : BorelSpace (GA D V) := ⟨rfl⟩
  have h1 : rp g = 1 := GlobalTheory.CovTop.VolBox.rp_eq_one V θ A rp hV hA hrp g hg
  rw [← measure_preimage_mul μ g⁻¹ {z | z ∈ S ∧ rp z ∈ B}]
  congr 1
  ext y
  show g⁻¹ * y ∈ S ∧ rp y ∈ B ↔ g⁻¹ * y ∈ S ∧ rp (g⁻¹ * y) ∈ B
  rw [map_mul rp, map_inv rp, h1, inv_one, one_mul]

theorem meas_low (D : D7) (V : HSp D) (θ : InfFam D) (A : Frames V) (rp : GA D V →* (∀ ρ, Upq V ρ))
    (hV : V.SigOK) (hA : IsFrames V A) (hrp : IsRealPart V θ A rp) (μ : Measure (GA D V)) [μ.IsMulLeftInvariant]
    (hidx : IdxSt) (M : ℕ) (hM : 1 ≤ M) (B : Set (∀ ρ, Upq V ρ)) :
    μ {h | h ∈ KM V 1 ∧ rp h ∈ B} ≤ ((M : ℝ≥0∞) ^ (2 * D.R.f * V.rank ^ 2)) * μ {h | h ∈ KM V M ∧ rp h ∈ B} := by
  classical
  have : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have : BorelSpace (GA D V) := ⟨rfl⟩
  have hfd : fdeg D.host.E = D.R.f := (GlobalTheory.T.two_le_hermitianRank_and_hostDegree_eq D).2
  obtain ⟨S, hScard, hS⟩ := hidx D.host.E V.rank M (-(V.gram)ᵀ) (GlobalTheory.Member.latC V) hM (GlobalTheory.T.selfDualLattice_neg_transpose_gram D V)
  set Q : Set (GA D V) := {h | h ∈ KM V M ∧ rp h ∈ B} with hQ
  let P : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E) → Set (GA D V) := fun s => {h | h ∈ KM V 1 ∧ rp h ∈ B ∧
    ∃ k, IsKM (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ) (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) M k ∧
      ((finHom V h).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) = s * k}
  have hcov : {h | h ∈ KM V 1 ∧ rp h ∈ B} ⊆ ⋃ s ∈ S, P s := by
    intro h ⟨h1, hB⟩
    obtain ⟨s, hsS, -, k, hk, e⟩ := hS _ h1
    exact Set.mem_iUnion₂.2 ⟨s, hsS, h1, hB, k, hk, e⟩
  have hP : ∀ s ∈ S, μ (P s) ≤ μ Q := by
    intro s hsS
    rcases (P s).eq_empty_or_nonempty with he | ⟨z, hz1, hzB, kz, hkz, hzs⟩
    · rw [he, measure_empty]; exact bot_le
    obtain ⟨w, hw, hwz⟩ := GlobalTheory.SplitDec.exists_finPart V z
    have hw1 : rp w = 1 := GlobalTheory.CovTop.VolBox.rp_eq_one V θ A rp hV hA hrp w hw
    have hsu : IsUnit s.det := by
      have hu : IsUnit ((finHom V z).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)).det := Matrix.isUnits_det_units _
      rw [hzs, Matrix.det_mul] at hu
      exact isUnit_of_mul_isUnit_left hu
    refine (measure_mono fun x hx => ?_).trans (measure_preimage_mul μ w⁻¹ Q).le
    obtain ⟨-, hxB, kx, hkx, hxs⟩ := hx
    refine ⟨?_, ?_⟩
    · show IsKM (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ) (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) M
        ((finHom V (w⁻¹ * x)).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E))
      have e1 : ((finHom V (w⁻¹ * x)).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) = kz⁻¹ * kx := by
        rw [map_mul, map_inv, ← hwz, Units.val_mul, Matrix.coe_units_inv, hzs, hxs, Matrix.mul_inv_rev,
          Matrix.mul_assoc, ← Matrix.mul_assoc s⁻¹, Matrix.nonsing_inv_mul _ hsu, Matrix.one_mul]
      rw [e1]
      exact isKM_mul (isKM_inv hkz) hkx
    · show rp (w⁻¹ * x) ∈ B
      rw [map_mul, map_inv, hw1, inv_one, one_mul]
      exact hxB
  calc μ {h | h ∈ KM V 1 ∧ rp h ∈ B} ≤ μ (⋃ s ∈ S, P s) := measure_mono hcov
    _ ≤ ∑ s ∈ S, μ (P s) := measure_biUnion_finset_le S P
    _ ≤ ∑ s ∈ S, μ Q := Finset.sum_le_sum hP
    _ = (S.card : ℝ≥0∞) * μ Q := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((M : ℝ≥0∞) ^ (2 * D.R.f * V.rank ^ 2)) * μ Q := by
      gcongr
      rw [← hfd]
      exact_mod_cast hScard

end MainStatements.Tam.T2
