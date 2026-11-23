import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousResQ
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicGLNormOneSplitStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarMeasureNormOneProductStatement
open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.CompanionTheory.CuspTransfer

noncomputable section
namespace GlobalTheory.CompanionTheory.CuspTransfer

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

variable (E a) in

abbrev splitFd : Set (GA E a) :=
  (fun p : normOneGL E a × ℝ => splitCentre E a p.2 * (p.1 : GA E a)) ''
    (RightCosetSpace.fundamentalDomain (rationalGLOne E a) ×ˢ Set.Ico (0 : ℝ) 1)

theorem coe_rationalGLOne_mem_latticeGL (δ : rationalGLOne E a) :
    ((δ : normOneGL E a) : GA E a) ∈ latticeGL E a := by
  obtain ⟨γ, hγ⟩ : ((δ : normOneGL E a) : GA E a) ∈ AdelicGLn.rationalGL E a := δ.2
  rw [← hγ]
  exact ratGL_mem_latticeGL γ

theorem splitCentre_mul_mul_swap (s t : ℝ) (d x : GA E a) :
    splitCentre E a s * splitCentre E a t * (d * x) = d * splitCentre E a s * (splitCentre E a t * x) := by
  simp only [mul_assoc]
  rw [← mul_assoc (splitCentre E a t) d x, splitCentre_comm t d, mul_assoc d, ← mul_assoc (splitCentre E a s) d,
    splitCentre_comm s d, mul_assoc]

theorem exists_lattice_smul_mem_splitFd (ha : 0 < a) (g : GA E a) :
    ∃ l : latticeGL E a, l • g ∈ splitFd E a := by
  obtain ⟨e, he⟩ := GlobalTheory.T.adelic_GL_norm_one_split E a ha
  obtain ⟨⟨x, t⟩, rfl⟩ := e.surjective g
  rw [he]
  obtain ⟨δ, hδ, -⟩ := RightCosetSpace.existsUnique_smul_mem_fundamentalDomain (rationalGLOne E a) x
  have hn : splitCentre E a ((-⌊t⌋ : ℤ) : ℝ) ∈ latticeGL E a := by
    rw [splitCentre_intCast]
    exact zpow_mem_latticeGL _
  refine ⟨⟨((δ : normOneGL E a) : GA E a) * splitCentre E a ((-⌊t⌋ : ℤ) : ℝ),
    mul_mem (coe_rationalGLOne_mem_latticeGL δ) hn⟩, ⟨δ • x, Int.fract t⟩,
    ⟨hδ, Int.fract_nonneg t, Int.fract_lt_one t⟩, ?_⟩
  change splitCentre E a (Int.fract t) * (((δ : normOneGL E a) : GA E a) * (x : GA E a)) =
    ((δ : normOneGL E a) : GA E a) * splitCentre E a ((-⌊t⌋ : ℤ) : ℝ) * (splitCentre E a t * (x : GA E a))
  have hf : Int.fract t = ((-⌊t⌋ : ℤ) : ℝ) + t := by
    rw [Int.fract]
    push_cast
    ring
  rw [hf, splitCentre_add, splitCentre_mul_mul_swap]

theorem eq_one_of_mul_mem_splitFd (ha : 0 < a) {l g : GA E a} (hl : l ∈ latticeGL E a) (hg : g ∈ splitFd E a)
    (h : l * g ∈ splitFd E a) : l = 1 := by
  obtain ⟨e, he⟩ := GlobalTheory.T.adelic_GL_norm_one_split E a ha
  obtain ⟨γ, m, rfl⟩ := mem_latticeGL_iff.1 hl
  obtain ⟨⟨x, s⟩, ⟨hx, hs⟩, rfl⟩ := hg
  obtain ⟨⟨y, u⟩, ⟨hy, hu⟩, hyu⟩ := h
  dsimp only at hx hs hy hu hyu
  have hγ : ratGL E a γ ∈ normOneGL E a := rationalGL_le_normOneGL ⟨γ, rfl⟩
  have key : e (y, u) = e (⟨ratGL E a γ, hγ⟩ * x, (m : ℝ) + s) := by
    rw [he, he, hyu, splitCentre_add, ← splitCentre_intCast]
    exact (splitCentre_mul_mul_swap (m : ℝ) s (ratGL E a γ) (x : GA E a)).symm
  obtain ⟨h1, h2⟩ := Prod.mk.inj (e.injective key)
  have hm : m = 0 := by
    have h3 : (m : ℝ) < 1 := by linarith [hs.1, hu.2]
    have h4 : (-1 : ℝ) < m := by linarith [hs.2, hu.1]
    have h5 : m < 1 := by exact_mod_cast h3
    have h6 : -1 < m := by exact_mod_cast h4
    omega
  subst hm
  let δ : rationalGLOne E a := ⟨⟨ratGL E a γ, hγ⟩, ⟨γ, rfl⟩⟩
  have h7 : δ = 1 := (RightCosetSpace.existsUnique_smul_mem_fundamentalDomain (rationalGLOne E a) x).unique
    (show δ • x ∈ _ from by
      change ((⟨ratGL E a γ, hγ⟩ : normOneGL E a) * x) ∈ _
      rw [← h1]
      exact hy) (by simpa using hx)
  have h8 : ratGL E a γ = 1 := congrArg (fun d : rationalGLOne E a => ((d : normOneGL E a) : GA E a)) h7
  rw [h8, zpow_zero, mul_one]

theorem measurableSet_splitFd (ha : 0 < a) : MeasurableSet (splitFd E a) := by
  obtain ⟨e, he⟩ := GlobalTheory.T.adelic_GL_norm_one_split E a ha
  have h : (fun p : normOneGL E a × ℝ => splitCentre E a p.2 * (p.1 : GA E a)) = e :=
    funext fun p => (he p.1 p.2).symm
  rw [splitFd, h]
  exact e.isClosedEmbedding.measurableEmbedding.measurableSet_image.2
    ((RightCosetSpace.measurableSet_fundamentalDomain _).prod measurableSet_Ico)

theorem isFundamentalDomain_splitFd : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 0 < a →
    ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure], IsFundamentalDomain (latticeGL E a)
      ((fun p : normOneGL E a × ℝ => splitCentre E a p.2 * (p.1 : GA E a)) ''
        (RightCosetSpace.fundamentalDomain (rationalGLOne E a) ×ˢ Set.Ico (0 : ℝ) 1)) μ := by
  intro E _ _ _ a ha μ _
  refine IsFundamentalDomain.mk' (measurableSet_splitFd ha).nullMeasurableSet fun g => ?_
  obtain ⟨l, hl⟩ := exists_lattice_smul_mem_splitFd ha g
  refine ⟨l, hl, fun l' hl' => ?_⟩
  have h1 : ((l' : GA E a) * (l : GA E a)⁻¹) * ((l : GA E a) * g) ∈ splitFd E a := by
    have e0 : (l' : GA E a) * (l : GA E a)⁻¹ * ((l : GA E a) * g) = (l' : GA E a) * g := by group
    rw [e0]
    exact hl'
  have h2 := eq_one_of_mul_mem_splitFd ha (mul_mem l'.2 (inv_mem l.2)) hl h1
  exact Subtype.ext (mul_inv_eq_one.1 h2)

end GlobalTheory.CompanionTheory.CuspTransfer
end
