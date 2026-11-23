import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalMod
import GroundTheory.PAdicHodge.ExistsGalFixCyclotomicLayerCycloCharNeOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaloisActionPeriodProductStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PeriodProductFiltrationLevelsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeTateCharacterWeightStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SenUnramifiedCharacterPeriodStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SenPeriodFiniteExtensionStatement
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer

theorem exact_degrees_of_product : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ),
    (∀ (g : GQ l) (hg : g ∈ GK K), (∀ u ∈ GroundTheory.PAdicHodge.unramifiedClosure l, g u = u) →
      Algebra.norm ℚ_[l] ((χ ⟨g, hg⟩ : (↥K.1)ˣ) : ↥K.1) =
        (((GroundTheory.PAdicHodge.cycloChar ⊥ (Formalism.Per6.toBot g) : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l])) →
    ∀ t : (↥K.1 →ₐ[ℚ_[l]] Om l) → Formalism.Per6.BdRp l, (∀ μ, PrePer K χ μ (t μ)) →
      ∀ μ, (μ = K.1.val → t μ ∉ FB l 2) ∧ (μ ≠ K.1.val → t μ ∉ FB l 1) := by
  intro l _ K χ hN t ht
  haveI hfK : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  obtain ⟨L, hLdef⟩ : ∃ L : IntermediateField ℚ_[l] (Om l),
      L = IntermediateField.normalClosure ℚ_[l] ↥K.1 (Om l) := ⟨_, rfl⟩
  haveI : FiniteDimensional ℚ_[l] ↥L := by
    subst hLdef
    infer_instance
  have hμL : ∀ (μ : ↥K.1 →ₐ[ℚ_[l]] Om l) (x : ↥K.1), μ x ∈ L := fun μ x => by
    subst hLdef
    exact μ.fieldRange_le_normalClosure ⟨x, rfl⟩
  have hKL : ∀ x ∈ K.1, x ∈ L := fun x hx => hμL K.1.val ⟨x, hx⟩
  let res : Gal(Om l/↥L) → GQ l := fun σ => σ.restrictScalars ℚ_[l]
  have hresv : ∀ (σ : Gal(Om l/↥L)) (y : ↥L), res σ y = y := fun σ y => σ.commutes y
  have hres : ∀ σ, res σ ∈ GK K := fun σ =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => hresv σ ⟨x, hKL x hx⟩
  obtain ⟨s, hs⟩ : ∃ s : Finset (↥K.1 →ₐ[ℚ_[l]] Om l), ∀ μ, μ ∈ s :=
    ⟨(Set.toFinite (Set.univ : Set (↥K.1 →ₐ[ℚ_[l]] Om l))).toFinset, fun μ => by simp⟩
  have hT0 : (∏ μ ∈ s, t μ) ≠ 0 := Finset.prod_ne_zero_iff.2 fun μ _ => (ht μ).1
  have htirr : Irreducible (GroundTheory.PAdicHodge.tBdR l) :=
    IsDiscreteValuationRing.irreducible_iff_uniformizer _ |>.2
      (GroundTheory.PAdicHodge.maximalIdeal_eq_span_fontaineT GroundTheory.PAdicHodge.untilt_epsilon
        GroundTheory.PAdicHodge.untilt_frobeniusEquiv_symm_epsilon_ne_one)
  obtain ⟨n, u, hTu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hT0 htirr
  have hTu' : ∏ μ ∈ s, t μ = GroundTheory.PAdicHodge.tBdR l ^ n * (u : Formalism.Per6.BdRp l) := by
    rw [hTu, mul_comm]
  have hcyc : ∀ σ : Gal(Om l/↥L),
      (((GroundTheory.PAdicHodge.cycloChar ⊥ (Formalism.Per6.toBot (res σ)) : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) =
        (((GroundTheory.PAdicHodge.cycloChar L σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) := fun σ => by
    have h1 := GroundTheory.PAdicHodge.gal_smul_fontaineT σ (GroundTheory.PAdicHodge.untilt_epsilon (p := l))
    have h2 := GroundTheory.PAdicHodge.gal_smul_fontaineT (Formalism.Per6.toBot (res σ))
      (GroundTheory.PAdicHodge.untilt_epsilon (p := l))
    have h3 := h2.symm.trans h1
    exact (algebraMap ℚ_[l] (Formalism.Per6.BdRp l)).injective (mul_right_cancel₀ htirr.ne_zero h3)
  have hn : n = 1 := GlobalTheory.T.hodge_tate_character_weight L (GlobalTheory.T.sen_period_finite_extension GlobalTheory.T.sen_unramified_character_period L) u n
    (fun σ => Algebra.norm ℚ_[l] ((χ ⟨res σ, hres σ⟩ : (↥K.1)ˣ) : ↥K.1))
    (fun σ => by
      rw [← hTu']
      exact GlobalTheory.T.galois_action_period_product K χ t s hs ht (res σ) (hres σ) fun μ x => hresv σ ⟨μ x, hμL μ x⟩)
    (fun σ hσ => (hN (res σ) (hres σ) hσ).trans (hcyc σ))
  subst hn
  intro μ
  exact GlobalTheory.T.period_product_filtration_levels s t K.1.val (hs _) u (by rw [hTu', pow_one]) ((ht _).2.2 rfl) μ (hs μ)

end GlobalTheory.CompanionTheory.LTPer
