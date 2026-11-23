import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.KeyBadSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LeWchartOne
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EqZeroOfSmulEqZero
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PolarizedDataFieldExtensionStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsNonzeroSectionPpDataStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionModuleDivisibleAtPrimeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionModuleBoundedDenominatorStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NonzeroSectionGenericFibreStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSectionNotInSetStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionModuleFieldExtMapStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrincipalExtensionProjectiveModuleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.KeyGen GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.KeyGen

theorem section_and_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L), 1 ≤ D.g → ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (_ : Algebra L L') (D' : PPData H L') (_ : D.Ext D') (s : Out.H0 D'.t.PP.L 1) (e : Fin D'.g → D'.B.carrier), KeyDeg.NonVan D'.t.G.hom s ∧ LinearIndependent (𝓞 L') e ∧ Submodule.span (𝓞 L') (Set.range e) = ⊤ := by
  intro E _ _ _ H L _ _ D _
  have : Smooth D.t.G.hom := D.t.semi.smooth
  have : GeometricallyConnected D.t.G.hom := D.t.semi.geomConnected
  have : QuasiCompact D.t.G.hom := D.t.semi.quasiCompact
  have hN : (LB.LinComb D.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ))).IsLB :=
    LB.isLB_linComb D.t.PP.isLB _ _
  obtain ⟨t, ht⟩ := GlobalTheory.T.exists_nonzero_section_pp_data E H L D
  obtain ⟨d₀, hd₀, hb⟩ := GlobalTheory.T.section_module_bounded_denominator (𝓞 L) D.t.G _ hN t ht
  let I : Ideal (𝓞 L) :=
    { carrier := {x | ∃ u : SecMod D.t.G.hom (LB.LinComb D.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ))), d₀ • u = x • t}
      add_mem' := by
        rintro a b ⟨u, hu⟩ ⟨v, hv⟩
        exact ⟨u + v, by rw [smul_add, hu, hv, add_smul]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c a ⟨u, hu⟩
        exact ⟨c • u, by rw [smul_comm, hu, smul_eq_mul, mul_smul]⟩ }
  have hI : I ≠ ⊥ := fun h0 => hd₀ (by
    have : d₀ ∈ I := ⟨t, rfl⟩
    rw [h0] at this
    simpa using this)
  obtain ⟨L', _, _, _, y, hy, hB⟩ := GlobalTheory.T.principal_extension_projective_module L D.B.carrier I hI
  obtain ⟨⟨D', m⟩⟩ := (GlobalTheory.T.polarized_data_field_extension E H L D L').1
  obtain ⟨hgg, -, io, -, hspan, -⟩ := (GlobalTheory.T.polarized_data_field_extension E H L D L').2 D' m
  obtain ⟨e, he1, he2⟩ := hB D'.B.carrier io hspan hgg
  obtain ⟨P, hP1, hP2⟩ := GlobalTheory.T.section_module_field_ext_map E H L D L' D' m
  have : Smooth D'.t.G.hom := D'.t.semi.smooth
  let φ := algebraMap (𝓞 L) (𝓞 L')
  let W : Ideal (𝓞 L') :=
    { carrier := {z | ∃ v : SecMod D'.t.G.hom (LB.LinComb D'.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ))), φ d₀ • v = z • P t}
      add_mem' := by
        rintro a b ⟨u, hu⟩ ⟨v, hv⟩
        exact ⟨u + v, by rw [smul_add, hu, hv, add_smul]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c a ⟨u, hu⟩
        exact ⟨c • u, by rw [smul_comm, hu, smul_eq_mul, mul_smul]⟩ }
  have hIW : I.map φ ≤ W := Ideal.map_le_iff_le_comap.2 fun x ⟨u, hu⟩ =>
    ⟨P u, by rw [← hP1, hu, hP1]⟩
  obtain ⟨s, hs⟩ : y ∈ W := hIW (hy ▸ Ideal.mem_span_singleton_self y)
  refine ⟨L', inferInstance, inferInstance, inferInstance, D', m, s, e, ?_, he1, he2⟩
  intro b'
  let b : Sp (𝓞 L) := spMap φ b'

  obtain ⟨x, u, hu, yy, hyy, hmem⟩ : ∃ (x : 𝓞 L) (u : SecMod D.t.G.hom (LB.LinComb D.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ)))),
      d₀ • u = x • t ∧ ∃ yy : D.t.G.left, D.t.G.hom yy = b ∧ yy ∈ Out.nonzeroLocus (M := LB.LinComb D.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ))) u := by
    by_cases hb0 : b.asIdeal = ⊥
    · exact ⟨d₀, t, rfl, GlobalTheory.T.nonzero_section_generic_fibre (𝓞 L) D.t.G _ hN t ht b hb0⟩
    · have hmax : b.asIdeal.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hb0 b.isPrime
      obtain ⟨x, u, hu, hV⟩ := GlobalTheory.T.exists_section_not_in_set (𝓞 L) _ (fun a m ha h => eq_zero_of_smul_eq_zero ha h) t ht d₀ hd₀ hb
        {u | ∀ yy : D.t.G.left, D.t.G.hom yy = b → yy ∉ Out.nonzeroLocus (M := LB.LinComb D.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ))) u}
        b.asIdeal hmax hb0 (fun u hu c e he h => GlobalTheory.T.section_module_divisible_at_prime (𝓞 L) _ D.t.G.hom _ b hmax u hu c e he h)
      simp only [Set.mem_setOf_eq, not_forall, not_not] at hV
      obtain ⟨yy, hyy, hmem⟩ := hV
      exact ⟨x, u, hu, yy, hyy, hmem⟩
  obtain ⟨y', hy', hm'⟩ := hP2 u b' yy hyy hmem
  refine ⟨y', hy', ?_⟩
  have hxI : φ x ∈ I.map φ := Ideal.mem_map_of_mem φ (show x ∈ I from ⟨u, hu⟩)
  rw [hy, Ideal.mem_span_singleton'] at hxI
  obtain ⟨w, hw⟩ := hxI
  have hφ : φ d₀ ≠ 0 := fun h0 => hd₀ (FaithfulSMul.algebraMap_injective (𝓞 L) (𝓞 L') (h0.trans (map_zero _).symm))
  have hPu : P u = w • s := by
    have : φ d₀ • (P u - w • s) = 0 := by
      rw [smul_sub, ← hP1, hu, hP1, smul_comm, hs, smul_smul, ← hw, sub_self]
    exact sub_eq_zero.1 (eq_zero_of_smul_eq_zero hφ this)
  rw [hPu] at hm'
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hm'
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨k, ?_⟩
  have : y' ∈ D'.t.G.left.basicOpen (constFn D'.t.G.hom _ w * LB.Sec.f (show SecMod D'.t.G.hom _ from s) k) := hk
  rw [Scheme.basicOpen_mul] at this
  exact this.2

end GlobalTheory.CompanionTheory.Ar.Sl.KeyGen
