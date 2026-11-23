import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsVectorFieldFrameSmoothCommGrpSchemeStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueModelHasJacobianOrderStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.JacobianOrderMonotoneSemistableModelStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianVarietyAutomorphismShiftsJacobianOrderStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ProdIrrAndWeakNeronStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.VectorFieldOrderAddOfProdStrictHenselianStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsModelMapDefinedWeakNeronFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelMapGenericallyOpenImmersionCalculusStatement

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem Model.twist_twist_symm {R K : Type} [CommRing R] [Field K] [Algebra R K] {A A' : Over (Sp K)}
    (M : Model R A) (f : A ≅ A') : (M.twist f).twist f.symm = M := by
  obtain ⟨Y, e, h₁, h₂, h₃⟩ := M
  simp [Model.twist]

theorem isIntegral_of_abelian {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] (hA : IsAbelianScheme A) :
    IsIntegral A.left := by
  have := hA.smooth
  have := hA.geomConnected
  exact GlobalTheory.isIntegral_of_smooth_of_geometricallyConnected A.hom

theorem exists_genIso_of_max_ord (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K]
    (hSH : SH R K) (π : R) (hπ : Irreducible π) (A : Over (Sp K)) [GrpObj A] (hA : IsAbelianScheme A)
    (I : Type) [Fintype I] [DecidableEq I] (D : I → VF A) (hD : IsFrame D)
    (J : Type) (M : J → Model R A) (hI : ∀ j, (M j).Irr) (hW : WeakNeron M) (o : J → ℤ)
    (ho : ∀ j, HasOrd (M j) D π (o j)) (ρ : ℤ) (hρ : ∀ j, o j ≤ ρ) (f : A ≅ A) (i : J) (hi : o i = ρ) :
    ∃ i', o i' = ρ ∧ GenIso (M i) (M i') f.hom := by
  have hint := isIntegral_of_abelian A hA
  obtain ⟨-, -, h3, -⟩ := GlobalTheory.T.modelMapGenericallyOpenImmersion_calculus R K hSH
  obtain ⟨hdvr, -, -, hfr⟩ := hSH
  have bound : ∀ (N : Model R A) (m : ℤ), N.Irr → HasOrd N D π m →
      m ≤ ρ ∧ (m = ρ → ∃ i', o i' = ρ ∧ GenIso N (M i') (𝟙 A)) := by
    intro N m hN hm
    obtain ⟨j, hj⟩ := GlobalTheory.T.exists_modelMapDefined_weakNeronFamily R K A J M hW N hN
    obtain ⟨h₁, h₂⟩ := GlobalTheory.T.jacobian_order_monotone_semistableModel R K π hπ A I D hD N (M j) m (o j) hN (hI j) hm (ho j) hj
    have := hρ j
    exact ⟨h₁.trans this, fun e => ⟨j, by omega, h₂ (by omega)⟩⟩
  obtain ⟨c, hc⟩ := GlobalTheory.T.abelianVariety_automorphism_shifts_jacobianOrder R K π hπ A hA I D hD f
  obtain ⟨c', hc'⟩ := GlobalTheory.T.abelianVariety_automorphism_shifts_jacobianOrder R K π hπ A hA I D hD f.symm
  have t₁ := hc _ _ (ho i)
  have t₂ := hc' _ _ (ho i)
  have t₃ := hc' _ _ t₁
  rw [Model.twist_twist_symm] at t₃
  have e₃ := (GlobalTheory.T.existsUnique_modelHasJacobianOrder R K π hπ A I D hD (M i) (hI i)).unique t₃ (ho i)
  have i₁ : ((M i).twist f).Irr := hI i
  have i₂ : ((M i).twist f.symm).Irr := hI i
  obtain ⟨b₁, b₁'⟩ := bound _ _ i₁ t₁
  obtain ⟨b₂, -⟩ := bound _ _ i₂ t₂
  obtain ⟨i', hi', hg⟩ := b₁' (by omega)
  exact ⟨i', hi', (h3 A A (M i) (M i') f).2.1.2 hg⟩

theorem WeakNeron.nonempty {R K : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K]
    (hSH : SH R K) {A : Over (Sp K)} [GrpObj A] {J : Type} {M : J → Model R A} (hW : WeakNeron M) :
    Nonempty J := by
  obtain ⟨hdvr, -, -, hfr⟩ := hSH
  obtain ⟨i, -⟩ := hW R K (by simp) (η[A]).left (by
    rw [← Category.assoc, Over.w]
    simp)
  exact ⟨i⟩

theorem exists_permuted_members : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (n : ℕ) (M : Fin n → Model R A), (∀ i, (M i).Irr) → WeakNeron M → ∃ S : Finset (Fin n), S.Nonempty ∧ (∀ (f : A ≅ A), ∀ i ∈ S, ∃ i' ∈ S, GenIso (M i) (M i') f.hom) ∧ ∀ (Θ : A ⊗ A ≅ A ⊗ A), ∀ i ∈ S, ∀ j ∈ S, ∃ i' ∈ S, ∃ j' ∈ S, GenIso ((M i).prod (M j)) ((M i').prod (M j')) Θ.hom := by
  intro R K _ _ _ _ _ hSH A _ _ hA n M hI hW
  have hne := hW.nonempty hSH
  have hdvr := hSH.1
  have hfr := hSH.2.2.2
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim K A hA
  obtain ⟨D, hD⟩ := GlobalTheory.T.exists_vectorFieldFrame_smooth_commGrpScheme K A g hg
  choose o ho using fun i => (GlobalTheory.T.existsUnique_modelHasJacobianOrder R K π hπ A (Fin g) D hD (M i) (hI i)).exists
  obtain ⟨i₀, hi₀⟩ := Finite.exists_max o
  refine ⟨Finset.univ.filter fun i => o i = o i₀, ⟨i₀, by simp⟩, ?_, ?_⟩
  · intro f i hi
    obtain ⟨i', hi', h⟩ := exists_genIso_of_max_ord R K hSH π hπ A hA _ D hD _ M hI hW o ho (o i₀) hi₀ f i
      (by simpa using hi)
    exact ⟨i', by simpa using hi', h⟩
  · intro Θ i hi j hj
    have hi : o i = o i₀ := by simpa using hi
    have hj : o j = o i₀ := by simpa using hj
    obtain ⟨D₂, hD₂, hp⟩ := GlobalTheory.T.vectorFieldOrder_add_of_prod_strictHenselian R K hSH π hπ A A _ _ D D hD hD
    obtain ⟨p₁, p₂⟩ := GlobalTheory.T.prod_irr_and_weakNeron' R K hSH A A
    obtain ⟨⟨i', j'⟩, h', h⟩ := exists_genIso_of_max_ord R K hSH π hπ (A ⊗ A)
      (AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA) _ D₂ hD₂ (Fin n × Fin n)
      (fun p => (M p.1).prod (M p.2)) (fun p => p₁ _ _ (hI _) (hI _)) (p₂ _ _ M M hW hW)
      (fun p => o p.1 + o p.2) (fun p => hp _ _ _ _ (hI _) (hI _) (ho _) (ho _)) (o i₀ + o i₀)
      (fun p => add_le_add (hi₀ _) (hi₀ _)) Θ (i, j) (by simp [hi, hj])
    have a₁ := hi₀ i'
    have a₂ := hi₀ j'
    have h' : o i' + o j' = o i₀ + o i₀ := h'
    exact ⟨i', by simp; omega, j', by simp; omega, h⟩

end GlobalTheory.SS
