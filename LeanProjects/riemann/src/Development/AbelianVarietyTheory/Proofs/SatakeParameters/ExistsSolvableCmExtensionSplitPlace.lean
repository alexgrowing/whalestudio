import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAbelianTotallyRealExtPrescribedCompletionStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCmFieldLiftDisjointOfRealSolvableStatement
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ArthurClozel
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
open scoped Pointwise

namespace GlobalTheory.AboveL

theorem mem_dec_congr {K K' Ω : Type} [Field K] [Field K'] [Field Ω] [Algebra K Ω] [Algebra K' Ω]
    (A : ValuationSubring Ω) (g : G K Ω) (g' : G K' Ω) (hg : ∀ x, g x = g' x) :
    g ∈ Dec (F := K) A ↔ g' ∈ Dec (F := K') A := by
  have key : ((g • A : ValuationSubring Ω) : Set Ω) = ((g' • A : ValuationSubring Ω) : Set Ω) := by
    rw [ValuationSubring.coe_pointwise_smul, ValuationSubring.coe_pointwise_smul]
    ext x
    simp only [Set.mem_smul_set, AlgEquiv.smul_def, hg]
  unfold Dec
  rw [ValuationSubring.decompositionSubgroup, ValuationSubring.decompositionSubgroup,
    MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
  constructor
  · intro h; apply SetLike.coe_injective; rw [← key]; exact congrArg _ h
  · intro h; apply SetLike.coe_injective; rw [key]; exact congrArg _ h

theorem exists_cm_solvable_split : ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w), ∀ N : Subgroup (G E Ω), IsOpen (N : Set (G E Ω)) → ∃ (M : Type) (_ : Field M) (_ : NumberField M) (_ : IsCMField M) (_ : Algebra M Ω) (_ : IsAlgClosure M Ω) (_ : Algebra E M) (_ : IsScalarTower E M Ω), SolvDisj M N ∧ (∀ g ∈ Dec (F := E) A, ∀ x : M, g (algebraMap M Ω x) = algebraMap M Ω x) ∧ ∀ g ∈ Dec (F := maximalRealSubfield M) A, ∀ x : M, g (algebraMap M Ω x) = algebraMap M Ω x := by
  intro Ω _ E _ _ _ _ _ A w h N hN
  let F := maximalRealSubfield E
  haveI : IsAlgClosure F Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.trans _ E Ω⟩

  obtain ⟨x₀, hx₀, hx₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
  let v : HeightOneSpectrum (𝓞 F) :=
    { asIdeal := w.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))
      isPrime := Ideal.IsPrime.comap _
      ne_bot := Ideal.comap_ne_bot_of_integral_mem hx₀0 hx₀ (Algebra.IsIntegral.isIntegral x₀) }
  have hv : IsPlaceOver A v := by
    intro x
    show _ ↔ algebraMap (𝓞 F) (𝓞 E) x ∈ w.asIdeal
    rw [← h]
    rfl
  obtain ⟨T, hvT, hlift⟩ := GlobalTheory.T.exists_cmField_lift_disjoint_of_real_solvable Ω E v N hN

  let φ := IsScalarTower.toAlgHom F E Ω
  let K : IntermediateField F Ω := φ.fieldRange
  haveI : FiniteDimensional F K := LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField φ).toLinearEquiv
  have hK : ∀ g : G F Ω, g ∈ K.fixingSubgroup ↔ ∀ x : E, g (algebraMap E Ω x) = algebraMap E Ω x := by
    intro g
    rw [IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro hg x; exact hg _ ⟨x, rfl⟩
    · rintro hg _ ⟨x, rfl⟩; exact hg x
  let V : Subgroup (Dec (F := F) A) := K.fixingSubgroup.subgroupOf (Dec (F := F) A)
  have hVo : IsOpen (V : Set (Dec (F := F) A)) := by
    rw [Subgroup.coe_subgroupOf]
    exact K.fixingSubgroup_isOpen.preimage continuous_subtype_val
  haveI : Fact (Nat.card (E ≃ₐ[F] E)).Prime :=
    ⟨by rw [IsGalois.card_aut_eq_finrank, Algebra.IsQuadraticExtension.finrank_eq_two F E]; exact Nat.prime_two⟩
  haveI : IsCyclic (E ≃ₐ[F] E) := isCyclic_of_prime_card rfl
  have habel : ∀ σ τ : E ≃ₐ[F] E, σ * τ = τ * σ := fun σ τ => (IsCyclic.commGroup).mul_comm σ τ
  have hcomm : commutator (Dec (F := F) A) ≤ V := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [commutatorElement_def, Subgroup.mem_subgroupOf, hK]
    intro x
    have h1 : AlgEquiv.restrictNormalHom (K₁ := Ω) E ((a * b * a⁻¹ * b⁻¹ : Dec (F := F) A) : G F Ω) = 1 := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
      rw [habel (AlgEquiv.restrictNormalHom E (a : G F Ω)) (AlgEquiv.restrictNormalHom E (b : G F Ω))]
      group
    have h2 := AlgEquiv.restrictNormal_commutes ((a * b * a⁻¹ * b⁻¹ : Dec (F := F) A) : G F Ω) E x
    have h3 : AlgEquiv.restrictNormal ((a * b * a⁻¹ * b⁻¹ : Dec (F := F) A) : G F Ω) E = 1 := h1
    rw [← h2, h3]
    rfl
  obtain ⟨F₁, hF₁fin, hF₁ab, hF₁real, hF₁dec, hF₁T⟩ := GlobalTheory.T.exists_abelian_totallyReal_ext_prescribedCompletion Ω F A v hv V hVo hcomm T hvT
  obtain ⟨M, iM, nM, cM, aM, acM, aEM, tM, hSD, hfix, hsub⟩ :=
    hlift F₁ hF₁fin inferInstance (isSolvable_of_comm fun a b => hF₁ab.toIsMulCommutative.is_comm.comm a b) hF₁real hF₁T
  have hkey : ∀ g : G F Ω, g ∈ Dec (F := F) A → (∀ z ∈ F₁, g z = z) →
      ∀ x : E, g (algebraMap E Ω x) = algebraMap E Ω x := by
    intro g hg hz
    exact (hK g).1 (Subgroup.mem_subgroupOf.1 ((hF₁dec ⟨g, hg⟩).1 ((IntermediateField.mem_fixingSubgroup_iff _ _).2 hz)))
  have hkey2 : ∀ g : G F Ω, g ∈ Dec (F := F) A → (∀ x : E, g (algebraMap E Ω x) = algebraMap E Ω x) →
      ∀ z ∈ F₁, g z = z := by
    intro g hg hE
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 ((hF₁dec ⟨g, hg⟩).2 (Subgroup.mem_subgroupOf.2 ((hK g).2 hE)))
  refine ⟨M, iM, nM, cM, aM, acM, aEM, tM, hSD, ?_, ?_⟩
  · intro g hg
    apply (hfix g).2
    let g' : G F Ω := g.restrictScalars F
    have hg' : g' ∈ Dec (F := F) A := (mem_dec_congr A g' g (fun _ => rfl)).2 hg
    exact hkey2 g' hg' (fun x => g.commutes x)
  · intro g hg
    have hfixP : ∀ x ∈ maximalRealSubfield M, g (algebraMap M Ω x) = algebraMap M Ω x :=
      fun x hx => g.commutes ⟨x, hx⟩
    have hF1 : ∀ z ∈ F₁, g z = z := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := hsub z hz
      exact hfixP x hx
    have hFfix : ∀ y : F, g.toRingEquiv (algebraMap F Ω y) = algebraMap F Ω y :=
      fun y => hF1 _ (F₁.algebraMap_mem y)
    let g' : G F Ω := AlgEquiv.ofRingEquiv (f := g.toRingEquiv) hFfix
    have hg' : g' ∈ Dec (F := F) A := (mem_dec_congr A g' g (fun _ => rfl)).2 hg
    have hE : ∀ x : E, g.toRingEquiv (algebraMap E Ω x) = algebraMap E Ω x := hkey g' hg' hF1
    let g'' : G E Ω := AlgEquiv.ofRingEquiv (f := g.toRingEquiv) hE
    exact (hfix g'').2 hF1

end GlobalTheory.AboveL
