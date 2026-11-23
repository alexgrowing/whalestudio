import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ArthurClozel
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAbelianTotallyRealExtPrescribedCompletionStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCmFieldLiftDisjointOfRealSolvableStatement
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.PrimesOverExistence.Places
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.AboveL.DecRes

variable {Ω F E : Type} [Field Ω] [Field F] [Field E] [Algebra F E] [Algebra F Ω] [Algebra E Ω] [IsScalarTower F E Ω]
  (A : ValuationSubring Ω)

def lift (h : G F Ω) (hh : ∀ x : E, h (algebraMap E Ω x) = algebraMap E Ω x) : G E Ω :=
  { (h : Ω ≃+* Ω) with commutes' := hh }

def resHom : Dec (F := E) A →* Dec (F := F) A where
  toFun g := ⟨AlgEquiv.restrictScalarsHom F (g : G E Ω), g.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem resHom_injective : Function.Injective (resHom (F := F) (E := E) A) := by
  intro g g' hgg
  apply Subtype.ext
  ext z
  have := congrArg (fun k : Dec (F := F) A => (k : G F Ω) z) hgg
  exact this

theorem mem_map_iff (V : Subgroup (Dec (F := E) A)) (g : Dec (F := E) A) :
    resHom (F := F) A g ∈ V.map (resHom (F := F) (E := E) A) ↔ g ∈ V :=
  (Subgroup.mem_map_iff_mem (resHom_injective (E := E) A))

variable (hfix : ∀ g ∈ Dec (F := F) A, ∀ x : E, g (algebraMap E Ω x) = algebraMap E Ω x)
include hfix

theorem resHom_surjective : Function.Surjective (resHom (F := F) (E := E) A) := by
  intro k
  exact ⟨⟨lift (k : G F Ω) (hfix _ k.2), k.2⟩, Subtype.ext (by ext z; rfl)⟩

theorem isOpen_map [FiniteDimensional F E] (V : Subgroup (Dec (F := E) A)) (hV : IsOpen (V : Set (Dec (F := E) A))) :
    IsOpen ((V.map (resHom (F := F) (E := E) A)) : Set (Dec (F := F) A)) := by
  obtain ⟨U, hU, hUV⟩ := isOpen_induced_iff.mp hV
  have h1 : (1 : Dec (F := E) A) ∈ V := V.one_mem
  have hU1 : (1 : G E Ω) ∈ U := by
    have : (1 : Dec (F := E) A) ∈ Subtype.val ⁻¹' U := by rw [hUV]; exact h1
    exact this
  obtain ⟨K, hK, hKU⟩ := (krullTopology_mem_nhds_one_iff E Ω U).mp (hU.mem_nhds hU1)
  haveI := hK
  haveI : FiniteDimensional F (K.restrictScalars F) :=
    (Module.Finite.trans E K : Module.Finite F K)
  apply Subgroup.isOpen_of_mem_nhds _ (g := 1)
  have hO : IsOpen (Subtype.val ⁻¹' ((K.restrictScalars F).fixingSubgroup : Set (G F Ω)) : Set (Dec (F := F) A)) :=
    (IntermediateField.fixingSubgroup_isOpen (K.restrictScalars F)).preimage continuous_subtype_val
  refine Filter.mem_of_superset (hO.mem_nhds ((K.restrictScalars F).fixingSubgroup.one_mem)) ?_
  intro k hk
  obtain ⟨g, rfl⟩ := resHom_surjective (E := E) A hfix k
  refine ⟨g, ?_, rfl⟩
  have hgU : (g : G E Ω) ∈ U := by
    apply hKU
    intro z
    exact hk ⟨z.1, z.2⟩
  have : g ∈ Subtype.val ⁻¹' U := hgU
  rw [hUV] at this
  exact this

theorem commutator_le_map (V : Subgroup (Dec (F := E) A)) (hc : commutator (Dec (F := E) A) ≤ V) :
    commutator (Dec (F := F) A) ≤ V.map (resHom (F := F) (E := E) A) := by
  have hs := resHom_surjective (E := E) A hfix
  rw [commutator_def, ← Subgroup.map_top_of_surjective _ hs, ← Subgroup.map_commutator]
  exact Subgroup.map_mono (by rw [← commutator_def]; exact hc)

end GlobalTheory.AboveL.DecRes

namespace GlobalTheory.AboveL

open GlobalTheory.AboveL.DecRes in

theorem exists_cm_solvDisj_dec_eq : ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w), (∀ g ∈ Dec (F := maximalRealSubfield E) A, ∀ x : E, g (algebraMap E Ω x) = algebraMap E Ω x) → ∀ V : Subgroup (Dec (F := E) A), IsOpen (V : Set (Dec (F := E) A)) → commutator (Dec (F := E) A) ≤ V → ∀ N : Subgroup (G E Ω), IsOpen (N : Set (G E Ω)) → ∃ (M : Type) (_ : Field M) (_ : NumberField M) (_ : IsCMField M) (_ : Algebra M Ω) (_ : IsAlgClosure M Ω) (_ : Algebra E M) (_ : IsScalarTower E M Ω), SolvDisj M N ∧ ∀ g : Dec (F := E) A, (∀ x : M, (g : G E Ω) (algebraMap M Ω x) = algebraMap M Ω x) ↔ g ∈ V := by
  intro Ω _ E _ _ _ _ _ A w h hfix V hVo hVc N hNo
  haveI : IsAlgClosure (maximalRealSubfield E) Ω :=
    ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.trans _ E Ω⟩
  obtain ⟨n, hn, hnv⟩ := (Formalism.MainNotions.V.Pf.ShaCmp.exists_over_iff (K := E) A).mp ⟨w, h⟩
  obtain ⟨v, hv⟩ := (Formalism.MainNotions.V.Pf.ShaCmp.exists_over_iff (K := maximalRealSubfield E) A).mpr ⟨n, hn, hnv⟩
  obtain ⟨T, hvT, hT⟩ := GlobalTheory.T.exists_cmField_lift_disjoint_of_real_solvable Ω E v N hNo
  obtain ⟨F₁, hfin, hab, hreal, hdecF, hsplit⟩ := GlobalTheory.T.exists_abelian_totallyReal_ext_prescribedCompletion Ω (maximalRealSubfield E) A v hv
    (V.map (resHom (F := maximalRealSubfield E) (E := E) A)) (isOpen_map A hfix V hVo)
    (commutator_le_map A hfix V hVc) T hvT
  have hsolv : IsSolvable (F₁ ≃ₐ[maximalRealSubfield E] F₁) :=
    isSolvable_of_comm fun a b => hab.toIsMulCommutative.is_comm.comm a b
  obtain ⟨M, i1, i2, i3, i4, i5, i6, i7, hSD, hM, -⟩ :=
    hT F₁ hfin hab.toIsGalois hsolv hreal hsplit
  refine ⟨M, i1, i2, i3, i4, i5, i6, i7, hSD, fun g => ?_⟩
  rw [hM (g : G E Ω), ← mem_map_iff (F := maximalRealSubfield E) A V g, ← hdecF, IntermediateField.mem_fixingSubgroup_iff]
  rfl

end GlobalTheory.AboveL
