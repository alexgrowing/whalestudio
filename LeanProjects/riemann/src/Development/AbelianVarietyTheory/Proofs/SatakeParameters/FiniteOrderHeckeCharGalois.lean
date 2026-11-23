import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlobalArtinReciprocityHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ArthurClozel
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalGLLocalComponentsEventuallySatake
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSatakeOfIsLocComp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspRepSatakeParametersUniqueStatement
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.HeckeToGal

theorem exists_galChar_of_finite_order : ∀ (Ω : Type) [Field Ω] (K : Type) [Field K] [NumberField K] [Algebra K Ω]
    [IsAlgClosure K Ω] (η : HChar K) (n : ℕ), 0 < n → η ^ n = 1 → ∃ χ : G K Ω →* ℂˣ,
      IsOpen (χ.ker : Set (G K Ω)) ∧ (χ = 1 → η = 1) ∧
      ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ∀ (A : ValuationSubring Ω) (σ : G K Ω),
        IsPlaceOver A v → IsFrob A (normV v) σ → χ σ = η.val v := by
  intro Ω _ K _ _ _ _ η n hn hη
  obtain ⟨art, ha⟩ := GlobalTheory.globalArtinReciprocity_holds K Ω
  have hηn : ∀ x, η.1 x ^ n = 1 := fun x => congrArg (fun ξ : HChar K => ξ.1 x) hη
  have hopen : IsOpen (η.1.ker : Set (Ideles K)) := isOpen_ker_of_pow η.1 η.2.1 hn hηn
  have hinf : infConn K ≤ η.1.ker := by
    rintro _ ⟨y, hy, rfl⟩
    let φ : (InfiniteAdeleRing K)ˣ →* ℂˣ :=
      η.1.comp (Units.map (MonoidHom.inl (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)))
    have hc : Continuous fun z : InfiniteAdeleRing K => (z, (1 : FiniteAdeleRing (𝓞 K) K)) :=
      continuous_id.prodMk continuous_const
    have hφ : Continuous φ := η.2.1.comp (Continuous.units_map _ hc)
    have hop : IsOpen (φ.ker : Set (InfiniteAdeleRing K)ˣ) := isOpen_ker_of_pow φ hφ hn (fun x => hηn _)
    have hcl : IsClopen (φ.ker : Set (InfiniteAdeleRing K)ˣ) := ⟨Subgroup.isClosed_of_isOpen _ hop, hop⟩
    exact hcl.connectedComponent_subset (one_mem φ.ker) hy
  have hker : art.ker ≤ η.1.ker := by
    rw [ha.ker]
    refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ hinf) (Subgroup.isClosed_of_isOpen _ hopen)
    rintro _ ⟨k, rfl⟩
    exact MonoidHom.mem_ker.mpr (η.2.2 k)
  have hs : Function.Surjective art := ha.quot.surjective
  let ηb : Gab K Ω →* ℂˣ :=
    art.liftOfRightInverse (Function.surjInv hs) (Function.rightInverse_surjInv hs) ⟨η.1, hker⟩
  have hηb : ∀ x, ηb (art x) = η.1 x := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply art (Function.surjInv hs) (Function.rightInverse_surjInv hs) ⟨η.1, hker⟩ x
  have hηbc : Continuous ηb := by
    refine ha.quot.isQuotientMap.continuous_iff.mpr ?_
    have e : (ηb ∘ art) = η.1 := funext hηb
    rw [e]
    exact η.2.1
  let χ : G K Ω →* ℂˣ := (ηb.comp (toAb K Ω))⁻¹
  have hχ : ∀ σ, χ σ = (ηb (toAb K Ω σ))⁻¹ := fun σ => rfl
  have hχc : Continuous χ := by
    have ht : Continuous (toAb K Ω) := (QuotientGroup.isQuotientMap_mk _).continuous
    exact (hηbc.comp ht).inv
  have hχn : ∀ σ, χ σ ^ n = 1 := fun σ => by
    obtain ⟨x, hx⟩ := hs (toAb K Ω σ)
    rw [hχ, ← hx, hηb, inv_pow, hηn, inv_one]
  refine ⟨χ, isOpen_ker_of_pow χ hχc hn hχn, fun h1 => ?_, ?_⟩
  · apply Subtype.ext
    refine MonoidHom.ext fun x => ?_
    obtain ⟨σ, hσ⟩ := toAb_surjective (E := K) (Ω := Ω) (art x)
    have e := DFunLike.congr_fun h1 σ
    rw [hχ, hσ, hηb, MonoidHom.one_apply, inv_eq_one] at e
    exact e
  · filter_upwards [(GlobalTheory.Mem.UnrAe.unr_ae_and_level K η).1] with v hv
    intro A σ hA hσ
    obtain ⟨x, hx, e⟩ := (ha.frob v A hA _).mpr ⟨σ, hσ, rfl⟩
    rw [hχ, ← map_inv, ← map_inv, ← e, hηb, ← η.val_eq hv x hx]
    rfl

end GlobalTheory.HeckeToGal

end
