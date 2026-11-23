import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.EtaleCohomology.TateTwists.EtaleSheafMonoEpiSectionCriteria
import Development.EtaleCohomology.TateTwists.EtaleTateTwistTensorIsoOfGeneratorMapIso

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

def LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorMapLocallySurjective : Prop :=
  ∀ (q : ℕ) [NeZero q] (i j k : ℤ) (T : Shv (ZMod q)) (μ : Pair (sgl (tw q i)) (sgl (tw q j)) (sgl T)),
    μ.IsTensor → i + j = k → ∀ φ : tw q k ⟶ T, (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)),
      Sec.map (sglι T) (Sec.map φ (twGen k ζ)) =
        μ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ))) →
    ∀ (U : Scheme.{0}) (b : Sec T U), Loc U fun V g => ∃ a : Sec (tw q k) V, Sec.map φ a = Sec.res g b

def LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorMapSectionsInjective : Prop :=
  ∀ (q : ℕ) [NeZero q] (i j k : ℤ) (T : Shv (ZMod q)) (μ : Pair (sgl (tw q i)) (sgl (tw q j)) (sgl T)),
    μ.IsTensor → i + j = k → ∀ φ : tw q k ⟶ T, (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)),
      Sec.map (sglι T) (Sec.map φ (twGen k ζ)) =
        μ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ))) →
    ∀ (U : Scheme.{0}) (a : Sec (tw q k) U), Sec.map φ a = 0 → Loc U fun _ g => Sec.res g a = 0

theorem LateralTheory.EtaleFoundations.etale_tate_twist_generator_map_isIso_of_inj_surj (hme : LateralTheory.EtaleFoundations.EtaleSheafMonoEpiSectionCriteria)
    (hs : LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorMapLocallySurjective) (hi : LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorMapSectionsInjective) :
    LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorCompatibleMapIsIso := by
  intro q _ i j k T μ hμ hk φ hφ
  have h := hme (ZMod q) φ
  have hm : Mono φ := h.2.1.2 (hi q i j k T μ hμ hk φ hφ)
  have he : Epi φ := h.2.2.1.2 (hs q i j k T μ hμ hk φ hφ)
  exact isIso_of_mono_of_epi φ
