import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HbApply
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mass.Transp

theorem orbSum_img : ∀ (K V V' : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (h : V →ₗ⋆[K] V →ₗ[K] K) (h' : V' →ₗ⋆[K] V' →ₗ[K] K) (e : V ≃ₗ[K] V'), (∀ x y, h' (e x) (e y) = h x y) → ∀ φ : Submodule (𝓞 K) V' → ℝ≥0∞, (∀ (s : Formalism.HermitianLatticesTheory.isom h') (M : Submodule (𝓞 K) V'), φ (s • M) = φ M) → ∀ L : Submodule (𝓞 K) V, (∀ (s : Formalism.HermitianLatticesTheory.isom h) (M : Submodule (𝓞 K) V), φ (GlobalTheory.Mass.Transp.img e (s • M)) = φ (GlobalTheory.Mass.Transp.img e M)) ∧ (∀ M : Submodule (𝓞 K) V, GlobalTheory.Mass.Transp.img e M ∈ Formalism.HermitianLatticesTheory.genus h' (GlobalTheory.Mass.Transp.img e L) ↔ M ∈ Formalism.HermitianLatticesTheory.genus h L) ∧ GlobalTheory.Mass.orbSum (Formalism.HermitianLatticesTheory.isom h') (Formalism.HermitianLatticesTheory.genus h' (GlobalTheory.Mass.Transp.img e L)) φ = GlobalTheory.Mass.orbSum (Formalism.HermitianLatticesTheory.isom h) (Formalism.HermitianLatticesTheory.genus h L) (fun M => φ (GlobalTheory.Mass.Transp.img e M)) := by
  intro K V V' _ _ _ _ _ _ _ _ _ _ _ h h' e he φ hφ L
  have hinv : ∀ (s : Formalism.HermitianLatticesTheory.isom h) (M : Submodule (𝓞 K) V),
      φ (GlobalTheory.Mass.Transp.img e (s • M)) = φ (GlobalTheory.Mass.Transp.img e M) := by
    intro s M
    have hs := img_smul (R := 𝓞 K) e he s M
    erw [hs, hφ]
  have hgen : ∀ M : Submodule (𝓞 K) V,
      GlobalTheory.Mass.Transp.img e M ∈ Formalism.HermitianLatticesTheory.genus h' (GlobalTheory.Mass.Transp.img e L) ↔ M ∈ Formalism.HermitianLatticesTheory.genus h L := by
    intro M
    constructor
    · intro hM
      have := genus_img e.symm (symm_isom e he) _ _ hM
      rwa [img_symm_img, img_symm_img] at this
    · exact genus_img e he L M
  refine ⟨hinv, hgen, ?_⟩
  symm
  refine GlobalTheory.Mass.OrbTransport.main _ _ _ _ (conj e he) (img e) _ _ φ (genus_stable _) (genus_stable _) ?_
    (fun g x _ => img_smul e he g x) hφ
  refine ⟨fun M hM => (hgen M).2 hM, fun a _ b _ hab => ?_, fun M hM => ⟨img e.symm M, ?_, img_img_symm e M⟩⟩
  · rw [← img_symm_img e a, hab, img_symm_img]
  · rw [← hgen, img_img_symm]; exact hM

end GlobalTheory.Mass.Transp
