import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsSpreadLocal
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsBasisIsoFree
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PVectorBundleRestrict
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

universe u

theorem isVectorBundle_freeModule (h : FreeSheafBasis.Statement.{u}) (Y : Scheme.{u}) (n : ℕ) :
    IsVectorBundle (freeModule Y n) := by
  intro y
  obtain ⟨V, hV, hyV, -⟩ := Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
    (show y ∈ (⊤ : Y.Opens) from trivial)
  exact ⟨V, hV, hyV, n, _, (h Y n).restrict le_top⟩

theorem isPreimmersion_baseChangeMap {X : Scheme.{0}} (f : X ⟶ SpecZ) (p : Nat.Primes) :
    IsPreimmersion (baseChangeMap f (ZLoc p)) := by
  have : IsPreimmersion (Spec.map (CommRingCat.ofHom (Int.castRingHom (ZLoc p)))) := by
    have h := IsPreimmersion.of_isLocalization (R := ℤ) (S := ZLoc p)
      (Ideal.span {((p : ℕ) : ℤ)}).primeCompl
    convert h using 3
    exact RingHom.ext_int _ _
  infer_instance

theorem SpreadLocal.proof (h₁ : FreeSheafBasis.Statement.{0}) (h₂ : BasisIsoFree.Statement.{0}) :
    SpreadLocal.Statement := by
  intro X f p E hE x
  obtain ⟨U, -, hxU, n, s, hs⟩ := hE x
  have := isPreimmersion_baseChangeMap f p
  obtain ⟨W, hWo, hW⟩ := (baseChangeMap f (ZLoc p)).isEmbedding.isInducing.isOpen_iff.mp U.2
  let W' : X.Opens := ⟨W, hWo⟩
  have hWU : baseChangeMap f (ZLoc p) ⁻¹ᵁ W' = U := Opens.ext hW
  refine ⟨W', hWU ▸ hxU, ?_⟩
  let V := baseChangeMap f (ZLoc p) ⁻¹ᵁ W'
  have hle : V.ι ''ᵁ ⊤ ≤ U := by simp [V, hWU]
  obtain ⟨eF⟩ := h₂ _ (E.restrict V.ι) n _ ((hs.restrict hle).restrictImage V.ι)
  let φ := (baseChangeMap f (ZLoc p) ∣_ W').toRingCatSheafHom
  have : (SheafOfModules.pushforward φ).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction (baseChangeMap f (ZLoc p) ∣_ W')).isRightAdjoint
  exact ⟨_, isVectorBundle_freeModule h₁ _ n,
    ⟨SheafOfModules.pullbackObjFreeIso φ (ULift.{0} (Fin n)) ≪≫ eF.symm ≪≫
      (Scheme.Modules.restrictFunctorIsoPullback V.ι).app E⟩⟩

end

end GroundTheory.Heights₂.Heights.Model
