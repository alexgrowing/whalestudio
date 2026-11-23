import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCorrectionApproximateIdealSectionsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PhiDivisorArcBlowup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.CoeNonzeroLocusCanonicalEqComplRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkElementsApproxLeadingTermQuotients
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

namespace GlobalTheory.CorrCover

theorem exists_corr : ∀ (Z M S₁ : Scheme.{0}) [IsIntegral M] [IsIntegral S₁] (sM : M ⟶ Sp ℤ) (p₁ : S₁ ⟶ M) (g : M ⟶ Z) (J : Z.IdealSheafData), LocallyOfFiniteType sM → QuasiCompact sM → Flat (p₁ ≫ sM) → Geo.Tor.IsNormalScheme S₁ → IsProper p₁ → IsDominant p₁ → FinalTheorems.EffCartier (J.comap (p₁ ≫ g)) → ∀ (U₁ : S₁.Opens), (U₁ : Set S₁).Nonempty → ∀ (z₁ : M) (R : Type) [CommRing R] [IsLocalRing R] (ev : M.presheaf.stalk z₁ →+* R), IsLocalHom ev → ∀ ξ₁ : Sp R ⟶ S₁, ξ₁ ≫ p₁ = spMap ev ≫ M.fromSpecStalk z₁ → ∃ g₀ : R, idlAlong (J.comap (p₁ ≫ g)) ξ₁ = Ideal.span {g₀} ∧ ∀ D e : ℕ, ∃ e' : ℕ, ∀ f : M.presheaf.stalk z₁, (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ (ξ' : Sp V ⟶ S₁) (ev' : M.presheaf.stalk z₁ →+* V), IsLocalHom ev' → spMap ev' ≫ M.fromSpecStalk z₁ = ξ' ≫ p₁ → Set.range (jK V ≫ ξ') ⊆ (U₁ : Set S₁) → ev' f ∈ idlAlong (J.comap (p₁ ≫ g)) ξ' ^ D ⊔ ((maximalIdeal (M.presheaf.stalk z₁)).map ev') ^ e') → ∃ h ∈ (Scheme.stalkClosedPointTo ξ₁).hom.range, ev f - h * g₀ ^ D ∈ maximalIdeal R ^ e := by
  intro Z M S₁ _ _ sM p₁ g J h1 h2 h3 hN h5 h6 hEC U₁ hU z₁ R _ _ ev hev ξ₁ hξ
  haveI := h1; haveI := h2; haveI := h3; haveI := h5; haveI := h6; haveI := hev
  set I := J.comap (p₁ ≫ g) with hIdef
  set x₁ := ξ₁ (closedPoint R)
  set ψ := (Scheme.stalkClosedPointTo ξ₁).hom
  obtain ⟨W, f₀, hx, -, hI⟩ := hEC x₁
  have st : ∀ k : ℕ, FinalTheorems.stalkId (I ^ k) x₁ = Ideal.span {(S₁.presheaf.germ _ x₁ hx).hom f₀ ^ k} := fun k => by
    rw [ReciprocityTheory.AnForm.R.ds_stalkId_eq_map _ W x₁ hx, Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, hI,
      Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton, map_pow]
  refine ⟨ψ ((S₁.presheaf.germ _ x₁ hx).hom f₀), ?_, ?_⟩
  · have := st 1
    rw [pow_one, pow_one] at this
    rw [idlAlong, this, Ideal.map_span, Set.image_singleton]
  intro D e
  obtain ⟨E, hE⟩ := EffCartierData.exists_idealSheaf_eq (CoverElements.effCartier_pow hEC D)
  obtain ⟨e', he'⟩ := GlobalTheory.T.exists_correction_approximate_ideal_sections M S₁ sM p₁ hN U₁ hU E z₁ e
  refine ⟨e', fun f hf => ?_⟩
  have hm := he' f (fun V _ _ _ _ hc ξ' ev' hl hc' hr => by
    rw [hE, TorRef.idlAlong_pow]
    exact hf V hc ξ' ev' hl hc' hr)
  obtain ⟨f₁, hf₁, r, hr, rfl⟩ := Submodule.mem_sup.1 hm
  obtain ⟨u, hu, hψ⟩ := CoverElements.exists_stalk_of_map p₁ E.idealSheaf ξ₁ ev hξ hf₁
  rw [hE, st D] at hu
  obtain ⟨h', rfl⟩ := Ideal.mem_span_singleton'.1 hu
  refine ⟨ψ h', ⟨h', rfl⟩, ?_⟩
  have hmR : (maximalIdeal (M.presheaf.stalk z₁)).map ev ≤ maximalIdeal R :=
    Ideal.map_le_iff_le_comap.2 fun x hx => (IsLocalRing.mem_maximalIdeal _).2 fun hu => hx (isUnit_of_map_unit ev x hu)
  have : ev r ∈ maximalIdeal R ^ e :=
    Ideal.pow_right_mono hmR e (by rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem ev hr)
  rw [map_add, ← hψ, map_mul, map_pow]
  convert this using 1
  exact add_sub_cancel_left _ _

end GlobalTheory.CorrCover
