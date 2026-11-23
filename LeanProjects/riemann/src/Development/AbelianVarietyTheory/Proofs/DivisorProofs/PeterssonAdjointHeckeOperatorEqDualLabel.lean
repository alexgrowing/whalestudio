import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.HeckeTupleStatement
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalToGlobal.ProjectiveLattices.UnramBridgeHolds
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdemOfIsPrimeIdem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffSetIntegralNat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermitiStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeckeAdjoint

theorem unramified_host (D : D7) : Algebra.Unramified (𝓞 D.host.F) (𝓞 D.host.E) := by
  haveI := D.host.isCMField_hostE
  exact Formalism.L2.Pj.unramBridge_holds D.host.E fun P hP => by
    obtain ⟨θ, t, ht, hθ⟩ := D.sp.cm.cmUnram.2.2 P hP
    refine ⟨θ, ?_⟩
    have : RingOfIntegers.mapRingEquiv
        (IsCMField.complexConj D.host.E : D.host.E ≃+* D.host.E) θ = t :=
      RingOfIntegers.ext ht.symm
    rwa [this]

theorem realUnif (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) : GlobalTheory.SphericalOps.RealUnif P := by
  haveI := P.isPrime
  haveI : Algebra.IsUnramifiedAt (𝓞 D.host.F) P.asIdeal :=
    Algebra.unramified_iff_forall.1 (unramified_host D) ⟨P.asIdeal, P.isPrime⟩
  have hle : (P.asIdeal.under (𝓞 D.host.F)).map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) ≤ P.asIdeal :=
    Ideal.map_comap_le
  have h1 : Ideal.ramificationIdx' (P.asIdeal.under (𝓞 D.host.F)) P.asIdeal = 1 := by
    letI := Localization.AtPrime.algebraOfLiesOver (P.asIdeal.under (𝓞 D.host.F)) P.asIdeal
    exact (Ideal.IsDedekindDomain.ramificationIdx'_eq_one_iff P.ne_bot hle).2
      ((Algebra.isUnramifiedAt_iff_map_eq (𝓞 D.host.F) (P.asIdeal.under (𝓞 D.host.F)) P.asIdeal).1 ‹_›).2
  have h2 : ¬ (P.asIdeal.under (𝓞 D.host.F)).map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) ≤ P.asIdeal ^ 2 :=
    fun h => (Ideal.ramificationIdx'_ne_one_iff hle).2 h h1
  rw [Ideal.map_le_iff_le_comap, SetLike.not_le_iff_exists] at h2
  obtain ⟨x, hx, hx2⟩ := h2
  exact ⟨x, algebraMap _ _ x, rfl, hx, hx2⟩

open GlobalTheory.SphericalOps in

theorem ipM_heckeOn_dualLab : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (J : Subgroup (GA D V)) (χ : GA D V → ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))), ∀ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), IsInfFam θ → μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → SchurMult θ M (J : Set (GA D V)) χ μ 𝓕 → ∀ P d R R', Hecke₂ V (J : Set (GA D V)) χ Sb P d R → Hecke₂ V (J : Set (GA D V)) χ Sb P (dualLab d) R' → ∀ T ∈ Mult θ M (J : Set (GA D V)) χ, ∀ T' ∈ Mult θ M (J : Set (GA D V)) χ, heckeOn M R T ∈ Mult θ M (J : Set (GA D V)) χ → heckeOn M R' T' ∈ Mult θ M (J : Set (GA D V)) χ → ipM M μ 𝓕 (heckeOn M R T) T' = ipM M μ 𝓕 T (heckeOn M R' T') := by
  intro D V S θ M J χ Sb μ 𝓕 hθ hμ h𝓕 hS P d R R' h h' T hT T' hT' hRT hRT'
  obtain ⟨R₁, h₁', hcard, K, x, hK, hR, hR₁⟩ := exists_dual (realUnif D P) h
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  haveI : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram
  haveI : μ.IsMulRightInvariant := GlobalTheory.T.isMulRightInvariant_haar_adelicUnitaryGroup_hermitianSpace D V μ hμ
  have hS' := hS hθ hμ h𝓕
  have h₁ := ipM_spec M μ 𝓕 _ _ (hS' _ hRT _ hT')
  have h₂ := ipM_spec M μ 𝓕 _ _ (hS' _ hT _ hRT')
  obtain ⟨c₃, h₃⟩ := hS' _ hT _ hT
  obtain ⟨c₄, h₄⟩ := hS' _ hT' _ hT'
  rw [GlobalTheory.MultMem.mem_mult_iff] at hT hT'
  have hex : ∀ τ, ∃ w : M.sm τ, (w : M.H τ) ≠ 0 := fun τ => by
    obtain ⟨w, hw, h0⟩ := (Submodule.ne_bot_iff _).1 (GlobalTheory.GardingVec.sm_ne_bot D V S M τ)
    exact ⟨⟨w, hw⟩, h0⟩
  choose v hv using hex
  have hv0 : ∏ τ, inner ℂ (v τ : M.H τ) (v τ : M.H τ) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun τ _ => inner_self_ne_zero.2 (hv τ)
  have e : heckeOn M R' T' v = heckeLin V R₁ (T' v) :=
    labelUnique (realUnif D) P (dualLab d) R' R₁ h' h₁' (T' v) (hT'.lev v)
  have key : ∫ g in 𝓕, star (heckeOn M R T v g) * T' v g ∂μ =
      ∫ g in 𝓕, star (T v g) * heckeOn M R' T' v g ∂μ := by
    rw [e]
    exact integral_adjoint h𝓕 K x R R₁ (hT.aut v).cont (hT'.aut v).cont (hT.aut v).left (hT'.aut v).left
      (fun k hk g => by rw [hT.lev v k (hK k hk).1, (hK k hk).2, one_mul])
      (fun k hk g => by rw [hT'.lev v k (hK k hk).1, (hK k hk).2, one_mul])
      (h₃ v v).1 (h₄ v v).1 hR hR₁ hcard
  exact mul_right_cancel₀ hv0 ((h₁ v v).2.symm.trans (key.trans (h₂ v v).2))

end GlobalTheory.HeckeAdjoint
