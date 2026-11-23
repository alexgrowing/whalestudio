import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EffCartierComapOfDisjoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericPreimageEqRangeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlatComapPowEffectiveCartierStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtendFiniteOverNormalDenseStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIsoFiniteBirationalNormalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormalNoetherianGenericFiberStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormalizationBlowupIsIsoDenseStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormalizedBlowupSeparatedStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericFiberNormalReducedStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundaryDivisorAvoidsAbelianLocusStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackDivisorAmpleMapSupportStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.TorRef

theorem genFibre_normBlowup_iso : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (X : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (BY : GlobalTheory.EffCartierData Y.X) (k n : ℕ)
    (ρ : gen Y ⟶ gen X) (X' N : Scheme.{0}) (b : X' ⟶ X.X) (ν : N ⟶ X'),
    Y.jQ ≫ ρ = X.jQ → GlobalTheory.IsAmpleLB (polOf Y k BY) → (∀ x ∈ BY.idealSheaf.support, x ∉ abLocus Y.t.G) → 0 < n →
    (((BY.idealSheaf ^ n).comap (genι Y)).map (ρ ≫ genι X)).comap (ρ ≫ genι X) = (BY.idealSheaf ^ n).comap (genι Y) →
    FinalTheorems.Blowup b (((BY.idealSheaf ^ n).comap (genι Y)).map (ρ ≫ genι X)) → IsFinite ν →
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme N →
    IsIso (ν ∣_ (b ⁻¹ᵁ (((BY.idealSheaf ^ n).comap (genι Y)).map (ρ ≫ genι X)).support.compl)) →
    Dense ((ν ⁻¹ᵁ (b ⁻¹ᵁ (((BY.idealSheaf ^ n).comap (genι Y)).map (ρ ≫ genι X)).support.compl) : N.Opens) : Set N) →
    ∃ e : gen Y ≅ pullback (ν ≫ b ≫ X.s) (spMap (algebraMap (𝓞 c.F) c.F)),
      e.hom ≫ pullback.snd _ _ = genStr Y ∧ e.hom ≫ pullback.fst _ _ ≫ ν ≫ b = ρ ≫ genι X := by
  intro E _ _ _ H D l Xo c X Y BY k n ρ X' N b ν hρ hA hBY hn hJ hB hν hN hνU hD
  haveI : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  set I := (BY.idealSheaf ^ n).comap (genι Y) with hIdef
  set f := ρ ≫ genι X with hfdef
  set J := I.map f with hJdef
  set U : X.X.Opens := J.support.compl with hUdef

  obtain ⟨hYn, hYr, hYl⟩ := GlobalTheory.T.generic_fiber_normal_reduced E H D l Xo c Y
  have hover : ρ ≫ genStr X = genStr Y := by
    haveI := hYr
    haveI : IsDominant Y.jQ := ⟨by rw [DenseRange]; exact Y.jQ_dense⟩
    refine ext_of_isDominant_of_isSeparated (Spec.map (CommRingCat.ofHom (algebraMap ℤ c.F))) ?_ Y.jQ ?_
    · exact specZIsTerminal.hom_ext _ _
    · rw [← Category.assoc, hρ]
      exact X.jQ_over.trans Y.jQ_over.symm

  have hIc : FinalTheorems.EffCartier I := GlobalTheory.T.flat_comap_pow_effective_cartier _ _ BY (genι Y) inferInstance n
  obtain ⟨q, hq, -⟩ := hB.2 (gen Y) f (by rw [hJ]; exact hIc)

  have hYoff : ∀ z, Y.jQ z ∉ I.support := GlobalTheory.T.boundary_divisor_avoids_abelian_locus E H D l Xo c Y BY n hBY
  have hXU : ∀ z, pullback.fst X.s (spMap (algebraMap (𝓞 c.F) c.F)) (X.jQ z) ∈ U := by
    intro z hz
    apply hYoff z
    rw [← hJ, Scheme.IdealSheafData.support_comap]
    change f (Y.jQ z) ∈ J.support
    have : f (Y.jQ z) = pullback.fst X.s (spMap (algebraMap (𝓞 c.F) c.F)) (X.jQ z) := by
      rw [hfdef, ← Scheme.Hom.comp_apply, ← Category.assoc, hρ]; rfl
    rw [this]; exact hz

  set V : (gen Y).Opens := q ⁻¹ᵁ (b ⁻¹ᵁ U) with hVdef
  have hVd : Dense (V : Set (gen Y)) := by
    refine Y.jQ_dense.mono ?_
    rintro _ ⟨z, rfl⟩
    change b (q (Y.jQ z)) ∈ U
    rw [← Scheme.Hom.comp_apply, hq, hfdef, ← Scheme.Hom.comp_apply, ← Category.assoc, hρ]
    exact hXU z
  haveI := hνU
  let a₀ : V.toScheme ⟶ N := (q ∣_ (b ⁻¹ᵁ U)) ≫ inv (ν ∣_ (b ⁻¹ᵁ U)) ≫ (ν ⁻¹ᵁ (b ⁻¹ᵁ U)).ι
  have ha₀ : a₀ ≫ ν = V.ι ≫ q := by
    simp only [a₀, Category.assoc]
    rw [← morphismRestrict_ι ν (b ⁻¹ᵁ U), IsIso.inv_hom_id_assoc, morphismRestrict_ι]
  obtain ⟨γ, hγ, -⟩ := GlobalTheory.T.extend_finite_over_normal_dense _ _ _ ν q V a₀ hν hYn hYl hVd ha₀

  have hcomm : γ ≫ ν ≫ b ≫ X.s = genStr Y ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
    rw [reassoc_of% hγ, reassoc_of% hq, hfdef, Category.assoc, pullback.condition, ← Category.assoc, hover]
  let e₀ : gen Y ⟶ pullback (ν ≫ b ≫ X.s) (spMap (algebraMap (𝓞 c.F) c.F)) := pullback.lift γ (genStr Y) hcomm
  have he₁ : e₀ ≫ pullback.fst _ _ = γ := pullback.lift_fst _ _ _
  have he₂ : e₀ ≫ pullback.snd _ _ = genStr Y := pullback.lift_snd _ _ _
  obtain ⟨hNl, hNs⟩ := GlobalTheory.T.normalized_blowup_separated c.F X.X X' N X.s J b ν X.proj hB hν
  obtain ⟨hNFn, hNFl⟩ := GlobalTheory.T.normal_noetherian_generic_fiber (𝓞 c.F) c.F N (ν ≫ b ≫ X.s) hN hNl

  have hfin : IsFinite e₀ := by
    haveI := hNs
    haveI : IsProper (e₀ ≫ pullback.snd _ _) := by rw [he₂]; exact isProper_genStr Y
    haveI : IsProper e₀ := IsProper.of_comp e₀ (pullback.snd (ν ≫ b ≫ X.s) (spMap (algebraMap (𝓞 c.F) c.F)))
    haveI : LocallyQuasiFinite e₀ := by
      refine LocallyQuasiFinite.of_finite_preimage_singleton e₀ fun z => ?_
      refine (GlobalTheory.T.pullback_divisor_ample_map_support E H D l Xo c X Y BY k n ρ X' b q hρ hA hn hJ hB hq (ν ((pullback.fst (ν ≫ b ≫ X.s) (spMap (algebraMap (𝓞 c.F) c.F))) z))).subset ?_
      intro y hy
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hy ⊢
      rw [← hy, ← hγ, ← he₁]; rfl
    exact IsFinite.of_isProper_of_locallyQuasiFinite e₀

  have hbU : IsIso (b ∣_ U) := blowBCSt.2.2 X.X X' b J U hB (by
    rw [Set.disjoint_left]; intro x hx hx'; exact hx hx')
  obtain ⟨jN, hjNo, hjNd, hjNr, hjNp⟩ := GlobalTheory.T.normalization_blowup_isIso_dense (𝓞 c.F) c.F X.X X' N (Xo.XF c) X.s b ν U X.jQ hNl X.jQ_open
    X.jQ_dense hXU hbU hνU hD
  set r := pullback.map (ν ≫ b ≫ X.s) (spMap (algebraMap (𝓞 c.F) c.F)) X.s (spMap (algebraMap (𝓞 c.F) c.F)) (ν ≫ b)
    (𝟙 _) (𝟙 _) (by simp) (by simp) with hrdef
  have her : e₀ ≫ r = ρ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hrdef, pullback.lift_fst, ← Category.assoc, he₁, reassoc_of% hγ, hq]
    · rw [Category.assoc, hrdef, pullback.lift_snd, Category.comp_id, he₂, ← hover]
  have hjN : Y.jQ ≫ e₀ = jN := by
    haveI := hjNo
    haveI := X.jQ_open
    have hsub : Set.range (Y.jQ ≫ e₀) ⊆ Set.range jN := by
      rw [← hjNp]
      rintro _ ⟨z, rfl⟩
      show (Y.jQ ≫ e₀ ≫ r) z ∈ Set.range X.jQ
      rw [her, hρ]
      exact ⟨z, rfl⟩
    have hk := IsOpenImmersion.lift_fac jN (Y.jQ ≫ e₀) hsub
    set kk := IsOpenImmersion.lift jN (Y.jQ ≫ e₀) hsub
    have : kk = 𝟙 _ := by
      rw [← cancel_mono X.jQ, Category.id_comp, ← hjNr, ← Category.assoc, hk, Category.assoc, her, hρ]
      exact hjNr.symm
    rw [← hk, this, Category.id_comp]
  have hpre : e₀ ⁻¹' Set.range jN = Set.range Y.jQ := by
    rw [← hjNp, ← Set.preimage_comp]
    change (e₀ ≫ r) ⁻¹' _ = _
    rw [her]
    exact GlobalTheory.T.generic_preimage_eq_range E H D l Xo c _ _ X Y ρ hρ
  have hiso : IsIso e₀ := GlobalTheory.T.isIso_finite_birational_normal _ _ _ e₀ Y.jQ jN hfin hYr hNFn hNFl Y.jQ_open hjNo hjN Y.jQ_dense hjNd hpre
  refine ⟨asIso e₀, he₂, ?_⟩
  change e₀ ≫ pullback.fst _ _ ≫ ν ≫ b = f
  rw [reassoc_of% he₁, reassoc_of% hγ, hq]

end GlobalTheory.TorRef
