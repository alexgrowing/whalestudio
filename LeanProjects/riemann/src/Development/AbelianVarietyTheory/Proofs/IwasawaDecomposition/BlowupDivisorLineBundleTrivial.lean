import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackModelArcPhiDivisor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDvrExtensionClosedPointStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DvrPointBoundaryCompatibleStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.MixedLower

theorem span_le_of_map {W V : Type} [CommRing W] [IsDomain W] [IsLocalRing W] [CommRing V] [IsDomain V] [IsLocalRing V]
    (hW : CDvr W) (f : W →+* V) (hf : Function.Injective f) [IsLocalHom f] (I : Ideal W) (a : W)
    (h : f a ∈ I.map f) : Ideal.span {a} ≤ I := by
  haveI : IsDiscreteValuationRing W := hW.1
  letI := f.toAlgebra
  have : FaithfulSMul W V := (faithfulSMul_iff_algebraMap_injective _ _).2 hf
  have : IsLocalHom (algebraMap W V) := ‹IsLocalHom f›
  have : Module.Flat W V := inferInstance
  have : Module.FaithfullyFlat W V := Module.FaithfullyFlat.of_flat_of_isLocalHom
  rw [Ideal.span_le, Set.singleton_subset_iff, ← Ideal.comap_map_eq_self_of_faithfullyFlat (B := V) I]
  exact h

theorem range_jK_spMap_subset {W V : Type} [CommRing W] [IsDomain W] [CommRing V] [IsDomain V] (f : W →+* V)
    (hf : Function.Injective f) : Set.range (jK V ≫ spMap f) ⊆ Set.range (jK W) := by
  have hinj : Function.Injective ((algebraMap V (FractionRing V)).comp f) :=
    (IsFractionRing.injective V (FractionRing V)).comp hf
  let gam : FractionRing W →+* FractionRing V := IsFractionRing.lift hinj
  have hcomm : ∀ r, gam (algebraMap W _ r) = algebraMap V _ (f r) := fun r => IsFractionRing.lift_algebraMap hinj r
  have hsq : spMap gam ≫ jK W = jK V ≫ spMap f := AnyChartExtend.spMap_jK' hcomm
  rw [← hsq]
  rintro _ ⟨p, rfl⟩
  exact ⟨_, rfl⟩

theorem ofChartMem : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (X Z : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (BY : EffCartierData Y.X) (π : Z.X ⟶ X.X) (e : gen Y ≅ gen Z) (J : X.X.IdealSheafData) (EX : EffCartierData Z.X) (n d d' k g : ℕ) (φs : InvFun ℤ) (𝒩 : Finset ℕ) (φ : InvFun (𝓞 E)) (DX : EffCartierData X.X), Module.finrank ℚ E * min D.p D.q ≤ g → IsPolFan id g φs → Refines H (min D.p D.q) φs 𝒩 φ → HasCones (ConeZ E φs) X → X.N4 → IsPol (comb d (resInt _ φs) 0 φ) k X DX → 0 < d' → IsPhiDiv (comb 0 φ d' φ) Y BY → IsBlowOf X Z Y BY π e J EX n → GlobalTheory.MixedLower.ChartMem (ConeZ E φs) X J φ (n * d') → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ¬ (∀ p : ℕ, p.Prime → IsUnit (p : W)) → ∀ ϖ : W, Irreducible ϖ → ∀ (χ : Sp W ⟶ Z.X) (t : SAB H (Sp W)) (_ : SABMap t Z.t χ) (P : PELUnif (maximalIdeal W) t), Set.range (jK W ≫ χ) ⊆ Set.range Z.j → ∀ be ∈ levelForms H 1 P.D.toPre.X, IsMonomial P.D.toPre ![ϖ] ![be] → ∀ m : ℕ, (m : ℝ) = (comb 0 φ (n * d') φ).evalZ be → Ideal.span {ϖ ^ m} ≤ idlAlong J (χ ≫ π) := by
  intro E _ _ _ H D l Xo c X Z Y BY π e J EX n d d' k g φs 𝒩 φ DX _ _ _ hcones _ _ _ _ hblow hchart W _ _ _ hW hmix ϖ hϖ χ t mt P
    hgen be hbe hmono m hm
  obtain ⟨R, _, _, _, ξ, tR, mR, PR, k', γ, hCN, hx, hEt, hFU, hTor, hCn, hIn⟩ := hcones ((χ ≫ π) (closedPoint W))
  obtain ⟨V, _, _, _, f, ψ, hV, hfi, hfl, hψl, hfϖ, hsq⟩ := GlobalTheory.T.exists_dvr_extension_closed_point X.X R ξ hCN hEt hFU W hW ϖ hϖ (χ ≫ π) hx.symm
  have hZX : Z.j ≫ π = X.j := hblow.2.1
  have hgenV : Set.range (jK V ≫ spMap ψ ≫ ξ) ⊆ Set.range X.j := by
    rw [← hsq, ← hZX]
    rintro _ ⟨p, rfl⟩
    obtain ⟨q, hq⟩ := range_jK_spMap_subset f hfi ⟨p, rfl⟩
    obtain ⟨z, hz⟩ := hgen ⟨q, rfl⟩
    refine ⟨z, ?_⟩
    simp only [Scheme.Hom.comp_apply] at hz hq ⊢
    rw [hz, hq]
  obtain ⟨ε, hε⟩ := GlobalTheory.T.dvr_point_boundary_compatible E H D l Xo c X Z π hZX R ξ tR mR PR hCN hTor W hW hmix ϖ hϖ χ t mt P hgen be hmono V hV f ψ hfi
    hfl hψl hfϖ hsq hgenV
  let beR : LinearMap.BilinForm ℤ PR.D.toPre.X := pull ε.toLinearMap be
  have hmem : beR ∈ levelForms H 1 PR.D.toPre.X := by
    obtain ⟨h1, h2, -⟩ := hbe
    refine ⟨fun y z => h1 _ _, fun a y z => ?_, fun y z => by simp⟩
    simp only [beR, pull_apply, LinearEquiv.coe_coe, map_smul]
    exact h2 _ _ _
  have hform : FormAt PR.D.toPre ψ (f ϖ) beR := fun y => hε y
  have hev : (comb 0 φ (n * d') φ).evalZ beR = (comb 0 φ (n * d') φ).evalZ be := evalZ_pull _ ε.surjective be
  have hVmix : ¬ ∀ p : ℕ, p.Prime → IsUnit (p : V) := fun h => hmix fun p hp => by
    have := h p hp
    rw [← map_natCast f] at this
    exact isUnit_of_map_unit f _ this
  have key := hchart R ξ tR mR PR k' γ hCN hEt hFU hTor hCn hIn V hV hVmix (f ϖ) hfϖ ψ hψl hgenV beR hmem hform m
    (hm.trans hev.symm)
  have hmap : (idlAlong J (χ ≫ π)).map f = (idlAlong J ξ).map ψ := by
    rw [← TraitOrder.idlAlong_comp, ← TraitOrder.idlAlong_comp, hsq]
  apply span_le_of_map hW f hfi
  rw [hmap, map_pow]
  exact key (Ideal.mem_span_singleton_self _)

end GlobalTheory.MixedLower
