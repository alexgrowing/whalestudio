import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptySabMapOfCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonomialLevelFormDvrPointStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PhiDivisorBaseChangeBlowupStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFiniteEtaleSurjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgHomExtOfIsHausdorff

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.MixedUpper

theorem idlAlong_arc_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (X Z : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (BY : EffCartierData Y.X) (π : Z.X ⟶ X.X) (e : gen Y ≅ gen Z) (J : X.X.IdealSheafData) (EX : EffCartierData Z.X) (n d' : ℕ) (φ : InvFun (𝓞 E)), IsPhiDiv (comb 0 φ d' φ) Y BY → IsBlowOf X Z Y BY π e J EX n → ∀ (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [CharZero O'] (b : 𝓞 c.F →+* O') (ϖ : O') (a : ArcIn D l (algebraMap (𝓞 c.F) c.F) O' b) [Module.Finite (𝓞 E) a.D₀.X], Irreducible ϖ → IsAdicComplete (Ideal.span {ϖ}) O' → ∀ χA : Sp (PowerSeries O') ⟶ X.X, χA ≫ X.s = spMap (PowerSeries.C (R := O')) ≫ spMap b → (∀ x : Sp (PowerSeries O'), χA x ∈ abLocus X.t.G ↔ PowerSeries.X ∉ x.asIdeal) → (∀ x : Sp (PowerSeries O'), PowerSeries.C ϖ * PowerSeries.X ∉ x.asIdeal → χA x ∈ Set.range X.j) → X.HasArcData a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := O')) PowerSeries.X χA → ∀ m : ℕ, (m : ℝ) = (comb 0 φ (n * d') φ).evalZ a.be → idlAlong J χA ≤ Ideal.span {PowerSeries.X ^ m} := by
  intro E _ _ _ H D l Xo c X Z Y BY π e J EX n d' φ hPhi hBlow O' _ _ _ _ b ϖ a _ hϖ hcpl χA h1 h2 h3 h4 m hm
  have key := GlobalTheory.T.phi_divisor_base_change_blowup E H D l Xo c X Z Y BY π e J EX n d' φ hPhi hBlow O' b ϖ a hϖ hcpl χA h1 h2 h3 h4 m hm
  rw [GlobalTheory.TraitOrder.idlAlong_comp] at key
  intro h hh
  have hf : PowerSeries.map (algebraMap O' (FractionRing O')) h ∈ Ideal.span {PowerSeries.X ^ m} :=
    key (Ideal.mem_map_of_mem _ hh)
  rw [Ideal.mem_span_singleton] at hf ⊢
  rw [PowerSeries.X_pow_dvd_iff] at hf ⊢
  intro i hi
  have := hf i hi
  rw [PowerSeries.coeff_map] at this
  exact (IsFractionRing.injective O' (FractionRing O')) (by rw [this, map_zero])

theorem idlAlong_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (X Z : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (BY : EffCartierData Y.X) (π : Z.X ⟶ X.X) (e : gen Y ≅ gen Z) (J : X.X.IdealSheafData) (EX : EffCartierData Z.X) (n d d' k g : ℕ) (φs : InvFun ℤ) (𝒩 : Finset ℕ) (φ : InvFun (𝓞 E)) (DX : EffCartierData X.X), Module.finrank ℚ E * min D.p D.q ≤ g → IsPolFan id g φs → Refines H (min D.p D.q) φs 𝒩 φ → HasCones (ConeZ E φs) X → X.N4 → IsPol (comb d (resInt _ φs) 0 φ) k X DX → 0 < d' → IsPhiDiv (comb 0 φ d' φ) Y BY → IsBlowOf X Z Y BY π e J EX n → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ¬ (∀ p : ℕ, p.Prime → IsUnit (p : W)) → ∀ ϖ : W, Irreducible ϖ → ∀ (χ : Sp W ⟶ Z.X) (t : SAB H (Sp W)) (_ : SABMap t Z.t χ) (P : PELUnif (maximalIdeal W) t), Set.range (jK W ≫ χ) ⊆ Set.range Z.j → ∀ be ∈ levelForms H 1 P.D.toPre.X, IsMonomial P.D.toPre ![ϖ] ![be] → ∀ m : ℕ, (m : ℝ) = (comb 0 φ (n * d') φ).evalZ be → idlAlong J (χ ≫ π) ≤ Ideal.span {ϖ ^ m} := by
  intro E _ _ _ H D l Xo c X Z Y BY π e J EX n d d' k g φs 𝒩 φ DX _ _ hRef _ hN4 _ _ hPhi hBlow W _ _ _ hW _ ϖ hϖ χ t ht P hχ be hbe hmon m hm
  haveI : IsDiscreteValuationRing W := hW.1
  by_cases hX : Subsingleton P.D.toPre.X
  · have h0 : (comb 0 φ (n * d') φ).evalZ be = 0 := InvFun.eval_of_subsingleton _ _
    have hm0 : m = 0 := by exact_mod_cast hm.trans h0
    subst hm0
    simp
  rw [not_subsingleton_iff_nontrivial] at hX
  obtain ⟨mZ⟩ := GlobalTheory.T.nonempty_sabMap_of_compatible E H D l Xo c X Z π hBlow.2.1 hBlow.2.2.1
  obtain ⟨mX, -⟩ := GlobalTheory.LevelCover.sab_comp ht mZ rfl
  have hχX : Set.range (jK W ≫ χ ≫ π) ⊆ Set.range X.j := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨z, hz⟩ := hχ ⟨x, rfl⟩
    refine ⟨z, ?_⟩
    rw [← hBlow.2.1]
    simp only [Scheme.Hom.comp_apply] at hz ⊢
    rw [hz]
  obtain ⟨T', gg, ϖ', kk, b', a, e', hinj, hloc, hϖ', hk, hass, hs', hr', hArc, hbe'⟩ :=
    GlobalTheory.T.monomial_level_form_dvr_point E H D l Xo c X W hW ϖ hϖ (χ ≫ π) t mX P hχX be hbe hmon hX
  haveI : Module.Finite (𝓞 E) a.D₀.X := Module.Finite.of_restrictScalars_finite ℤ _ _
  have hTame := hRef.2.2.2.2.1
  have hev : (comb 0 φ (n * d') φ).evalZ a.be = kk * (comb 0 φ (n * d') φ).evalZ be := by
    have h1 : (comb 0 φ (n * d') φ).evalZ a.be =
        (comb 0 φ (n * d') φ).eval P.D.toPre.X (fun u v => (kk : ℝ) * (be u v : ℝ)) := by
      rw [InvFun.evalZ, ← InvFun.eval_equiv _ e']
      congr 1
      funext u v
      rw [hbe' u v]
      push_cast
      ring
    rw [h1]
    obtain ⟨N, r, hr⟩ := Module.Finite.exists_fin' (𝓞 E) P.D.toPre.X
    rw [InvFun.evalZ, InvFun.eval_eq _ hr, InvFun.eval_eq _ hr]
    simp only [comb]
    rw [hTame.1 N kk]
    push_cast
    ring
  have hcpl : IsAdicComplete (Ideal.span {ϖ'}) T'.V := by
    rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ').1 hϖ']
    infer_instance
  obtain ⟨χA, hchar, hspec⟩ := hN4 T'.V b' ϖ' a (Or.inr ⟨inferInstance, hϖ', hcpl⟩)
  have hprop := (hchar χA).1 rfl
  obtain ⟨ev, hevX⟩ := GlobalTheory.PowerSeriesAdicEval.exists_algHom_apply_X (R := T'.V) (Ideal.span {ϖ'})
    (Ideal.mem_span_singleton_self ϖ')
  have hC : ∀ x, ev.toRingHom (PowerSeries.C x) = x := fun x => by
    have := ev.commutes x
    simpa using this
  have hsp := hspec hϖ' (spMap gg ≫ χ ≫ π) ev.toRingHom hs' hr' hArc hC hevX
  have hB := idlAlong_arc_le E H D l Xo c X Z Y BY π e J EX n d' φ hPhi hBlow T'.V b' ϖ' a hϖ' hcpl χA hprop.1 hprop.2.1
    hprop.2.2.1 hprop.2.2.2 (kk * m) (by push_cast; rw [hev, hm])
  have h1 : idlAlong J (spMap gg ≫ χ ≫ π) ≤ Ideal.span {ϖ' ^ (kk * m)} := by
    rw [← hsp, GlobalTheory.TraitOrder.idlAlong_comp]
    refine (Ideal.map_mono hB).trans ?_
    rw [Ideal.map_span, Set.image_singleton, map_pow]
    change Ideal.span {ev PowerSeries.X ^ (kk * m)} ≤ _
    rw [hevX]
  rw [GlobalTheory.TraitOrder.idlAlong_comp] at h1
  have h2 : Ideal.span {ϖ' ^ (kk * m)} = (Ideal.span {ϖ ^ m}).map gg := by
    rw [Ideal.map_span, Set.image_singleton, map_pow, Ideal.span_singleton_eq_span_singleton, pow_mul]
    exact (hass.pow_pow (n := m)).symm
  rw [h2] at h1
  letI := gg.toAlgebra
  have : FaithfulSMul W T'.V := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have : IsLocalHom (algebraMap W T'.V) := hloc
  have : Module.Flat W T'.V := inferInstance
  have : Module.FaithfullyFlat W T'.V := Module.FaithfullyFlat.of_flat_of_isLocalHom
  rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := T'.V) (Ideal.span {ϖ ^ m})]
  exact Ideal.le_comap_of_map_le h1

end GlobalTheory.MixedUpper
