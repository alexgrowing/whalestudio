import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharZeroAdicCompletion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecompositionGroupLocalGaloisIso
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import GroundTheory.LocalFields.ConductorReciprocity
import GroundTheory.LocalFields.LubinTateReciprocity
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LubinTateTorsionGaloisActionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinFrobeniusActionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilGroupDenseInDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinUnitOfUniformizerStatement
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LTRecip

theorem lubinTate_action : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (a : Weil h →* (w.adicCompletion E)ˣ), IsLocalArtin h a → ∀ (ι : Ω →ₐ[E] Kbar w), IsLocEmb A w ι →
    ∀ [ValuativeRel (Kbar w)] [TopologicalSpace (Kbar w)] [IsValuativeTopology (Kbar w)]
      [ValuativeExtension (w.adicCompletion E) (Kbar w)] {π : 𝒪[w.adicCompletion E]} (hπ : Irreducible π)
      {f : PowerSeries 𝒪[w.adicCompletion E]} (hf : IsLubinTateSeries π f)
      (c : Dec (F := E) A →* (w.adicCompletion E)ˣ),
      Continuous (fun g => ((c g : (w.adicCompletion E)ˣ) : w.adicCompletion E)) →
      (∀ σ : Weil h, ((c ⟨σ, Weil_le_Dec h σ.2⟩ : (w.adicCompletion E)ˣ) : w.adicCompletion E) =
        (a σ : w.adicCompletion E) * (π : w.adicCompletion E) ^ deg σ) →
      ∀ (g : Dec (F := E) A) (τ : GalLoc w), Lifts ι τ (g : G E Ω) →
      ∀ (u : 𝒪[w.adicCompletion E]), (u : w.adicCompletion E) = (c g : w.adicCompletion E) →
      ∀ (n : ℕ), ∀ x ∈ lubinTateTorsion (Kbar w) (hπ := hπ) hf n, lubinTateGalPointMap (hπ := hπ) hf τ x = u • x := by
  intro E Ω _ _ _ _ _ A w h a ha ι hι _ _ _ _ π hπ f hf c hc hcW g τ hτ u hu n x hx

  have hWeil : ∀ (σ : Weil h) (τ' : GalLoc w), Lifts ι τ' (σ : G E Ω) → ∀ (u' : 𝒪[w.adicCompletion E]),
      (u' : w.adicCompletion E) = (a σ : w.adicCompletion E) * (π : w.adicCompletion E) ^ deg σ →
      lubinTateGalPointMap (hπ := hπ) hf τ' x = u' • x := by
    intro σ τ' hτ' u' hu'
    obtain ⟨v, hv⟩ := GlobalTheory.T.local_artin_unit_of_uniformizer E Ω A w h a ha σ π u' hπ hu'
    have hy : unitUniformizerPow hπ v (-deg σ) = a σ := by
      apply Units.ext
      rw [unitUniformizerPow, Units.val_mul, Units.coe_map, Units.val_zpow_eq_zpow_val, Units.val_mk0]
      change ((v : 𝒪[w.adicCompletion E]) : w.adicCompletion E) * _ = _
      rw [hv, hu', zpow_neg, mul_assoc, mul_inv_cancel₀ (zpow_ne_zero _ (coe_ne_zero_of_irreducible hπ)), mul_one]
    have hvx : (v : 𝒪[w.adicCompletion E]) • x ∈ lubinTateTorsion (Kbar w) (hπ := hπ) hf n :=
      Submodule.smul_mem _ _ hx
    obtain ⟨hz, hact⟩ := GlobalTheory.T.lubin_tate_torsion_galois_action (w.adicCompletion E) (Kbar w) hπ hf v (-deg σ) n _ hvx
    have key := GlobalTheory.T.local_artin_frobenius_action E Ω A w h a ha ι hι σ τ' hτ' _ hz
    rw [← hy, hact, smul_smul, Units.inv_mul, one_smul] at key
    apply IdealPoint.ext
    rw [lubinTateGalPointMap_val, key, ← hv]
  set K := w.adicCompletion E
  have hπ0 : (π : K) ≠ 0 := coe_ne_zero_of_irreducible hπ
  set γ := valuation K ((π : K) ^ n) with hγ
  have hγ0 : γ ≠ 0 := by simp [γ, hπ0]

  set T := lubinTateField (Kbar w) hπ hf n
  have hU : IsOpen (T.fixingSubgroup : Set (GalLoc w)) := T.fixingSubgroup_isOpen

  set V : Set (Dec (F := E) A) :=
    (fun g' => ((c g' : Kˣ) : K)) ⁻¹' {z : K | valuation K (z - (c g : K)) < γ} with hVdef
  have hball : IsOpen {z : K | valuation K (z - (c g : K)) < γ} := by
    refine isOpen_iff_mem_nhds.2 fun z hz => (IsValuativeTopology.mem_nhds_iff).2 ⟨Units.mk0 γ hγ0, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    have e : z + y - (c g : K) = (z - (c g : K)) + y := by ring
    show valuation K (z + y - (c g : K)) < γ
    rw [e]
    exact Valuation.map_add_lt _ hz hy
  have hV : IsOpen V := hball.preimage hc
  have hgV : g ∈ V := by
    show valuation K (((c g : Kˣ) : K) - (c g : K)) < γ
    rw [sub_self, map_zero]
    exact zero_lt_iff.2 hγ0
  obtain ⟨σ, τ', hτ', hU', hV'⟩ := GlobalTheory.T.weil_group_dense_in_decomposition E Ω A w h ι hι g τ hτ _ hU V hV hgV

  set cσ : K := ((c ⟨σ, Weil_le_Dec h σ.2⟩ : Kˣ) : K) with hcσ
  have hclose : valuation K (cσ - (u : K)) < γ := by rw [hu]; exact hV'
  have hγ1 : γ ≤ 1 := by
    rw [hγ, map_pow]
    exact pow_le_one₀ zero_le π.2
  have huv : valuation K (u : K) ≤ 1 := u.2
  have hcσ1 : valuation K cσ ≤ 1 := by
    have e : cσ = (cσ - (u : K)) + (u : K) := by ring
    rw [e]
    exact (Valuation.map_add _ _ _).trans (max_le (hclose.le.trans hγ1) huv)
  let uσ : 𝒪[K] := ⟨cσ, hcσ1⟩
  have hWeil := hWeil σ τ' hτ' uσ (hcW σ)

  have hxT : x.val ∈ T := val_mem_lubinTateField hπ hf hx
  have hfix : (τ⁻¹ * τ') x.val = x.val := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hU' _ hxT
  have hττ' : τ' x.val = τ x.val := by
    rw [AlgEquiv.mul_apply] at hfix
    have := congrArg τ hfix
    rwa [AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply] at this

  set t : K := (cσ - (u : K)) / (π : K) ^ n with ht
  have htv : valuation K t ≤ 1 := by
    rw [ht, map_div₀]
    rw [div_le_one₀ (zero_lt_iff.2 hγ0)]
    exact hclose.le
  let t' : 𝒪[K] := ⟨t, htv⟩
  have hsplit : uσ = u + π ^ n * t' := by
    apply Subtype.ext
    show cσ = (u : K) + (π : K) ^ n * t
    rw [ht, mul_div_cancel₀ _ (pow_ne_zero n hπ0)]
    ring
  have hxn : π ^ n • x = 0 := (mem_lubinTateTorsion hf n x).1 hx
  have hmod : uσ • x = u • x := by
    rw [hsplit, add_smul, mul_comm, mul_smul, hxn, smul_zero, add_zero]
  apply IdealPoint.ext
  rw [lubinTateGalPointMap_val, ← hττ', ← lubinTateGalPointMap_val, hWeil, hmod]

end GlobalTheory.LTRecip

end
