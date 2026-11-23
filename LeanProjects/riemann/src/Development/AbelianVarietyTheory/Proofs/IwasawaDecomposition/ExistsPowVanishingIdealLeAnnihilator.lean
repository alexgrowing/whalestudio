import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory.QCoh

theorem exists_isIrreducible_inter_open_subset {α : Type*} [TopologicalSpace α] [NoetherianSpace α]
    {T : Set α} (hT : IsClosed T) (hne : T.Nonempty) :
    ∃ Z : Set α, IsClosed Z ∧ IsIrreducible Z ∧ Z ⊆ T ∧
      ∃ U : Set α, IsOpen U ∧ (∃ x ∈ T, x ∈ U) ∧ T ∩ U ⊆ Z := by
  classical
  obtain ⟨S, hS, hc, hi, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hT
  have hSne : S.Nonempty := by
    obtain ⟨x, t, ht, -⟩ := hne
    exact ⟨t, ht⟩
  obtain ⟨Z, hZ⟩ := hS.exists_maximal hSne
  have hfin : (S \ {Z}).Finite := hS.diff
  refine ⟨Z, hc Z hZ.1, hi Z hZ.1, Set.subset_sUnion_of_mem hZ.1, (⋃₀ (S \ {Z}))ᶜ, ?_, ?_, ?_⟩
  · rw [isOpen_compl_iff, Set.sUnion_eq_biUnion]
    exact hfin.isClosed_biUnion fun t ht => hc t ht.1
  · by_contra h
    have hsub : Z ⊆ ⋃₀ (hfin.toFinset : Set (Set α)) := fun x hx => by
      rw [hfin.coe_toFinset]
      by_contra hx'
      exact h ⟨x, Set.subset_sUnion_of_mem hZ.1 hx, hx'⟩
    obtain ⟨z, hz, hZz⟩ := isIrreducible_iff_sUnion_isClosed.1 (hi Z hZ.1) hfin.toFinset
      (fun z hz => hc z (hfin.mem_toFinset.1 hz).1) hsub
    have hz' := hfin.mem_toFinset.1 hz
    exact hz'.2 (le_antisymm (hZ.2 hz'.1 hZz) hZz)
  · rintro x ⟨⟨t, ht, hxt⟩, hx⟩
    by_contra hxZ
    exact hx ⟨t, ⟨ht, fun e => hxZ ((show t = Z from e) ▸ hxt)⟩, hxt⟩

variable {X : Scheme.{0}}

theorem exists_pow_vanishingIdeal_le_annihilator [IsLocallyNoetherian X] (F : X.Modules)
    [IsFiniteQC F] (Z : Closeds X) (W : X.affineOpens) (h : support F ∩ W.1 ⊆ Z) :
    ∃ k : ℕ, (Scheme.IdealSheafData.vanishingIdeal Z).ideal W ^ k ≤
      Module.annihilator Γ(X, W.1) Γ(F, W.1) := by
  have := finite_sections F W.2
  have : IsNoetherianRing Γ(X, W.1) := IsLocallyNoetherian.component_noetherian W
  refine Ideal.exists_pow_le_of_le_radical_of_fg ?_ (IsNoetherian.noetherian _)
  rw [Scheme.IdealSheafData.vanishingIdeal_ideal, ← PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical,
    ← Module.support_eq_zeroLocus, ← fromSpec_preimage_support F W.2]
  refine PrimeSpectrum.vanishingIdeal_anti_mono fun p hp => h ⟨hp, ?_⟩
  exact W.2.range_fromSpec.le ⟨p, rfl⟩

theorem pow_le_annihilator_kernel_unit (I : X.IdealSheafData) (E : X.Modules) [E.IsQuasicoherent]
    (W : X.affineOpens) {k : ℕ}
    (h : I.ideal W ^ (k + 1) ≤ Module.annihilator Γ(X, W.1) Γ(E, W.1)) :
    I.ideal W ^ k ≤ Module.annihilator Γ(X, W.1)
      Γ(kernel ((Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι).unit.app E), W.1) := by
  set φ := (Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι).unit.app E with hφ
  intro a ha
  refine Module.mem_annihilator.2 fun t => ?_
  have h₁ : appLinear (kernel.ι φ) W.1 t ∈ (I.ideal W • ⊤ : Submodule Γ(X, W.1) Γ(E, W.1)) := by
    have := (surjective_and_ker_unit_subschemeι I E W).2
    rw [← hφ, ← range_kernel_ι_app] at this
    exact this.le ⟨t, rfl⟩
  have h₂ : ∀ u ∈ (I.ideal W • ⊤ : Submodule Γ(X, W.1) Γ(E, W.1)), a • u = 0 := fun u hu => by
    refine Submodule.smul_induction_on hu (fun r hr n _ => ?_) fun x y hx hy => ?_
    · rw [smul_smul]
      exact Module.mem_annihilator.1 (h (pow_succ (I.ideal W) k ▸ Ideal.mul_mem_mul ha hr)) n
    · rw [smul_add, hx, hy, add_zero]
  refine injective_kernel_ι_app φ W.1 ?_
  change appLinear (kernel.ι φ) W.1 (a • t) = appLinear (kernel.ι φ) W.1 0
  rw [map_smul, map_zero]
  exact h₂ _ h₁

theorem devissage : ∀ (X : Scheme.{0}) [AlgebraicGeometry.IsNoetherian X] (P : X.Modules → Prop), (∀ F : X.Modules, IsZero F → P F) → (∀ S : ShortComplex X.Modules, S.ShortExact → IsFiniteQC S.X₁ → IsFiniteQC S.X₃ → P S.X₁ → P S.X₃ → P S.X₂) → (∀ (Z : Closeds X), IsIrreducible (Z : Set X) → (∀ F : X.Modules, IsFiniteQC F → GlobalTheory.QCoh.support F ⊂ (Z : Set X) → P F) → ∀ G : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme.Modules, IsFiniteQC G → P ((Scheme.Modules.pushforward (redι Z)).obj G)) → ∀ F : X.Modules, IsFiniteQC F → P F := by
  intro X _ P h0 hext hZ
  suffices H : ∀ T : Closeds X, ∀ F : X.Modules, IsFiniteQC F → support F = T → P F from
    fun F hF => H ⟨support F, isClosed_support F⟩ F hF rfl
  intro T
  induction T using WellFoundedLT.induction with
  | ind T ih =>
  intro F hF hT
  have ih' : ∀ E : X.Modules, IsFiniteQC E → support E ⊂ (T : Set X) → P E := fun E hE h =>
    ih ⟨support E, isClosed_support E⟩ h E hE rfl
  rcases (T : Set X).eq_empty_or_nonempty with he | hne
  · exact h0 F (support_eq_empty_iff.1 (hT.trans he))
  obtain ⟨Z, hZc, hZi, hZT, U, hU, ⟨x, hxT, hxU⟩, hUZ⟩ :=
    exists_isIrreducible_inter_open_subset T.isClosed hne
  obtain ⟨W, hW, hxW, hWU⟩ := exists_affine_mem_le (U := ⟨U, hU⟩) x hxU
  let Z' : Closeds X := ⟨Z, hZc⟩
  have hP := hZ Z' hZi fun E hE h => ih' E hE (h.trans_subset hZT)
  obtain ⟨k, hk⟩ := exists_pow_vanishingIdeal_le_annihilator F Z' ⟨W, hW⟩
    fun y hy => hUZ ⟨hT ▸ hy.1, hWU hy.2⟩
  have key : ∀ (k : ℕ) (E : X.Modules), IsFiniteQC E → support E ⊆ T →
      (Scheme.IdealSheafData.vanishingIdeal Z').ideal ⟨W, hW⟩ ^ k ≤
        Module.annihilator Γ(X, W) Γ(E, W) → P E := by
    intro k
    induction k with
    | zero =>
      intro E hE hET h
      refine ih' E hE ⟨hET, fun hle => ?_⟩
      have h₁ := (mem_support_iff_annihilator_le (F := E) hW ⟨x, hxW⟩).1 (hle hxT)
      rw [pow_zero, Ideal.one_eq_top] at h
      exact (hW.primeIdealOf ⟨x, hxW⟩).isPrime.ne_top (top_le_iff.1 (h.trans h₁))
    | succ k ihk =>
      intro E hE hET h
      let G := (Scheme.Modules.pullback (redι Z')).obj E
      let φ : E ⟶ (Scheme.Modules.pushforward (redι Z')).obj G :=
        (Scheme.Modules.pullbackPushforwardAdjunction (redι Z')).unit.app E
      have hepi : Epi φ := (epi_iff_forall_affine φ).2 fun V hV =>
        (surjective_and_ker_unit_subschemeι _ E ⟨V, hV⟩).1
      have hS : (ShortComplex.mk (kernel.ι φ) φ (kernel.condition φ)).ShortExact :=
        { exact := ShortComplex.exact_kernel φ }
      have hK : IsFiniteQC (kernel φ) := inferInstance
      exact hext _ hS hK (IsFiniteQC.of_epi φ)
        (ihk _ hK ((support_subset_of_mono (kernel.ι φ)).trans hET)
          (pow_le_annihilator_kernel_unit _ E ⟨W, hW⟩ h)) (hP G inferInstance)
  exact key k F hF hT.le hk

end GlobalTheory.QCoh
