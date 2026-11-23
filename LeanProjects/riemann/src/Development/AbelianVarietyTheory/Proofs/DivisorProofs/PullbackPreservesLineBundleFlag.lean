import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GenericFiniteMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSection
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsQuasicoherentOfLocallyIso

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (toMod)
open GlobalTheory.VB
open GlobalTheory.IndefiniteRowSideFullHecke.GenericFiniteMaps
open GlobalTheory

namespace GlobalTheory.FlagPull

theorem injective_of_isBaseChange_of_retraction {A B M M' N N' : Type*} [CommRing A]
    [CommRing B] [Algebra A B] [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']
    [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N] [AddCommGroup N']
    [Module A N'] [Module B N'] [IsScalarTower A B N'] {l : M →ₗ[A] N} {l' : M' →ₗ[A] N'}
    (hl : IsBaseChange B l) (hl' : IsBaseChange B l') (a : M →ₗ[A] M') (b : N →ₗ[B] N')
    (hab : ∀ m, b (l m) = l' (a m)) (r : M' →ₗ[A] M) (hr : r ∘ₗ a = LinearMap.id) :
    Function.Injective b := by
  have e : b ∘ₗ hl.equiv.toLinearMap = hl'.equiv.toLinearMap ∘ₗ a.baseChange B := by
    ext m
    simp [hab]
  have ha : Function.Injective (a.baseChange B) := by
    have h : (r.baseChange B) ∘ₗ (a.baseChange B) = LinearMap.id := by
      rw [← LinearMap.baseChange_comp, hr, LinearMap.baseChange_id]
    exact Function.LeftInverse.injective (g := r.baseChange B) fun x => by
      rw [← LinearMap.comp_apply, h, LinearMap.id_apply]
  have h : Function.Injective (b ∘ₗ hl.equiv.toLinearMap) := by
    rw [e]
    exact hl'.equiv.injective.comp ha
  exact Function.Injective.of_comp_right h hl.equiv.surjective

theorem isQuasicoherent_X₂ {X : Scheme.{0}} (S : ShortComplex X.Modules) (hS : S.ShortExact)
    {s : ℕ} (h₃ : IsVB S.X₃ s) [S.X₁.IsQuasicoherent] : S.X₂.IsQuasicoherent := by
  have := hS.mono_f
  have := hS.epi_g
  have : S.X₃.IsQuasicoherent := h₃.isQuasicoherent
  have hex (W : X.Opens) (t : Γ(S.X₂, W)) (ht : S.g.app W t = 0) : ∃ u, S.f.app W u = t :=
    (QCoh.exact_app_of_exact_of_mono hS.exact W t).1 ht
  refine QCoh.isQuasicoherent_of_forall_exists_affine _ fun x => ?_
  obtain ⟨U, -, hxU, σ, hσ, hg⟩ :=
    DualExact.exists_local_section S.g h₃ (V := ⊤) (x := x) trivial
  obtain ⟨_, ⟨U', hU', rfl⟩, hxU', hle⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU U.2
  have hle : U' ≤ U := hle
  refine ⟨U', hU', hxU', fun a => (QCoh.isLocalizedModule_resBasicOpen_iff _ a).2
    ⟨fun t => ?_, fun t ht => ?_⟩⟩
  · have hD : X.basicOpen a ≤ U' := X.basicOpen_le a
    obtain ⟨n, t₃, ht₃⟩ := QCoh.exists_pow_smul_eq_res S.X₃ hU' a hD rfl (S.g.app _ t)
    obtain ⟨u, hu⟩ := hex _ (t - σ _ (hD.trans hle) (S.g.app _ t)) (by rw [map_sub, hg, sub_self])
    obtain ⟨m, u', hu'⟩ := QCoh.exists_pow_smul_eq_res S.X₁ hU' a hD rfl u
    refine ⟨n + m, a ^ m • σ U' hle t₃ + a ^ n • S.f.app U' u', ?_⟩
    have e₁ : S.X₂.presheaf.map (homOfLE hD).op (σ U' hle t₃) =
        σ _ (hD.trans hle) (S.X₃.presheaf.map (homOfLE hD).op t₃) := (hσ _ _ hle hD t₃).symm
    have e₂ : S.X₂.presheaf.map (homOfLE hD).op (S.f.app U' u') =
        S.f.app _ (S.X₁.presheaf.map (homOfLE hD).op u') := (QCoh.app_res S.f hD u').symm
    have e₃ : t = σ _ (hD.trans hle) (S.g.app _ t) + S.f.app _ u := by rw [hu]; abel
    rw [map_add, S.X₂.map_smul, S.X₂.map_smul, e₁, e₂, ← ht₃, ← hu', map_smul,
      Scheme.Modules.Hom.app_smul, map_pow, map_pow, smul_smul, smul_smul]
    conv_lhs => rw [e₃]
    rw [smul_add, pow_add]
    congr 1
    · rw [mul_comm]
  · have hD : X.basicOpen a ≤ U' := X.basicOpen_le a
    obtain ⟨n, hn⟩ := QCoh.exists_pow_smul_eq_zero S.X₃ hU' a hD rfl (S.g.app U' t)
      (by rw [← QCoh.app_res, ht, map_zero])
    obtain ⟨u, hu⟩ := hex U' (a ^ n • t) (by rw [Scheme.Modules.Hom.app_smul, hn])
    obtain ⟨m, hm⟩ := QCoh.exists_pow_smul_eq_zero S.X₁ hU' a hD rfl u
      (QCoh.injective_app_of_mono S.f _ (by
        rw [QCoh.app_res, hu, S.X₂.map_smul, ht, smul_zero, map_zero]))
    exact ⟨m + n, by rw [pow_add, mul_smul, ← hu, ← Scheme.Modules.Hom.app_smul, hm, map_zero]⟩

theorem mono_pullback_map_f {X Y : Scheme.{0}} (f : Y ⟶ X) (S : ShortComplex X.Modules)
    (hS : S.ShortExact) {s : ℕ} (h₃ : IsVB S.X₃ s) [S.X₁.IsQuasicoherent]
    [S.X₂.IsQuasicoherent] : Mono ((Scheme.Modules.pullback f).map S.f) := by
  have := hS.mono_f
  have := hS.epi_g
  have hex (W : X.Opens) (t : Γ(S.X₂, W)) (ht : S.g.app W t = 0) : ∃ u, S.f.app W u = t :=
    (QCoh.exact_app_of_exact_of_mono hS.exact W t).1 ht
  have hz (W : X.Opens) (u : Γ(S.X₁, W)) : S.g.app W (S.f.app W u) = 0 :=
    (QCoh.exact_app_of_exact_of_mono hS.exact W _).2 ⟨u, rfl⟩
  refine QCoh.mono_of_locally_app_injective _ fun W y hy => ?_
  obtain ⟨U, -, hxU, σ, -, hg⟩ :=
    DualExact.exists_local_section S.g h₃ (V := ⊤) (x := f y) trivial
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hxU U.2
  have hVU : V ≤ U := hVU
  obtain ⟨_, ⟨U', hU', rfl⟩, hyU', hle⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (show y ∈ W ⊓ f ⁻¹ᵁ V from ⟨hy, hyV⟩) (W ⊓ f ⁻¹ᵁ V).2
  have e : U' ≤ f ⁻¹ᵁ V := fun _ h => (hle h).2
  refine ⟨U', hyU', fun _ h => (hle h).1, ?_⟩
  let π : Γ(S.X₂, V) →ₗ[Γ(X, V)] Γ(S.X₂, V) := LinearMap.id - σ V hVU ∘ₗ QCoh.homAppLinear S.g V
  have hc (t : Γ(S.X₂, V)) : ∃ u, QCoh.homAppLinear S.f V u = π t := hex V _ (by
    change S.g.app V (t - σ V hVU (S.g.app V t)) = 0
    rw [map_sub, hg, sub_self])
  let ρ : Γ(S.X₂, V) →ₗ[Γ(X, V)] Γ(S.X₁, V) :=
    LinearMap.codRestrictOfInjective π (QCoh.homAppLinear S.f V) (QCoh.injective_app_of_mono S.f V) hc
  have hρ : ρ ∘ₗ QCoh.homAppLinear S.f V = LinearMap.id := by
    refine LinearMap.ext fun u => QCoh.injective_app_of_mono S.f V ?_
    have h := LinearMap.codRestrictOfInjective_comp_apply π (QCoh.homAppLinear S.f V)
      (QCoh.injective_app_of_mono S.f V) hc (S.f.app V u)
    change S.f.app V (ρ (S.f.app V u)) = S.f.app V u
    refine h.trans ?_
    change S.f.app V u - σ V hVU (S.g.app V (S.f.app V u)) = S.f.app V u
    rw [hz, map_zero, sub_zero]
  letI := QCoh.appLEAlgebra f e
  letI := QCoh.appLEModule f ((Scheme.Modules.pullback f).obj S.X₁) e
  haveI := QCoh.appLE_isScalarTower f ((Scheme.Modules.pullback f).obj S.X₁) e
  letI := QCoh.appLEModule f ((Scheme.Modules.pullback f).obj S.X₂) e
  haveI := QCoh.appLE_isScalarTower f ((Scheme.Modules.pullback f).obj S.X₂) e
  exact injective_of_isBaseChange_of_retraction
    (QCoh.isBaseChange_pullbackSections f S.X₁ hU' hV e)
    (QCoh.isBaseChange_pullbackSections f S.X₂ hU' hV e) (QCoh.homAppLinear S.f V)
    (QCoh.homAppLinear ((Scheme.Modules.pullback f).map S.f) U')
    (QCoh.pullback_map_app_pullbackSections f S.f e) ρ hρ

theorem isQuasicoherent_and_hasFlag_pullback {X Y : Scheme.{0}} (f : Y ⟶ X) {E : X.Modules}
    {l : List (LB X)} (h : HasFlag E l) :
    E.IsQuasicoherent ∧ HasFlag ((Scheme.Modules.pullback f).obj E) (l.map fun L => L.pull f) := by
  induction h with
  | nil h => exact ⟨QCoh.isQuasicoherent_of_isZero h, .nil (Functor.map_isZero _ h)⟩
  | @cons L l S hS hL e h ih =>
    obtain ⟨h₁, ih⟩ := ih
    have h₃ : IsVB S.X₃ 1 := (isVB_toMod hL).of_iso e.symm
    haveI := h₁
    haveI h₂ : S.X₂.IsQuasicoherent := isQuasicoherent_X₂ S hS h₃
    refine ⟨h₂, ?_⟩
    have := hS.epi_g
    obtain ⟨φ⟩ := nonempty_pullback_toMod_iso hL f
    have hS' : (S.map (Scheme.Modules.pullback f)).ShortExact :=
      ShortComplex.ShortExact.mk' (QCoh.exact_map_pullback f hS.exact).1
        (mono_pullback_map_f f S hS h₃) (QCoh.exact_map_pullback f hS.exact).2
    exact .cons (S.map (Scheme.Modules.pullback f)) hS' (Semi.LB.isLB_pull hL f)
      ((Scheme.Modules.pullback f).mapIso e ≪≫ φ) ih

theorem hasFlag_pullback : ∀ (X Y : Scheme.{0}) (f : Y ⟶ X) (E : X.Modules) (l : List (LB X)),
    HasFlag E l → HasFlag ((Scheme.Modules.pullback f).obj E) (l.map fun L => L.pull f) :=
  fun _ _ f _ _ h => (isQuasicoherent_and_hasFlag_pullback f h).2

end GlobalTheory.FlagPull
