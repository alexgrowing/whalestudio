import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ZariskiLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits IsLocalRing MonoidalCategory

universe u

noncomputable section

attribute [local instance] algebraOfOver

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] {X : Scheme.{u}}
  [X.Over (Spec (.of A))]

lemma existsUnique_glue_of_supportedIn {F : X.Modules} {T : Set X}
    (hF : Scheme.Modules.SupportedIn F T) {W₁ W₂ : X.Opens} (hcov : W₁ ⊔ W₂ = ⊤)
    (hdisj : Disjoint ((W₁ ⊓ W₂ : X.Opens) : Set X) T) (s₁ : Γ(F, W₁)) (s₂ : Γ(F, W₂)) :
    ∃! s : Γ(F, ⊤), resF F (le_top : W₁ ≤ ⊤) s = s₁ ∧ resF F (le_top : W₂ ≤ ⊤) s = s₂ := by
  have hzero : ∀ {V : X.Opens}, V ≤ W₁ ⊓ W₂ → ∀ t : Γ(F, V), t = 0 := fun hV t =>
    hF _ (Set.disjoint_of_subset_left hV hdisj) t
  let Wf : ULift.{u} Bool → X.Opens := fun b => if b.down then W₁ else W₂
  have hWf : ∀ b c : ULift.{u} Bool, Wf b ⊓ Wf c ≤ W₁ ⊓ W₂ ∨ b = c := by
    rintro ⟨_ | _⟩ ⟨_ | _⟩
    · exact Or.inr rfl
    · exact Or.inl (le_of_eq (inf_comm _ _))
    · exact Or.inl le_rfl
    · exact Or.inr rfl
  let sf : ∀ b, ToType ((modulesAb F).1.obj (op (Wf b))) := fun b => by
    rcases b with ⟨_ | _⟩
    · exact s₂
    · exact s₁
  have hcovx : ∀ x ∈ (⊤ : X.Opens), ∃ b, x ∈ Wf b := fun x _ => by
    have : x ∈ W₁ ⊔ W₂ := hcov ▸ trivial
    rcases this with h | h
    · exact ⟨⟨true⟩, h⟩
    · exact ⟨⟨false⟩, h⟩
  obtain ⟨s, hs⟩ := sheaf_exists_glue (modulesAb F) (V := ⊤) Wf (fun _ => le_top) hcovx sf
    (fun b c => by
      rcases hWf b c with h | rfl
      · exact (hzero h _).trans (hzero h _).symm
      · rfl)
  refine ⟨s, ⟨hs ⟨true⟩, hs ⟨false⟩⟩, fun t ht => ?_⟩
  apply sheaf_eq_of_locally (modulesAb F) t s
  intro x _
  have : x ∈ W₁ ⊔ W₂ := hcov ▸ trivial
  rcases this with h | h
  · exact ⟨W₁, le_top, h, ht.1.trans (hs ⟨true⟩).symm⟩
  · exact ⟨W₂, le_top, h, ht.2.trans (hs ⟨false⟩).symm⟩

variable {W₁ W₂ : X.Opens} (hcov : W₁ ⊔ W₂ = ⊤)
  (hdisj : Disjoint ((W₁ ⊓ W₂ : X.Opens) : Set X) (closedFibre (A := A) X))

variable (A) in

def splitSection (n : ℕ) : Γ(fibreQuot A X n, ⊤) :=
  (existsUnique_glue_of_supportedIn (supportedIn_fibreQuot_closedFibre n) hcov hdisj
    (resF (fibreQuot A X n) (le_top : W₁ ≤ ⊤) (fibreOne A X n)) 0).exists.choose

lemma splitSection_spec (n : ℕ) :
    resF (fibreQuot A X n) (le_top : W₁ ≤ ⊤) (splitSection A hcov hdisj n) =
        resF (fibreQuot A X n) (le_top : W₁ ≤ ⊤) (fibreOne A X n) ∧
      resF (fibreQuot A X n) (le_top : W₂ ≤ ⊤) (splitSection A hcov hdisj n) = 0 :=
  (existsUnique_glue_of_supportedIn (supportedIn_fibreQuot_closedFibre n) hcov hdisj
    (resF (fibreQuot A X n) (le_top : W₁ ≤ ⊤) (fibreOne A X n)) 0).exists.choose_spec

lemma quotPowMap_fibreOne (n : ℕ) :
    (quotPowMap (maximalIdeal A) (𝟙_ X.Modules) n).app ⊤ (fibreOne A X (n + 1)) =
      fibreOne A X n := by
  change ((quotPowπ (maximalIdeal A) (𝟙_ X.Modules) (n + 1)).app ⊤ ≫
    (quotPowMap (maximalIdeal A) (𝟙_ X.Modules) n).app ⊤) _ = _
  rw [← Scheme.Modules.Hom.comp_app, quotPowπ_map]

lemma quotPowMap_splitSection (n : ℕ) :
    (quotPowMap (maximalIdeal A) (𝟙_ X.Modules) n).app ⊤ (splitSection A hcov hdisj (n + 1)) =
      splitSection A hcov hdisj n := by
  obtain ⟨h₁, h₂⟩ := splitSection_spec hcov hdisj (n + 1)
  refine (existsUnique_glue_of_supportedIn (supportedIn_fibreQuot_closedFibre n) hcov hdisj
    (resF (fibreQuot A X n) (le_top : W₁ ≤ ⊤) (fibreOne A X n)) 0).unique ⟨?_, ?_⟩
    (splitSection_spec hcov hdisj n)
  · rw [resF_app, h₁, ← resF_app, quotPowMap_fibreOne]
  · rw [resF_app, h₂, map_zero]

variable (A X) in

abbrev fibreTower : ∀ n, Sheaf.H.{u} (modulesAb (fibreQuot A X (n + 1))) 0 →ₗ[A]
    Sheaf.H.{u} (modulesAb (fibreQuot A X n)) 0 :=
  fun n => H.linearMap A (quotPowMap (maximalIdeal A) (𝟙_ X.Modules) n) 0

lemma mem_towerLimit_splitSection :
    (fun n => (Sheaf.H.equiv₀ (modulesAb (fibreQuot A X n)) isTerminalTop).symm
      (splitSection A hcov hdisj n)) ∈ towerLimit (fibreTower A X) := by
  intro n
  change Sheaf.H.map.{u} (modulesAbMap (quotPowMap (maximalIdeal A) (𝟙_ X.Modules) n)) 0
    ((Sheaf.H.equiv₀ _ isTerminalTop).symm (splitSection A hcov hdisj (n + 1))) = _
  exact (Sheaf.H.equiv₀_symm_naturality isTerminalTop _ _).trans
    (congrArg _ (quotPowMap_splitSection hcov hdisj n))

include hcov hdisj in

theorem false_of_split (hΓ : Function.Surjective (algebraMap A Γ(X, ⊤)))
    (hsurj : ∀ x : (∀ n, Sheaf.H.{u} (modulesAb (fibreQuot A X n)) 0),
      x ∈ towerLimit (fibreTower A X) → x 0 ∈ LinearMap.range
      (H.linearMap.{u} A (quotPowπ (maximalIdeal A) (𝟙_ X.Modules) 0) 0))
    {x₁ x₂ : X} (hx₁ : x₁ ∈ closedFibre (A := A) X) (hx₁W : x₁ ∈ W₁)
    (hx₂ : x₂ ∈ closedFibre (A := A) X) (hx₂W : x₂ ∈ W₂) : False := by
  obtain ⟨h, hh⟩ := hsurj _ (mem_towerLimit_splitSection hcov hdisj)
  set g : Γ(X, ⊤) := Sheaf.H.equiv₀ (modulesAb (𝟙_ X.Modules)) isTerminalTop h
  obtain ⟨a, ha⟩ := hΓ g
  have hs : splitSection A hcov hdisj 0 = (algebraMap A Γ(X, ⊤) a) • fibreOne A X 0 := by
    have e1 : Sheaf.H.equiv₀ (modulesAb (fibreQuot A X 0)) isTerminalTop
        (H.linearMap A (quotPowπ (maximalIdeal A) (𝟙_ X.Modules) 0) 0 h) =
          splitSection A hcov hdisj 0 := by
      rw [hh]
      exact AddEquiv.apply_symm_apply _ _
    rw [← e1]
    change Sheaf.H.equiv₀ _ isTerminalTop (Sheaf.H.map.{u}
      (modulesAbMap (quotPowπ (maximalIdeal A) (𝟙_ X.Modules) 0)) 0 h) = _
    rw [← Sheaf.H.equiv₀_naturality]
    change (quotPowπ (maximalIdeal A) (𝟙_ X.Modules) 0).app ⊤ g = _
    have e2 : (show Γ(𝟙_ X.Modules, ⊤) from g) =
        algebraMap A Γ(X, ⊤) a • (show Γ(𝟙_ X.Modules, ⊤) from (1 : Γ(X, ⊤))) := by
      rw [← ha]
      exact (mul_one (algebraMap A Γ(X, ⊤) a)).symm
    rw [e2]
    exact Scheme.Modules.Hom.app_smul _ _ _
  obtain ⟨hs₁, hs₂⟩ := splitSection_spec hcov hdisj 0
  rw [hs, resF_smul] at hs₁ hs₂
  rcases isUnit_or_isUnit_one_sub_self a with hu | hu
  · apply resF_fibreOne_ne_zero hx₂ hx₂W 0
    have hu' : IsUnit (resO (le_top : W₂ ≤ ⊤) (algebraMap A Γ(X, ⊤) a)) := (hu.map _).map _
    obtain ⟨v, hv⟩ := hu'
    rw [← hv] at hs₂
    have := congrArg (fun t => (↑v⁻¹ : Γ(X, W₂)) • t) hs₂
    simpa [smul_smul] using this
  · apply resF_fibreOne_ne_zero hx₁ hx₁W 0
    have hu' : IsUnit (resO (le_top : W₁ ≤ ⊤) (algebraMap A Γ(X, ⊤) (1 - a))) := (hu.map _).map _
    have e : resO (le_top : W₁ ≤ ⊤) (algebraMap A Γ(X, ⊤) (1 - a)) •
        resF (fibreQuot A X 0) (le_top : W₁ ≤ ⊤) (fibreOne A X 0) = 0 := by
      rw [map_sub, map_one, map_sub, map_one, sub_smul, one_smul, hs₁, sub_self]
    obtain ⟨v, hv⟩ := hu'
    rw [← hv] at e
    have := congrArg (fun t => (↑v⁻¹ : Γ(X, W₁)) • t) e
    simpa [smul_smul] using this

section Connected

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] {X : Scheme.{u}}
  [X.Over (Spec (.of A))]

omit [IsNoetherianRing A] in

lemma isClosed_closedFibre : IsClosed (closedFibre (A := A) X) :=
  (isClosed_singleton_closedPoint A).preimage (X ↘ Spec (.of A)).base.hom.continuous

theorem isConnected_closedFibre_of_surj [IsProper (X ↘ Spec (.of A))]
    (hΓ : Function.Bijective (algebraMap A Γ(X, ⊤)))
    (hsurj : ∀ x : (∀ n, Sheaf.H.{u} (modulesAb (fibreQuot A X n)) 0),
      x ∈ towerLimit (fibreTower A X) → x 0 ∈ LinearMap.range
      (H.linearMap.{u} A (quotPowπ (maximalIdeal A) (𝟙_ X.Modules) 0) 0)) :
    _root_.IsConnected (closedFibre (A := A) X) := by
  refine ⟨?_, ?_⟩
  ·
    have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of A))
    have hinj : Function.Injective (X ↘ Spec (.of A)).appTop := by
      intro r s hrs
      obtain ⟨r', rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of A)).inv).2 r
      obtain ⟨s', rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of A)).inv).2 s
      have : algebraMap A Γ(X, ⊤) r' = algebraMap A Γ(X, ⊤) s' := hrs
      rw [hΓ.1 this]
    have : IsDominant (X ↘ Spec (.of A)) := isDominant_of_of_appTop_injective hinj
    have hrange : Set.range (X ↘ Spec (.of A)).base = Set.univ := by
      rw [← ((X ↘ Spec (.of A)).isClosedMap.isClosed_range).closure_eq]
      exact (X ↘ Spec (.of A)).denseRange.closure_range
    obtain ⟨x, hx⟩ : closedPoint A ∈ Set.range (X ↘ Spec (.of A)).base := hrange ▸ trivial
    exact ⟨x, hx⟩
  · intro u v hu hv hsub hu' hv'
    by_contra hne
    set X₀ := closedFibre (A := A) X
    have hX₀ : IsOpen X₀ᶜ := isClosed_closedFibre.isOpen_compl
    let W₁ : X.Opens := ⟨u ∪ X₀ᶜ, hu.union hX₀⟩
    let W₂ : X.Opens := ⟨v ∪ X₀ᶜ, hv.union hX₀⟩
    have hcov : W₁ ⊔ W₂ = ⊤ := by
      apply le_antisymm le_top
      intro x _
      by_cases hx : x ∈ X₀
      · rcases hsub hx with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr (Or.inl h)
      · exact Or.inl (Or.inr hx)
    have hdisj : Disjoint ((W₁ ⊓ W₂ : X.Opens) : Set X) X₀ := by
      rw [Set.disjoint_left]
      rintro x ⟨h₁, h₂⟩ hx
      rcases h₁ with h₁ | h₁
      · rcases h₂ with h₂ | h₂
        · exact hne ⟨x, hx, h₁, h₂⟩
        · exact h₂ hx
      · exact h₁ hx
    obtain ⟨x₁, hx₁, hx₁u⟩ := hu'
    obtain ⟨x₂, hx₂, hx₂v⟩ := hv'
    exact false_of_split hcov hdisj hΓ.2 hsurj hx₁ (Or.inl hx₁u) hx₂ (Or.inl hx₂v)

end Connected

end

end GroundTheory.Arith.SchemeCoh
