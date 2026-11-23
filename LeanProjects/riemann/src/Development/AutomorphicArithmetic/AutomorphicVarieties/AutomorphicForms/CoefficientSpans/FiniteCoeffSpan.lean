import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.InfEmbGrpEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.FormsFiniteAlt

noncomputable section

open NumberField GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm

namespace UpperTheory.V.Af.CoefficientSpans

def CharFinite : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (L : Subgroup (AdelicGLn.FiniteAdelicGL K n)),
    IsOpen (L : Set (AdelicGLn.FiniteAdelicGL K n)) →
  ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (archCompact K n) W)
    (χ : UEnv K n → ℂ),
    FiniteDimensional ℂ (Submodule.span ℂ {φ : archSmooth K n | IsAutomorphicForm φ.1 ∧
      (∀ k ∈ L, ∀ g, φ.1 (g * finEmb K n k) = φ.1 g) ∧
      (∀ g, (fun k : archCompact K n => φ.1 (g * infEmb K n k)) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ) ∧
      ∀ z ∈ (isExpLieAlgebra K n).centerU, uAction z φ = χ z • φ})

def AutTo : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a),
    IsAutForm φ → IsAutomorphicForm (K := E) (n := a) φ.1

def CptTo : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), ∃ e : archCompact E a ≃* Kinf E a,
    ∀ (φ : Sm E a) (k : archCompact E a) (g : GA E a), (cptRep E a (e k) φ).1 g = φ.1 (g * infEmb E a k)

def CentreTo : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), ∀ z ∈ (isExpLieAlgebra E a).centerU,
    ∃ z' ∈ Algebra.adjoin ℂ {x : Module.End ℂ (Sm E a) | ∃ τ u, x = cap τ u},
      ∀ (φ : Sm E a) (h : φ.1 ∈ archSmooth E a), (uAction z ⟨φ.1, h⟩).1 = (z' φ).1

theorem finite_coeffSpan {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G W) : FiniteDimensional ℂ (GlobalTheory.Published.AutFin.coeffSpan ρ) := by
  let m : Module.Dual ℂ W →ₗ[ℂ] W →ₗ[ℂ] (G → ℂ) :=
    LinearMap.mk₂ ℂ (fun ℓ w k => ℓ (ρ k w)) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
      (fun _ _ _ => by funext k; simp) (fun _ _ _ => by funext k; simp)
  refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range (TensorProduct.lift m)) (Submodule.span_le.2 ?_)
  rintro _ ⟨ℓ, w, rfl⟩
  exact ⟨ℓ ⊗ₜ w, rfl⟩

theorem coeffSpan_right {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W) :
    ∀ f ∈ GlobalTheory.Published.AutFin.coeffSpan ρ, ∀ k' : G, (fun k => f (k * k')) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ := by
  intro f hf k'
  have : GlobalTheory.Published.AutFin.coeffSpan ρ ≤ (GlobalTheory.Published.AutFin.coeffSpan ρ).comap (LinearMap.funLeft ℂ ℂ fun k => k * k') :=
    Submodule.span_le.2 (by
      rintro _ ⟨ℓ, w, rfl⟩
      exact Submodule.subset_span ⟨ℓ, ρ k' w, funext fun k => by simp [LinearMap.funLeft_apply]⟩)
  exact this hf

theorem charFinite_of (h : Fin.FormsFinite) : CharFinite := by
  intro K _ _ n L hL W _ _ _ ρ χ
  let S : Submodule ℂ (archSmooth K n) :=
    { carrier := {φ | IsAutomorphicForm φ.1 ∧ (∀ k ∈ L, ∀ g, φ.1 (g * finEmb K n k) = φ.1 g) ∧
        (∀ g, (fun k : archCompact K n => φ.1 (g * infEmb K n k)) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ) ∧
        ∀ z ∈ (isExpLieAlgebra K n).centerU, uAction z φ = χ z • φ}
      add_mem' := fun {φ ψ} p q => ⟨p.1.add q.1, fun k hk g => congrArg₂ (· + ·) (p.2.1 k hk g) (q.2.1 k hk g),
        fun g => add_mem (p.2.2.1 g) (q.2.2.1 g), fun z hz => by rw [map_add, p.2.2.2 z hz, q.2.2.2 z hz, smul_add]⟩
      zero_mem' := ⟨isAutomorphicForm_zero, fun _ _ _ => rfl, fun _ => zero_mem _, fun z _ => by simp⟩
      smul_mem' := fun c φ p => ⟨p.1.smul c, fun k hk g => congrArg (c * ·) (p.2.1 k hk g),
        fun g => Submodule.smul_mem _ c (p.2.2.1 g), fun z hz => by rw [map_smul, p.2.2.2 z hz, smul_comm]⟩ }
  have hS : FiniteDimensional ℂ S := h K n S
    ⟨fun φ p => p.1.isLeftInvariant, fun φ p => p.1.hasModerateGrowth, ⟨L, hL, fun φ p => p.2.1⟩,
      ⟨_, finite_coeffSpan ρ, coeffSpan_right ρ, fun φ p => p.2.2.1⟩,
      fun z hz => ⟨Polynomial.X - Polynomial.C (χ z), Polynomial.monic_X_sub_C _, fun φ p => by
        simp [p.2.2.2 z hz]⟩⟩
  exact Submodule.finiteDimensional_of_le (S₂ := S) (Submodule.span_le.2 fun _ p => p)

theorem finite_of (h0 : CharFinite) (h1 : AutTo) (h2 : CptTo) (h3 : CentreTo) :
    GlobalTheory.Published.AutomorphicFormsFiniteGL := by
  intro E _ _ _ a L hL W _ _ _ ρ _ c
  obtain ⟨e, he⟩ := h2 E a
  let S : Subalgebra ℂ (Module.End ℂ (Sm E a)) :=
    { carrier := {z | ∃ t : ℂ, ∀ φ : Sm E a, (∀ τ u, cap τ u φ = c τ u • φ) → z φ = t • φ}
      mul_mem' := by
        rintro x y ⟨s, hs⟩ ⟨t, ht⟩
        exact ⟨t * s, fun φ h => by rw [Module.End.mul_apply, ht φ h, map_smul, hs φ h, mul_smul]⟩
      add_mem' := by
        rintro x y ⟨s, hs⟩ ⟨t, ht⟩
        exact ⟨s + t, fun φ h => by rw [LinearMap.add_apply, ht φ h, hs φ h, add_smul]⟩
      algebraMap_mem' := fun t => ⟨t, fun φ _ => rfl⟩ }
  have hχ : ∀ z : UEnv E a, ∃ t : ℂ, z ∈ (isExpLieAlgebra E a).centerU → ∀ (φ : Sm E a) (h : φ.1 ∈ archSmooth E a),
      (∀ τ u, cap τ u φ = c τ u • φ) → uAction z ⟨φ.1, h⟩ = t • ⟨φ.1, h⟩ := by
    intro z
    by_cases hz : z ∈ (isExpLieAlgebra E a).centerU
    · obtain ⟨z', h4, h5⟩ := h3 E a z hz
      obtain ⟨t, ht⟩ : z' ∈ S := Algebra.adjoin_le (S := S) (by rintro _ ⟨τ, u, rfl⟩; exact ⟨c τ u, fun φ h => h τ u⟩) h4
      exact ⟨t, fun _ φ h hc => Subtype.ext ((h5 φ h).trans (congrArg Subtype.val (ht φ hc)))⟩
    · exact ⟨0, fun h => absurd h hz⟩
  choose χ hχ using hχ
  have hf := h0 E a L hL W (ρ.comp e.toMonoidHom) χ
  set T := Submodule.span ℂ {φ : archSmooth E a | IsAutomorphicForm φ.1 ∧
      (∀ k ∈ L, ∀ g, φ.1 (g * finEmb E a k) = φ.1 g) ∧
      (∀ g, (fun k : archCompact E a => φ.1 (g * infEmb E a k)) ∈ GlobalTheory.Published.AutFin.coeffSpan (ρ.comp e.toMonoidHom)) ∧
      ∀ z ∈ (isExpLieAlgebra E a).centerU, uAction z φ = χ z • φ}
  have hle : (Submodule.span ℂ (GlobalTheory.Published.AutFinGL.forms L ρ c)).map (Sm E a).subtype ≤ T.map (archSmooth E a).subtype := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨φ, ⟨p1, p2, p3, p4⟩, rfl⟩
    have hA := h1 E a φ p1
    refine ⟨⟨φ.1, hA.isSmooth.1⟩, Submodule.subset_span ⟨hA, fun k hk g => ?_, fun g => ?_,
      fun z hz => hχ z hz φ _ p4⟩, rfl⟩
    · change φ.1 (g * finEmb E a k) = φ.1 g
      rw [Fb.finEmb_eq]
      exact congrFun (congrArg Subtype.val (p2 k hk)) g
    · have hm : GlobalTheory.Published.AutFin.coeffSpan ρ ≤
          (GlobalTheory.Published.AutFin.coeffSpan (ρ.comp e.toMonoidHom)).comap (LinearMap.funLeft ℂ ℂ e) :=
        Submodule.span_le.2 (by rintro _ ⟨ℓ, w, rfl⟩; exact Submodule.subset_span ⟨ℓ, w, rfl⟩)
      have := hm (p3 g)
      simp only [← he]
      exact this
  have := Submodule.finiteDimensional_of_le hle
  exact Module.Finite.equiv (Submodule.equivMapOfInjective _ (Sm E a).injective_subtype _).symm

end UpperTheory.V.Af.CoefficientSpans
