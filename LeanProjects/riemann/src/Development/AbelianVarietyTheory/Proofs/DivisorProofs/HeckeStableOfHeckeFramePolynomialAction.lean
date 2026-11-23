import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices

set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial

namespace GlobalTheory.ExpFrame

theorem map_mk_smul_sum {O A : Type} [CommRing O] [Ring A] [Algebra O A] {V W : Type} [AddCommGroup V] [Module O V] [Module A V]
    [IsScalarTower O A V] [AddCommGroup W] [Module O W] [Module A W] [IsScalarTower O A W] (U : Submodule A V)
    (ψ : U →ₗ[A] W) {κ : Type} (S : Finset κ) (c : O) (v : κ → V) (hv : ∀ s, v s ∈ U) (x : V) (hx : x ∈ U)
    (e : x = c • ∑ s ∈ S, v s) : c • ∑ s ∈ S, ψ ⟨v s, hv s⟩ = ψ ⟨x, hx⟩ := by
  have e' : (⟨x, hx⟩ : U) = c • ∑ s ∈ S, (⟨v s, hv s⟩ : U) := by
    apply Subtype.ext
    simpa using e
  rw [e', LinearMap.map_smul_of_tower, map_sum]

section
variable {O A G I : Type} [CommRing O] [Ring A] [Algebra O A] [Group G] (Γ : Subgroup G) {K : Subgroup G} (jK : K →* A)
  (tr : I → Finset G) (cst : I → O)

theorem hecke_values_mem {V : Type} [AddCommGroup V] [Module O V] [Module A V]
    [IsScalarTower O A V] [Module (MvPolynomial I O) (Forms O Γ jK V)]
    (hV : (∀ (c : O) (f : Forms O Γ jK V), (C c : MvPolynomial I O) • f = c • f) ∧
      ∀ i (f : Forms O Γ jK V) (g : G), (((X i : MvPolynomial I O) • f : Forms O Γ jK V) : G → V) g =
        cst i • ∑ s ∈ tr i, (f : G → V) (g * s))
    (U : Submodule A V) (t : MvPolynomial I O) :
    ∀ f : Forms O Γ jK V, (∀ g, (f : G → V) g ∈ U) →
      ∀ g, ((t • f : Forms O Γ jK V) : G → V) g ∈ U := by
  induction t using MvPolynomial.induction_on with
  | C c =>
    intro f hf g
    rw [hV.1 c f]
    exact U.smul_of_tower_mem c (hf g)
  | add p q hp hq =>
    intro f hf g
    rw [add_smul]
    exact U.add_mem (hp f hf g) (hq f hf g)
  | mul_X p i hp =>
    intro f hf g
    rw [mul_smul]
    apply hp
    intro g'
    rw [hV.2 i f g']
    exact U.smul_of_tower_mem _ (U.sum_mem fun s _ => hf _)

theorem hecke_values_map {V W : Type} [AddCommGroup V] [Module O V] [Module A V]
    [IsScalarTower O A V] [Module (MvPolynomial I O) (Forms O Γ jK V)]
    [AddCommGroup W] [Module O W] [Module A W]
    [IsScalarTower O A W] [Module (MvPolynomial I O) (Forms O Γ jK W)]
    (hV : (∀ (c : O) (f : Forms O Γ jK V), (C c : MvPolynomial I O) • f = c • f) ∧
      ∀ i (f : Forms O Γ jK V) (g : G), (((X i : MvPolynomial I O) • f : Forms O Γ jK V) : G → V) g =
        cst i • ∑ s ∈ tr i, (f : G → V) (g * s))
    (hW : (∀ (c : O) (f : Forms O Γ jK W), (C c : MvPolynomial I O) • f = c • f) ∧
      ∀ i (f : Forms O Γ jK W) (g : G), (((X i : MvPolynomial I O) • f : Forms O Γ jK W) : G → W) g =
        cst i • ∑ s ∈ tr i, (f : G → W) (g * s))
    (U : Submodule A V)
    (ψ : U →ₗ[A] W) (t : MvPolynomial I O) :
    ∀ (f : Forms O Γ jK V) (φ : Forms O Γ jK W)
      (hf : ∀ g, (f : G → V) g ∈ U), (∀ g, (φ : G → W) g = ψ ⟨(f : G → V) g, hf g⟩) →
      ∀ g (h : ((t • f : Forms O Γ jK V) : G → V) g ∈ U),
        ((t • φ : Forms O Γ jK W) : G → W) g = ψ ⟨_, h⟩ := by
  induction t using MvPolynomial.induction_on with
  | C c =>
    intro f φ hf hφ g h
    have e : (⟨_, h⟩ : U) = c • ⟨(f : G → V) g, hf g⟩ := by
      apply Subtype.ext
      simp only [hV.1 c f]
      rfl
    rw [e, LinearMap.map_smul_of_tower, ← hφ g, hW.1 c φ]
    rfl
  | add p q hp hq =>
    intro f φ hf hφ g h
    have hp' := hecke_values_mem Γ jK tr cst hV U p f hf g
    have hq' := hecke_values_mem Γ jK tr cst hV U q f hf g
    have e : (⟨_, h⟩ : U) = ⟨_, hp'⟩ + ⟨_, hq'⟩ := by
      apply Subtype.ext
      simp only [add_smul]
      rfl
    rw [e, map_add, ← hp f φ hf hφ g hp', ← hq f φ hf hφ g hq', add_smul]
    rfl
  | mul_X p i hp =>
    intro f φ hf hφ g h
    have hX := hecke_values_mem Γ jK tr cst hV U (X i) f hf
    have hφX : ∀ g', (((X i : MvPolynomial I O) • φ : Forms O Γ jK W) : G → W) g' = ψ ⟨_, hX g'⟩ := by
      intro g'
      refine (hW.2 i φ g').trans (Eq.trans ?_ (map_mk_smul_sum U ψ (tr i) (cst i) (fun s => (f : G → V) (g' * s))
        (fun s => hf _) _ (hX g') (hV.2 i f g')))
      exact congrArg (fun z => cst i • z) (Finset.sum_congr rfl fun s _ => hφ (g' * s))
    have h2 : ((p • ((X i : MvPolynomial I O) • f) : Forms O Γ jK V) : G → V) g ∈ U := by
      rw [← mul_smul]
      exact h
    have e : (⟨_, h⟩ : U) = ⟨_, h2⟩ := by
      apply Subtype.ext
      simp only [mul_smul]
    rw [e, mul_smul]
    exact hp _ _ hX hφX g h2

theorem hecke_stable_nat (V W : Type) [AddCommGroup V] [Module O V] [Module A V]
    [IsScalarTower O A V] [Module (MvPolynomial I O) (Forms O Γ jK V)]
    [AddCommGroup W] [Module O W] [Module A W]
    [IsScalarTower O A W] [Module (MvPolynomial I O) (Forms O Γ jK W)]
    (hV : (∀ (c : O) (f : Forms O Γ jK V), (C c : MvPolynomial I O) • f = c • f) ∧
      ∀ i (f : Forms O Γ jK V) (g : G), (((X i : MvPolynomial I O) • f : Forms O Γ jK V) : G → V) g =
        cst i • ∑ s ∈ tr i, (f : G → V) (g * s))
    (hW : (∀ (c : O) (f : Forms O Γ jK W), (C c : MvPolynomial I O) • f = c • f) ∧
      ∀ i (f : Forms O Γ jK W) (g : G), (((X i : MvPolynomial I O) • f : Forms O Γ jK W) : G → W) g =
        cst i • ∑ s ∈ tr i, (f : G → W) (g * s)) :
    HeckeStable O Γ jK (MvPolynomial I O) V ∧ HeckeNat O Γ jK (MvPolynomial I O) V W :=
  ⟨fun U t f hf => hecke_values_mem Γ jK tr cst hV U t f hf,
    fun U ψ t f φ hf hf' hφ g => hecke_values_map Γ jK tr cst hV hW U ψ t f φ hf hφ g (hf' g)⟩

end

set_option maxHeartbeats 1000000 in

theorem heckeStable_heckeNat_of_isHecke : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (lam : ι → ℕ → ℕ) (jK : F.K →* alg F.O N lam) [Module F.T (Forms F.O (A := alg F.O N lam) F.Γ jK (NablaT F.O N lam))] (W : Type) [AddCommGroup W] [Module F.O W] [Module (alg F.O N lam) W] [IsScalarTower F.O (alg F.O N lam) W] [Module F.T (Forms F.O (A := alg F.O N lam) F.Γ jK W)], F.IsHecke lam jK (NablaT F.O N lam) → F.IsHecke lam jK W → HeckeStable F.O (A := alg F.O N lam) F.Γ jK F.T (NablaT F.O N lam) ∧ HeckeNat F.O (A := alg F.O N lam) F.Γ jK F.T (NablaT F.O N lam) W := by
  intro l _ ι _ _ N F lam jK i1 W i2 i3 i4 i5 i6 hV hW
  refine @hecke_stable_nat F.O (alg F.O N lam) F.G F.I _ _ _ _ F.Γ F.K jK F.tr F.cst (NablaT F.O N lam) W _ _ _ _ _ _ _ _ _ _ ?_ ?_
  · exact hV
  · exact hW

end GlobalTheory.ExpFrame
