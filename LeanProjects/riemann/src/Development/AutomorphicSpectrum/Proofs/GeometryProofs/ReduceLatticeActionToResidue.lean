import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeAt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

section EvalRank

variable {E : Type} [Field E] [NumberField E]

theorem trace_eigProj {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : 𝓞 E →+* Module.End K V) (σ : E →+* K) :
    LinearMap.trace K V (HT.eigProj ρ σ) = (Module.finrank K (HT.eigSp ρ σ) : K) := by
  have h : LinearMap.IsProj (HT.eigSp ρ σ) (HT.eigProj ρ σ) :=
    ⟨fun x => HT.LatBasic.eigProj_mem ρ σ x, fun x hx => HT.LatBasic.eigProj_of_mem hx⟩
  exact h.trace

theorem trace_eigProj_eq_sum {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (ρ : 𝓞 E →+* Module.End K V) (σ : E →+* K) :
    LinearMap.trace K V (HT.eigProj ρ σ) =
      ∑ k, σ (HT.dualInt E k) * LinearMap.trace K V (ρ (RingOfIntegers.basis E k)) := by
  simp [HT.eigProj, map_sum, map_smul]

variable {Ω Vs C : Type} [Field Ω] [AddCommGroup Vs] [Module Ω Vs] [Field C]

theorem comb_single {R : Subring Ω} {g : ℕ} (ℓ : Fin g → Vs) (j : Fin g) :
    comb (R := R) ℓ (Pi.single j 1) = ℓ j := by
  classical
  unfold comb
  rw [Finset.sum_eq_single j (fun i _ h => by simp [Pi.single_apply, h]) (by simp)]
  simp

theorem exists_comb {R : Subring Ω} {g : ℕ} {ℓ : Fin g → Vs} {v : Vs}
    (h : v ∈ Submodule.span R (Set.range ℓ)) : ∃ x : Fin g → R, v = comb ℓ x := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 h
  exact ⟨c, by rw [← hc]; rfl⟩

theorem trace_of_comb {R : Subring Ω} {g : ℕ} {ℓ : Fin g → Vs} (hl : LinearIndependent Ω ℓ)
    (hs : Submodule.span Ω (Set.range ℓ) = ⊤) (f : Module.End Ω Vs) (x : Fin g → Fin g → R)
    (hx : ∀ j, f (ℓ j) = comb ℓ (x j)) :
    LinearMap.trace Ω Vs f = ((∑ j, x j j : R) : Ω) := by
  classical
  set b := Module.Basis.mk hl hs.ge with hb
  have hbj : ∀ j, b j = ℓ j := fun j => by simp [hb]
  rw [LinearMap.trace_eq_matrix_trace Ω b f, Matrix.trace]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, hbj, hx j, comb]
  simp only [← hbj, map_sum, map_smul, Module.Basis.repr_self]
  simp [Finsupp.single_apply]

theorem trace_of_cols {g : ℕ} (f : Module.End C (Fin g → C)) (y : Fin g → Fin g → C)
    (hy : ∀ j, f (Pi.single j 1) = y j) :
    LinearMap.trace C (Fin g → C) f = ∑ j, y j j := by
  classical
  rw [LinearMap.trace_eq_matrix_trace C (Pi.basisFun C (Fin g)) f, Matrix.trace]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  simp [hy j]

end EvalRank

theorem finrank_eigSp_eval : ∀ (E : Type) [Field E] [NumberField E] (Ω Vs C : Type) [Field Ω] [CharZero Ω] [AddCommGroup Vs] [Module Ω Vs]
    [FiniteDimensional Ω Vs] [Field C] [CharZero C] (ρ : 𝓞 E →+* Module.End Ω Vs) (R' : Subring Ω) (g : ℕ)
    (ℓ : Fin g → Vs) (ψ : R' →+* C) (ρC : 𝓞 E →+* Module.End C (Fin g → C)) (σ : E →+* Ω) (σC : E →+* C),
    LinearIndependent Ω ℓ → Submodule.span Ω (Set.range ℓ) = ⊤ →
    (∀ a i, ρ a (ℓ i) ∈ Submodule.span R' (Set.range ℓ)) → Tied ℓ ψ ρ ρC →
    (∀ e : E, ∃ h : σ e ∈ R', ψ ⟨σ e, h⟩ = σC e) →
    Module.finrank C (HT.eigSp ρC σC) = Module.finrank Ω (HT.eigSp ρ σ) := by
  intro E _ _ Ω Vs C _ _ _ _ _ _ _ ρ R' g ℓ ψ ρC σ σC hl hs hst hT hσ
  classical
  choose M hM using fun (a : 𝓞 E) (j : Fin g) => exists_comb (hst a j)
  have hC : ∀ a j, ρC a (Pi.single j 1) = fun i => ψ (M a j i) := by
    intro a j
    have := hT a (Pi.single j 1) (M a j) (by rw [comb_single]; exact hM a j)
    rw [← this]
    congr 1
    ext i
    by_cases h : i = j
    · subst h; simp
    · simp [Pi.single_apply, h]
  have tΩ : ∀ a, LinearMap.trace Ω Vs (ρ a) = ((∑ j, M a j j : R') : Ω) :=
    fun a => trace_of_comb hl hs (ρ a) (M a) (hM a)
  have tC : ∀ a, LinearMap.trace C (Fin g → C) (ρC a) = ψ (∑ j, M a j j) := by
    intro a
    rw [trace_of_cols (ρC a) (fun j i => ψ (M a j i)) (hC a), map_sum]
  set T : R' := ∑ k, ⟨σ (HT.dualInt E k), (hσ _).1⟩ * ∑ j, M (RingOfIntegers.basis E k) j j with hTdef
  have h1 : (Module.finrank Ω (HT.eigSp ρ σ) : Ω) = (T : Ω) := by
    rw [← trace_eigProj, trace_eigProj_eq_sum, hTdef]
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [tΩ]
    push_cast
    rfl
  have h2 : T = (Module.finrank Ω (HT.eigSp ρ σ) : R') := by
    apply Subtype.ext
    rw [← h1]
    simp
  have h3 : (Module.finrank C (HT.eigSp ρC σC) : C) = ψ T := by
    rw [← trace_eigProj, trace_eigProj_eq_sum, hTdef, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [tC, map_mul]
    congr 1
    exact ((hσ _).2).symm
  rw [h2, map_natCast] at h3
  exact_mod_cast h3

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
