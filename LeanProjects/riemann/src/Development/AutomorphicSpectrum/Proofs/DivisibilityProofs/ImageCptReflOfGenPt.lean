import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpPair
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import Development.AutomorphicSpectrum.Statements.GeometryStatements.PadicIntegersHenselianFiniteResidue
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SabMapId
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MapDomainRelationLiftCommutingSquare
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HodgeComponentFactorPointStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GenericPointFieldIsoStatement
open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Indep

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

theorem pp_monomial (M : Top.RootModel Ψ N) (II : IntersectionSystem) (m : Option (Ψ × Fin N) →₀ ℕ) (a : ℝ) :
    M.PP II (monomial m a) = a * limUnder (𝓝[>] (0:ℝ)) (fun t => M.arMono II t m) := by
  have : (monomial m a : Top.RPA Ψ N) = a • basisMonomials (Option (Ψ × Fin N)) ℝ m := by
    rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  rw [this, map_smul, Top.RootModel.PP, Module.Basis.constr_basis, smul_eq_mul]

end GlobalTheory.CompanionTheory.Ar.Indep

namespace GlobalTheory.CompanionTheory.Ar.Indep

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

theorem pp_toA_eq_of_tendsto (M M' : Top.RootModel Ψ N) (II : IntersectionSystem) (hconv : M.Converges II)
    (h : ∀ m : (Ψ × Fin N) →₀ ℕ, Tendsto (fun t => M.arMono II t (m.mapDomain some) -
      M'.arMono II t (m.mapDomain some)) (𝓝[>] (0:ℝ)) (𝓝 0)) (F : Top.RP Ψ N) :
    M.PP II (Top.toA F) = M'.PP II (Top.toA F) := by
  rw [F.as_sum]
  simp only [Top.toA, map_sum, rename_monomial, pp_monomial]
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  obtain ⟨L, hL⟩ := hconv (m.mapDomain some)
  have hL' : Tendsto (fun t => M'.arMono II t (m.mapDomain some)) (𝓝[>] (0:ℝ)) (𝓝 L) := by
    have := hL.sub (h m)
    simpa using this
  rw [hL.limUnder_eq, hL'.limUnder_eq]

end GlobalTheory.CompanionTheory.Ar.Indep

namespace GlobalTheory.CompanionTheory.Ar.Indep

theorem spectrumMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]; rfl

theorem cst_of_factor {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
    {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} (A : HodgeCpt Y S y)
    (hβ : Mono (spMap β)) (x : Sp A.Ω₀ ⟶ Xo.XF c) (hx : A.ξ₀ = x ≫ Y.j) :
    spMap A.fn ≫ x ≫ Limits.pullback.snd _ _ = spMap A.cst := by
  rw [← cancel_mono (spMap β), spectrumMap_comp, ← A.cst_over, ← Y.jQ_over]
  have h1 : A.ξ ≫ A.f = spMap A.fn ≫ x ≫ Y.jQ ≫ Limits.pullback.fst _ _ := by
    have := A.fn_over
    unfold GlobalTheory.CompanionTheory.Ar.Dominates at this
    rw [this, hx]; rfl
  have h2 := h1 =≫ Y.s
  simp only [Category.assoc] at h2 ⊢
  rw [← Limits.pullback.condition]
  exact h2.symm

theorem imageCpt_refl_of_genPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω Ω' : Type) [Field Ω] [Field Ω'] (K K' : Type) [Fintype K] [Fintype K'] (J : K → Type) (J' : K' → Type) (y : (Σ k, J k) → Ω) (y' : (Σ k, J' k) → Ω') (A : HodgeCpt Y S y) (A' : HodgeCpt Y S y'), Mono (spMap β) → genPt A.ξ₀ = genPt A'.ξ₀ → IsImageCpt (Iso.refl Xo.X) A A' := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω Ω' _ _ K K' _ _ J J' y y' A A' hβ hgen
  obtain ⟨x, hx⟩ := GlobalTheory.T.hodge_component_factor_point E H D l Xo c O β Y S Ω K J y A hβ
  obtain ⟨x', hx'⟩ := GlobalTheory.T.hodge_component_factor_point E H D l Xo c O β Y S Ω' K' J' y' A' hβ
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.generic_point_field_iso Y.X A.Ω₀ A'.Ω₀ A.ξ₀ A'.ξ₀ A.gen₀ A'.gen₀ hgen
  haveI : Mono Y.j := by
    haveI := hβ
    haveI := Y.jQ_open
    unfold Model.j
    infer_instance
  have hxx : spMap ψ.toRingHom ≫ x' = x := by
    rw [← cancel_mono Y.j, Category.assoc, ← hx', ← hx, hψ]
  refine ⟨x, x', ψ, hx, hx', ?_, ?_, cst_of_factor A hβ x hx, cst_of_factor A' hβ x' hx'⟩
  · rw [← Category.assoc, hxx]
    exact (congrArg (x ≫ ·) (Category.comp_id _)).symm
  · rw [← Category.assoc, hxx]

end GlobalTheory.CompanionTheory.Ar.Indep

namespace GlobalTheory.CompanionTheory.Ar.Indep

end GlobalTheory.CompanionTheory.Ar.Indep
