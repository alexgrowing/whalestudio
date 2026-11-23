import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AdmissibleBaseChartRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassifiedOnOpenOfSpecialisesToClassifiedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordFamilyFromRegularBaseCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsToricChartRingFactorisationLocalHomStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegeneratingFamilyDataFromBaseAlgClosedResidueStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon

theorem injective_of_flat_of_isDomain {A R : Type} [CommRing A] [IsDomain A] [CommRing R] [Nontrivial R] (ψ : A →+* R)
    (h : ψ.Flat) : Function.Injective ψ := by
  letI := ψ.toAlgebra
  haveI : Module.Flat A R := h
  refine (injective_iff_map_eq_zero ψ).2 fun a ha => ?_
  by_contra h0
  have hr := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := R) (mem_nonZeroDivisors_of_ne_zero h0)
  have h1 : a • (1 : R) = a • (0 : R) := by
    rw [Algebra.smul_def, Algebra.smul_def, mul_zero, _root_.mul_one]; exact ha
  exact one_ne_zero (hr h1)

theorem exists_canon_through : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → IsAlgClosed (ResidueField V) → ∀ (C : MonoFam Xo c φ V), Nontrivial C.P.D.toPre.X → ∃ (k : Type) (_ : Field k) (m e : ℕ) (C₁ : MonoFam Xo c φ (ChartRing k m e)) (θ : ChartRing k m e →+* V), Nonempty (Canon C₁) ∧ (∃ hm : C₁.m = m, ∀ i, C₁.s i = bdParam k m e (Fin.cast hm i)) ∧ IsLocalHom θ ∧ Through C C₁ θ := by
  intro E _ _ _ H Dw l Xo c φ V _ _ _ hV hk C hn
  obtain ⟨D', L, θ₀, N, ε, e, s, hp, hq, hθ₀, hb, hδ, hs, hu, hdiv⟩ := GlobalTheory.T.degeneratingFamily_data_from_base_algClosed_residue Xo c φ V hV hk C hn
  have hC₀ : (MvPolynomial.eval₂Hom θ₀ s).comp MvPolynomial.C = θ₀ := RingHom.ext fun a => MvPolynomial.eval₂Hom_C _ _ _
  have hsm : ∀ i, s (.inl i) ∈ maximalIdeal V := fun i => by
    obtain ⟨u, hu⟩ := (hs i).symm
    rw [← hu]; exact Ideal.mul_mem_right _ _ (C.s_mem i)
  have hs0 : ∀ i, s (.inl i) ≠ 0 := fun i h => C.s_ne_zero i ((hs i).eq_zero_iff.1 h)
  obtain ⟨k, _, e', ψ, θ, hcompl, hθ, hθψ, hψ, hbd⟩ := GlobalTheory.T.exists_toricChartRing_factorisation_localHom L.W ⟨L.b.comp (algebraMap ℚ c.F)⟩ C.m N V hV.1.2.2.2
    (MvPolynomial.eval₂Hom θ₀ s) (by rw [hC₀]; exact hθ₀) (fun i => by rw [MvPolynomial.eval₂Hom_X']; exact hsm i)
  have hθX : ∀ j, θ (ψ (MvPolynomial.X j)) = s j := fun j => by
    rw [← RingHom.comp_apply, hθψ, MvPolynomial.eval₂Hom_X']
  have hθC : θ.comp (ψ.comp MvPolynomial.C) = θ₀ := by rw [← RingHom.comp_assoc, hθψ, hC₀]
  have hinj : Function.Injective (ψ.comp MvPolynomial.C) :=
    (injective_of_flat_of_isDomain ψ hcompl.2.2.1).comp (MvPolynomial.C_injective _ _)
  let b₁ : c.F →+* ChartRing k C.m e' := (ψ.comp MvPolynomial.C).comp L.b
  have hR : GlobalTheory.Mum.Base (ChartRing k C.m e') :=
    ⟨GlobalTheory.MumfordChart.admissibleBase_chartRing k C.m e', (b₁.charZero_iff b₁.injective).1 inferInstance⟩
  have htor : ∀ j, IsUnit (ψ (MvPolynomial.X (.inr j))) := fun j => hθ.map_nonunit _ (by rw [hθX]; exact hu j)
  have hmem : ∀ i, ψ (MvPolynomial.X (.inl i)) ∈ maximalIdeal (ChartRing k C.m e') := fun i hi =>
    hsm i (by rw [← hθX]; exact hi.map θ)
  have hne : ∀ i, θ (ψ (MvPolynomial.X (.inl i))) ≠ 0 := fun i => by rw [hθX]; exact hs0 i
  have hval : ∀ i y, (ε (.inl i) : LinearMap.BilinForm ℤ L.D.X) y y = C.δ i (e.symm y) (e.symm y) := fun i y => by
    rw [hδ i]
    show _ = (ε (.inl i) : LinearMap.BilinForm ℤ L.D.X) (e (e.symm y)) (e (e.symm y))
    rw [e.apply_symm_apply]
  have hnn : ∀ i y, 0 ≤ (ε (.inl i) : LinearMap.BilinForm ℤ L.D.X) y y := fun i y => by
    rw [hval]; exact C.cone.nonneg i _
  have hpos : ∀ y, y ≠ 0 → 0 < ∑ i, (ε (.inl i) : LinearMap.BilinForm ℤ L.D.X) y y := fun y hy => by
    obtain ⟨i, hi⟩ := C.mono.exists_pos (maximalIdeal.isMaximal V).ne_top (y := e.symm y) (by simpa using hy)
    refine Finset.sum_pos' (fun j _ => hnn j y) ⟨i, Finset.mem_univ _, ?_⟩
    rw [hval]
    exact pos_of_mul_pos_left (by rw [mul_comm]; exact hi) (Int.natCast_nonneg l.M')
  obtain ⟨t₁, P₁, e₁, hdiv₁, hmono⟩ := GlobalTheory.T.mumford_family_from_regular_base_coordinates L (ChartRing k C.m e') hR (ψ.comp MvPolynomial.C) hinj C.m N
    (fun j => ψ (MvPolynomial.X j)) (fun j => (ε j : LinearMap.BilinForm ℤ L.D.X)) (fun j => (ε j).2)
    (fun i => ⟨hmem i, fun h => hne i (by rw [h, map_zero])⟩) htor hnn hpos e.injective.nontrivial
  obtain ⟨y₁, yo, κ, h₁, h₂, h₃, h₄, h₅⟩ := GlobalTheory.T.classified_on_open_of_specialises_to_classified Xo c φ D' L (ChartRing k C.m e') V hR hV C.toFam t₁ P₁
    (ψ.comp MvPolynomial.C) θ hθ (by rw [← RingHom.comp_assoc, hθC, hb]) C.m N (fun j => ψ (MvPolynomial.X j))
    (fun j => (ε j : LinearMap.BilinForm ℤ L.D.X)) e₁ e (fun j => (ε j).2) hne htor hdiv₁
    (by rw [hθC, funext hθX]; exact hdiv)
  have hrk : Module.finrank (𝓞 E) P₁.D.toPre.X = Module.finrank (𝓞 E) C.P.D.toPre.X := (e₁.trans e.symm).finrank_eq
  have hcone : IsCone H.bar φ fun i => pull e₁.toLinearMap (ε (.inl i) : LinearMap.BilinForm ℤ L.D.X) := by
    have h := C.cone.pull_equiv (e₁.trans e.symm)
    have he : (fun i => pull (e₁.trans e.symm).toLinearMap (C.δ i)) =
        fun i => pull e₁.toLinearMap (ε (.inl i) : LinearMap.BilinForm ℤ L.D.X) := by
      funext i
      rw [hδ i]
      refine LinearMap.ext₂ fun a b => ?_
      show (ε (.inl i) : LinearMap.BilinForm ℤ L.D.X) (e (e.symm (e₁ a))) (e (e.symm (e₁ b))) = _
      rw [e.apply_symm_apply, e.apply_symm_apply]
      rfl
    rwa [he] at h
  let C₁ : MonoFam Xo c φ (ChartRing k C.m e') :=
    ⟨⟨b₁, t₁, P₁, y₁, h₁, h₂⟩, C.m, fun i => ψ (MvPolynomial.X (.inl i)), hmem,
      fun i => pull e₁.toLinearMap (ε (.inl i) : LinearMap.BilinForm ℤ L.D.X), hcone, hrk.le.trans C.rank, hmono⟩
  exact ⟨k, _, C.m, e', C₁, θ, ⟨⟨D', by rw [← hp, ← hrk], by rw [← hq, ← hrk], L, N, ε, e₁, fun _ => rfl, ψ, hcompl, hψ,
    rfl, fun _ => rfl, htor, hdiv₁⟩⟩, ⟨rfl, hbd⟩, hθ, yo, κ, h₃, h₄, h₅⟩

end GlobalTheory.UCanon
