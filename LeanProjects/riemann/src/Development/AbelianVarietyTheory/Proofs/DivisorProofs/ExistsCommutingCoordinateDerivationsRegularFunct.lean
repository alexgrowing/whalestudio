import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPreimageValueRulesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfValEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularFderivConstantVectorUniformisedStatement

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
open Filter Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem exists_commuting_derivations_of_values {R : Type} [CommRing R] [Algebra ℂ R] {g : ℕ} (P : Set (Fin g → ℂ))
    (v : R → (Fin g → ℂ) → ℂ) (hP : IsOpen P) (hd : ∀ x, DifferentiableOn ℂ (v x) P)
    (he : ∀ z ∈ P, ∃ e : R →ₐ[ℂ] ℂ, ∀ b, v b z = e b) (hinj : ∀ x, (∀ z ∈ P, v x z = 0) → x = 0)
    (hder : ∀ x w, ∃ y, ∀ z ∈ P, fderiv ℂ (v x) z w = v y z) :
    ∃ d : Fin g → Derivation ℂ R R, (∀ a b x, d a (d b x) = d b (d a x)) ∧
      ∀ a x, ∀ z ∈ P, v (d a x) z = fderiv ℂ (v x) z (Pi.single a 1) := by
  choose D hD using hder
  have hext : ∀ x y, (∀ z ∈ P, v x z = v y z) → x = y := fun x y h ↦ by
    refine sub_eq_zero.1 (hinj _ fun z hz ↦ ?_)
    obtain ⟨e, he⟩ := he z hz
    rw [he, map_sub, ← he, ← he, h z hz, sub_self]
  have hadd : ∀ x y, ∀ z ∈ P, v (x + y) z = v x z + v y z := fun x y z hz ↦ by
    obtain ⟨e, he⟩ := he z hz
    simp only [he, map_add]
  have hmul : ∀ x y, ∀ z ∈ P, v (x * y) z = v x z * v y z := fun x y z hz ↦ by
    obtain ⟨e, he⟩ := he z hz
    simp only [he, map_mul]
  have hsmul : ∀ (c : ℂ) x, ∀ z ∈ P, v (c • x) z = c • v x z := fun c x z hz ↦ by
    obtain ⟨e, he⟩ := he z hz
    simp only [he, map_smul]
  have hat : ∀ x, ∀ z ∈ P, DifferentiableAt ℂ (v x) z := fun x z hz ↦ (hd x).differentiableAt (hP.mem_nhds hz)
  have hcongr : ∀ (f k : (Fin g → ℂ) → ℂ), (∀ z ∈ P, f z = k z) → ∀ z ∈ P, fderiv ℂ f z = fderiv ℂ k z :=
    fun f k h z hz ↦ Filter.EventuallyEq.fderiv_eq (Filter.eventually_of_mem (hP.mem_nhds hz) h)
  let Dl : (Fin g → ℂ) → R →ₗ[ℂ] R := fun w ↦
    { toFun := fun x ↦ D x w
      map_add' := fun x y ↦ hext _ _ fun z hz ↦ by
        rw [hadd _ _ z hz, ← hD _ _ z hz, ← hD _ _ z hz, ← hD _ _ z hz,
          hcongr _ (v x + v y) (hadd x y) z hz, fderiv_add (hat x z hz) (hat y z hz)]
        rfl
      map_smul' := fun c x ↦ hext _ _ fun z hz ↦ by
        rw [RingHom.id_apply, hsmul _ _ z hz, ← hD _ _ z hz, ← hD _ _ z hz,
          hcongr _ (c • v x) (hsmul c x) z hz, fderiv_const_smul (hat x z hz)]
        rfl }
  have hL : ∀ w x y, Dl w (x * y) = x • Dl w y + y • Dl w x := fun w x y ↦ hext _ _ fun z hz ↦ by
    change v (D (x * y) w) z = v (x * D y w + y * D x w) z
    rw [hadd _ _ z hz, hmul _ _ z hz, hmul _ _ z hz, ← hD _ _ z hz, ← hD _ _ z hz, ← hD _ _ z hz,
      hcongr _ (v x * v y) (hmul x y) z hz, fderiv_mul (hat x z hz) (hat y z hz)]
    rfl
  have h2 : ∀ x w w', ∀ z ∈ P, v (D (D x w) w') z = fderiv ℂ (fderiv ℂ (v x)) z w' w := fun x w w' z hz ↦ by
    have ha : AnalyticAt ℂ (v x) z := ReciprocityTheory.AnForm.Osgood.osgood g P (v x) hP (hd x) z hz
    rw [← hD _ _ z hz, ← hcongr _ _ (hD x w) z hz,
      fderiv_clm_apply ha.fderiv.differentiableAt (differentiableAt_const w)]
    simp
  refine ⟨fun a ↦ Derivation.mk' (Dl (Pi.single a 1)) (hL _), fun a b x ↦ hext _ _ fun z hz ↦ ?_,
    fun a x z hz ↦ (hD x _ z hz).symm⟩
  have ha : AnalyticAt ℂ (v x) z := ReciprocityTheory.AnForm.Osgood.osgood g P (v x) hP (hd x) z hz
  change v (D (D x _) _) z = v (D (D x _) _) z
  rw [h2 _ _ _ z hz, h2 _ _ _ z hz]
  exact (ha.contDiffAt (n := ⊤)).isSymmSndFDerivAt le_top _ _

theorem exists_commuting_coordinate_derivations : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (U : A.left.Opens), ∃ d : Fin g → Derivation ℂ (Sec (str A) U) (Sec (str A) U), (∀ a b x, d a (d b x) = d b (d a x)) ∧ ∀ a x, ∀ z ∈ pre u.ex U, val u.ex U (d a x) z = fderiv ℂ (val u.ex U x) z (Pi.single a 1) := by
  intro A _ g L u hA U
  obtain ⟨h1, h2, -, -, -, -, -, -, -, h10, -⟩ := GlobalTheory.T.uniformisation_preimage_value_rules A g L u
  exact exists_commuting_derivations_of_values (R := Sec (str A) U) (pre u.ex U) (val u.ex U) (h1 U) (h2 U) (h10 U)
    (GlobalTheory.T.eq_zero_of_val_eq_zero_abelian A g L u hA U) (GlobalTheory.T.isRegular_fderiv_constant_vector_uniformised A g L u hA U)

end GlobalTheory.CechPer
