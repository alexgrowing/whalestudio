import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyTorusExtensionOfIsGt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantFieldCoefficientsOfLinearVectorFiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudTorusWeightZeroInvariantFieldCoeffsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VertCoeff

theorem isWt_sub {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
    {oa : Q.OAct O} (Y : Ray oa) (α : Q.X) (V : Y.H.left.Opens) (f g : Γ(Y.H.left, V)) (hf : IsWt Y α V f)
    (hg : IsWt Y α V g) : IsWt Y α V (f - g) := by
  intro S _ φ x x' c a a' ha ha' h h' hq hc
  have e : ∀ (b : Sp S ⟶ Y.H.left), valR b V (f - g) = valR b V f - valR b V g := fun b => by
    unfold valR; split_ifs <;> simp
  rw [e, e, hf S φ x x' c a a' ha ha' h h' hq hc, hg S φ x x' c a a' ha ha' h h' hq hc, mul_sub]

theorem lifts_sub_eq_sum_invFields : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (V : Q.P.A.left.Opens) (D : Derivation ℤ R R) (d d' : Fld Y.H.left), IsLift Y.H ⇑D (Y.q.left ⁻¹ᵁ V) d → IsLift Y.H ⇑D (Y.q.left ⁻¹ᵁ V) d' → (∀ (α : Q.X) (V' : Q.P.A.left.Opens), V' ≤ V → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (d _ f)) → (∀ (α : Q.X) (V' : Q.P.A.left.Opens), V' ≤ V → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (d' _ f)) → ∃ h : Fin n → Γ(Y.H.left, Y.q.left ⁻¹ᵁ V), (∀ a, IsWt Y 0 _ (h a)) ∧ ∀ (O' : Y.H.left.Opens), O' ≤ Y.q.left ⁻¹ᵁ V → ∀ f, d O' f - d' O' f = ∑ a, rsT (h a) O' * dd a O' f := by
  intro R _ _ Q O _ _ _ oa Y n v dd hdd V D d d' hd hd' hw hw'
  have hsm : Smooth Y.H.hom := (GlobalTheory.isSemiAbelian_of_isGt _ _ _ Y.isGt).smooth
  let δ : Fld Y.H.left := fun O f => d O f - d' O f
  have hF : IsField (Y.q.left ⁻¹ᵁ V) δ := by
    refine ⟨fun W hW f f' => ?_, fun W hW f f' => ?_, fun W W' h hW f => ?_⟩
    · simp only [δ, hd.1.1 W hW, hd'.1.1 W hW]; ring
    · simp only [δ, hd.1.2.1 W hW, hd'.1.2.1 W hW]; ring
    · simp only [δ, hd.1.2.2 W W' h hW, hd'.1.2.2 W W' h hW, map_sub]
  have hC : ∀ O, O ≤ Y.q.left ⁻¹ᵁ V → ∀ r, δ O (constFn Y.H.hom O r) = 0 := fun O hO r => by
    simp only [δ, hd.2 O hO r, hd'.2 O hO r, sub_self]
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_invariant_field_coefficients_of_linear_vectorField R Y.H hsm n v dd hdd _ δ hF hC
  refine ⟨c, GlobalTheory.T.raynaudTorusWeight_zero_invariantField_coeffs R Q O oa Y n v dd hdd V δ hF hC
    (fun α V' hV' f hf => isWt_sub Y α _ _ _ (hw α V' hV' f hf) (hw' α V' hV' f hf)) c hc, fun O' hO' f => hc O' hO' f⟩

end GlobalTheory.VertCoeff
