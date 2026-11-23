import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobPullHomExtAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsTo
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactMapOfIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKerTorusExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianGenericExtendsOverOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusFiniteIdentityPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusTwistSmoothCurveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianGenericPullbackStatement

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.TwoSeq GlobalTheory.AbDatum
attribute [local instance] Over.cartesianMonoidalCategory

open scoped CategoryTheory.Obj

namespace GlobalTheory.DieuCover

theorem exists_cover_hasDieu : (∀ (O : Type) [CommRing O] (c : O →+* O) (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [IsAlgClosed k] [CharP k q] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] [IsIntegral C], IsSmoothProjCurve k C → ∀ (G₀ : Over C) [GrpObj G₀] [IsSemiAbelian G₀] (i₀ : OAct O G₀), AbGen c i₀ → ∀ (G : Over C) [GrpObj G] [IsSemiAbelian G] (i : OAct O G) (φ₀ : G.left ⟶ G₀.left), IsActPull i i₀ (frob C q (natCast_eq_zero C q k)) φ₀ → ∀ (U : C.Opens) (A : Over U.toScheme) [GrpObj A] (j : OAct O A) (φ : A.left ⟶ G.left) (h : IsGrpPullback A G U.ι φ), genericPoint C ∈ U → IsAbelianScheme A → IsActPull j i U.ι φ → ∀ P : LB (A ⊗ A).left, IsSelfDual c j P → ∀ (g : ℕ) (hg : IsVB (omega G) g) (d₀ : DieuDatumOn q k c i g U.ι), IsDRDatumOn q k c i j h P hg d₀ → ∀ x : C, x ∉ U → ∃ V : C.Opens, x ∈ V ∧ (∀ y ∈ V, y ≠ x → y ∈ U) ∧ ∃ d : DieuDatumOn q k c i g V.ι, ∃ ψ, Agree (b := C.homOfLE (inf_le_left : V ⊓ U ≤ V)) (c := C.homOfLE (inf_le_right : V ⊓ U ≤ U)) d d₀ (by simp) ψ) → GlobalTheory.CovTop.HypothesesXH → GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.CovHt.HypothesesH → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (q : ℕ) [Fact q.Prime], q ≠ 2 → ¬ q ∣ (discr E).natAbs → ∀ (k : Type) [Field k] [IsAlgClosed k] [CharP k q] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] [IsIntegral C], IsSmoothProjCurve k C → ∀ (G : Over C) [GrpObj G] [IsSemiAbelian G] (i : OAct (𝓞 E) G), AbGen (H.bar : 𝓞 E →+* 𝓞 E) i → ∃ (C₁ : Scheme.{0}) (_ : Algebra k Γ(C₁, ⊤)) (_ : IsIntegral C₁) (π : C₁ ⟶ C), IsSmoothProjCurve k C₁ ∧ IsCover k π ∧ ∃ (G₁ : Over C₁) (_ : GrpObj G₁) (_ : IsSemiAbelian G₁) (i₁ : OAct (𝓞 E) G₁) (φ : G₁.left ⟶ G.left), IsActPull i₁ i π φ ∧ HasDieu q k (H.bar : 𝓞 E →+* 𝓞 E) i₁ := by
  intro hbad p₁ p₂ _ E _ _ _ H q _ _ _ k _ _ _ C a _ hC G _ hG i hab
  have hlft : LocallyOfFiniteType (strHom k C) := by
    have := hC.smooth
    infer_instance
  obtain ⟨hfin, hpt⟩ := GlobalTheory.T.frobenius_finite_identity_points q k C hlft
  obtain ⟨a', hC', hstr⟩ := GlobalTheory.T.frobenius_twist_smooth_curve q k C hC
  have h0 : (q : Γ(C, ⊤)) = 0 := natCast_eq_zero C q k
  have := hG.comm
  have hS : IsSemiAbelian ((Over.pullback (frob C q h0)).obj G) := IsSemiAbelian.pullback (frob C q h0) G hG
  have hact := GlobalTheory.TorusPart.exists_isActPull (frob C q h0) i
  have hab' := GlobalTheory.T.abelian_generic_pullback _ _ C C (frob C q h0) (hpt _) G i _ _ _ hact hab
  refine ⟨C, a', inferInstance, frob C q h0, hC', ⟨hfin, ⟨fun x => ⟨x, hpt x⟩⟩, hstr⟩, _, _, hS, _, _, hact, ?_⟩
  clear hstr hfin hpt hlft hC
  clear a
  obtain ⟨U, A, _, j, φ, h, P, g, hg, d₀, hU, hA, hj, hP, hd⟩ :=
    GlobalTheory.T.abelian_generic_extends_over_open p₁ p₂ _ _ q k C hC' _ _ hab'
  exact hasDieu_of_points q k _ _ g hg U d₀ fun x hx =>
    hbad _ _ q k C hC' G i hab _ _ _ hact U A j φ h hU hA hj P hP g hg d₀ hd x hx

end GlobalTheory.DieuCover
