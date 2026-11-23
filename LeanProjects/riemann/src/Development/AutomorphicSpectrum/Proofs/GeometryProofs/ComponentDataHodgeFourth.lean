import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ContDiffUncentre
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeHermitianFormExistsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeInnerProductAdjointStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorGenericStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.InteriorPointPolarisedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.PhMuFree

open LieTangent in

theorem valAt_diff {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {L : Type} [AddCommGroup L] [Module Ω L] {M : LieModel G ξ L}
    {R : Type} [CommRing R] [IsLocalRing R] {z : Spec (CommRingCat.of R) ⟶ X} {f : G ⟶ G} [IsMonHom f]
    {A : L →ₗ[Ω] L} (hA : M.IsDiffOf f A) {e : L} {w : epsAt z ⟶ G} (h : M.ValAt z e w) :
    M.ValAt z (A e) (w ≫ f) := by
  rw [LieModel.valAt_iff] at *
  obtain ⟨h1, v, hv, rfl⟩ := h
  refine ⟨h1, v ≫ f, ?_, by rw [Category.assoc]⟩
  rw [LieModel.extends_iff] at *
  refine ⟨?_, by rw [hA e, hv.2, Category.assoc]⟩
  have h2 := hv.1
  rw [isTanAt_iff] at h2 ⊢
  rw [← Category.assoc, h2, one_comp]

theorem conj_ne_of_sq {x : ℂ} {d : ℕ} (hd : 0 < d) (hx : x ^ 2 = -(d : ℂ)) : starRingEnd ℂ x ≠ x := by
  intro h
  have him : x.im = 0 := Complex.conj_eq_iff_im.1 h
  have hre := congrArg Complex.re hx
  have : x = (x.re : ℂ) := Complex.ext rfl (by simpa using him)
  rw [this] at hre
  norm_cast at hre
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  simp at hre
  nlinarith [sq_nonneg x.re]

theorem bar_bar {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (a : 𝓞 E) : H.bar (H.bar a) = a := by
  apply RingOfIntegers.ext
  rw [H.bar_eq, H.bar_eq]
  simp

theorem val_eig {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
    {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y)
    {z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X} (hξ : IsCptGen 𝔐.ξ) (hg : genPt 𝔐.ξ ⤳ centre z)
    (s : CMType H ⊕ CMType H) (a : 𝓞 E) (t : 𝔐.X.presheaf.stalk (centre z))
    (ht : genMap 𝔐.ξ ⟨centre z, hg⟩ t = 𝔐.emb s a) {e : 𝔐.Li} (he : e ∈ 𝔐.Vgen s)
    {v : epsAt z ⟶ 𝔐.t.G} (hv : 𝔐.M.ValAt z e v) :
    v ≫ 𝔐.t.act.act a = LieTangent.epsScale z ((Scheme.stalkClosedPointTo z).hom t) ≫ v := by
  haveI := 𝔐.t.act.hom a
  have h1 := valAt_diff (𝔐.act a) hv
  have h2 := hv.smul hg t
  have e1 : 𝔐.ρ a e = genMap 𝔐.ξ ⟨centre z, hg⟩ t • e := by
    have h3 := (Submodule.mem_iInf _).1 he a
    rw [LinearMap.mem_ker] at h3
    rw [ht]
    simpa [sub_eq_zero] using h3
  rw [e1] at h1
  exact h1.unique hξ h2

theorem hodgeInnerProduct_blocks_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X) (τ : CMType H) (e e' : Or.𝔐.Li) (v v' : epsAt z ⟶ Or.𝔐.t.G) (a : ℂ), Or.𝔐.Interior z → e ∈ Or.𝔐.Vgen (Or.bg τ) → e' ∈ Or.𝔐.Vgen (Or.sm τ) → Or.𝔐.M.ValAt z e v → Or.𝔐.M.ValAt z e' v' → HodgeIP Or.𝔐.t.G Or.𝔐.t.PP.L z v v' a → a = 0 := by
  intro E _ _ _ H D l Xo c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or z τ e e' v v' a hz he he' hv hv' hI
  have hβ : Function.Injective (algebraMap (𝓞 c.F) c.F) := FaithfulSMul.algebraMap_injective _ _
  obtain ⟨-, -, hc0, -, -, -, -, hreg⟩ := GlobalTheory.T.hodge_cpt_interior_generic E H D l Xo c (𝓞 c.F) (algebraMap (𝓞 c.F) c.F) Y S₀ Ω K J Dc.y Or.𝔐 hβ
  haveI := hc0
  have hP := GlobalTheory.T.interior_point_polarised E H D l Xo c Y S₀ Ω K J Dc.y Or.𝔐 z hz
  have hg : genPt Or.𝔐.ξ ⤳ centre z := Or.𝔐.all _
  have hξ : IsCptGen Or.𝔐.ξ := Or.𝔐.tie.gen
  obtain ⟨Vz, _, _, ⟨MR⟩⟩ := lieModel_exists Or.𝔐.X Or.𝔐.t.G ℂ z
  obtain ⟨h, hHI, -, -⟩ := GlobalTheory.T.hodge_hermitian_form_exists E H Or.𝔐.X Or.𝔐.t z Vz MR hP
  obtain ⟨g, hgen⟩ := hreg (Sum.inl τ) H.rt ⟨centre z, hg⟩
  set x : ℂ := (Scheme.stalkClosedPointTo z).hom g with hx
  have hsq : g ^ 2 = -(H.d : Or.𝔐.X.presheaf.stalk (centre z)) := by
    apply hξ.inj ⟨centre z, hg⟩
    rw [map_pow, hgen, map_neg, map_natCast, ← map_pow, H.rt_sq, map_neg, map_natCast]
  have hx2 : x ^ 2 = -(H.d : ℂ) := by
    rw [hx, ← map_pow, hsq, map_neg, map_natCast]
  have hne : starRingEnd ℂ x ≠ x := conj_ne_of_sq H.d_prime.pos hx2
  have hin : ∀ b, Or.𝔐.emb (Sum.inr τ) b = Or.𝔐.emb (Sum.inl τ) (H.bar b) := fun _ => rfl
  have key : ∃ b, v ≫ Or.𝔐.t.act.act b = LieTangent.epsScale z x ≫ v ∧
      v' ≫ Or.𝔐.t.act.act (H.bar b) = LieTangent.epsScale z x ≫ v' := by
    rcases Or.side with ⟨hb, hs, -⟩ | ⟨hb, hs, -⟩
    · rw [hb] at he
      rw [hs] at he'
      refine ⟨H.rt, val_eig Or.𝔐 hξ hg (Sum.inl τ) _ g hgen he hv,
        val_eig Or.𝔐 hξ hg (Sum.inr τ) _ g ?_ he' hv'⟩
      rw [hin, bar_bar, hgen]
    · rw [hb] at he
      rw [hs] at he'
      refine ⟨H.bar H.rt, val_eig Or.𝔐 hξ hg (Sum.inr τ) _ g ?_ he hv, ?_⟩
      · rw [hin, bar_bar, hgen]
      · rw [bar_bar]
        exact val_eig Or.𝔐 hξ hg (Sum.inl τ) _ g hgen he' hv'
  obtain ⟨b, A1, A2⟩ := key
  obtain ⟨p, rfl⟩ := MR.onto v hv.isTanAt
  obtain ⟨p', rfl⟩ := MR.onto v' hv'.isTanAt
  have ha : a = h p p' := (hHI _ _ _).1 hI
  have hadj := GlobalTheory.T.hodge_inner_product_adjoint E H Or.𝔐.X Or.𝔐.t z (MR.pt p) (MR.pt p') b (h (x • p) p') hP (MR.tan p) (MR.tan p')
  rw [A1, A2, ← MR.pt_smul, ← MR.pt_smul] at hadj
  have e1 : h (x • p) p' = h p (x • p') := (hHI _ _ _).1 (hadj.1 ((hHI _ _ _).2 rfl))
  rw [map_smulₛₗ, map_smul] at e1
  simp only [LinearMap.smul_apply, smul_eq_mul] at e1
  rw [ha]
  have e2 : (starRingEnd ℂ x - x) * h p p' = 0 := by
    rw [sub_mul, e1, sub_self]
  exact (mul_eq_zero.1 e2).resolve_left (sub_ne_zero.2 hne)

end GlobalTheory.CompanionTheory.Ar.Cusp.PhMuFree
