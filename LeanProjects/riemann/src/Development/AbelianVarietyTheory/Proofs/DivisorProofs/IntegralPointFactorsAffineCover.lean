import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrdInjective

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.GroupBplus (AffOp)
open GlobalTheory.RingChain (RChain mv baseOf Qt IsFrobLin)
open GlobalTheory.ChainPts.PullHT (pullA)
open GlobalTheory.PerfdLat (piMap)
open scoped TensorProduct Pointwise
open GlobalTheory.ChainPts
open GlobalTheory.ChainDesc

namespace GlobalTheory.ChainDesc

theorem exists_extend_algClosed {A B K : Type} [CommRing A] [CommRing B] [Field K] [IsAlgClosed K] (g : A →+* B)
    (hg : Function.Injective g) (hi : g.IsIntegral) (ψ : A →+* K) : ∃ φ : B →+* K, φ.comp g = ψ := by
  letI := g.toAlgebra
  haveI : Algebra.IsIntegral A B := ⟨hi⟩
  haveI : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
  obtain ⟨Q, -, hQ, hQ'⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (R := A) (S := B) (RingHom.ker ψ) ⊥ (by
    intro x hx
    have : x = 0 := hg ((Ideal.mem_bot.1 hx).trans (map_zero g).symm)
    simp [this])
  haveI : Q.LiesOver (RingHom.ker ψ) := ⟨hQ'.symm⟩
  letI : Algebra (A ⧸ RingHom.ker ψ) K := (RingHom.kerLift ψ).toAlgebra
  haveI : FaithfulSMul (A ⧸ RingHom.ker ψ) K :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective ψ)
  haveI : Algebra.IsIntegral (A ⧸ RingHom.ker ψ) (B ⧸ Q) := inferInstance
  let l : (B ⧸ Q) →ₐ[A ⧸ RingHom.ker ψ] K := IsAlgClosed.lift
  refine ⟨l.toRingHom.comp (Ideal.Quotient.mk Q), RingHom.ext fun a => ?_⟩
  exact l.commutes (Ideal.Quotient.mk _ a)

theorem exists_extend_subring {A B K : Type} [CommRing A] [CommRing B] [Field K] [IsAlgClosed K] (g : A →+* B)
    (hg : Function.Injective g) (hi : g.IsIntegral) (R : Subring K) (hR : ∀ x : K, IsIntegral R x → x ∈ R)
    (ψ : A →+* R) : ∃ φ : B →+* R, φ.comp g = ψ := by
  obtain ⟨φ, hφ⟩ := exists_extend_algClosed g hg hi (R.subtype.comp ψ)
  refine ⟨φ.codRestrict R fun b => hR _ ?_, RingHom.ext fun a => Subtype.ext (RingHom.congr_fun hφ a)⟩
  obtain ⟨p, hp, hb⟩ := hi b
  refine ⟨p.map ψ, hp.map ψ, ?_⟩
  rw [Polynomial.eval₂_map]
  change p.eval₂ (R.subtype.comp ψ) (φ b) = 0
  rw [← hφ, ← Polynomial.hom_eval₂, hb, map_zero]

theorem exists_spMap_fromSpec {X : Scheme.{0}} {V : X.Opens} (hV : IsAffineOpen V) {R : Type} [CommRing R]
    (w : Sp R ⟶ X) (hw : ⊤ ≤ w ⁻¹ᵁ V) : ∃ ψ : Γ(X, V) →+* R, w = spMap ψ ≫ hV.fromSpec := by
  have h : Set.range w ⊆ Set.range hV.fromSpec := by
    rw [hV.range_fromSpec]
    rintro _ ⟨x, rfl⟩
    exact hw (Set.mem_univ x)
  refine ⟨(Spec.preimage (IsOpenImmersion.lift hV.fromSpec w h)).hom, ?_⟩
  change w = Spec.map (Spec.preimage (IsOpenImmersion.lift hV.fromSpec w h)) ≫ hV.fromSpec
  rw [Spec.map_preimage, IsOpenImmersion.lift_fac]

theorem IsCov.exists_extend : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (B B' : GlobalTheory.Vert.Model O) (f : GlobalTheory.Vert.Model.Hom B' B) (g : ∀ U : AffOp B.X, Γ(B'.X, f.f ⁻¹ᵁ U.1) →+* U.Bp) (k : IsCov f g) (K : Type) [Field K] [IsAlgClosed K] (R : Subring K), (∀ x : K, IsIntegral R x → x ∈ R) → ∀ (w : Sp R ⟶ B'.X) (U : AffOp B.X), ⊤ ≤ w ⁻¹ᵁ f.f ⁻¹ᵁ U.1 → ∃ φ : U.Bp →+* R, spMap φ ≫ U.toX = w ≫ f.f ∧ w = spMap (φ.comp (g U)) ≫ (k.isAffineOpen U).fromSpec := by
  intro O _ _ _ B B' f g k K _ _ R hR w U hw
  obtain ⟨ψ, rfl⟩ := exists_spMap_fromSpec (k.isAffineOpen U) w hw
  have e : (g U).comp (f.f.app U.1).hom = algebraMap Γ(B.X, U.1) U.Bp := RingHom.ext (k.2.2.2.1 U)
  have hi : (g U).IsIntegral := by
    refine RingHom.IsIntegral.tower_top (f.f.app U.1).hom (g U) ?_
    rw [e]
    exact Algebra.IsIntegral.isIntegral (R := Γ(B.X, U.1)) (A := U.Bp)
  obtain ⟨φ, hφ⟩ := exists_extend_subring (g U) (k.2.2.1 U) hi R hR ψ
  refine ⟨φ, ?_, by rw [hφ]⟩
  have h := IsAffineOpen.SpecMap_appLE_fromSpec f.f U.2.1 (k.isAffineOpen U) le_rfl
  rw [Scheme.Hom.appLE_eq_app] at h
  rw [Category.assoc, ← h, AffOp.toX, ← e, ← hφ]
  simp only [Cris.spMap_comp, Category.assoc]
  rfl

end GlobalTheory.ChainDesc
