import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LnStepFalse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumLifts

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj
open GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Toroidal GlobalTheory.LocM.Frm GlobalTheory.HeightParts
open GlobalTheory.GradedNorm GlobalTheory.LieHt
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LieSmooth

namespace GlobalTheory.LieSmooth.HtEmb

variable {F : Type} [Field F] [NumberField F] {Y : Var F} {K : Type} [Field K] [NumberField K] {φ : F →+* K}
  (p : Sp K ⟶ Y.X) (hp : p ≫ Y.str = spMap φ)

include hp in

theorem isFinite_pt : IsFinite p := by
  letI := φ.toAlgebra
  have : IsScalarTower ℚ F K := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have : Module.Finite F K := Module.Finite.of_restrictScalars_finite ℚ F K
  have : IsFinite (p ≫ Y.str) := by
    rw [hp]
    exact (IsFinite.SpecMap_iff _).2 this
  exact IsFinite.of_comp p Y.str

theorem sum_over {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω] (σ : F →+* Ω)
    [Fintype {θ : K →+* Ω // θ.comp φ = σ}] (f : {y : Sp Ω ⟶ Y.X // y ≫ Y.str = spMap σ} → ℝ) :
    ∑ θ : {θ : K →+* Ω // θ.comp φ = σ},
        f ⟨spMap θ.1 ≫ p, by rw [Category.assoc, hp, ← Spec.map_comp]; exact congrArg spMap θ.2⟩ =
      p.residueDegree (IsLocalRing.closedPoint K) *
        ∑ᶠ (y : {y : Sp Ω ⟶ Y.X // y ≫ Y.str = spMap σ}) (_ : below y.1 = below p), f y := by
  have := isFinite_pt p hp
  have hw : IsClosed ({IsLocalRing.closedPoint K} : Set (Sp K)) := IsLocalRing.isClosed_singleton_closedPoint K
  rw [← finsum_subtype_eq_finsum_cond, ← finsum_eq_sum_of_fintype]
  refine Eq.trans ?_ (CoverHt.finsum_lifts σ p Y.str (IsLocalRing.closedPoint K) hw f)
  refine finsum_eq_of_bijective (fun θ => ⟨⟨spMap θ.1, by
    rw [hp, ← Spec.map_comp]; exact congrArg spMap θ.2⟩, Subsingleton.elim (α := PrimeSpectrum K) _ _⟩)
    ⟨fun a b h => ?_, ?_⟩ fun _ => rfl
  · have h1 : spMap a.1 = spMap b.1 := congrArg (fun t => t.1.1) h
    exact Subtype.ext (congrArg CommRingCat.Hom.hom (Spec.map_injective h1))
  · rintro ⟨⟨z, hz⟩, hz'⟩
    obtain ⟨χ, rfl⟩ := Spec.map_surjective z
    have h2 : Spec.map (CommRingCat.ofHom φ ≫ χ) = spMap σ := by
      rw [Spec.map_comp, ← hz, hp]
    exact ⟨⟨χ.hom, congrArg CommRingCat.Hom.hom (Spec.map_injective h2)⟩, rfl⟩

include hp in

theorem finrank_eq : (Module.finrank ℚ K : ℝ) = Module.finrank ℚ F *
    (p.residueDegree (IsLocalRing.closedPoint K) * Nat.card {y : AlgPt Y // below y.1 = below p}) := by
  classical
  have := isFinite_pt p hp
  have hw : IsClosed ({IsLocalRing.closedPoint K} : Set (Sp K)) := IsLocalRing.isClosed_singleton_closedPoint K
  have hx : IsClosed ({below p} : Set Y.X) := by
    have := p.isClosedMap _ hw
    exact (Set.image_singleton (f := p) (a := (IsLocalRing.closedPoint K : Sp K))) ▸ this
  have h := sum_over p hp (algebraMap F (AlgebraicClosure F)) fun _ => 1
  obtain ⟨_, _⟩ := ExtConj.pts Y _ hx
  have e (α : Type) [Finite α] : ∑ᶠ _ : α, (1 : ℝ) = Nat.card α := by
    have := Fintype.ofFinite α
    simp [finsum_eq_sum_of_fintype]
  rw [← finsum_subtype_eq_finsum_cond] at h
  have h' := h.trans (congrArg _ (e {y : AlgPt Y // below y.1 = below p}))
  rw [← h']
  letI := φ.toAlgebra
  have : IsScalarTower ℚ F K := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have : Module.Finite F K := Module.Finite.of_restrictScalars_finite ℚ F K
  have hc : Fintype.card {θ : K →+* AlgebraicClosure F // θ.comp φ = algebraMap F (AlgebraicClosure F)} =
      Module.finrank F K := by
    rw [← AlgHom.card F K (AlgebraicClosure F)]
    exact Fintype.card_congr ⟨fun θ => ⟨θ.1, fun a => RingHom.congr_fun θ.2 a⟩, fun a => ⟨a.toRingHom, a.comp_algebraMap⟩,
      fun _ => rfl, fun _ => rfl⟩
  rw [Finset.sum_const, Finset.card_univ, hc, ← Module.finrank_mul_finrank ℚ F K]
  simp

theorem main : ∀ {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F} (A : Adl C Y) {K : Type} [Field K] [NumberField K] (φ : F →+* K) (p : Sp K ⟶ Y.X) (hp : p ≫ Y.str = spMap φ), A.ht (below p) = -((∑ σ : K →+* ℂ, (Real.log (C.pn Y (σ.comp φ) A.D (A.m _) (C.cx Y _ ((eqn A.D (below p))⁻¹ : Y.Fnˣ)) (cxPtOf p hp σ)) / 2 - (A.n : ℕ) * A.ci (InfinitePlace.mk (σ.comp φ)))) + ∑ᶠ v : HeightOneSpectrum (𝓞 F), ∑ θ : EmbOver φ, A.lg v (extOf v) (algPtOf p hp θ)) / (((A.n : ℕ) : ℝ) * (Module.finrank ℚ K : ℝ)) := by
  intro F _ _ C Y A K _ _ φ p hp
  classical
  set d : ℝ := ((p.residueDegree (IsLocalRing.closedPoint K) : ℕ) : ℝ) with hd
  have h₁ : ∑ σ : K →+* ℂ, (Real.log (C.pn Y (σ.comp φ) A.D (A.m _) (C.cx Y _ ((eqn A.D (below p))⁻¹ : Y.Fnˣ))
      (cxPtOf p hp σ)) / 2 - (A.n : ℕ) * A.ci (InfinitePlace.mk (σ.comp φ))) =
      d * ∑ σ : F →+* ℂ, ∑ᶠ (z : Pts Y σ) (_ : Cartier.under z = below p),
        (Real.log (C.pn Y σ A.D (A.m σ) (C.cx Y σ ((eqn A.D (below p))⁻¹ : Y.Fnˣ)) z) / 2 -
          (A.n : ℕ) * A.ci (InfinitePlace.mk σ)) := by
    rw [Finset.mul_sum, ← Fintype.sum_fiberwise (fun σ : K →+* ℂ => σ.comp φ)]
    refine Finset.sum_congr rfl fun σ _ => Eq.trans ?_ (sum_over p hp σ fun z : Pts Y σ =>
      Real.log (C.pn Y σ A.D (A.m σ) (C.cx Y σ ((eqn A.D (below p))⁻¹ : Y.Fnˣ)) z) / 2 -
          (A.n : ℕ) * A.ci (InfinitePlace.mk σ))
    refine Finset.sum_congr rfl ?_
    rintro ⟨θ, rfl⟩ _
    rfl
  have h₂ : ∑ᶠ v : HeightOneSpectrum (𝓞 F), ∑ θ : EmbOver φ, A.lg v (extOf v) (algPtOf p hp θ) =
      d * ∑ᶠ v : HeightOneSpectrum (𝓞 F), if h : Nonempty (TrueGeo.Ext v) then
        ∑ᶠ (y : AlgPt Y) (_ : below y.1 = below p), A.lg v h.some y else 0 := by
    rw [mul_finsum]
    refine finsum_congr fun v => ?_
    rw [dif_pos (inferInstance : Nonempty (TrueGeo.Ext v))]
    exact @sum_over F _ _ Y K _ _ φ p hp _ _ _ _ (algebraMap F (AlgebraicClosure F))
      (inferInstanceAs (Fintype (EmbOver φ))) (A.lg v (extOf v))
  have h₃ := finrank_eq p hp
  have hK : (Module.finrank ℚ K : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have hd0 : d ≠ 0 := left_ne_zero_of_mul (right_ne_zero_of_mul (h₃ ▸ hK))
  rw [h₁, h₂, h₃, Adl.ht, ← mul_add, ← mul_neg, ← hd]
  rw [show ∀ a b c : ℝ, a * (b * (d * c)) = d * (a * b * c) from fun a b c => by ring, mul_div_mul_left _ _ hd0]

end GlobalTheory.LieSmooth.HtEmb

end
