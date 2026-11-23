import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.ConeClosed

theorem exists_homogenisation {k J : Type} [Field k] (i : J) (P : MvPolynomial J k) :
    ∃ (n : ℕ) (Q : MvPolynomial J k), ∀ w : J → k, w i ≠ 0 →
      MvPolynomial.eval w Q = w i ^ n * MvPolynomial.eval (fun j => w j / w i) P := by
  induction P using MvPolynomial.induction_on with
  | C a => exact ⟨0, MvPolynomial.C a, fun w _ => by simp⟩
  | add P P' h h' =>
    obtain ⟨n, Q, hQ⟩ := h
    obtain ⟨n', Q', hQ'⟩ := h'
    refine ⟨n + n', MvPolynomial.X i ^ n' * Q + MvPolynomial.X i ^ n * Q', fun w hw => ?_⟩
    simp only [map_add, map_mul, map_pow, MvPolynomial.eval_X, hQ w hw, hQ' w hw]
    ring
  | mul_X P j h =>
    obtain ⟨n, Q, hQ⟩ := h
    refine ⟨n + 1, Q * MvPolynomial.X j, fun w hw => ?_⟩
    simp only [map_mul, MvPolynomial.eval_X, hQ w hw]
    field_simp
    ring

def constHom {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) (U : X.Opens) : k →+* Γ(X, U) :=
  (p.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom

theorem constHom_apply {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) (U : X.Opens) (a : k) :
    constHom p U a = constFn p U a := rfl

theorem exists_point {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) {U : X.Opens}
    (hU : IsAffineOpen U) (φ : Γ(X, U) →+* k) (hφ : ∀ a, φ (constFn p U a) = a) :
    ∃ x : Sp k ⟶ X, x ≫ p = 𝟙 _ ∧ ⊤ ≤ x ⁻¹ᵁ U ∧ ∀ f, GlobalTheory.ZH.valR x U f = φ f := by
  let ψ : Γ(X, U) ⟶ CommRingCat.of k := CommRingCat.ofHom φ
  have hx := GlobalTheory.Points.le_preimage_specMap_fromSpec hU ψ
  have hv : ∀ f, ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR (Spec.map ψ ≫ hU.fromSpec) U f = φ f := fun f => by
    rw [GlobalTheory.Points.valR_eq _ U hx, GlobalTheory.Points.valMap_specMap_fromSpec]
    rfl
  refine ⟨Spec.map ψ ≫ hU.fromSpec, ?_, hx, hv⟩
  rw [← Spec.map_preimage ((Spec.map ψ ≫ hU.fromSpec) ≫ p), ← Spec.map_id]
  congr 1
  ext a
  rw [← GlobalTheory.Points.valR_constFn p _ U hx, hv, hφ]
  rfl

theorem valR_eval₂ {k J : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) {U : X.Opens}
    (x : Sp k ⟶ X) (hp : x ≫ p = 𝟙 _) (hx : ⊤ ≤ x ⁻¹ᵁ U) (r : J → Γ(X, U)) (P : MvPolynomial J k) :
    GlobalTheory.ZH.valR x U (MvPolynomial.eval₂Hom (constHom p U) r P) =
      MvPolynomial.eval (fun j => GlobalTheory.ZH.valR x U (r j)) P := by
  have e : (CrdCalc.valHom x U hx).comp (MvPolynomial.eval₂Hom (constHom p U) r) =
      MvPolynomial.eval (fun j => GlobalTheory.ZH.valR x U (r j)) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_)
    · rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, MvPolynomial.eval_C, ← CrdCalc.valR_eq]
      exact GlobalTheory.Points.valR_constFn_of_section p x hp U hx a
    · rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_X', MvPolynomial.eval_X, ← CrdCalc.valR_eq]
  rw [CrdCalc.valR_eq x U hx, ← e]
  rfl

theorem mem_cone_of_vanishing : (∀ (k : Type) [Field k] [IsAlgClosed k] (X : Scheme.{0}) (p : X ⟶ Sp k) (H : LB X) (J : Type) [Fintype J] (s : J → H.Sec) (J₀ : Set J), H.IsLB → ImmBy p H s J₀ → ∀ v : J → k, (∃ i ∈ J₀, v i ≠ 0) → (∀ Pf ∈ MvPolynomial.vanishingIdeal k (cone p H s), MvPolynomial.eval v Pf = 0) → v ∈ cone p H s) := by
  intro k _ _ X p H J _ s J₀ hH him v ⟨i, hi, hvi⟩ hv
  obtain ⟨hU, r, hr, hgen⟩ := him.2 i hi
  let Φ : MvPolynomial J k →+* Γ(X, (Out.nonzeroLocus (s i))) := MvPolynomial.eval₂Hom (constHom p (Out.nonzeroLocus (s i))) r
  have hsurj : Function.Surjective Φ := by
    rw [← RingHom.range_eq_top, eq_top_iff, ← hgen, Subring.closure_le]
    rintro _ (⟨a, rfl⟩ | ⟨j, rfl⟩)
    · exact ⟨MvPolynomial.C a, MvPolynomial.eval₂Hom_C _ _ _⟩
    · exact ⟨MvPolynomial.X j, MvPolynomial.eval₂Hom_X' _ _ _⟩
  have hker : RingHom.ker Φ ≤ RingHom.ker (MvPolynomial.eval fun j => v j / v i) := by
    intro P hP
    obtain ⟨n, Q, hQ⟩ := exists_homogenisation i P
    have hmem : MvPolynomial.X i * Q ∈ MvPolynomial.vanishingIdeal k (cone p H s) := by
      rw [MvPolynomial.mem_vanishingIdeal_iff]
      rintro w ⟨x, hp, hw⟩
      rw [MvPolynomial.aeval_eq_eval, map_mul, MvPolynomial.eval_X]
      by_cases hwi : w i = 0
      · rw [hwi, zero_mul]
      have hx : ⊤ ≤ x ⁻¹ᵁ (Out.nonzeroLocus (s i)) := (CrdCalc.crd_isUnit_iff i hw).1 (Ne.isUnit hwi)
      have e : (fun j => w j / w i) = fun j => GlobalTheory.ZH.valR x (Out.nonzeroLocus (s i)) (r j) := funext fun j => by
        rw [CrdCalc.crd_ratio hw (hr j) hx, mul_div_cancel_right₀ _ hwi]
      rw [hQ w hwi, e, ← valR_eval₂ p x hp hx r P, RingHom.mem_ker.1 hP, CrdCalc.valR_eq x (Out.nonzeroLocus (s i)) hx, map_zero,
        mul_zero, mul_zero]
    have h := hv _ hmem
    rw [map_mul, MvPolynomial.eval_X, hQ v hvi] at h
    exact (mul_eq_zero.1 ((mul_eq_zero.1 h).resolve_left hvi)).resolve_left (pow_ne_zero _ hvi)
  let φ : Γ(X, (Out.nonzeroLocus (s i))) →+* k := Φ.liftOfSurjective hsurj ⟨_, hker⟩
  have hφ : ∀ P, φ (Φ P) = MvPolynomial.eval (fun j => v j / v i) P := fun P =>
    RingHom.liftOfSurjective_comp_apply Φ hsurj ⟨_, hker⟩ P
  obtain ⟨x, hp, hx, hval⟩ := exists_point p hU φ fun a => by
    have := hφ (MvPolynomial.C a)
    rwa [MvPolynomial.eval_C, show Φ (MvPolynomial.C a) = constFn p (Out.nonzeroLocus (s i)) a from
      MvPolynomial.eval₂Hom_C _ _ _] at this
  obtain ⟨w, hw⟩ := CrdCalc.crd_exists hH s x
  have hwi : w i ≠ 0 := ((CrdCalc.crd_isUnit_iff i hw).2 hx).ne_zero
  refine ⟨x, hp, ?_⟩
  have h := CrdCalc.crd_smul (Units.mk0 (v i / w i) (div_ne_zero hvi hwi)) hw
  convert h using 2 with j
  have h₁ := hφ (MvPolynomial.X j)
  rw [MvPolynomial.eval_X, show Φ (MvPolynomial.X j) = r j from MvPolynomial.eval₂Hom_X' _ _ _] at h₁
  rw [CrdCalc.crd_ratio hw (hr j) hx, hval, h₁, Units.val_mk0]
  field_simp

end GlobalTheory.ZH.ConeClosed
end
