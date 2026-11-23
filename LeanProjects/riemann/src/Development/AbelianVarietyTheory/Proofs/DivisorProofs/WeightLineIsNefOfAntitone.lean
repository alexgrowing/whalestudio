import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArithVarHasHhUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelExpNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemipositiveOfIsometricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemipositiveNonnegCombinationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticHeightTensorAdditiveOnCurvesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagDeterminantNefOnFibresStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagDeterminantNonnegCurveDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagDeterminantEndpointsTrivialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightLineClassFlagDeterminantExpansionStatement

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CovTop GlobalTheory.FlagZ GlobalTheory.ArInt Formalism.DegreeFormula GlobalTheory.Cartier

noncomputable section

namespace GlobalTheory.FlagZ.WtNef

theorem isoSemiPos : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} (L M : GlobalTheory.HermLB p) (D : ℕ),
    L.Isometric M → L.SemiPos D → M.SemiPos D :=
  @GlobalTheory.T.semipositive_of_isometric

theorem combSemiPos : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} (ι : Type) [Fintype ι]
    (L : ι → GlobalTheory.HermLB p) (n : ι → ℤ) (D : ℕ), (∀ i, (L i).SemiPos D) → (∀ i, 0 ≤ n i) →
    (GlobalTheory.ArInt.comb L n).SemiPos D :=
  @GlobalTheory.T.semipositive_nonneg_combination

theorem curveHeightAdd : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ},
    GlobalTheory.IsArithVar p D → ∀ (L M : GlobalTheory.HermLB p) (h h' h'' : X → ℝ), L.IsArithHeight h → M.IsArithHeight h' →
    (L.tens M).IsArithHeight h'' → ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z],
    topologicalKrullDim Z = 1 → h'' (i (genericPoint Z)) = h (i (genericPoint Z)) + h' (i (genericPoint Z)) :=
  @GlobalTheory.T.arithmetic_height_tensor_additive_on_curves

theorem flDetNefFib : ∀ (ι : Type) [Fintype ι] (N : ℕ) (τ : ι) (l : Fin (N + 1)),
    GlobalTheory.ArInt.NefFib (flDet τ l : GlobalTheory.HermLB (flStr ι N)) :=
  @GlobalTheory.T.flag_determinant_nef_on_fibres

theorem flDetHoriz : ∀ (ι : Type) [Fintype ι] (N : ℕ) (τ : ι) (l : Fin (N + 1)) (Z : Scheme.{0})
    (i : Z ⟶ Fl ι N) [IsClosedImmersion i] [IsIntegral Z] [IsLocallyNoetherian Z], CharZero Γ(Z, ⊤) →
    topologicalKrullDim Z = 1 →
    ∃ (r : ((flDet τ l : GlobalTheory.HermLB (flStr ι N)).restr i).B.ι → Z.functionFieldˣ)
      (hr : IsRatSec ((flDet τ l : GlobalTheory.HermLB (flStr ι N)).restr i).B r),
      0 ≤ ((flDet τ l : GlobalTheory.HermLB (flStr ι N)).restr i).curveDeg hr :=
  @GlobalTheory.T.flag_determinant_nonneg_curve_degree

theorem flDetEnds : ∀ (ι : Type) [Fintype ι] (N : ℕ) (τ : ι),
    (flDet τ 0 : GlobalTheory.HermLB (flStr ι N)).Isometric (GlobalTheory.HermLB.triv _) ∧
    (flDet τ (Fin.last N) : GlobalTheory.HermLB (flStr ι N)).Isometric (GlobalTheory.HermLB.triv _) :=
  @GlobalTheory.T.flag_determinant_endpoints_trivial

theorem abelIcls : ∀ (ι : Type) [Fintype ι] (N : ℕ) (lam : ι → Fin N → ℤ), ∃ e₀ e₁ : ι → ℤ,
    (wtLine lam).icls = ∑ x : ι × Fin (N + 1), abelExp lam x • (flDet x.1 x.2 : GlobalTheory.HermLB (flStr ι N)).icls +
      ∑ τ, (e₀ τ • (flDet τ 0 : GlobalTheory.HermLB (flStr ι N)).icls +
        e₁ τ • (flDet τ (Fin.last N) : GlobalTheory.HermLB (flStr ι N)).icls) :=
  @GlobalTheory.T.weight_line_class_flag_determinant_expansion

theorem wtLine_isNef : Hypotheses2 → ∀ (ι : Type) [Fintype ι] (N : ℕ) (lam : ι → Fin N → ℤ),
    (∀ τ (a b : Fin N), a ≤ b → lam τ b ≤ lam τ a) → (wtLine lam).IsNef (dimFl ι N) := by
  intro hP ι _ N lam hlam
  have hX := (isArithVar_hasHh_unique ι N).1
  have HE : GlobalTheory.Published.ArExists := hP.p4.arExists
  have hF (x : ι × Fin (N + 1)) : (flDet x.1 x.2 : GlobalTheory.HermLB (flStr ι N)).IsNef (dimFl ι N) :=
    ⟨semiPos_detDual _ _ _ _, flDetNefFib ι N x.1 x.2,
      fun Z i _ _ _ hc hd => flDetHoriz ι N x.1 x.2 Z i hc hd⟩
  obtain ⟨e₀, e₁, he⟩ := abelIcls ι N lam
  have hiso : (comb (fun x : ι × Fin (N + 1) => (flDet x.1 x.2 : GlobalTheory.HermLB (flStr ι N)))
      (abelExp lam)).Isometric (wtLine lam) := by
    refine GlobalTheory.HermLB.icls_eq_iff.1 ?_
    have h0 (τ : ι) : (flDet τ 0 : GlobalTheory.HermLB (flStr ι N)).icls = 0 :=
      GlobalTheory.HermLB.icls_eq_iff.2 (flDetEnds ι N τ).1
    have h1 (τ : ι) : (flDet τ (Fin.last N) : GlobalTheory.HermLB (flStr ι N)).icls = 0 :=
      GlobalTheory.HermLB.icls_eq_iff.2 (flDetEnds ι N τ).2
    rw [icls_comb, he]
    simp only [h0, h1, smul_zero, add_zero, Finset.sum_const_zero]
  have hsp : (wtLine lam).SemiPos (dimFl ι N) :=
    isoSemiPos _ _ _ hiso (combSemiPos _ _ _ _ (fun x => (hF x).semiPos) (abelExp_nonneg lam hlam))
  have hex (L : GlobalTheory.HermLB (flStr ι N)) : ∃ h, L.IsArithHeight h :=
    (HE ℤ (Fl ι N) (flStr ι N) (dimFl ι N) hX).1 L
  obtain ⟨h, H⟩ := hex (wtLine lam)
  refine (H.isNef_iff hX).2 ⟨hsp, fun Z i _ _ hd => ?_⟩
  have hht {L : GlobalTheory.HermLB (flStr ι N)} {g : Fl ι N → ℝ} (G : L.IsArithHeight g) :
      (hex L).choose (i (genericPoint Z)) = g (i (genericPoint Z)) :=
    congrFun ((hex L).choose_spec.unique hX G) _
  let F₀ : GlobalTheory.HermLB.IsomClass (flStr ι N) → ℝ :=
    Quotient.lift (s := GlobalTheory.HermLB.isometrySetoid (flStr ι N)) (fun L => (hex L).choose (i (genericPoint Z)))
      fun L M e => (hht (e.isArithHeight hX (hex L).choose_spec)).symm
  let F : GlobalTheory.HermLB.IsomClass (flStr ι N) →+ ℝ := AddMonoidHom.mk' F₀ (by
    rintro ⟨L⟩ ⟨M⟩
    exact curveHeightAdd hX L M _ _ _ (hex L).choose_spec (hex M).choose_spec (hex _).choose_spec Z i hd)
  have hFL (L : GlobalTheory.HermLB (flStr ι N)) : F L.icls = (hex L).choose (i (genericPoint Z)) := rfl
  have key : h (i (genericPoint Z)) = ∑ y : ι × Fin (N + 1),
      (abelExp lam y : ℝ) * (hex (flDet y.1 y.2 : GlobalTheory.HermLB (flStr ι N))).choose (i (genericPoint Z)) := by
    rw [← hht H, ← hFL, ← GlobalTheory.HermLB.icls_eq_iff.2 hiso, icls_comb, map_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [map_zsmul, hFL, zsmul_eq_mul]
  rw [key]
  refine Finset.sum_nonneg fun y _ => mul_nonneg (by exact_mod_cast abelExp_nonneg lam hlam y) ?_
  exact (((hex _).choose_spec.isNef_iff hX).1 (hF y)).2 Z i hd

end GlobalTheory.FlagZ.WtNef
