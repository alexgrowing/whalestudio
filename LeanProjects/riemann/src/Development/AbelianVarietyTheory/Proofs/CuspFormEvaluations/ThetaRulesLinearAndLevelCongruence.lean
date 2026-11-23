import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaValueNaturalAlgebraMap
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointBaseChangeUniqueReflIff
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaRule

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.RunIn

attribute [local instance] Over.cartesianMonoidalCategory

section Lin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem monomial_degree_of_mem_harm {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {P : MvPolynomial (LtN Dw n) c.F}
    (hP : P ∈ harmA (Dw := Dw) c a n) {m : LtN Dw n →₀ ℕ} (hm : m ∈ P.support) :
    (m.sum fun _ e => e) = ∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), a (τ, i) := by
  have hrow := hP.1.2.2 m hm
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun i _ => hrow τ i

theorem totalDegree_of_mem_harm {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {P : MvPolynomial (LtN Dw n) c.F}
    (hP : P ∈ harmA (Dw := Dw) c a n) (h0 : P ≠ 0) :
    P.totalDegree = ∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), a (τ, i) := by
  obtain ⟨m0, hm0⟩ := Finset.nonempty_iff_ne_empty.2 (mt MvPolynomial.support_eq_empty.1 h0)
  unfold MvPolynomial.totalDegree
  refine le_antisymm (Finset.sup_le fun m hm => (monomial_degree_of_mem_harm hP hm).le) ?_
  rw [← monomial_degree_of_mem_harm hP hm0]
  exact Finset.le_sup (f := fun s : LtN Dw n →₀ ℕ => s.sum fun _ e => e) hm0

theorem thExpr_eq_sum_superset (nab : NabV Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo y.x)))
    {P : MvPolynomial (LtN Dw n) c.F} (hP : P ∈ harmA (Dw := Dw) c a n) (U : Finset (LtN Dw n →₀ ℕ))
    (hU : P.support ⊆ U) :
    thExpr Xo c nab y P F = algebraMap c.F S (((l.M : c.F) ^ (∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), a (τ, i)))⁻¹) *
      ∑ m ∈ U, algebraMap c.F S (P.coeff m) * ∏ b, nab y ((l.M : ℤ) ^ 2) (F b) (colOf m b) := by
  unfold thExpr
  rw [Finset.sum_subset hU (fun m _ hm => by rw [MvPolynomial.notMem_support_iff.1 hm, map_zero, zero_mul])]
  by_cases h0 : P = 0
  · subst h0; simp
  · rw [totalDegree_of_mem_harm hP h0]

theorem thExpr_linear (nab : NabV Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo y.x)))
    {N : ℕ} (cf : Fin N → c.F) (Q : Fin N → MvPolynomial (LtN Dw n) c.F) (hQ : ∀ i, Q i ∈ harmA (Dw := Dw) c a n)
    {P : MvPolynomial (LtN Dw n) c.F} (hP : P ∈ harmA (Dw := Dw) c a n) (hsum : ∑ i, cf i • Q i = P) :
    thExpr Xo c nab y P F = ∑ i, algebraMap c.F S (cf i) * thExpr Xo c nab y (Q i) F := by
  classical
  set U := P.support ∪ Finset.univ.biUnion fun i => (Q i).support
  have hQU : ∀ i, (Q i).support ⊆ U := fun i =>
    (Finset.subset_biUnion_of_mem (fun i => (Q i).support) (Finset.mem_univ i)).trans Finset.subset_union_right
  rw [thExpr_eq_sum_superset nab y F hP U Finset.subset_union_left]
  simp only [fun i => thExpr_eq_sum_superset nab y F (hQ i) U (hQU i)]
  subst hsum
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, smul_eq_mul, map_sum, map_mul, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => by ring

theorem thValAt_linear (hC : ChartIndepSt2) [StarRing (𝓞 E)] (nab : NabV Xo c) (hnab : IsNab Xo c nab)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (x : Fin n → Dw.La)
    {N : ℕ} (cf : Fin N → c.F) (Q : Fin N → MvPolynomial (LtN Dw n) c.F) (hQ : ∀ i, Q i ∈ harmA (Dw := Dw) c a n)
    {P : MvPolynomial (LtN Dw n) c.F} (hP : P ∈ harmA (Dw := Dw) c a n) (hsum : ∑ i, cf i • Q i = P)
    {S : Type} [CommRing S] [Algebra c.F S] (y0 : FrPt Xo c S) {v : S} (hv : ThValAt Xo c nab y0 x P v)
    (vi : Fin N → S) (hvi : ∀ i, ThValAt Xo c nab y0 x (Q i) (vi i)) :
    v = ∑ i, algebraMap c.F S (cf i) * vi i := by
  obtain ⟨S', _, _, φ, y', F, hff, hmap, hV, he⟩ := hv
  have hrefl : FrMap (AlgHom.id c.F S') y' y' :=
    (GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c S' S' (AlgHom.id c.F S') y').2.1
  have e1 : ∀ i, φ (vi i) = thExpr Xo c nab y' (Q i) F := fun i =>
    GlobalTheory.thetaValue_natural GlobalTheory.abelianSchemeLaws_all.1 hC E H Dw l Xo c nab hnab S S' φ y0 y' hmap a n x (Q i) (hQ i)
      _ _ (hvi i) ⟨S', inferInstance, inferInstance, AlgHom.id c.F S', y', F,
        RingHom.FaithfullyFlat.of_bijective Function.bijective_id, hrefl, hV, rfl⟩
  apply hff.injective
  show φ v = φ (∑ i, algebraMap c.F S (cf i) * vi i)
  rw [he, thExpr_linear nab y' F cf Q hQ hP hsum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, AlgHom.commutes, e1 i]

theorem levPt_eq_of_sub_mem {S : Type} [CommRing S] (x0 : Sp S ⟶ Xo.X) {u u' : Dw.La}
    (h : u - u' ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) : levPt Xo x0 u = levPt Xo x0 u' := by
  have e : Xo.univ.eta u = Xo.univ.eta u' := by
    have h1 := Xo.univ.eta_add (u - u') u'
    rw [sub_add_cancel, Xo.univ.eta_ker _ h, _root_.one_mul] at h1
    exact h1
  unfold levPt
  rw [e]

end Lin

theorem isThRule_linear_and_congr : ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), (∀ (x : Fin n → Dw.La) (m : ℕ) (cf : Fin m → c.F) (Q : Fin m → MvPolynomial (LtN Dw n) c.F) (f : Rul Xo c) (g : Fin m → Rul Xo c), (∀ i, Q i ∈ harmA c a n) → (∑ i, cf i • Q i) ∈ harmA c a n → IsThRule Xo c nab x (∑ i, cf i • Q i) f → (∀ i, IsThRule Xo c nab x (Q i) (g i)) → f = ∑ i, cf i • g i) ∧ ∀ (x x' : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F) (f : Rul Xo c), (∀ b, x b - x' b ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) → IsThRule Xo c nab x P f → IsThRule Xo c nab x' P f := by
  intro hC E _ _ _ H Dw l Xo c _ nab hnab a n
  refine ⟨fun x m cf Q f g hQ hP hf hg => ?_, fun x x' P f hx hf p y => ?_⟩
  · funext p y
    rw [thValAt_linear hC nab hnab x cf Q hQ hP rfl y (hf p y) (fun i => g i p y) (fun i => hg i p y)]
    rw [Finset.sum_apply, Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => (Algebra.smul_def (cf i) (g i p y)).symm
  · obtain ⟨S', _, _, φ, y', F, hff, hmap, hV, he⟩ := hf p y
    exact ⟨S', inferInstance, inferInstance, φ, y', F, hff, hmap,
      fun b => levPt_eq_of_sub_mem (Xo := Xo) y'.x (hx b) ▸ hV b, he⟩

end GlobalTheory.ThetaRule
