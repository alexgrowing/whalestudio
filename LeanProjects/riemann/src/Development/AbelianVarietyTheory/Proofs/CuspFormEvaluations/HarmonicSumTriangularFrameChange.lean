import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndBC
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsCombAtGMulVec
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsNatCastSmulCoeffIsIntegral
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.InvariantOperatorValueTriangularChangeStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TriangularFrame

theorem basis_of_triangular {T : Type} [Fintype T] {r : T → ℕ} {S : Type} [CommRing S] {d : ℕ}
    (u : (Σ τ : T, Fin (r τ)) → Fin d → S) (cf : ∀ τ : T, Fin (r τ) → Fin (r τ) → S)
    (h0 : ∀ τ i j, i < j → cf τ i j = 0) (h1 : ∀ τ i, IsUnit (cf τ i i))
    (hb : ∀ v : Fin d → S, ∃! a : (Σ τ : T, Fin (r τ)) → S, ∀ j, ∑ ℓ, a ℓ * u ℓ j = v j) (v : Fin d → S) :
    ∃! a : (Σ τ : T, Fin (r τ)) → S, ∀ e, ∑ ℓ, a ℓ * (∑ j, cf ℓ.1 ℓ.2 j * u ⟨ℓ.1, j⟩ e) = v e := by
  classical
  have hdet : ∀ τ, IsUnit (Matrix.of (cf τ)).det := fun τ => by
    rw [Matrix.det_of_lowerTriangular (Matrix.of (cf τ)) (fun i j hij => h0 τ i j (by simpa using hij))]
    exact IsUnit.prod_iff.2 fun i _ => h1 τ i
  have key : ∀ (a : (Σ τ : T, Fin (r τ)) → S) e, ∑ ℓ, a ℓ * (∑ j, cf ℓ.1 ℓ.2 j * u ⟨ℓ.1, j⟩ e) =
      ∑ ℓ : (Σ τ : T, Fin (r τ)), Matrix.vecMul (fun i => a ⟨ℓ.1, i⟩) (Matrix.of (cf ℓ.1)) ℓ.2 * u ℓ e := by
    intro a e
    rw [Fintype.sum_sigma, Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul]
    simp only [_root_.mul_assoc]
    exact Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun (i j : Fin (r τ)) => a ⟨τ, i⟩ * (cf τ i j * u ⟨τ, j⟩ e))
  simp only [key]
  obtain ⟨b, hb1, hb2⟩ := hb v
  have back : ∀ a : (Σ τ : T, Fin (r τ)) → S,
      (∀ e, ∑ ℓ : (Σ τ : T, Fin (r τ)), Matrix.vecMul (fun i => a ⟨ℓ.1, i⟩) (Matrix.of (cf ℓ.1)) ℓ.2 * u ℓ e = v e) →
      a = fun ℓ => Matrix.vecMul (fun i => b ⟨ℓ.1, i⟩) (Matrix.of (cf ℓ.1))⁻¹ ℓ.2 := by
    intro a ha
    have := hb2 _ ha
    subst this
    funext ℓ
    show _ = Matrix.vecMul (Matrix.vecMul (fun i => a ⟨ℓ.1, i⟩) (Matrix.of (cf ℓ.1))) _ _
    rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ (hdet _), Matrix.vecMul_one]
  refine ⟨fun ℓ => Matrix.vecMul (fun i => b ⟨ℓ.1, i⟩) (Matrix.of (cf ℓ.1))⁻¹ ℓ.2, fun e => ?_, back⟩
  rw [← hb1 e]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  congr 1
  show Matrix.vecMul (Matrix.vecMul (fun i => b ⟨ℓ.1, i⟩) (Matrix.of (cf ℓ.1))⁻¹) _ _ = _
  rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (hdet _), Matrix.vecMul_one]

theorem fst_comp_jetTan {S : Type} [CommRing S] {κ : Type} [DecidableEq κ] (ℓ : κ) :
    (TrivSqZeroExt.fstHom S S S).comp (jetTan ℓ : Jet S κ (0 + 1) →ₐ[S] DualNumber S) = jetAug := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  show TrivSqZeroExt.fst (MvPolynomial.aeval
    (fun i => if i = ℓ then (DualNumber.eps : DualNumber S) else 0) (MvPolynomial.X i : MvPolynomial κ S)) =
    MvPolynomial.aeval (fun _ => (0 : S)) (MvPolynomial.X i : MvPolynomial κ S)
  by_cases h : i = ℓ <;> simp [h]

theorem left_one {T : Scheme.{0}} {X : Over T} {M : Over T} [GrpObj M] : (1 : X ⟶ M).left = X.hom ≫ η[M].left := by
  show (toUnit X ≫ η[M]).left = _
  rw [Over.comp_left]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem isTanAt_jetTan {S : Type} [CommRing S] (x0 : Sp S ⟶ Xo.X) {κ : Type} [DecidableEq κ]
    (x : overAt x0 (Jet S κ (0 + 1)) ⟶ Xo.univ.t.G)
    (hx : homAt x0 (jetAug : Jet S κ (0 + 1) →ₐ[S] S) ≫ x = 1) (ℓ : κ) :
    IsTanAt x0 (homAt x0 (jetTan ℓ : Jet S κ (0 + 1) →ₐ[S] DualNumber S) ≫ x).left := by
  refine ⟨Over.w _, ?_⟩
  have h1 := congrArg (fun f => f.left) hx
  simp only [Over.comp_left, left_one] at h1 ⊢
  have e : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫
      (homAt x0 (jetTan ℓ : Jet S κ (0 + 1) →ₐ[S] DualNumber S)).left =
      (homAt x0 (jetAug : Jet S κ (0 + 1) →ₐ[S] S)).left := by
    rw [← fst_comp_jetTan ℓ]
    exact (Spec.map_comp _ _).symm
  refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ x.left) e)).trans (h1.trans ?_)
  have e' : spMap (algebraMap S S) = 𝟙 _ := Spec.map_id _
  show (spMap (algebraMap S S) ≫ x0) ≫ _ = x0 ≫ _
  rw [e', Category.id_comp]

theorem eq_of_isPullSec_id {X : Scheme.{0}} (A : Over X) [GrpObj A] (L : LB A.left) (k : ℤ) (T : Over X)
    (F F' : LB.Sec (LPow A L k T)) (h : IsPullSec A L k (𝟙 T ▷ A) (whiskerRight_snd _ _) F F') : F' = F := by
  have key : ∀ (g : T ⊗ A ⟶ T ⊗ A) (hg : g ≫ snd T A = snd T A), g = 𝟙 _ → IsPullSec A L k g hg F F' → F' = F := by
    intro g hg e h
    subst e
    obtain ⟨f, hf⟩ := F
    obtain ⟨f', hf'⟩ := F'
    congr
    funext j
    refine (h j).trans ?_
    show ((T ⊗ A).left.presheaf.map (𝟙 _)).hom (f j) = f j
    rw [CategoryTheory.Functor.map_id]
    rfl
  exact key _ _ (MonoidalCategory.id_whiskerRight _ _) h

theorem sum_eq (hC : ChartIndepSt2) [StarRing (𝓞 E)] (nab : NabV Xo c) (hnab : IsNab Xo c nab)
    {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (ho u' h1 h2 h3 s' h4)
    (cf : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Fin (Dw.mult τ) → S)
    (h0 : ∀ τ i j, i < j → cf τ i j = 0) (hu : ∀ τ i, IsUnit (cf τ i i))
    (hcomb : ∀ τ i, IsCombAt y.x (y.u τ) (cf τ i) (u' τ i)) (n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ)
    (P : MvPolynomial (LtN Dw n) c.F)
    (hP : P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) (k : ℕ)
    (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) :
    ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) *
        ∏ b, nab (⟨y.x, ho, u', h1, h2, h3, s', h4⟩ : FrPt Xo c S) k (F b) (colOf m b) =
      (∏ ℓ : Lt1 Dw, cf ℓ.1 ℓ.2 ℓ.2 ^ a (ℓ.1, ℓ.2)) *
        ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y k (F b) (colOf m b) := by
  letI : Algebra ℚ S := ((algebraMap c.F S).comp (algebraMap ℚ c.F)).toAlgebra
  set y' : FrPt Xo c S := ⟨y.x, ho, u', h1, h2, h3, s', h4⟩ with hy'
  obtain ⟨C, hex, hpin⟩ := hnab.2 S y
  obtain ⟨C', hex', hpin'⟩ := hnab.2 S y'
  choose f hf using fun b => hex k (F b)
  choose f' hf' using fun b => hex' k (F b)
  let uv : Lt1 Dw → Fin C.d → S := fun ℓ e => ∑ j, cf ℓ.1 ℓ.2 j * C.uvec ⟨ℓ.1, j⟩ e
  let D : ChartAt Xo c y' :=
    ⟨C.d, C.B, uv, C.x, C.e, C.wP, C.h,
      ⟨C.chart.zero, C.chart.trunc, C.chart.law, C.chart.act, fun ℓ => by
        have := GlobalTheory.TangentLinear.isCombAt_mulVec E H Dw l Xo S y.x _
          (fun j => isTanAt_jetTan y.x (C.x 1) (C.chart.zero 1) ((0 : Fin 1), j)) (y.u ℓ.1)
          (Matrix.of fun e j => C.uvec ⟨ℓ.1, j⟩ e) (cf ℓ.1 ℓ.2) (u' ℓ.1 ℓ.2)
          (fun i => C.chart.tan ⟨ℓ.1, i⟩) (hcomb ℓ.1 ℓ.2)
        have e : (Matrix.of fun e j => C.uvec ⟨ℓ.1, j⟩ e).mulVec (cf ℓ.1 ℓ.2) = uv ℓ := by
          funext e
          simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, uv]
          exact Finset.sum_congr rfl fun j _ => _root_.mul_comm _ _
        rw [e] at this
        exact this,
        basis_of_triangular C.uvec cf h0 hu C.chart.basis⟩,
      ⟨C.frame.gen, C.frame.ph1, C.frame.ph2, C.frame.sy, C.frame.ad⟩, C.prim, C.gauge, C.rig0⟩
  obtain ⟨N, hN, hNP, hsupp⟩ := GlobalTheory.exists_natCast_smul_mem_harmA E H Dw l c a n P hP
  have hI := hC E H Dw l Xo c hnab.1 S y' C' D k n F f' f hf' hf a _ hNP
  have hNu : IsUnit (algebraMap c.F S (N : c.F)) :=
    (IsUnit.mk0 (N : c.F) (Nat.cast_ne_zero.2 hN.ne')).map _
  have hsc : ∀ (C₀ : ChartAt Xo c y') (g : Fin n → MvPowerSeries (Fin 1 × Fin C₀.d) S),
      chartVal C₀ k g ((N : c.F) • P) = algebraMap c.F S (N : c.F) * chartVal C₀ k g P := by
    intro C₀ g
    simp only [chartVal, hsupp, MvPolynomial.coeff_smul, smul_eq_mul, map_mul, Finset.mul_sum, _root_.mul_assoc]
  rw [hsc, hsc] at hI
  have hI' := hNu.mul_left_cancel hI
  have e₁ : ∀ m, ∏ b, nab y k (F b) (colOf m b) =
      ∏ b, C.B.nabVal S C.h H.w0 k (f b) C.uvec (MvPolynomial.monomial (colOf m b) 1) := fun m =>
    Finset.prod_congr rfl fun b _ => hpin k (F b) (f b) (hf b) (colOf m b)
  have e₂ : ∀ m, ∏ b, nab y' k (F b) (colOf m b) =
      ∏ b, C'.B.nabVal S C'.h H.w0 k (f' b) C'.uvec (MvPolynomial.monomial (colOf m b) 1) := fun m =>
    Finset.prod_congr rfl fun b _ => hpin' k (F b) (f' b) (hf' b) (colOf m b)
  simp only [e₁]
  exact (Finset.sum_congr rfl fun m _ => congrArg _ (e₂ m)).trans <| hI'.trans (GlobalTheory.T.invariantOperator_value_triangular_change E H Dw l c S C.d C.B C.h C.gauge k n f C.uvec uv cf h0 (fun _ _ _ => rfl) hu a P hP)

theorem harmonic_sum_frBor : ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (S : Type) [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S) (t : Ix Dw → Sˣ), FrBor t y y' → ∀ (h : ptO Xo y'.x ⟶ ptO Xo y.x), h.left = 𝟙 _ → ∀ (n : ℕ), ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∀ (N : ℕ) (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))) (F' : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y'.x))), (∀ b, IsPullSec Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) (F b) (F' b)) → ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y' ((N : ℤ) ^ 2) (F' b) (colOf m b) = (∏ ℓ : Lt1 Dw, ((t (some ℓ) : Sˣ) : S) ^ a (ℓ.1, ℓ.2)) * ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y ((N : ℤ) ^ 2) (F b) (colOf m b) := by
  intro hC E _ _ _ H Dw l Xo c _ nab hnab S _ _ y y' t hb h hh n a P hP N
  obtain ⟨x', ho, u', h1, h2, h3, s', h4⟩ := y'
  obtain ⟨hx, hcf, -⟩ := hb
  dsimp only at hx
  subst hx
  choose cf hd h0 hcomb using hcf
  have e : h = 𝟙 _ := Over.OverMorphism.ext hh
  subst e
  have hk : ((N : ℤ) ^ 2) = ((N ^ 2 : ℕ) : ℤ) := (Nat.cast_pow N 2).symm
  generalize ((N : ℤ) ^ 2) = K at hk
  subst hk
  intro F F' hF
  have hFF : F' = F := funext fun b => eq_of_isPullSec_id _ _ _ _ _ _ (hF b)
  subst hFF
  have := sum_eq hC nab hnab y ho u' h1 h2 h3 s' h4 cf h0 (fun τ i => by rw [hd]; exact Units.isUnit _) hcomb
    n a P hP (N ^ 2) F'
  simp only [hd] at this
  exact this

end GlobalTheory.TriangularFrame
