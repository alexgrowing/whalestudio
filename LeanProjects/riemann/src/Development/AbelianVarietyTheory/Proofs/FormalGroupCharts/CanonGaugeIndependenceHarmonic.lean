import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.WickOperatorVanishing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GEWick
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.HStable
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.HarmSecond
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CanonGaugeSubIsBiadd
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CanonGaugeIndependenceAll

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory

section Adjoint

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
  {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]

theorem bilinPart_sub_adjoint (B : FB R d O) (h h' : PS k 2 d) (hh : B.IsCanonGauge k h)
    (hh' : B.IsCanonGauge k h') (a : O) :
    (dAct k B a).transpose * bilinPart k (h' - h) = bilinPart k (h' - h) * dAct k B (star a) := by
  have hp : ∀ {n : ℕ} (j : Fin n), WickVanishing.GP (pt k (n := n) d j) := fun j => WickVanishing.gp_pt j
  have hA : ∀ a, WickVanishing.GP (B.actK k a) := fun a i => WickVanishing.const_actK B a i
  have a1 := WickVanishing.pair_points_zero_constant (WickVanishing.gp_comp1 _ _ (hA a) (hp (n := 2) 0)) (hp 1)
  have a2 := WickVanishing.pair_points_zero_constant (hp (n := 2) 0) (WickVanishing.gp_comp1 _ _ (hA (star a)) (hp (n := 2) 1))
  have e := (canonGauge_sub_isBiadd R d O k B h h' hh hh').2.2.2.2 a
  rw [WickVanishing.gt_ev_sub _ a1, WickVanishing.gt_ev_sub _ a2] at e
  ext j i
  have e' := congrArg (coeff (Finsupp.single ((0 : Fin 2), j) 1 + Finsupp.single ((1 : Fin 2), i) 1)) e
  rw [map_sub, map_sub, WickVanishing.coeff_ad_side1 B h hh, WickVanishing.coeff_ad_side1 B h' hh', WickVanishing.coeff_ad_side2 B h hh,
    WickVanishing.coeff_ad_side2 B h' hh'] at e'
  simp only [Matrix.mul_apply, Matrix.transpose_apply, bilinPart, map_sub, sub_mul, mul_sub,
    Finset.sum_sub_distrib]
  rw [← e']
  simp only [mul_comm]

theorem bilinPart_sub_eigen_eq_zero (B : FB R d O) (h h' : PS k 2 d) (hh : B.IsCanonGauge k h)
    (hh' : B.IsCanonGauge k h') (u v : Fin d → k) (a : O) (s t : k)
    (hu : (dAct k B a).mulVec u = s • u) (hv : (dAct k B (star a)).mulVec v = t • v) (hst : IsUnit (s - t)) :
    dotProduct u ((bilinPart k (h' - h)).mulVec v) = 0 := by
  have e := congrArg (fun M => dotProduct u (Matrix.mulVec M v)) (bilinPart_sub_adjoint B h h' hh hh' a)
  simp only [← Matrix.mulVec_mulVec] at e
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, hu, hv, Matrix.mulVec_smul, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, smul_eq_mul] at e
  rw [← hst.mul_right_eq_zero, sub_mul, e, sub_self]

end Adjoint

theorem canonGauge_independence_harmonic :
    ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] [Module.Free ℤ O] [Module.Finite ℤ O] [IsReduced O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h h' : PS k 2 d), B.IsCanonGauge k h → B.IsCanonGauge k h' → ∀ (T : Type) [Fintype T] (r : T → ℕ) (cc : T → T) (isX : T → Prop) (σ : T → O →+* k), (∀ τ, cc (cc τ) = τ) → (∀ τ, isX τ ∨ isX (cc τ)) → (∀ τ a, σ (cc τ) a = σ τ (star a)) → (∀ τ τ', τ ≠ τ' → ∃ a, IsUnit (σ τ a - σ τ' a)) → ∀ u : (Σ τ : T, Fin (r τ)) → Fin d → k, (∀ l a, (dAct k B a).mulVec (u l) = σ l.1 a • u l) → ∀ (n : ℕ) (Q : MvPolynomial ((Σ τ : T, Fin (r τ)) × Fin n) k), (∀ τ, isX τ → ∀ (i : Fin (r τ)) (i' : Fin (r (cc τ))), ∑ b : Fin n, MvPolynomial.pderiv (((⟨τ, i⟩ : Σ τ : T, Fin (r τ))), b) (MvPolynomial.pderiv (((⟨cc τ, i'⟩ : Σ τ : T, Fin (r τ))), b) Q) = 0) → ∀ (w0 : O) (mm : ℕ) (f : Fin n → PS k 1 d), ∑ mo ∈ Q.support, Q.coeff mo * ∏ b, B.nabVal k h w0 mm (f b) u (MvPolynomial.monomial (colM mo b) 1) = ∑ mo ∈ Q.support, Q.coeff mo * ∏ b, B.nabVal k h' w0 mm (f b) u (MvPolynomial.monomial (colM mo b) 1) := by
  intro R _ d O _ _ _ _ _ k _ _ _ B h h' hh hh' T _ r cc isX σ hcc hX hσ hsep u hu n Q hQ w0 mm f
  have key : ∀ l l' : (Σ τ : T, Fin (r τ)), l'.1 ≠ cc l.1 →
      dotProduct (u l) ((bilinPart k (h' - h)).mulVec ((dAct k B w0).mulVec (u l'))) = 0 := by
    intro l l' hne
    have hne' : l.1 ≠ cc l'.1 := fun e => hne (by rw [e, hcc])
    obtain ⟨a, ha⟩ := hsep _ _ hne'
    rw [hσ] at ha
    rw [hu l' w0, Matrix.mulVec_smul, dotProduct_smul,
      bilinPart_sub_eigen_eq_zero B h h' hh hh' (u l) (u l') a _ _ (hu l a) (hu l' (star a)) ha, smul_zero]
  refine canonGauge_independence_all.2.2.1 R d O k B h h' hh hh' w0 mm n _ u Q ?_ f
  refine harmSecond_holds k T r cc isX hcc hX n (fun l l' =>
    dotProduct (u l) ((bilinPart k (h' - h)).mulVec ((dAct k B w0).mulVec (u l'))) +
      dotProduct (u l') ((bilinPart k (h' - h)).mulVec ((dAct k B w0).mulVec (u l)))) ?_ Q hQ
  intro l l' hne
  have hne' : l.1 ≠ cc l'.1 := fun e => hne (by rw [e, hcc])
  rw [key l l' hne, key l' l hne', add_zero]

end GlobalTheory
