import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectionStatementHolds

set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatCore GlobalTheory.LineNorm GlobalTheory.FlatModel
open MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv actR)
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.FlatDenom

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

def IsProjMat {X : Scheme.{0}} (t : SAB H X) {R : Type} [CommRing R] (ξ : Sp R ⟶ X) (σ : 𝓞 E →+* R) {g : ℕ}
    (e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)) (U : Matrix (Fin g) (Fin g) R) : Prop :=
  ∀ (S : Type) [CommRing S] (φ : R →+* S),
    EigRowsAt t (spMap φ ≫ ξ) (φ.comp σ) (bcV t φ e) (U.map φ) ∧
    ∀ w v, IsCombAtG t (spMap φ ≫ ξ) (bcV t φ e) w v → IsEigG t (φ.comp σ) v →
      Matrix.vecMul w (U.map φ) = ((discr E : ℤ) : S) • w

open GlobalTheory.FlatModel.Proj in

theorem exists_isProjMat {X : Scheme.{0}} {t : SAB H X} {R : Type} [CommRing R] {ξ : Sp R ⟶ X} {g : ℕ}
    {e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)} (he : IsTanBasis t ξ e) (σ : 𝓞 E →+* R) :
    ∃ U : Matrix (Fin g) (Fin g) R, IsProjMat t ξ σ e U := by
  classical
  let b := RingOfIntegers.basis E
  obtain ⟨c, hc1, hc2⟩ := exists_dual b (discr_ne_zero E)
  have hbas : ∀ w, IsTanAtG t ξ w → ∃ a, IsCombAtG t ξ e a w := fun w hw => by
    have h0 : spMap (RingHom.id R) = 𝟙 (Sp R) := Spec.map_id _
    have h1 : spMap (dualMap (RingHom.id R)) = 𝟙 _ := by
      have : dualMap (RingHom.id R) = RingHom.id _ := by ext s <;> simp [dualMap]
      rw [this]
      exact Spec.map_id _
    have := he.2 R (RingHom.id R) w (by rwa [h0, Category.id_comp])
    simp only [h0, h1, Category.id_comp] at this
    exact this.exists
  choose ρ hρ using fun (a : 𝓞 E) (k : Fin g) =>
    hbas _ (GlobalTheory.LieMet.isTan_tv (actR t.act a (GlobalTheory.LieMet.tanOf (he.1 k))))
  refine ⟨Matrix.of fun k j => ∑ i, σ (c i) * ρ (b i) k j, fun S _ φ => ?_⟩
  have he' := isTanBasis_bc he φ
  let T : Fin g → TanM (spMap φ ≫ ξ) t.G := fun j => GlobalTheory.LieMet.tanOf (he'.1 j)
  have hT : bcV t φ e = fun j => (tv (T j)).left := rfl
  have hA : ∀ a k, actR t.act a (T k) = ∑ j, φ (ρ a k j) • T j := fun a k => by
    refine (GlobalTheory.LieMet.isComb_iff T _ _).1 ?_
    have := GlobalTheory.GradedPieces.comb_map φ rfl (hρ a k)
    have e1 : spMap (dualMap φ) ≫ (tv (actR t.act a (GlobalTheory.LieMet.tanOf (he.1 k)))).left =
        (tv (actR t.act a (T k))).left := (Category.assoc _ _ _).symm
    rw [e1] at this
    exact this
  have hU : ∀ k, ∑ j, φ (∑ i, σ (c i) * ρ (b i) k j) • T j = ∑ i, (φ.comp σ) (c i) • actR t.act (b i) (T k) := fun k => by
    simp only [hA, map_sum, map_mul, Finset.sum_smul, Finset.smul_sum, smul_smul, RingHom.comp_apply]
    exact Finset.sum_comm
  refine ⟨fun k u hu a => ?_, fun w v hw hv => ?_⟩
  · rw [hT] at hu
    rw [eq_of_comb T hu, GlobalTheory.ShFam.Pad.Pull.eig_iff]
    simp only [Matrix.map_apply, Matrix.of_apply]
    rw [hU]
    exact eig_proj _ _ b c hc1 a _
  · rw [hT] at hw
    have hv0 := eq_of_comb T hw
    have hv1 : ∀ a, actR t.act a (∑ i, w i • T i) = (φ.comp σ) a • ∑ i, w i • T i := fun a => by
      rw [← GlobalTheory.ShFam.Pad.Pull.eig_iff, ← hv0]
      exact hv a
    have h2 := proj_eig _ _ b c hc2 _ hv1
    have h3 : ∑ j, (∑ k, w k • fun j => φ (∑ i, σ (c i) * ρ (b i) k j)) j • T j =
        ∑ j, (((discr E : ℤ) : S) • w) j • T j := by
      have h4 : ∑ j, (((discr E : ℤ) : S) • w) j • T j = ((discr E : ℤ) : S) • ∑ j, w j • T j := by
        simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul]
      rw [h4]
      refine Eq.trans ?_ h2
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_smul, mul_smul]
      rw [Finset.sum_comm]
      simp only [← Finset.smul_sum, hU]
      simp only [map_sum, map_smul, Finset.smul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => smul_comm _ _ _
    have hu := he.2 S φ _ (GlobalTheory.LieMet.isTan_tv (∑ j, (((discr E : ℤ) : S) • w) j • T j))
    have h5 := hu.unique ((GlobalTheory.LieMet.isComb_iff T _ _).2 rfl) ((GlobalTheory.LieMet.isComb_iff T _ _).2 h3.symm)
    rw [h5]
    funext j
    simp [Matrix.vecMul, dotProduct, Finset.sum_apply]

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def IsFrameCoord (Y : Model Xo c β) {R : Type} [CommRing R] (ξ : Sp R ⟶ Y.X) {g : ℕ}
    (e : Fin g → (Sp (DualNumber R) ⟶ Y.t.G.left)) (U : Matrix (Fin g) (Fin g) R) {k : Type} [CommRing k]
    [Algebra c.F k] (φ : R →+* k) (y : FrPt Xo c k) (σ : E →+* ℂ) (M : Matrix (Fin (Dw.mult σ)) (Fin g) k)
    (C : Matrix (Fin g) (Fin (Dw.mult σ)) k) : Prop :=
  (∀ i, ∃ w : Sp (DualNumber k) ⟶ Y.oF.t.G.left,
    w ≫ Y.oF.t.G.hom = spMap (algebraMap k (DualNumber k)) ≫ GlobalTheory.AllWt.ptF y ∧ w ≫ Y.m0.toSABMap.φ = y.u σ i ∧
      IsCombAtG Y.t (spMap φ ≫ ξ) (bcV Y.t φ e) (M i) (w ≫ Y.m.φ)) ∧
  C * M = U.map φ ∧ M * C = ((discr E : ℤ) : k) • (1 : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) k)

def DetLaw (Z : Comp Xo c) (f : Rul Xo c) (σ₁ σ₂ : E →+* ℂ) : Prop :=
  IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f ∧
  ∀ (k : Type) [Field k] [Algebra c.F k] (z y : FrPt Xo c k), LiesOn Z y → z.x = y.x →
    ∀ (g₁ : Matrix (Fin (Dw.mult σ₁)) (Fin (Dw.mult σ₁)) k) (g₂ : Matrix (Fin (Dw.mult σ₂)) (Fin (Dw.mult σ₂)) k),
      (∀ i, IsCombAt y.x (y.u σ₁) (g₁ i) (z.u σ₁ i)) → (∀ i, IsCombAt y.x (y.u σ₂) (g₂ i) (z.u σ₂ i)) →
      evR Xo c f z * g₁.det = g₂.det * evR Xo c f y

theorem isPreimmersion_fst (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) :
    IsPreimmersion (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))) := by
  have : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 c.F))
  infer_instance

theorem isPreimmersion_j (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) : IsPreimmersion Y.j := by
  have := isPreimmersion_fst Y
  have := Y.jQ_open
  unfold Model.j
  infer_instance

end GlobalTheory.FlatDenom

end
