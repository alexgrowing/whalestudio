import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePartBase
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ReprMemOfBasisRational

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
open GlobalTheory.LiftLower
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftLower

section Generic

variable {K : Type} [Field K] [NumberField K] [StarRing K] {M W' ι : Type} [AddCommGroup M] [Module K M]
  [NormedAddCommGroup W'] [InnerProductSpace ℂ W'] [Fintype ι]

omit [NumberField K] in

theorem inner_coef_of_rat (b : Module.Basis ι K M) (σ : K →+* ℂ) (c₁ : M →ₛₗ[σ] W') (pr : M →ₗ⋆[K] M →ₗ[K] K)
    (hp : ∀ a a', inner ℂ (c₁ (b a)) (c₁ (b a')) = σ (pr (b a) (b a'))) (u v : M) (hu : ∀ a, b.repr u a ∈ cmMax K) :
    inner ℂ (c₁ u) (c₁ v) = σ (pr u v) := by
  conv_lhs => rw [← b.sum_repr u, ← b.sum_repr v]
  conv_rhs => rw [← b.sum_repr u, ← b.sum_repr v]
  simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, map_mul,
    RingHom.id_apply, sum_inner, inner_sum, inner_smul_left, inner_smul_right, hp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
  rw [starRingEnd_apply (b.repr u a'), hu a' σ]

theorem inner_eq_csumAt (S : CSD K) (hb : S.HasRatBasis) (b : Module.Basis ι K M) (σ : K →+* ℂ) (c₁ : M →ₛₗ[σ] W')
    (pr : M →ₗ⋆[K] M →ₗ[K] K) (hp : ∀ a a', inner ℂ (c₁ (b a)) (c₁ (b a')) = σ (pr (b a) (b a')))
    (e : S.V ≃ₗ[K] M) (hr : ∀ i a, b.repr (e (S.bV i)) a ∈ cmMax K) (he : ∀ x x', pr (e x) (e x') = S.pair x x')
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (j : S.Forms →ₛₗ[σ] H)
    (hj : ∀ x y : S.Forms, inner ℂ (j x) (j y) =
      ∑ c, ((S.wt c : ℂ))⁻¹ * inner ℂ (c₁ (e ((x : S.Cl → S.V) c))) (c₁ (e ((y : S.Cl → S.V) c)))) (x y : S.Forms) :
    inner ℂ (j x) (j y) = csumAt S σ x y := by
  have hrat : ∀ k c a, b.repr (e ((S.basis k : S.Cl → S.V) c)) a ∈ cmMax K := by
    intro k c a
    rw [← S.bV.sum_repr ((S.basis k : S.Cl → S.V) c)]
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
    exact Subfield.sum_mem _ fun i _ => Subfield.mul_mem _ (S.basis_rat hb k c i) (hr i a)
  have hH : ∀ k l, inner ℂ (j (S.basis k)) (j (S.basis l)) = σ (S.H k l) := by
    intro k l
    rw [hj]
    unfold CSD.H CSD.csum
    rw [Matrix.of_apply, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [inner_coef_of_rat b σ c₁ pr hp _ _ (hrat k c), he, map_mul, map_inv₀, map_natCast]
  conv_lhs => rw [← S.basis.sum_repr x, ← S.basis.sum_repr y]
  unfold csumAt
  simp only [map_sum, LinearMap.map_smulₛₗ, sum_inner, inner_sum, inner_smul_left, inner_smul_right, hH,
    dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
  rw [starRingEnd_apply]
  ring

theorem inner_eq_csumAt_of_pres {G Γ W : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {ι₀ : Γ →* G} {S : CSD K} {σ₀ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ}
    (P : Bridge.ClassPres ι₀ S σ₀ ρ J χ) (b : Module.Basis ι K M) (c₀ : M →ₛₗ[σ₀] W) (pr : M →ₗ⋆[K] M →ₗ[K] K)
    {Q : (S.V ≃ₗ[K] M) → Prop}
    (hP : ∃ e : S.V ≃ₗ[K] M, (∀ i a, b.repr (e (S.bV i)) a ∈ cmMax K) ∧ (∀ x, P.coef x = c₀ (e x)) ∧
      (∀ x x', pr (e x) (e x') = S.pair x x') ∧ Q e)
    (hb : S.HasRatBasis) (σ : K →+* ℂ) (c₁ : M →ₛₗ[σ] W')
    (hp : ∀ a a', inner ℂ (c₁ (b a)) (c₁ (b a')) = σ (pr (b a) (b a')))
    (H : HMod (G → W')) (j : S.Forms →ₛₗ[σ] H.H)
    (hH : ∀ x y : H.H, inner ℂ x y = Bridge.adInner ι₀ J P.y (H.e x) (H.e y))
    (hj : ∀ (x : S.Forms) h, ∃ v, P.ext (x : S.Cl → S.V) h = c₀ v ∧ H.e (j x) h = c₁ v) (x y : S.Forms) :
    inner ℂ (j x) (j y) = csumAt S σ x y := by
  obtain ⟨e, hr, he, hpair, -⟩ := hP
  have hval : ∀ (z : S.Forms) cl, H.e (j z) (P.y cl) = c₁ (e (z.1 cl)) := by
    intro z cl
    obtain ⟨v, h0, h1⟩ := hj z (P.y cl)
    have h3 : P.coef (z.1 cl) = P.coef (e.symm v) := by
      rw [← GlobalTheory.PresBasic.ext_y P z cl, h0, he, e.apply_symm_apply]
    rw [h1, GlobalTheory.PresBasic.coef_injective _ h3, e.apply_symm_apply]
  refine inner_eq_csumAt S hb _ σ c₁ _ hp e hr hpair j (fun z w => ?_) x y
  rw [hH]
  unfold Bridge.adInner
  refine Finset.sum_congr rfl fun cl _ => ?_
  rw [hval, hval, CSD.wt, ← Nat.card_eq_fintype_card, Nat.card_congr (P.stabI cl).toEquiv]

end Generic

theorem inner_conjForms_eq_csumAt : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.models_jV → ∀ gramR c0R c0L, Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ) (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) c c₁ H j, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsConjForms R i σ (c0L i) c c₁ H j → ∀ x y, ⟪j x, j y⟫_ℂ = csumAt (A.MtCSD i A.μ0) σ x y := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hjV gramR c0R c0L hT i σ c c₁ H j hC x y
  have hb : (A.MtCSD i A.μ0).HasRatBasis :=
    (GlobalTheory.HeckeRational.dcOp_matrix_mem_cmMax (Vc D i) (R.cV i).coef (R.βV i) (R.datVt i A.μ0) (R.B.L i A.μ0).pres
      (hT.coefL i A.μ0) (hT.mapL i)
      (fun g a k => (coefAction_repr_mem_subfield (labLL D) _ _ GlobalTheory.HeckeRational.labLL_mem_cmMax g a k).2) {1} 1
      (fun f => by funext h; simp [Bridge.dcOp])).1
  have h1 := hC.model.choose_spec.2.2.2
  have h2 : ∀ (z : A.fam.amb.FL i A.μ0) h, ∃ v, (R.B.L i A.μ0).pres.ext z.1 h = c0L i v ∧ H.e (j z) h = c₁ v :=
    fun z h => (hC.base z h).imp fun v hv => ⟨(congrFun (hjV i A.μ0 z) h).symm.trans hv.1, hv.2⟩
  exact inner_eq_csumAt_of_pres (R.B.L i A.μ0).pres _ (c0L i) _ (hT.coefL i A.μ0) hb σ c₁ hC.pair H j h1 h2 x y

end GlobalTheory.LiftLower

end
