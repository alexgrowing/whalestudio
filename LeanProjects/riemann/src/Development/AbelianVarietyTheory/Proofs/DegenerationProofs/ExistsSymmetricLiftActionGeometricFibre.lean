import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KfBijective
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory.UT GlobalTheory.ZH.ClassWeight

noncomputable section
namespace GlobalTheory.ZH.ClassWeight

section General
open ReciprocityTheory.ChartRestriction.G.H1 GlobalTheory.ThetaPtMove
variable {B B' : Scheme.{0}} {G : Over B} [GrpObj G] {A : Over B'} [GrpObj A]
  {f : B' ⟶ B} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over B'} {T₀ : Over B} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
  {L₀ : LB G.left} {L₁ : LB A.left} {w : LB.Iso L₁ (L₀.pull φ)}

theorem sv_sum_smul {L : LB A.left} {k : ℤ} {I : Type} (F : Finset I) (c : I → Γ(T.left, ⊤))
    (v : I → SecM A L k T) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) {J} (hJ : Good L z J) :
    ThetaAct.sv (∑ l ∈ F, c l • v l) r z J =
      ∑ l ∈ F, gs (r ≫ (fst T A).left) z ⊤ (c l) * ThetaAct.sv (v l) r z J := by
  induction F using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    have h := ThetaAct.sv_add (0 : SecM A L k T) 0 r z hJ
    rw [add_zero] at h
    exact left_eq_add.1 h
  | insert a F ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ThetaAct.sv_add _ _ _ _ hJ, ThetaAct.sv_smul _ _ _ _ hJ, ih]

theorem secRel_sum {k : ℤ} {I : Type} [Fintype I] (c : I → Γ(T₀.left, ⊤))
    {t : I → LB.Sec (LPow A L₁ k T)} {s : I → LB.Sec (LPow G L₀ k T₀)} (h : ∀ l, SecRel hp τ hτ w (t l) (s l)) :
    SecRel hp τ hτ w (SecM.toSec A (∑ l, τ.appTop.hom (c l) • SecM.ofSec A (t l)))
      (SecM.toSec G (∑ l, c l • SecM.ofSec G (s l))) := by
  intro Z r z J J' hJ hJ'
  refine (sv_sum_smul Finset.univ c (fun l => SecM.ofSec G (s l)) (r ≫ psi hp τ hτ) z hJ).trans (Eq.trans ?_
    (congrArg (_ * ·) (sv_sum_smul Finset.univ (fun l => τ.appTop.hom (c l)) (fun l => SecM.ofSec A (t l))
      r z hJ').symm))
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_left_comm, Category.assoc, psi_fst', ← Category.assoc]
  exact congrArg₂ (· * ·) (gs_pull _ τ z ⊤ trivial (c l)).symm (h l Z r z J J' hJ hJ')

theorem isActOf_unique {L : LB A.left} (hL : L.IsLB) {k : ℤ} {θ : ThetaGrp A L k T}
    {s s₁ s₂ : LB.Sec (LPow A L k T)} (h₁ : IsActOf A L k θ s s₁) (h₂ : IsActOf A L k θ s s₂) :
    SecM.ofSec A s₁ = SecM.ofSec A s₂ :=
  ThetaAct.sv_ext hL fun y J hJ =>
    ((ThetaAct.isActOf_iff hL θ s s₁).1 h₁ y J hJ).trans ((ThetaAct.isActOf_iff hL θ s s₂).1 h₂ y J hJ).symm

theorem exists_isActOf' {L : LB A.left} (hL : L.IsLB) {k : ℤ} (θ : ThetaGrp A L k T)
    (s : LB.Sec (LPow A L k T)) : ∃ s', IsActOf A L k θ s s' := by
  obtain ⟨v, hv⟩ := ThetaAct.exists_act hL θ (SecM.ofSec A s)
  exact ⟨SecM.toSec A v, (ThetaAct.isActOf_iff hL θ _ _).2 fun y J hJ => hv _ _ y J hJ⟩

theorem ofSec_eq_sum {L : LB A.left} {k : ℤ} {I : Type} [Fintype I] (c : I → Γ(T.left, ⊤))
    (s : I → LB.Sec (LPow A L k T)) (σ : LB.Sec (LPow A L k T))
    (h : ∀ j, σ.f j = ∑ l, liftFun A _ (c l) * (s l).f j) : σ = SecM.toSec A (∑ l, c l • SecM.ofSec A (s l)) := by
  have e : SecM.ofSec A σ = ∑ l, c l • SecM.ofSec A (s l) := by
    refine Subtype.ext (funext fun j => (h j).trans ?_)
    rw [Submodule.coe_sum, Finset.sum_apply]
    rfl
  rw [← e]
  rfl

theorem symLift_act_move [IsCommMonObj A] (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) {k : ℤ} {n : ℕ}
    {x : T ⟶ A} {x₀ : T₀ ⟶ G} (hx : τ ≫ x₀.left = x.left ≫ φ) (hn : x ^ n = 1) {θ₀ : ThetaGrp G L₀ k T₀}
    (H₀ : SymLift G L₀ k n x₀ θ₀) {I : Type} [Fintype I] (c : I → I → Γ(T₀.left, ⊤)) (c' : I → I → Γ(T.left, ⊤))
    (hc : ∀ l i, τ.appTop.hom (c l i) = c' l i)
    {t : I → LB.Sec (LPow A L₁ k T)} {s : I → LB.Sec (LPow G L₀ k T₀)} (h : ∀ l, SecRel hp τ hτ w (t l) (s l))
    (hs : ∀ i σ, IsActOf G L₀ k θ₀ (s i) σ → ∀ j, σ.f j = ∑ l, liftFun G _ (c l i) * (s l).f j) :
    ∃ θ : ThetaGrp A L₁ k T, SymLift A L₁ k n x θ ∧ ∀ i t', IsActOf A L₁ k θ (t i) t' →
      SecM.ofSec A t' = ∑ l, c' l i • SecM.ofSec A (t l) := by
  obtain ⟨θ, hθ, H⟩ := symLift_move hp τ hτ hw hL₀ hL₁ hx hn H₀
  refine ⟨θ, hθ, fun i t' ht' => ?_⟩
  obtain ⟨σ, hσ⟩ := exists_isActOf' hL₀ θ₀ (s i)
  have e := ofSec_eq_sum _ _ σ (hs i σ hσ)
  have hr := secRel_sum hp τ hτ (fun l => c l i) h
  rw [← e] at hr
  refine (isActOf_unique hL₁ ht' (H _ _ _ _ (h i) hr hσ)).trans ?_
  simp only [hc]
  rfl

end General

theorem appTop_fn {R : Type} [CommRing R] (V : Type) [CommRing V] [IsDomain V] (F : Type) [Field F]
    [Algebra (FractionRing V) F] (y : R →+* F) (c : R) :
    (show (TFK (R := V) F).left ⟶ (baseOver (Sp R)).left from spMap y).appTop.hom (fn c) = kf V F (y c) :=
  (congrArg (fun q => q.hom c) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom y))).symm

theorem exists_symLift_act : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (w : LB.Iso u.A.L (ρ.P.L.pull u.φ)), w.IsGen → ∀ t : S.J → SecA u.A (PadicAlgCl p) S.N, (∀ i, Moved u w (t i) (ρ.s i)) → ∀ (a : S.Gam) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), x.left ≫ u.φ = spMap y₀ ≫ (ρ.pt (S.r • a)).left → x ^ S.N = 1 → ∃ θ : ThetaGrp u.A.A u.A.L (S.N : ℤ) (TFK (R := u.V) (PadicAlgCl p)), SymLift u.A.A u.A.L S.N S.N x θ ∧ ∀ i t', IsActOf u.A.A u.A.L S.N θ (t i) t' → SecM.ofSec u.A.A t' = ∑ l, kf u.V (PadicAlgCl p) (y₀ (algebraMap o S.R (S.ρ a l i))) • SecM.ofSec u.A.A (t l) := by
  intro o Ω _ _ _ _ S ρ p _ y₀ u w hw t ht a x hx hn
  have := u.A.isAb.comm
  exact symLift_act_move u.cart (T := TFK (R := u.V) (PadicAlgCl p))
    (T₀ := baseOver (Sp S.R)) (spMap y₀) (base_eq u) hw ρ.P.isLB u.A.isLB hx.symm hn (ρ.U_sym a)
    (fun l i => fn (algebraMap o S.R (S.ρ a l i))) _ (fun l i => appTop_fn u.V (PadicAlgCl p) y₀ _) ht (ρ.U_act a)

end GlobalTheory.ZH.ClassWeight
end
