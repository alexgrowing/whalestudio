import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueLieBasisCoeffsOfDerivationAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLieBasisDualPointsOfTangentModuleBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValueAtInvariantFieldTranslateSqZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValidGaugeImpliesValid
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TangentOrigin

noncomputable section

namespace GlobalTheory.HxUniq

open GlobalTheory.KS (rsT_self eq_of_rsT_eq)

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

theorem evalPt_lieExp_comb {m : ℕ} (u : Fin m → TanM (𝟙 (Sp R)) G) (dd : Fin m → Fld G.left)
    (hd : ∀ i, IsInv G (u i) (dd i)) (B : Type) [CommRing B] [Algebra R B] (e : Fin m → B)
    (he : ∀ i j, e i * e j = 0) (z : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) B ⟶ G) (O : G.left.Opens)
    (h : ⊤ ≤ z.left ⁻¹ᵁ O) :
    ∃ h' : ⊤ ≤ (GlobalTheory.SqZero.lieExp (fun i => GlobalTheory.VertCoeffRing.tvE (u i)) e (fun i => he i i) * z).left ⁻¹ᵁ O, ∀ f,
      evalPt _ O h' f = evalPt z.left O h f + ∑ i, e i * evalPt z.left O h (dd i O f) := by
  induction m with
  | zero =>
    have : GlobalTheory.SqZero.lieExp (fun i => GlobalTheory.VertCoeffRing.tvE (u i)) e (fun i => he i i) * z = z := by
      simp [GlobalTheory.SqZero.lieExp]
    rw [this]
    exact ⟨h, fun f => by simp⟩
  | succ m ih =>
    obtain ⟨h₁, H₁⟩ := ih (fun i => u i.succ) (fun i => dd i.succ) (fun i => hd i.succ) (fun i => e i.succ)
      (fun i j => he _ _)
    obtain ⟨h₂, H₂⟩ := GlobalTheory.VertCoeffRing.evalPt_tvE_mul (hd 0) (e 0) (he 0 0) _ O h₁
    have : GlobalTheory.SqZero.lieExp (fun i => GlobalTheory.VertCoeffRing.tvE (u i)) e (fun i => he i i) * z =
        (ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.epsTo R (e 0) (he 0 0)) ≫ GlobalTheory.VertCoeffRing.tvE (u 0)) *
          (GlobalTheory.SqZero.lieExp (fun i => GlobalTheory.VertCoeffRing.tvE (u i.succ)) (fun i => e i.succ)
            (fun i => he i.succ i.succ) * z) := by
      rw [GlobalTheory.SqZero.lieExp, GlobalTheory.SqZero.lieExp, Fin.prod_univ_succ, _root_.mul_assoc]
    rw [this]
    refine ⟨h₂, fun f => ?_⟩
    rw [H₂, H₁, H₁, Fin.sum_univ_succ, mul_add, Finset.mul_sum]
    simp only [← _root_.mul_assoc, he, zero_mul, Finset.sum_const_zero]
    ring

theorem coeff_eq_zero [Smooth G.hom] {n : ℕ} (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G))
    (dd : Fin n → Fld G.left) (hd : ∀ a, IsInv G (v a) (dd a)) (W : G.left.Opens) (c : Fin n → Γ(G.left, W))
    (hc : ∀ Wo : G.left.Opens, Wo ≤ W → ∀ f, ∑ a, rsT (c a) Wo * dd a Wo f = 0) (a : Fin n) : c a = 0 := by
  let J := {V : G.left.Opens // IsAffineOpen V ∧ V ≤ W}
  have hcov : W ≤ ⨆ k : J, k.1 := by
    intro x hx
    obtain ⟨V, hV, hxV, hVW⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 (G.left.isBasis_affineOpens)) hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨V, hV, hVW⟩, hxV⟩
  refine eq_of_rsT_eq (fun k : J => k.1) (fun k => k.2.2) hcov _ _ fun k => ?_
  rw [GlobalTheory.KS.rsT_zero]
  obtain ⟨V, hV, hVW⟩ := k
  have hu := GlobalTheory.VertCoeffRing.existsUnique_coeff_affine_ring (fun a => GlobalTheory.VertCoeffRing.tvE (v a))
    (GlobalTheory.VertCoeffRing.isLieBasis_tvE v) dd
    (fun B _ _ e he z O h => evalPt_lieExp_comb (fun a => v a) dd hd B e he z O h) V V hV hV le_rfl
    (fun _ => 0) (fun _ _ => by simp) (fun _ _ => by simp) (fun _ => rfl)
  have h1 : ∀ f, (fun _ => (0 : Γ(G.left, V))) f = ∑ a, (fun a => rsT (c a) V) a * rsT (dd a V f) V := by
    intro f
    simp only [rsT_self]
    exact (hc V hVW f).symm
  have h0 : ∀ f, (fun _ => (0 : Γ(G.left, V))) f = ∑ a, (fun _ => (0 : Γ(G.left, V))) a * rsT (dd a V f) V := by
    intro f; simp
  exact congrFun (hu.unique h1 h0) a

end GlobalTheory.HxUniq

theorem GlobalTheory.HxUniq.raynaud_coeff_eq_zero : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (W : Y.H.left.Opens) (c : Fin n → Γ(Y.H.left, W)), (∀ Wo : Y.H.left.Opens, Wo ≤ W → ∀ f, ∑ a, rsT (c a) Wo * dd a Wo f = 0) → ∀ a, c a = 0 := by
  intro R _ _ Q O _ _ _ oa Y n v dd hd W c hc a
  have : Smooth Y.H.hom := (GlobalTheory.isSemiAbelian_of_isGt _ _ _ Y.isGt).smooth
  exact GlobalTheory.HxUniq.coeff_eq_zero v dd hd W c hc a
