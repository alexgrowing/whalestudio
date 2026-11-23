import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisRaynaudTangentInvariantFields
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothCommGroupSchemeHomTangentAtOriginSurjectivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantVectorFieldOfTangentVectorLinearCombinaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantVectorFieldPullbackAlongGroupHomStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.InvFactor

section Lie
variable {R : Type} [CommRing R] {G B : Over (Sp R)} [GrpObj G] [GrpObj B] [IsCommMonObj G] [IsCommMonObj B]

theorem smT_comp (a : R) (v : overAt (𝟙 (Sp R)) (DualNumber R) ⟶ G) (φ : G ⟶ B) :
    smT (𝟙 (Sp R)) a (v ≫ φ) = smT (𝟙 (Sp R)) a v ≫ φ := (Category.assoc _ _ _).symm

def lieMap (q : G ⟶ B) [IsMonHom q] : TanM (𝟙 (Sp R)) G →ₗ[R] TanM (𝟙 (Sp R)) B where
  toFun v := ReciprocityTheory.ChartRestriction.G.PullbackSections.mkT (tv v ≫ q) (by rw [smT_comp, ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_mem, MonObj.one_comp])
  map_add' u v := ReciprocityTheory.ChartRestriction.G.PullbackSections.tanM_ext (MonObj.mul_comp (tv u) (tv v) q)
  map_smul' a v := ReciprocityTheory.ChartRestriction.G.PullbackSections.tanM_ext (smT_comp a (tv v) q).symm

theorem tv_lieMap (q : G ⟶ B) [IsMonHom q] (v : TanM (𝟙 (Sp R)) G) : tv (lieMap q v) = tv v ≫ q := rfl

end Lie

theorem exists_basis_pull_matrix : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∃ (g : ℕ) (w : Module.Basis (Fin g) R (TanM (𝟙 (Sp R)) Dd.toPre.P.A)) (e : Fin g → Fld Dd.toPre.P.A.left) (P : Matrix (Fin g) (Fin n) R) (Qm : Matrix (Fin n) (Fin g) R), (∀ c, IsInv Dd.toPre.P.A (w c) (e c)) ∧ P * Qm = 1 ∧ ∀ b (V : Dd.toPre.P.A.left.Opens) (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ V → ∀ f : Γ(Dd.toPre.P.A.left, V), dd b W (pbT Y.q.left f W) = ∑ c, constFn Y.H.hom W (P c b) * pbT Y.q.left (e c V f) W := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y n v dd hdd
  have hB : Smooth Dd.toPre.P.A.hom := Dd.toPre.P.isAb.smooth
  obtain ⟨g, ⟨w⟩⟩ := GlobalTheory.RayBasis.exists_basis hB
  choose e he using fun c => GlobalTheory.RayBasis.exists_isInv (w c)
  haveI : IsMonHom Y.q := Y.q_linear.isMonHom
  have hq : Smooth Y.q.left := Y.smooth_q
  let L := lieMap Y.q
  choose s hs using fun c => GlobalTheory.T.smooth_commGroupSchemeHom_tangentAtOrigin_surjective R Y.H Dd.toPre.P.A Y.q hq (w c)
  have hs' : ∀ c, L (s c) = w c := fun c => ReciprocityTheory.ChartRestriction.G.PullbackSections.tanM_ext (hs c)
  refine ⟨g, w, e, Matrix.of fun c b => w.repr (L (v b)) c, Matrix.of fun b c => v.repr (s c) b, he, ?_, ?_⟩
  · ext c c'
    simp only [Matrix.mul_apply, Matrix.of_apply]
    have h1 : w.repr (L (s c')) c = ∑ b, w.repr (L (v b)) c * v.repr (s c') b := by
      conv_lhs => rw [← v.sum_repr (s c')]
      rw [map_sum, map_sum, Finsupp.coe_finset_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [map_smul, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
    rw [← h1, hs', w.repr_self, Matrix.one_apply, Finsupp.single_apply]
    exact if_congr eq_comm rfl rfl
  · intro b V W hW f
    have hu : ∑ c, Matrix.of (fun c b => w.repr (L (v b)) c) c b • w c = L (v b) := w.sum_repr _
    have hinv := GlobalTheory.T.invariant_vectorField_of_tangent_vector_linear_combination R Dd.toPre.P.A g w e he (fun c => Matrix.of (fun c b => w.repr (L (v b)) c) c b)
    rw [hu] at hinv
    rw [GlobalTheory.T.invariant_vectorField_pullback_along_group_hom R Y.H Dd.toPre.P.A Y.q (v b) (L (v b)) (dd b) _ rfl (hdd b) hinv V W hW f, GlobalTheory.KS.pbT_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [GlobalTheory.KS.pbT_mul, GlobalTheory.KS.pbT_constFn _ _ hW, Over.w Y.q, Matrix.of_apply]

end GlobalTheory.InvFactor
