import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidChartDualNumberDeformation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDerivativesCoboundaryCoeffsMemMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelObjectLoweredLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInvariantFieldDualNumberOfIsInvariantTangentVeStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KSZeroDer

theorem isInvDer_of_isInv {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A]
    {v : TanM (𝟙 (Sp K)) A} {u : epsR K ⟶ A} (hu : u.left = (tv v).left) (ht : IsTangent u)
    {dd : Fld A.left} (hd : IsInv A v dd) : GlobalTheory.KS.IsInvDer u dd :=
  GlobalTheory.T.isInvariantField_dualNumber_of_isInvariant_tangentVector K A v u dd hu ht hd

theorem pbT_id_le {X : Scheme.{0}} {O₀ O : X.Opens} (h : O ≤ O₀) (s : Γ(X, O₀)) : pbT (𝟙 X) s O = rsT s O := by
  rw [pbT, rsT, dif_pos (show O ≤ (𝟙 X : X ⟶ X) ⁻¹ᵁ O₀ from h), dif_pos h]
  rfl

theorem constFn_zero_fn {R : Type} [CommRing R] {X : Scheme.{0}} (q : X ⟶ Sp R) (O : X.Opens) :
    constFn q O 0 = 0 := by
  rw [constFn, map_zero, map_zero]

theorem id_app_apply {X : Scheme.{0}} (O : X.Opens) (s : Γ(X, O)) : ((𝟙 X : X ⟶ X).app O).hom s = s := by
  simp only [Scheme.Hom.id_app]
  rfl

theorem rsT_mul_le {X : Scheme.{0}} {O₀ O : X.Opens} (h : O ≤ O₀) (s t : Γ(X, O₀)) : rsT (s * t) O = rsT s O * rsT t O := by
  rw [rsT, rsT, rsT, dif_pos h, dif_pos h, dif_pos h, map_mul]

theorem dlg_eq {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] (L : LB A.left)
    (δ : Fld A.left) (hf : IsField ⊤ δ) (i i' : L.ι) (ψ : Γ(A.left, L.U i ⊓ L.U i'))
    (hψ : (L.g i i').val * ψ = δ (L.U i ⊓ L.U i') (L.g i i').val) (O : A.left.Opens) (hO : O ≤ L.U i ⊓ L.U i') :
    dlg A (𝟙 _) L δ i i' O = rsT ψ O := by
  rw [dlg, pbT_id_le hO, pbT_id_le hO]
  have e2 := congrArg (fun s => rsT s O) hψ
  have e3 : rsT (δ (L.U i ⊓ L.U i') (L.g i i').val) O = δ O (rsT (L.g i i').val O) := by
    rw [rsT, rsT, dif_pos hO, dif_pos hO]
    exact (hf.2.2 _ O hO le_top _).symm
  rw [rsT_mul_le hO, e3] at e2
  rw [← e2, mul_comm (rsT (L.g i i').val O), _root_.mul_assoc, ← rsT_mul_le hO, Units.mul_inv]
  have e4 : rsT (1 : Γ(A.left, L.U i ⊓ L.U i')) O = 1 := by rw [rsT, dif_pos hO, map_one]
  rw [e4, _root_.mul_one]

theorem main : ∀ (K : Type) [Field K] [CharZero K] (P₀ : Out.PolAV (Sp K)) (n : ℕ) (v : Module.Basis (Fin n) K (TanM (𝟙 (Sp K)) P₀.A)) (dd : Fin n → Fld P₀.A.left), (∀ a, IsInv P₀.A (v a) (dd a)) → ∀ M : Matrix (Fin n) (Fin n) K, KSRel P₀.A (𝟙 P₀.A.left) P₀.L dd (fun _ => 0) M → M = 0 := by
  intro K _ _ P₀ n v dd hdd M hM
  haveI : IsCommMonObj P₀.A := P₀.isAb.comm
  obtain ⟨u, hu, hul⟩ := GlobalTheory.Heat.DlogIndep.exists_isLieBasis v
  have hinv : ∀ a, GlobalTheory.KS.IsInvDer (u a) (dd a) := fun a => isInvDer_of_isInv (hul a) (hu.1 a) (hdd a)
  have hiso := GlobalTheory.SiegLower.lbIso_pull_id P₀.isLB
  obtain ⟨⟨φ, hφ⟩, -⟩ := GlobalTheory.KS.DlogPol.dlog_independent K P₀ n u dd hu hinv _ (𝟙 _) P₀.L P₀.isLB hiso
  obtain ⟨J, W, j, d, hcov, hWj, hl, hdiff⟩ := hM
  have hcv : ∀ z : P₀.A.left, ∃ i, (𝟙 P₀.A.left : P₀.A.left ⟶ P₀.A.left) z ∈ W i := fun z => by
    have h2 : z ∈ ⨆ i, W i := by rw [hcov]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 h2
  have hpb : IsPullback (𝟙 P₀.A.left) P₀.A.hom P₀.A.hom (𝟙 (Sp K)) := IsPullback.of_horiz_isIso ⟨by simp⟩
  refine GlobalTheory.KSUniq.theta_eq_fibre P₀ u hu dd hinv P₀.A.hom (𝟙 _) (𝟙 _) hpb (U := ⊤) (isAffineOpen_top _) P₀.L
    P₀.isLB hiso (fun _ => 0) M 0 W W j j d (fun _ _ _ => 0) (fun _ => le_top) (fun _ => le_top) hWj hWj hcv hcv
    (fun i => (hl i).1) (fun _ => isField_zero _) ?_ ?_ φ hφ ?_ ?_
  · intro i h r
    have e : r = (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom r) := by
      simp
    have := (hl i).2 (W i) le_rfl ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom r)
    show _ = (P₀.A.hom.appLE ⊤ (W i) h).hom 0
    rw [map_zero]
    conv_lhs => rw [e]
    exact this.trans (by simp [constFn])
  · intro k h r
    show (0 : Γ(P₀.A.left, W k)) = (P₀.A.hom.appLE ⊤ (W k) h).hom 0
    rw [map_zero]
  · intro i i' O hO f
    rw [id_app_apply, id_app_apply, hdiff i i' O hO f]
    simp only [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have p : pbT (𝟙 P₀.A.left) (P₀.L.g (j i) (j i')).val
        ((𝟙 P₀.A.left) ⁻¹ᵁ P₀.L.U (j i) ⊓ (𝟙 P₀.A.left) ⁻¹ᵁ P₀.L.U (j i')) = (P₀.L.g (j i) (j i')).val :=
      GlobalTheory.Heat.DlogIndep.pbT_id (X := P₀.A.left) (P₀.L.U (j i) ⊓ P₀.L.U (j i')) _
    have hψ := hφ b (j i) (j i')
    rw [p] at hψ
    rw [dlg_eq P₀.L (dd b) (hdd b).1 (j i) (j i') (φ b (j i) (j i')) hψ O
      (fun z hz => ⟨hWj i (hO hz).1, hWj i' (hO hz).2⟩)]
    rfl
  · intro k k' O hO f
    rw [id_app_apply]
    simp only [Matrix.zero_apply, constFn_zero_fn, zero_mul, Finset.sum_const_zero, sub_self]
    rfl

end GlobalTheory.KSZeroDer
