import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDerivativesCoboundaryCoeffsMemMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantFieldsCechH1Relation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCechOneCoboundaryOfMixedOverlaps
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
namespace GlobalTheory.LieRigid

open GlobalTheory.ZH.CrdCalc (valR_res valR_spMap valR_eq valHom)

theorem dlg_sub {A : Type} [CommRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (L : LB B.left)
    (δ : Fld B.left) (hδ : IsField ⊤ δ) (i j : L.ι) {O T : B.left.Opens} (hO : O ≤ L.U i ⊓ L.U j) (hT : T ≤ O) :
    rsT (dlg B (𝟙 _) L δ i j O) T = rsT (dlg B (𝟙 _) L δ i j (L.U i ⊓ L.U j)) T := by
  rw [GlobalTheory.CoverRefinementPullback.dlg_res' B L δ hδ i j (hT.trans hO)]
  unfold dlg
  rw [GlobalTheory.KS.rsT_of_le hT, map_mul, GlobalTheory.CoverRefinementPullback.pbT_id' _ hO, GlobalTheory.CoverRefinementPullback.pbT_id' _ hO, ← hδ.2.2 _ _ hT le_top,
    GlobalTheory.CoverRefinementPullback.resG_resG', GlobalTheory.CoverRefinementPullback.resG_resG']
  rfl

theorem lie_inj : ∀ (R : Type) [CommRing R] [IsLocalRing R] (P : PolAV (Sp R)) (w : TanM (𝟙 (Sp R)) P.A) (δ : Fld P.A.left), IsInv P.A w δ → ∀ (K : Type) (V : K → P.A.left.Opens) (jk : K → P.L.ι), ⨆ k, V k = ⊤ → (∀ k, V k ≤ P.L.U (jk k)) → ∀ (b : ∀ k, Γ(P.A.left, V k)), (∀ k k', rsT (b k') (V k ⊓ V k') - rsT (b k) (V k ⊓ V k') = dlg P.A (𝟙 _) P.L δ (jk k) (jk k') (V k ⊓ V k')) → w = 0 := by
  intro R _ _ P w δ hδ K V jk hV hVj b hb
  have hδ1 : IsField ⊤ δ := hδ.1
  have hcob : IsCob P.L.U (fun j j' => dlg P.A (𝟙 _) P.L δ j j' (P.L.U j ⊓ P.L.U j')) := by
    refine GlobalTheory.T.isCechOneCoboundary_of_mixed_overlaps P.A.left P.L.ι K P.L.U V hV _
      (fun k k' => dlg P.A (𝟙 _) P.L δ (jk k) (jk k') (V k ⊓ V k'))
      (fun j k => rsT (dlg P.A (𝟙 _) P.L δ j (jk k) (P.L.U j ⊓ P.L.U (jk k))) (P.L.U j ⊓ V k))
      (fun j j' k => ?_) (fun j k k' => ?_) ⟨b, fun k k' => (hb k k').symm⟩
    · have t1 : P.L.U j ⊓ P.L.U j' ⊓ V k ≤ P.L.U j ⊓ P.L.U j' := inf_le_left
      have t2 : P.L.U j ⊓ P.L.U j' ⊓ V k ≤ P.L.U j ⊓ V k := le_inf (inf_le_left.trans inf_le_left) inf_le_right
      have t3 : P.L.U j ⊓ P.L.U j' ⊓ V k ≤ P.L.U j' ⊓ V k := le_inf (inf_le_left.trans inf_le_right) inf_le_right
      rw [GlobalTheory.KS.rsT_rsT (inf_le_inf le_rfl (hVj k)) t2, GlobalTheory.KS.rsT_rsT (inf_le_inf le_rfl (hVj k)) t3,
        ← GlobalTheory.CoverRefinementPullback.dlg_tri _ _ P.isLB δ hδ1 j j' (jk k) t1 (t3.trans (inf_le_inf le_rfl (hVj k)))
          (t2.trans (inf_le_inf le_rfl (hVj k)))]
      abel
    · have t1 : P.L.U j ⊓ V k ⊓ V k' ≤ V k ⊓ V k' := le_inf (inf_le_left.trans inf_le_right) inf_le_right
      have t2 : P.L.U j ⊓ V k ⊓ V k' ≤ P.L.U j ⊓ V k := inf_le_left
      have t3 : P.L.U j ⊓ V k ⊓ V k' ≤ P.L.U j ⊓ V k' := le_inf (inf_le_left.trans inf_le_left) inf_le_right
      rw [dlg_sub _ _ δ hδ1 (jk k) (jk k') (inf_le_inf (hVj k) (hVj k')) t1,
        GlobalTheory.KS.rsT_rsT (inf_le_inf le_rfl (hVj k)) t2, GlobalTheory.KS.rsT_rsT (inf_le_inf le_rfl (hVj k')) t3,
        ← GlobalTheory.CoverRefinementPullback.dlg_tri _ _ P.isLB δ hδ1 j (jk k) (jk k')
          (t2.trans (inf_le_inf le_rfl (hVj k))) (t1.trans (inf_le_inf (hVj k) (hVj k')))
          (t3.trans (inf_le_inf le_rfl (hVj k')))]
      abel
  obtain ⟨H, hH⟩ := hcob

  have hgp := GlobalTheory.Heat.DlogIndep.isGrpPullback_self P.A
  obtain ⟨u, hu⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.push_surj hgp (tv w)
  have hul : u.left = (tv w).left := (Category.comp_id _).symm.trans (congrArg (fun q => q.left) hu)
  have hut : IsTangent u :=
    (ReciprocityTheory.ChartRestriction.G.PullbackSections.isTangent_iff hgp _).2 (by rw [hu]; exact ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_mem _)
  have hee : ∀ (S : Type) [CommRing S] [Algebra R S] (φ : DualNumber R →ₐ[R] S),
      φ DualNumber.eps * φ DualNumber.eps = 0 := fun S _ _ φ => by
    rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
  have hφ : ∀ (S : Type) [CommRing S] [Algebra R S] (φ : DualNumber R →ₐ[R] S),
      (algOverHom φ ≫ u : algOver R S ⟶ P.A) = (Chart.spMap (SqZero.epsTo R (φ DualNumber.eps) (hee S φ)) ≫ u) := by
    intro S _ _ φ
    have e : φ = SqZero.epsTo R (φ DualNumber.eps) (hee S φ) := DualNumber.algHom_ext (by simp [SqZero.epsTo, SqZero.dualTo_apply])
    conv_lhs => rw [e]
    rfl
  have h1 : u = 1 := GlobalTheory.Heat.DlogIndep.eq_one_of_coboundary P.isLB P.ktriv (DualNumber.eps : DualNumber R)
    DualNumber.eps_mul_eps u (fun j => -H j)
    (fun S _ _ φ y U hU => by
      rw [hφ S φ]; exact (GlobalTheory.Heat.DlogIndep.valR_translate hul hut hδ _ (hee S φ) y U hU).1)
    (fun S _ _ φ y j j' hj hj' => by
      rw [hφ S φ]
      have hU : ⊤ ≤ y.left ⁻¹ᵁ (P.L.U j ⊓ P.L.U j') := fun p hp => ⟨hj hp, hj' hp⟩
      have e₁ := congrArg (valHom (R := S) y.left _ hU) (hH j j')
      have r₁ : valHom (R := S) y.left _ hU (rsT (H j) _) = valHom (R := S) y.left _ hj (H j) := by
        rw [rsT, dif_pos inf_le_left, ← valR_eq, ← valR_eq]
        exact valR_res _ _ hU _
      have r₂ : valHom (R := S) y.left _ hU (rsT (H j') _) = valHom (R := S) y.left _ hj' (H j') := by
        rw [rsT, dif_pos inf_le_right, ← valR_eq, ← valR_eq]
        exact valR_res _ _ hU _
      simp only [dlg, GlobalTheory.Heat.DlogIndep.pbT_id, map_sub, map_mul, r₁, r₂] at e₁
      have e₂ : valHom (R := S) y.left _ hU (P.L.g j j').val * valHom (R := S) y.left _ hU (P.L.g j j')⁻¹.val = 1 := by
        rw [← map_mul, Units.mul_inv, map_one]
      refine ((GlobalTheory.Heat.DlogIndep.valR_translate hul hut hδ _ (hee S φ) y _ hU).2 _).trans ?_
      simp only [valR_eq (R := S) _ _ hU, valR_eq (R := S) _ _ hj, valR_eq (R := S) _ _ hj', map_neg]
      linear_combination (φ DualNumber.eps * valHom (R := S) y.left _ hU (P.L.g j j').val) * e₁ +
        (-(φ DualNumber.eps * valHom (R := S) y.left _ hU (δ _ (P.L.g j j').val))) * e₂)
  have h2 : tv w = tv (0 : TanM (𝟙 (Sp R)) P.A) := by
    rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_zero, ← hu, h1, map_one]
  exact ReciprocityTheory.ChartRestriction.G.PullbackSections.tanM_ext h2

end GlobalTheory.LieRigid
