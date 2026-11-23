import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Adj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapDegreeSymmetric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSection
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HomAppHomOfRestrictImage

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

namespace GlobalTheory.RankTwoChern

section Hom

open GlobalTheory.VB (IsVB IsFrame homMod homMap homApp homMk homApp_resM)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)
open GlobalTheory.LB (resG_resG resG_self)

variable {X : Scheme.{0}}

theorem homMap_comp_zero (S : ShortComplex X.Modules) (G : X.Modules) :
    homMap S.g (𝟙 G) ≫ homMap S.f (𝟙 G) = 0 := by
  ext V ψ : 3
  refine VB.hom_ext fun W h s => ?_
  change homApp ψ h ((S.f ≫ S.g).app W s) = 0
  rw [S.zero]
  exact map_zero (homApp ψ h)

theorem shortExact_homMod (S : ShortComplex X.Modules) {s : ℕ} (hS : S.ShortExact)
    (h₃ : IsVB S.X₃ s) (G : X.Modules) :
    (ShortComplex.mk (homMap S.g (𝟙 G)) (homMap S.f (𝟙 G)) (homMap_comp_zero S G)).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  have hex (W : X.Opens) (t : Γ(S.X₂, W)) (ht : S.g.app W t = 0) : ∃ u, S.f.app W u = t :=
    (QCoh.exact_app_of_exact_of_mono hS.exact W t).1 ht
  have hz (W : X.Opens) (u : Γ(S.X₁, W)) : S.g.app W (S.f.app W u) = 0 :=
    (QCoh.exact_app_of_exact_of_mono hS.exact W _).2 ⟨u, rfl⟩
  have hinj (W : X.Opens) : Function.Injective (appLinear S.f W) :=
    QCoh.injective_app_of_mono S.f W
  refine ShortComplex.ShortExact.mk' (DualExact.exact_of_locally _ fun V x hx => ?_)
    (QCoh.mono_of_locally_app_injective _ fun V x hx => ?_)
    (QCoh.epi_of_locally_app_surjective _ fun V x hx => ?_)
  · obtain ⟨U, hU, hxU, σ, hσ, hg⟩ := DualExact.exists_local_section S.g h₃ hx
    refine ⟨U, hU, hxU, fun (l : Γ(homMod S.X₂ G, U)) (hl : (homMap S.f (𝟙 G)).app U l = 0) =>
      ⟨homMk (fun W h => homApp l h ∘ₗ σ W h) fun W W' h h' t => ?_, ?_⟩⟩
    · rw [LinearMap.comp_apply, LinearMap.comp_apply, hσ W W' h h', homApp_resM]
    · refine VB.hom_ext fun W h t => ?_
      change homApp l h (σ W h (S.g.app W t)) = _
      obtain ⟨u, hu⟩ := hex W (t - σ W h (S.g.app W t)) (by rw [map_sub, hg, sub_self])
      have : homApp ((homMap S.f (𝟙 G)).app U l) h u = homApp l h (S.f.app W u) := rfl
      rw [hl, hu, map_sub, VB.homApp_zero, LinearMap.zero_apply, eq_comm, sub_eq_zero] at this
      exact this.symm
  · obtain ⟨U, hU, hxU, σ, hσ, hg⟩ := DualExact.exists_local_section S.g h₃ hx
    refine ⟨U, hxU, hU, fun (a b : Γ(homMod S.X₃ G, U)) hab => VB.hom_ext fun W h t => ?_⟩
    rw [← hg W h t]
    exact congrArg (fun ψ : Γ(homMod S.X₂ G, U) => homApp ψ h (σ W h t)) hab
  · obtain ⟨U, hU, hxU, σ, hσ, hg⟩ := DualExact.exists_local_section S.g h₃ hx
    let ρ (W : X.Opens) (h : W ≤ U) : Γ(S.X₂, W) →ₗ[Γ(X, W)] Γ(S.X₁, W) :=
      LinearMap.codRestrictOfInjective (LinearMap.id - σ W h ∘ₗ appLinear S.g W)
        (appLinear S.f W) (hinj W) fun t => hex W _ (by
          change S.g.app W (t - σ W h (S.g.app W t)) = 0
          rw [map_sub, hg, sub_self])
    have hρ (W : X.Opens) (h : W ≤ U) (t : Γ(S.X₂, W)) :
        S.f.app W (ρ W h t) = t - σ W h (S.g.app W t) :=
      LinearMap.codRestrictOfInjective_comp_apply _ (appLinear S.f W) _ _ t
    refine ⟨U, hxU, hU, fun (l : Γ(homMod S.X₁ G, U)) =>
      ⟨homMk (fun W h => homApp l h ∘ₗ ρ W h) fun W W' h h' t => ?_, ?_⟩⟩
    · rw [LinearMap.comp_apply, LinearMap.comp_apply, ← homApp_resM]
      congr 1
      apply hinj W'
      rw [appLinear_apply, appLinear_apply, app_resM, hρ, hρ, map_sub, app_resM, hσ W W' h h']
    · refine VB.hom_ext fun W h u => ?_
      change homApp l h (ρ W h (S.f.app W u)) = _
      congr 1
      apply hinj W
      rw [appLinear_apply, appLinear_apply, hρ, hz, map_zero, sub_zero]

theorem resM_frame_eq {A : X.Modules} (c d : VB.Chart A 1) {W : X.Opens} (hc : W ≤ c.U)
    (hd : W ≤ d.U) : resM A hc (c.e 0) =
      (((c.isFrame.detUnit d.isFrame hc hd)⁻¹ : Γ(X, W)ˣ) : Γ(X, W)) • resM A hd (d.e 0) := by
  change _ = (d.isFrame.basis hd).det (c.isFrame.basis hc) • _
  rw [Module.Basis.det_apply, Matrix.det_unique, Module.Basis.toMatrix_apply]
  have := (d.isFrame.basis hd).sum_repr (c.isFrame.basis hc 0)
  rw [Fin.sum_univ_one] at this
  simp only [IsFrame.basis_apply] at this ⊢
  exact this.symm

theorem resM_homApp_resM {A G : X.Modules} {U V W T : X.Opens} (φ : Γ(homMod A G, V))
    (e : Γ(A, U)) (hV : W ≤ V) (hU : W ≤ U) (h : T ≤ W) :
    resM G h (homApp φ hV (resM A hU e)) = homApp φ (h.trans hV) (resM A (h.trans hU) e) := by
  rw [← homApp_resM, resM_resM]

theorem homApp_frame_eq {A G : X.Modules} {V W : X.Opens} (φ : Γ(homMod A G, V))
    (c d : VB.Chart A 1) (hV : W ≤ V) (hc : W ≤ c.U) (hd : W ≤ d.U) :
    homApp φ hV (resM A hc (c.e 0)) = resG X (le_inf hc hd)
      (((c.isFrame.detUnit d.isFrame inf_le_left inf_le_right)⁻¹ : Γ(X, c.U ⊓ d.U)ˣ) :
        Γ(X, c.U ⊓ d.U)) • homApp φ hV (resM A hd (d.e 0)) := by
  rw [resM_frame_eq c d hc hd, map_smul,
    ← IsFrame.res_detUnit c.isFrame d.isFrame inf_le_left inf_le_right (le_inf hc hd), ← map_inv]
  rfl

def evalHom (A G : X.Modules) : homMod A G ⟶ twist G (CechPic.dual (VB.det A 1)) :=
  GlobalTheory.LB.homOfLinear (fun V =>
    { toFun φ := Twist.mkSec (fun c : VB.Chart A 1 =>
        homApp φ (inf_le_left : V ⊓ c.U ≤ V) (resM A inf_le_right (c.e 0)))
        fun (c d : VB.Chart A 1) => (resM_homApp_resM φ _ _ _ _).trans
          ((homApp_frame_eq φ c d _ _ inf_le_right).trans
            (congrArg _ (resM_homApp_resM φ _ _ _ _).symm))
      map_add' φ ψ := Twist.sec_ext fun c => rfl
      map_smul' a φ := Twist.sec_ext fun c => rfl })
    fun h φ => Twist.sec_ext fun c : VB.Chart A 1 =>
      (resM_homApp_resM φ (c.e 0) inf_le_left inf_le_right (inf_le_inf_right _ h)).symm

theorem bijective_eval {A : X.Modules} (G : X.Modules) (c : VB.Chart A 1) {W : X.Opens}
    (hW : W ≤ c.U) : Function.Bijective fun φ : Γ(homMod A G, W) =>
      homApp φ le_rfl (resM A hW (c.e 0)) := by
  refine ⟨fun φ ψ e => VB.hom_ext fun T h s => ?_, fun t => ⟨homMk (fun T h =>
    ((c.isFrame.basis (h.trans hW)).coord 0).smulRight (resM G h t)) fun T T' h h' s => ?_, ?_⟩⟩
  · have e' := congrArg (resM G h) e
    simp only [← homApp_resM, resM_resM] at e'
    rw [← (c.isFrame.basis (h.trans hW)).sum_repr s, Fin.sum_univ_one, map_smul, map_smul,
      IsFrame.basis_apply]
    exact congrArg _ e'
  · simp only [LinearMap.smulRight_apply, Module.Basis.coord_apply, resM_smul, resM_resM]
    rw [← IsFrame.repr_resM]
  · simp only [VB.homApp_homMk, LinearMap.smulRight_apply, Module.Basis.coord_apply, resM_self]
    rw [← c.isFrame.basis_apply hW, Module.Basis.repr_self, Finsupp.single_eq_same, one_smul]

theorem isIso_evalHom {A : X.Modules} (h : IsVB A 1) (G : X.Modules) : IsIso (evalHom A G) := by
  refine Twist.isIso_of_cover _ (U := fun c : VB.Chart A 1 => c.U) h.isLB_det.cover
    fun c W hW => ?_
  rw [← (Twist.chartEquiv (F := G) (isLB_dual h.isLB_det) c hW).bijective.of_comp_iff']
  convert bijective_eval G c hW using 2 with φ
  exact resM_homApp_resM φ (c.e 0) inf_le_left inf_le_right (le_inf le_rfl hW)

variable {R : Type} [CommRing R] [Algebra R Γ(X, ⊤)] {F : X.Modules}

theorem chiLenPic_homMod (S : ShortComplex X.Modules) (hS : S.ShortExact) (h₁ : IsVB S.X₁ 1)
    (h₃ : IsVB S.X₃ 1) (hF : FiniteLenTwists R F) (c : Pic X) :
    chiLenPic R (homMod S.X₂ F) c =
      chiLenPic R F (c - cls _ h₃.isLB_det) + chiLenPic R F (c - cls _ h₁.isLB_det) := by
  have := isIso_evalHom h₁ F
  have := isIso_evalHom h₃ F
  have e := congrFun (chiLenPic_shortExact (shortExact_homMod S hS h₃ F)
    ((hF.twist (isLB_dual h₃.isLB_det)).of_iso (asIso (evalHom S.X₃ F)).symm)
    ((hF.twist (isLB_dual h₁.isLB_det)).of_iso (asIso (evalHom S.X₁ F)).symm)) c
  refine e.trans ?_
  change chiLenPic R (homMod S.X₃ F) c + chiLenPic R (homMod S.X₁ F) c = _
  rw [chiLenPic_congr R (asIso (evalHom S.X₃ F)), chiLenPic_congr R (asIso (evalHom S.X₁ F)),
    chiLenPic_twist R F (isLB_dual h₃.isLB_det), chiLenPic_twist R F (isLB_dual h₁.isLB_det),
    eq_neg_of_add_eq_zero_left (cls_dual_add h₃.isLB_det),
    eq_neg_of_add_eq_zero_left (cls_dual_add h₁.isLB_det), neg_add_eq_sub, neg_add_eq_sub]

theorem chiLenPic_homMod_flag {E : X.Modules} (fl : GlobalTheory.Vert.Flag E 2) (hF : FiniteLenTwists R F)
    (c : Pic X) : chiLenPic R (homMod E F) c =
      chiLenPic R F (c - cls _ (fl.isLB_root 1)) + chiLenPic R F (c - cls _ (fl.isLB_root 0)) := by
  have h₁ : IsVB (fl.F (0 : Fin 2).succ) 1 := fl.isVB _
  have h₃ : IsVB (cokernel (fl.ι (0 : Fin 2).succ)) 1 := fl.isVB_cokernel _
  have hS : (ShortComplex.mk (fl.ι (0 : Fin 2).succ) (cokernel.π _)
    (cokernel.condition _)).ShortExact := { exact := ShortComplex.exact_cokernel _ }
  have h0 : IsZero (fl.F (0 : Fin 2).castSucc) := VB.isVB_zero_iff.1 (fl.isVB _)
  have e₁ : cls _ h₁.isLB_det = cls _ (fl.isLB_root 0) :=
    ((cls_eq_iff (fl.isLB_root 0) h₁.isLB_det).2 ((fl.isVB_gr 0).lbIso_det_of_iso
      (cokernelIsoOfEq (h0.eq_of_src _ 0) ≪≫ cokernelZeroIsoTarget))).symm
  have e₃ : cls _ h₃.isLB_det = cls _ (fl.isLB_root 1) := by
    obtain ⟨h, e⟩ := VBExt.isVB_and_cls_det_of_shortExact X _ 1 1 hS h₁ h₃
    have e' := fl.cls_det
    rw [Fin.sum_univ_two, ← e₁] at e'
    exact add_left_cancel (e.symm.trans e')
  rw [← e₁, ← e₃]
  exact chiLenPic_homMod _ hS h₁ h₃ hF c

theorem bwdDiff_bwdDiff_eq_zero {E : X.Modules} (f g : GlobalTheory.Vert.Flag E 2)
    (hF : FiniteLenTwists R F) :
    bwdDiff (cls _ (f.isLB_root 0) - cls _ (g.isLB_root 0))
      (bwdDiff (cls _ (g.isLB_root 1) - cls _ (f.isLB_root 0)) (chiLenPic R F)) = 0 := by
  funext c
  have e := f.cls_det.symm.trans g.cls_det
  rw [Fin.sum_univ_two, Fin.sum_univ_two] at e
  have h := (chiLenPic_homMod_flag f hF (c + cls _ (g.isLB_root 0))).symm.trans
    (chiLenPic_homMod_flag g hF _)
  generalize cls _ (f.isLB_root 0) = l at *
  generalize cls _ (f.isLB_root 1) = l' at *
  generalize cls _ (g.isLB_root 0) = m at *
  generalize cls _ (g.isLB_root 1) = m' at *
  obtain rfl : l' = m + m' - l := by rw [← e]; abel
  rw [show c + m - (m + m' - l) = c - (m' - l) by abel, show c + m - l = c - (l - m) by abel,
    show c + m - m' = c - (l - m) - (m' - l) by abel, add_sub_cancel_right] at h
  simp only [bwdDiff_apply, Pi.zero_apply]
  linear_combination -h

end Hom

theorem capDeg_vp_eq_zero : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X → ∀ (W W' : B.X.Modules) (ψ : B.GenIso W W') (R R' : GlobalTheory.Vert.Model.FlagPair ψ 2) (D : B.VDivQ) (y : PicSym B.X), B.capDeg_vp p D ((c1 (R'.fl'.root 1) (R'.fl'.isLB_root 1) - c1 (R.fl'.root 0) (R.fl'.isLB_root 0)) * (c1 (R.fl'.root 0) (R.fl'.isLB_root 0) - c1 (R'.fl'.root 0) (R'.fl'.isLB_root 0)) * y) = 0 := by
  intro O _ _ _ p _ _ _ B _ W W' ψ R R' D y
  rw [← firstChernPic_class, ← firstChernPic_class, ← firstChernPic_class, ← map_sub, ← map_sub]
  have key (I : B.effVert) := bwdDiff_bwdDiff_eq_zero R.fl' R'.fl'
    (Vert.Model.isVertical_divMod I).finiteLenTwists
  generalize cls _ (R'.fl'.isLB_root 1) - cls _ (R.fl'.isLB_root 0) = a at *
  generalize cls _ (R.fl'.isLB_root 0) - cls _ (R'.fl'.isLB_root 0) = b at *
  have heff (I : B.effVert) : Vert.Model.effDeg I (firstChernPic a * firstChernPic b * y) = 0 := by
    refine LinearMap.congr_fun (picSym_linearMap_ext
      (l := Vert.Model.effDeg I ∘ₗ LinearMap.mulLeft ℚ (firstChernPic a * firstChernPic b)) (l' := 0)
      fun n g => ?_) y
    have h := picForm_prod (Vert.Model.isVertical_divMod I).diffVanish
      (Fin.cons a (Fin.cons b g : Fin (n + 1) → _) : Fin (n + 1 + 1) → _)
    rw [multiDiff_cons', multiDiff_cons', key I, multiDiff_eq_shiftAct, map_zero] at h
    simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Pi.zero_apply, Int.cast_zero,
      ite_self] at h
    rw [LinearMap.comp_apply, LinearMap.mulLeft_apply, mul_assoc]
    exact h
  induction D using TensorProduct.induction_on with
  | zero => simp
  | tmul q D =>
    obtain ⟨I, J, rfl⟩ := Vert.Model.exists_eq_ofEff_sub D
    simp [Vert.Model.capDeg_vp, Vert.Model.vDegQ, heff]
  | add D D' h h' => rw [map_add, LinearMap.add_apply, h, h', add_zero]

end GlobalTheory.RankTwoChern

theorem _root_.GlobalTheory.T.flag_pair_capDeg_difference_zero : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X → ∀ (W W' : B.X.Modules) (ψ : B.GenIso W W') (R R' : GlobalTheory.Vert.Model.FlagPair ψ 2) (D : B.VDivQ) (y : PicSym B.X), B.capDeg_vp p D ((c1 (R'.fl'.root 1) (R'.fl'.isLB_root 1) - c1 (R.fl'.root 0) (R.fl'.isLB_root 0)) * (c1 (R.fl'.root 0) (R.fl'.isLB_root 0) - c1 (R'.fl'.root 0) (R'.fl'.isLB_root 0)) * y) = 0 :=
  GlobalTheory.RankTwoChern.capDeg_vp_eq_zero
