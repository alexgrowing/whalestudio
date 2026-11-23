import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UnitThetaConstantsGenerateIntegralTorsionImports
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingStalkGeneric
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionPull
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PrimScale

open TopologicalSpace GlobalTheory.HolHom

theorem chart_one_le {X : Scheme.{0}} (L : LB X) (j : Fin 1 → L.ι) :
    LB.wchart L (fun _ : Fin 1 => 𝟙 X) j ≤ L.U (j 0) := fun _ hy => Set.mem_iInter.1 hy 0

theorem exists_section_firstPower_restrict {X : Scheme.{0}} {L : LB X} (s : L.Sec) : ∃ t : H0 L 1, ∀ j,
    t.f j = (X.presheaf.map (homOfLE (chart_one_le L j)).op).hom (s.f (j 0)) := by
  have le := chart_one_le L
  refine ⟨⟨fun j => (X.presheaf.map (homOfLE (le j)).op).hom (s.f (j 0)),
    fun (i j : Fin 1 → L.ι) => fn_ext fun y hy => ?_⟩, fun _ => rfl⟩
  refine ((gs_res (𝟙 X) y _ hy _).trans (gs_res (𝟙 X) y (le i) hy.1 _)).trans
    ((SecPullIso.gs_sec_trans s (𝟙 X) y (le i hy.1) (le j hy.2)).trans (Eq.symm ((gs_mul (𝟙 X) y _ hy _ _).trans
      (congrArg₂ (· * ·) ((gs_unit (𝟙 X) y _ hy _).trans (congrArg Units.val ?_))
        ((gs_res (𝟙 X) y _ hy _).trans (gs_res (𝟙 X) y (le j) hy.2 _))))))
  refine (gm_linComb L _ _ (𝟙 X) y i j hy.1 hy.2).trans ?_
  simp

theorem valR_mul' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (a b : Γ(X, U)) : valR x U (a * b) = valR x U a * valR x U b := by
  simp only [valR_eq _ _ h, map_mul]

theorem valR_const {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (p : X ⟶ Sp A) (h : x ≫ p = 𝟙 _) (a : A) :
    valR x ⊤ (p.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)) = a := by
  refine (valR_comp x p ⊤ _).symm.trans ?_
  rw [h, valR, dif_pos (show ⊤ ≤ 𝟙 (Sp A) ⁻¹ᵁ ⊤ from le_top)]
  have : Scheme.Hom.appLE (𝟙 (Sp A)) ⊤ ⊤ le_top = 𝟙 _ := (Category.id_comp _).trans ((Sp A).presheaf.map_id _)
  rw [this]
  exact Iso.inv_hom_id_apply _ _

theorem exists_primitive_scaling : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (G : Over (Sp V)) [GrpObj G], IsSemiAbelian G → ∀ (M : LB G.left), M.IsLB → ∀ (Y : Scheme.{0}) (L : LB Y), L.IsLB → ∀ (ψ : pullback G.hom (jK V) ⟶ Y) (w : LB.Iso (M.pull (pullback.fst G.hom (jK V))) (L.pull ψ)), w.IsGen → ∀ θ : LB.Sec L, (∃ z, ψ z ∈ nonzeroLocus θ) → ∃ (ϑ : H0 M 1) (c : FractionRing V), c ≠ 0 ∧ (∃ z ∈ nonzeroLocus ϑ, G.hom z = IsLocalRing.closedPoint V) ∧ ∀ x : Sp (FractionRing V) ⟶ pullback G.hom (jK V), x ≫ pullback.snd G.hom (jK V) = 𝟙 _ → ∀ (i : M.ι) (k : L.ι), ⊤ ≤ (x ≫ pullback.fst G.hom (jK V)) ⁻¹ᵁ M.U i → ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ L.U k → valR x _ (w.s (fun _ => k, fun _ => i)).val * valR (x ≫ pullback.fst G.hom (jK V)) _ (ϑ.f (fun _ => i)) = c * valR (x ≫ ψ) _ (θ.f k) := by
  intro V _ _ _ G _ hG M hM Y L hL ψ w hw θ hθ
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  have := hG.geomConnected
  have := grpObj_geometricallyIntegral_of_smooth _ G
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hK := IsPullback.of_hasPullback G.hom (jK V)
  have hs := IsPullback.of_hasPullback G.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)))
  have := DvrModel.isIntegral_of_geometricallyIntegral hK
  have := DvrModel.isIntegral_of_geometricallyIntegral hs
  obtain ⟨r, hr⟩ := SecPullIso.exists_pull ψ L (M.pull (pullback.fst G.hom (jK V))) w hL (LB.isLB_linComb hM _ _) hw θ
  obtain ⟨n, ⟨σ, hσ, b, x₀, hx₀, hb⟩, -⟩ := DvrModel.existsUnique_zpow_mul_sec hK hs hϖ hM r (by
    obtain ⟨x, hx⟩ := hθ
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 hx
    obtain ⟨a, ha⟩ := exists_chart (L := M.pull (pullback.fst G.hom (jK V))) (LB.isLB_linComb hM _ _) x
    have hk' := Y.basicOpen_le _ hk
    have u := (SecPullIso.isUnit_gs_iff ψ x hk' _).2 hk
    rw [hr x k a hk' ha] at u
    have u' := (SecPullIso.isUnit_gs_iff (𝟙 _) x ha _).1 (isUnit_of_mul_isUnit_right u)
    exact ⟨a, fun h => by rw [h, Scheme.basicOpen_zero] at u'; exact u'⟩)
  have h0 : algebraMap V (FractionRing V) ϖ ^ n ≠ 0 :=
    zpow_ne_zero _ ((map_ne_zero_iff _ (IsFractionRing.injective V _)).2 hϖ.ne_zero)
  obtain ⟨ϑ, hϑ⟩ := exists_section_firstPower_restrict σ
  refine ⟨ϑ, _, h0, ⟨x₀, Opens.mem_iSup.2 ⟨fun _ => b, ?_⟩, hx₀⟩, fun x hx i k hi hk => ?_⟩
  · refine (congrArg G.left.basicOpen (hϑ fun _ => b)).ge ?_
    exact (Scheme.basicOpen_res _ _ _).ge ⟨Set.mem_iInter.2 fun _ => G.left.basicOpen_le _ hb, hb⟩
  · have hi₁ : ⊤ ≤ (x ≫ pullback.fst G.hom (jK V)) ⁻¹ᵁ LB.wchart M (fun _ : Fin 1 => 𝟙 G.left) (fun _ => i) :=
      fun z hz => Set.mem_iInter.2 fun _ => hi hz
    have hi₂ : ⊤ ≤ x ⁻¹ᵁ (M.pull (pullback.fst G.hom (jK V))).U (fun _ => i) := fun z hz => mem_pull.2 (hi hz)
    have hW : ⊤ ≤ x ⁻¹ᵁ ((L.pull ψ).U (fun _ => k) ⊓ (M.pull (pullback.fst G.hom (jK V))).U (fun _ => i)) :=
      fun z hz => ⟨mem_pull.2 (hk hz), hi₂ hz⟩
    have l₁ : (L.pull ψ).U (fun _ => k) ⊓ (M.pull (pullback.fst G.hom (jK V))).U (fun _ => i) ≤ ψ ⁻¹ᵁ L.U k :=
      fun y hy => mem_pull.1 hy.1
    have e₁ : valR (x ≫ pullback.fst G.hom (jK V)) _ (ϑ.f (fun _ => i)) =
        algebraMap V (FractionRing V) ϖ ^ n * valR x _ (r.f fun _ => i) := by
      refine (congrArg (valR _ _) (hϑ fun _ => i)).trans ?_
      refine (valR_res _ _ _ hi₁).trans ((valR_appLE x _ _ _ _ _ hi₂).symm.trans
        ((congrArg (valR x _) (hσ fun _ => i)).trans ((valR_mul' x _ hi₂ _ _).trans (congrArg (· * _) ?_))))
      exact (valR_res x le_top _ hi₂).trans (valR_const x _ hx _)
    have e₂ : (ψ.appLE _ _ l₁).hom (θ.f k) = (show Γ(pullback G.hom (jK V), (L.pull ψ).U (fun _ => k) ⊓
        (M.pull (pullback.fst G.hom (jK V))).U (fun _ => i))ˣ from w.s (fun _ => k, fun _ => i)).val *
          ((pullback G.hom (jK V)).presheaf.map (homOfLE inf_le_right).op).hom (r.f fun _ => i) :=
      fn_ext fun y hy => by
        refine (gs_appLE _ _ _ _ (𝟙 _) y hy _).trans ?_
        rw [Category.id_comp, hr y k _ (l₁ hy) hy.2]
        exact ((gs_mul (𝟙 _) y _ hy _ _).trans (congrArg₂ (· * ·) (gs_unit (𝟙 _) y _ hy _)
          (gs_res (𝟙 _) y _ hy _))).symm
    have e₃ := (valR_appLE x ψ _ _ l₁ _ hW).symm.trans ((congrArg (valR x _) e₂).trans
      ((valR_mul' x _ hW _ _).trans (congrArg (_ * ·) (valR_res x _ _ hW))))
    rw [e₁, e₃]
    exact mul_left_comm _ _ _

end GlobalTheory.PrimScale
