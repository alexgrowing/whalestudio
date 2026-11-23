import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteOfLeOfIsNoetherianRingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeOfThickeningsLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleTrivialOnFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSquareUnique
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjBySmoothIsProperGeometricallyIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NsmulMemSmulTop
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianLiftAmpleBundleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumLift

theorem ker_factor_sq {R : Type} [CommRing R] (J : Ideal R) (e : ℕ) :
    RingHom.ker (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1))) :
      R ⧸ J ^ (e + 1 + 1) →+* R ⧸ J ^ (e + 1)) ^ 2 = ⊥ := by
  rw [pow_two, eq_bot_iff]
  refine Ideal.mul_le.2 fun x hx y hy => ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [RingHom.mem_ker, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at hx hy
  rw [Ideal.mem_bot, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  have h := Ideal.mul_mem_mul hx hy
  rw [← pow_add] at h
  exact Ideal.pow_le_pow_right (by omega) h

theorem exists_lift_of_step (step : ∀ (R R₀ : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing R₀] [IsLocalRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (Y₀ : Over (Sp R₀)) [GrpObj Y₀], IsAbelianScheme Y₀ → ∀ L₀ : LB Y₀.left, L₀.IsLB → RelAmple Y₀ L₀ → KTriv Y₀ L₀ → ∃ (Y : Over (Sp R)) (_ : GrpObj Y) (L : LB Y.left) (i : Y₀.left ⟶ Y.left), IsAbelianScheme Y ∧ L.IsLB ∧ RelAmple Y L ∧ KTriv Y L ∧ IsGrpPullback Y₀ Y (spMap π) i ∧ LBIso L₀ (L.pull i)) : ∀ (R₁ R : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] [IsNoetherianRing R₁] [CommRing R] [IsDomain R] [IsLocalRing R], IsAdicComplete (maximalIdeal R₁) R₁ → ∀ π : R₁ →+* R, Function.Surjective π → ∀ Q : GlobalTheory.PolDeg.Data R, ∃ (A : Over (Sp R₁)) (_ : GrpObj A) (_ : IsCommMonObj A) (i : Q.B.left ⟶ A.left) (l : (Q.B ⊗ Q.B).left ⟶ (A ⊗ A).left) (N : LB (A ⊗ A).left), IsAbelianScheme A ∧ IsGrpPullback Q.B A (spMap π) i ∧ IsSquare i l ∧ N.IsLB ∧ GlobalTheory.AbDual.IsAdditive N ∧ GlobalTheory.AbDual.IsAdditive (GlobalTheory.AbDual.swap N) ∧ LBIso (N.pull l) (abelian₂ Q.B Q.M.L) := by
  intro R₁ R _ _ _ _ _ _ _ hc π hπ Q
  set I := RingHom.ker π with hI
  have hItop : I ≠ ⊤ := by
    intro h
    have h1 : (1 : R₁) ∈ I := h ▸ Submodule.mem_top
    rw [hI, RingHom.mem_ker, map_one] at h1
    exact one_ne_zero h1
  have hIc : IsAdicComplete I R₁ := GlobalTheory.T.isAdicComplete_of_le_of_isNoetherianRing' R₁ I (maximalIdeal R₁) (le_maximalIdeal hItop) hc
  have hne : ∀ e : ℕ, I ^ (e + 1) ≠ ⊤ := fun e h =>
    hItop (top_le_iff.1 (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero e)))
  haveI hnt : ∀ e : ℕ, Nontrivial (R₁ ⧸ I ^ (e + 1)) := fun e => Ideal.Quotient.nontrivial_iff.2 (hne e)
  haveI hloc : ∀ e : ℕ, IsLocalRing (R₁ ⧸ I ^ (e + 1)) := fun e =>
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  let St : ℕ → Type 1 := fun e => Σ Y : Over (Sp (R₁ ⧸ I ^ (e + 1))), Σ _ : GrpObj Y,
    {L : LB Y.left // IsAbelianScheme Y ∧ L.IsLB ∧ RelAmple Y L ∧ KTriv Y L}
  have hstep : ∀ (e : ℕ) (y : St e), ∃ (y' : St (e + 1)) (i : y.1.left ⟶ y'.1.left),
      @IsGrpPullback _ _ y.1 y.2.1 y'.1 y'.2.1 (thickTrans R₁ I e) i ∧ LBIso y.2.2.1 (y'.2.2.1.pull i) := by
    rintro e ⟨Y, g, L, hA, hL, ha, hK⟩
    obtain ⟨Y', g', L', i, hA', hL', ha', hK', hi, hLi⟩ := step (R₁ ⧸ I ^ (e + 1 + 1)) (R₁ ⧸ I ^ (e + 1))
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1))))
      (Ideal.Quotient.factor_surjective _) (ker_factor_sq I e) Y hA L hL ha hK
    exact ⟨⟨Y', g', L', hA', hL', ha', hK'⟩, i, hi, hLi⟩
  choose nx β hβ hLβ using hstep
  let e₀ : R₁ ⧸ I ^ (0 + 1) ≃+* R :=
    (Ideal.quotEquivOfEq (by rw [zero_add, pow_one])).trans (RingHom.quotientKerEquivOfSurjective hπ)
  let s : Sp (R₁ ⧸ I ^ (0 + 1)) ⟶ Sp R := spMap (e₀.symm : R →+* R₁ ⧸ I ^ (0 + 1))
  let t : Sp R ⟶ Sp (R₁ ⧸ I ^ (0 + 1)) := spMap (e₀ : R₁ ⧸ I ^ (0 + 1) →+* R)
  have hts : t ≫ s = 𝟙 _ := by
    simp only [t, s, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [RingEquiv.comp_symm]
    simp
  have htπ : t ≫ thick R₁ I 0 = spMap π := by
    simp only [t, thick, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
  let Y₀ : Over (Sp (R₁ ⧸ I ^ (0 + 1))) := (Over.pullback s).obj Q.B
  let g₀ : Y₀.left ⟶ Q.B.left := pullback.fst Q.B.hom s
  have G₀ : IsGrpPullback Y₀ Q.B s g₀ := isGrpPullback_pullback Q.B s
  have hL₀ : (Q.M.L.pull g₀).IsLB := pull_isLB Q.M.isLB g₀
  have hA₀ : IsAbelianScheme Y₀ := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback Q.isAb G₀
  haveI := Q.isAb.proper
  have ha₀ : RelAmple Y₀ (Q.M.L.pull g₀) := GlobalTheory.AmpleBaseChange.relAmple_of_isPullback Q.M.isLB Q.ample G₀.1
  have hK₀ : KTriv Y₀ (Q.M.L.pull g₀) := by
    obtain ⟨w, hw⟩ : LBIso (Q.M.L.pull g₀) (Q.M.L.pull g₀) := (GlobalTheory.CechPic.cls_eq_iff hL₀ hL₀).1 rfl
    exact kTriv_pull G₀ Q.M.isLB hL₀ ((isGen_iff w).1 hw) Q.ktriv
  let y₀ : St 0 := ⟨Y₀, inferInstance, Q.M.L.pull g₀, hA₀, hL₀, ha₀, hK₀⟩
  let Y : ∀ n : ℕ, St n := fun n => Nat.rec (motive := fun n => St n) y₀ (fun n y => nx n y) n
  letI : ∀ e, GrpObj (Y e).1 := fun e => (Y e).2.1
  obtain ⟨B, _, M, b, hB, hM, haM, hb, -, hiso⟩ := GlobalTheory.AlgGroup.exists_abelianScheme_of_tower R₁ I hItop hIc hc
    (fun e => (Y e).1) (fun e => β e (Y e)) (fun e => (Y e).2.2.2.1) (fun e => hβ e (Y e))
    (fun e => (Y e).2.2.1) (fun e => (Y e).2.2.2.2.1) (fun e => hLβ e (Y e)) (Y 0).2.2.2.2.2.1
  haveI : IsCommMonObj B := hB.comm
  let φ : Q.B.left ⟶ Y₀.left := pullback.lift (𝟙 _) (Q.B.hom ≫ t)
    (by rw [Category.id_comp, Category.assoc, hts, Category.comp_id])
  have hφ₁ : φ ≫ g₀ = 𝟙 _ := pullback.lift_fst _ _ _
  have hφ₂ : φ ≫ Y₀.hom = Q.B.hom ≫ t := pullback.lift_snd _ _ _
  haveI : IsMonHom (Iso.refl Q.B).hom := inferInstanceAs (IsMonHom (𝟙 Q.B))
  have n₀ : IsGrpPullback Q.B Q.B (t ≫ s) (φ ≫ g₀) :=
    (isGrpPullback_of_iso (Iso.refl Q.B)).congr hts.symm hφ₁.symm
  have hcan : IsGrpPullback Q.B Y₀ t φ := IsGrpPullback.cancel G₀ n₀ hφ₂
  have hi : IsGrpPullback Q.B B (spMap π) (φ ≫ b 0) := (hcan.comp (hb 0)).congr htπ rfl
  have hLi : LBIso Q.M.L (M.pull (φ ≫ b 0)) := by
    refine (GlobalTheory.CechPic.cls_eq_iff Q.M.isLB (pull_isLB hM _)).1 ?_
    have a₂ : GlobalTheory.CechPic.cls _ hL₀ = GlobalTheory.CechPic.cls _ (pull_isLB hM (b 0)) :=
      (GlobalTheory.CechPic.cls_eq_iff _ _).2 (hiso 0)
    rw [GlobalTheory.CechPic.cls_pull hM, GlobalTheory.CechPic.pull_comp, ← GlobalTheory.CechPic.cls_pull hM (b 0) (pull_isLB hM (b 0)), ← a₂,
      GlobalTheory.CechPic.cls_pull Q.M.isLB, ← GlobalTheory.CechPic.pull_comp, hφ₁, GlobalTheory.CechPic.pull_id]
  have hJ : I ^ (0 + 1) ≤ Ideal.jacobson ⊥ :=
    (Ideal.pow_le_self (Nat.succ_ne_zero 0)).trans (IsAdicComplete.le_jacobson_bot I)
  have hK : KTriv B M := GlobalTheory.T.line_bundle_trivial_on_fibre R₁ (I ^ (0 + 1)) hJ B hB M hM haM Y₀ (b 0) (hb 0) _ hL₀ (hiso 0) hK₀
  have hP := GlobalTheory.AbDual.isPerfect_lam hM hK
  obtain ⟨H, hH, aH⟩ := GlobalTheory.BirigidLift.exists_relAmple_prod hB hB hM haM hM haM
  obtain ⟨a₁, a₂⟩ := GlobalTheory.BirigidLift.additive_of_triv hB hB hH aH hP.isLB hP.zero_left hP.zero_right
  have w : (φ ≫ b 0) ≫ B.hom = Q.B.hom ≫ spMap π := hi.1.w
  exact ⟨B, inferInstance, hB.comm, φ ≫ b 0, _, abelian₂ B M, hB, hi, GlobalTheory.LamPull.exists_isSquare w, hP.isLB, a₁, a₂,
    (GlobalTheory.LamPull.lbIso_lam_pull hi hM Q.M.isLB hLi (GlobalTheory.LamPull.exists_isSquare w)).symm⟩

theorem exists_lift : ∀ (R₁ R : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] [IsNoetherianRing R₁] [CommRing R] [IsDomain R] [IsLocalRing R], IsAdicComplete (maximalIdeal R₁) R₁ → ∀ π : R₁ →+* R, Function.Surjective π → ∀ Q : GlobalTheory.PolDeg.Data R, ∃ (A : Over (Sp R₁)) (_ : GrpObj A) (_ : IsCommMonObj A) (i : Q.B.left ⟶ A.left) (l : (Q.B ⊗ Q.B).left ⟶ (A ⊗ A).left) (N : LB (A ⊗ A).left), IsAbelianScheme A ∧ IsGrpPullback Q.B A (spMap π) i ∧ IsSquare i l ∧ N.IsLB ∧ GlobalTheory.AbDual.IsAdditive N ∧ GlobalTheory.AbDual.IsAdditive (GlobalTheory.AbDual.swap N) ∧ LBIso (N.pull l) (abelian₂ Q.B Q.M.L) :=
  exists_lift_of_step GlobalTheory.T.exists_abelian_lift_ample_bundle

end GlobalTheory.MumLift
