import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOfPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTauLattice
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsUniqueEqConstMulEllTheta
import Development.AbelianVarietyTheory.Definitions.Divisors.PerFactor

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg.TautBaseModel

theorem exists_tautBase {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] [IsNoetherianRing W] (b : o →+* W)
    (P : PolAV (Sp W)) (r : ℕ) (x : Fin r → (𝟙_ (Over (Sp W)) ⟶ P.A)) :
    ∃ T : TautBase o W, T.b = b ∧ T.g = P.g ∧ ∃ (hB : T.B = P.A) (hr : T.r = r), HEq T.grp P.grp ∧ HEq T.M.L P.L ∧
      ∀ i : Fin T.r, HEq (T.c₀ (Pi.single i 1)) (x (Fin.cast hr i)) := by
  haveI := P.isAb.comm
  obtain ⟨rig, hrig⟩ := P.rigid
  let M : RigLB P.A := ⟨P.L, rig, P.isLB, hrig⟩
  have hC : CubeSt := GlobalTheory.abelianSchemeLaws_all.1.cube
  obtain ⟨cub⟩ := (hC (Sp W) P M rfl).1
  let c : (Fin r → ℤ) → (𝟙_ (Over (Sp W)) ⟶ P.A) := fun a => ∏ i, x i ^ a i
  have hc : ∀ a a', c (a + a') = c a * c a' := fun a a' => by
    simp only [c, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]
  obtain ⟨τ, h₁, h₂, h₃⟩ := GlobalTheory.TauLocal.exists_tau_local M cub c hc
  refine ⟨{ b := b, B := P.A, isAb := P.isAb, g := P.g, smoothDim := P.smoothDim, M := M, cub := cub,
            ample := P.ample, ktriv := P.ktriv, r := r, c₀ := c, c₀_add := hc, τ₀ := τ, τ₀_gen := h₁,
            τ₀_symm := h₂, τ₀_add := h₃ }, rfl, rfl, rfl, rfl, HEq.rfl, HEq.rfl, fun i => heq_of_eq ?_⟩
  show ∏ j, x j ^ (Pi.single i (1 : ℤ) : Fin r → ℤ) j = x i
  rw [Finset.prod_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zpow_zero]) (by simp)]
  simp

theorem exists_tautBase_curve {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] [IsNoetherianRing W] (b : o →+* W)
    (h37 : IsUnit (37 : W)) : ∃ T : TautBase o W, T.b = b ∧ T.g = 1 ∧ T.r = 1 ∧ (∀ t : T.M.L.Gen, ¬ t.IsGen) ∧
    ∃ a, T.c₀ a ≠ 1 := by
  let E : _root_.WeierstrassCurve W := ⟨0, 0, 1, -1, 0⟩
  haveI : E.IsElliptic := ⟨by
    have : E.Δ = 37 := by
      norm_num [E, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
        WeierstrassCurve.b₈]
    rw [this]
    exact h37⟩
  have he : E.toAffine.Equation 0 0 := by
    rw [WeierstrassCurve.Affine.equation_iff]; simp [E]
  let P : PolAV (Sp W) := GlobalTheory.WeierstrassCurve.ellPolAV E
  let x : 𝟙_ (Over (Sp W)) ⟶ P.A :=
    Over.homMk (GlobalTheory.WeierstrassCurve.pt E (A := W) ![0, 0, 1] (GlobalTheory.WeierstrassCurve.isUnimodularSol_some he))
      ((GlobalTheory.WeierstrassCurve.pt_toSpec E _ _).trans (Spec.map_id _))
  have hx : x ≠ 1 := fun e => GlobalTheory.WeierstrassCurve.pt_some_ne_zero E he (by
    have e' := congrArg (fun q => q.left) e
    refine e'.trans ?_
    rw [← GlobalTheory.WeierstrassCurve.eSec_ellPolAV E, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    rfl)
  obtain ⟨T, hb, hg, hB, hr, hgrp, hL, hc⟩ := exists_tautBase b P 1 (fun _ => x)
  refine ⟨T, hb, hg, hr, ?_⟩
  obtain ⟨b', B, isAb, g, sm, M, cub, am, kt, r, c, ca, τ, τg, τs, τa⟩ := T
  dsimp only at hg hB hr hgrp hL hc
  subst hB hr
  cases hgrp
  refine ⟨?_, Pi.single 0 1, fun e => hx ((eq_of_heq (hc 0)).symm.trans e)⟩
  show ∀ t : M.L.Gen, ¬ t.IsGen
  rw [eq_of_heq hL]
  exact GlobalTheory.WeierstrassCurve.not_isGen_ellPolAV E

theorem exists_tautBase_rat : ∃ T : TautBase ℤ ℚ, T.g = 1 ∧ T.r = 1 ∧ (∀ t : T.M.L.Gen, ¬ t.IsGen) ∧
    ∃ a, T.c₀ a ≠ 1 := by
  obtain ⟨T, -, h⟩ := exists_tautBase_curve (Int.castRingHom ℚ) (Ne.isUnit (by norm_num))
  exact ⟨T, h⟩

theorem exists_tautBase_two_adic : ∃ T : TautBase ℤ ℤ_[2], T.g = 1 ∧ T.r = 1 ∧ (∀ t : T.M.L.Gen, ¬ t.IsGen) ∧
    ∃ a, T.c₀ a ≠ 1 := by
  have h : IsUnit (37 : ℤ_[2]) := by
    have := (PadicInt.norm_natCast_eq_one_iff (p := 2) (n := 37)).2 (by norm_num)
    exact PadicInt.isUnit_iff.2 (by exact_mod_cast this)
  obtain ⟨T, -, h⟩ := exists_tautBase_curve (Int.castRingHom ℤ_[2]) h
  exact ⟨T, h⟩

variable {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W)

theorem c₀_zero : T.c₀ 0 = 1 := mul_eq_left.1 ((T.c₀_add 0 0).symm.trans (by rw [add_zero]))

theorem val_τ₀_zero (a : Fin T.r → ℤ) (z J) (hJ : Good T.M.L z J) : val (T.τ₀ 0 a) (𝟙 _) z J = 1 := by
  have h := T.τ₀_add 0 0 a z J hJ
  have f : cubV T.cub z J (T.c₀ 0) (T.c₀ 0) (T.c₀ a) = 1 := by
    rw [c₀_zero]; exact (isCub_cubV T.cub hJ).face _ _
  rw [f, _root_.mul_one, add_zero] at h
  exact mul_eq_left.1 h.symm

theorem τ₀_add_right (a a' a'' : Fin T.r → ℤ) (z J) (hJ : Good T.M.L z J) :
    val (T.τ₀ a (a' + a'')) (𝟙 _) z J * cubV T.cub z J (T.c₀ a) (T.c₀ a') (T.c₀ a'') =
      val (T.τ₀ a a') (𝟙 _) z J * val (T.τ₀ a a'') (𝟙 _) z J := by
  have h := isCub_cubV T.cub hJ
  rw [T.τ₀_symm a _ z J hJ, T.τ₀_symm a a' z J hJ, T.τ₀_symm a a'' z J hJ, h.s01, h.s12]
  exact T.τ₀_add a' a'' a z J hJ

theorem exists_good_choice : ∃ (z : (𝟙_ (Over (Sp W))).left) (J : _), Good T.M.L z J := by
  choose J hJ using fun ψ : (𝟙_ (Over (Sp W))).left ⟶ T.B.left => exists_chart T.M.isLB (ψ (closedPoint W))
  exact ⟨closedPoint W, J, hJ⟩

theorem val_τ₀_torus (b : o →+* W) (r : ℕ) (u : Γ((𝟙_ (Over (Sp W))).left, ⊤)ˣ)
    (β : LinearMap.BilinForm ℤ (Fin r → ℤ)) (hβ : ∀ a a', β a a' = β a' a) (a a' : Fin r → ℤ) (z J)
    (hJ : Good (TautBase.torus b r u β hβ).M.L z J) :
    val ((TautBase.torus b r u β hβ).τ₀ a a') (𝟙 _) z J = gm (𝟙 _) z ⊤ (u ^ β a a') :=
  gm_res _ z _ (hJ.mem _ _) _

theorem prod_lamPts_symm {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] {Z : Over S} (x y : Z ⟶ B) {U : Type}
    [CommGroup U] (h : (Z.left ⟶ B.left) → U) : ∏ i, h (lamPts x y i) ^ negε i = ∏ i, h (lamPts y x i) ^ negε i := by
  simp only [Fin.prod_univ_four]
  show h (x * y).left ^ (-1 : ℤ) * h x.left ^ (1 : ℤ) * h y.left ^ (1 : ℤ) * h (1 : Z ⟶ B).left ^ (-1 : ℤ) =
    h (y * x).left ^ (-1 : ℤ) * h y.left ^ (1 : ℤ) * h x.left ^ (1 : ℤ) * h (1 : Z ⟶ B).left ^ (-1 : ℤ)
  rw [mul_comm y x, mul_right_comm _ (h x.left ^ (1 : ℤ))]

open InhTate in

theorem tauCoord_symm {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (Q : Data R) (a b : Q.X)
    (k k' : (FractionRing R)ˣ) (h : Q.TauCoord a b k) (h' : Q.TauCoord b a k') :
    ∃ x x' : R, IsUnit x ∧ IsUnit x' ∧ (k : FractionRing R) * algebraMap R _ x = k' * algebraMap R _ x' := by
  obtain ⟨u, hu, e⟩ := h
  obtain ⟨u', hu', e'⟩ := h'
  obtain ⟨jj, hjj⟩ := GlobalTheory.TauLocal.exists_chart_all Q.M
  have key : ∀ (p q : 𝟙_ (Over (Sp R)) ⟶ Q.B) (t : LB.Gen (LB.LinComb Q.M.L (lamPts p q) negε)), t.IsGen →
      ∃ w : Γ(Sp R, ⊤)ˣ, ∀ z J, Good Q.M.L z J → val t (toUnit (TK R)).left z J =
        gm (𝟙 (TK R).left) z ⊤ (pullTop (jK R) w) * ∏ i, (fun ψ => gm ((toUnit (TK R)).left ≫ ψ) z _
          (Q.M.L.g (J ((toUnit (TK R)).left ≫ ψ)) (jj ψ))) (lamPts p q i) ^ negε i := by
    intro p q t ht
    have htop : (⊤ : (𝟙_ (Over (Sp R))).left.Opens) ≤ LB.wchart Q.M.L (lamPts p q) (fun i => jj (lamPts p q i)) :=
      fun y _ => Set.mem_iInter.2 fun i => hjj _ y
    refine ⟨res htop (t.s (fun i => jj (lamPts p q i))), fun z J hJ => ?_⟩
    refine (gen_trans ht _ z (hJ.mem _ _) (htop trivial)).trans ?_
    rw [mul_comm]
    refine congrArg₂ (· * ·) ?_ rfl
    refine (gm_res _ z htop trivial _).symm.trans (Eq.trans ?_ (gm_pull (𝟙 _) (jK R) z ⊤ trivial _).symm)
    rfl
  obtain ⟨w, hw⟩ := key _ _ u hu
  obtain ⟨w', hw'⟩ := key _ _ u' hu'
  have k₁ : unitOn k * pullTop (jK R) w = unitOn k' * pullTop (jK R) w' := GlobalTheory.TauLocal.eq_of_gm Q.M.isLB fun z J hJ => by
    have s := Q.tau_symm a b z J hJ
    rw [e z J hJ, e' z J hJ, hw z J hJ, hw' z J hJ, ← _root_.mul_assoc, ← _root_.mul_assoc] at s
    rw [map_mul, map_mul]
    refine mul_right_cancel (s.trans (congrArg₂ (· * ·) rfl ?_))
    exact prod_lamPts_symm (Q.c b) (Q.c a) (fun ψ => gm ((toUnit (TK R)).left ≫ ψ) z _
      (Q.M.L.g (J ((toUnit (TK R)).left ≫ ψ)) (jj ψ)))
  have nat := fun v : Γ(Sp R, ⊤)ˣ => congrArg (fun g => g.hom v.val)
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  have e₂ := congrArg (fun v => (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom v.val) k₁
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom w.val, (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom w'.val,
    w.isUnit.map _, w'.isUnit.map _, ?_⟩
  refine Eq.trans ?_ (e₂.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ (nat w'))))
  · refine Eq.symm ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ (nat w)))
    exact (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv_hom_id_apply k.val
  · exact (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv_hom_id_apply k'.val

theorem not_exists_data_of_not_symm [IsDomain (MvPowerSeries (Fin 1) ℚ)] :
    ∃ ε : Fin 1 → LinearMap.BilinForm ℤ (Fin 2 → ℤ), ¬ ∃ (Q : Data (MvPowerSeries (Fin 1) ℚ)) (e : Q.X ≃+ (Fin 2 → ℤ)),
      ∀ a b, ∃ k : (FractionRing (MvPowerSeries (Fin 1) ℚ))ˣ,
        (k : FractionRing (MvPowerSeries (Fin 1) ℚ)) = Taut.perFactor ℚ 1 1 1 2 ε (e a) (e b) ∧ Q.TauCoord a b k := by
  refine ⟨fun _ => (LinearMap.mul ℤ ℤ).compl₁₂ (LinearMap.proj 0) (LinearMap.proj 1), fun ⟨Q, e, h⟩ => ?_⟩
  obtain ⟨k, hk, c⟩ := h (e.symm (Pi.single 0 1)) (e.symm (Pi.single 1 1))
  obtain ⟨k', hk', c'⟩ := h (e.symm (Pi.single 1 1)) (e.symm (Pi.single 0 1))
  obtain ⟨x, x', -, hx', e₁⟩ := tauCoord_symm Q _ _ k k' c c'
  rw [hk, hk'] at e₁
  simp [Taut.perFactor, Taut.coordT] at e₁
  rw [← map_mul] at e₁
  have e₂ := IsFractionRing.injective _ _ e₁
  have := (e₂ ▸ hx').map (MvPowerSeries.constantCoeff (σ := Fin 1) (R := ℚ))
  simp at this

theorem not_forall_exists_data : ¬ ∀ {o W : Type} [CommRing o] [CommRing W] [IsDomain W] [IsLocalRing W] [IsNoetherianRing W]
    (T : TautBase o W) (N m n : ℕ) [IsDomain (MvPowerSeries (Fin N) W)]
    (ε : Fin N → LinearMap.BilinForm ℤ (Fin T.r → ℤ)),
    ∃ (Q : Data (MvPowerSeries (Fin N) W)) (e : Q.X ≃+ (Fin T.r → ℤ)) (β : Q.B.left ⟶ T.B.left),
      IsGrpPullback Q.B T.B (spMap MvPowerSeries.C) β ∧
      (∀ a, (Q.c a).left ≫ β = spMap MvPowerSeries.C ≫ (T.c₀ (e a)).left) ∧
      ∀ a b, ∃ k : (FractionRing (MvPowerSeries (Fin N) W))ˣ,
        (k : FractionRing (MvPowerSeries (Fin N) W)) = Taut.perFactor W m N n T.r ε (e a) (e b) ∧ Q.TauCoord a b k := by
  intro h
  haveI : IsDomain (MvPowerSeries (Fin 1) ℚ) := NoZeroDivisors.to_isDomain _
  obtain ⟨ε, hε⟩ := not_exists_data_of_not_symm
  obtain ⟨Q, e, -, -, -, h₁⟩ := h (TautBase.torus (RingHom.id ℚ) 2 1 0 (fun _ _ => rfl)) 1 1 1 ε
  exact hε ⟨Q, e, h₁⟩

end GlobalTheory.PolDeg.TautBaseModel
