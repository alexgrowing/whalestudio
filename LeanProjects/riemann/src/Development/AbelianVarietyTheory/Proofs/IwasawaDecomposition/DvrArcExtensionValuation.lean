import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmIdempotentAddStarEqOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRationalPair
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.TorRef
open ReciprocityTheory.ChartRestriction.G.DVR
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ArcBuild

open GlobalTheory.TauTwist

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {T : CDVR} {t : SAB H (Sp T.V)}

theorem genRel_psi_D0 (P : PELUnif (maximalIdeal T.V) t) {ϖ : T.V} (hϖ : Irreducible ϖ) (F : Type) [Field F]
    [Algebra (FractionRing T.V) F] (y : P.D.toPre.X) :
    GenRel (isoPullId (idIso P.D.toPre.P.L) rfl)
      (LB.pullGen _ _ _ (P.D.toPre.psi y) (jFK (R := T.V) F))
      (LB.pullGen _ _ _ ((D0 P hϖ).psi y) (jFK (R := T.V) F))
      ((algebraMap (FractionRing T.V) F (algebraMap T.V _ ϖ)) ^ (beF P hϖ y y / 2)) := by
  have h0 : algebraMap (FractionRing T.V) F (algebraMap T.V _ ϖ) ≠ 0 :=
    (map_ne_zero _).2 ((map_ne_zero_iff _ (IsFractionRing.injective T.V (FractionRing T.V))).2 hϖ.ne_zero)
  have hq : beF P hϖ y y / 2 = qv P hϖ y := by rw [beF_self]; omega
  let u : Fˣ := Units.mk0 _ h0 ^ (beF P hϖ y y / 2)
  have hu : ((u : Fˣ) : F) = (algebraMap (FractionRing T.V) F (algebraMap T.V _ ϖ)) ^ (beF P hϖ y y / 2) := by
    simp only [u, Units.val_zpow_eq_zpow_val, Units.val_mk0]
  rw [← hu]
  refine ArcOfPoint.genRel_id_of_val P.D.toPre.P.isLB (pullGen_isGen _ _ _ _ (P.D.toPre.psi_gen y) _) fun z J hJ => ?_
  have ht : Units.map (algebraMap (FractionRing T.V) F).toMonoidHom (tF P hϖ y (H.w0 • y)) = u⁻¹ := by
    apply Units.ext
    simp only [u, tF, beF_w0, hq, Units.coe_map, map_zpow, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val,
      Units.val_mk0, zpow_neg]
    show (algebraMap (FractionRing T.V) F) ((((piK hϖ : (FractionRing T.V)ˣ) : FractionRing T.V) ^ qv P hϖ y)⁻¹) = _
    rw [map_inv₀, map_zpow₀]; rfl
  letI := H.starRing
  rw [val_pull hJ, val_pull hJ, Category.id_comp]
  erw [val_psi_twist H.w0 (tF P hϖ) y (jFK (R := T.V) F) hJ]
  rw [show jFK (R := T.V) F = 𝟙 _ ≫ spMap (algebraMap (FractionRing T.V) F) from (Category.id_comp _).symm,
    unitAt_spMap, ht, map_inv, ← _root_.mul_assoc, mul_inv_cancel, _root_.one_mul]

attribute [local instance] GlobalTheory.TorusExt.gtGroup in

theorem qkExt_of_genRel (P : PELUnif (maximalIdeal T.V) t) {ϖ : T.V} (hϖ : Irreducible ϖ) {k : ℕ}
    (hk : ∀ a a', (k : ℤ) ∣ beF P hϖ a a') (F : Type) [Field F] [Algebra (FractionRing T.V) F]
    (r : QkPt P.D.toPre (FractionRing T.V) k) (q₀ : QkPt (D0 P hϖ) F k) (q : QkPt P.D.toPre F k)
    (hext : QkExt (algebraMap _ F) (letI := H.starRing; qkScale (cmIdempotent_add_star_eq_one (H := H)) (isScalarForm_tF P hϖ)
      (psiRel0 P hϖ) (isRootForm_rF P hϖ hk) (D0 P hϖ).psi_gen r) q₀)
    (hqy : q.y = q₀.y)
    (hgen : ∀ z, GenRel (isoPullId (idIso P.D.toPre.P.L) rfl) (q.g.s z) (q₀.g.s z)
      ((algebraMap (FractionRing T.V) F (algebraMap T.V (FractionRing T.V) ϖ)) ^ (beF P hϖ q₀.y z / k))) :
    QkExt (algebraMap _ F) r q := by
  letI := H.starRing
  have hr := isRootForm_rF P hϖ hk
  have h1 := qkRel_qkScale (D := P.D.toPre) (ψ := (D0 P hϖ).psi) (hψ := (D0 P hϖ).psi_gen) (cmIdempotent_add_star_eq_one (H := H))
    (isScalarForm_tF P hϖ) (psiRel0 P hϖ) hr r
  have h2 : QkRel (D := D0 P hϖ) (ψ := P.D.toPre.psi) (hψ := P.D.toPre.psi_gen) (fun y x => (rF P hϖ k y x)⁻¹)
      (qkScale (cmIdempotent_add_star_eq_one (H := H)) (isScalarForm_tF P hϖ) (psiRel0 P hϖ) hr (D0 P hϖ).psi_gen r) r := h1.symm
  have h0 : algebraMap (FractionRing T.V) F (algebraMap T.V _ ϖ) ≠ 0 :=
    (map_ne_zero _).2 ((map_ne_zero_iff _ (IsFractionRing.injective T.V (FractionRing T.V))).2 hϖ.ne_zero)
  have hval : ∀ χ (y : Sp F) J, Good P.D.toPre.P.L y J →
      val (q.g.s χ) (𝟙 (Sp F)) y J = unitAt (𝟙 (Sp F)) y (Units.mk0 _ h0 ^ (beF P hϖ q₀.y χ / k)) *
        val (q₀.g.s χ) (𝟙 (Sp F)) y J := by
    intro χ y J hJ
    have g := hgen χ
    rw [show (algebraMap (FractionRing T.V) F (algebraMap T.V (FractionRing T.V) ϖ)) ^ (beF P hϖ q₀.y χ / k) =
      ((Units.mk0 _ h0 ^ (beF P hϖ q₀.y χ / k) : Fˣ) : F) by simp only [Units.val_zpow_eq_zpow_val, Units.val_mk0]] at g
    exact ArcOfPoint.val_of_genRel_id P.D.toPre.P.isLB (q.g.isGen χ) g y hJ
  have hb : q.g.b = q₀.g.b := by
    obtain ⟨h₁, -⟩ := (ArcOfPoint.genRel_id_iff P.D.toPre.P.isLB (q.g.isGen 0) (q₀.g.s 0)
      (Units.mk0 _ h0 ^ (beF P hϖ q₀.y 0 / k)) (IsLocalRing.closedPoint F)).1 (by
        have g := hgen 0
        rwa [show (algebraMap (FractionRing T.V) F (algebraMap T.V (FractionRing T.V) ϖ)) ^ (beF P hϖ q₀.y 0 / k) =
          ((Units.mk0 _ h0 ^ (beF P hϖ q₀.y 0 / k) : Fˣ) : F) by simp only [Units.val_zpow_eq_zpow_val, Units.val_mk0]] at g)
    exact Over.OverMorphism.ext (h₁ 2)
  have h3 : QkRel (D := D0 P hϖ) (ψ := P.D.toPre.psi) (hψ := P.D.toPre.psi_gen)
      (fun y x => Units.map (algebraMap (FractionRing T.V) F).toMonoidHom ((rF P hϖ k y x)⁻¹)) q₀ q := by
    refine ⟨hqy, gtRel_of_val hb fun χ y J hJ => ?_⟩
    have e : Units.map (algebraMap (FractionRing T.V) F).toMonoidHom ((rF P hϖ k q₀.y χ)⁻¹) =
        Units.mk0 _ h0 ^ (beF P hϖ q₀.y χ / k) := by
      rw [rF, ← zpow_neg, neg_neg, map_zpow]
      congr 1
      exact Units.ext rfl
    beta_reduce
    rw [e]
    exact hval χ y J hJ
  exact QkRel.qkExt (D := D0 P hϖ) (ψ := P.D.toPre.psi) (hψ := P.D.toPre.psi_gen)
    (f := algebraMap (FractionRing T.V) F) (r := fun y x => (rF P hϖ k y x)⁻¹)
    (r' := fun y x => Units.map (algebraMap (FractionRing T.V) F).toMonoidHom ((rF P hϖ k y x)⁻¹)) (fun y x => rfl)
    h2 h3 hext

theorem hasArcData_arc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : CDVR) (io : c.F →+* T.Fr) (b : O →+* T.V) (y : Sp T.V ⟶ Y.X) (z : Sp T.Fr ⟶ Xo.XF c), (algebraMap T.V T.Fr).comp b = io.comp β → y ≫ Y.s = spMap b → z ≫ pullback.snd _ _ = spMap io → z ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ y → ∀ (t : SAB H (Sp T.V)) (m : SABMap t Y.t y) (P : PELUnif (maximalIdeal T.V) t) (hX : Nontrivial P.D.toPre.X) (ϖ : T.V) (hϖ : Irreducible ϖ) (hdiv : ∀ a a', (2 * l.M' : ℤ) ∣ GlobalTheory.ArcBuild.beF P hϖ a a') (hL : GlobalTheory.ArcExt.LevelReps Y y t m P) (hLie : GlobalTheory.ArcBuild.LieCl P D β b) (hTate : GlobalTheory.ArcBuild.TateCl P hϖ Y b y m hdiv hL), Y.HasArcData (GlobalTheory.ArcBuild.arc P hϖ Y b y m hX hdiv hL hLie hTate) (Ideal.span {ϖ}) (RingHom.id T.V) ϖ y := by
  intro E _ _ _ H D l Xo c O _ β Y T io b y z hb hy hz hzj t m P hX ϖ hϖ hdiv hL hLie hTate
  rw [← hϖ.maximalIdeal_eq]
  have hs : spMap (RingHom.id T.V) = 𝟙 _ := Spec.map_id _
  have he : eSec P.D.toPre.P.A ≫ 𝟙 _ = spMap (RingHom.id T.V) ≫ eSec P.D.toPre.P.A := by
    rw [hs, Category.comp_id, Category.id_comp]
  refine ⟨t, m, P, 𝟙 _, he, isoPullId (idIso P.D.toPre.P.L) rfl, LinearEquiv.refl _ _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hs]
    have : IsMonHom (Iso.refl P.D.toPre.P.A).hom := inferInstanceAs (IsMonHom (𝟙 P.D.toPre.P.A))
    exact @isGrpPullback_of_iso _ _ _ _ _ (Iso.refl _) this
  · exact (isGen_iff _).2 (isoPullId_pgen (idIso_isGen P.D.toPre.P.isLB) rfl)
  · exact isoPullId_maps (L' := ⟨P.D.toPre.P.L, P.D.toPre.rig, P.D.toPre.P.isLB, P.D.toPre.rig_gen⟩)
      (L := ⟨P.D.toPre.P.L, P.D.toPre.rig, P.D.toPre.P.isLB, P.D.toPre.rig_gen⟩) (idIso_maps _) rfl hs he
  · intro x; exact (Category.comp_id _).trans (Category.id_comp _).symm
  · intro x; rw [hs]; exact (Category.comp_id _).trans (Category.id_comp _).symm
  · intro F _ _ i₁ i₂ uF hF huF
    have hi : i₁ = i₂ := by
      have h : (@algebraMap (FractionRing T.V) F _ _ i₁) = (@algebraMap (FractionRing T.V) F _ _ i₂) :=
        IsLocalization.ringHom_ext (nonZeroDivisors T.V) (RingHom.ext fun x => (hF x).symm)
      exact Algebra.algebra_ext _ _ fun r => congrArg (· r) h
    subst hi huF
    refine ⟨fun y => genRel_psi_D0 P hϖ F y, fun yF hyF k p₀ σ hσ q₀ q x hext hqy hgen hx => ?_⟩
    rcases hσ with ⟨rfl, v, hp, rfl⟩ | ⟨rfl, v, hv, hp, rfl⟩
    · obtain rfl := eq_of_heq hp
      exact (hL.1 v).choose_spec F yF hyF q x
        (qkExt_of_genRel P hϖ (dvd_of_dvd P hϖ (Nat.dvd_lcm_right l.M l.A) hdiv) F _ q₀ q hext hqy hgen) hx
    · obtain rfl := eq_of_heq hp
      have hext' : QkExt (algebraMap (FractionRing T.V) F) (eta0 P hϖ Y y m hdiv hL v) q₀ := hext
      rw [eta0, dif_pos hv] at hext'
      exact (hL.2 v hv).choose_spec F yF hyF q x
        (qkExt_of_genRel P hϖ (dvd_of_dvd P hϖ (Nat.dvd_lcm_left l.M l.A) hdiv) F _ q₀ q hext' hqy hgen) hx

end GlobalTheory.ArcBuild
