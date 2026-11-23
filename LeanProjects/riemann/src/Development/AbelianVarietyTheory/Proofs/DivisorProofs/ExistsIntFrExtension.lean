import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsResidueFactor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFrameExtensionExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePointMemClosed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecUnitClosedFibre
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationTrivialTorusAbelianLocus
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.DepthSum

section Core

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace NumberField
  IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

theorem thetaCore_trait :
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l)
    (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β),
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (yt : Sp V ⟶ Y.X)
      (z : Sp (FractionRing V) ⟶ Xo.XF c), z ≫ Y.j = spMap (algebraMap V (FractionRing V)) ≫ yt →
      ∀ (G : SAB H (Sp V)) (_m : SABMap G Y.t yt) (t' : SAB H (Sp (FractionRing V)))
        (m2 : SABMap t' G (spMap (algebraMap V (FractionRing V)))),
        ∃ θ : LB.Sec G.PP.L, (∀ σ : LB.Sec G.PP.L, ∃! a : V, ∀ i, σ.f i = constFn G.G.hom _ a * θ.f i) ∧
          (∃ (g : G.G.left) (i : G.PP.L.ι), G.G.hom g = closedPoint V ∧ g ∈ G.G.left.basicOpen (θ.f i)) ∧
          ∃ (w2 : LB.Iso t'.PP.L (G.PP.L.pull m2.φ)) (σ' : LB.Sec t'.PP.L), IsRigIso m2.cm t'.PP G.PP w2 ∧
            (∀ (j : G.PP.L.ι) (k : t'.PP.L.ι) (W : t'.G.left.Opens) (h₁ : W ≤ m2.φ ⁻¹ᵁ G.PP.L.U j)
              (h₂ : W ≤ (G.PP.L.pull m2.φ).U (fun _ => j) ⊓ t'.PP.L.U k),
              (m2.φ.appLE _ _ h₁).hom (θ.f j) =
                resG _ h₂ (w2.s (fun _ => j, k)).val * resG _ (h₂.trans inf_le_right) (σ'.f k)) ∧
            ∀ s' : LB.Sec t'.PP.L, ∃! a : FractionRing V, ∀ i, s'.f i = constFn t'.G.hom _ a * σ'.f i := by
  intro E _ _ _ H D l Xo c O _ β Y V _ _ _ yt z hz G m t' m2
  have := G.semi.smooth
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m2
  have cancel : ∀ (p : Sp (FractionRing V) ⟶ Y.X) (_ : p = z ≫ Y.j) (n : SABMap t' Y.t p), Nonempty (SABMap t' Y.oF.t z) := by
    intro p hp n; subst hp
    exact ⟨(sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ Y.m n).choose⟩
  obtain ⟨m3⟩ := cancel _ hz.symm n
  obtain ⟨b, hb⟩ := globalSections_rank_one_fibre GlobalTheory.allSixLaws.2.1.secTwist amplePt Y.oF m3
  obtain ⟨θ, hθ⟩ := GlobalTheory.ThetaDvr.thetaNZ_of_polAt GlobalTheory.allSixLaws.1 GlobalTheory.allSixLaws.2.1 E H V G
    (GlobalTheory.GoodTrait.polAt_of_point Y m (jK V) z hz)
  obtain ⟨g, k₀, hg₂, hgb⟩ := hθ (closedPoint V)
  have hk₀ : g ∈ G.PP.L.U k₀ := G.G.left.basicOpen_le _ hgb
  have un : IsUnit (gs (𝟙 _) g _ (θ.f k₀)) := by
    rw [gs_eq (𝟙 _) g _ hk₀]; exact (G.G.left.mem_basicOpen _ _ hk₀).1 hgb
  obtain ⟨w2, g2, r2, -⟩ := m2.lin
  have down := sec_pull_down ((isGen_iff w2).1 g2) G.PP.isLB t'.PP.isLB
  obtain ⟨σ', hσ'⟩ := down θ
  have : IsDominant (spMap (algebraMap V (FractionRing V))) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V (FractionRing V))).le.trans bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (spMap (algebraMap V (FractionRing V)))
  have : IsSchemeTheoreticallyDominant m2.φ := IsSchemeTheoreticallyDominant.of_isPullback m2.cart.1.flip
  have : QuasiCompact m2.φ := MorphismProperty.of_isPullback (P := @QuasiCompact) m2.cart.1.flip inferInstance

  have inj : ∀ (σ τ σK τK : _) (r : V), (∀ (Z : Scheme.{0}) (q : Z ⟶ t'.G.left) (y : Z) j k, m2.φ (q y) ∈ G.PP.L.U j →
      q y ∈ t'.PP.L.U k → gs (q ≫ m2.φ) y _ (LB.Sec.f σ j) = (gw w2 q y j k).val * gs q y _ (LB.Sec.f σK k)) →
      (∀ (Z : Scheme.{0}) (q : Z ⟶ t'.G.left) (y : Z) j k, m2.φ (q y) ∈ G.PP.L.U j →
      q y ∈ t'.PP.L.U k → gs (q ≫ m2.φ) y _ (LB.Sec.f τ j) = (gw w2 q y j k).val * gs q y _ (LB.Sec.f τK k)) →
      (∀ k, LB.Sec.f σK k = constFn t'.G.hom _ (algebraMap V _ r) * LB.Sec.f τK k) →
      ∀ j, LB.Sec.f σ j = constFn G.G.hom _ r * LB.Sec.f τ j := by
    intro σ τ σK τK r h₁ h₂ h₃ j
    refine m2.φ.app_injective _ (fn_ext fun y hy => ?_)
    obtain ⟨k, hk⟩ := exists_chart t'.PP.isLB y
    refine (gs_pull (𝟙 _) m2.φ y _ hy _).trans (Eq.trans ?_ (gs_pull (𝟙 _) m2.φ y _ hy _).symm)
    rw [gs_mul (𝟙 _ ≫ m2.φ) y _ hy, gs_constFn _ _ (𝟙 _ ≫ m2.φ) y hy, h₁ _ (𝟙 _) y j k hy hk, h₂ _ (𝟙 _) y j k hy hk, (sec_eq_iff _ _ _ _).1 h₃ k y hk,
      Category.id_comp, m2.cart.1.w, cst_comp, mul_left_comm]
  have mulc : ∀ {s t u : LB.Sec t'.PP.L} {a a' : FractionRing V}, (∀ k, s.f k = constFn t'.G.hom _ a * t.f k) →
      (∀ k, t.f k = constFn t'.G.hom _ a' * u.f k) → ∀ k, s.f k = constFn t'.G.hom _ (a * a') * u.f k :=
    fun h h' => (sec_eq_iff _ _ _ _).2 fun k y hy => by
      rw [(sec_eq_iff _ _ _ _).1 h k y hy, (sec_eq_iff _ _ _ _).1 h' k y hy, cst_mul, _root_.mul_assoc]
  have invc : ∀ {s t : LB.Sec t'.PP.L} {a : FractionRing V}, a ≠ 0 → (∀ k, s.f k = constFn t'.G.hom _ a * t.f k) →
      ∀ k, t.f k = constFn t'.G.hom _ a⁻¹ * s.f k := fun ha h => (sec_eq_iff _ _ _ _).2 fun k y hy => by
    rw [(sec_eq_iff _ _ _ _).1 h k y hy, ← _root_.mul_assoc, ← cst_mul, inv_mul_cancel₀ ha, cst_one, _root_.one_mul]
  have unit : ∀ (σ : LB.Sec G.PP.L) (r : V), (∀ j, θ.f j = constFn G.G.hom _ r * σ.f j) → IsUnit r := fun σ r h => by
    by_contra hr
    rw [(sec_eq_iff _ _ _ _).1 h k₀ g hk₀] at un
    exact cst_not_isUnit G.G.hom g hg₂ hr (isUnit_of_mul_isUnit_left un)
  obtain ⟨a₀, ha₀, -⟩ := hb σ'
  have h₀ : a₀ ≠ 0 := fun h => not_isUnit_zero (unit θ 0 (inj θ θ σ' σ' 0 hσ' hσ' ((sec_eq_iff _ _ _ _).2 fun k y hy => by
    rw [(sec_eq_iff _ _ _ _).1 ha₀ k y hy, h, map_zero, ← _root_.mul_assoc, ← cst_mul, mul_zero])))
  have gen : ∀ s' : LB.Sec t'.PP.L, ∃! a : FractionRing V, ∀ i, s'.f i = constFn t'.G.hom _ a * σ'.f i := fun s' => by
    obtain ⟨a, ha, hu⟩ := hb s'
    refine ⟨a * a₀⁻¹, mulc ha (invc h₀ ha₀), fun a' ha' => ?_⟩
    rw [← hu _ (mulc ha' ha₀), mul_inv_cancel_right₀ h₀]
  refine ⟨θ, fun σ => ?_, ⟨g, k₀, hg₂, (G.G.left.mem_basicOpen _ _ hk₀).2 (by rwa [gs_eq _ _ _ hk₀] at un)⟩, w2, σ', ⟨g2, r2⟩,
    fun j k W h₁ h₂ => fn_ext fun y hy => ?_, gen⟩
  · obtain ⟨σK, hσK⟩ := down σ
    obtain ⟨a, ha, -⟩ := gen σK
    have ex : ∃ r : V, ∀ i, σ.f i = constFn G.G.hom _ r * θ.f i := by
      by_cases h : IsLocalization.IsInteger V a
      · obtain ⟨r, rfl⟩ := h
        exact ⟨r, inj σ θ σK σ' r hσK hσ' ha⟩
      · have hne : a ≠ 0 := fun e => h (e ▸ IsLocalization.isInteger_zero)
        obtain ⟨r, hr⟩ := (ValuationRing.isInteger_or_isInteger V a).resolve_left h
        obtain ⟨u, rfl⟩ := unit σ r (inj θ σ σ' σK r hσ' hσK (hr ▸ invc hne ha))
        exact absurd ⟨(u⁻¹ : Vˣ), by rw [← inv_inv a, ← hr, map_units_inv]⟩ h
    obtain ⟨r, hr⟩ := ex
    refine ⟨r, hr, fun r' hr' => ?_⟩
    by_contra hne
    have e : cst G.G.hom g (r' - r) * gs (𝟙 _) g _ (θ.f k₀) = cst G.G.hom g (r' - r) * 0 := by
      rw [cst_sub, sub_mul, ← (sec_eq_iff _ _ _ _).1 hr' k₀ g hk₀, ← (sec_eq_iff _ _ _ _).1 hr k₀ g hk₀, sub_self, mul_zero]
    exact un.ne_zero (cst_regular G.G.hom g (sub_ne_zero.2 hne) e)
  · rw [gs_appLE m2.φ _ _ h₁ (𝟙 _) y hy, hσ' _ (𝟙 _) y j k (h₁ hy) (h₂ hy).2, gs_mul _ y _ hy, gs_res _ y _ hy]
    exact congrArg₂ (· * ·) ((gs_res (𝟙 _) y h₂ hy _).trans (gs_unit (𝟙 _) y _ (h₂ hy) _)).symm rfl

end Core

section Frame

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

set_option maxHeartbeats 400000 in

theorem thetaFrame_trait :
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β),
    ∀ (yt : Sp T.V ⟶ Y.X) (z : Sp T.Fr ⟶ Xo.XF c),
    z ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ yt → z ≫ pullback.snd _ _ = spMap io →
    ∀ (G : SAB H (Sp T.V)) (_m : SABMap G Y.t yt) (t' : SAB H (Sp T.Fr))
      (m1 : SABMap t' Xo.univ.t (z ≫ pullback.fst _ _)) (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr))),
      letI := io.toAlgebra
      ∀ s₀ : LB.Sec (PPx (z ≫ pullback.fst _ _)),
      (∀ s' : LB.Sec (PPx (z ≫ pullback.fst _ _)), ∃! a : T.Fr, ∀ i, s'.f i = scal (z ≫ pullback.fst _ _) a i * s₀.f i) →
      ∃ (θ : LB.Sec G.PP.L) (s : LB.Sec (PPx (z ≫ pullback.fst _ _))),
        (∀ σ : LB.Sec G.PP.L, ∃! a : T.V, ∀ i,
          σ.f i = resG G.G.left le_top ((G.G.hom).appTop.hom (toΓ T.V a)) * θ.f i) ∧
        (∃ (w1 : LB.Iso t'.PP.L (Xo.univ.t.PP.L.pull m1.φ)) (w2 : LB.Iso t'.PP.L (G.PP.L.pull m2.φ))
          (σ : LB.Sec t'.PP.L) (s1 : LB.Sec (Xo.univ.t.PP.L.pull m1.φ)) (θ2 : LB.Sec (G.PP.L.pull m2.φ)),
          RigIso m1 w1 ∧ RigIso m2 w2 ∧ IsoMaps w1 σ s1 ∧ IsoMaps w2 σ θ2 ∧ PullSec m2.φ θ θ2 ∧
          ∀ g : t'.G.left ⟶ Gx (z ≫ pullback.fst _ _),
            g ≫ (snd (Over.mk (z ≫ pullback.fst _ _)) Xo.univ.t.G).left = m1.φ →
            g ≫ (fst (Over.mk (z ≫ pullback.fst _ _)) Xo.univ.t.G).left = t'.G.hom →
            ∀ j (h : (Xo.univ.t.PP.L.pull m1.φ).U j ≤ g ⁻¹ᵁ (PPx (z ≫ pullback.fst _ _)).U (fun _ => j PUnit.unit)),
              s1.f j = (g.appLE _ _ h).hom (s.f (fun _ => j PUnit.unit))) ∧
        (∀ s' : LB.Sec (PPx (z ≫ pullback.fst _ _)), ∃! a : T.Fr, ∀ i,
          s'.f i = scal (z ≫ pullback.fst _ _) a i * s.f i) ∧
        ∃ a : T.Frˣ, ∀ i, s.f i = scal (z ≫ pullback.fst _ _) (a : T.Fr) i * s₀.f i := by
  intro T io O _ β Y yt z hz hzs G m t' m1 m2
  obtain ⟨θ, hθ, -, w2, σ', ⟨g2, r2⟩, hcl, hgen⟩ := thetaCore_trait E H Dw l Xo c O β Y T.V yt z hz G m t' m2
  generalize (z ≫ pullback.fst _ _ : Sp T.Fr ⟶ Xo.X) = x at m1 ⊢
  intro s₀ hs₀
  obtain ⟨w1, g1, r1, -⟩ := m1.lin
  have hw1 := (isGen_iff w1).1 g1
  have hL := Xo.univ.t.PP.isLB
  have hL' := t'.PP.isLB
  obtain ⟨s1, hs1⟩ := thf_secUp hw1 hL hL' σ'
  let A := Xo.univ.t.G
  have cond : (snd (Over.mk x) A).left ≫ A.hom = (fst (Over.mk x) A).left ≫ x :=
    (Over.w (snd (Over.mk x) A)).trans (Over.w (fst (Over.mk x) A)).symm
  let h : Gx x ⟶ t'.G.left := m1.cart.1.lift _ _ cond
  have hφ : h ≫ m1.φ = (snd (Over.mk x) A).left := m1.cart.1.lift_fst _ _ cond
  have hh : h ≫ t'.G.hom = (fst (Over.mk x) A).left := m1.cart.1.lift_snd _ _ cond
  let a0 : Over.mk (t'.G.hom ≫ x) ⟶ Over.mk x := Over.homMk t'.G.hom rfl
  let b0 : Over.mk (t'.G.hom ≫ x) ⟶ A := Over.homMk m1.φ m1.cart.1.w
  let g0 : t'.G.left ⟶ Gx x := (lift a0 b0).left
  have g0f : g0 ≫ (fst (Over.mk x) A).left = t'.G.hom := congrArg (fun q => q.left) (lift_fst a0 b0)
  have g0s : g0 ≫ (snd (Over.mk x) A).left = m1.φ := congrArg (fun q => q.left) (lift_snd a0 b0)
  have uniq : ∀ g : t'.G.left ⟶ Gx x, g ≫ (snd (Over.mk x) A).left = m1.φ → g ≫ (fst (Over.mk x) A).left = t'.G.hom →
      g ≫ h = 𝟙 _ := fun g e₁ e₂ => m1.cart.1.hom_ext (by rw [Category.assoc, hφ, e₁, Category.id_comp])
        (by rw [Category.assoc, hh, e₂, Category.id_comp])
  have hg0 : g0 ≫ h = 𝟙 _ := uniq g0 g0s g0f
  have h0g : h ≫ g0 = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc]
      show h ≫ g0 ≫ (fst (Over.mk x) A).left = 𝟙 _ ≫ (fst (Over.mk x) A).left
      rw [g0f, hh, Category.id_comp]
    · rw [Category.assoc]
      show h ≫ g0 ≫ (snd (Over.mk x) A).left = 𝟙 _ ≫ (snd (Over.mk x) A).left
      rw [g0s, hφ, Category.id_comp]
  let s : LB.Sec (PPx x) := thfPull1 Xo.univ.t.PP.L h hφ s1
  have hsf : ∀ j : Fin 1 → Xo.univ.t.PP.L.ι, s.f j = (h.appLE _ _ (chart_le_pullback_open _ h hφ j)).hom (s1.f (fun _ => j 0)) :=
    fun j => rfl
  let θ2 := thfPull G.PP.L m2.φ θ
  have hI2 : IsoMaps w2 σ' θ2 := fun (i : PUnit → G.PP.L.ι) k => fn_ext fun y hy => by
    have h₁ : (G.PP.L.pull m2.φ).U i ⊓ t'.PP.L.U k ≤ m2.φ ⁻¹ᵁ G.PP.L.U (i PUnit.unit) :=
      inf_le_left.trans (LB.wchart_le G.PP.L _ i PUnit.unit)
    have h₂ : (G.PP.L.pull m2.φ).U i ⊓ t'.PP.L.U k ≤ (G.PP.L.pull m2.φ).U (fun _ => i PUnit.unit) ⊓ t'.PP.L.U k :=
      le_rfl
    have e := congrArg (gs (𝟙 _) y _) (hcl (i PUnit.unit) k _ h₁ h₂)
    refine (gs_res _ y _ hy _).trans ((gs_appLE m2.φ _ _ _ (𝟙 _) y hy.1 _).trans
      (((gs_appLE m2.φ _ _ h₁ (𝟙 _) y hy _).symm.trans e).trans ((gs_mul _ y _ hy _ _).trans ?_)))
    refine Eq.symm ((gs_mul _ y _ hy _ _).trans ?_)
    exact congrArg₂ (· * ·) (gs_res _ y h₂ hy _).symm ((gs_res _ y _ hy _).trans (gs_res _ y _ hy _).symm)
  have hI1 : IsoMaps w1 σ' s1 := fun (i : PUnit → Xo.univ.t.PP.L.ι) k => fn_ext fun y hy => by
    exact (gs_res _ y _ hy _).trans ((hs1 _ (𝟙 _) y i k hy.1 hy.2).trans (Eq.symm ((gs_mul _ y _ hy _ _).trans
      (congrArg₂ (· * ·) (gs_unit (𝟙 _) y _ hy _) (gs_res _ y _ hy _)))))
  have hgc : ∀ g : t'.G.left ⟶ Gx x, g ≫ (snd (Over.mk x) A).left = m1.φ → g ≫ (fst (Over.mk x) A).left = t'.G.hom →
      ∀ (j : PUnit → Xo.univ.t.PP.L.ι) (hj : (Xo.univ.t.PP.L.pull m1.φ).U j ≤ g ⁻¹ᵁ (PPx x).U (fun _ => j PUnit.unit)),
        s1.f j = (g.appLE _ _ hj).hom (s.f (fun _ => j PUnit.unit)) := fun g e₁ e₂ j hj => fn_ext fun y hy =>
    Eq.symm ((gs_appLE g _ _ hj (𝟙 _) y hy _).trans
      ((gs_appLE h _ _ (chart_le_pullback_open _ h hφ _) (𝟙 _ ≫ g) y (hj hy) _).trans
        (congrArg (fun q => gs q y _ (s1.f j)) (by rw [Category.id_comp, uniq g e₁ e₂]))))
  have hgenS : ∀ s'' : LB.Sec (PPx x), ∃! a : T.Fr, ∀ i, s''.f i = scal x a i * s.f i := by
    intro s''
    have le : ∀ j, m1.φ ⁻¹ᵁ Xo.univ.t.PP.L.U j ≤ g0 ⁻¹ᵁ (PPx x).U (fun _ => j) := fun j y hy =>
      Set.mem_iInter.2 fun _ => (congrArg (fun q => q y ∈ Xo.univ.t.PP.L.U j) g0s).mpr hy
    let σ : ∀ j, Γ(t'.G.left, m1.φ ⁻¹ᵁ Xo.univ.t.PP.L.U j) := fun j => (g0.appLE _ _ (le j)).hom (s''.f (fun _ => j))
    have gP : ∀ (Z : Scheme.{0}) (r : Z ⟶ t'.G.left) (z : Z) j, m1.φ (r z) ∈ Xo.univ.t.PP.L.U j →
        gs r z _ (σ j) = gs (r ≫ g0) z _ (s''.f (fun _ => j)) := fun Z r z j hz => gs_appLE g0 _ _ (le j) r z hz _
    obtain ⟨τ, hτ⟩ := sec_down hw1 hL hL' σ fun y j j' h₁ h₂ => by
      have m : (𝟙 _ ≫ g0) y ∈ (PPx x).U (fun _ => j) := le j h₁
      have m' : (𝟙 _ ≫ g0) y ∈ (PPx x).U (fun _ => j') := le j' h₂
      have gg : gm (𝟙 _ ≫ g0) y _ ((PPx x).g (fun _ => j) (fun _ => j')) =
          gm m1.φ y (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j') :=
        (gm_linComb Xo.univ.t.PP.L (K := Fin 1) (fun _ => (snd (Over.mk x) A).left) (fun _ => 1) (𝟙 _ ≫ g0) y _ _ m m').trans
          (by rw [Fin.prod_univ_one, zpow_one, Category.assoc, g0s, Category.id_comp])
      exact (gP _ (𝟙 _) y j h₁).trans ((gs_compat s'' (𝟙 _ ≫ g0) y m m').trans
        (congrArg₂ (· * ·) (congrArg Units.val gg) (gP _ (𝟙 _) y j' h₂).symm))
    obtain ⟨a, ha, hu⟩ := hgen τ
    refine ⟨a, fun (i : Fin 1 → Xo.univ.t.PP.L.ι) => ?_, fun a' ha' => hu a' ?_⟩
    · obtain ⟨j, rfl⟩ : ∃ j, i = fun _ => j := ⟨i 0, funext fun k => congrArg i (Subsingleton.elim k 0)⟩
      refine fn_ext fun y hy => ?_
      have mφ : m1.φ ((𝟙 _ ≫ h) y) ∈ Xo.univ.t.PP.L.U j :=
        (congrArg (fun q => q y ∈ Xo.univ.t.PP.L.U j)
          (by rw [Category.id_comp, hφ] : (𝟙 _ ≫ h) ≫ m1.φ = (snd (Over.mk x) A).left)).mpr (Set.mem_iInter.1 hy 0)
      obtain ⟨k, hk⟩ := exists_chart hL' ((𝟙 _ ≫ h) y)
      have e1 : gs (𝟙 _) y _ (s''.f (fun _ => j)) =
          (gw w1 (𝟙 _ ≫ h) y j k).val * (cst ((𝟙 _ ≫ h) ≫ t'.G.hom) y a * gs (𝟙 _ ≫ h) y _ (σ'.f k)) := by
        have c1 : (𝟙 _ ≫ h) ≫ g0 = 𝟙 _ := by rw [Category.id_comp, h0g]
        refine (congrArg (fun q => gs q y _ (s''.f (fun _ => j))) c1).symm.trans ?_
        refine (gP _ (𝟙 _ ≫ h) y j mφ).symm.trans ((hτ _ (𝟙 _ ≫ h) y j k mφ hk).trans (congrArg _ ?_))
        rw [ha k, gs_mul _ y _ hk, gs_constFn _ _ _ y hk]
      have e2 : gs (𝟙 _) y _ (s.f (fun _ => j)) = (gw w1 (𝟙 _ ≫ h) y j k).val * gs (𝟙 _ ≫ h) y _ (σ'.f k) :=
        (gs_appLE h _ _ (chart_le_pullback_open _ h hφ _) (𝟙 _) y hy _).trans
          (hs1 _ (𝟙 _ ≫ h) y (fun _ => j) k (chart_le_pullback_open _ h hφ _ hy) hk)
      have e3 : gs (𝟙 _) y _ (scal x a (fun _ => j)) = cst ((𝟙 _ ≫ h) ≫ t'.G.hom) y a := by
        rw [show (𝟙 _ ≫ h) ≫ t'.G.hom = 𝟙 _ ≫ (fst (Over.mk x) A).left by rw [Category.assoc, hh]]
        exact gs_constFn (fst (Over.mk x) A).left _ (𝟙 _) y hy a
      exact e1.trans ((mul_left_comm _ _ _).trans (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) e3 e2))))
    · intro k
      refine fn_ext fun y hy => ?_
      obtain ⟨j, hj⟩ := exists_chart hL (m1.φ y)
      have c2 : (𝟙 _ ≫ g0) ≫ h = 𝟙 _ := by rw [Category.id_comp, hg0]
      have mg : (𝟙 _ ≫ g0) y ∈ (PPx x).U (fun _ => j) := le j hj
      have e1 := hτ _ (𝟙 _) y j k hj hy
      have e2 : gs (𝟙 _) y _ (σ j) =
          cst (𝟙 _ ≫ t'.G.hom) y a' * ((gw w1 (𝟙 _) y j k).val * gs (𝟙 _) y _ (σ'.f k)) := by
        refine (gP _ (𝟙 _) y j hj).trans ?_
        rw [ha' (fun _ => j), gs_mul _ y _ mg]
        refine congrArg₂ (· * ·) ?_ ?_
        · exact (gs_constFn (fst (Over.mk x) A).left _ _ y mg a').trans (by rw [Category.assoc, g0f])
        · refine (gs_appLE h _ _ (chart_le_pullback_open _ h hφ _) (𝟙 _ ≫ g0) y mg _).trans ?_
          rw [c2]
          exact hs1 _ (𝟙 _) y (fun _ => j) k (mem_pull.2 hj) hy
      rw [gs_mul _ y _ hy, gs_constFn _ _ _ y hy]
      rw [e1, mul_left_comm] at e2
      exact (Units.mul_right_inj _).1 e2
  obtain ⟨a, ha, -⟩ := hs₀ s
  have a0 : a ≠ 0 := by
    rintro rfl
    have z0 : ∀ i, s.f i = 0 := fun i => by
      rw [ha i]
      simp only [scal, ReciprocityTheory.ChartRestriction.G.Out.liftFun, toΓ, map_zero, zero_mul]
    obtain ⟨b, -, hb⟩ := hgenS s
    exact zero_ne_one ((hb 0 fun i => by rw [z0 i, mul_zero]).trans (hb 1 fun i => by rw [z0 i, mul_zero]).symm)
  exact ⟨θ, s, hθ, ⟨w1, w2, σ', s1, θ2, ⟨g1, r1⟩, ⟨g2, r2⟩, hI1, hI2, fun j hj => rfl, hgc⟩, hgenS,
    Units.mk0 a a0, ha⟩

end Frame

section Points

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FactorDepth GlobalTheory.GenericCentre
attribute [local instance] Over.cartesianMonoidalCategory

end Points

end GlobalTheory.DepthSum
