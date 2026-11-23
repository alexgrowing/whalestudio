import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBSer
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndFrFixAsm

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FrRatio

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermB

attribute [local instance] Over.cartesianMonoidalCategory

theorem psJet_trunc {S κ : Type} [CommRing S] [Fintype κ] [DecidableEq κ] (m : ℕ) (f : MvPowerSeries κ S) :
    (jetTrunc : Jet S κ (m + 1) →ₐ[S] Jet S κ m) (psJet (m + 1) f) = psJet m f := by
  show Ideal.Quotient.mk _ (psTrunc (m + 1) f) = Ideal.Quotient.mk _ (psTrunc m f)
  exact Ideal.Quotient.eq.2 (psTrunc_succ_sub f)

theorem unitΓ_map {A B : Type} [CommRing A] [CommRing B] {S : Type} [CommRing S] [Algebra S A] [Algebra S B]
    (σ : A →ₐ[S] B) (U : Aˣ) :
    unitΓ (Units.map (σ : A →* B) U) = pullU (spMap (σ : A →+* B)) ⊤ (unitΓ U) := by
  unfold unitΓ pullU
  ext
  simp [toΓ, spMap]
  have h2 := congrArg (fun g => CommRingCat.Hom.hom g (U : A))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (σ : A →+* B)))
  exact h2

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} {t : SAB H X0}
variable {S : Type} [CommRing S] {x0 : Sp S ⟶ X0} {d : ℕ} {x : ∀ m, jOG x0 d m 1 ⟶ t.G}
variable {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S} {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S}
  {κ : Type} [Fintype κ] {tg : κ → (Sp (DualNumber S) ⟶ t.G.left)} {uvec : κ → Fin d → S}

private theorem jetCopy_trunc_lemma {n : ℕ} (m : ℕ) (i : Fin n) :
    (jetTrunc : Jet S (Fin n × Fin d) (m + 1) →ₐ[S] _).comp (jetCopy d (m + 1) i) =
      (jetCopy d m i).comp (jetTrunc : Jet S (Fin 1 × Fin d) (m + 1) →ₐ[S] _) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro p
  simp [jetCopy, jetMap, jetTrunc, liftJet, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.lift_mk,
    Ideal.Quotient.factor_mk, MvPolynomial.bind₁_X_right]
  rfl

theorem jpt_tr (hch : IsChartG t x0 d F act tg uvec x) (m : ℕ) {n : ℕ} (i : Fin n) :
    homAt x0 (jetTrunc : Jet S (Fin n × Fin d) (m + 1) →ₐ[S] _) ≫ jptG t x0 d x (m + 1) i = jptG t x0 d x m i := by
  have key := jetCopy_trunc_lemma (S := S) (d := d) m i
  unfold jptG
  rw [← Category.assoc, homAt_comp, key, ← hch.trunc m, ← Category.assoc, homAt_comp]

theorem cφ_tr (hch : IsChartG t x0 d F act tg uvec x) (m : ℕ) (I : ULift.{0} (Finset (Fin 2))) :
    (homAt x0 (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] _)).left ≫
      cφG t ![jptG t x0 d x (m + 1) (0 : Fin 2), jptG t x0 d x (m + 1) (1 : Fin 2)] I =
      cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] I := by
  simp only [cφG, ← Over.comp_left]
  refine congrArg Over.Hom.left ((psum_hom (preHom _) _ I.down).trans ?_)
  refine congrArg (fun f => psum t.G f I.down) (funext fun i => ?_)
  fin_cases i
  · exact jpt_tr hch m 0
  · exact jpt_tr hch m 1

theorem triple_lift_truncation (hch : IsChartG t x0 d F act tg uvec x) (m : ℕ) (i j k : Fin 3) :
    (ρn x0 d 3 m).left ≫ (lift (jptG t x0 d x (m + 1) i) (lift (jptG t x0 d x (m + 1) j) (jptG t x0 d x (m + 1) k))).left =
      (lift (jptG t x0 d x m i) (lift (jptG t x0 d x m j) (jptG t x0 d x m k))).left := by
  unfold ρn
  rw [← Over.comp_left]
  simp only [comp_lift, jpt_tr hch]

theorem pair_lift_truncation (hch : IsChartG t x0 d F act tg uvec x) (m : ℕ) :
    (ρn x0 d 2 m).left ≫ (lift (jptG t x0 d x (m + 1) (0 : Fin 2)) (jptG t x0 d x (m + 1) (1 : Fin 2))).left =
      (lift (jptG t x0 d x m (0 : Fin 2)) (jptG t x0 d x m (1 : Fin 2))).left := by
  unfold ρn
  rw [← Over.comp_left]
  simp only [comp_lift, jpt_tr hch]

theorem pe_tr (e : ∀ m, FrTyG t x0 d x m) {n : ℕ} (m : ℕ) (v' v : Fin 2 → Fin d → MvPolynomial (Fin n × Fin d) S)
    (hv : ∀ i j, v' i j - v i j ∈ orig S (Fin n × Fin d) ^ (m + 1)) (y : (jOG x0 d m n).left)
    (J : ((jOG x0 d m n).left ⟶ t.G.left) → t.PP.L.ι) (hJ : Good t.PP.L y J) :
    val (peG t x0 d x e (m + 1) v') (ρn x0 d n m).left y J =
      val (e (m + 1)) ((homAt x0 (jetSubstP m fun p : Fin 2 × Fin d => v p.1 p.2)).left ≫
        (homAt x0 (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] _)).left) y J := by
  have hs : (ρn x0 d n m).left ≫ (homAt x0 (jetSubstP (m + 1) fun p : Fin 2 × Fin d => v' p.1 p.2)).left =
      (homAt x0 (jetSubstP m fun p : Fin 2 × Fin d => v p.1 p.2)).left ≫
        (homAt x0 (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] _)).left := by
    rw [← Over.comp_left, ← Over.comp_left, homAt_comp, homAt_comp, jetSubstP_trunc,
      jetSubstP_congr m (fun p : Fin 2 × Fin d => v' p.1 p.2) (fun p : Fin 2 × Fin d => v p.1 p.2)
        (fun p => hv p.1 p.2)]
  exact (val_pull hJ (e (m + 1)) _ _).trans (congrArg (fun r => val (e (m + 1)) r y J) hs)

end

theorem alg1 {M : Type} [CommGroup M] (W b1 b2 b3 g1 g2 g3 : M)
    (h : W * (b1 * (b2⁻¹ * b3⁻¹)) = W * (g1 * b1 * ((g2 * b2)⁻¹ * (g3 * b3)⁻¹))) : g1 = g2 * g3 := by
  have h' := mul_left_cancel h
  have hr : g1 * b1 * ((g2 * b2)⁻¹ * (g3 * b3)⁻¹) = (g1 * (g2 * g3)⁻¹) * (b1 * (b2⁻¹ * b3⁻¹)) := by
    simp only [mul_inv]
    ac_rfl
  rw [hr] at h'
  have h1 : g1 * (g2 * g3)⁻¹ = 1 := by
    apply mul_right_cancel (b := b1 * (b2⁻¹ * b3⁻¹))
    rw [_root_.one_mul]
    exact h'.symm
  exact mul_inv_eq_one.mp h1

theorem alg2 {M : Type} [CommGroup M] (W b0 bs g0 gs : M) (h0 : b0 = W * bs) (h1 : g0 * b0 = W * (gs * bs)) :
    g0 = gs := by
  subst h0
  apply mul_right_cancel (b := W * bs)
  rw [h1, mul_left_comm]

theorem alg3 {M : Type} [CommGroup M] (L W ba bb ga gb : M) (h0 : L * ba = W * bb)
    (h1 : L * (ga * ba) = W * (gb * bb)) : ga = gb := by
  apply mul_right_cancel (b := W * bb)
  calc ga * (W * bb) = ga * (L * ba) := by rw [h0]
    _ = L * (ga * ba) := mul_left_comm _ _ _
    _ = W * (gb * bb) := h1
    _ = gb * (W * bb) := mul_left_comm _ _ _

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} {t : SAB H X0}
variable {S : Type} [CommRing S] {x0 : Sp S ⟶ X0} {d : ℕ} {x : ∀ m, jOG x0 d m 1 ⟶ t.G}
variable {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S} {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S}
  {κ : Type} [Fintype κ] {tg : κ → (Sp (DualNumber S) ⟶ t.G.left)} {uvec : κ → Fin d → S}

omit [Fintype κ] in
theorem gm_map {A B : Type} [CommRing A] [CommRing B] [Algebra S A] [Algebra S B] (σ : A →ₐ[S] B) (U : Aˣ)
    (y : (overAt x0 B).left) :
    gm (homAt x0 σ).left y ⊤ (unitΓ U) = gm (𝟙 _) y ⊤ (unitΓ (Units.map (σ : A →* B) U)) := by
  rw [unitΓ_map]
  refine Eq.trans ?_ (gm_pull (𝟙 _) (homAt x0 σ).left y ⊤ trivial (unitΓ U)).symm
  rw [Category.id_comp]

theorem exists_ratioU (hch : IsChartG t x0 d F act tg uvec x) (e : ∀ m, FrTyG t x0 d x m) (he : ∀ m, (e m).IsGen)
    (m : ℕ) : ∃ U : (Jet S (Fin 2 × Fin d) m)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ (jOG x0 d m 2).left) (z : Z)
      (J : (Z ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J →
      val (e (m + 1)) (r ≫ (homAt x0 (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] _)).left) z J =
        gm r z ⊤ (unitΓ U) * val (e m) r z J := by
  have hL := t.PP.isLB
  obtain ⟨u, hu⟩ := exists_ratio t.PP.L hL
    (φ := fun k => (homAt x0 (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] _)).left ≫
      cφG t ![jptG t x0 d x (m + 1) (0 : Fin 2), jptG t x0 d x (m + 1) (1 : Fin 2)] k) (ε := cε 2)
    (fun U _ h => Finset.prod_congr rfl fun I _ => congrArg (fun q => h q ^ cε 2 I) (cφ_tr hch m I))
    (LB.pullGen t.PP.L _ _ (e (m + 1)) _) (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ (he (m + 1)) _) (e m) (he m)
  have hU : unitΓ (Units.map (Scheme.ΓSpecIso (CommRingCat.of (Jet S (Fin 2 × Fin d) m))).hom.hom.toMonoidHom u) = u :=
    Units.ext (congrArg (fun f => CommRingCat.Hom.hom f u.val)
      (Iso.hom_inv_id (Scheme.ΓSpecIso (CommRingCat.of (Jet S (Fin 2 × Fin d) m)))))
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of (Jet S (Fin 2 × Fin d) m))).hom.hom.toMonoidHom u,
    fun Z r z J hJ => ?_⟩
  rw [hU]
  exact (val_pull hJ _ _ _).symm.trans (hu Z r z J hJ)

set_option maxHeartbeats 4000000 in
theorem frRatioG (hch : IsChartG t x0 d F act tg uvec x) {ph1 ph2 sy ad} {e : ∀ m, FrTyG t x0 d x m}
    (hfr : IsFrameG t x0 d x F act ph1 ph2 sy ad e) (m : ℕ) :
    ∃ U : (Jet S (Fin 2 × Fin d) m)ˣ,
      LB.Gen.Corr t.PP.L _ _ _ _
        (LB.pullGen t.PP.L _ _ (e (m + 1)) (homAt x0 (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] _)).left)
        (scaleGenG t _ _ (unitΓ U) (e m)) ∧
      jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => psIn d m (![0, 1] : Fin 2 → Fin 3) (F j), fun j => MvPolynomial.X ((2 : Fin 3), j)] : Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) p.1 p.2) (U : Jet S (Fin 2 × Fin d) m) = jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)] : Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) p.1 p.2) (U : Jet S (Fin 2 × Fin d) m) * jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => MvPolynomial.X ((1 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)] : Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) p.1 p.2) (U : Jet S (Fin 2 × Fin d) m) ∧
      jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => MvPolynomial.X ((1 : Fin 2), j), fun j => MvPolynomial.X ((0 : Fin 2), j)] : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) p.1 p.2) (U : Jet S (Fin 2 × Fin d) m) = U ∧
      ∀ a : 𝓞 E, jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => psIn d m ![0] (act a j), fun j => MvPolynomial.X ((1 : Fin 2), j)] : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) p.1 p.2) (U : Jet S (Fin 2 × Fin d) m) = jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)] : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) p.1 p.2) (U : Jet S (Fin 2 × Fin d) m) := by
  have hL := t.PP.isLB
  obtain ⟨U, hU⟩ := exists_ratioU hch e hfr.gen m
  have hσ : ∀ {n : ℕ} (v : Fin 2 → Fin d → MvPolynomial (Fin n × Fin d) S) (y : (jOG x0 d m n).left)
      (J : ((jOG x0 d m n).left ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L y J →
      val (e (m + 1)) ((homAt x0 (jetSubstP m fun p : Fin 2 × Fin d => v p.1 p.2)).left ≫
        (homAt x0 (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] _)).left) y J =
      gm (𝟙 _) y ⊤ (unitΓ (Units.map ((jetSubstP m fun p : Fin 2 × Fin d => v p.1 p.2 :
          Jet S (Fin 2 × Fin d) m →ₐ[S] Jet S (Fin n × Fin d) m) : _ →* _) U)) *
        val (peG t x0 d x e m v) (𝟙 _) y J := fun v y J hJ =>
    (hU _ _ y J hJ).trans (congrArg₂ (· * ·) (gm_map _ U y)
      ((congrArg (fun r => val (e m) r y J) (Category.id_comp _).symm).trans (val_pull hJ _ _ _).symm))
  have hXX : ∀ {n : ℕ} (k : Fin n) (j : Fin d),
      (MvPolynomial.X (k, j) : MvPolynomial (Fin n × Fin d) S) - MvPolynomial.X (k, j) ∈
        orig S (Fin n × Fin d) ^ (m + 1) := fun k j => by simp
  have hunit : ∀ {A : Type} [CommRing A] [Algebra S A] (a b c : Aˣ),
      (∀ y, gm (𝟙 (overAt x0 A).left) y ⊤ (unitΓ a) = gm (𝟙 _) y ⊤ (unitΓ b) * gm (𝟙 _) y ⊤ (unitΓ c)) →
      (a : A) = b * c := by
    intro A _ _ a b c h
    have hu : unitΓ a = unitΓ b * unitΓ c := unit_ext (V := ⊤) fun y _ => (h y).trans (map_mul _ _ _).symm
    exact toΓ_injective A ((congrArg Units.val hu).trans (map_mul _ _ _).symm)
  have hunit2 : ∀ {A : Type} [CommRing A] [Algebra S A] (a b : Aˣ),
      (∀ y, gm (𝟙 (overAt x0 A).left) y ⊤ (unitΓ a) = gm (𝟙 _) y ⊤ (unitΓ b)) → (a : A) = b := by
    intro A _ _ a b h
    have hu : unitΓ a = unitΓ b := unit_ext (V := ⊤) fun y _ => h y
    exact toΓ_injective A (congrArg Units.val hu)
  have htr : ∀ {n : ℕ} (u' : (Jet S (Fin n × Fin d) (m + 1))ˣ) (u : (Jet S (Fin n × Fin d) m)ˣ) (f),
      (u' : Jet S (Fin n × Fin d) (m + 1)) = psJet (m + 1) f → (u : Jet S (Fin n × Fin d) m) = psJet m f →
      ∀ y, gm (ρn x0 d n m).left y ⊤ (unitΓ u') = gm (𝟙 _) y ⊤ (unitΓ u) := by
    intro n u' u f h' h y
    refine (gm_map _ u' y).trans (congrArg (fun w => gm (𝟙 _) y ⊤ (unitΓ w)) (Units.ext ?_))
    simp only [Units.coe_map, MonoidHom.coe_coe]
    rw [h', h]
    exact psJet_trunc m f
  refine ⟨U, corr_of_val hL fun y J hJ => ?_, ?_, ?_, fun a => ?_⟩
  · exact (val_pull hJ _ _ _).trans ((hU _ (𝟙 _) y J hJ).trans (val_scale t _ _ _ _ _ y J hJ).symm)
  · refine hunit (Units.map ((jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => psIn d m (![0, 1] : Fin 2 → Fin 3) (F j), fun j => MvPolynomial.X ((2 : Fin 3), j)] : Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) p.1 p.2) : Jet S (Fin 2 × Fin d) m →ₐ[S] Jet S (Fin 3 × Fin d) m) : Jet S (Fin 2 × Fin d) m →* Jet S (Fin 3 × Fin d) m) U) (Units.map ((jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)] : Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) p.1 p.2) : Jet S (Fin 2 × Fin d) m →ₐ[S] Jet S (Fin 3 × Fin d) m) : Jet S (Fin 2 × Fin d) m →* Jet S (Fin 3 × Fin d) m) U) (Units.map ((jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => MvPolynomial.X ((1 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)] : Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) p.1 p.2) : Jet S (Fin 2 × Fin d) m →ₐ[S] Jet S (Fin 3 × Fin d) m) : Jet S (Fin 2 × Fin d) m →* Jet S (Fin 3 × Fin d) m) U) fun y => ?_
    choose J hJ using fun χ : (jOG x0 d m 3).left ⟶ t.G.left => exists_chart hL (χ y)
    obtain ⟨u1, hu1, hc1⟩ := hfr.ph1 m
    obtain ⟨u1', hu1', hc1'⟩ := hfr.ph1 (m + 1)
    have E0 := (val_corr hJ hc1 (𝟙 _)).trans (val_scale t _ _ _ _ _ y J hJ)
    have E1 := (val_corr hJ hc1' (ρn x0 d 3 m).left).trans (val_scale t _ _ _ _ _ y J hJ)
    rw [val_mul hJ, val_mul hJ, val_inv, val_inv] at E0 E1
    have hth : val (LB.pullGen t.PP.L (thφ t.G (x3 t.G)) thε t.cub.t (lift (jptG t x0 d x (m + 1) (0 : Fin 3))
        (lift (jptG t x0 d x (m + 1) (1 : Fin 3)) (jptG t x0 d x (m + 1) (2 : Fin 3)))).left) (ρn x0 d 3 m).left y J =
        val (LB.pullGen t.PP.L (thφ t.G (x3 t.G)) thε t.cub.t (lift (jptG t x0 d x m (0 : Fin 3))
          (lift (jptG t x0 d x m (1 : Fin 3)) (jptG t x0 d x m (2 : Fin 3)))).left) (𝟙 _) y J :=
      (val_pull hJ _ _ _).trans ((congrArg (fun r => val t.cub.t r y J)
        ((triple_lift_truncation hch m 0 1 2).trans (Category.id_comp _).symm)).trans (val_pull hJ _ _ _).symm)
    rw [hth, htr u1' u1 ph1 hu1' hu1 y,
      pe_tr e m (![fun j => psIn d (m + 1) (![0, 1] : Fin 2 → Fin 3) (F j), fun j => MvPolynomial.X ((2 : Fin 3), j)] : Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) (![fun j => psIn d m (![0, 1] : Fin 2 → Fin 3) (F j), fun j => MvPolynomial.X ((2 : Fin 3), j)] : Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) (fun i j => by fin_cases i; exacts [psIn_succ_sub m _ _, hXX _ j]) y J hJ,
      pe_tr e m (![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)] : Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) (![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)] : Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) (fun i j => by fin_cases i <;> exact hXX _ j) y J hJ,
      pe_tr e m (![fun j => MvPolynomial.X ((1 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)] : Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) (![fun j => MvPolynomial.X ((1 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)] : Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) (fun i j => by fin_cases i <;> exact hXX _ j) y J hJ,
      hσ (![fun j => psIn d m (![0, 1] : Fin 2 → Fin 3) (F j), fun j => MvPolynomial.X ((2 : Fin 3), j)] : Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) y J hJ, hσ (![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)] : Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) y J hJ, hσ (![fun j => MvPolynomial.X ((1 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)] : Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) y J hJ] at E1
    exact alg1 _ _ _ _ _ _ _ (E0.symm.trans E1)
  · refine hunit2 (Units.map ((jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => MvPolynomial.X ((1 : Fin 2), j), fun j => MvPolynomial.X ((0 : Fin 2), j)] : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) p.1 p.2) : Jet S (Fin 2 × Fin d) m →ₐ[S] Jet S (Fin 2 × Fin d) m) : Jet S (Fin 2 × Fin d) m →* Jet S (Fin 2 × Fin d) m) U) U fun y => ?_
    choose J hJ using fun χ : (jOG x0 d m 2).left ⟶ t.G.left => exists_chart hL (χ y)
    obtain ⟨s, hs, hcs⟩ := hfr.sy m
    obtain ⟨s', hs', hcs'⟩ := hfr.sy (m + 1)
    have E0 := (val_corr hJ hcs (𝟙 _)).trans (val_scale t _ _ _ _ _ y J hJ)
    have E1 := (val_corr hJ hcs' (ρn x0 d 2 m).left).trans (val_scale t _ _ _ _ _ y J hJ)
    have hinv : ∀ {k n : ℕ} (w : (Jet S (Fin n × Fin d) k)ˣ), unitΓ w⁻¹ = (unitΓ w)⁻¹ := fun w => map_inv _ w
    have hsi : gm (ρn x0 d 2 m).left y ⊤ (unitΓ s'⁻¹) = gm (𝟙 _) y ⊤ (unitΓ s⁻¹) := by
      rw [hinv, hinv, map_inv, map_inv, htr s' s sy hs' hs y]
    have hL0 : val (e (m + 1)) (ρn x0 d 2 m).left y J = gm (𝟙 _) y ⊤ (unitΓ U) * val (e m) (𝟙 _) y J :=
      (congrArg (fun r => val (e (m + 1)) r y J) (Category.id_comp _).symm).trans (hU _ (𝟙 _) y J hJ)
    rw [hL0, hsi, pe_tr e m (![fun j => MvPolynomial.X ((1 : Fin 2), j), fun j => MvPolynomial.X ((0 : Fin 2), j)] : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) (![fun j => MvPolynomial.X ((1 : Fin 2), j), fun j => MvPolynomial.X ((0 : Fin 2), j)] : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) (fun i j => by fin_cases i <;> exact hXX _ j) y J hJ, hσ (![fun j => MvPolynomial.X ((1 : Fin 2), j), fun j => MvPolynomial.X ((0 : Fin 2), j)] : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) y J hJ] at E1
    exact (alg2 _ _ _ _ _ E0 E1).symm
  · refine hunit2 (Units.map ((jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => psIn d m ![0] (act a j), fun j => MvPolynomial.X ((1 : Fin 2), j)] : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) p.1 p.2) : Jet S (Fin 2 × Fin d) m →ₐ[S] Jet S (Fin 2 × Fin d) m) : Jet S (Fin 2 × Fin d) m →* Jet S (Fin 2 × Fin d) m) U) (Units.map ((jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)] : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) p.1 p.2) : Jet S (Fin 2 × Fin d) m →ₐ[S] Jet S (Fin 2 × Fin d) m) : Jet S (Fin 2 × Fin d) m →* Jet S (Fin 2 × Fin d) m) U) fun y => ?_
    choose J hJ using fun χ : (jOG x0 d m 2).left ⟶ t.G.left => exists_chart hL (χ y)
    obtain ⟨wL, -, hwL⟩ := hfr.ad a
    obtain ⟨ua, hua, hca⟩ := hwL m
    obtain ⟨ua', hua', hca'⟩ := hwL (m + 1)
    have E0 := (val_corr hJ hca (𝟙 _)).trans (val_scale t _ _ _ _ _ y J hJ)
    have E1 := (val_corr hJ hca' (ρn x0 d 2 m).left).trans (val_scale t _ _ _ _ _ y J hJ)
    rw [val_mul hJ] at E0 E1
    have hw : val (LB.pullGen t.PP.L _ _ wL (lift (jptG t x0 d x (m + 1) (0 : Fin 2))
        (jptG t x0 d x (m + 1) (1 : Fin 2))).left) (ρn x0 d 2 m).left y J =
        val (LB.pullGen t.PP.L _ _ wL (lift (jptG t x0 d x m (0 : Fin 2)) (jptG t x0 d x m (1 : Fin 2))).left) (𝟙 _) y J :=
      (val_pull hJ _ _ _).trans ((congrArg (fun r => val wL r y J) ((pair_lift_truncation hch m).trans (Category.id_comp _).symm)).trans
        (val_pull hJ _ _ _).symm)
    rw [hw, htr ua' ua (ad a) hua' hua y,
      pe_tr e m (![fun j => psIn d (m + 1) ![0] (act a j), fun j => MvPolynomial.X ((1 : Fin 2), j)] : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) (![fun j => psIn d m ![0] (act a j), fun j => MvPolynomial.X ((1 : Fin 2), j)] : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) (fun i j => by fin_cases i; exacts [psIn_succ_sub m _ _, hXX _ j]) y J hJ,
      pe_tr e m (![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn d (m + 1) ![1] (act (H.bar a) j)] : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) (![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)] : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) (fun i j => by fin_cases i; exacts [hXX _ j, psIn_succ_sub m _ _]) y J hJ,
      hσ (![fun j => psIn d m ![0] (act a j), fun j => MvPolynomial.X ((1 : Fin 2), j)] : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) y J hJ, hσ (![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)] : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) y J hJ] at E1
    exact alg3 _ _ _ _ _ _ E0 E1

end Main

end Formalism.MainNotions.ModuliIntegralCharts.H1.FrRatio

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

theorem frRatio_holds : FrRatioSt := by
  intro E _ _ _ H Dw l Xo c _ hstar S _ _ _ y C m
  have hch : L2.Pj.IsChartG Xo.univ.t y.x C.d C.B.G.F C.B.A.act _ C.uvec C.x :=
    ⟨C.chart.zero, C.chart.trunc, C.chart.law, C.chart.act, C.chart.tan, C.chart.basis⟩
  exact FrRatio.frRatioG hch ⟨C.frame.gen, C.frame.ph1, C.frame.ph2, C.frame.sy, C.frame.ad⟩ m

theorem frTruncFix_holds : FrTruncFixSt := frTruncFix_of frRatio_holds

end Formalism.MainNotions.ModuliIntegralCharts.H1
