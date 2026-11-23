import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBGen
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBPrim
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBSer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

namespace GlobalTheory.FrameAdjSeries

open Formalism.MainNotions.ModuliIntegralCharts.H1.GermB Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun

section Pts

variable {S : Type} [CommRing S] (d : ℕ)

theorem subst_copy (m : ℕ) {n : ℕ} (φ : Fin 2 → Fin d → MvPolynomial (Fin n × Fin d) S) (i : Fin 2) :
    (jetSubstP m (fun p : Fin 2 × Fin d => φ p.1 p.2)).comp (jetCopy d m i) =
      jetSubstP m (fun p : Fin 1 × Fin d => φ i p.2) := by
  apply jet_hom_ext
  intro p
  simp only [AlgHom.comp_apply, jetSubstP, jetCopy, jetMap_mk, MvPolynomial.aeval_X]

theorem substX (m : ℕ) {n : ℕ} (k : Fin n) :
    jetSubstP m (fun p : Fin 1 × Fin d => (MvPolynomial.X (k, p.2) : MvPolynomial (Fin n × Fin d) S)) =
      jetCopy d m k := by
  apply jet_hom_ext
  intro p
  simp [jetSubstP, jetCopy, jetMap_mk]

def jetRen (m : ℕ) {n n' : ℕ} (r : Fin n → Fin n') : Jet S (Fin n × Fin d) m →ₐ[S] Jet S (Fin n' × Fin d) m :=
  jetMap (fun q : Fin n × Fin d => MvPolynomial.X (r q.1, q.2)) fun _ => X_mem_orig _

theorem ren_copy (m : ℕ) {n n' : ℕ} (r : Fin n → Fin n') (i : Fin n) :
    (jetRen (S := S) d m r).comp (jetCopy d m i) = jetCopy d m (r i) := by
  apply jet_hom_ext
  intro p
  simp only [AlgHom.comp_apply, jetRen, jetCopy, jetMap_mk, MvPolynomial.aeval_X]

theorem ren_one (m : ℕ) {n' : ℕ} (r : Fin 1 → Fin n') : jetRen (S := S) d m r = jetCopy d m (r 0) := by
  apply jet_hom_ext
  rintro ⟨i, j⟩
  obtain rfl : i = 0 := Subsingleton.elim _ _
  simp only [jetRen, jetCopy, jetMap_mk, MvPolynomial.aeval_X]

theorem subst_psIn (m : ℕ) {n n' : ℕ} (r : Fin n → Fin n') (g : Fin d → MvPowerSeries (Fin n × Fin d) S) :
    jetSubstP m (fun p : Fin 1 × Fin d => psIn d m r (g p.2)) =
      (jetRen d m r).comp (jetSubstP m (fun p : Fin 1 × Fin d => psTrunc m (g p.2))) := by
  have hr : (MvPolynomial.aeval fun q : Fin n × Fin d => (MvPolynomial.X (r q.1, q.2) : MvPolynomial (Fin n' × Fin d) S)) =
      MvPolynomial.rename fun p : Fin n × Fin d => (r p.1, p.2) := MvPolynomial.algHom_ext fun q => by simp
  apply jet_hom_ext
  intro p
  simp only [jetSubstP, jetRen, AlgHom.comp_apply, jetMap_mk, MvPolynomial.aeval_X, map_sub, MvPolynomial.aeval_C,
    MvPolynomial.algebraMap_eq, psIn, MvPolynomial.constantCoeff_rename, hr, MvPolynomial.rename_C]

end Pts

theorem jetSubstP_zero_eq {S κ κ' : Type} [CommRing S] (φ ψ : κ → MvPolynomial κ' S) :
    (jetSubstP 0 φ : Jet S κ 0 →ₐ[S] Jet S κ' 0) = jetSubstP 0 ψ := by
  apply jet_hom_ext
  intro i
  have h0 : (Ideal.Quotient.mk (orig S κ ^ (0 + 1)) (MvPolynomial.X i) : Jet S κ 0) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (by simpa using X_mem_orig (R := S) i)
  rw [h0, map_zero, map_zero]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} {t : SAB H X0}
variable {S : Type} [CommRing S] {x0 : Sp S ⟶ X0} {d : ℕ} {x : ∀ m, jOG x0 d m 1 ⟶ t.G}
variable {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S} {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S}
  {κ : Type} [Fintype κ] {tg : κ → (Sp (DualNumber S) ⟶ t.G.left)} {uvec : κ → Fin d → S}

theorem pt_sub (m : ℕ) {n : ℕ} (φ : Fin 2 → Fin d → MvPolynomial (Fin n × Fin d) S) (i : Fin 2) :
    homAt x0 (jetSubstP m (fun p : Fin 2 × Fin d => φ p.1 p.2)) ≫ jptG t x0 d x m i =
      homAt x0 (jetSubstP m (fun p : Fin 1 × Fin d => φ i p.2)) ≫ x m := by
  rw [jptG, ← Category.assoc, homAt_comp, subst_copy]

theorem pt_X (m : ℕ) {n : ℕ} (k : Fin n) :
    homAt x0 (jetSubstP m (fun p : Fin 1 × Fin d => (MvPolynomial.X (k, p.2) : MvPolynomial (Fin n × Fin d) S))) ≫ x m =
      jptG t x0 d x m k := by
  rw [substX]
  try rfl

theorem pt_law (hch : IsChartG t x0 d F act tg uvec x) (m : ℕ) {n : ℕ} (r : Fin 2 → Fin n) :
    homAt x0 (jetSubstP m (fun p : Fin 1 × Fin d => psIn d m r (F p.2))) ≫ x m =
      jptG t x0 d x m (r 0) * jptG t x0 d x m (r 1) := by
  have hk : ∀ i, homAt x0 (jetRen d m r) ≫ jptG t x0 d x m i = jptG t x0 d x m (r i) := fun i => by
    rw [jptG, jptG, ← Category.assoc, homAt_comp, ren_copy]
  rw [subst_psIn, ← homAt_comp, Category.assoc, hch.law m, MonObj.comp_mul, hk, hk]

theorem pt_act (hch : IsChartG t x0 d F act tg uvec x) (m : ℕ) {n : ℕ} (r : Fin 1 → Fin n) (a : 𝓞 E) :
    homAt x0 (jetSubstP m (fun p : Fin 1 × Fin d => psIn d m r (act a p.2))) ≫ x m =
      jptG t x0 d x m (r 0) ≫ t.act.act a := by
  rw [subst_psIn, ← homAt_comp, Category.assoc, ← hch.act m a, ← Category.assoc, ren_one]
  try rfl

theorem pe_pt (m : ℕ) {n : ℕ} (σ : Jet S (Fin 2 × Fin d) m →ₐ[S] Jet S (Fin n × Fin d) m) (I : ULift.{0} (Finset (Fin 2))) :
    (homAt x0 σ).left ≫ cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] I =
      (psum t.G ![homAt x0 σ ≫ jptG t x0 d x m (0 : Fin 2), homAt x0 σ ≫ jptG t x0 d x m (1 : Fin 2)] I.down).left := by
  simp only [cφG, ← Over.comp_left]
  refine congrArg Over.Hom.left ((psum_hom (preHom _) _ I.down).trans ?_)
  refine congrArg (fun f => psum t.G f I.down) (funext fun i => ?_)
  fin_cases i <;> rfl

theorem wl_pt {T : Over X0} (a b : T ⟶ t.G) (c : 𝓞 E) (I : ULift.{0} (Finset (Fin 2))) :
    (lift a b).left ≫ cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act c] I =
      (psum t.G ![a, b ≫ t.act.act c] I.down).left := by
  simp only [cφG, ← Over.comp_left]
  refine congrArg Over.Hom.left ((psum_hom (preHom _) _ I.down).trans ?_)
  refine congrArg (fun f => psum t.G f I.down) (funext fun i => ?_)
  fin_cases i
  · show lift a b ≫ fst t.G t.G = a
    exact lift_fst _ _
  · show lift a b ≫ (snd t.G t.G ≫ t.act.act c) = b ≫ t.act.act c
    exact lift_snd_assoc _ _ _

theorem wl_pt' {T : Over X0} (a b : T ⟶ t.G) (c : 𝓞 E) (I : ULift.{0} (Finset (Fin 2))) :
    (lift a b).left ≫ cφG t ![fst t.G t.G ≫ t.act.act c, snd t.G t.G] I =
      (psum t.G ![a ≫ t.act.act c, b] I.down).left := by
  simp only [cφG, ← Over.comp_left]
  refine congrArg Over.Hom.left ((psum_hom (preHom _) _ I.down).trans ?_)
  refine congrArg (fun f => psum t.G f I.down) (funext fun i => ?_)
  fin_cases i
  · show lift a b ≫ (fst t.G t.G ≫ t.act.act c) = a ≫ t.act.act c
    exact lift_fst_assoc _ _ _
  · show lift a b ≫ snd t.G t.G = b
    exact lift_snd _ _

theorem frame_origin_jet_one (hch : IsChartG t x0 d F act tg uvec x) : x 0 = 1 := by
  have hj : (Algebra.ofId S (Jet S (Fin 1 × Fin d) 0)).comp jetAug = AlgHom.id S _ := by
    apply jet_hom_ext
    intro p
    rw [AlgHom.comp_apply, jetAug_X, map_zero, AlgHom.id_apply]
    exact (Ideal.Quotient.eq_zero_iff_mem.2 (by simpa using X_mem_orig (R := S) p)).symm
  calc x 0 = 𝟙 _ ≫ x 0 := (Category.id_comp _).symm
    _ = (homAt x0 (Algebra.ofId S (Jet S (Fin 1 × Fin d) 0)) ≫ homAt x0 jetAug) ≫ x 0 := by
        rw [homAt_comp, hj, homAt_id]
    _ = homAt x0 (Algebra.ofId S (Jet S (Fin 1 × Fin d) 0)) ≫ 1 := by rw [Category.assoc, hch.zero 0]
    _ = 1 := map_one (preHom _)

theorem jpt_trunc' (hch : IsChartG t x0 d F act tg uvec x) (m : ℕ) {n : ℕ} (i : Fin n) :
    homAt x0 (jetTrunc : Jet S (Fin n × Fin d) (m + 1) →ₐ[S] _) ≫ jptG t x0 d x (m + 1) i = jptG t x0 d x m i := by
  have hc : (jetTrunc : Jet S (Fin n × Fin d) (m + 1) →ₐ[S] _).comp (jetCopy d (m + 1) i) =
      (jetCopy d m i).comp (jetTrunc : Jet S (Fin 1 × Fin d) (m + 1) →ₐ[S] _) := by
    apply jet_hom_ext
    intro p
    rfl
  rw [jptG, jptG, ← Category.assoc, homAt_comp, hc, ← homAt_comp, Category.assoc, hch.trunc m]

theorem pair_trunc (hch : IsChartG t x0 d F act tg uvec x) (m : ℕ) :
    (ρn x0 d 2 m).left ≫ (lift (jptG t x0 d x (m + 1) (0 : Fin 2)) (jptG t x0 d x (m + 1) (1 : Fin 2))).left =
      𝟙 _ ≫ (lift (jptG t x0 d x m (0 : Fin 2)) (jptG t x0 d x m (1 : Fin 2))).left := by
  rw [← Over.comp_left, Category.id_comp, comp_lift, jpt_trunc' hch, jpt_trunc' hch]

set_option maxHeartbeats 4000000 in
theorem exists_ad_one (hch : IsChartG t x0 d F act tg uvec x) (e : ∀ m, FrTyG t x0 d x m)
    (heg : ∀ m, (e m).IsGen) (htr : FrTrunc t x0 d x e) (a : 𝓞 E)
    (wL : LB.Gen (LB.LinComb t.PP.L
      (Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)]) (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G]))
      (Sum.elim (cε 2) fun I => -cε 2 I))) (hwLg : wL.IsGen)
    (hwL0 : ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over X0)).left) (z : Z) (J : (Z ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J →
      val wL (r ≫ (zz t).left) z J = 1) :
    ∃ ad : MvPowerSeries (Fin 2 × Fin d) S, MvPowerSeries.constantCoeff ad = 1 ∧ ∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ,
      (u : Jet S (Fin 2 × Fin d) m) = psJet m ad ∧ LB.Gen.Corr t.PP.L _ _ _ _
        (LB.mulGen t.PP.L _ _ _ _
          (LB.pullGen t.PP.L _ _ wL (lift (jptG t x0 d x m (0 : Fin 2)) (jptG t x0 d x m (1 : Fin 2))).left)
          (peG t x0 d x e m ![fun j => psIn d m ![0] (act a j), fun j => MvPolynomial.X ((1 : Fin 2), j)]))
        (scaleGenG t _ _ (unitΓ u) (peG t x0 d x e m ![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)])) := by
  have hL := t.PP.isLB
  have hpe : ∀ m {n : ℕ} (φ : Fin 2 → Fin d → MvPolynomial (Fin n × Fin d) S),
      (peG t x0 d x e m φ).IsGen :=
    fun m n φ => ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ (heg m) _
  have hXX : ∀ (m : ℕ) {n : ℕ} (k : Fin n) (j : Fin d),
      (MvPolynomial.X (k, j) : MvPolynomial (Fin n × Fin d) S) - MvPolynomial.X (k, j) ∈
        orig S (Fin n × Fin d) ^ (m + 1) := fun m n k j => by simp
  obtain ⟨ad, had⟩ := exists_series t x0 d (n := 2) _ _ _ _
    (fun m => LB.mulGen t.PP.L _ _ _ _
      (LB.pullGen t.PP.L _ _ wL (lift (jptG t x0 d x m (0 : Fin 2)) (jptG t x0 d x m (1 : Fin 2))).left)
      (peG t x0 d x e m ![fun j => psIn d m ![0] (act a j), fun j => MvPolynomial.X ((1 : Fin 2), j)]))
    (fun m => ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ hwLg _)
      (hpe m _))
    (fun m => peG t x0 d x e m
      ![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)])
    (fun m => hpe m _)
    (fun m U _ h => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, wl_pt, wl_pt', pe_pt, pt_sub, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, pt_X, pt_act hch, zpow_neg, Finset.prod_inv_distrib]
      simp only [inv_mul_cancel_right])
    (fun m y J hJ => (val_mul hJ _ _ _).trans (Eq.trans (congrArg₂ (· * ·)
      ((val_pull hJ _ _ _).trans ((congrArg (fun r => val wL r y J) (pair_trunc hch m)).trans (val_pull hJ _ _ _).symm))
      (pe_trunc t x0 d htr
        (fun m => ![fun j => psIn d m ![0] (act a j), fun j => MvPolynomial.X ((1 : Fin 2), j)])
        (fun m i j => by fin_cases i; exacts [psIn_succ_sub m _ _, hXX m _ j]) m y J hJ))
      (val_mul hJ _ _ _).symm))
    (fun m y J hJ => pe_trunc t x0 d htr
      (fun m => ![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)])
      (fun m i j => by fin_cases i; exacts [hXX m _ j, psIn_succ_sub m _ _]) m y J hJ)
  have hx0 : x 0 = 1 := frame_origin_jet_one hch
  have hj0 : ∀ {n : ℕ} (i : Fin n), jptG t x0 d x 0 i = 1 := fun i => by
    rw [jptG, hx0]
    exact map_one (preHom _)
  have hadc : MvPowerSeries.constantCoeff ad = 1 := by
    obtain ⟨u, hu, hc⟩ := had 0
    have hU : unitΓ u = 1 := by
      refine unit_ext (V := ⊤) fun y _ => ?_
      choose I hI using fun χ : (jOG x0 d 0 2).left ⟶ t.G.left => exists_chart hL (χ y)
      have e1 := (val_corr hI hc (𝟙 _)).trans (val_scale t _ _ _ _ _ y I hI)
      have hl : (𝟙 _ ≫ (lift (jptG t x0 d x 0 (0 : Fin 2)) (jptG t x0 d x 0 (1 : Fin 2))).left) =
          ((𝟙 _ ≫ (toUnit (jOG x0 d 0 2)).left) ≫ (zz t).left) := by
        rw [Category.id_comp, Category.id_comp, ← Over.comp_left, comp_lift, hj0, hj0]
        rfl
      have hA1 : val (LB.pullGen t.PP.L _ _ wL (lift (jptG t x0 d x 0 (0 : Fin 2)) (jptG t x0 d x 0 (1 : Fin 2))).left)
          (𝟙 _) y I = 1 := by
        refine (val_pull hI _ _ _).trans ?_
        rw [hl]
        exact hwL0 _ _ y I hI
      have hAB : val (peG t x0 d x e 0
          ![fun j => psIn d 0 ![0] (act a j), fun j => MvPolynomial.X ((1 : Fin 2), j)]) (𝟙 _) y I =
          val (peG t x0 d x e 0
          ![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn d 0 ![1] (act (H.bar a) j)]) (𝟙 _) y I :=
        (val_pull hI _ _ _).trans ((congrArg (fun σ => val (e 0) (𝟙 _ ≫ (homAt x0 σ).left) y I)
          (jetSubstP_zero_eq _ _)).trans (val_pull hI _ _ _).symm)
      rw [val_mul hI, hA1, hAB, _root_.one_mul] at e1
      rw [map_one]
      exact (right_eq_mul.1 e1)
    have hu1 : (u : Jet S (Fin 2 × Fin d) 0) = 1 := by
      apply toΓ_injective
      rw [map_one]
      exact congrArg Units.val hU
    show MvPowerSeries.coeff 0 ad = 1
    rw [← coeff_psTrunc 0 ad 0 le_rfl]
    have h0 := hu.symm.trans hu1
    rw [psJet, ← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq] at h0
    have h1 := coeff_eq_zero_of_mem h0 (e := 0) (by simp)
    rw [MvPolynomial.coeff_sub, sub_eq_zero, MvPolynomial.coeff_one, if_pos rfl] at h1
    exact h1
  exact ⟨ad, hadc, had⟩

end GlobalTheory.FrameAdjSeries

theorem GlobalTheory.FrameAdjSeries.exists_ad :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S) (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (κ : Type) [Fintype κ] (tg : κ → (Sp (DualNumber S) ⟶ t.G.left)) (uvec : κ → Fin d → S) (x : ∀ m, jOG x0 d m 1 ⟶ t.G), (∀ j, MvPowerSeries.constantCoeff (F j) = 0) → (∀ a j, MvPowerSeries.constantCoeff (act a j) = 0) → IsChartG t x0 d F act tg uvec x → ∀ e : ∀ m, FrTyG t x0 d x m, (∀ m, (e m).IsGen) → FrTrunc t x0 d x e → FrAxes t x0 d x e → ∃ ad : 𝓞 E → PS S 2 d, (∀ a, MvPowerSeries.constantCoeff (ad a) = 1) ∧ ∀ a : 𝓞 E, ∃ wL : LB.Gen (LB.LinComb t.PP.L (Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)]) (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G])) (Sum.elim (cε 2) fun I => -cε 2 I)), wL.IsGen ∧ ∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m (ad a) ∧ LB.Gen.Corr t.PP.L _ _ _ _ (LB.mulGen t.PP.L _ _ _ _ (LB.pullGen t.PP.L _ _ wL (lift (jptG t x0 d x m (0 : Fin 2)) (jptG t x0 d x m (1 : Fin 2))).left) (peG t x0 d x e m ![fun j => psIn d m ![0] (act a j), fun j => X ((1 : Fin 2), j)])) (scaleGenG t _ _ (unitΓ u) (peG t x0 d x e m ![fun j => X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)])) := by
  intro E _ _ _ H X0 t S _ x0 d F act κ _ tg uvec x _ _ hch e heg htr _
  choose wL hwLg hwL0 using fun a => Formalism.MainNotions.ModuliIntegralCharts.H1.GermB.exists_wL t a
  choose ad hadc had using fun a => GlobalTheory.FrameAdjSeries.exists_ad_one hch e heg htr a (wL a) (hwLg a) (hwL0 a)
  exact ⟨ad, hadc, fun a => ⟨wL a, hwLg a, had a⟩⟩
