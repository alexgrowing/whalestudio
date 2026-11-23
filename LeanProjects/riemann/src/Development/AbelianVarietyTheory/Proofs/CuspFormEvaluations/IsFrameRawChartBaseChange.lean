import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndBC
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.JetSubstPCompJetBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FrameBaseChange

open MvPolynomial (X C)

theorem spec_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R' →+* R'') (g : R →+* R') :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

theorem gm_unit_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (u : Aˣ) {Z : Scheme.{0}} (r : Z ⟶ Sp B)
    (z : Z) : gm r z ⊤ (unitΓ (Units.map f.toMonoidHom u)) = gm (r ≫ spMap f) z ⊤ (unitΓ u) := by
  apply Units.ext
  rw [gm_val _ _ _ (by simp), gm_val _ _ _ (by simp)]
  unfold unitΓ toΓ
  simp only [Units.coe_map]
  have key := congrArg (fun g => g.hom (u : A)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at key
  erw [key]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}

theorem val_scale {Y Z : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ Xo.univ.t.G.left)} {ε : K → ℤ}
    {z : Z} {J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι} (hJ : Good Xo.univ.t.PP.L z J) (c : Γ(Y, ⊤)ˣ)
    (t : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ ε)) (r : Z ⟶ Y) :
    val (Formalism.L2.Pj.scaleGen φ ε c t) r z J = gm r z ⊤ c * val t r z J := by
  unfold val Formalism.L2.Pj.scaleGen
  erw [map_mul, gm_res r z _ (hJ.mem φ r)]

variable {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ Xo.X)

theorem psIn_map {d n n' : ℕ} (m : ℕ) (r : Fin n → Fin n') (f : MvPowerSeries (Fin n × Fin d) S) :
    psIn d m r (MvPowerSeries.map ψ f) = MvPolynomial.map ψ (psIn d m r f) := by
  unfold psIn
  rw [MvPolynomial.map_rename]
  congr 1
  unfold psTrunc
  rw [map_sum]
  simp only [MvPolynomial.map_monomial, MvPowerSeries.coeff_map]

theorem subst_square {n n' d : ℕ} (m : ℕ) (φ : Fin n × Fin d → MvPolynomial (Fin n' × Fin d) S) :
    homAt (spMap ψ ≫ x0) (jetSubstP m (fun i => MvPolynomial.map ψ (φ i)) :
        Jet S' (Fin n × Fin d) m →ₐ[S'] Jet S' (Fin n' × Fin d) m) ≫ rjBC ψ x0 d m n =
      rjBC ψ x0 d m n' ≫ homAt x0 (jetSubstP m φ : Jet S (Fin n × Fin d) m →ₐ[S] Jet S (Fin n' × Fin d) m) := by
  unfold rjBC Formalism.L2.Pj.homAt
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, Over.homMk_left]
  rw [spec_comp, spec_comp]
  congr 1
  exact ReciprocityTheory.ChartRestriction.G.PullbackSections.jetSubstP_comp_jetBC ψ m φ

theorem jetMap_congr {R κ κ' : Type} [CommRing R] {m : ℕ} {f g : κ → MvPolynomial κ' R} (e : f = g)
    (hf : ∀ i, f i ∈ orig R κ') (hg : ∀ i, g i ∈ orig R κ') : jetMap (m := m) f hf = jetMap (m := m) g hg := by
  subst e
  rfl

theorem copy_square (d m n : ℕ) (i : Fin n) :
    homAt (spMap ψ ≫ x0) (jetCopy d m i : Jet S' (Fin 1 × Fin d) m →ₐ[S'] Jet S' (Fin n × Fin d) m) ≫
        rjBC ψ x0 d m 1 =
      rjBC ψ x0 d m n ≫ homAt x0 (jetCopy d m i : Jet S (Fin 1 × Fin d) m →ₐ[S] Jet S (Fin n × Fin d) m) := by
  unfold rjBC Formalism.L2.Pj.homAt jetCopy
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, Over.homMk_left]
  rw [spec_comp, spec_comp]
  congr 1
  have hS : ∀ p : Fin 1 × Fin d, (X (i, p.2) : MvPolynomial (Fin n × Fin d) S) ∈ orig S (Fin n × Fin d) := by
    intro p
    simp only [orig]
    exact Ideal.subset_span ⟨_, rfl⟩
  have hS' : ∀ p : Fin 1 × Fin d,
      MvPolynomial.map ψ (X (i, p.2) : MvPolynomial (Fin n × Fin d) S) ∈ orig S' (Fin n × Fin d) := by
    intro p
    rw [MvPolynomial.map_X]
    simp only [orig]
    exact Ideal.subset_span ⟨_, rfl⟩
  have h := ReciprocityTheory.ChartRestriction.G.PullbackSections.jetMap_comp_jetBC ψ m (fun p : Fin 1 × Fin d => (X (i, p.2) : MvPolynomial (Fin n × Fin d) S)) hS hS'
  rw [jetMap_congr (g := fun p : Fin 1 × Fin d => MvPolynomial.map ψ (X (i, p.2) : MvPolynomial (Fin n × Fin d) S))
    (funext fun p => (MvPolynomial.map_X ψ (i, p.2)).symm) _ hS']
  exact h

variable {ψ x0} {d : ℕ} {x : ∀ m, rjO x0 d m 1 ⟶ Xo.univ.t.G} {x' : ∀ m, rjO (spMap ψ ≫ x0) d m 1 ⟶ Xo.univ.t.G}

theorem point_bc (hx : ∀ m, x' m = rjBC ψ x0 d m 1 ≫ x m) {n : ℕ} (m : ℕ) (i : Fin n) :
    rjpt (spMap ψ ≫ x0) d x' m i = rjBC ψ x0 d m n ≫ rjpt x0 d x m i := by
  unfold rjpt
  rw [hx m, ← Category.assoc, copy_square, Category.assoc]

variable {e : ∀ m, RFrTy x0 d x m} {e' : ∀ m, RFrTy (spMap ψ ≫ x0) d x' m} {m : ℕ}
  (hc : LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (e' m) (LB.pullGen Xo.univ.t.PP.L
    (cφ ![rjpt x0 d x m (0 : Fin 2), rjpt x0 d x m (1 : Fin 2)]) (cε 2) (e m) (rjBC ψ x0 d m 2).left))
  {Z : Scheme.{0}} {z : Z} {J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι} (hJ : Good Xo.univ.t.PP.L z J)
include hc hJ

theorem val_subst {n : ℕ} (φ : Fin 2 → Fin d → MvPolynomial (Fin n × Fin d) S)
    (φ' : Fin 2 → Fin d → MvPolynomial (Fin n × Fin d) S') (hφ : ∀ i j, φ' i j = MvPolynomial.map ψ (φ i j))
    (r : Z ⟶ (rjO (spMap ψ ≫ x0) d m n).left) :
    val (rpe (spMap ψ ≫ x0) d x' e' m φ') r z J = val (rpe x0 d x e m φ) (r ≫ (rjBC ψ x0 d m n).left) z J := by
  unfold rpe
  refine ((val_pull hJ _ _ r).trans ((val_corr hJ hc _).trans (val_pull hJ _ _ _))).trans
    (Eq.trans (congrArg (fun q => val (e m) q z J) ?_) (val_pull hJ _ _ _).symm)
  have e2 : (fun p : Fin 2 × Fin d => φ' p.1 p.2) = fun p => MvPolynomial.map ψ (φ p.1 p.2) :=
    funext fun p => hφ p.1 p.2
  have hsq := subst_square ψ x0 m (fun p : Fin 2 × Fin d => φ p.1 p.2)
  simp only [Category.assoc, ← Over.comp_left, e2, hsq]

end GlobalTheory.FrameBaseChange

namespace GlobalTheory

open FrameBaseChange
open MvPolynomial (X C)

theorem isFrame_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S S' : Type) [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ Xo.X) (d : ℕ) (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S) (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (x : ∀ m, rjO x0 d m 1 ⟶ Xo.univ.t.G) (x' : ∀ m, rjO (spMap ψ ≫ x0) d m 1 ⟶ Xo.univ.t.G), (∀ m, x' m = rjBC ψ x0 d m 1 ≫ x m) → ∀ (e : ∀ m, RFrTy x0 d x m) (e' : ∀ m, RFrTy (spMap ψ ≫ x0) d x' m), (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → (∀ m, LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (e' m) (LB.pullGen Xo.univ.t.PP.L (cφ ![rjpt x0 d x m (0 : Fin 2), rjpt x0 d x m (1 : Fin 2)]) (cε 2) (e m) (rjBC ψ x0 d m 2).left)) → ∀ (ph1 ph2 : MvPowerSeries (Fin 3 × Fin d) S) (sy : MvPowerSeries (Fin 2 × Fin d) S) (ad : 𝓞 E → MvPowerSeries (Fin 2 × Fin d) S), RIsFrame x0 d x F act ph1 ph2 sy ad e → RIsFrame (spMap ψ ≫ x0) d x' (fun i => MvPowerSeries.map ψ (F i)) (fun a i => MvPowerSeries.map ψ (act a i)) (MvPowerSeries.map ψ ph1) (MvPowerSeries.map ψ ph2) (MvPowerSeries.map ψ sy) (fun a => MvPowerSeries.map ψ (ad a)) e' := by
  intro E _ _ _ H Dw l Xo S S' _ _ ψ x0 d F act x x' hx e e' he he' hc ph1 ph2 sy ad hF
  have hL : Xo.univ.t.PP.L.IsLB := Xo.univ.t.PP.isLB
  refine ⟨he', ?_, ?_, ?_, ?_⟩
  · intro m
    obtain ⟨u, hu, hcr⟩ := hF.ph1 m
    refine ⟨Units.map (jetBC ψ (Fin 3 × Fin d) m).toMonoidHom u, ?_, ?_⟩
    · rw [Units.coe_map]
      show jetBC ψ _ m (u : Jet S (Fin 3 × Fin d) m) = _
      rw [hu, ReciprocityTheory.ChartRestriction.G.PullbackSections.jetBC_psJet]
    · apply corr_of_val hL
      intro y J hJ
      have hlift : lift (rjpt (spMap ψ ≫ x0) d x' m (0 : Fin 3))
          (lift (rjpt (spMap ψ ≫ x0) d x' m (1 : Fin 3)) (rjpt (spMap ψ ≫ x0) d x' m (2 : Fin 3))) =
          rjBC ψ x0 d m 3 ≫ lift (rjpt x0 d x m (0 : Fin 3)) (lift (rjpt x0 d x m (1 : Fin 3)) (rjpt x0 d x m (2 : Fin 3))) := by
        simp only [point_bc hx, CartesianMonoidalCategory.comp_lift]
      refine (val_pull hJ _ _ _).trans ?_
      rw [hlift, Over.comp_left, ← Category.assoc]
      refine Eq.trans (val_pull hJ _ _ _).symm ((val_corr hJ hcr _).trans ((val_scale hJ _ _ _).trans ?_))
      refine Eq.trans ?_ (val_scale hJ _ _ _).symm
      refine congrArg₂ (· * ·) ?_ ?_
      · rw [gm_unit_map]
        rfl
      · simp only [val_mul hJ, val_inv]
        refine congrArg₂ (· * ·) ?_ (congrArg₂ (· * ·) (congrArg Inv.inv ?_) (congrArg Inv.inv ?_)) <;>
          exact (val_subst (hc m) hJ _ _ (by intro i j; fin_cases i <;> simp [psIn_map]) _).symm
  · intro m
    obtain ⟨u, hu, hcr⟩ := hF.ph2 m
    refine ⟨Units.map (jetBC ψ (Fin 3 × Fin d) m).toMonoidHom u, ?_, ?_⟩
    · rw [Units.coe_map]
      show jetBC ψ _ m (u : Jet S (Fin 3 × Fin d) m) = _
      rw [hu, ReciprocityTheory.ChartRestriction.G.PullbackSections.jetBC_psJet]
    · apply corr_of_val hL
      intro y J hJ
      have hlift : lift (rjpt (spMap ψ ≫ x0) d x' m (1 : Fin 3))
          (lift (rjpt (spMap ψ ≫ x0) d x' m (2 : Fin 3)) (rjpt (spMap ψ ≫ x0) d x' m (0 : Fin 3))) =
          rjBC ψ x0 d m 3 ≫ lift (rjpt x0 d x m (1 : Fin 3)) (lift (rjpt x0 d x m (2 : Fin 3)) (rjpt x0 d x m (0 : Fin 3))) := by
        simp only [point_bc hx, CartesianMonoidalCategory.comp_lift]
      refine (val_pull hJ _ _ _).trans ?_
      rw [hlift, Over.comp_left, ← Category.assoc]
      refine Eq.trans (val_pull hJ _ _ _).symm ((val_corr hJ hcr _).trans ((val_scale hJ _ _ _).trans ?_))
      refine Eq.trans ?_ (val_scale hJ _ _ _).symm
      refine congrArg₂ (· * ·) ?_ ?_
      · rw [gm_unit_map]
        rfl
      · simp only [val_mul hJ, val_inv]
        refine congrArg₂ (· * ·) ?_ (congrArg₂ (· * ·) (congrArg Inv.inv ?_) (congrArg Inv.inv ?_)) <;>
          exact (val_subst (hc m) hJ _ _ (by intro i j; fin_cases i <;> simp [psIn_map]) _).symm
  · intro m
    obtain ⟨u, hu, hcr⟩ := hF.sy m
    refine ⟨Units.map (jetBC ψ (Fin 2 × Fin d) m).toMonoidHom u, ?_, ?_⟩
    · rw [Units.coe_map]
      show jetBC ψ _ m (u : Jet S (Fin 2 × Fin d) m) = _
      rw [hu, ReciprocityTheory.ChartRestriction.G.PullbackSections.jetBC_psJet]
    · apply corr_of_val hL
      intro y J hJ
      refine ((val_corr hJ (hc m) _).trans (val_pull hJ _ _ _)).trans ?_
      refine ((val_corr hJ hcr _).trans (val_scale hJ _ _ _)).trans ?_
      refine Eq.trans ?_ (val_scale hJ _ _ _).symm
      refine congrArg₂ (· * ·) ?_ ?_
      · rw [← map_inv, gm_unit_map]
        rfl
      · refine (val_subst (hc m) hJ _ _ ?_ _).symm
        intro i j
        fin_cases i <;> simp
  · intro a
    obtain ⟨wL, hwL, hm⟩ := hF.ad a
    refine ⟨wL, hwL, fun m => ?_⟩
    obtain ⟨u, hu, hcr⟩ := hm m
    refine ⟨Units.map (jetBC ψ (Fin 2 × Fin d) m).toMonoidHom u, ?_, ?_⟩
    · rw [Units.coe_map]
      show jetBC ψ _ m (u : Jet S (Fin 2 × Fin d) m) = _
      rw [hu, ReciprocityTheory.ChartRestriction.G.PullbackSections.jetBC_psJet]
    · apply corr_of_val hL
      intro y J hJ
      have hlift : lift (rjpt (spMap ψ ≫ x0) d x' m (0 : Fin 2)) (rjpt (spMap ψ ≫ x0) d x' m (1 : Fin 2)) =
          rjBC ψ x0 d m 2 ≫ lift (rjpt x0 d x m (0 : Fin 2)) (rjpt x0 d x m (1 : Fin 2)) := by
        simp only [point_bc hx, CartesianMonoidalCategory.comp_lift]
      have h3 := (val_mul hJ _ _ _).symm.trans
        ((val_corr hJ hcr (𝟙 _ ≫ (rjBC ψ x0 d m 2).left)).trans (val_scale hJ _ _ _))
      refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (h3.trans (Eq.trans ?_ (val_scale hJ _ _ _).symm)))
      · refine congrArg₂ (· * ·) ?_ (val_subst (hc m) hJ _ _ (by intro i j; fin_cases i <;> simp [psIn_map]) _)
        refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
        show val wL (𝟙 _ ≫ (lift (rjpt (spMap ψ ≫ x0) d x' m (0 : Fin 2)) (rjpt (spMap ψ ≫ x0) d x' m (1 : Fin 2))).left) y J =
          val wL ((𝟙 _ ≫ (rjBC ψ x0 d m 2).left) ≫ (lift (rjpt x0 d x m (0 : Fin 2)) (rjpt x0 d x m (1 : Fin 2))).left) y J
        rw [hlift, Over.comp_left, Category.assoc]
      · refine congrArg₂ (· * ·) ?_ (val_subst (hc m) hJ _ _ (by intro i j; fin_cases i <;> simp [psIn_map]) _).symm
        rw [gm_unit_map]
        rfl

end GlobalTheory
