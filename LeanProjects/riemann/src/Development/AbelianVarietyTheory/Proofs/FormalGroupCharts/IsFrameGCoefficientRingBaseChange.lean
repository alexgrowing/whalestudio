import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBGen
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartPrimTrPfA
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.IntChartPf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExistsTruncatedIntegralChart
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.JetSubstPCompJetBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TripleFrameBaseChange

open MvPolynomial (X C)

theorem spec_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R' →+* R'') (g : R →+* R') :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem gm_unit_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (u : Aˣ) {Z : Scheme.{0}} (r : Z ⟶ Sp B)
    (z : Z) : gm r z ⊤ (unitΓ (Units.map f.toMonoidHom u)) = gm (r ≫ spMap f) z ⊤ (unitΓ u) := by
  refine Eq.trans ?_ (gm_pull r (spMap f) z ⊤ trivial (unitΓ u))
  refine congrArg (gm r z ⊤) (Units.ext ?_)
  exact congrArg (fun q => q.hom u.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} {t : SAB H X0}

theorem val_scale {Y Z : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ t.G.left)} {ε : K → ℤ}
    {z : Z} {J : (Z ⟶ t.G.left) → t.PP.L.ι} (hJ : Good t.PP.L z J) (c : Γ(Y, ⊤)ˣ)
    (g : LB.Gen (LB.LinComb t.PP.L φ ε)) (r : Z ⟶ Y) :
    val (scaleGenG t φ ε c g) r z J = gm r z ⊤ c * val g r z J :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z le_top (hJ.mem φ r) c) rfl)

variable {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ X0)

def jetOver (d m n : ℕ) : jOG (spMap ψ ≫ x0) d m n ⟶ jOG x0 d m n :=
  Over.homMk (spMap (jetBC ψ (Fin n × Fin d) m)) (by
    dsimp
    simp only [spMap, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 3
    ext s
    exact jetBC_algebraMap ψ _ m s)

theorem psIn_map {d n n' : ℕ} (m : ℕ) (r : Fin n → Fin n') (f : MvPowerSeries (Fin n × Fin d) S) :
    psIn d m r (MvPowerSeries.map ψ f) = MvPolynomial.map ψ (psIn d m r f) := by
  unfold psIn
  rw [MvPolynomial.map_rename]
  congr 1
  unfold psTrunc
  rw [map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [MvPolynomial.map_monomial, MvPowerSeries.coeff_map]

theorem subst_square {n n' d : ℕ} (m : ℕ) (φ : Fin n × Fin d → MvPolynomial (Fin n' × Fin d) S) :
    homAt (spMap ψ ≫ x0) (jetSubstP m (fun i => MvPolynomial.map ψ (φ i)) :
        Jet S' (Fin n × Fin d) m →ₐ[S'] Jet S' (Fin n' × Fin d) m) ≫ jetOver ψ x0 d m n =
      jetOver ψ x0 d m n' ≫ homAt x0 (jetSubstP m φ : Jet S (Fin n × Fin d) m →ₐ[S] Jet S (Fin n' × Fin d) m) := by
  apply Over.OverMorphism.ext
  show spMap _ ≫ spMap (jetBC ψ _ m) = spMap (jetBC ψ _ m) ≫ spMap _
  rw [spec_comp, spec_comp]
  exact congrArg spMap (PullbackSections.jetSubstP_comp_jetBC ψ m φ)

theorem jetMap_congr {R κ κ' : Type} [CommRing R] {m : ℕ} {f g : κ → MvPolynomial κ' R} (e : f = g)
    (hf : ∀ i, f i ∈ orig R κ') (hg : ∀ i, g i ∈ orig R κ') : jetMap (m := m) f hf = jetMap (m := m) g hg := by
  subst e
  rfl

theorem copy_square (d m n : ℕ) (i : Fin n) :
    homAt (spMap ψ ≫ x0) (jetCopy d m i : Jet S' (Fin 1 × Fin d) m →ₐ[S'] Jet S' (Fin n × Fin d) m) ≫
        jetOver ψ x0 d m 1 =
      jetOver ψ x0 d m n ≫ homAt x0 (jetCopy d m i : Jet S (Fin 1 × Fin d) m →ₐ[S] Jet S (Fin n × Fin d) m) := by
  apply Over.OverMorphism.ext
  show spMap _ ≫ spMap (jetBC ψ _ m) = spMap (jetBC ψ _ m) ≫ spMap _
  rw [spec_comp, spec_comp]
  have e := PullbackSections.jetMap_comp_jetBC ψ m (fun p : Fin 1 × Fin d => (X (i, p.2) : MvPolynomial (Fin n × Fin d) S))
    (fun _ => X_mem_orig _) (fun p => by rw [MvPolynomial.map_X]; exact X_mem_orig _)
  rw [jetMap_congr (show (fun p : Fin 1 × Fin d => MvPolynomial.map ψ (X (i, p.2) : MvPolynomial (Fin n × Fin d) S)) =
    fun p => X (i, p.2) from funext fun p => MvPolynomial.map_X ψ _) _ (fun _ => X_mem_orig _)] at e
  exact congrArg spMap e

variable {ψ x0} {d : ℕ} {x : ∀ m, jOG x0 d m 1 ⟶ t.G} {x' : ∀ m, jOG (spMap ψ ≫ x0) d m 1 ⟶ t.G}

theorem point_bc (hx : ∀ m, x' m = jetOver ψ x0 d m 1 ≫ x m) {n : ℕ} (m : ℕ) (i : Fin n) :
    jptG t (spMap ψ ≫ x0) d x' m i = jetOver ψ x0 d m n ≫ jptG t x0 d x m i := by
  unfold jptG
  rw [hx m, ← Category.assoc, copy_square, Category.assoc]

variable {e : ∀ m, FrTyG t x0 d x m} {e' : ∀ m, FrTyG t (spMap ψ ≫ x0) d x' m} {m : ℕ}
  (hc : LB.Gen.Corr t.PP.L _ _ _ _ (e' m) (LB.pullGen t.PP.L
    (cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)]) (cε 2) (e m) (jetOver ψ x0 d m 2).left))
  {Z : Scheme.{0}} {z : Z} {J : (Z ⟶ t.G.left) → t.PP.L.ι} (hJ : Good t.PP.L z J)
include hc hJ

theorem val_subst {n : ℕ} (φ : Fin 2 → Fin d → MvPolynomial (Fin n × Fin d) S)
    (φ' : Fin 2 → Fin d → MvPolynomial (Fin n × Fin d) S') (hφ : ∀ i j, φ' i j = MvPolynomial.map ψ (φ i j))
    (r : Z ⟶ (jOG (spMap ψ ≫ x0) d m n).left) :
    val (peG t (spMap ψ ≫ x0) d x' e' m φ') r z J = val (peG t x0 d x e m φ) (r ≫ (jetOver ψ x0 d m n).left) z J := by
  obtain rfl : φ' = fun i j => MvPolynomial.map ψ (φ i j) := funext fun i => funext fun j => hφ i j
  refine (val_pull hJ _ _ _).trans ((val_corr hJ hc _).trans ((val_pull hJ _ _ _).trans
    (Eq.trans ?_ (val_pull hJ _ _ _).symm)))
  rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left,
    subst_square ψ x0 m (fun p : Fin 2 × Fin d => φ p.1 p.2)]

end GlobalTheory.TripleFrameBaseChange

namespace GlobalTheory

open TripleFrameBaseChange
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X C)

theorem isFrameG_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S S' : Type) [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ X0) (x1 : Sp S' ⟶ X0), x1 = spMap ψ ≫ x0 → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG x1 d m 1 ⟶ t.G), (∀ m, (x' m).left = spMap (jetCoef ψ (Fin 1 × Fin d) m) ≫ (x m).left) → ∀ (e : ∀ m, FrTyG t x0 d x m) (e' : ∀ m, FrTyG t x1 d x' m), (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → (∀ m, LB.Gen.Corr t.PP.L _ _ _ _ (e' m) (LB.pullGen t.PP.L _ _ (e m) (spMap (jetCoef ψ (Fin 2 × Fin d) m)))) → ∀ (F : Fin d → PS S 2 d) (act : 𝓞 E → Fin d → PS S 1 d) (ph1 ph2 : PS S 3 d) (sy : PS S 2 d) (ad : 𝓞 E → PS S 2 d), IsFrameG t x0 d x F act ph1 ph2 sy ad e → IsFrameG t x1 d x' (fun i => (MvPowerSeries.map ψ (F i))) (fun a i => (MvPowerSeries.map ψ (act a i))) (MvPowerSeries.map ψ ph1) (MvPowerSeries.map ψ ph2) (MvPowerSeries.map ψ sy) (fun a => (MvPowerSeries.map ψ (ad a))) e' := by
  intro E _ _ _ H X0 t S S' _ _ ψ x0 x1 h01 d x x' hx0 e e' _ he' hc0 F act ph1 ph2 sy ad h
  subst h01
  have hx : ∀ m, x' m = jetOver ψ x0 d m 1 ≫ x m := fun m => Over.OverMorphism.ext (hx0 m)
  have hc : ∀ m, LB.Gen.Corr t.PP.L _ _ _ _ (e' m) (LB.pullGen t.PP.L
      (cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)]) (cε 2) (e m) (jetOver ψ x0 d m 2).left) := hc0
  have hX : ∀ {n : ℕ} (p : Fin n × Fin d), (X p : MvPolynomial (Fin n × Fin d) S') = MvPolynomial.map ψ (X p) :=
    fun p => (MvPolynomial.map_X ψ p).symm
  refine ⟨he', fun m => ?_, fun m => ?_, fun m => ?_, fun a => ?_⟩
  · obtain ⟨u, hu, hcor⟩ := h.ph1 m
    refine ⟨Units.map (jetBC ψ _ m).toMonoidHom u, (congrArg (jetBC ψ _ m) hu).trans (PullbackSections.jetBC_psJet ψ m ph1),
      corr_of_val t.PP.isLB fun y J hJ => ?_⟩
    have k := val_corr hJ hcor (𝟙 _ ≫ (jetOver ψ x0 d m 3).left)
    refine (val_pull hJ _ _ _).trans (Eq.trans ?_ ((val_pull hJ _ _ _).symm.trans (k.trans ?_)))
    · rw [point_bc hx, point_bc hx, point_bc hx, ← comp_lift, ← comp_lift, Over.comp_left, Category.assoc]
    · refine (val_scale hJ _ _ _).trans (Eq.trans ?_ (val_scale hJ _ _ _).symm)
      refine congrArg₂ (· * ·) (gm_unit_map _ u _ y).symm ?_
      refine (val_mul hJ _ _ _).trans (Eq.trans (congrArg₂ (· * ·) ?_ ?_) (val_mul hJ _ _ _).symm)
      · exact (val_subst (hc m) hJ _ _ (Fin.forall_fin_two.2 ⟨fun j => psIn_map ψ m _ _, fun j => hX _⟩) _).symm
      refine (val_mul hJ _ _ _).trans (Eq.trans (congrArg₂ (· * ·) ?_ ?_) (val_mul hJ _ _ _).symm)
      all_goals
        exact (val_inv _ _).trans ((congrArg (·⁻¹)
          (val_subst (hc m) hJ _ _ (Fin.forall_fin_two.2 ⟨fun j => hX _, fun j => hX _⟩) _).symm).trans
          (val_inv _ _).symm)
  · obtain ⟨u, hu, hcor⟩ := h.ph2 m
    refine ⟨Units.map (jetBC ψ _ m).toMonoidHom u, (congrArg (jetBC ψ _ m) hu).trans (PullbackSections.jetBC_psJet ψ m ph2),
      corr_of_val t.PP.isLB fun y J hJ => ?_⟩
    have k := val_corr hJ hcor (𝟙 _ ≫ (jetOver ψ x0 d m 3).left)
    refine (val_pull hJ _ _ _).trans (Eq.trans ?_ ((val_pull hJ _ _ _).symm.trans (k.trans ?_)))
    · rw [point_bc hx, point_bc hx, point_bc hx, ← comp_lift, ← comp_lift, Over.comp_left, Category.assoc]
    · refine (val_scale hJ _ _ _).trans (Eq.trans ?_ (val_scale hJ _ _ _).symm)
      refine congrArg₂ (· * ·) (gm_unit_map _ u _ y).symm ?_
      refine (val_mul hJ _ _ _).trans (Eq.trans (congrArg₂ (· * ·) ?_ ?_) (val_mul hJ _ _ _).symm)
      · exact (val_subst (hc m) hJ _ _ (Fin.forall_fin_two.2 ⟨fun j => hX _, fun j => psIn_map ψ m _ _⟩) _).symm
      refine (val_mul hJ _ _ _).trans (Eq.trans (congrArg₂ (· * ·) ?_ ?_) (val_mul hJ _ _ _).symm)
      all_goals
        exact (val_inv _ _).trans ((congrArg (·⁻¹)
          (val_subst (hc m) hJ _ _ (Fin.forall_fin_two.2 ⟨fun j => hX _, fun j => hX _⟩) _).symm).trans
          (val_inv _ _).symm)
  · obtain ⟨u, hu, hcor⟩ := h.sy m
    refine ⟨Units.map (jetBC ψ _ m).toMonoidHom u, (congrArg (jetBC ψ _ m) hu).trans (PullbackSections.jetBC_psJet ψ m sy),
      corr_of_val t.PP.isLB fun y J hJ => ?_⟩
    have k := val_corr hJ hcor (𝟙 _ ≫ (jetOver ψ x0 d m 2).left)
    refine (val_corr hJ (hc m) _).trans ((val_pull hJ _ _ _).trans (k.trans ?_))
    refine (val_scale hJ _ _ _).trans (Eq.trans ?_ (val_scale hJ _ _ _).symm)
    refine congrArg₂ (· * ·) (gm_unit_map _ u⁻¹ _ y).symm ?_
    exact (val_subst (hc m) hJ _ _ (Fin.forall_fin_two.2 ⟨fun j => hX _, fun j => hX _⟩) _).symm
  · obtain ⟨wL, hw, hall⟩ := h.ad a
    refine ⟨wL, hw, fun m => ?_⟩
    obtain ⟨u, hu, hcor⟩ := hall m
    refine ⟨Units.map (jetBC ψ _ m).toMonoidHom u, (congrArg (jetBC ψ _ m) hu).trans (PullbackSections.jetBC_psJet ψ m (ad a)),
      corr_of_val t.PP.isLB fun y J hJ => ?_⟩
    have k := val_corr hJ hcor (𝟙 _ ≫ (jetOver ψ x0 d m 2).left)
    refine (val_mul hJ _ _ _).trans (Eq.trans (congrArg₂ (· * ·) ?_ ?_) ((val_mul hJ _ _ _).symm.trans (k.trans ?_)))
    · refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
      rw [point_bc hx, point_bc hx, ← comp_lift, Over.comp_left, Category.assoc]
    · exact val_subst (hc m) hJ _ _ (Fin.forall_fin_two.2 ⟨fun j => psIn_map ψ m _ _, fun j => hX _⟩) _
    · refine (val_scale hJ _ _ _).trans (Eq.trans ?_ (val_scale hJ _ _ _).symm)
      refine congrArg₂ (· * ·) (gm_unit_map _ u _ y).symm ?_
      exact (val_subst (hc m) hJ _ _ (Fin.forall_fin_two.2 ⟨fun j => hX _, fun j => psIn_map ψ m _ _⟩) _).symm

end GlobalTheory
