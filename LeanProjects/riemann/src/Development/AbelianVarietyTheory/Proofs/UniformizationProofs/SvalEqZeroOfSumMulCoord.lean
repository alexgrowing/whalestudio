import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.CancelSecAct

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace WeightVal

theorem eq_zero_of_stalk_sum {S : Scheme.{0}} (X : Type) [AddCommGroup X] (Y : Over S) {V : Y.left.Opens}
    (s : Finset X) (h : X → Γ(Y.left, V))
    (hs : ∀ w : (splitTorus S X ⊗ Y).left, (snd (splitTorus S X) Y).left w ∈ V →
      ∑ χ ∈ s, gs (𝟙 _) w ⊤ (TorusInj.chiP X Y χ) * gs (snd (splitTorus S X) Y).left w V (h χ) = 0) :
    ∀ χ ∈ s, h χ = 0 := by
  refine TorusInj.eq_zero_of_sum X Y s h (fn_ext fun w hw => ?_)
  have k : ∀ c : Γ(Y.left, V),
      gs (𝟙 _) w ((snd (splitTorus S X) Y).left ⁻¹ᵁ V) (((snd (splitTorus S X) Y).left.app V).hom c) =
        gs (snd (splitTorus S X) Y).left w V c := fun c =>
    (gs_pull (𝟙 _) _ w V hw c).trans (by rw [Category.id_comp])
  rw [DVR.gs_fsum (𝟙 _) w _ hw, gs_eq (𝟙 _) w _ hw 0, map_zero, map_zero]
  refine Eq.trans (Finset.sum_congr rfl fun χ _ => ?_) (hs w hw)
  rw [gs_mul (𝟙 _) w _ hw, k, gs_res (𝟙 _) w _ hw]

theorem gs_chiP_whisker {S : Scheme.{0}} (X : Type) [AddCommGroup X] {Z Y : Over S} (x : Z ⟶ Y) (χ : X)
    (w : (splitTorus S X ⊗ Z).left) :
    gs (splitTorus S X ◁ x).left w ⊤ (TorusInj.chiP X Y χ) = gs (𝟙 _) w ⊤ (TorusInj.chiP X Z χ) := by
  refine (gs_pull (splitTorus S X ◁ x).left (fst (splitTorus S X) Y).left w ⊤ trivial _).trans
    (Eq.trans ?_ (gs_pull (𝟙 _) (fst (splitTorus S X) Z).left w ⊤ trivial _).symm)
  rw [Category.id_comp, ← Over.comp_left, whiskerLeft_fst]

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)

theorem val_act (β : D.X) {W : Scheme.{0}} (ρ : W ⟶ (WeightPf.Te D I e ⊗ thickObj R I e G).left) (w : W) {J}
    (hJ : Good D.P.L w J) :
    (val (g.t β) (ρ ≫ (WeightPf.act g).left) w J).val =
      gs ρ w ⊤ (TorusInj.chiP D.X (thickObj R I e G) β) *
        (val (g.t β) (ρ ≫ (snd (WeightPf.Te D I e) (thickObj R I e G)).left) w J).val := by
  have E := val_corr hJ (g.t_weight β) ρ
  rw [val_mul hJ, val_pull hJ, val_pull hJ] at E
  refine (congrArg Units.val E).trans ((Units.val_mul _ _).trans (congrArg₂ (· * ·) ?_ rfl))
  have hm := hJ.mem (L := D.P.L) (K := PEmpty) (Y := (WeightPf.Te D I e ⊗ thickObj R I e G).left)
    PEmpty.elim ρ
  exact (congrArg Units.val ((gm_res ρ w _ hm _).trans
    (gm_pull ρ (fst (WeightPf.Te D I e) (thickObj R I e G)).left w ⊤ trivial (charUnit _ D.X β)))).trans
      ((gs_unit _ w ⊤ trivial _).symm.trans
      (gs_pull ρ (fst (WeightPf.Te D I e) (thickObj R I e G)).left w ⊤ trivial _).symm)

theorem coeff_eq_zero_over {Y : Over (Spec (CommRingCat.of R))} (p : Y ⟶ D.P.A) {K : Type} [Fintype K]
    {φ : D.X → K → (Y.left ⟶ D.P.A.left)} {ε : K → ℤ} (d : ∀ α, LB.Sec (LB.LinComb D.P.L (φ α) ε)) (s : Finset D.X)
    (H : ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ Y.left), r ≫ p.left = x ≫ g.pG.left →
      ∀ (z : Z) (J), Good D.P.L z J → ∑ α ∈ s, sval (d α) r z J * (val (g.t α) x z J).val = 0)
    (α : D.X) (hα : α ∈ s) (Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (x : Z ⟶ thickObj R I e G)
    (r : Z.left ⟶ Y.left) (hr : r ≫ p.left = x.left ≫ g.pG.left) (z : Z.left) (J) (hJ : Good D.P.L z J) :
    sval (d α) r z J = 0 := by
  classical
  let jf : D.X → K → D.P.L.ι := fun β a => J (r ≫ φ β a)
  let jt : D.X → Fin 4 → D.P.L.ι := fun β a => J (x.left ≫ D.Oφ g.pG β a)
  let V : Z.left.Opens := s.inf (fun β => r ⁻¹ᵁ LB.wchart D.P.L (φ β) (jf β) ⊓
      x.left ⁻¹ᵁ LB.wchart D.P.L (D.Oφ g.pG β) (jt β))
  have hz : z ∈ V := DVR.mem_finf s _ _ fun β _ => ⟨hJ.mem (φ β) r, hJ.mem (D.Oφ g.pG β) x.left⟩
  have hVf : ∀ β ∈ s, V ≤ r ⁻¹ᵁ LB.wchart D.P.L (φ β) (jf β) :=
    fun β hβ => (Finset.inf_le hβ).trans inf_le_left
  have hVt : ∀ β ∈ s, V ≤ x.left ⁻¹ᵁ LB.wchart D.P.L (D.Oφ g.pG β) (jt β) :=
    fun β hβ => (Finset.inf_le hβ).trans inf_le_right
  have ex : ∀ β ∈ s, ∃ c : Γ(Z.left, V), ∀ (W : Scheme.{0}) (ρ : W ⟶ Z.left) (w : W),
      ρ w ∈ V → gs ρ w V c = gs (ρ ≫ r) w (LB.wchart D.P.L (φ β) (jf β)) ((d β).f (jf β)) *
        (gm (ρ ≫ x.left) w (LB.wchart D.P.L (D.Oφ g.pG β) (jt β)) ((g.t β).s (jt β))).val := fun β hβ =>
    ⟨(r.appLE _ V (hVf β hβ)).hom ((d β).f (jf β)) * (x.left.appLE _ V (hVt β hβ)).hom ((g.t β).s (jt β)).val,
      fun W ρ w hw => (gs_mul ρ w V hw _ _).trans (congrArg₂ (· * ·) (gs_appLE _ _ V _ ρ w hw _)
        ((gs_appLE _ _ V _ ρ w hw _).trans (gs_unit (ρ ≫ x.left) w _ (hVt β hβ hw) _)))⟩
  choose! c hc using ex
  have hsn : (WeightPf.Te D I e ◁ x).left ≫ (snd (WeightPf.Te D I e) (thickObj R I e G)).left =
      (snd (WeightPf.Te D I e) Z).left ≫ x.left := by
    rw [← Over.comp_left, ← Over.comp_left, whiskerLeft_snd]
  let σ : Z ⟶ WeightPf.Te D I e ⊗ Z := lift (toUnit _ ≫ η[WeightPf.Te D I e]) (𝟙 _)
  have hσ : σ.left ≫ (snd (WeightPf.Te D I e) Z).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_snd, Over.id_left]
  have H0 := eq_zero_of_stalk_sum D.X Z s c (fun w hw => by
    choose j hj using fun ψ : (WeightPf.Te D I e ⊗ Z).left ⟶ D.P.A.left => exists_chart D.P.isLB (ψ w)
    let J₂ : ((WeightPf.Te D I e ⊗ Z).left ⟶ D.P.A.left) → D.P.L.ι := fun ψ =>
      if ψ w ∈ D.P.L.U (J (σ.left ≫ ψ)) then J (σ.left ≫ ψ) else j ψ
    have hJ₂ : Good D.P.L w J₂ := fun ψ => by
      by_cases h : ψ w ∈ D.P.L.U (J (σ.left ≫ ψ))
      · simpa only [J₂, if_pos h] using h
      · simpa only [J₂, if_neg h] using hj ψ
    have eJ : ∀ ψ : Z.left ⟶ D.P.A.left, ψ ((snd (WeightPf.Te D I e) Z).left w) ∈ D.P.L.U (J ψ) →
        J₂ ((snd (WeightPf.Te D I e) Z).left ≫ ψ) = J ψ := fun ψ h => by
      have e₁ : σ.left ≫ (snd (WeightPf.Te D I e) Z).left ≫ ψ = ψ := by
        rw [← Category.assoc, hσ, Category.id_comp]
      simp only [J₂, e₁]
      exact if_pos h
    have E := H _ ((WeightPf.Te D I e ◁ x).left ≫ (WeightPf.act g).left) ((snd (WeightPf.Te D I e) Z).left ≫ r)
      (by rw [Category.assoc, Category.assoc, hr, WeightPf.act_left_pG, ← Category.assoc, ← Category.assoc, hsn])
      w J₂ hJ₂
    refine Eq.trans (Finset.sum_congr rfl fun β hβ => ?_) E
    rw [hc β hβ _ _ w hw, val_act g β _ w hJ₂, mul_left_comm, hsn, gs_chiP_whisker,
      sval_of (d β) _ w J₂ (jf β) (fun a => by
        rw [Category.assoc]; exact eJ _ (Set.mem_iInter.1 (hVf β hβ hw) a)),
      val_of (g.t β) _ w J₂ (jt β) (fun a => by
        rw [Category.assoc]; exact eJ _ (Set.mem_iInter.1 (hVt β hβ hw) a))]) α hα
  have E := hc α hα _ (𝟙 _) z hz
  rw [H0, gs_eq _ z V hz, map_zero, map_zero, Category.id_comp, Category.id_comp] at E
  exact (Units.mul_left_eq_zero _).1 E.symm

end WeightVal

theorem sval_eq_zero_of_sum_mul_coord : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (Y : Over (Spec (CommRingCat.of R))) (p : Y ⟶ D.P.A) (K : Type) [Fintype K] (φ : D.X → K → (Y.left ⟶ D.P.A.left)) (ε : K → ℤ) (d : ∀ α, LB.Sec (LB.LinComb D.P.L (φ α) ε)) (s : Finset D.X), (∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ Y.left), r ≫ p.left = x ≫ g.pG.left → ∀ (z : Z) (J), Good D.P.L z J → ∑ α ∈ s, sval (d α) r z J * (val (g.t α) x z J).val = 0) → ∀ α ∈ s, ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ Y.left), r ≫ p.left = x ≫ g.pG.left → ∀ (z : Z) (J), Good D.P.L z J → sval (d α) r z J = 0 := by
  intro R _ _ I D e G _ _ g Y p K _ φ ε d s H α hα Z x r hr z J hJ
  exact WeightVal.coeff_eq_zero_over g p d s H α hα (Over.mk (x ≫ (thickObj R I e G).hom)) (Over.homMk x rfl) r hr z J hJ

end GlobalTheory
