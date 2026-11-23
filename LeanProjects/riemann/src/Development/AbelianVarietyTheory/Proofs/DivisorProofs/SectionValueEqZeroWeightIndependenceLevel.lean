import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistBaseChangeAndValuationStatements
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CrossRelationGivesConvolutionRelation
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalEqZeroOfIndepCombStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalEqZeroOfSumMulCoord
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.StalkMapInjectiveOfFlat
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.FieldBaseChange

noncomputable section

namespace GlobalTheory

namespace WeightValPart

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)

theorem coeff_eq_zero_over {Y : Over (Spec (CommRingCat.of R))} (p : Y ⟶ D.P.A) {X : Scheme.{0}} {N : LB X}
    (hN : N.IsLB) {ι₀ : D.P.A.left ⟶ X} {π : N.ι → D.P.L.ι} (hP : IsPart N D.P.L ι₀ π) {K : Type} [Fintype K]
    {φ : D.X → K → (Y.left ⟶ X)} {ε : K → ℤ} (d : ∀ α, LB.Sec (LB.LinComb N (φ α) ε)) (s : Finset D.X)
    (H : ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ Y.left), r ≫ p.left = x ≫ g.pG.left →
      ∀ (z : Z) (J), Good N z J → ∑ α ∈ s, sval (d α) r z J * (val (g.t α) x z (rs ι₀ π J)).val = 0)
    (α : D.X) (hα : α ∈ s) (Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (x : Z ⟶ thickObj R I e G)
    (r : Z.left ⟶ Y.left) (hr : r ≫ p.left = x.left ≫ g.pG.left) (z : Z.left) (J) (hJ : Good N z J) :
    sval (d α) r z J = 0 := by
  classical
  let jf : D.X → K → N.ι := fun β a => J (r ≫ φ β a)
  let jt : D.X → Fin 4 → D.P.L.ι := fun β a => rs ι₀ π J (x.left ≫ D.Oφ g.pG β a)
  let V : Z.left.Opens := s.inf (fun β => r ⁻¹ᵁ LB.wchart N (φ β) (jf β) ⊓
      x.left ⁻¹ᵁ LB.wchart D.P.L (D.Oφ g.pG β) (jt β))
  have hz : z ∈ V := DVR.mem_finf s _ _ fun β _ => ⟨hJ.mem (φ β) r, (hP.good hJ).mem (D.Oφ g.pG β) x.left⟩
  have hVf : ∀ β ∈ s, V ≤ r ⁻¹ᵁ LB.wchart N (φ β) (jf β) :=
    fun β hβ => (Finset.inf_le hβ).trans inf_le_left
  have hVt : ∀ β ∈ s, V ≤ x.left ⁻¹ᵁ LB.wchart D.P.L (D.Oφ g.pG β) (jt β) :=
    fun β hβ => (Finset.inf_le hβ).trans inf_le_right
  have ex : ∀ β ∈ s, ∃ c : Γ(Z.left, V), ∀ (W : Scheme.{0}) (ρ : W ⟶ Z.left) (w : W),
      ρ w ∈ V → gs ρ w V c = gs (ρ ≫ r) w (LB.wchart N (φ β) (jf β)) ((d β).f (jf β)) *
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
  have H0 := WeightVal.eq_zero_of_stalk_sum D.X Z s c (fun w hw => by
    choose j hj using fun ψ : (WeightPf.Te D I e ⊗ Z).left ⟶ X => exists_chart hN (ψ w)
    let J₂ : ((WeightPf.Te D I e ⊗ Z).left ⟶ X) → N.ι := fun ψ =>
      if ψ w ∈ N.U (J (σ.left ≫ ψ)) then J (σ.left ≫ ψ) else j ψ
    have hJ₂ : Good N w J₂ := fun ψ => by
      by_cases h : ψ w ∈ N.U (J (σ.left ≫ ψ))
      · simpa only [J₂, if_pos h] using h
      · simpa only [J₂, if_neg h] using hj ψ
    have eJ : ∀ ψ : Z.left ⟶ X, ψ ((snd (WeightPf.Te D I e) Z).left w) ∈ N.U (J ψ) →
        J₂ ((snd (WeightPf.Te D I e) Z).left ≫ ψ) = J ψ := fun ψ h => by
      have e₁ : σ.left ≫ (snd (WeightPf.Te D I e) Z).left ≫ ψ = ψ := by
        rw [← Category.assoc, hσ, Category.id_comp]
      simp only [J₂, e₁]
      exact if_pos h
    have E := H _ ((WeightPf.Te D I e ◁ x).left ≫ (WeightPf.act g).left) ((snd (WeightPf.Te D I e) Z).left ≫ r)
      (by rw [Category.assoc, Category.assoc, hr, WeightPf.act_left_pG, ← Category.assoc, ← Category.assoc, hsn])
      w J₂ hJ₂
    refine Eq.trans (Finset.sum_congr rfl fun β hβ => ?_) E
    rw [hc β hβ _ _ w hw, WeightVal.val_act g β _ w (hP.good hJ₂), mul_left_comm, hsn, WeightVal.gs_chiP_whisker,
      sval_of (d β) _ w J₂ (jf β) (fun a => by
        rw [Category.assoc]; exact eJ _ (Set.mem_iInter.1 (hVf β hβ hw) a)),
      val_of (g.t β) _ w (rs ι₀ π J₂) (jt β) (fun a => by
        have m : ((x.left ≫ D.Oφ g.pG β a) ≫ ι₀) ((snd (WeightPf.Te D I e) Z).left w) ∈
            N.U (J ((x.left ≫ D.Oφ g.pG β a) ≫ ι₀)) := (hP.mem _ _).2 (Set.mem_iInter.1 (hVt β hβ hw) a)
        show π (J₂ ((((snd (WeightPf.Te D I e) Z).left ≫ x.left) ≫ D.Oφ g.pG β a) ≫ ι₀)) =
          π (J ((x.left ≫ D.Oφ g.pG β a) ≫ ι₀))
        rw [show (((snd (WeightPf.Te D I e) Z).left ≫ x.left) ≫ D.Oφ g.pG β a) ≫ ι₀ =
          (snd (WeightPf.Te D I e) Z).left ≫ ((x.left ≫ D.Oφ g.pG β a) ≫ ι₀) by simp only [Category.assoc], eJ _ m])]) α hα
  have E := hc α hα _ (𝟙 _) z hz
  rw [H0, gs_eq _ z V hz, map_zero, map_zero, Category.id_comp, Category.id_comp] at E
  exact (Units.mul_left_eq_zero _).1 E.symm

end WeightValPart

theorem sval_eq_zero_of_sum_mul_coord_part : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (Y : Over (Spec (CommRingCat.of R))) (p : Y ⟶ D.P.A) (X : Scheme.{0}) (N : LB X), N.IsLB → ∀ (ι₀ : D.P.A.left ⟶ X) (π : N.ι → D.P.L.ι), IsPart N D.P.L ι₀ π → ∀ (K : Type) [Fintype K] (φ : D.X → K → (Y.left ⟶ X)) (ε : K → ℤ) (d : ∀ α, LB.Sec (LB.LinComb N (φ α) ε)) (s : Finset D.X), (∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ Y.left), r ≫ p.left = x ≫ g.pG.left → ∀ (z : Z) (J), Good N z J → ∑ α ∈ s, sval (d α) r z J * (val (g.t α) x z (rs ι₀ π J)).val = 0) → ∀ α ∈ s, ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ Y.left), r ≫ p.left = x ≫ g.pG.left → ∀ (z : Z) (J), Good N z J → sval (d α) r z J = 0 := by
  intro R _ _ I D e G _ _ g Y p X N hN ι₀ π hP K _ φ ε d s H α hα Z x r hr z J hJ
  exact WeightValPart.coeff_eq_zero_over g p hN hP d s H α hα (Over.mk (x ≫ (thickObj R I e G).hom))
    (Over.homMk x rfl) r hr z J hJ

end GlobalTheory
