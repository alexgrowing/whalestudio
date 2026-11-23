import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace CubeExtension

section Group

variable {S : Scheme.{0}}

theorem smooth_tensor (A B : Over S) [Smooth A.hom] [Smooth B.hom] : Smooth (A ⊗ B).hom := by
  change Smooth (pullback.fst A.hom B.hom ≫ A.hom)
  infer_instance

theorem geometricallyConnected_tensor (A B : Over S) [Smooth A.hom] [Smooth B.hom]
    [GeometricallyConnected A.hom] [GeometricallyConnected B.hom] :
    GeometricallyConnected (A ⊗ B).hom := by
  change GeometricallyConnected (pullback.fst A.hom B.hom ≫ A.hom)
  exact GeometricallyConnected.comp _ _

variable (G : Over S) [GrpObj G] [IsCommMonObj G]

theorem eSec_comp : eSec G ≫ G.hom = 𝟙 S := Over.w η[G]

theorem eSec_three :
    eSec (G3 G) = (lift (1 : 𝟙_ (Over S) ⟶ G) (lift (1 : 𝟙_ (Over S) ⟶ G) (1 : 𝟙_ (Over S) ⟶ G))).left := by
  unfold eSec
  congr 1
  ext <;> simp [Hom.one_def]

theorem formEq_origin :
    FormEq (K := PEmpty) (PEmpty.elim : PEmpty → ((𝟙_ (Over S)).left ⟶ G.left)) PEmpty.elim
      (fun I => eSec (G3 G) ≫ thφ G (x3 G) I) thε := by
  intro U _ h
  rw [eSec_three, prod_cub]
  simp

end Group

theorem pullGen_genPull {X Y Z : Scheme.{0}} (M : LB X) (c : LB.Gen M) (f : Y ⟶ X) (h : Z ⟶ Y) :
    LB.pullGen M _ _ (LB.genPull M c f) h = LB.genPull M c (h ≫ f) := by
  refine lbGen_ext fun j => congrArg Units.val ?_
  exact LB.pull_res_comp h f _ _ _ _ _

end CubeExtension

open CubeExtension

theorem cubical_extends_of_extension
    (h₁ : (∀ (X S : Scheme.{0}) (f : X ⟶ S), Smooth f → GeometricallyConnected f → GeometricallyIntegral f))
    (h₂ : (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (K : Type) [Field K] [Algebra V K] [IsFractionRing V K] (H X : Scheme.{0}) (p : H ⟶ Spec (CommRingCat.of V)) (e : Spec (CommRingCat.of V) ⟶ H), Smooth p → GeometricallyIntegral p → e ≫ p = 𝟙 _ → ∀ (eK : Spec (CommRingCat.of K) ⟶ pullback p (etaK V K)), eK ≫ pullback.fst p (etaK V K) = etaK V K ≫ e → ∀ (L : LB X), L.IsLB → ∀ (I : Type) [Fintype I] (φ : I → (H ⟶ X)) (ε : I → ℤ) (t : LB.Gen (LB.LinComb L (fun i => pullback.fst p (etaK V K) ≫ φ i) ε)) (ρ : LB.Gen (LB.LinComb L (fun i => e ≫ φ i) ε)), t.IsGen → ρ.IsGen → LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t eK) (LB.pullGen L _ _ ρ (etaK V K)) → ∃! c : LB.Gen (LB.LinComb L φ ε), c.IsGen ∧ LB.pullGen L _ _ c (pullback.fst p (etaK V K)) = t)) : Semi.cubical_extendsSt.{0} := by
  intro V _ _ _ K _ _ _ G _ _ _ _ _ _ eA heA L t hc ht
  have s₂ := smooth_tensor G G
  have s₃ := smooth_tensor G (G ⊗ G)
  have c₂ := geometricallyConnected_tensor G G
  have c₃ := geometricallyConnected_tensor G (G ⊗ G)
  obtain ⟨ρ, hρ, hv⟩ := exists_gen L.isLB (formEq_origin G) (LB.oneGen L.L) (LB.isGen_oneGen L.L)
  refine h₂ V K (G3 G).left G.left (G3 G).hom (eSec (G3 G)) s₃ (h₁ _ _ _ s₃ c₃) (eSec_comp _) eA heA
    L.L L.isLB thK (thφ G (x3 G)) thε t ρ ht hρ (corr_of_val L.isLB fun y J hJ => ?_)
  refine (val_corr hJ hc (𝟙 _)).trans ((val_one _).trans (Eq.symm ?_))
  exact (val_pull hJ ρ _ _).trans ((hv _ _ y J hJ).trans (val_one _))

theorem extendGen_of_extension
    (h₁ : (∀ (X S : Scheme.{0}) (f : X ⟶ S), Smooth f → GeometricallyConnected f → GeometricallyIntegral f))
    (h₂ : (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (K : Type) [Field K] [Algebra V K] [IsFractionRing V K] (H X : Scheme.{0}) (p : H ⟶ Spec (CommRingCat.of V)) (e : Spec (CommRingCat.of V) ⟶ H), Smooth p → GeometricallyIntegral p → e ≫ p = 𝟙 _ → ∀ (eK : Spec (CommRingCat.of K) ⟶ pullback p (etaK V K)), eK ≫ pullback.fst p (etaK V K) = etaK V K ≫ e → ∀ (L : LB X), L.IsLB → ∀ (I : Type) [Fintype I] (φ : I → (H ⟶ X)) (ε : I → ℤ) (t : LB.Gen (LB.LinComb L (fun i => pullback.fst p (etaK V K) ≫ φ i) ε)) (ρ : LB.Gen (LB.LinComb L (fun i => e ≫ φ i) ε)), t.IsGen → ρ.IsGen → LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t eK) (LB.pullGen L _ _ ρ (etaK V K)) → ∃! c : LB.Gen (LB.LinComb L φ ε), c.IsGen ∧ LB.pullGen L _ _ c (pullback.fst p (etaK V K)) = t)) : Semi.extendGenSt.{0} := by
  intro V _ _ _ K _ _ _ G _ _ _ _ _ _ eA heA N r hr hc
  obtain ⟨c, ⟨hc₁, hc₂⟩, hu⟩ := h₂ V K G.left G.left G.hom (eSec G) inferInstance
    (h₁ _ _ _ inferInstance inferInstance) (eSec_comp _) eA heA N.L N.isLB PUnit (fun _ => 𝟙 _)
    (fun _ => 1) r N.rig hr N.rigGen hc
  obtain ⟨r', ⟨h₃, h₄⟩, hu'⟩ := existsUnique_genPull_eq (𝟙 G.left)
    (fun _ => Function.bijective_id) N.L c hc₁
  refine ⟨r', ⟨h₃, ?_⟩, fun r'' ⟨h₅, h₆⟩ => hu' r'' ⟨h₅, hu _ ⟨LB.isGen_genPull _ _ h₅ _, ?_⟩⟩⟩
  · rw [← h₄, pullGen_genPull] at hc₂
    exact hc₂
  · rw [pullGen_genPull]
    exact h₆

theorem cubical_extends_and_extendGen :
    (∀ (X S : Scheme.{0}) (f : X ⟶ S), Smooth f → GeometricallyConnected f → GeometricallyIntegral f) →
    (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (K : Type) [Field K] [Algebra V K] [IsFractionRing V K] (H X : Scheme.{0}) (p : H ⟶ Spec (CommRingCat.of V)) (e : Spec (CommRingCat.of V) ⟶ H), Smooth p → GeometricallyIntegral p → e ≫ p = 𝟙 _ → ∀ (eK : Spec (CommRingCat.of K) ⟶ pullback p (etaK V K)), eK ≫ pullback.fst p (etaK V K) = etaK V K ≫ e → ∀ (L : LB X), L.IsLB → ∀ (I : Type) [Fintype I] (φ : I → (H ⟶ X)) (ε : I → ℤ) (t : LB.Gen (LB.LinComb L (fun i => pullback.fst p (etaK V K) ≫ φ i) ε)) (ρ : LB.Gen (LB.LinComb L (fun i => e ≫ φ i) ε)), t.IsGen → ρ.IsGen → LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t eK) (LB.pullGen L _ _ ρ (etaK V K)) → ∃! c : LB.Gen (LB.LinComb L φ ε), c.IsGen ∧ LB.pullGen L _ _ c (pullback.fst p (etaK V K)) = t) →
    Semi.cubical_extendsSt.{0} ∧ Semi.extendGenSt.{0} :=
  fun h₁ h₂ => ⟨cubical_extends_of_extension h₁ h₂, extendGen_of_extension h₁ h₂⟩

end GlobalTheory
