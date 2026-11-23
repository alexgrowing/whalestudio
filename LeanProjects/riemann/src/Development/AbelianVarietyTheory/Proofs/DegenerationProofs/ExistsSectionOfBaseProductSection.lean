import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UnitThetaConstantsGenerateIntegralTorsionImports
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSumsAtHalfCurveFraction

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnitTheta

theorem le_preimage_wchart_of_section {X Y : Scheme.{0}} (L : LB X) (π : Y ⟶ X) (σ : X ⟶ Y) (h : σ ≫ π = 𝟙 X)
    (k : L.ι) : L.U k ≤ σ ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => π) (fun _ => k) := by
  intro x hx
  refine Set.mem_iInter.2 fun _ => ?_
  change (σ ≫ π) x ∈ L.U k
  rw [h]
  exact hx

noncomputable def secOfSection {X Y : Scheme.{0}} (L : LB X) (π : Y ⟶ X) (σ : X ⟶ Y) (h : σ ≫ π = 𝟙 X)
    (s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => π) (fun _ => 1))) : LB.Sec L where
  f k := (X.presheaf.map (homOfLE (le_preimage_wchart_of_section L π σ h k)).op).hom
    ((σ.app _).hom (s.f (fun _ => k)))
  compat i j := fn_ext fun x hx => by
    have li := le_preimage_wchart_of_section L π σ h i hx.1
    have lj := le_preimage_wchart_of_section L π σ h j hx.2
    rw [gs_res _ x inf_le_left hx, gs_mul _ x _ hx, gs_res _ x inf_le_right hx, gs_res _ x _ hx.1, gs_res _ x _ hx.2,
      gs_unit _ x _ hx]
    refine (gs_pull (𝟙 X) σ x _ li _).trans ((sec_trans s (𝟙 X ≫ σ) x li lj).trans
      (congrArg₂ (· * ·) ?_ (gs_pull (𝟙 X) σ x _ lj _).symm))
    simp only [trF, Fin.prod_univ_one, zpow_one, Category.assoc, h, Category.comp_id]

theorem gs_secOfSection {X Y Z : Scheme.{0}} (L : LB X) (π : Y ⟶ X) (σ : X ⟶ Y) (h : σ ≫ π = 𝟙 X)
    (s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => π) (fun _ => 1))) (r : Z ⟶ X) (z : Z) (k : L.ι)
    (hz : r z ∈ L.U k) : gs r z _ ((secOfSection L π σ h s).f k) =
      gs (r ≫ σ) z (LB.wchart L (fun _ : Fin 1 => π) (fun _ => k)) (s.f (fun _ => k)) :=
  (gs_res r z _ hz _).trans (gs_pull r σ z _ (le_preimage_wchart_of_section L π σ h k hz) _)

theorem valR_secOfSection {X Y : Scheme.{0}} (L : LB X) (π : Y ⟶ X) (σ : X ⟶ Y) (h : σ ≫ π = 𝟙 X)
    (s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => π) (fun _ => 1))) {F : Type} [CommRing F] (r : Sp F ⟶ X)
    (k : L.ι) (hr : ⊤ ≤ r ⁻¹ᵁ L.U k) : valR r _ ((secOfSection L π σ h s).f k) =
      valR (r ≫ σ) (LB.wchart L (fun _ : Fin 1 => π) (fun _ => k)) (s.f (fun _ => k)) :=
  (HolHom.valR_res r _ _ hr).trans (HolHom.valR_comp r σ _ _).symm

theorem mem_nonzeroLocus_secOfSection {X Y : Scheme.{0}} (L : LB X) (π : Y ⟶ X) (σ : X ⟶ Y) (h : σ ≫ π = 𝟙 X)
    (h' : π ≫ σ = 𝟙 Y) (s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => π) (fun _ => 1))) (y : Y)
    (hy : y ∈ nonzeroLocus s) : π y ∈ nonzeroLocus (secOfSection L π σ h s) := by
  obtain ⟨j, hj⟩ := AmpleSpan.exists_chart_of_mem s hy
  obtain ⟨k, rfl⟩ : ∃ k, j = fun _ => k := ⟨j (0 : Fin 1), funext fun i => by rw [Subsingleton.elim i 0]⟩
  have hk : π y ∈ L.U k := Set.mem_iInter.1 hj 0
  rw [AmpleSpan.mem_nonzeroLocus_iff_gs _ π y hk, gs_secOfSection L π σ h s π y k hk, h']
  exact (AmpleSpan.mem_nonzeroLocus_iff_gs s (𝟙 Y) y hj).1 hy

theorem exists_sec_of_baseOver : ∀ (R : Type) [CommRing R] (P : PolAV (Sp R)) (th : LB.Sec (LPow P.A P.L 1 (baseOver (Sp R)))), ∃ θ : LB.Sec P.L, (∀ y ∈ nonzeroLocus th, (snd (baseOver (Sp R)) P.A).left y ∈ nonzeroLocus θ) ∧ ∀ (z : baseOver (Sp R) ⟶ P.A) (τ : LB.Gen (LB.LinComb P.L (Y := (baseOver (Sp R)).left) (K := Fin 1) (fun _ => z.left) (fun _ => 1))) (a : R), IsValueAt P.A P.L 1 th z τ (fn a) → ∀ (F : Type) [CommRing F] (f : R →+* F) (k : P.L.ι), ⊤ ≤ (spMap f ≫ z.left) ⁻¹ᵁ P.L.U k → valR (spMap f ≫ z.left) _ (θ.f k) = f a * valR (X := (baseOver (Sp R)).left) (spMap f) _ (τ.s (fun _ => k)).val := by
  intro R _ P th
  let σ : P.A ⟶ baseOver (Sp R) ⊗ P.A := lift (toUnit P.A) (𝟙 P.A)
  have h : σ ≫ snd _ _ = 𝟙 _ := lift_snd _ _
  have h' : snd _ _ ≫ σ = 𝟙 _ := by
    refine CartesianMonoidalCategory.hom_ext _ _ (toUnit_unique _ _) ?_
    rw [Category.assoc, h, Category.comp_id, Category.id_comp]
  have hl : σ.left ≫ (snd (baseOver (Sp R)) P.A).left = 𝟙 _ := by rw [← Over.comp_left, h, Over.id_left]
  have hl' : (snd (baseOver (Sp R)) P.A).left ≫ σ.left = 𝟙 _ := by rw [← Over.comp_left, h', Over.id_left]
  refine ⟨secOfSection P.L _ σ.left hl th, mem_nonzeroLocus_secOfSection P.L _ σ.left hl hl' th, ?_⟩
  intro z τ a hv F _ f k hk
  have e : z ≫ σ = ptSecT P.A z := by
    refine CartesianMonoidalCategory.hom_ext _ _ (toUnit_unique _ _) ?_
    rw [Category.assoc, h, Category.comp_id, ptSecT, lift_snd]
  have e' : z.left ≫ σ.left = (ptSecT P.A z).left := by rw [← Over.comp_left, e]
  let x : Sp F ⟶ (baseOver (Sp R)).left := spMap f
  have hw : ⊤ ≤ x ⁻¹ᵁ LB.wchart P.L (fun _ : Fin 1 => z.left) (fun _ => k) :=
    fun p hp => Set.mem_iInter.2 fun _ => hk hp
  have H := congrArg (valR x _) (hv (fun _ => k))
  have H₁ := (HolHom.valR_comp x (ptSecT P.A z).left _ _).trans ((HolHom.valR_res x _ _ hw).symm.trans H)
  have H₂ := H₁.trans (((HolHom.valR_eq x _ hw _).trans (map_mul _ _ _)).trans (congrArg₂ (· * ·)
    ((HolHom.valR_eq x _ hw _).symm.trans ((HolHom.valR_res x _ _ hw).trans (Conv.valR_spMap_top f a)))
    (HolHom.valR_eq x _ hw _).symm))
  refine (valR_secOfSection P.L _ σ.left hl th (x ≫ z.left) k hk).trans ?_
  rw [Category.assoc, e']
  exact H₂

end GlobalTheory.UnitTheta
