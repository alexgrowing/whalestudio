import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubicalOfNormalised
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqOneOfAppLESectionEqOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothGeometricallyIntegralAbLocusTensorObj

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory.CubeGen

open GlobalTheory.AbLaw.Cube

theorem surjective_appTop {X : Scheme.{0}} (P : Over X) (e : 𝟙_ (Over X) ⟶ P) (hs : Smooth P.hom)
    (hg : GeometricallyIntegral P.hom) (hr : IsReduced X) (hab : genericPoints X ⊆ abLocus P) :
    Function.Surjective P.hom.appTop.hom := by
  change ∀ u : Γ(P.left, P.hom ⁻¹ᵁ ⊤), ∃ a, (P.hom.app ⊤).hom a = u
  intro u
  have he : e.left ≫ P.hom = 𝟙 X := Over.w e
  have hle : (⊤ : X.Opens) ≤ e.left ⁻¹ᵁ (P.hom ⁻¹ᵁ ⊤) := fun _ _ => trivial
  have key : ∀ (g : X ⟶ X) (hg : g = 𝟙 X) (h' : (⊤ : X.Opens) ≤ g ⁻¹ᵁ ⊤) (c : Γ(X, ⊤)),
      (g.appLE ⊤ ⊤ h').hom c = c := by
    rintro g rfl h' c
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
    change (X.presheaf.map (𝟙 (Opposite.op (⊤ : X.Opens)))).hom c = c
    rw [CategoryTheory.Functor.map_id]
    rfl
  have hφψ : ∀ c : Γ(X, ⊤), (e.left.appLE (P.hom ⁻¹ᵁ ⊤) ⊤ hle).hom ((P.hom.app ⊤).hom c) = c := fun c =>
    (congrArg (fun φ => CommRingCat.Hom.hom φ c) (Scheme.Hom.comp_appLE e.left P.hom ⊤ ⊤ hle)).symm.trans
      (key _ he hle c)
  refine ⟨(e.left.appLE (P.hom ⁻¹ᵁ ⊤) ⊤ hle).hom u, ?_⟩
  have h1 := GlobalTheory.eq_one_of_appLE_section_eq_one X P e.left he hs hg ⟨hr, hab⟩ ⊤
    (1 + u - (P.hom.app ⊤).hom ((e.left.appLE (P.hom ⁻¹ᵁ ⊤) ⊤ hle).hom u)) hle
    (by rw [map_sub, map_add, map_one, hφψ]; ring)
  linear_combination -h1

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

def cubicalOfNormalised (s₂ : Function.Surjective (A ⊗ A).hom.appTop.hom)
    (s₃ : Function.Surjective (A ⊗ A ⊗ A).hom.appTop.hom) (s₄ : Function.Surjective (A ⊗ A ⊗ A ⊗ A).hom.appTop.hom)
    (M : RigLB A) (t : LB.Gen (Theta A M.L)) (ht : t.IsGen) (hn : IsNormalised t) : CubicalStr A M :=
  { t := t
    isGen := ht
    face := fun i => by
      have key : ∀ a b c : G2 A ⟶ A, lift 1 1 ≫ a = (1 : 𝟙_ (Over S) ⟶ A) → lift 1 1 ≫ b = (1 : 𝟙_ (Over S) ⟶ A) →
          lift 1 1 ≫ c = (1 : 𝟙_ (Over S) ⟶ A) → a = 1 ∨ b = 1 ∨ c = 1 →
          LB.Gen.Corr M.L _ _ (Y := (G2 A).left) _ _
            (LB.pullGen M.L (thφ A (x3 A)) thε t (lift a (lift b c)).left) (LB.oneGen M.L) := by
        intro a b c ha hb hc h
        refine corr_of_val_section M.isLB s₂ (lift 1 1) (fun V _ k => ?_) (DVR.pullGen_isGen _ _ _ _ ht _) oneGen_isGen
          (fun y J hJ => (hn.pull _ ha hb hc hJ).trans (val_one _).symm)
        refine (Fintype.prod_empty _).trans (Eq.trans ?_ (prod_cub a b c k).symm)
        apply Additive.ofMul.injective
        rcases h with rfl | rfl | rfl <;> simp only [_root_.mul_one, _root_.one_mul, ofMul_mul, ofMul_inv, ofMul_one] <;> abel
      fin_cases i
      · exact key 1 (x2 A 0) (x2 A 1) (MonObj.comp_one _) (by simp [x2]) (by simp [x2]) (.inl rfl)
      · exact key (x2 A 0) 1 (x2 A 1) (by simp [x2]) (MonObj.comp_one _) (by simp [x2]) (.inr (.inl rfl))
      · exact key (x2 A 0) (x2 A 1) 1 (by simp [x2]) (by simp [x2]) (MonObj.comp_one _) (.inr (.inr rfl))
    cubeSymmetric_swap_first := by
      refine corr_of_val_section M.isLB s₃ (lift 1 (lift 1 1)) (φ := thφ A (x3 A)) (ε := thε) (fun V _ k => ?_) ht
        (DVR.pullGen_isGen _ _ _ _ ht _) (fun y J hJ => (hn y J hJ).trans
          (hn.pull _ (by simp [x3]) (by simp [x3]) (by simp [x3]) hJ).symm)
      refine (prod_cub _ _ _ k).trans (Eq.trans ?_ ((prod_theta k).trans (prod_cub _ _ _ k)).symm)
      rw [_root_.mul_comm (x3 A 1) (x3 A 0)]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    cubeSymmetric_swap_last := by
      refine corr_of_val_section M.isLB s₃ (lift 1 (lift 1 1)) (φ := thφ A (x3 A)) (ε := thε) (fun V _ k => ?_) ht
        (DVR.pullGen_isGen _ _ _ _ ht _) (fun y J hJ => (hn y J hJ).trans
          (hn.pull _ (by simp [x3]) (by simp [x3]) (by simp [x3]) hJ).symm)
      refine (prod_cub _ _ _ k).trans (Eq.trans ?_ ((prod_theta k).trans (prod_cub _ _ _ k)).symm)
      rw [_root_.mul_comm (x3 A 2) (x3 A 1), mul_right_comm (x3 A 0) (x3 A 2)]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    cocycle := by
      let e : 𝟙_ (Over S) ⟶ G4 A := lift 1 (lift 1 (lift 1 1))
      have e₀ : e ≫ x4 A 0 = 1 := by simp [e, x4]
      have e₁ : e ≫ x4 A 1 = 1 := by simp [e, x4]
      have e₂ : e ≫ x4 A 2 = 1 := by simp [e, x4]
      have e₃ : e ≫ x4 A 3 = 1 := by simp [e, x4]
      have f₀ : e ≫ padd A (x4 A 0) (x4 A 1) = 1 := (MonObj.comp_mul _ _ _).trans (by rw [e₀, e₁, _root_.mul_one])
      have f₁ : e ≫ padd A (x4 A 1) (x4 A 2) = 1 := (MonObj.comp_mul _ _ _).trans (by rw [e₁, e₂, _root_.mul_one])
      refine corr_of_val_section M.isLB s₄ e (fun V _ k => ?_)
        (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _) (DVR.pullGen_isGen _ _ _ _ ht _))
        (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _) (DVR.pullGen_isGen _ _ _ _ ht _))
        (fun y J hJ => ((val_mul hJ _ _ _).trans
          (congrArg₂ (· * ·) (hn.pull e f₀ e₂ e₃ hJ) (hn.pull e e₀ e₁ e₃ hJ))).trans ((val_mul hJ _ _ _).trans
          (congrArg₂ (· * ·) (hn.pull e e₀ f₁ e₃ hJ) (hn.pull e e₁ e₂ e₃ hJ))).symm)
      refine (DVR.prod_sum₂ (K := thK) (K' := thK) (U := V) _ (prod_cub (x4 A 0) (x4 A 1 * x4 A 2) (x4 A 3) k)
        (prod_cub (x4 A 1) (x4 A 2) (x4 A 3) k)).trans (Eq.trans ?_
        (DVR.prod_sum₂ (K := thK) (K' := thK) (U := V) _ (prod_cub (x4 A 0 * x4 A 1) (x4 A 2) (x4 A 3) k)
        (prod_cub (x4 A 0) (x4 A 1) (x4 A 3) k)).symm)
      apply Additive.ofMul.injective
      simp only [_root_.mul_assoc (x4 A 0), ofMul_mul, ofMul_inv]
      abel }

theorem exists_gen_of_lbIso {Z : Scheme.{0}} (L : LB Z) (f : Z ⟶ Z) (h : LBIso L (L.pull f)) :
    ∃ s : LB.Gen (LB.LinComb L (K := Fin 2) ![f, 𝟙 Z] ![1, -1]), s.IsGen := by
  obtain ⟨w, hw⟩ := h
  refine gen_chartPull (A := (L.pull f).div L) (h := 𝟙 Z)
    { idx := fun j => (fun _ => j 0, j 1)
      le := fun j y hy => ?_
      g := fun y j j' hj hj' => ?_ } w hw
  · have h0 : f y ∈ L.U (j 0) := Set.mem_iInter.1 hy 0
    have h1 : y ∈ L.U (j 1) := Set.mem_iInter.1 hy 1
    exact ⟨mem_pull.2 h0, h1⟩
  · have a0 : f y ∈ L.U (j 0) := Set.mem_iInter.1 hj 0
    have a1 : y ∈ L.U (j 1) := Set.mem_iInter.1 hj 1
    have b0 : f y ∈ L.U (j' 0) := Set.mem_iInter.1 hj' 0
    have b1 : y ∈ L.U (j' 1) := Set.mem_iInter.1 hj' 1
    refine (gm_linComb L _ _ (𝟙 Z) y j j' hj hj').trans ?_
    refine Eq.trans ?_ (gm_div L (L.pull f) (𝟙 Z) y _ _ ⟨⟨mem_pull.2 a0, a1⟩, mem_pull.2 b0, b1⟩).symm
    rw [gm_pull_g L f (𝟙 Z) y _ _ (mem_pull.2 a0) (mem_pull.2 b0)]
    simp [Fin.prod_univ_two]

theorem cubical_and_symmetric : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (L : RigLB G), IsSemiAbelian G → (IsReduced X ∧ genericPoints X ⊆ abLocus G) → ((∃ t : (Theta G L.L).Gen, t.IsGen) → Nonempty (CubicalStr G L)) ∧ (LBIso L.L (L.L.pull (GrpObj.inv (X := G)).left) → L.IsSymmetric) := by
  intro X G _ _ L hsa hrg
  obtain ⟨hr, hab⟩ := hrg
  have hsm : Smooth G.hom := hsa.smooth
  have hgc : GeometricallyConnected G.hom := hsa.geomConnected
  have hgi : GeometricallyIntegral G.hom := GlobalTheory.grpObj_geometricallyIntegral_of_smooth X G
  refine ⟨fun ⟨t, ht⟩ => ?_, fun hiso => ?_⟩
  · obtain ⟨t', ht', hn⟩ := exists_normalised L.isLB t ht
    obtain ⟨sm2, gi2, ab2⟩ := GlobalTheory.smooth_geometricallyIntegral_abLocus_tensorObj X G G hsm hsm hgi hgi
    obtain ⟨sm3, gi3, ab3⟩ := GlobalTheory.smooth_geometricallyIntegral_abLocus_tensorObj X G (G ⊗ G) hsm sm2 hgi gi2
    obtain ⟨sm4, gi4, ab4⟩ := GlobalTheory.smooth_geometricallyIntegral_abLocus_tensorObj X G (G ⊗ G ⊗ G) hsm sm3 hgi gi3
    have g2 : genericPoints X ⊆ abLocus (G ⊗ G) := fun x hx => ab2 ⟨hab hx, hab hx⟩
    have g3 : genericPoints X ⊆ abLocus (G ⊗ G ⊗ G) := fun x hx => ab3 ⟨hab hx, g2 hx⟩
    have g4 : genericPoints X ⊆ abLocus (G ⊗ G ⊗ G ⊗ G) := fun x hx => ab4 ⟨hab hx, g3 hx⟩
    exact ⟨cubicalOfNormalised (surjective_appTop (G ⊗ G) (lift 1 1) sm2 gi2 hr g2)
      (surjective_appTop (G ⊗ G ⊗ G) (lift 1 (lift 1 1)) sm3 gi3 hr g3)
      (surjective_appTop (G ⊗ G ⊗ G ⊗ G) (lift 1 (lift 1 (lift 1 1))) sm4 gi4 hr g4) L t' ht' hn⟩
  · exact GlobalTheory.PrimNorm.isSymmetric_of_hasGen L (exists_gen_of_lbIso L.L _ hiso)

end GlobalTheory.CubeGen
