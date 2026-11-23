import Mathlib
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.EFam
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.IsSeparatedOfProj
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.IsIntegralRBIff
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR GlobalTheory.PD KaehlerDifferential GlobalTheory.W1 GlobalTheory.WH

theorem UpperTheory.etaleCorrespondence_differentials_statement :
    ∀ (d : ℕ) (Z Y : Scheme.{0}) [IsIntegral Z] [IsIntegral Y] (s : Z ⟶ Sp ℂ) (s' : Y ⟶ Sp ℂ) [SmoothOfRelativeDimension d s] [SmoothOfRelativeDimension d s'] (hP : IsProjOver s) (c1 c2 : Y ⟶ Z) (h1 : c1 ≫ s = s') (h2 : c2 ≫ s = s') [IsFinite c1] [Etale c1] [IsFinite c2] [Etale c2] [instK : Algebra ℂ Z.functionField] [instL : Algebra ℂ Y.functionField] (hK : instK = ffAlg s) (hL : instL = ffAlg s') [Algebra Z.functionField Y.functionField] [IsScalarTower ℂ Z.functionField Y.functionField] (g1 : ∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c1 ⁻¹ᵁ V) (g : Γ(Z, V)), (Y.presheaf.germ (c1 ⁻¹ᵁ V) (genericPoint Y) hV').hom ((c1.app V).hom g) = algebraMap Z.functionField Y.functionField ((Z.presheaf.germ V (genericPoint Z) hV).hom g)) (j2 : Z.functionField →ₐ[ℂ] Y.functionField) (g2 : ∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c2 ⁻¹ᵁ V) (g : Γ(Z, V)), j2 ((Z.presheaf.germ V (genericPoint Z) hV).hom g) = (Y.presheaf.germ (c2 ⁻¹ᵁ V) (genericPoint Y) hV').hom (c2.app V g)) (F : Type) [Field F] [Algebra ℂ F] [Algebra F Z.functionField] [Algebra F Y.functionField] [IsScalarTower ℂ F Z.functionField] [IsScalarTower F Z.functionField Y.functionField] [IsScalarTower ℂ F Y.functionField] (x : Fin (d + 1) → F) (U : Fin (d + 1) → Z.Opens) (hx : IsFinCover ℂ Z.functionField x) (hU : IsAffCover s U (rB ℂ Z.functionField x)) (l : Fin d) (hg : genericPoint Y ∈ c1 ⁻¹ᵁ U l.succ) (hg0 : genericPoint Y ∈ c1 ⁻¹ᵁ U 0) (e : rB ℂ Y.functionField x {l.succ} →ₐ[ℂ] ℂ) (e0 : rB ℂ Y.functionField x {0} →ₐ[ℂ] ℂ) (y : CxPts s' (RingHom.id ℂ)), UpperTheory.A.Mt s' (c1 ⁻¹ᵁ U l.succ) hg _ e y → UpperTheory.A.Mt s' (c1 ⁻¹ᵁ U 0) hg0 _ e0 y → e0 ⟨_, tco_mem ℂ Y.functionField x l⟩ ≠ 0 := by
  intro d Z Y _ _ s s' _ _ hP c1 c2 h1 h2 _ _ _ _ instK instL hK hL _ _ g1 j2 g2 F _ _ _ _ _ _ _ x U hx hU l hg hg0 e e0 y hM hM0
  have mem : ∀ (I : Finset (Fin (d + 1))) (i j : Fin (d + 1)), i ∈ I →
      algebraMap F Y.functionField (x j / x i) ∈ rB ℂ Y.functionField x I := fun I i j hi =>
    (integralClosure (rA ℂ x I) Y.functionField).algebraMap_mem
      ⟨x j / x i, Algebra.subset_adjoin ⟨i, hi, j, rfl⟩⟩
  obtain ⟨f0, hf0⟩ := (UpperTheory.A.mem_rB_pull h1 hK hL g1 hU {0} ⟨0, by simp⟩ (c1 ⁻¹ᵁ U 0) (by simp) hg0 _).1
    (tco_mem ℂ Y.functionField x l)
  have hV : genericPoint Y ∈ c1 ⁻¹ᵁ U 0 ⊓ c1 ⁻¹ᵁ U l.succ := ⟨hg0, hg⟩
  obtain ⟨fb, hfb⟩ := (UpperTheory.A.mem_rB_pull h1 hK hL g1 hU {0, l.succ} ⟨0, by simp⟩
    (c1 ⁻¹ᵁ U 0 ⊓ c1 ⁻¹ᵁ U l.succ) (by simp) hV _).1 (mem _ l.succ 0 (by simp))
  have hres : (Y.presheaf.germ _ (genericPoint Y) hV).hom (resG Y inf_le_left f0) =
      algebraMap F Y.functionField (x l.succ / x 0) := by
    rw [← hf0]
    exact Y.presheaf.germ_res_apply (homOfLE inf_le_left) (genericPoint Y) hV f0
  have hne := hx.pd.ne
  have hunit : resG Y inf_le_left f0 * fb = 1 := by
    apply germ_injective_of_isIntegral Y (genericPoint Y) hV
    rw [map_mul, map_one, hres, hfb, ← map_mul, div_mul_div_comm, mul_comm (x l.succ), div_self (mul_ne_zero (hne _) (hne _)), map_one]
  have hy : y ∈ CxPts.ptsIn s' (RingHom.id ℂ) (c1 ⁻¹ᵁ U 0 ⊓ c1 ⁻¹ᵁ U l.succ) :=
    CxPts.mem_ptsIn_inf.2 ⟨hM0.1, hM.1⟩
  have hval := hM0.2 f0 (hf0 ▸ tco_mem ℂ Y.functionField x l)
  have h3 : e0 ⟨_, tco_mem ℂ Y.functionField x l⟩ = CxPts.ev s' (RingHom.id ℂ) _ f0 y := by
    rw [← hval]; congr 2; exact hf0.symm
  rw [h3, ← CxPts.ev_res inf_le_left hy f0]
  exact CxPts.ev_ne_zero hy (IsUnit.of_mul_eq_one _ hunit)
