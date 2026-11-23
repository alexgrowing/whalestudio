import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedEighthPowerEndomorphismActsByIntMatri
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationEndomorphismClosedFibreTorusCharac
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterMapOfIntegralMatrixActionStatement
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.E8Endomorphism

open GlobalTheory.Poinc.Sep.EndCompat

theorem lattice_of_charMap {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (S a a' : Matrix (Fin 8) (Fin 8) ℤ)
    (hS : S.transpose = S) (hSa : S * a' = a.transpose * S) (c : Fin 8 → (X →+ Y)) (e : Y ≃+ (Fin 8 → X))
    (hT : ∀ y, ∑ v, c v (∑ u, S v u • e y u) = y) (h : Y →+ Y) (hh : ∀ u χ, h (c u χ) = ∑ v, a' u v • c v χ)
    (y : Y) : e (h y) = fun u => ∑ v, a u v • e y v := by
  have hM' : a'.transpose * S = S * a := by
    have := congrArg Matrix.transpose hSa
    rwa [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hS] at this
  have hM : ∀ w u, ∑ v, a' v w * S v u = ∑ x, S w x * a x u := fun w u => by
    have := congrFun (congrFun hM' w) u
    simpa [Matrix.mul_apply] using this
  have key : ∀ x : Fin 8 → X, ∑ v, c v (∑ u, S v u • x u) = e.symm x := by
    intro x
    conv_rhs => rw [← hT (e.symm x)]
    simp
  apply e.symm.injective
  rw [AddEquiv.symm_apply_apply, ← key]
  conv_lhs => rw [← hT y]
  simp only [map_sum, map_zsmul, hh, Finset.smul_sum, smul_smul]
  have L : ∀ f : Fin 8 → Fin 8 → Fin 8 → Y, ∑ v, ∑ u, ∑ w, f v u w = ∑ w, ∑ u, ∑ v, f v u w := fun f => by
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl fun u _ => Finset.sum_comm]
    rw [Finset.sum_comm]
  calc ∑ v, ∑ u, ∑ w, (S v u * a' v w) • c w (e y u)
      = ∑ w, ∑ u, ∑ v, (S v u * a' v w) • c w (e y u) := L (fun v u w => (S v u * a' v w) • c w (e y u))
    _ = ∑ w, ∑ u, (∑ v, a' v w * S v u) • c w (e y u) := by
        refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.sum_smul]
        exact Finset.sum_congr rfl fun v _ => by rw [mul_comm]
    _ = ∑ w, ∑ u, (∑ x, S w x * a x u) • c w (e y u) := by simp only [hM]
    _ = ∑ w, ∑ x, ∑ u, (S w x * a x u) • c w (e y u) := by
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun u _ => Finset.sum_smul

theorem endU_lattice_adjoint : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → IsDiscreteValuationRing R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (pr : Fin 8 → (A'.A ⟶ A.A)), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing R))) (y : Fin 8 → (T' ⟶ A.A)), ∃! z : T' ⟶ A'.A, ∀ a, z ≫ pr a = y a) → LBIso A'.L (LB.LinComb (abelian₂ A.A A.L) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (pG : Fin 8 → (G' ⟶ G)), (∀ v, IsMonHom (pG v)) → (∀ v, (Over.pullback (jK R)).map (pG v) ≫ U.gen.hom = U'.gen.hom ≫ pr v) → ∀ (c : Fin 8 → (D.toPre.X →+ D'.toPre.X)), (∀ v, TorMatch U U' (RingHom.id R) (pG v).left (c v)) → ∀ e : D'.toPre.X ≃+ (Fin 8 → D.toPre.X), (∀ y, ∑ v, c v (∑ u, (W + W.transpose) v u • e y u) = y) → ∀ (a a' : Matrix (Fin 8) (Fin 8) ℤ), (W + W.transpose) * a' = a.transpose * (W + W.transpose) → ∀ E' : GlobalTheory.UT.EndU U'.toUnifPre, (∀ u, E'.aA ≫ pr u = (List.ofFn fun v => pr v ^ a' u v).prod) → ∀ y, e (E'.h y) = fun u => ∑ v, a u v • e y v := by
  intro R _ _ _ hB hDVR G _ _ hG D A U G' _ _ hG' D' A' U' W hW pr hpr huniqA hL pG hpG hpGc c hc e he a a' haa' E' hE' y
  have hCN : GlobalTheory.TorRef.IsCN R := ⟨hB.1.1, hB.1.2.2.1, hB.1.2.2.2, hB.2⟩
  haveI : IsNoetherianRing R := hCN.1
  haveI : IsIntegrallyClosed R := hCN.2.1
  haveI := E'.homG
  haveI := U.gen_hom
  have hstep : ∀ u, E'.aG ≫ pG u = (List.ofFn fun v => pG v ^ a' u v).prod := by
    intro u
    haveI := hpG u
    have hR : IsMonHom (List.ofFn fun v => pG v ^ a' u v).prod := by
      refine isMonHom_of_mul _ fun T x z => ?_
      have key : ∀ w : T ⟶ G', w ≫ (List.ofFn fun v => pG v ^ a' u v).prod = ∏ v, (w ≫ pG v) ^ a' u v := fun w => by
        rw [← List.prod_ofFn]
        exact map_ofFn_prod (preH w) pG (a' u)
      rw [key, key, key, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun v _ => ?_
      haveI := hpG v
      rw [MonObj.mul_comp, mul_zpow]
    obtain ⟨F0, -, huniq⟩ := GlobalTheory.semiAbelianHomExtension_holds.fractionField R (FractionRing R) G' G hG' hG
      ((Over.pullback (jK R)).map (E'.aG ≫ pG u))
    refine (huniq _ ⟨inferInstance, rfl⟩).trans (huniq _ ⟨hR, ?_⟩).symm
    rw [← cancel_mono U.gen.hom]
    have e1 : (Over.pullback (jK R)).map (E'.aG ≫ pG u) ≫ U.gen.hom =
        U'.gen.hom ≫ (List.ofFn fun v => pr v ^ a' u v).prod := by
      rw [Functor.map_comp, Category.assoc, hpGc u, ← Category.assoc, E'.ext, Category.assoc, hE' u]
    rw [e1]
    calc (Over.pullback (jK R)).map (List.ofFn fun v => pG v ^ a' u v).prod ≫ U.gen.hom
        = ((postH U.gen.hom U.gen_hom).comp (pullH (jK R) G' G)) (List.ofFn fun v => pG v ^ a' u v).prod := rfl
      _ = (List.ofFn fun v => ((postH U.gen.hom U.gen_hom).comp (pullH (jK R) G' G)) (pG v) ^ a' u v).prod :=
          map_ofFn_prod _ pG (a' u)
      _ = (List.ofFn fun v => preH U'.gen.hom (pr v) ^ a' u v).prod :=
          congrArg (fun z : Fin 8 → _ => (List.ofFn fun v => z v ^ a' u v).prod) (funext hpGc)
      _ = preH U'.gen.hom (List.ofFn fun v => pr v ^ a' u v).prod := (map_ofFn_prod _ pr (a' u)).symm
      _ = U'.gen.hom ≫ (List.ofFn fun v => pr v ^ a' u v).prod := rfl
  have hEC := GlobalTheory.Poinc.Eq8.endChar_endU R hCN D' A' G' hG' U' E'
  have hh := GlobalTheory.T.characterMap_of_integral_matrix_action R hCN D A G hG U D' A' G' hG' U' pG hpG c hc a' E'.aG E'.h E'.homG hEC hstep
  exact lattice_of_charMap (W + W.transpose) a a' (by rw [Matrix.transpose_add, Matrix.transpose_transpose, add_comm])
    haa' c e he E'.h hh y

end GlobalTheory.Poinc.E8Endomorphism
