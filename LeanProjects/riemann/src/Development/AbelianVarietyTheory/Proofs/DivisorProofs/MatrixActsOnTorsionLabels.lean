import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianHomExtensionHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationEndomorphismOfAdmissibleBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleAdjointOfGenericAdjointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndomorphismMovesTorsionLatticeByAdjointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerFormBundleMatricesAdjointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerEndomorphismLatticeAdjointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.Eq8.MatTors

theorem endU_exists (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hadm : AdmBase R (maximalIdeal R))
    (D : DegData R (maximalIdeal R)) (P : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (hG : IsSemiAbelian G) (U : Unif (maximalIdeal R) D P G) (aA : P.A ⟶ P.A) (haA : IsMonHom aA) :
    ∃ E : GlobalTheory.UT.EndU U.toUnifPre, E.aA = aA := by
  haveI := hadm.1
  haveI := hadm.2.2.1
  have := U.gen_hom
  have hinv : IsMonHom U.gen.inv := inferInstance
  obtain ⟨F, ⟨hF, hF'⟩, -⟩ := GlobalTheory.Published.SemiAbelianHomExtension.fractionField GlobalTheory.semiAbelianHomExtension_holds R
    (FractionRing R) G G hG hG (U.gen.hom ≫ aA ≫ U.gen.inv)
  obtain ⟨E, -, hE⟩ := GlobalTheory.UT.exists_degenerationEndomorphism_of_admissibleBase R (maximalIdeal R) hadm D P G hG U F aA hF haA
    (by rw [hF']; simp)
  exact ⟨E, hE⟩

theorem isMonHom_matrix (S : Scheme.{0}) (X Y : Over S) [GrpObj X] [GrpObj Y] [IsCommMonObj Y] (pr : Fin 8 → (X ⟶ Y))
    (hpr : ∀ a, IsMonHom (pr a))
    (hu : ∀ (T' : Over S) (y' : Fin 8 → (T' ⟶ Y)), ∃! x : T' ⟶ X, ∀ a, x ≫ pr a = y' a) (f : X ⟶ X)
    (a : Matrix (Fin 8) (Fin 8) ℤ) (hf : ∀ u, f ≫ pr u = (List.ofFn fun v => pr v ^ a u v).prod) : IsMonHom f := by
  haveI : ∀ v, IsMonHom (pr v) := hpr
  refine ReciprocityTheory.ChartRestriction.G.Geo.Tor.isMonHom_of_mul f fun T x y => ?_
  have hz : ∀ (z : T ⟶ X) (u : Fin 8), z ≫ f ≫ pr u = ∏ v, (z ≫ pr v) ^ a u v := by
    intro z u
    let φz : (X ⟶ Y) →* (T ⟶ Y) := ⟨⟨(z ≫ ·), MonObj.comp_one z⟩, MonObj.comp_mul z⟩
    rw [hf u, List.prod_ofFn]
    exact (map_prod φz _ _).trans (Finset.prod_congr rfl fun v _ => map_zpow φz _ _)
  refine (hu T fun u => ((x * y) ≫ f) ≫ pr u).unique (fun u => rfl) (fun u => ?_)
  rw [MonObj.mul_comp, Category.assoc, Category.assoc, Category.assoc, hz, hz, hz]
  simp only [MonObj.mul_comp, mul_zpow, Finset.prod_mul_distrib]

theorem exists_adjoint (S a : Matrix (Fin 8) (Fin 8) ℤ) (hS : S.det = 1) : ∃ a', S * a' = a.transpose * S :=
  ⟨S⁻¹ * (a.transpose * S), Matrix.mul_nonsing_inv_cancel_left S _ (hS ▸ isUnit_one)⟩

theorem matrix_acts_on_torsion_labels : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → IsDiscreteValuationRing R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (pr : Fin 8 → (A'.A ⟶ A.A)), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing R))) (y : Fin 8 → (T' ⟶ A.A)), ∃! z : T' ⟶ A'.A, ∀ a, z ≫ pr a = y a) → LBIso A'.L (LB.LinComb (abelian₂ A.A A.L) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (pG : Fin 8 → (G' ⟶ G)), (∀ v, IsMonHom (pG v)) → (∀ v, (Over.pullback (jK R)).map (pG v) ≫ U.gen.hom = U'.gen.hom ≫ pr v) → ∀ (c : Fin 8 → (D.toPre.X →+ D'.toPre.X)), (∀ v, TorMatch U U' (RingHom.id R) (pG v).left (c v)) → ∀ e : D'.toPre.X ≃+ (Fin 8 → D.toPre.X), (∀ y, ∑ v, c v (∑ u, (W + W.transpose) v u • e y u) = y) → ∀ (a : Matrix (Fin 8) (Fin 8) ℤ) (f : A'.A ⟶ A'.A), (∀ u, f ≫ pr u = (List.ofFn fun v => pr v ^ a u v).prod) → ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing R) K] (m : ℕ) (pk pk' : QkPt D'.toPre K m) (x : TFK (R := R) K ⟶ A'.A), 1 ≤ m → QkToAkU U'.toUnifPre K m pk x → QkToAkU U'.toUnifPre K m pk' (x ≫ f) → CongMod m (e pk'.y) (fun u => ∑ v, a u v • e pk.y v) := by
  intro R _ _ _ hB hdvr G _ _ hG D A U G' _ _ hG' D' A' U' W hW pr hpr hpu hL pG hpG hext c hc e he a f hf K _ _ _ m pk pk' x
    hm hx hx'
  obtain ⟨a', ha⟩ := exists_adjoint (W + W.transpose) a hW.2
  obtain ⟨f', hf', -⟩ := hpu A'.A (fun u => (List.ofFn fun v => pr v ^ a' u v).prod)
  obtain ⟨E, hE⟩ := endU_exists R hB.1 D' A' G' hG' U' f (isMonHom_matrix _ A'.A A.A pr hpr hpu f a hf)
  obtain ⟨E', hE'⟩ := endU_exists R hB.1 D' A' G' hG' U' f' (isMonHom_matrix _ A'.A A.A pr hpr hpu f' a' hf')
  subst hE hE'
  have h₁ := GlobalTheory.T.eighthPower_formBundle_matrices_adjoint _ A A' W pr hpr hL a a' ha E.aA E'.aA hf hf'
  have h₂ := GlobalTheory.T.mumfordBundle_adjoint_of_generic_adjoint R hB G' hG' D' A' U' E E' h₁
  obtain ⟨w, hw⟩ := GlobalTheory.T.endomorphism_moves_torsionLattice_by_adjoint R hB G' hG' D' A' U' E E' h₂ K m pk pk' x hm hx hx'
  have h₃ := GlobalTheory.T.eighth_power_endomorphism_lattice_adjoint R hB hdvr G hG D A U G' hG' D' A' U' W hW pr hpr hpu hL pG hpG hext c hc e he a a' ha E' hf' pk.y
  exact ⟨e w, by rw [hw, map_add, map_nsmul, h₃]⟩

end GlobalTheory.Poinc.Eq8.MatTors
