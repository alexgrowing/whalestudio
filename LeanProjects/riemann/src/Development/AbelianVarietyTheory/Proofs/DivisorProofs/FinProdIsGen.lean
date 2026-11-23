import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomOfMulComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.XValuePf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.MumSide

section Helpers
variable {X Y : Scheme.{0}} {L : LB X}

theorem exists_zpow (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (n : ℤ) :
    ∃ t' : LB.Gen (LB.LinComb L φ (fun k => n * ε k)), t'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → val t' r z J = val t r z J ^ n := by
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · exact ⟨GeneratorPullback.powGen L φ ε t m, DVR.powGen_isGen _ _ _ _ ht m,
      fun Z r z J _ => (DVR.val_pow t m r z J).trans (zpow_natCast _ _).symm⟩
  · obtain ⟨t', ht', hv⟩ := exists_gen hL (φ' := φ) (ε' := fun k => -(m : ℤ) * ε k) (fun U _ h => by
        refine Finset.prod_congr rfl fun k _ => ?_
        show _ = h (φ k) ^ (-(m : ℤ) * ε k)
        rw [neg_mul]) (LB.invGen L _ _ (GeneratorPullback.powGen L φ ε t m))
        (DVR.invGen_isGen _ _ _ _ (DVR.powGen_isGen _ _ _ _ ht m))
    refine ⟨t', ht', fun Z r z J hJ => ?_⟩
    rw [hv Z r z J hJ, val_inv, DVR.val_pow, zpow_neg, zpow_natCast]

theorem finProd_isGen {I K : Type} [Fintype I] [Fintype K] (φ : I → K → (Y ⟶ X)) (ε : I → K → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb L (φ i) (ε i))) (ht : ∀ i, (t i).IsGen) : (GeneratorPullback.finProdGen L φ ε t).IsGen := by
  intro (j : I × K → L.ι) (j' : I × K → L.ι)
  refine unit_ext fun y hy => ?_
  have v : ∀ j : I × K → L.ι, y ∈ LB.wchart L (fun p : I × K => φ p.1 p.2) j →
      gm (𝟙 Y) y (LB.wchart L (fun p : I × K => φ p.1 p.2) j) ((GeneratorPullback.finProdGen L φ ε t).s j) =
        ∏ i, gm (𝟙 Y) y (LB.wchart L (φ i) (fun k => j (i, k))) ((t i).s (fun k => j (i, k))) := fun j hj =>
    (map_prod _ _ _).trans (Finset.prod_congr rfl fun _ _ => gm_res (𝟙 Y) y _ hj _)
  refine ((gm_res (𝟙 Y) y _ hy _).trans (v j hy.1)).trans (Eq.trans ?_ ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gm_linComb L _ _ (𝟙 Y) y j j' hy.1 hy.2) ((gm_res (𝟙 Y) y _ hy _).trans (v j' hy.2)))).symm)
  rw [Fintype.prod_prod_type, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => gen_trans (ht i) (𝟙 Y) y
    (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.1 (i, k)) (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.2 (i, k))

theorem val_finProd {I K : Type} [Fintype I] [Fintype K] (φ : I → K → (Y ⟶ X)) (ε : I → K → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb L (φ i) (ε i))) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    val (GeneratorPullback.finProdGen L φ ε t) r z J = ∏ i, val (t i) r z J :=
  (map_prod _ _ _).trans (Finset.prod_congr rfl fun i _ =>
    gm_res r z _ (hJ.mem (fun p : I × K => φ p.1 p.2) r) _)

end Helpers

section Rows
variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}

theorem comp_tensφ' {S : Scheme.{0}} {B B' T : Over S} [GrpObj B] (pr : Fin r → (B' ⟶ B)) (x : T ⟶ B')
    (k : (Fin r × Fin r) × Fin 4) : x.left ≫ tensφ pr k = GlobalTheory.PolDeg.lamPts (x ≫ pr k.1.1) (x ≫ pr k.1.2) k.2 := by
  obtain ⟨⟨i, j⟩, k⟩ := k
  fin_cases k
  · exact congrArg (·.left) (MonObj.comp_mul x (pr i) (pr j))
  · rfl
  · rfl
  · exact congrArg (·.left) (MonObj.comp_one (M := B) x)

theorem matAct_zero (T : Tens D D' W) : GlobalTheory.TensAct.matAct T 0 = 1 := by
  have h := GlobalTheory.TensAct.matAct_add T 0 0
  rw [add_zero] at h
  exact mul_eq_left.1 h.symm

theorem four_eq (T : Tens D D' W) (A : Matrix (Fin r) (Fin r) ℤ) (f : D'.P.A ⟶ D'.P.A)
    (hf : f = GlobalTheory.TensAct.matAct T A) (a : Fin 4) :
    (![(padd D'.P.A (𝟙 _) f).left, 𝟙 D'.P.A.left, f.left, (toUnit D'.P.A ≫ η[D'.P.A]).left] :
      Fin 4 → (D'.P.A.left ⟶ D'.P.A.left)) a =
      (GlobalTheory.TensAct.matAct T ((![1 + A, 1, A, 0] : Fin 4 → Matrix (Fin r) (Fin r) ℤ) a)).left := by
  subst hf
  fin_cases a
  · show (padd D'.P.A (𝟙 _) _).left = (GlobalTheory.TensAct.matAct T (1 + A)).left
    rw [GlobalTheory.TensAct.matAct_add, GlobalTheory.TensAct.matAct_one]; rfl
  · show 𝟙 D'.P.A.left = (GlobalTheory.TensAct.matAct T 1).left
    rw [GlobalTheory.TensAct.matAct_one]; rfl
  · rfl
  · show (toUnit D'.P.A ≫ η[D'.P.A]).left = (GlobalTheory.TensAct.matAct T 0).left
    rw [matAct_zero]; rfl

theorem sum_one_smul {X : Type} [AddCommGroup X] (v : Fin r → X) (i : Fin r) :
    ∑ k, (1 : Matrix (Fin r) (Fin r) ℤ) i k • v k = v i := by
  rw [Finset.sum_eq_single i]
  · rw [Matrix.one_apply_eq, one_smul]
  · intro l _ hl
    rw [Matrix.one_apply_ne hl.symm, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem xe_four (T : Tens D D' W) (A : Matrix (Fin r) (Fin r) ℤ) (y : D'.X) (a : Fin 4) (i : Fin r) :
    T.xe ((![y + GlobalTheory.TensAct.latAct T A y, y, GlobalTheory.TensAct.latAct T A y, 0] : Fin 4 → D'.X) a) i =
      ∑ k, (![1 + A, 1, A, 0] : Fin 4 → Matrix (Fin r) (Fin r) ℤ) a i k • T.xe y k := by
  fin_cases a
  · show T.xe (y + GlobalTheory.TensAct.latAct T A y) i = ∑ k, (1 + A) i k • T.xe y k
    rw [map_add, Pi.add_apply, GlobalTheory.TensAct.xe_latAct]
    simp only [Matrix.add_apply, add_smul, Finset.sum_add_distrib, sum_one_smul]
  · show T.xe y i = ∑ k, (1 : Matrix (Fin r) (Fin r) ℤ) i k • T.xe y k
    rw [sum_one_smul]
  · show T.xe (GlobalTheory.TensAct.latAct T A y) i = ∑ k, A i k • T.xe y k
    rw [GlobalTheory.TensAct.xe_latAct]
  · show T.xe 0 i = ∑ k, (0 : Matrix (Fin r) (Fin r) ℤ) i k • T.xe y k
    simp only [map_zero, Pi.zero_apply, Matrix.zero_apply, zero_smul, Finset.sum_const_zero]

end Rows

end GlobalTheory.MumSide
