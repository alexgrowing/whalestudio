import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

section BoxValues

variable {X Y Z : Scheme.{0}}

private theorem gm_inv' {Y Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : r z ∈ U) (a : Γ(Y, U)ˣ) :
    gm r z U a⁻¹ = (gm r z U a)⁻¹ := by
  unfold gm
  rw [dif_pos h]
  exact map_inv _ a

private theorem gm_res' {Y Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {U V : Y.Opens} (hle : V ≤ U) (h : r z ∈ V)
    (a : Γ(Y, U)ˣ) : gm r z V (res hle a) = gm r z U a := by
  ext
  rw [← gs_unit r z V h, ← gs_unit r z U (hle h)]
  exact gs_res r z hle h a.val

theorem gs_secOfIso_eq {A B : LB Y} (u : LB.Iso A B) (t : LB.Sec B) (hu : u.IsGen) (hA : A.IsLB) (hB : B.IsLB)
    (a : A.ι) (b : B.ι) (r : Z ⟶ Y) (z : Z) (hz : r z ∈ A.U a ⊓ B.U b) :
    gs r z (A.U a) ((secOfIso t hu hA hB).f a) =
      ((gm r z ((LB.div B A).U (b, a)) (u.s (b, a)))⁻¹).val * gs r z (B.U b) (t.f b) := by
  have hD : r z ∈ (LB.div B A).U (b, a) := divLe a b hz
  rw [← gs_res r z (inf_le_left : A.U a ⊓ B.U b ≤ A.U a) hz]
  change gs r z _ (rs inf_le_left ((secOfIso t hu hA hB).f a)) = _
  rw [secOfIso_spec t hu hA hB a b, isoCand, gs_mul r z _ hz, gs_unit r z _ hz, gm_inv' r z _ hz,
    gm_res' r z (divLe a b) hz]
  congr 1
  exact gs_res r z inf_le_right hz (t.f b)

theorem gs_boxSecGen_eq {X' Y' : Scheme.{0}} (L : LB X) {j : ℕ} (pr : Fin j → (X' ⟶ X)) {K : Type} [Fintype K]
    (φ' : K → (Y' ⟶ X')) (ε : K → ℤ) (p : Fin j → (Y' ⟶ Y)) (φ : Fin j → K → (Y ⟶ X))
    (hφ : ∀ i a, φ' a ≫ pr i = p i ≫ φ i a) (σ : ∀ i, LB.Sec (LB.LinComb L (φ i) ε))
    (jN : K → Fin j → L.ι) (r : Z ⟶ Y') (z : Z) (hz : r z ∈ LB.wchart (LB.LinComb L pr (fun _ => 1)) φ' jN) :
    gs r z _ ((boxSecGen L pr φ' ε p φ hφ σ).f jN) =
      ∏ i, gs (r ≫ p i) z (LB.wchart L (φ i) (fun a => jN a i)) ((σ i).f (fun a => jN a i)) := by
  change gs r z _ (boxSecGenF L pr φ' ε p φ hφ σ jN) = _
  rw [boxSecGenF, gs_prod r z _ hz]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [gs_res r z _ hz]
  exact gs_pull r (p i) z _ (box_le_of_comp L pr φ' (φ i) (p i) i (hφ i) jN hz) _

theorem exists_boxSec_val {X' Y' : Scheme.{0}} {M : LB X} {M' : LB X'} (hM : M.IsLB) (hM' : M'.IsLB) {j : ℕ}
    {pr : Fin j → (X' ⟶ X)} (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) (hw : w.IsGen) {K : Type} [Fintype K]
    (φ' : K → (Y' ⟶ X')) (ε : K → ℤ) (p : Fin j → (Y' ⟶ Y)) (φ : Fin j → K → (Y ⟶ X))
    (hφ : ∀ i a, φ' a ≫ pr i = p i ≫ φ i a) (σ : ∀ i, LB.Sec (LB.LinComb M (φ i) ε)) :
    ∃ σ' : LB.Sec (LB.LinComb M' φ' ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J J'), Good M z J → Good M' z J' →
      (∏ a, bw w (r ≫ φ' a) z (fun i => J ((r ≫ φ' a) ≫ pr i)) (J' (r ≫ φ' a)) ^ ε a).val * sval σ' r z J' =
        ∏ i, sval (σ i) (r ≫ p i) z J := by
  refine ⟨secOfIso (u := LB.linCombIso w φ' ε) (boxSecGen M pr φ' ε p φ hφ σ) (linCombIso_isGen w hw φ' ε)
    (linComb_isLB M' hM' φ' ε) (linComb_isLB _ (linComb_isLB M hM pr _) φ' ε), ?_⟩
  intro Z r z J J' hJ hJ'
  have hA : r z ∈ LB.wchart M' φ' (fun a => J' (r ≫ φ' a)) := Good.mem hJ' φ' r
  have hB : r z ∈ LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' (fun a i => J ((r ≫ φ' a) ≫ pr i)) :=
    Set.mem_iInter.2 fun a => Good.mem hJ pr (r ≫ φ' a)
  have h1 := gs_secOfIso_eq (LB.linCombIso w φ' ε) (boxSecGen M pr φ' ε p φ hφ σ) (linCombIso_isGen w hw φ' ε)
    (linComb_isLB M' hM' φ' ε) (linComb_isLB _ (linComb_isLB M hM pr _) φ' ε) (fun a => J' (r ≫ φ' a))
    (fun a i => J ((r ≫ φ' a) ≫ pr i)) r z ⟨hA, hB⟩
  have h2 := gs_boxSecGen_eq M pr φ' ε p φ hφ σ (fun a i => J ((r ≫ φ' a) ≫ pr i)) r z hB
  have h3 := gm_linCombIso w φ' ε r z (fun a i => J ((r ≫ φ' a) ≫ pr i)) (fun a => J' (r ≫ φ' a)) ⟨hB, hA⟩
  rw [sval_of _ r z J' (fun a => J' (r ≫ φ' a)) (fun _ => rfl)]
  erw [h1, h3, h2, Units.mul_inv_cancel_left]
  refine Finset.prod_congr rfl (fun i _ => (sval_of (σ i) (r ≫ p i) z J _ (fun a => ?_)).symm)
  rw [Category.assoc, Category.assoc, hφ]

end BoxValues

theorem exists_boxSec_pow_ext : ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (pA : IsPowPolAV A' A j) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (t : Fin j → LB.Sec (LB.LinComb A.L (K := Fin 1) (fun _ => (snd (TFK (R := R) F) A.A).left) (fun _ => (k : ℤ)))), ∃ t' : LB.Sec (LB.LinComb A'.L (K := Fin 1) (fun _ => (snd (TFK (R := R) F) A'.A).left) (fun _ => (k : ℤ))), (∀ (Z : Scheme.{0}) (r : Z ⟶ ((TFK (R := R) F) ⊗ A'.A).left) (z : Z) (J J'), Geo.Tor.Good A.L z J → Geo.Tor.Good A'.L z J' → (bw pA.w (r ≫ (snd (TFK (R := R) F) A'.A).left) z (fun i => J ((r ≫ (snd (TFK (R := R) F) A'.A).left) ≫ (pA.pr i).left)) (J' (r ≫ (snd (TFK (R := R) F) A'.A).left)) ^ k).val * Geo.Tor.sval t' r z J' = ∏ i, Geo.Tor.sval (t i) (r ≫ ((TFK (R := R) F) ◁ pA.pr i).left) z J) := by
  intro R _ _ j A A' pA F _ _ k t
  have hφ : ∀ (i : Fin j) (_ : Fin 1), (snd (TFK (R := R) F) A'.A).left ≫ (pA.pr i).left =
      ((TFK (R := R) F) ◁ pA.pr i).left ≫ (snd (TFK (R := R) F) A.A).left := fun i _ => by
    rw [← Over.comp_left, ← Over.comp_left, whiskerLeft_snd]
  obtain ⟨t', ht'⟩ := exists_boxSec_val A.isLB A'.isLB pA.w pA.w_gen
    (fun _ : Fin 1 => (snd (TFK (R := R) F) A'.A).left) (fun _ => (k : ℤ))
    (fun i => ((TFK (R := R) F) ◁ pA.pr i).left) (fun _ _ => (snd (TFK (R := R) F) A.A).left) hφ t
  refine ⟨t', fun Z r z J J' hJ hJ' => ?_⟩
  have h := ht' Z r z J J' hJ hJ'
  rw [Fin.prod_univ_one, zpow_natCast] at h
  exact h

end GlobalTheory
