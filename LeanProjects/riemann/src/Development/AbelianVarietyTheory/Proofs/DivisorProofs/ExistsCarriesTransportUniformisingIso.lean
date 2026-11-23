import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.SecTransport

open TopologicalSpace Opposite

variable {X Y : Scheme.{0}} {L : LB X} {M : LB Y} {β : Y ⟶ X}

lemma le_pull (j : Fin 1 → L.ι) (i : M.ι) :
    LB.wchart L (fun _ : Fin 1 => β) j ⊓ M.U i ≤ (L.pull β).U (fun _ => j 0) ⊓ M.U i :=
  fun _ hy => ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy.1 0, hy.2⟩

lemma le_one (j : Fin 1 → L.ι) (i : M.ι) :
    LB.wchart L (fun _ : Fin 1 => β) j ⊓ M.U i ≤ LB.wchart M (fun _ : Fin 1 => 𝟙 Y) (fun _ => i) :=
  fun _ hy => Set.mem_iInter.2 fun _ => hy.2

def piece (ℓ : LB.Iso M (L.pull β)) (c : Γ(Y, ⊤)) (k : ℕ) (σ' : H0 M k) (j : Fin 1 → L.ι) (i : M.ι) :
    Γ(Y, LB.wchart L (fun _ : Fin 1 => β) j ⊓ M.U i) :=
  (Y.presheaf.map (homOfLE le_top).op).hom c * ((res (le_pull j i) (ℓ.s (fun _ => j 0, i))) ^ k).val *
    (Y.presheaf.map (homOfLE (le_one j i)).op).hom (σ'.f (fun _ => i))

theorem gs_piece (ℓ : LB.Iso M (L.pull β)) (c : Γ(Y, ⊤)) (k : ℕ) (σ' : H0 M k) (j : Fin 1 → L.ι) (i : M.ι)
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (hz : r z ∈ LB.wchart L (fun _ : Fin 1 => β) j ⊓ M.U i) :
    gs r z _ (piece ℓ c k σ' j i) = gs r z ⊤ c * (gw ℓ r z (j 0) i ^ k).val *
      gs r z (LB.wchart M (fun _ : Fin 1 => 𝟙 Y) (fun _ => i)) (σ'.f (fun _ => i)) := by
  exact (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) ((gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·)
    (gs_res r z le_top hz c) ((gs_unit r z _ hz _).trans (congrArg Units.val ((map_pow _ _ _).trans
      (congrArg (· ^ k) (gm_res r z (le_pull j i) hz _)))))))
    (gs_res r z (le_one j i) hz _))

theorem indep (hL : L.IsLB) (ℓ : LB.Iso M (L.pull β)) (hℓ : PGen ℓ) (k : ℕ) (σ' : H0 M k) {Z : Scheme.{0}}
    (r : Z ⟶ Y) (z : Z) (j₀ : L.ι) (i i' : M.ι) (hj : β (r z) ∈ L.U j₀) (hi : r z ∈ M.U i) (hi' : r z ∈ M.U i') :
    (gw ℓ r z j₀ i ^ k).val * gs r z (LB.wchart M (fun _ : Fin 1 => 𝟙 Y) (fun _ => i)) (σ'.f (fun _ => i)) =
      (gw ℓ r z j₀ i' ^ k).val * gs r z (LB.wchart M (fun _ : Fin 1 => 𝟙 Y) (fun _ => i')) (σ'.f (fun _ => i')) := by
  have e1 := hℓ Z r z j₀ j₀ i i' hj hj hi hi'
  rw [gm_self hL (r ≫ β) z hj, _root_.one_mul] at e1
  have hm : r z ∈ LB.wchart M (fun _ : Fin 1 => 𝟙 Y) (fun _ => i) := Set.mem_iInter.2 fun _ => hi
  have hm' : r z ∈ LB.wchart M (fun _ : Fin 1 => 𝟙 Y) (fun _ => i') := Set.mem_iInter.2 fun _ => hi'
  have e2 := sec_trans σ' r z hm hm'
  have e3 : trF (L := M) (fun _ : Fin 1 => 𝟙 Y) (fun _ => (k : ℤ)) r z (fun _ => i) (fun _ => i') =
      gm r z _ (M.g i i') ^ k := by
    simp only [trF, Fin.prod_univ_one, Category.comp_id, zpow_natCast]
  rw [e2, e3, ← _root_.mul_assoc, ← Units.val_mul, e1, mul_pow, inv_pow,
    _root_.mul_comm ((gm r z _ (M.g i i') ^ k)⁻¹), _root_.mul_assoc, _root_.inv_mul_cancel, _root_.mul_one]

theorem exists_transport (hL : L.IsLB) (hM : M.IsLB) (ℓ : LB.Iso M (L.pull β)) (hℓ : ℓ.IsGen) (c : Γ(Y, ⊤))
    (k : ℕ) (σ' : H0 M k) : ∃ σ : SecK L β k, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) J J', Good L z J → Good M z J' →
      sval σ r z J = gs r z ⊤ c * (gw ℓ r z (J (r ≫ β)) (J' r) ^ k).val * sval σ' r z J' := by
  have hP := (isGen_iff ℓ).1 hℓ
  have glue : ∀ j : Fin 1 → L.ι, ∃ a : Γ(Y, LB.wchart L (fun _ : Fin 1 => β) j), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z)
      (i : M.ι), r z ∈ LB.wchart L (fun _ : Fin 1 => β) j → r z ∈ M.U i →
      gs r z _ a = gs r z ⊤ c * (gw ℓ r z (j 0) i ^ k).val *
        gs r z (LB.wchart M (fun _ : Fin 1 => 𝟙 Y) (fun _ => i)) (σ'.f (fun _ => i)) := by
    intro j
    obtain ⟨a, ha, -⟩ := Y.sheaf.existsUnique_gluing' (fun i : M.ι => LB.wchart L (fun _ : Fin 1 => β) j ⊓ M.U i)
      (LB.wchart L (fun _ : Fin 1 => β) j) (fun i => homOfLE inf_le_left)
      (fun y hy => Opens.mem_iSup.2 ⟨(exists_chart hM y).choose, hy, (exists_chart hM y).choose_spec⟩)
      (fun i => piece ℓ c k σ' j i) (fun i i' => fn_ext fun y hy => by
        refine (gs_res (𝟙 Y) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 Y) y inf_le_right hy _).symm)
        rw [gs_piece ℓ c k σ' j i (𝟙 Y) y hy.1, gs_piece ℓ c k σ' j i' (𝟙 Y) y hy.2, _root_.mul_assoc, _root_.mul_assoc]
        exact congrArg _ (indep hL ℓ hP k σ' (𝟙 Y) y (j 0) i i' (Set.mem_iInter.1 hy.1.1 0) hy.1.2 hy.2.2))
    refine ⟨a, fun Z r z i h₁ h₂ => ?_⟩
    have hz : r z ∈ LB.wchart L (fun _ : Fin 1 => β) j ⊓ M.U i := ⟨h₁, h₂⟩
    exact (gs_res r z inf_le_left hz a).symm.trans ((congrArg (gs r z _) (ha i)).trans (gs_piece ℓ c k σ' j i r z hz))
  choose a ha using glue
  refine ⟨⟨a, fun j j' => fn_ext fun y hy => ?_⟩, fun Z r z J J' hJ hJ' => ?_⟩
  · obtain ⟨i, hi⟩ := exists_chart hM y
    refine (gs_res (𝟙 Y) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_unit (𝟙 Y) y _ hy _).trans (congrArg Units.val (gm_linComb L _ _ (𝟙 Y) y j j' hy.1 hy.2)))
      (gs_res (𝟙 Y) y _ hy _))).symm)
    change gs (𝟙 Y) y (LB.wchart L (fun _ : Fin 1 => β) j) (a j) =
      _ * gs (𝟙 Y) y (LB.wchart L (fun _ : Fin 1 => β) j') (a j')
    rw [ha j _ (𝟙 Y) y i hy.1 hi, ha j' _ (𝟙 Y) y i hy.2 hi]
    have e1 := hP Y (𝟙 Y) y (j 0) (j' 0) i i (Set.mem_iInter.1 hy.1 0) (Set.mem_iInter.1 hy.2 0) hi hi
    rw [gm_self hM (𝟙 Y) y hi, inv_one, _root_.mul_one] at e1
    rw [e1]
    simp only [Fin.prod_univ_one, zpow_natCast, mul_pow, Units.val_mul, Units.val_pow_eq_pow_val]
    ring
  · rw [sval_of σ' r z J' (fun _ => J' r) (fun _ => by rw [Category.comp_id])]
    exact ha _ Z r z (J' r) (hJ.mem (fun _ : Fin 1 => β) r) (hJ' r)

end GlobalTheory.Mum.SecTransport

namespace GlobalTheory.Mum

theorem Trait.exists_carries : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R))
    (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ) (u : W)
    (σ' : H0 T.U.LG.L k), ∃ σ'' : SecK C.P.L.L T.β k, T.Carries u σ' σ'' := by
  intro R _ _ _ D C W _ _ _ T k u σ'
  exact SecTransport.exists_transport C.P.L.isLB T.U.LG.isLB T.ℓ T.ℓ_gen (scal T.G.hom u) k σ'

end GlobalTheory.Mum
