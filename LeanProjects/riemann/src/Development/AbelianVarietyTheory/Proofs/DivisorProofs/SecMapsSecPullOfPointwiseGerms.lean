import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
namespace GlobalTheory

theorem secMaps_secPull_of_pointwise : ∀ {Y XA XG : Scheme.{0}} (θ : Y ⟶ XA) (φ : XA ⟶ XG) (fst : Y ⟶ XG), θ ≫ φ = fst →
    ∀ (LP : LB XA) (LL LM : LB XG), LL.IsLB →
    ∀ (ψ : LB.Iso LP (LL.pull φ)) (e : LB.Iso LM LL) (w₀ : LB.Iso (LP.pull θ) (LM.pull fst)),
      (∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i : LL.ι) (j : LM.ι) (k : LP.ι),
        fst (r z) ∈ LL.U i → fst (r z) ∈ LM.U j → θ (r z) ∈ LP.U k →
        gw w₀ r z j (fun _ => k) = (gm (r ≫ fst) z (LL.U i ⊓ LM.U j) (e.s (i, j)))⁻¹ * gw ψ (r ≫ θ) z i k) →
    ∀ (th : LP.Sec) (σ : LL.Sec) (σ' : LM.Sec),
      (∀ (j : (LL.pull φ).ι) (i : LP.ι) (h : (LL.pull φ).U j ⊓ LP.U i ≤ φ ⁻¹ᵁ LL.U (j PUnit.unit)),
        (φ.appLE _ _ h).hom (σ.f (j PUnit.unit)) =
          (show Γ(XA, (LL.pull φ).U j ⊓ LP.U i) from (ψ.s (j, i)).val) * resG _ inf_le_right (th.f i)) →
      GlobalTheory.Cartier.SecMaps e σ' σ →
      GlobalTheory.Cartier.SecMaps w₀ (GlobalTheory.Cartier.secPull th θ) (GlobalTheory.Cartier.secPull σ' fst) := by
  intro Y XA XG θ φ fst hfst LP LL LM hLL ψ e w₀ hw th σ σ' hth he
  subst hfst
  rintro ⟨J, K⟩
  apply fn_ext
  intro y hy
  have hj : (θ ≫ φ) y ∈ LM.U (J PUnit.unit) := mem_pull.1 hy.1
  have hk : θ y ∈ LP.U (K PUnit.unit) := mem_pull.1 hy.2
  obtain ⟨i, hi⟩ := exists_chart hLL ((θ ≫ φ) y)
  have hm1 : (θ ≫ φ) y ∈ LL.U i ⊓ LM.U (J PUnit.unit) := ⟨hi, hj⟩
  have hm2 : θ y ∈ (LL.pull φ).U (fun _ => i) ⊓ LP.U (K PUnit.unit) := ⟨mem_pull.2 hi, hk⟩
  have ha := congrArg (gs (θ ≫ φ) y (LL.U i ⊓ LM.U (J PUnit.unit))) (he (i, J PUnit.unit))
  have hb := congrArg (gs θ y ((LL.pull φ).U (fun _ => i) ⊓ LP.U (K PUnit.unit)))
    (hth (fun _ => i) (K PUnit.unit) (inf_le_left.trans fun x hx => mem_pull.1 hx))
  have hc := hw Y (𝟙 Y) y i (J PUnit.unit) (K PUnit.unit) hi hj hk
  simp only [Category.id_comp] at hc
  rw [gs_mul _ y _ hm1, gs_unit _ y _ hm1] at ha
  change gs _ y _ (resG XG _ _) = _ * gs _ y _ (resG XG _ _) at ha
  rw [gs_res _ y _ hm1, gs_res _ y _ hm1] at ha
  dsimp only at hb
  erw [gs_mul _ y _ hm2, gs_unit _ y _ hm2] at hb
  change _ = _ * gs _ y _ (resG XA _ _) at hb
  rw [gs_res _ y _ hm2] at hb
  have hb' : gs (θ ≫ φ) y (LL.U i) (σ.f i) =
      (gw ψ θ y i (K PUnit.unit)).val * gs θ y (LP.U (K PUnit.unit)) (th.f (K PUnit.unit)) :=
    (gs_pull θ φ y _ hi _).symm.trans ((gs_res θ y _ hm2 _).symm.trans hb)
  have hm3 : (𝟙 Y) y ∈ (LM.pull (θ ≫ φ)).U J := hy.1
  have hm4 : (𝟙 Y) y ∈ (LP.pull θ).U K := hy.2
  change gs (𝟙 Y) y _ (resG Y _ (resG Y _ _)) = _
  erw [gs_res _ y _ hy, gs_res _ y _ hm3, gs_pull (𝟙 Y) (θ ≫ φ) y _ hj, gs_mul _ y _ hy, gs_unit _ y _ hy]
  change _ = _ * gs (𝟙 Y) y _ (resG Y _ (resG Y _ _))
  erw [gs_res _ y _ hy, gs_res _ y _ hm4, gs_pull (𝟙 Y) θ y (LP.U (K PUnit.unit)) hk]
  simp only [Category.id_comp]
  change _ = (gw w₀ (𝟙 Y) y (J PUnit.unit) fun _ => K PUnit.unit).val * _
  rw [hc, Units.val_mul, _root_.mul_assoc, ← hb']
  dsimp only [id] at ha
  rw [ha, Units.inv_mul_cancel_left]

end GlobalTheory
