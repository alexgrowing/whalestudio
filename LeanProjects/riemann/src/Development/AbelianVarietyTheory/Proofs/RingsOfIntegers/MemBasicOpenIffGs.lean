import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.SectionRatio

open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace

theorem mem_basicOpen_iff_gs {Y : Scheme.{0}} {U : Y.Opens} (f : Γ(Y, U)) (y : Y) (hy : y ∈ U) :
    y ∈ Y.basicOpen f ↔ IsUnit (gs (𝟙 Y) y U f) := by
  rw [gs_eq (𝟙 Y) y U hy f, Scheme.mem_basicOpen Y f y hy]
  exact Iff.rfl

theorem exists_quot {Y : Scheme.{0}} {U : Y.Opens} (a b : Γ(Y, U)) :
    ∃ q : Γ(Y, Y.basicOpen b), ∀ y ∈ Y.basicOpen b,
      gs (𝟙 Y) y _ q * gs (𝟙 Y) y U b = gs (𝟙 Y) y U a := by
  have hD : Y.basicOpen b ≤ U := Y.basicOpen_le b
  have hu : IsUnit ((Y.presheaf.map (homOfLE hD).op).hom b) := Y.toRingedSpace.isUnit_res_basicOpen b
  obtain ⟨w, hw⟩ := hu
  refine ⟨(Y.presheaf.map (homOfLE hD).op).hom a * ↑w⁻¹, fun y hy => ?_⟩
  have key : ((Y.presheaf.map (homOfLE hD).op).hom a * ↑w⁻¹) * (Y.presheaf.map (homOfLE hD).op).hom b =
      (Y.presheaf.map (homOfLE hD).op).hom a := by
    have hw' : (Y.presheaf.map (homOfLE hD).op).hom b = ↑w := hw.symm
    rw [hw', _root_.mul_assoc, Units.inv_mul, _root_.mul_one]
  rw [← gs_res (𝟙 Y) y hD hy b, ← gs_mul (𝟙 Y) y _ hy, key, gs_res (𝟙 Y) y hD hy a]

private theorem exists_global_unit_of_compatible_of_iSup_eq {Y : Scheme.{0}} {P : Type} (W : P → Y.Opens) (hW : ∀ y, ∃ p, y ∈ W p)
    (q : ∀ p, Γ(Y, W p))
    (hq : ∀ p p' (y : Y), y ∈ W p → y ∈ W p' → gs (𝟙 Y) y (W p) (q p) = gs (𝟙 Y) y (W p') (q p')) :
    ∃ c : Γ(Y, ⊤), ∀ p (y : Y), y ∈ W p → gs (𝟙 Y) y ⊤ c = gs (𝟙 Y) y (W p) (q p) := by
  have hcov : (⊤ : Y.Opens) ≤ iSup W := fun y _ => by
    obtain ⟨p, hp⟩ := hW y
    exact Opens.mem_iSup.2 ⟨p, hp⟩
  have hcomp : TopCat.Presheaf.IsCompatible Y.sheaf.1 W q := by
    intro p p'
    apply fn_ext
    intro y hy
    exact (gs_res (𝟙 Y) y inf_le_left hy (q p)).trans
      ((hq p p' y hy.1 hy.2).trans (gs_res (𝟙 Y) y inf_le_right hy (q p')).symm)
  obtain ⟨c, hc, -⟩ := TopCat.Sheaf.existsUnique_gluing' Y.sheaf W ⊤ (fun p => homOfLE le_top) hcov q hcomp
  refine ⟨c, fun p y hy => ?_⟩
  rw [← hc p]
  exact (gs_res (𝟙 Y) y le_top hy c).symm

private theorem gs_id_linComb_eq_trF_mul_sval {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (j : K → L.ι) (y : Y) (hy : y ∈ (LB.LinComb L φ ε).U j)
    (J : (Y ⟶ X) → L.ι) (hJ : Good L y J) :
    gs (𝟙 Y) y ((LB.LinComb L φ ε).U j) (s.f j) =
      (trF φ ε (𝟙 Y) y j (fun k => J (𝟙 Y ≫ φ k))).val * sval s (𝟙 Y) y J :=
  sec_trans s (𝟙 Y) y hy (hJ.mem φ (𝟙 Y))

theorem exists_ratio {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {Ix : Type} (a b : Ix → LB.Sec (LB.LinComb L φ ε))
    (hb : ∀ (y : Y) (J), Good L y J → ∃ i, IsUnit (sval (b i) (𝟙 Y) y J))
    (hab : ∀ i i' (y : Y) (J), Good L y J →
      sval (a i) (𝟙 Y) y J * sval (b i') (𝟙 Y) y J = sval (a i') (𝟙 Y) y J * sval (b i) (𝟙 Y) y J) :
    ∃ c : Γ(Y, ⊤), ∀ i (y : Y) (J), Good L y J →
      sval (a i) (𝟙 Y) y J = gs (𝟙 Y) y ⊤ c * sval (b i) (𝟙 Y) y J := by

  let W : Ix × (K → L.ι) → Y.Opens := fun p => Y.basicOpen ((b p.1).f p.2)
  choose q hq using fun p : Ix × (K → L.ι) => exists_quot ((a p.1).f p.2) ((b p.1).f p.2)
  have goodAt : ∀ y : Y, ∃ J, Good L y J := fun y => by
    obtain ⟨J, hJ, -⟩ := exists_good L hL y (K := Empty) (fun e => e.elim) (fun e => e.elim)
      (fun e => e.elim) (fun e => e.elim)
    exact ⟨J, hJ⟩

  have loc : ∀ p (y : Y), y ∈ W p → ∀ J, Good L y J →
      gs (𝟙 Y) y (W p) (q p) * sval (b p.1) (𝟙 Y) y J = sval (a p.1) (𝟙 Y) y J ∧
        IsUnit (sval (b p.1) (𝟙 Y) y J) := by
    intro p y hy J hJ
    have hyc : y ∈ (LB.LinComb L φ ε).U p.2 := Y.basicOpen_le _ hy
    have e := hq p y hy
    rw [gs_id_linComb_eq_trF_mul_sval (b p.1) p.2 y hyc J hJ, gs_id_linComb_eq_trF_mul_sval (a p.1) p.2 y hyc J hJ] at e
    have hu := (mem_basicOpen_iff_gs ((b p.1).f p.2) y hyc).1 hy
    rw [gs_id_linComb_eq_trF_mul_sval (b p.1) p.2 y hyc J hJ] at hu
    set T := trF φ ε (𝟙 Y) y p.2 (fun k => J (𝟙 Y ≫ φ k))
    refine ⟨?_, isUnit_of_mul_isUnit_right hu⟩
    apply T.isUnit.mul_left_cancel
    linear_combination e
  obtain ⟨c, hc⟩ := exists_global_unit_of_compatible_of_iSup_eq W (fun y => by
      obtain ⟨J, hJ⟩ := goodAt y
      obtain ⟨i, hi⟩ := hb y J hJ
      exact ⟨(i, fun k => J (𝟙 Y ≫ φ k)),
        (mem_basicOpen_iff_gs ((b i).f _) y (hJ.mem φ (𝟙 Y))).2 hi⟩) q
    (fun p p' y hy hy' => by
      obtain ⟨J, hJ⟩ := goodAt y
      obtain ⟨e1, u1⟩ := loc p y hy J hJ
      obtain ⟨e2, u2⟩ := loc p' y hy' J hJ
      have e3 := hab p.1 p'.1 y J hJ
      apply (u1.mul u2).mul_right_cancel
      linear_combination sval (b p'.1) (𝟙 Y) y J * e1 + e3 - sval (b p.1) (𝟙 Y) y J * e2)
  refine ⟨c, fun i y J hJ => ?_⟩
  obtain ⟨i₀, h₀⟩ := hb y J hJ
  have hy₀ : y ∈ W (i₀, fun k => J (𝟙 Y ≫ φ k)) :=
    (mem_basicOpen_iff_gs ((b i₀).f _) y (hJ.mem φ (𝟙 Y))).2 h₀
  obtain ⟨e1, -⟩ := loc _ y hy₀ J hJ
  rw [hc _ y hy₀]
  apply h₀.mul_right_cancel
  linear_combination hab i i₀ y J hJ - sval (b i) (𝟙 Y) y J * e1

theorem ratio_glue : ∀ (X Y : Scheme.{0}) (L : LB X), L.IsLB → ∀ (K₁ K₂ K₃ : Type) [Fintype K₁] [Fintype K₂] [Fintype K₃] (φ₁ : K₁ → (Y ⟶ X)) (ε₁ : K₁ → ℤ) (φ₂ : K₂ → (Y ⟶ X)) (ε₂ : K₂ → ℤ) (φ₃ : K₃ → (Y ⟶ X)) (ε₃ : K₃ → ℤ) (h : Y ⟶ Y), Geo.Tor.FormEq φ₁ ε₁ (Sum.elim (fun k => h ≫ φ₂ k) φ₃) (Sum.elim ε₂ ε₃) → ∀ (u : LB.Gen (LB.LinComb L φ₃ ε₃)), u.IsGen → ∀ (Ix : Type) (s'' : Ix → LB.Sec (LB.LinComb L φ₁ ε₁)) (s : Ix → LB.Sec (LB.LinComb L φ₂ ε₂)), (∀ (y : Y) (J), Geo.Tor.Good L y J → ∃ i, IsUnit (Geo.Tor.sval (s i) h y J)) → (∀ i i' (y : Y) (J), Geo.Tor.Good L y J → Geo.Tor.sval (s'' i) (𝟙 Y) y J * Geo.Tor.sval (s i') h y J = Geo.Tor.sval (s'' i') (𝟙 Y) y J * Geo.Tor.sval (s i) h y J) → ∃ c : Γ(Y, ⊤), ∀ i (y : Y) (J), Geo.Tor.Good L y J → Geo.Tor.sval (s'' i) (𝟙 Y) y J = Geo.Tor.gs (𝟙 Y) y ⊤ c * (Geo.Tor.sval (s i) h y J * (Geo.Tor.val u (𝟙 Y) y J).val) := by
  intro X Y L hL K₁ K₂ K₃ _ _ _ φ₁ ε₁ φ₂ ε₂ φ₃ ε₃ h hF u hu Ix s'' s hs hx
  have hF' : Geo.Tor.FormEq (Sum.elim (fun k => h ≫ φ₂ k) φ₃) (Sum.elim ε₂ ε₃) φ₁ ε₁ :=
    fun U _ g => (hF U g).symm
  choose b hb using fun i => Geo.Tor.exists_sec hL hF' (Geo.Tor.pullMulSec (s i) h u hu)
  have key : ∀ i (y : Y) (J), Geo.Tor.Good L y J →
      Geo.Tor.sval (b i) (𝟙 Y) y J = Geo.Tor.sval (s i) h y J * (Geo.Tor.val u (𝟙 Y) y J).val := by
    intro i y J hJ
    rw [hb i Y (𝟙 Y) y J hJ, Geo.Tor.sval_pullMulSec (s i) h u hu (𝟙 Y) y hJ, Category.id_comp]
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.SectionRatio.exists_ratio hL s'' b
    (fun y J hJ => by
      obtain ⟨i, hi⟩ := hs y J hJ
      exact ⟨i, by rw [key i y J hJ]; exact hi.mul (Geo.Tor.val u (𝟙 Y) y J).isUnit⟩)
    (fun i i' y J hJ => by
      rw [key i y J hJ, key i' y J hJ]
      linear_combination (Geo.Tor.val u (𝟙 Y) y J).val * hx i i' y J hJ)
  refine ⟨c, fun i y J hJ => ?_⟩
  rw [hc i y J hJ, key i y J hJ]

end GlobalTheory.SectionRatio
