import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagCell2

theorem isOpen_setOf_mem_frames {F Ω ι : Type} [Field F] [Field Ω] [Algebra F Ω] [Finite ι] {m k : ι → ℕ}
    {M : GlobalTheory.ZH.RatModel F Ω} (S : Fr M m k) (B : Mat m Ω) : IsOpen {z : M.Z | B ∈ S.S z} := by
  have hP (g : Mat m Ω) : IsOpen {z : M.Z | Par k (M.O z).toSubring g} := by
    have : {z : M.Z | Par k (M.O z).toSubring g} = ⋂ τ, ((⋂ i, ⋂ j, {z : M.Z | g τ i j ∈ M.O z}) ∩
        ({_z : M.Z | (g τ).det ≠ 0} ∩ ({z : M.Z | (g τ).det⁻¹ ∈ M.O z} ∩
          {_z : M.Z | ∀ i j : Fin (m τ), (i : ℕ) < k τ → i < j → g τ i j = 0}))) := by
      ext z
      simp only [Par, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff]
      rfl
    rw [this]
    exact isOpen_iInter_of_finite fun τ => (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      M.isOpen_setOf_mem_O _).inter (isOpen_const.inter ((M.isOpen_setOf_mem_O _).inter isOpen_const))
  refine isOpen_iff_forall_mem_open.2 fun z hz => ?_
  obtain ⟨U, A, hzU, -, hU⟩ := S.loc z
  exact ⟨(U : Set M.Z) ∩ {z' | Par k (M.O z').toSubring (B * A⁻¹)}, fun w hw => (hU w hw.1 B).2 hw.2,
    U.isOpen.inter (hP _), hzU, (hU z hzU B).1 hz⟩

theorem isOpen_inCell_and_regAt : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ)
    (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f →
    ∀ (A : Mat m X.Fn) (u : Cell m → Y.Fn), IsOpen {y : Y.X | InCell E E' φ f A u y} ∧
      ∀ y, InCell E E' φ f A u y → ∀ j, RegAt y (u j) := by
  intro F _ X Y ι _ m E E' φ f hR A u
  refine ⟨((isOpen_setOf_mem_frames E A).preimage f.continuous).inter (isOpen_setOf_mem_frames E' _), ?_⟩
  rintro y ⟨hA, hu⟩ ⟨τ, ⟨b, a⟩, hab⟩
  have h := hR.sub y _ hu A hA
  have hd : ∀ τ, (A.map φ τ).det ≠ 0 := fun τ => by
    have := Mat.det_map A (φ : X.Fn →+* Y.Fn) τ
    exact this.trans_ne ((map_ne_zero _).2 (Fr.det_ne hA τ))
  rw [mul_assoc, Mat.mul_inv hd, mul_one] at h
  have h2 := (h τ).1 a b
  have hab' : a < b := hab
  have e : upM u τ a b = u ⟨τ, ⟨(b, a), hab⟩⟩ := by
    simp only [upM, upU, Matrix.of_apply, dif_pos hab']
  rw [e] at h2
  exact mem_O_ratOf.1 h2

end GlobalTheory.FlagCell2
