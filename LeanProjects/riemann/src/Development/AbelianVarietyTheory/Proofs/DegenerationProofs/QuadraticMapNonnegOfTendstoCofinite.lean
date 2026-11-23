import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

noncomputable section
namespace GlobalTheory.ZH

theorem quadraticMap_nonneg_of_tendsto_cofinite {X : Type} [AddCommGroup X] [Module.Free ℤ X]
    (q : QuadraticMap ℤ X ℝ) (hq : Filter.Tendsto q Filter.cofinite Filter.atTop) (x : X) : 0 ≤ q x := by
  by_contra hneg
  push_neg at hneg
  have hx : x ≠ 0 := by
    rintro rfl
    simp at hneg
  have hinj : Function.Injective (fun n : ℤ => n • x) := smul_left_injective ℤ hx
  have h1 := (hq.comp hinj.tendsto_cofinite).eventually (Filter.eventually_gt_atTop 0)
  obtain ⟨n, hn⟩ := h1.exists
  simp only [Function.comp, QuadraticMap.map_smul, zsmul_eq_mul, Int.cast_mul] at hn
  nlinarith [mul_self_nonneg (n : ℝ)]

namespace RatModel
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω}

theorem dotProduct_div_mem_O {J : Type} [Fintype J] {a₀ : M.Z} {v e : J → Ω} {t : Ω}
    (hv : ∀ j, v j ∈ M.O a₀) (he : ∀ j, e j ∈ M.O a₀) (ht : t⁻¹ ∈ M.O a₀) : (v ⬝ᵥ e) / t ∈ M.O a₀ := by
  rw [div_eq_mul_inv]
  exact mul_mem (sum_mem fun j _ => mul_mem (hv j) (he j)) ht

theorem val_dotProduct_div {K : Type} [Field K] {y : Sp K ⟶ M.Z} {a₀ : M.Z} (h : ∀ w, y w ⤳ a₀)
    {J : Type} [Fintype J] {v e : J → Ω} {t : Ω} (hv : ∀ j, v j ∈ M.O a₀) (he : ∀ j, e j ∈ M.O a₀)
    (ht0 : t ≠ 0) (ht' : t ∈ M.O a₀) (ht : t⁻¹ ∈ M.O a₀) :
    M.val y ((v ⬝ᵥ e) / t) = (∑ j, M.val y (v j) * M.val y (e j)) / M.val y t := by
  have h1 : M.val y t * M.val y t⁻¹ = 1 := by
    rw [← val_mul h ht' ht, mul_inv_cancel₀ ht0, val_one]
  have h2 : ∀ s : Finset J, M.val y (∑ j ∈ s, v j * e j) = ∑ j ∈ s, M.val y (v j) * M.val y (e j) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [val_zero]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        val_add h (mul_mem (hv a) (he a)) (sum_mem fun j _ => mul_mem (hv j) (he j)),
        val_mul h (hv a) (he a), ih]
  rw [div_eq_mul_inv, div_eq_mul_inv, dotProduct,
    val_mul h (sum_mem fun j _ => mul_mem (hv j) (he j)) ht, h2, eq_inv_of_mul_eq_one_right h1]

end RatModel

namespace ThetaSys
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω}

theorem Test.norm_pair_le {p : ℕ} [Fact p.Prime] {y : S.R →+* PadicAlgCl p} (τ : S.Test p y)
    {h : S.Gam} (hh : h ∈ τ.yy.ker) {u : S.J → PadicAlgCl p} (hu : u ∈ τ.E) :
    ‖∑ j, u j * y ⟨S.ev h j, S.ev_mem h j⟩‖ ≤ τ.δ := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨α, l, i, hα, hl, rfl⟩ := hu
    have h1 := τ.le α hα h hh i
    simp only [_root_.mul_assoc]
    rw [← Finset.mul_sum, norm_mul]
    calc _ ≤ Real.exp (τ.q α / S.N) * (τ.δ * Real.exp (-(τ.q α / S.N))) :=
          mul_le_mul hl h1 (norm_nonneg _) (Real.exp_pos _).le
      _ = τ.δ := by rw [Real.exp_neg]; field_simp
  | zero => simpa using τ.δ_pos.le
  | add a b _ _ ha hb =>
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  | smul c a _ ha =>
    have hc : ‖(c : PadicAlgCl p)‖ ≤ 1 := (mem_OO_iff _).1 c.2
    have : ∀ j, (c • a) j = (c : PadicAlgCl p) * a j := fun j => rfl
    simp only [this, _root_.mul_assoc]
    rw [← Finset.mul_sum, norm_mul]
    calc _ ≤ 1 * τ.δ := mul_le_mul hc ha (norm_nonneg _) zero_le_one
      _ = τ.δ := _root_.one_mul _

theorem Test.norm_proj_zero_le {p : ℕ} [Fact p.Prime] {y : S.R →+* PadicAlgCl p} (τ : S.Test p y)
    {T : AddSubgroup S.Gam} (hT : T = S.perp τ.yy.ker) {h : S.Gam} (hh : h ∈ τ.yy.ker) (i : S.J) :
    ‖∑ j, y (algebraMap o S.R (S.proj T 0 j i)) * y ⟨S.ev h j, S.ev_mem h j⟩‖ ≤ τ.δ := by
  subst hT
  have := τ.le 0 (fun v0 => by
    rw [map_zero]; exact quadraticMap_nonneg_of_tendsto_cofinite τ.q τ.pos _) h hh i
  simpa only [map_zero, zero_div, neg_zero, Real.exp_zero, _root_.mul_one] using this

theorem Test.exists_norm_proj_zero_eq {p : ℕ} [Fact p.Prime] {y : S.R →+* PadicAlgCl p} (τ : S.Test p y)
    {T : AddSubgroup S.Gam} (hT : T = S.perp τ.yy.ker) {h : S.Gam} (hh : h ∈ τ.yy.ker) :
    ∃ i, ‖∑ j, y (algebraMap o S.R (S.proj T 0 j i)) * y ⟨S.ev h j, S.ev_mem h j⟩‖ = τ.δ := by
  subst hT
  have := τ.unit0 h hh
  simpa only [map_zero] using this

theorem val_pair_div {M : RatModel o Ω} {U₀ : M.Z.Opens} (hO : S.Over₀ M U₀) {U : Set M.Z}
    (hU : U ⊆ U₀) {z : M.Z} {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ M.Z} (hc : M.Cen U z y)
    {y₀ : S.R →+* PadicAlgCl p} (hat : S.At M y y₀) {v : S.J → Ω} (hv : ∀ j, v j ∈ M.ringOn U)
    (h : S.Gam) {x₀ : S.Gam} (hx : S.th x₀ ≠ 0) :
    M.val (gPt p ≫ y) ((v ⬝ᵥ S.ev h) / S.th x₀) =
      (∑ j, M.val (gPt p ≫ y) (v j) * y₀ ⟨S.ev h j, S.ev_mem h j⟩) / M.val (gPt p ≫ y) (S.th x₀) := by
  let w : Sp (PadicAlgCl p) := IsLocalRing.closedPoint (PadicAlgCl p)
  have hζ : (gPt p ≫ y) w ∈ U := hc.2 ⟨w, rfl⟩
  have hs := RatModel.specializes_of_range_eq (RatModel.range_eq_singleton (gPt p ≫ y) w)
  rw [RatModel.val_dotProduct_div hs (fun j => RatModel.ringOn_le_O hζ (hv j))
    (fun j => RatModel.ringOn_le_O (hU hζ) (hO.le (S.ev_mem h j))) hx
    (RatModel.ringOn_le_O (hU hζ) (hO.le (S.th_mem x₀)))
    (RatModel.ringOn_le_O (hU hζ) (hO.th_unit x₀ hx))]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by rw [hat]

end ThetaSys

theorem coord_regular_and_unit : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.Over₀ M U₀ → ((∀ U₁ : M.Z.Opens, U₁ ≤ U₀ → (U₁ : Set M.Z).Nonempty → ∀ z : M.Z, IsClosed ({z} : Set M.Z) → (∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y) ∧ ∀ φ ∈ M.ringOn U₁, (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y → ‖M.val (gPt p ≫ y) φ‖ ≤ 1) → φ ∈ M.O z) ∧ JacobsonSpace M.Z) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ z y → ∃ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ ∧ (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) ∧ Nonempty (S.Test p y₀)) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → (∀ x, x ∈ S.supI M z ↔ ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ) ∧ S.HH M z = τ.yy.ker) → ((∀ ξ : M.Z, S.IsoFree (S.TT M ξ) ∧ S.perp (S.TT M ξ) = S.HH M ξ) ∧ (∀ ξ z : M.Z, ξ ⤳ z → S.supI M z ⊆ S.supI M ξ) ∧ (∀ ξ ∈ U₀, S.TT M ξ = ⊥) ∧ (∀ (ξ : M.Z) (W : M.Z.Opens), ξ ∈ W → ∃ x ∈ W, IsClosed ({x} : Set M.Z) ∧ ξ ⤳ x ∧ S.supI M x = S.supI M ξ)) → S.IsEE M U₀ EE → ∀ ξ : M.Z, ∀ x₀ ∈ S.supI M ξ, ∀ h ∈ S.HH M ξ, (∀ v ∈ EE.E ξ, (v ⬝ᵥ S.ev h) / S.th x₀ ∈ M.O ξ) ∧ ∃ i, (fun j => algebraMap o Ω (S.proj (S.TT M ξ) 0 j i)) ⬝ᵥ S.ev h ≠ 0 ∧ S.th x₀ / ((fun j => algebraMap o Ω (S.proj (S.TT M ξ) 0 j i)) ⬝ᵥ S.ev h) ∈ M.O ξ := by
  intro o Ω _ _ _ _ S M U₀ EE hO hLL hT hsup hstr hEE
  have closed : ∀ z : M.Z, IsClosed ({z} : Set M.Z) → ∀ x₀ ∈ S.supI M z, ∀ h ∈ S.HH M z,
      (∀ v ∈ EE.E z, (v ⬝ᵥ S.ev h) / S.th x₀ ∈ M.O z) ∧
      ∃ i, (fun j => algebraMap o Ω (S.proj (S.TT M z) 0 j i)) ⬝ᵥ S.ev h ≠ 0 ∧
        S.th x₀ / ((fun j => algebraMap o Ω (S.proj (S.TT M z) 0 j i)) ⬝ᵥ S.ev h) ∈ M.O z := by
    intro z hz x₀ hx₀ h hh
    have hx : S.th x₀ ≠ 0 := hx₀.1
    refine ⟨fun v hv => ?_, ?_⟩
    · let V : M.Z.Opens := ⟨⋂ j, {a | v j ∈ M.O a}, isOpen_iInter_of_finite fun j => M.isOpen_setOf_mem_O _⟩
      have hV : (V : Set M.Z).Nonempty := ⟨genericPoint M.Z, Set.mem_iInter.2 fun j => by
        simp only [Set.mem_setOf_eq, M.O_genericPoint]; trivial⟩
      have hvV : ∀ j, v j ∈ M.ringOn ((U₀ ⊓ V : M.Z.Opens) : Set M.Z) := fun j =>
        RatModel.mem_ringOn.2 fun a ha => Set.mem_iInter.1 ha.2 j
      refine (hLL.1 (U₀ ⊓ V) inf_le_left (M.nonempty_inf hO.ne hV) z hz).2 _ ?_ ?_
      · exact RatModel.mem_ringOn.2 fun a ha => RatModel.dotProduct_div_mem_O
          (fun j => RatModel.ringOn_le_O ha (hvV j))
          (fun j => RatModel.ringOn_le_O ha.1 (hO.le (S.ev_mem h j)))
          (RatModel.ringOn_le_O ha.1 (hO.th_unit x₀ hx))
      · intro p _ y hc
        have hc0 : M.Cen U₀ z y := ⟨hc.1, fun a ha => (hc.2 ha).1⟩
        obtain ⟨y₀, hat, -, ⟨τ⟩⟩ := hT z p y hc0
        obtain ⟨h1, h2⟩ := hsup z p y y₀ τ hc0 hat
        rw [ThetaSys.val_pair_div hO (fun a ha => ha.1) hc hat hvV h hx, norm_div, (h1 x₀).1 hx₀,
          div_le_one τ.δ_pos]
        refine τ.norm_pair_le (h2 ▸ hh) (u := fun j => M.val (gPt p ≫ y) (v j)) ?_
        rw [← hEE.2 z p y y₀ τ hc0 hat]
        exact Submodule.subset_span ⟨v, hv, rfl⟩
    · have hw : ∀ i j, algebraMap o Ω (S.proj (S.TT M z) 0 j i) ∈ M.ringOn (U₀ : Set M.Z) :=
        fun i j => Subalgebra.algebraMap_mem _ _
      have hval : ∀ i (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p)
          (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ →
          ‖M.val (gPt p ≫ y) (((fun j => algebraMap o Ω (S.proj (S.TT M z) 0 j i)) ⬝ᵥ S.ev h) / S.th x₀)‖ =
            ‖∑ j, y₀ (algebraMap o S.R (S.proj (S.TT M z) 0 j i)) * y₀ ⟨S.ev h j, S.ev_mem h j⟩‖ / τ.δ := by
        intro i p _ y y₀ τ hc hat
        rw [ThetaSys.val_pair_div hO subset_rfl hc hat (hw i) h hx, norm_div,
          ((hsup z p y y₀ τ hc hat).1 x₀).1 hx₀]
        congr 2
        exact Finset.sum_congr rfl fun j _ => by rw [hat (algebraMap o S.R _)]; rfl
      have hmem : ∀ i, ((fun j => algebraMap o Ω (S.proj (S.TT M z) 0 j i)) ⬝ᵥ S.ev h) / S.th x₀ ∈ M.O z := by
        intro i
        refine (hLL.1 U₀ le_rfl hO.ne z hz).2 _ ?_ ?_
        · exact RatModel.mem_ringOn.2 fun a ha => RatModel.dotProduct_div_mem_O
            (fun j => RatModel.ringOn_le_O ha (hw i j))
            (fun j => RatModel.ringOn_le_O ha (hO.le (S.ev_mem h j)))
            (RatModel.ringOn_le_O ha (hO.th_unit x₀ hx))
        · intro p _ y hc
          obtain ⟨y₀, hat, -, ⟨τ⟩⟩ := hT z p y hc
          have h2 := (hsup z p y y₀ τ hc hat).2
          rw [hval i p y y₀ τ hc hat, div_le_one τ.δ_pos]
          exact τ.norm_proj_zero_le (by rw [← h2]; rfl) (h2 ▸ hh) i
      obtain ⟨p, _, y, hc⟩ := (hLL.1 U₀ le_rfl hO.ne z hz).1
      obtain ⟨y₀, hat, -, ⟨τ⟩⟩ := hT z p y hc
      have h2 := (hsup z p y y₀ τ hc hat).2
      obtain ⟨i, hi⟩ := τ.exists_norm_proj_zero_eq (T := S.TT M z) (by rw [← h2]; rfl) (h2 ▸ hh)
      have h3 := hval i p y y₀ τ hc hat
      rw [hi, div_self τ.δ_pos.ne', RatModel.norm_val_eq_one_iff hc.1 (hmem i), RatModel.isUnit_O_iff] at h3
      refine ⟨i, fun h0 => h3.1 (by simp only [h0, zero_div]), ?_⟩
      simpa only [inv_div] using h3.2
  intro ξ x₀ hx₀ h hh
  obtain ⟨U, b, hξU, -, hb⟩ := EE.loc ξ
  obtain ⟨x, hxU, hxc, hsp, hI⟩ := hstr.2.2.2 ξ U hξU
  have hH : S.HH M x = S.HH M ξ := by simp only [ThetaSys.HH, hI]
  have hTT : S.TT M x = S.TT M ξ := by simp only [ThetaSys.TT, hH]
  obtain ⟨c1, c2⟩ := closed x hxc x₀ (hI ▸ hx₀) h (hH ▸ hh)
  have hle := RatModel.O_le_of_specializes hsp
  refine ⟨fun v hv => ?_, ?_⟩
  · rw [hb ξ hξU] at hv
    induction hv using Submodule.span_induction with
    | mem v hv => exact hle (c1 v (by rw [hb x hxU]; exact Submodule.subset_span hv))
    | zero => simp
    | add a c _ _ ha hc => rw [add_dotProduct, add_div]; exact add_mem ha hc
    | smul c a _ ha =>
      have : c • a = (c : Ω) • a := rfl
      rw [this, smul_dotProduct, smul_eq_mul, mul_div_assoc]
      exact mul_mem c.2 ha
  · rw [hTT] at c2
    obtain ⟨i, h1, h2⟩ := c2
    exact ⟨i, h1, hle h2⟩

end GlobalTheory.ZH
end
