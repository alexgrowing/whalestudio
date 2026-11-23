import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicOutsideLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajPos
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.HermitianTraceFormVanishing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowDomainCriterionHolds

namespace ReciprocityTheory.ChartRestriction.G.FD.FlowMajorantFlags

open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem Hf_sub_left (x : Frame X.Ψ r) (τ : X.Ψ) (u v w : Fin r → ℂ) :
    X.Hf x τ (u - v) w = X.Hf x τ u w - X.Hf x τ v w := by
  simp only [Data.Hf_eq_jp, Data.jp_sub, hermC_sub_left]

theorem Hf_smul_left (x : Frame X.Ψ r) (τ : X.Ψ) (k : ℂ) (u w : Fin r → ℂ) :
    X.Hf x τ (k • u) w = k * X.Hf x τ u w := by
  simp only [Data.Hf_eq_jp, Data.jp_smul, hermC_smul_left]

theorem Hf_smul_right (x : Frame X.Ψ r) (τ : X.Ψ) (k : ℂ) (u w : Fin r → ℂ) :
    X.Hf x τ u (k • w) = conj k * X.Hf x τ u w := by
  simp only [Data.Hf_eq_jp, hermC_smul_right]

theorem maj_smul {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (k : ℝ) (v : Fin r → ℂ) :
    X.maj x τ ((k : ℂ) • v) = k ^ 2 * X.maj x τ v := by
  apply Complex.ofReal_injective
  rw [← X.Hf_self hx τ, Hf_smul_left, Hf_smul_right, X.Hf_self hx τ, Complex.conj_ofReal]
  push_cast; ring

theorem ppos_flag {z z' : Frame X.Ψ r} (hz : z ∈ X.dom) (hz' : z' ∈ X.dom) (hf : X.SameFlag z z')
    (τ : X.Ψ) (v : Fin r → ℂ) : X.ppos z' τ v = X.ppos z τ v := by
  have hspan := hf τ
  have hmem : X.ppos z τ v ∈ Submodule.span ℂ
      (Set.range fun a : Fin X.p0 => col (mat z' τ) (Fin.castLE X.p0_le a)) := by
    rw [← hspan]
    unfold Data.ppos
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  obtain ⟨β, hβ⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hmem
  rw [← hβ]
  apply X.ppos_eq_of z' τ (X.gramPos_det_ne hz' τ) v β
  intro b
  rw [hβ]
  have hb : col (mat z' τ) (Fin.castLE X.p0_le b) ∈ Submodule.span ℂ
      (Set.range fun a : Fin X.p0 => col (mat z τ) (Fin.castLE X.p0_le a)) := by
    rw [hspan]; exact Submodule.subset_span ⟨b, rfl⟩
  obtain ⟨γ, hγ⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hb
  rw [← hγ, hermC_sum_right]
  exact Finset.sum_eq_zero fun a _ => by
    rw [hermC_smul_right, X.ppos_orth z τ (X.gramPos_det_ne hz τ) v a, mul_zero]

theorem Hf_flag {z z' : Frame X.Ψ r} (hz : z ∈ X.dom) (hz' : z' ∈ X.dom) (hf : X.SameFlag z z')
    (τ : X.Ψ) (u w : Fin r → ℂ) : X.Hf z' τ u w = X.Hf z τ u w := by
  simp only [Data.Hf, ppos_flag X hz hz' hf]

theorem maj_flag {z z' : Frame X.Ψ r} (hz : z ∈ X.dom) (hz' : z' ∈ X.dom) (hf : X.SameFlag z z')
    (τ : X.Ψ) (v : Fin r → ℂ) : X.maj z' τ v = X.maj z τ v := by
  apply Complex.ofReal_injective
  rw [← X.Hf_self hz' τ, ← X.Hf_self hz τ, Hf_flag X hz hz' hf]

theorem flowMatV_mulVec (e : Fin r → ℂ) (τ : X.Ψ) (s : ℂ) (v : Fin r → ℂ) :
    Matrix.mulVec (X.flowMatV e τ s) v = v + (-(I * X.c τ * s) * hermC τ.1 X.Gm v e) • e := by
  funext a
  simp only [Data.flowMatV, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, hermC, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [sub_eq_add_neg]
  congr 1
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem ppos_flowV (e : X.Ψ → Fin r → ℂ) (s : X.Ψ → ℂ) {z : Frame X.Ψ r} (hz : z ∈ X.dom)
    (hTz : X.flowV e s z ∈ X.dom) (τ : X.Ψ) (v : Fin r → ℂ)
    (hve : hermC τ.1 X.Gm v (e τ) = 0) (hpe : hermC τ.1 X.Gm (X.ppos z τ v) (e τ) = 0) :
    X.ppos (X.flowV e s z) τ v = X.ppos z τ v := by
  have hcol : ∀ a, col (mat (X.flowV e s z) τ) a =
      Matrix.mulVec (X.flowMatV (e τ) τ (s τ)) (col (mat z τ) a) :=
    fun a => Data.col_mul (X.flowMatV (e τ) τ (s τ)) (mat z τ) a
  have hT := flowMatV_mulVec X (e τ) τ (s τ)
  set β : Fin X.p0 → ℂ := fun a => ∑ b, hermC τ.1 X.Gm v (col (mat z τ) (Fin.castLE X.p0_le b)) *
    (X.gramPos z τ)⁻¹ b a with hβ
  have hp : X.ppos z τ v = ∑ a, β a • col (mat z τ) (Fin.castLE X.p0_le a) := rfl
  have hcoef : ∑ a, β a * (-(I * X.c τ * s τ) *
      hermC τ.1 X.Gm (col (mat z τ) (Fin.castLE X.p0_le a)) (e τ)) = 0 := by
    have : ∑ a, β a * (-(I * X.c τ * s τ) *
        hermC τ.1 X.Gm (col (mat z τ) (Fin.castLE X.p0_le a)) (e τ)) =
        -(I * X.c τ * s τ) * hermC τ.1 X.Gm (X.ppos z τ v) (e τ) := by
      rw [hp, hermC_sum_left, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hermC_smul_left]; ring
    rw [this, hpe, mul_zero]
  have hsum : ∑ a, β a • col (mat (X.flowV e s z) τ) (Fin.castLE X.p0_le a) = X.ppos z τ v := by
    simp only [hcol, hT, smul_add, Finset.sum_add_distrib, smul_smul]
    rw [← hp, ← Finset.sum_smul, hcoef, zero_smul, add_zero]
  rw [← hsum]
  apply X.ppos_eq_of _ τ (X.gramPos_det_ne hTz τ) v β
  intro b
  rw [hsum, hcol, hT, hermC_add_right, hermC_smul_right,
    X.ppos_orth z τ (X.gramPos_det_ne hz τ) v b, zero_add, hermC_sub_left, hve, hpe, sub_zero,
    mul_zero]

theorem maj_flowV (e : X.Ψ → Fin r → ℂ) (s : X.Ψ → ℂ) {z : Frame X.Ψ r} (hz : z ∈ X.dom)
    (hTz : X.flowV e s z ∈ X.dom) (τ : X.Ψ) (v : Fin r → ℂ)
    (hve : hermC τ.1 X.Gm v (e τ) = 0) (hpe : hermC τ.1 X.Gm (X.ppos z τ v) (e τ) = 0) :
    X.maj (X.flowV e s z) τ v = X.maj z τ v := by
  apply Complex.ofReal_injective
  rw [← X.Hf_self hTz τ, ← X.Hf_self hz τ]
  simp only [Data.Hf, ppos_flowV X e s hz hTz τ v hve hpe]

theorem hpe_of {z : Frame X.Ψ r} (hz : z ∈ X.dom) (τ : X.Ψ) (v e : Fin r → ℂ)
    (hH : X.Hf z τ e v = 0) (hh : hermC τ.1 X.Gm e v = 0) :
    hermC τ.1 X.Gm (X.ppos z τ v) e = 0 := by
  have h1 : hermC τ.1 X.Gm (X.ppos z τ e) v = 0 := by
    rw [Data.Hf_eq_two_ppos, hh, sub_zero] at hH
    simpa using hH
  rw [X.ppos_selfadj hz, ← hermC_conj τ.1 X.Gm_herm, h1, map_zero]

end ReciprocityTheory.ChartRestriction.G.FD.FlowMajorantFlags
