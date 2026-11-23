import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.EllipticFunctions
import GroundTheory.GlobalFields.ComplexMultiplication.EllipticConstant
import GroundTheory.GlobalFields.ComplexMultiplication.EllipticRational
import GroundTheory.GlobalFields.ComplexMultiplication.Residue
import GroundTheory.GlobalFields.ComplexMultiplication.ResidueTheorem
import GroundTheory.GlobalFields.ComplexMultiplication.EllipticResidues

open Complex Filter Topology Set
open scoped PeriodPair

noncomputable section

namespace GroundTheory.Global
namespace Elliptic

variable {L : PeriodPair}

variable (L) in

def torusOrder (f : ℂ → ℂ) (x : Torus L) : ℤ :=
  (meromorphicOrderAt f x.out).untopD 0

lemma torusOrder_mk {f : ℂ → ℂ} (hf : IsEllipticFunction L f) (z : ℂ) :
    torusOrder L f (Torus.mk L z) = (meromorphicOrderAt f z).untopD 0 := by
  have h := (Torus.mk_eq_mk_iff L).1 (QuotientAddGroup.out_eq' (Torus.mk L z))
  have := hf.2.meromorphicOrderAt_add h z
  rw [add_sub_cancel] at this
  rw [torusOrder, this]

lemma isEllipticFunction_logDeriv {f : ℂ → ℂ} (hf : IsEllipticFunction L f) :
    IsEllipticFunction L (logDeriv f) := by
  refine ⟨fun z ↦ ?_, fun z l hl ↦ ?_⟩
  · have : logDeriv f = fun w ↦ deriv f w / f w := rfl
    rw [this]
    exact (hf.1 z).deriv.div (hf.1 z)
  · simp only [logDeriv_apply]
    rw [hf.2 z l hl]
    congr 1
    rw [← deriv_comp_add_const, hf.2.comp_add hl]

lemma residue_logDeriv_eq_untopD {f : ℂ → ℂ} {z : ℂ} (hf : MeromorphicAt f z) :
    residue (logDeriv f) z = (((meromorphicOrderAt f z).untopD 0 : ℤ) : ℂ) := by
  by_cases htop : meromorphicOrderAt f z = ⊤
  · rw [htop, WithTop.untopD_top, Int.cast_zero]
    rw [meromorphicOrderAt_eq_top_iff] at htop
    have hmer : MeromorphicAt (logDeriv f) z := by
      have : logDeriv f = fun w ↦ deriv f w / f w := rfl
      rw [this]
      exact hf.deriv.div hf
    have h0 : logDeriv f =ᶠ[𝓝[≠] z] fun _ ↦ (0 : ℂ) := by
      filter_upwards [htop] with w hw
      simp [logDeriv_apply, hw]
    rw [residue_congr hmer h0]
    exact residue_eq_zero_of_analyticAt analyticAt_const
  · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 htop
    rw [← hn, WithTop.untopD_coe]
    exact residue_logDeriv hf hn.symm

lemma torusResidue_logDeriv {f : ℂ → ℂ} (hf : IsEllipticFunction L f) (x : Torus L) :
    torusResidue L (logDeriv f) x = (torusOrder L f x : ℂ) :=
  residue_logDeriv_eq_untopD (hf.1 _)

lemma finite_support_torusResidue {f : ℂ → ℂ} (hf : IsEllipticFunction L f) :
    (Function.support (torusResidue L f)).Finite := by
  refine (finite_image_singularSet L hf.1 hf.2).subset ?_
  intro x hx
  refine ⟨x.out, fun ha ↦ hx (residue_eq_zero_of_analyticAt ha), QuotientAddGroup.out_eq' x⟩

lemma finite_support_torusOrder {f : ℂ → ℂ} (hf : IsEllipticFunction L f) :
    (Function.support (torusOrder L f)).Finite := by
  refine (finite_support_torusResidue (isEllipticFunction_logDeriv hf)).subset ?_
  intro x hx
  simp only [Function.mem_support, torusResidue_logDeriv hf] at hx ⊢
  exact_mod_cast hx

theorem finsum_torusOrder_eq_zero {f : ℂ → ℂ} (hf : IsEllipticFunction L f) :
    ∑ᶠ x : Torus L, torusOrder L f x = 0 := by
  have h := finsum_torusResidue_eq_zero (isEllipticFunction_logDeriv hf)
  simp_rw [torusResidue_logDeriv hf] at h
  have hc := (Int.castAddHom ℂ).map_finsum (finite_support_torusOrder hf)
  simp only [Int.coe_castAddHom] at hc
  rw [← hc] at h
  exact_mod_cast h

variable (L) in

def degree (f : ℂ → ℂ) : ℕ :=
  ∑ᶠ x : Torus L, (-torusOrder L f x).toNat

lemma toNat_neg_untopD_sub_const {f : ℂ → ℂ} {z : ℂ} (hf : MeromorphicAt f z) (c : ℂ) :
    (-(meromorphicOrderAt (fun w ↦ f w - c) z).untopD 0).toNat =
      (-(meromorphicOrderAt f z).untopD 0).toNat := by
  have hc : MeromorphicAt (fun _ : ℂ ↦ -c) z := analyticAt_const.meromorphicAt
  have e : (fun w ↦ f w - c) = f + fun _ ↦ -c := by
    funext w; simp [sub_eq_add_neg]
  have hc0 : 0 ≤ meromorphicOrderAt (fun _ : ℂ ↦ -c) z := analyticAt_const.meromorphicOrderAt_nonneg
  rw [e]
  by_cases hneg : meromorphicOrderAt f z < 0
  · rw [meromorphicOrderAt_add_eq_left_of_lt hc (hneg.trans_le hc0)]
  · push Not at hneg
    have h1 : 0 ≤ meromorphicOrderAt (f + fun _ ↦ -c) z :=
      le_trans (le_min hneg hc0) (meromorphicOrderAt_add hf hc)
    have key : ∀ o : WithTop ℤ, 0 ≤ o → (-(o.untopD 0)).toNat = 0 := by
      intro o ho
      induction o with
      | top => simp
      | coe n =>
        simp only [WithTop.untopD_coe]
        have : (0 : ℤ) ≤ n := by exact_mod_cast ho
        omega
    rw [key _ h1, key _ hneg]

lemma nonneg_of_toNat_neg_untopD_eq_zero {o : WithTop ℤ} (h : (-(o.untopD 0)).toNat = 0) :
    0 ≤ o := by
  induction o with
  | top => exact le_top
  | coe n =>
    simp only [WithTop.untopD_coe] at h
    exact_mod_cast (by omega : (0 : ℤ) ≤ n)

lemma toNat_neg_untopD_eq_zero_of_nonneg {o : WithTop ℤ} (h : 0 ≤ o) :
    (-(o.untopD 0)).toNat = 0 := by
  induction o with
  | top => simp
  | coe n =>
    simp only [WithTop.untopD_coe]
    have : (0 : ℤ) ≤ n := by exact_mod_cast h
    omega

lemma eq_neg_one_of_toNat_neg_untopD_eq_one {o : WithTop ℤ} (h : (-(o.untopD 0)).toNat = 1) :
    o = ((-1 : ℤ) : WithTop ℤ) := by
  induction o with
  | top => simp at h
  | coe n =>
    simp only [WithTop.untopD_coe] at h
    have : n = -1 := by omega
    rw [this]

lemma eventually_nhdsNE_of_eventually_codiscrete {p : ℂ → Prop} (h : ∀ᶠ z in codiscrete ℂ, p z)
    (x : ℂ) : ∀ᶠ z in 𝓝[≠] x, p z := by
  rw [Filter.Eventually, codiscrete, mem_codiscreteWithin] at h
  have := disjoint_principal_right.1 (h x (mem_univ x))
  filter_upwards [this] with z hz
  by_contra hpz
  exact hz ⟨mem_univ z, hpz⟩

lemma finite_support_toNat_neg_torusOrder {f : ℂ → ℂ} (hf : IsEllipticFunction L f) :
    (Function.support fun x ↦ (-torusOrder L f x).toNat).Finite :=
  (finite_support_torusOrder hf).subset fun x hx ↦ by
    simp only [Function.mem_support] at hx ⊢
    omega

theorem finsum_toNat_torusOrder_sub_const {f : ℂ → ℂ} (hf : IsEllipticFunction L f) (c : ℂ) :
    ∑ᶠ x : Torus L, (torusOrder L (fun z ↦ f z - c) x).toNat = degree L f := by
  classical
  have hg : IsEllipticFunction L (fun z ↦ f z - c) := by
    refine ⟨fun z ↦ ?_, fun z l hl ↦ by simp only [hf.2 z l hl]⟩
    have := hf.1 z
    fun_prop
  set g : ℂ → ℂ := fun z ↦ f z - c with hgdef
  have hfin := finite_support_torusOrder hg
  set s := hfin.toFinset with hs
  have hsupp : Function.support (torusOrder L g) ⊆ ↑s := by simp [hs]
  have hsum := finsum_torusOrder_eq_zero hg
  rw [finsum_eq_sum_of_support_subset _ hsupp] at hsum
  have h1 : ∑ᶠ x, (torusOrder L g x).toNat = ∑ x ∈ s, (torusOrder L g x).toNat :=
    finsum_eq_sum_of_support_subset _ fun x hx ↦ hsupp (by
      simp only [Function.mem_support] at hx ⊢
      omega)
  have hpt : ∀ x, (-torusOrder L f x).toNat = (-torusOrder L g x).toNat := fun x ↦
    (toNat_neg_untopD_sub_const (hf.1 _) c).symm
  have h2 : degree L f = ∑ x ∈ s, (-torusOrder L g x).toNat := by
    rw [degree]
    simp_rw [hpt]
    exact finsum_eq_sum_of_support_subset _ fun x hx ↦ hsupp (by
      simp only [Function.mem_support] at hx ⊢
      omega)
  rw [h1, h2]
  have key : ∀ x, ((torusOrder L g x).toNat : ℤ) - ((-torusOrder L g x).toNat : ℤ) =
      torusOrder L g x := fun x ↦ Int.toNat_sub_toNat_neg _
  have : ((∑ x ∈ s, (torusOrder L g x).toNat : ℕ) : ℤ) =
      ((∑ x ∈ s, (-torusOrder L g x).toNat : ℕ) : ℤ) := by
    push_cast
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
    simp only [key]
    exact hsum
  exact_mod_cast this

theorem finsum_toNat_torusOrder_eq_degree {f : ℂ → ℂ} (hf : IsEllipticFunction L f) :
    ∑ᶠ x : Torus L, (torusOrder L f x).toNat = degree L f := by
  simpa using finsum_toNat_torusOrder_sub_const hf 0

lemma eq_zero_of_finsum_eq_zero_nat {α : Type*} {u : α → ℕ} (hu : (Function.support u).Finite)
    (h : ∑ᶠ x, u x = 0) (x : α) : u x = 0 := by
  classical
  by_contra hx
  rw [finsum_eq_sum_of_support_subset u (s := hu.toFinset) (by simp)] at h
  exact hx ((Finset.sum_eq_zero_iff.1 h) x (by simpa using hx))

theorem degree_eq_zero_iff {f : ℂ → ℂ} (hf : IsEllipticFunction L f) :
    degree L f = 0 ↔ ∃ c : ℂ, f =ᶠ[codiscrete ℂ] fun _ ↦ c := by
  constructor
  · intro h0
    have hall := eq_zero_of_finsum_eq_zero_nat (finite_support_toNat_neg_torusOrder hf) h0
    apply exists_eventuallyEq_const_of_meromorphicOrderAt_nonneg L hf.1 hf.2
    intro z
    have := hall (Torus.mk L z)
    rw [torusOrder_mk hf] at this
    exact nonneg_of_toNat_neg_untopD_eq_zero this
  · rintro ⟨c, hc⟩
    rw [degree]
    have : ∀ x : Torus L, (-torusOrder L f x).toNat = 0 := by
      intro x
      apply toNat_neg_untopD_eq_zero_of_nonneg
      rw [meromorphicOrderAt_congr (eventually_nhdsNE_of_eventually_codiscrete hc x.out)]
      exact analyticAt_const.meromorphicOrderAt_nonneg
    simp [this]

theorem degree_ne_one {f : ℂ → ℂ} (hf : IsEllipticFunction L f) : degree L f ≠ 1 := by
  classical
  intro h1
  set u : Torus L → ℕ := fun x ↦ (-torusOrder L f x).toNat with hu
  have hfin : (Function.support u).Finite := finite_support_toNat_neg_torusOrder hf
  set s := hfin.toFinset with hs
  have hsum : ∑ x ∈ s, u x = 1 := by
    rw [← finsum_eq_sum_of_support_subset u (by simp [hs])]
    exact h1
  obtain ⟨x₀, hx₀s, hx₀⟩ : ∃ x₀ ∈ s, u x₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    rw [Finset.sum_eq_zero hcon] at hsum
    exact zero_ne_one hsum
  have hsplit := Finset.add_sum_erase s u hx₀s
  rw [hsum] at hsplit
  have hux₀ : u x₀ = 1 := by omega
  have hrest : ∀ x, x ≠ x₀ → u x = 0 := by
    intro x hx
    by_cases hxs : x ∈ s
    · have h0 : ∑ y ∈ s.erase x₀, u y = 0 := by omega
      exact Finset.sum_eq_zero_iff.1 h0 x (Finset.mem_erase.2 ⟨hx, hxs⟩)
    · simpa [hs] using hxs
  have hres := finsum_torusResidue_eq_zero hf
  rw [finsum_eq_single _ x₀ (fun x hx ↦ ?_)] at hres
  · have hord := eq_neg_one_of_toNat_neg_untopD_eq_one hux₀
    exact residue_ne_zero_of_meromorphicOrderAt_eq_neg_one (hf.1 _) hord hres
  · exact residue_eq_zero_of_meromorphicOrderAt_nonneg (hf.1 _)
      (nonneg_of_toNat_neg_untopD_eq_zero (hrest x hx))

theorem degree_weierstrassP : degree L ℘[L] = 2 := by
  have hP : IsEllipticFunction L ℘[L] := isEllipticFunction_weierstrassP
  have h0 : (0 : Torus L) = Torus.mk L 0 := (QuotientAddGroup.mk_zero _).symm
  rw [degree, finsum_eq_single _ (0 : Torus L) ?_]
  · rw [h0, torusOrder_mk hP]
    have h2 : meromorphicOrderAt ℘[L] 0 = ((-2 : ℤ) : WithTop ℤ) := by
      rw [L.order_weierstrassP 0 (zero_mem _)]
      norm_num
    rw [h2, WithTop.untopD_coe]
    rfl
  · intro x hx
    obtain ⟨z, rfl⟩ := Torus.mk_surjective L x
    have hz : z ∉ L.lattice := fun h ↦ hx (by
      rw [h0]
      exact (Torus.mk_eq_mk_iff L).2 (by simpa using h))
    rw [torusOrder_mk hP]
    exact toNat_neg_untopD_eq_zero_of_nonneg
      (L.analyticOnNhd_weierstrassP z hz).meromorphicOrderAt_nonneg

end Elliptic
end GroundTheory.Global
