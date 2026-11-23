import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValAtEqOfResidueFieldHom
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumLogEmbeddingAddFinsumLogAdicAbvEqZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinsumSubConst
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HtTrivAndNefIff

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar Formalism.BasicNotions GlobalTheory.TrueGeo

namespace GlobalTheory.TrueGeo.HtEvalUp

theorem le_mul_finsum_cond {α : Type} {p : α → Prop} {d : ℕ} (hd : Nat.card {y // p y} = d) (hd0 : d ≠ 0)
    (r c : ℝ) (f g : α → ℝ) (h : ∀ y, p y → c + g y ≤ r * f y) :
    (d : ℝ) * c + ∑ᶠ (y) (_ : p y), g y ≤ r * ∑ᶠ (y) (_ : p y), f y := by
  have : Finite {y // p y} := Nat.finite_of_card_ne_zero (hd ▸ hd0)
  letI := Fintype.ofFinite {y // p y}
  rw [← finsum_subtype_eq_finsum_cond, ← finsum_subtype_eq_finsum_cond, finsum_eq_sum_of_fintype,
    finsum_eq_sum_of_fintype, ← hd, Nat.card_eq_fintype_card, Finset.mul_sum]
  calc (Fintype.card {y // p y} : ℝ) * c + ∑ i : {y // p y}, g i = ∑ i : {y // p y}, (c + g i) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    _ ≤ _ := Finset.sum_le_sum fun i _ => h i.1 i.2

theorem finsum_le_finsum_of_finite {α : Type} {f g : α → ℝ} (hf : (Function.support f).Finite)
    (hg : (Function.support g).Finite) (h : ∀ a, f a ≤ g a) : ∑ᶠ a, f a ≤ ∑ᶠ a, g a := by
  classical
  rw [finsum_eq_sum_of_support_subset f (s := (hf.union hg).toFinset) (by intro a ha; simp [ha]),
    finsum_eq_sum_of_support_subset g (s := (hf.union hg).toFinset) (by intro a ha; simp [ha])]
  exact Finset.sum_le_sum fun a _ => h a

theorem main : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y) (k : ℕ+) (x : Y.X),
    IsClosed ({x} : Set Y.X) →
    (∀ y : AlgPt Y, below y.1 = x → {v : HeightOneSpectrum (𝓞 F) | ∃ e : Ext v, A.lg v e y ≠ 0}.Finite) →
    ∀ s : Y.Fn, ((k : ℕ) • A.D).GeneratesAt x s →
    ∀ (α : (F →+* ℂ) → ℝ) (β : HeightOneSpectrum (𝓞 F) → ℝ), (Function.support β).Finite →
    (∀ (σ : F →+* ℂ) (z : Pts Y σ), under z = x →
      Real.exp (-(2 * α σ)) ≤ C.pn Y σ _ (C.mPow Y σ A.D (k : ℕ) (A.m σ)) (C.cx Y σ s) z) →
    (∀ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (y : AlgPt Y), below y.1 = x →
      Real.exp (-β v) ≤ e.w (valAt y.1 (s * (eqn A.D x : Y.Fn) ^ (k : ℕ))) * Real.exp ((k : ℕ) * A.lg v e y)) →
    A.ht x ≤ (∑ σ : F →+* ℂ, (α σ + (k : ℕ) * (A.n : ℕ) * A.ci (InfinitePlace.mk σ)) + ∑ᶠ v, β v) /
      ((k : ℕ) * (A.n : ℕ) * (Module.finrank ℚ F : ℝ)) := by
  intro F _ _ C Y A k x hx hlg s hs α β hβ hα hβv
  classical
  have hE : A.D.IsEqn x (eqn A.D x) := Base.isEqn_eqn A.D x
  have hEk : ((k : ℕ) • A.D).IsEqn x (eqn A.D x ^ (k : ℕ)) := hE.nsmul _
  have hu : UnitAt x (s * (eqn A.D x : Y.Fn) ^ (k : ℕ)) := by
    have := hEk.generatesAt_iff.1 hs
    simpa [Units.val_pow_eq_pow_val] using this
  obtain ⟨d, hd0, hc⟩ := HtTwist.exists_card Y.str x hx
  obtain ⟨N, hN, H⟩ := exists_finprod_valAt_eq F Y x hx _ hu
  have hk : (0 : ℝ) < ((k : ℕ) : ℝ) := Nat.cast_pos.2 k.pos

  have hArch (σ : F →+* ℂ) : (d : ℝ) * (-(α σ + (k : ℕ) * (A.n : ℕ) * A.ci (InfinitePlace.mk σ))) +
      -Real.log ‖σ N‖ ≤ ((k : ℕ) : ℝ) * ∑ᶠ (z : Pts Y σ) (_ : under z = x),
        (Real.log (C.pn Y σ A.D (A.m σ) (C.cx Y σ ((eqn A.D x)⁻¹ : Y.Fnˣ)) z) / 2 -
          (A.n : ℕ) * A.ci (InfinitePlace.mk σ)) := by
    obtain ⟨hf, hp⟩ := H ℂ σ
    have key := TrivNef.finsum_neg_log (normHom : ℂ →*₀ ℝ).toMonoidHom (fun a ha => norm_ne_zero_iff.2 ha) hf
      (fun y => valAt y.1 (s * (eqn A.D x : Y.Fn) ^ (k : ℕ))) fun y hy => (Base.valAt_zpow y.1 (hy ▸ hu)).1
    rw [hp] at key
    have key' : ∑ᶠ (z : Pts Y σ) (_ : under z = x), -Real.log ‖valAt z.1 (s * (eqn A.D x : Y.Fn) ^ (k : ℕ))‖ =
        -Real.log ‖σ N‖ := key
    rw [← key']
    refine le_mul_finsum_cond (hc ℂ σ) hd0 _ _ _ _ fun z hz => ?_
    have hz' : below z.1 = x := hz
    have hz2 : under z = x := hz
    have hGz : valAt z.1 (s * (eqn A.D x : Y.Fn) ^ (k : ℕ)) ≠ 0 := (Base.valAt_zpow z.1 (hz' ▸ hu)).1
    have hsplit : s = s * (eqn A.D x : Y.Fn) ^ (k : ℕ) * (((eqn A.D x)⁻¹ : Y.Fnˣ) : Y.Fn) ^ (k : ℕ) := by
      rw [mul_assoc, ← mul_pow, Units.mul_inv, one_pow, mul_one]
    have hgen : A.D.GeneratesAt (under z) (((eqn A.D x)⁻¹ : Y.Fnˣ) : Y.Fn) := by
      rw [hz2, Units.val_inv_eq_inv_val]; exact CartierDiv.isEqn_iff_generatesAt_inv.1 hE
    have hreg : ((k : ℕ) • A.D).RegularAt (under z) ((((eqn A.D x)⁻¹ : Y.Fnˣ) : Y.Fn) ^ (k : ℕ)) := by
      rw [hz2]
      convert (CartierDiv.isEqn_iff_generatesAt_inv.1 hEk).regularAt using 1
      simp [Units.val_pow_eq_pow_val, inv_pow]
    have hGreg : RegAt (under z) (s * (eqn A.D x : Y.Fn) ^ (k : ℕ)) := by rw [hz2]; exact hu.regAt
    have hpn : C.pn Y σ _ (C.mPow Y σ A.D (k : ℕ) (A.m σ)) (C.cx Y σ s) z =
        ‖valAt z.1 (s * (eqn A.D x : Y.Fn) ^ (k : ℕ))‖ ^ 2 *
          C.pn Y σ A.D (A.m σ) (C.cx Y σ ((eqn A.D x)⁻¹ : Y.Fnˣ)) z ^ (k : ℕ) := by
      conv_lhs => rw [hsplit]
      rw [C.pn_mul Y σ _ _ _ _ z hGreg hreg, C.pn_mPow Y σ A.D (k : ℕ) (A.m σ) _ z hgen, TrivNef.ratVal_eq_valAt]
    have hh := hα σ z hz
    rw [hpn] at hh
    have hP0 := C.pn_nonneg Y σ A.D (A.m σ) (C.cx Y σ ((eqn A.D x)⁻¹ : Y.Fnˣ)) z
    have ha : 0 < ‖valAt z.1 (s * (eqn A.D x : Y.Fn) ^ (k : ℕ))‖ := norm_pos_iff.2 hGz
    have hP : 0 < C.pn Y σ A.D (A.m σ) (C.cx Y σ ((eqn A.D x)⁻¹ : Y.Fnˣ)) z := by
      rcases hP0.lt_or_eq with h | h
      · exact h
      · exfalso
        rw [← h, zero_pow (PNat.ne_zero k), mul_zero] at hh
        exact absurd hh (not_le.2 (Real.exp_pos _))
    have hl := Real.log_le_log (Real.exp_pos _) hh
    rw [Real.log_exp, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at hl
    simp only [Nat.cast_ofNat] at hl
    have e : ((k : ℕ) : ℝ) * (Real.log (C.pn Y σ A.D (A.m σ) (C.cx Y σ ((eqn A.D x)⁻¹ : Y.Fnˣ)) z) / 2 -
        (A.n : ℕ) * A.ci (InfinitePlace.mk σ)) = ((k : ℕ) : ℝ) * Real.log (C.pn Y σ A.D (A.m σ)
          (C.cx Y σ ((eqn A.D x)⁻¹ : Y.Fnˣ)) z) / 2 - (k : ℕ) * (A.n : ℕ) * A.ci (InfinitePlace.mk σ) := by ring
    rw [e]
    linarith

  have hA : Nat.card {y : AlgPt Y // below y.1 = x} = d := hc _ _
  have hFin (v : HeightOneSpectrum (𝓞 F)) : (d : ℝ) * (-β v) + -Real.log (NumberField.HeightOneSpectrum.adicAbv F v N) ≤
      ((k : ℕ) : ℝ) * ∑ᶠ (y : AlgPt Y) (_ : below y.1 = x), A.lg v (Ext.instNonempty v).some y := by
    obtain ⟨hf, hp⟩ := H (AlgebraicClosure F) (algebraMap F _)
    have key := TrivNef.finsum_neg_log (Ext.instNonempty v).some.w.toMonoidHom
      (fun a ha => (Ext.instNonempty v).some.w.ne_zero ha) hf
      (fun y => valAt y.1 (s * (eqn A.D x : Y.Fn) ^ (k : ℕ))) fun y hy => (Base.valAt_zpow y.1 (hy ▸ hu)).1
    rw [hp] at key
    have key' : ∑ᶠ (y : AlgPt Y) (_ : below y.1 = x),
        -Real.log ((Ext.instNonempty v).some.w (valAt y.1 (s * (eqn A.D x : Y.Fn) ^ (k : ℕ)))) =
        -Real.log (NumberField.HeightOneSpectrum.adicAbv F v N) :=
      key.trans (congrArg (fun a => -Real.log a) ((Ext.instNonempty v).some.w_alg N))
    rw [← key']
    refine le_mul_finsum_cond hA hd0 _ _ _ _ fun y hy => ?_
    have h1 := hβv v (Ext.instNonempty v).some y hy
    have hw : 0 < (Ext.instNonempty v).some.w (valAt y.1 (s * (eqn A.D x : Y.Fn) ^ (k : ℕ))) :=
      (Ext.instNonempty v).some.w.pos (Base.valAt_zpow y.1 (hy ▸ hu)).1
    have hl := Real.log_le_log (Real.exp_pos _) h1
    rw [Real.log_exp, Real.log_mul hw.ne' (Real.exp_pos _).ne', Real.log_exp] at hl
    linarith

  have hfin : Finite {y : AlgPt Y // below y.1 = x} := Nat.finite_of_card_ne_zero (hA ▸ hd0)
  have hS : (Function.support fun v : HeightOneSpectrum (𝓞 F) =>
      ∑ᶠ (y : AlgPt Y) (_ : below y.1 = x), A.lg v (Ext.instNonempty v).some y).Finite := by
    refine (Set.finite_iUnion fun y : {y : AlgPt Y // below y.1 = x} => hlg y.1 y.2).subset fun v hv => ?_
    by_contra hn
    apply hv
    refine finsum_eq_zero_of_forall_eq_zero fun y => ?_
    rw [finsum_eq_if]
    split_ifs with hy
    · by_contra h0
      exact hn (Set.mem_iUnion.2 ⟨⟨y, hy⟩, ⟨_, h0⟩⟩)
    · rfl
  obtain ⟨hPF1, hPF2⟩ := sum_log_embedding_add_finsum_log_adicAbv_eq_zero F N hN
  have hb1 : (Function.support fun v => (d : ℝ) * (-β v)).Finite := hβ.subset fun v hv h0 => hv (by simp [h0])
  have hb2 : (Function.support fun v => -Real.log (NumberField.HeightOneSpectrum.adicAbv F v N)).Finite :=
    hPF1.subset fun v hv h0 => hv (by simp [h0])
  have hb3 : (Function.support fun v => (d : ℝ) * (-β v) +
      -Real.log (NumberField.HeightOneSpectrum.adicAbv F v N)).Finite :=
    (hb1.union hb2).subset (Function.support_add _ _)
  have hb4 : (Function.support fun v => ((k : ℕ) : ℝ) *
      ∑ᶠ (y : AlgPt Y) (_ : below y.1 = x), A.lg v (Ext.instNonempty v).some y).Finite :=
    hS.subset fun v hv h0 => hv (by simp [h0])
  have hFsum := finsum_le_finsum_of_finite hb3 hb4 hFin
  rw [finsum_add_distrib hb1 hb2, ← mul_finsum, ← mul_finsum, finsum_neg_distrib, finsum_neg_distrib] at hFsum
  have hAsum := Finset.sum_le_sum fun σ (_ : σ ∈ Finset.univ) => hArch σ
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_neg_distrib,
    Finset.sum_neg_distrib] at hAsum
  have hdite : (∑ᶠ v : HeightOneSpectrum (𝓞 F), if h : Nonempty (Ext v) then
      ∑ᶠ (y : AlgPt Y) (_ : below y.1 = x), A.lg v h.some y else 0) =
      ∑ᶠ v : HeightOneSpectrum (𝓞 F), ∑ᶠ (y : AlgPt Y) (_ : below y.1 = x), A.lg v (Ext.instNonempty v).some y :=
    finsum_congr fun v => dif_pos (Ext.instNonempty v)
  have hn : (0 : ℝ) < ((A.n : ℕ) : ℝ) := Nat.cast_pos.2 A.n.pos
  have hF : (0 : ℝ) < (Module.finrank ℚ F : ℝ) := Nat.cast_pos.2 Module.finrank_pos
  have hd : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hd0)
  rw [Adl.ht, hdite, hA, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos hn hF]

end GlobalTheory.TrueGeo.HtEvalUp
