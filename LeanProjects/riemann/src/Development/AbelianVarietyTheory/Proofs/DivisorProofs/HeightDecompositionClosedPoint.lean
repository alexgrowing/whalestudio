import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueLiesUnder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HtTrivAndNefIff

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O

namespace GlobalTheory.Mean4O.HtComb

theorem finsum_rel {α ι : Type} [Fintype ι] {p : α → Prop} (hp : {y | p y}.Finite) (a l d : α → ℝ) (c : ι → α → ℝ)
    (q r : ℝ) (b : ι → ℝ) (h : ∀ y, p y → q * a y = l y + ∑ i, b i * c i y - r * d y) :
    q * ∑ᶠ (y) (_ : p y), a y =
      (∑ᶠ (y) (_ : p y), l y) + ∑ i, b i * (∑ᶠ (y) (_ : p y), c i y) - r * ∑ᶠ (y) (_ : p y), d y := by
  have e (f : α → ℝ) : ∑ᶠ (y) (_ : p y), f y = ∑ y ∈ hp.toFinset, f y := finsum_mem_eq_finite_toFinset_sum f hp
  simp only [e, Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun y hy => h y (hp.mem_toFinset.1 hy)

theorem finsum_log {α K : Type} [Field K] (w : K →* ℝ) (hw : ∀ a, a ≠ 0 → w a ≠ 0) {p : α → Prop}
    (hp : {y | p y}.Finite) (f : α → K) (hf : ∀ y, p y → f y ≠ 0) :
    ∑ᶠ (y : α) (_ : p y), Real.log (w (f y)) = Real.log (w (∏ᶠ (y : α) (_ : p y), f y)) := by
  have h₁ := finsum_mem_eq_finite_toFinset_sum (fun y => Real.log (w (f y))) hp
  have h₂ := finprod_mem_eq_finite_toFinset_prod f hp
  refine h₁.trans (Eq.trans ?_ (congrArg (fun a => Real.log (w a)) h₂).symm)
  rw [map_prod, Real.log_prod fun y hy => hw _ (hf y (hp.mem_toFinset.1 hy))]

theorem unitAt_quot {F : Type} [Field F] {Y : Var F} {ι : Type} [Fintype ι] (D : Y.Dv) (E : ι → Y.Dv) (q : ℕ)
    (b : ι → ℤ) (h : q • D = ∑ i, b i • E i) (x : Y.X) :
    UnitAt x (genAt D x ^ q / ∏ i, genAt (E i) x ^ b i) := by
  classical
  have h₁ : ∀ s : Finset ι, CartierDiv.IsEqn (∑ i ∈ s, b i • E i) x (∏ i ∈ s, eqn (E i) x ^ b i) := fun s => by
    induction s using Finset.induction_on with
    | empty => simpa using CartierDiv.isEqn_zero x
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      exact ((Base.isEqn_eqn (E a) x).zsmul (b a)).add ih
  have h₂ := (Base.isEqn_eqn D x).nsmul q
  have h₃ := h₁ Finset.univ
  rw [← h] at h₃
  have h₄ := h₂.iff_unitAt.1 h₃
  convert h₄ using 1
  simp [genAt, Finset.prod_inv_distrib, div_eq_mul_inv, mul_comm]

theorem main : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (M : Adl C Y) (ι : Type) [Fintype ι] (ρ : ι → Adl C Y) (t : ι → ℝ) (g : ∀ σ, Pts Y σ → ℝ), IsComb M ρ t g → (∀ i (y : AlgPt Y), {v : HeightOneSpectrum (𝓞 F) | ∃ e : TrueGeo.Ext v, (ρ i).lg v e y ≠ 0}.Finite) → ∀ x : Y.X, IsClosed ({x} : Set Y.X) → M.ht x = ∑ i, t i * (ρ i).ht x + (∑ σ : F →+* ℂ, ∑ᶠ (z : Pts Y σ) (_ : under z = x), g σ z) / ((Module.finrank ℚ F : ℝ) * (Nat.card {y : AlgPt Y // below y.1 = x} : ℝ)) := by
  intro F _ _ C Y M ι _ ρ t g ⟨q, b, hq, ht, hD, hi, hv⟩ hfs x hx
  have hu := unitAt_quot M.D (fun i => (ρ i).D) q b hD x
  set U : Y.Fn := genAt M.D x ^ q / ∏ i, genAt (ρ i).D x ^ b i with hU
  obtain ⟨N, hN, H⟩ := exists_finprod_valAt_eq F Y x hx _ hu
  have hfin : Finite {y : AlgPt Y // below y.1 = x} := (ExtConj.pts Y x hx).2
  obtain ⟨n, hn, hc⟩ := HtTwist.exists_card Y.str x hx
  have hA : Nat.card {y : AlgPt Y // below y.1 = x} = n := hc _ _
  let a (A : Adl C Y) (σ : F →+* ℂ) : ℝ := ∑ᶠ (z : Pts Y σ) (_ : under z = x), lnAdl A σ z
  let c (A : Adl C Y) (v : HeightOneSpectrum (𝓞 F)) : ℝ :=
    ∑ᶠ (y : AlgPt Y) (_ : below y.1 = x), A.lg v (Ext.instNonempty v).some y
  have hht (A : Adl C Y) : A.ht x = -((∑ σ, a A σ) + ∑ᶠ v, c A v) / (((A.n : ℕ) : ℝ) * (Module.finrank ℚ F : ℝ) * n) := by
    simp only [Adl.ht, dif_pos (Ext.instNonempty _), hA]
    congr 3
    refine Finset.sum_congr rfl fun σ _ => finsum_congr fun z => finsum_congr fun hz => ?_
    subst hz
    rfl
  have h₁ (σ : F →+* ℂ) : q * a M σ = Real.log ‖σ N‖ + ∑ i, b i * a (ρ i) σ -
      q * (M.n : ℕ) * ∑ᶠ (z : Pts Y σ) (_ : under z = x), g σ z := by
    obtain ⟨hf, hp⟩ := H ℂ σ
    have key := finsum_log (normHom : ℂ →*₀ ℝ).toMonoidHom (fun a ha => norm_ne_zero_iff.2 ha) hf
      (fun y => valAt y.1 U) fun y hy => (Base.valAt_zpow y.1 (hy ▸ hu)).1
    rw [hp] at key
    have := finsum_rel (p := fun z : Pts Y σ => under z = x) hf (lnAdl M σ) (fun z => Real.log ‖valAt z.1 U‖) (g σ)
      (fun i => lnAdl (ρ i) σ) q (q * (M.n : ℕ)) (fun i => b i) fun z hz => by
        rw [(hi σ z).2, TrivNef.ratVal_eq_valAt, hz]
    exact this.trans (congrArg (fun s => s + _ - _) key)
  have h₂ (v : HeightOneSpectrum (𝓞 F)) : q * c M v =
      Real.log (NumberField.HeightOneSpectrum.adicAbv F v N) + ∑ i, b i * c (ρ i) v := by
    obtain ⟨hf, hp⟩ := H (AlgebraicClosure F) (algebraMap F _)
    let e := (Ext.instNonempty v).some
    have key := finsum_log e.w.toMonoidHom (fun a ha => e.w.ne_zero ha) hf
      (fun y => valAt y.1 U) fun y hy => (Base.valAt_zpow y.1 (hy ▸ hu)).1
    rw [hp] at key
    have := finsum_rel (p := fun y : AlgPt Y => below y.1 = x) hf (M.lg v e) (fun y => Real.log (e.w (valAt y.1 U)))
      (fun _ => 0) (fun i => (ρ i).lg v e) q 0 (fun i => b i) fun y hy => by
        rw [hv v e y, hy, zero_mul, sub_zero]
    rw [zero_mul, sub_zero] at this
    exact this.trans (congrArg (fun s => s + _) (key.trans (congrArg Real.log (e.w_alg N))))
  have hs (i : ι) : (Function.support (c (ρ i))).Finite := by
    refine (Set.finite_iUnion fun y : {y : AlgPt Y // below y.1 = x} => hfs i y.1).subset fun v hv => ?_
    by_contra h
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_not, ne_eq] at h
    refine hv ?_
    simp only [c]
    rw [← finsum_subtype_eq_finsum_cond]
    simp [h]
  obtain ⟨hl, h₃⟩ := sum_log_embedding_add_finsum_log_adicAbv_eq_zero F N hN
  have hs' (i : ι) : (Function.support fun v => (b i : ℝ) * c (ρ i) v).Finite :=
    (hs i).subset fun v (hv : (b i : ℝ) * c (ρ i) v ≠ 0) (h0 : c (ρ i) v = 0) => hv (by rw [h0, mul_zero])
  have h₄ : q * ∑ᶠ v, c M v = (∑ᶠ v : HeightOneSpectrum (𝓞 F), Real.log (NumberField.HeightOneSpectrum.adicAbv F v N)) +
      ∑ i, b i * ∑ᶠ v, c (ρ i) v := by
    rw [mul_finsum]
    simp only [h₂, mul_finsum]
    rw [finsum_add_distrib hl, finsum_sum_comm _ _ fun i _ => hs' i]
    refine (Set.finite_iUnion hs').subset fun v hv => ?_
    by_contra h
    simp only [Set.mem_iUnion, Function.mem_support, not_exists, not_not, ne_eq] at h
    exact hv (Finset.sum_eq_zero fun i _ => h i)
  have h₅ : q * ∑ σ, a M σ = (∑ σ : F →+* ℂ, Real.log ‖σ N‖) + ∑ i, b i * (∑ σ, a (ρ i) σ) -
      q * (M.n : ℕ) * ∑ σ : F →+* ℂ, ∑ᶠ (z : Pts Y σ) (_ : under z = x), g σ z := by
    simp only [Finset.mul_sum, h₁]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_comm]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hF : (Module.finrank ℚ F : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have hm (A : Adl C Y) : ((A.n : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 A.n.ne_zero
  have hq' : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hq.ne'
  have h₆ (i : ι) : (q : ℝ) * (M.n : ℕ) * (Module.finrank ℚ F : ℝ) * n * (t i * (ρ i).ht x) =
      -(b i * (∑ σ, a (ρ i) σ)) - b i * ∑ᶠ v, c (ρ i) v := by
    have := hm (ρ i)
    calc _ = ((q : ℝ) * (M.n : ℕ) * t i) * ((Module.finrank ℚ F : ℝ) * n * (ρ i).ht x) := by ring
      _ = _ := by
        rw [ht i, hht]
        field_simp
        ring
  have hM := hm M
  refine mul_left_cancel₀ (a := (q : ℝ) * (M.n : ℕ) * (Module.finrank ℚ F : ℝ) * n) (by positivity) ?_
  rw [mul_add, Finset.mul_sum, hA]
  simp only [h₆, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  rw [hht M]
  have e₁ (s : ℝ) : (q : ℝ) * (M.n : ℕ) * (Module.finrank ℚ F : ℝ) * n *
      (s / (((M.n : ℕ) : ℝ) * (Module.finrank ℚ F : ℝ) * n)) = q * s := by field_simp
  have e₂ (s : ℝ) : (q : ℝ) * (M.n : ℕ) * (Module.finrank ℚ F : ℝ) * n *
      (s / ((Module.finrank ℚ F : ℝ) * n)) = q * (M.n : ℕ) * s := by field_simp
  rw [e₁, e₂]
  linear_combination -h₄ - h₅ - h₃

end GlobalTheory.Mean4O.HtComb
