import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAlgAtlasAtlasOf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MSmoothOfWeightIffIsCInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogNormUnitLocallyHarmonic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitAtOfDivisorRelation
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.Mean4O GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.CxPts
open Filter Topology
open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LeviRelation

section Values

variable {F : Type} [Field F] {Y : Var F} {σ : F →+* ℂ}

theorem ratVal_zpow {y : Pts Y σ} {f : Y.Fn} (h : UnitAt (under y) f) (n : ℤ) :
    ratVal (f ^ n) y = ratVal f y ^ n := by
  have hpow : ∀ m : ℕ, ratVal (f ^ m) y = ratVal f y ^ m := by
    intro m
    induction m with
    | zero => simp [Base.ratVal_one]
    | succ m ih => rw [pow_succ, ratVal_mul (GlobalTheory.CombUnit.unitAt_pow h m).regAt h.regAt, ih, pow_succ]
  have hinv : ∀ g : Y.Fn, UnitAt (under y) g → ratVal g⁻¹ y = (ratVal g y)⁻¹ := by
    intro g hg
    have e := ratVal_mul (y := y) hg.regAt hg.inv.regAt
    rw [mul_inv_cancel₀ hg.ne_zero, Base.ratVal_one] at e
    exact eq_inv_of_mul_eq_one_right e.symm
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · rw [zpow_natCast, zpow_natCast, hpow]
  · rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, hinv _ (GlobalTheory.CombUnit.unitAt_pow h m), hpow]

theorem ratVal_prod {ι : Type} (s : Finset ι) {y : Pts Y σ} (u : ι → Y.Fn)
    (h : ∀ i ∈ s, UnitAt (under y) (u i)) : ratVal (∏ i ∈ s, u i) y = ∏ i ∈ s, ratVal (u i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Base.ratVal_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      ratVal_mul (h a (Finset.mem_insert_self a s)).regAt
        (GlobalTheory.CombUnit.unitAt_prod s u fun i hi => h i (Finset.mem_insert_of_mem hi)).regAt,
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

end Values

theorem levi_sum_mul {ι κ : Type} [Fintype κ] (s : Finset ι) (c : ι → ℝ) (ψ : ι → (κ → ℂ) → ℝ)
    {y : κ → ℂ} (hψ : ∀ i ∈ s, ContDiffAt ℝ 2 (ψ i) y) (w : κ → ℂ) :
    levi (fun v => ∑ i ∈ s, c i * ψ i v) y w = ∑ i ∈ s, c i * levi (ψ i) y w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [levi]
  | insert a s ha ih =>
    have hs : ContDiffAt ℝ 2 (fun v => ∑ i ∈ s, c i * ψ i v) y :=
      ContDiffAt.sum fun i hi => contDiffAt_const.mul (hψ i (Finset.mem_insert_of_mem hi))
    have e : (fun v => ∑ i ∈ insert a s, c i * ψ i v) =
        fun v => (∑ i ∈ s, c i * ψ i v) + c a * ψ a v := by
      funext v; rw [Finset.sum_insert ha]; ring
    rw [e, levi_add_smul (c a) hs (hψ a (Finset.mem_insert_self a s)),
      ih fun i hi => hψ i (Finset.mem_insert_of_mem hi), Finset.sum_insert ha]
    ring

section Norms

variable {F : Type} [Field F] [NumberField F] {Y : Var F} {σ : F →+* ℂ} {C : CxSt F}

theorem neg_lnN_genAt {Δ : Y.Dv} (m : C.Met Y σ Δ) {f : Y.Fn} {y : Pts Y σ}
    (hf : Δ.GeneratesAt (under y) f) (hp : PosAt m y) :
    -lnN m (genAt Δ (under y)) y =
      -lnN m f y + Real.log ‖ratVal (f * (eqn Δ (under y) : Y.Fn)) y‖ := by
  have hu : UnitAt (under y) (f * (eqn Δ (under y) : Y.Fn)) :=
    (Base.isEqn_eqn Δ (under y)).generatesAt_iff.1 hf
  have e : C.pn Y σ Δ m (C.cx Y σ f) y =
      ‖ratVal (f * (eqn Δ (under y) : Y.Fn)) y‖ ^ 2 * C.pn Y σ Δ m (C.cx Y σ (genAt Δ (under y))) y := by
    rw [← C.pn_mul Y σ Δ m _ _ y hu.regAt (generatesAt_genAt Δ _).regularAt]
    congr 2
    simp [genAt]
  have hn : ‖ratVal (f * (eqn Δ (under y) : Y.Fn)) y‖ ≠ 0 := norm_ne_zero_iff.2 (ratVal_ne_zero hu)
  unfold PosAt at hp
  simp only [lnN]
  rw [e, Real.log_mul (pow_ne_zero 2 hn) (ne_of_gt hp), Real.log_pow]
  push_cast
  ring

end Norms

end GlobalTheory.LeviRelation

namespace GlobalTheory.LeviRelation

section Local

variable {F : Type} [Field F] [NumberField F] {Y : Var F} {e : ℕ} {M : Man e} (I : ManIs M Y)
  (a : Fin (M.n + 1)) {ι : Type} [Fintype ι] (Δ : ι → Y.Dv) (m : ∀ i, (cxSt F).Met Y (I.ε a) (Δ i))
  (k : ι → ℤ)

def relFun (p : M.X a) : ℝ :=
  ∑ i, (k i : ℝ) * (-lnN (m i) (genAt (Δ i) (under (I.pt a p))) (I.pt a p)) +
    Real.log ‖ratVal (∏ i, (genAt (Δ i) (under (I.pt a p)) : Y.Fn) ^ k i) (I.pt a p)‖

theorem relFun_local (Q : ι → LocPot (M.X a)) (hQ : ∀ i, IsPot (I.pt a) (m i) (Q i))
    (hrel : ∑ i, k i • Δ i = 0) (z : M.X a) :
    ∃ u : Y.Fn, ∀ p ∈ ⋂ i, (Q i).U z, UnitAt (under (I.pt a p)) u ∧
      relFun I a Δ m k p = ∑ i, (k i : ℝ) * (Q i).φ z p + Real.log ‖ratVal u (I.pt a p)‖ := by
  choose f hf using fun i => hQ i z
  refine ⟨∏ i, f i ^ k i, fun p hp => ?_⟩
  have hp' : ∀ i, p ∈ (Q i).U z := Set.mem_iInter.1 hp
  set y := I.pt a p
  set x := under y
  have hfi := fun i => hf i p (hp' i)
  have hui : ∀ i, UnitAt x (f i * (eqn (Δ i) x : Y.Fn)) := fun i =>
    (Base.isEqn_eqn (Δ i) x).generatesAt_iff.1 (hfi i).1
  have hE0 := GlobalTheory.CombUnit.isEqn_sum Finset.univ Δ k (fun i => eqn (Δ i) x) fun i _ => Base.isEqn_eqn (Δ i) x
  rw [hrel] at hE0
  have hEu := (CartierDiv.isEqn_zero x).iff_unitAt.1 hE0
  set E : Y.Fn := ∏ i, (eqn (Δ i) x : Y.Fn) ^ k i with hEdef
  have hE : UnitAt x E := by
    simpa [E, Units.coe_prod, Units.val_zpow_eq_zpow_val] using hEu
  have hP : (∏ i, (genAt (Δ i) x : Y.Fn) ^ k i) = E⁻¹ := by
    simp [E, genAt, Units.val_inv_eq_inv_val, inv_zpow, Finset.prod_inv_distrib]
  have hEne : E ≠ 0 := hE.ne_zero
  have hu : (∏ i, f i ^ k i) = E⁻¹ * ∏ i, (f i * (eqn (Δ i) x : Y.Fn)) ^ k i := by
    rw [Finset.prod_congr rfl fun i _ => mul_zpow (f i) _ (k i), Finset.prod_mul_distrib, ← hEdef]
    field_simp
  have hUall : ∀ i ∈ Finset.univ, UnitAt x ((f i * (eqn (Δ i) x : Y.Fn)) ^ k i) :=
    fun i _ => GlobalTheory.CombUnit.unitAt_zpow (hui i) (k i)
  have hUprod := GlobalTheory.CombUnit.unitAt_prod Finset.univ _ hUall
  refine ⟨hu ▸ hE.inv.mul hUprod, ?_⟩
  have hne : ∀ i, ratVal (f i * (eqn (Δ i) x : Y.Fn)) y ≠ 0 := fun i => ratVal_ne_zero (hui i)
  have hv : ratVal (∏ i, f i ^ k i) y =
      ratVal E⁻¹ y * ∏ i, ratVal (f i * (eqn (Δ i) x : Y.Fn)) y ^ k i := by
    rw [hu, ratVal_mul hE.inv.regAt hUprod.regAt, ratVal_prod _ _ hUall]
    congr 1
    exact Finset.prod_congr rfl fun i _ => ratVal_zpow (hui i) (k i)
  have hEv : ratVal E⁻¹ y ≠ 0 := ratVal_ne_zero hE.inv
  have hlog : Real.log ‖ratVal (∏ i, f i ^ k i) y‖ = Real.log ‖ratVal E⁻¹ y‖ +
      ∑ i, (k i : ℝ) * Real.log ‖ratVal (f i * (eqn (Δ i) x : Y.Fn)) y‖ := by
    rw [hv, norm_mul, Real.log_mul (norm_ne_zero_iff.2 hEv)
      (norm_ne_zero_iff.2 (Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (hne i))), norm_prod,
      Real.log_prod (fun i _ => (norm_ne_zero_iff.2 (zpow_ne_zero _ (hne i))))]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [norm_zpow, Real.log_zpow]
  rw [hlog]
  simp only [relFun]
  rw [hP]
  have hterm : ∀ i, (k i : ℝ) * (-lnN (m i) (genAt (Δ i) x) y) =
      (k i : ℝ) * (Q i).φ z p + (k i : ℝ) * Real.log ‖ratVal (f i * (eqn (Δ i) x : Y.Fn)) y‖ := by
    intro i
    rw [neg_lnN_genAt (m i) (hfi i).1 (hfi i).2.1, (hfi i).2.2]
    ring
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib]
  ring

end Local

end GlobalTheory.LeviRelation

namespace GlobalTheory.LeviRelation

theorem levi_sum_eq_levi_of_relation : ∀ {F : Type} [Field F] [NumberField F] {Y : Var F} {e : ℕ} {M : Man e} (I : ManIs M Y) (a : Fin (M.n + 1)) {ι : Type} [Fintype ι] (Δ : ι → Y.Dv) (m : ∀ i, (cxSt F).Met Y (I.ε a) (Δ i)) (Q : ι → LocPot (M.X a)) (k : ι → ℤ), (∀ i, IsPot (I.pt a) (m i) (Q i)) → (∀ i, IsPotential (M.A a) (Q i)) → ∑ i, k i • Δ i = 0 → ∃ g : M.X a → ℝ, (M.A a).Smooth g ∧ ∀ j, ∀ y ∈ ((M.A a).chart j).target, ∀ w, ∑ i, (k i : ℝ) * leviAt (M.A a) (Q i) j y w = levi (g ∘ ((M.A a).chart j).symm) y w := by
  intro F _ _ Y e M I a ι _ Δ m Q k hQ hQ' hrel
  classical
  set g := relFun I a Δ m k
  have hloc : ∀ z, ∃ W : Set (M.X a), IsOpen W ∧ z ∈ W ∧ ∃ G : M.X a → ℂ, (M.A a).HoloOn W G ∧
      ∀ p ∈ W, g p = ∑ i, (k i : ℝ) * (Q i).φ z p + (G p).re := by
    intro z
    obtain ⟨u, hu⟩ := relFun_local I a Δ m k Q hQ hrel z
    have hz : z ∈ ⋂ i, (Q i).U z := Set.mem_iInter.2 fun i => (Q i).mem_U z
    obtain ⟨W, hWo, hzW, G, hG, hGe⟩ := log_norm_ratVal_eq_re_holo F Y e M I a u z (hu z hz).1
    refine ⟨W ∩ ⋂ i, (Q i).U z, hWo.inter (isOpen_iInter_of_finite fun i => (Q i).isOpen_U z), ⟨hzW, hz⟩, G,
      fun j => (hG j).mono fun w hw => ⟨hw.1, hw.2.1⟩, fun p hp => ?_⟩
    exact (hu p hp.2).2.trans (by rw [hGe p hp.1])
  have key : ∀ j, ∀ y ∈ ((M.A a).chart j).target, ContDiffAt ℝ ∞ (g ∘ ((M.A a).chart j).symm) y ∧
      ∀ w, ∑ i, (k i : ℝ) * leviAt (M.A a) (Q i) j y w = levi (g ∘ ((M.A a).chart j).symm) y w := by
    intro j y hy
    set c := (M.A a).chart j
    set z := c.symm y
    obtain ⟨W, hWo, hzW, G, hG, hGe⟩ := hloc z
    have hψ : ∀ i, ContDiffAt ℝ ∞ ((Q i).φ z ∘ c.symm) y := fun i =>
      ((hQ' i).1 z j).contDiffAt ((c.isOpen_inter_preimage_symm ((Q i).isOpen_U z)).mem_nhds ⟨hy, (Q i).mem_U z⟩)
    have hGa : AnalyticAt ℂ (G ∘ c.symm) y := hG j y ⟨hy, hzW⟩
    have hR : ContDiffAt ℝ ∞ (fun v => ((G ∘ c.symm) v).re) y := by
      have := (Complex.reCLM.contDiff (n := ∞)).contDiffAt.comp y
        (hGa.restrictScalars (𝕜 := ℝ)).contDiffAt
      simpa [Function.comp_def] using this
    have hev : (g ∘ c.symm) =ᶠ[𝓝 y] fun v => (∑ i, (k i : ℝ) * ((Q i).φ z ∘ c.symm) v) + 1 * ((G ∘ c.symm) v).re := by
      filter_upwards [(c.isOpen_inter_preimage_symm hWo).mem_nhds ⟨hy, hzW⟩] with v hv
      simp only [Function.comp_apply, one_mul]
      exact hGe _ hv.2
    have hS : ContDiffAt ℝ ∞ (fun v => ∑ i, (k i : ℝ) * ((Q i).φ z ∘ c.symm) v) y :=
      ContDiffAt.sum fun i _ => contDiffAt_const.mul (hψ i)
    refine ⟨(hS.add (contDiffAt_const.mul hR)).congr_of_eventuallyEq hev, fun w => ?_⟩
    have h2 : ∀ {f : (Fin e → ℂ) → ℝ}, ContDiffAt ℝ ∞ f y → ContDiffAt ℝ 2 f y := fun h => h.of_le (WithTop.coe_le_coe.2 le_top)
    rw [levi_congr hev, levi_add_smul 1 (h2 hS) (h2 hR), levi_re_analytic hGa,
      levi_sum_mul Finset.univ (fun i => (k i : ℝ)) (fun i => (Q i).φ z ∘ c.symm) (fun i _ => h2 (hψ i))]
    simp only [mul_zero, add_zero]
    rfl
  exact ⟨g, fun j y hy => (key j y hy.1).1.contDiffWithinAt, fun j y hy w => (key j y hy).2 w⟩

end GlobalTheory.LeviRelation
