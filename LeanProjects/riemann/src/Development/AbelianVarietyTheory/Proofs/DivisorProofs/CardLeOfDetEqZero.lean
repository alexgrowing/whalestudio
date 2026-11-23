import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormsSupLatticeSplitOverComponents
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecZEqZeroOfGenVal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.OneMemSecAndSecInfEqBot
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HostGeneratorPowFourTraceNormModEight

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.ShortDet

section Generic

open Polynomial in

theorem card_le_of_det_eq_zero {Ω S : Type} [Field Ω] [CharZero Ω] [Fintype S] [DecidableEq S] (A B : Matrix S S Ω) {a : Ω}
    (ha : (A + a • B).det ≠ 0) (T : Finset ℕ) (hT : ∀ n ∈ T, (A + (n : Ω) • B).det = 0) : T.card ≤ Fintype.card S := by
  classical
  have hev : ∀ t : Ω, Polynomial.eval t (Matrix.det ((X : Polynomial Ω) • B.map C + A.map C)) = (A + t • B).det := fun t => by
    rw [← coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    simp [add_comm, mul_comm t]
  have h0 : Matrix.det ((X : Polynomial Ω) • B.map C + A.map C) ≠ 0 := fun h => ha (by rw [← hev, h, eval_zero])
  rw [← Finset.card_image_of_injective T (Nat.cast_injective (R := Ω))]
  refine (card_le_degree_of_subset_roots fun x hx => ?_).trans (natDegree_det_X_add_C_le B A)
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hx
  exact (mem_roots h0).2 ((hev _).trans (hT n hn))

theorem exists_nat_coeff {K V ι : Type} [Field K] [AddCommGroup V] [Module K V] [Fintype ι] (P : V → Prop) (w : ι → V) (N : ℕ)
    (h : ∀ v i (a : K), P (v + a • w i) → ∃ n : ℕ, n ≤ N ∧ P (v + (n : K) • w i)) (a : ι → K) (ha : P (∑ i, a i • w i)) :
    ∃ n : ι → ℕ, (∀ i, n i ≤ N) ∧ P (∑ i, n i • w i) := by
  classical
  have key : ∀ s : Finset ι, ∃ b : ι → K, (∀ i ∈ s, ∃ n : ℕ, n ≤ N ∧ b i = n) ∧ P (∑ i, b i • w i) := fun s => by
    induction s using Finset.induction_on with
    | empty => exact ⟨a, by simp, ha⟩
    | insert k s hk ih =>
      obtain ⟨b, hb, hP⟩ := ih
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k)] at hP
      obtain ⟨n, hn, hP'⟩ := h _ _ _ hP
      refine ⟨Function.update b k n, fun i hi => ?_, ?_⟩
      · by_cases e : i = k
        · exact ⟨n, hn, by rw [e, Function.update_self]⟩
        · rw [Function.update_of_ne e]
          exact hb i ((Finset.mem_insert.1 hi).resolve_left e)
      · rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k), Function.update_self,
          Finset.sum_congr rfl fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]]
        exact hP'
  obtain ⟨b, hb, hP⟩ := key Finset.univ
  choose n hn hn' using fun i => hb i (Finset.mem_univ i)
  exact ⟨n, hn, by simpa only [hn', Nat.cast_smul_eq_nsmul] using hP⟩

def torusChar (K : Type) [Field K] {ι : Type} [Fintype ι] (e : ι → ℤ) : (ι → Kˣ) →* K where
  toFun t := ((∏ i, t i ^ e i : Kˣ) : K)
  map_one' := by simp
  map_mul' t t' := by simp [mul_zpow, Finset.prod_mul_distrib]

theorem torusChar_injective (K : Type) [Field K] [CharZero K] {ι : Type} [Fintype ι] :
    Function.Injective (torusChar K (ι := ι)) := fun e e' h => funext fun i => by
  classical
  have hw : ∀ d : ι → ℤ, torusChar K d (Pi.mulSingle i (Units.mk0 2 two_ne_zero)) = ((2 ^ d i : ℚ) : K) := fun d => by
    show ((∏ j, _ ^ d j : Kˣ) : K) = _
    rw [Finset.prod_eq_single i (fun j _ hj => by simp [Pi.mulSingle_eq_of_ne hj]) (by simp)]
    simp
  have := (hw e).symm.trans (h ▸ hw e')
  exact zpow_right_injective₀ (a := (2 : ℚ)) (by norm_num) (by norm_num) (Rat.cast_injective this)

theorem eq_zero_of_torusChar {K V ι : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] [Fintype ι]
    (s : Finset (ι → ℤ)) (v : (ι → ℤ) → V) (h : ∀ t, ∑ e ∈ s, torusChar K e t • v e = 0) : ∀ e ∈ s, v e = 0 := fun e he => by
  refine (Module.forall_dual_apply_eq_zero_iff K _).1 fun φ => ?_
  have hl := (linearIndependent_monoidHom (ι → Kˣ) K).comp _ (torusChar_injective K)
  refine linearIndependent_iff'.1 hl s (fun e => φ (v e)) (funext fun t => ?_) e he
  have := congrArg φ (h t)
  simpa [map_sum, mul_comm] using this

end Generic

section Geo

open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.LevDesc
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut LevelMod)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem card_levelAut_le (Dw : Datum H) (l : Level H) :
    Nat.card (LevelAut Dw l) ≤ l.M ^ (2 * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) ^ 2 := by
  have := Dw.fin
  have := GlobalTheory.datum_free_int Dw
  have : Module.Finite ℤ Dw.La := Module.Finite.trans (𝓞 E) Dw.La
  have hM : Ideal.span {(l.M : 𝓞 E)} ≤ l.Mb := l.prod ▸ Ideal.mul_le_left
  have hle : (nsmulAddMonoidHom (α := Dw.La) l.M).range ≤ (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).toAddSubgroup := by
    rintro _ ⟨x, rfl⟩
    change l.M • x ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
    exact Submodule.smul_mem_smul (hM (Ideal.mem_span_singleton_self _)) Submodule.mem_top
  have h1 := AddSubgroup.index_dvd_of_le hle
  rw [AddSubgroup.index_range_nsmul] at h1
  have h3 := l.three_le
  have h2 : Nat.card (LevelMod Dw l) ≤ l.M ^ Module.finrank ℤ Dw.La := Nat.le_of_dvd (by positivity) h1
  let b := Module.finBasis ℤ Dw.La
  let π := (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ
  have hi : Function.Injective fun (g : LevelAut Dw l) i => g (π (b i)) := fun g g' h => by
    have : ((g : LevelMod Dw l →ₗ[𝓞 E] LevelMod Dw l) ∘ₗ π).toAddMonoidHom.toIntLinearMap =
        ((g' : LevelMod Dw l →ₗ[𝓞 E] LevelMod Dw l) ∘ₗ π).toAddMonoidHom.toIntLinearMap := b.ext fun i => congrFun h i
    refine LinearEquiv.ext fun x => ?_
    obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ x
    exact LinearMap.congr_fun this a
  refine (Nat.card_le_card_of_injective _ hi).trans ?_
  rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin, ← GlobalTheory.datum_finrank_int, sq, pow_mul]
  exact Nat.pow_le_pow_left h2 _

theorem eq_zero_of_sum_secZ (e₀ : Ix Dw → ℤ) (s : Finset (Ix Dw → ℤ)) (g : (Ix Dw → ℤ) → Rul Xo c)
    (hg : ∀ e, g e ∈ secZ Xo c (e₀ + e)) (h : ∑ e ∈ s, g e = 0) : ∀ e ∈ s, g e = 0 := fun e he => by
  funext p y
  refine eq_zero_of_torusChar (K := c.F) s (fun e => g e p y) (fun t => ?_) e he
  obtain ⟨y', hy'⟩ := GlobalTheory.SecSeparation.exists_frBor y fun i => Units.map (algebraMap c.F p.R).toMonoidHom (t i)
  have h1 := congrFun (congrFun h p) y'
  rw [Finset.sum_apply, Finset.sum_apply] at h1
  have h2 : ∀ e, g e p y' = torusChar c.F e₀ t • torusChar c.F e t • g e p y := fun e => by
    rw [(hg e).2 p _ y y' hy', smul_smul, Algebra.smul_def]
    congr 1
    simp [torusChar, zpow_add, Finset.prod_mul_distrib, ← map_zpow]
  simp only [h2, ← Finset.smul_sum] at h1
  exact (smul_eq_zero.1 h1).resolve_left (Units.ne_zero _)

theorem genVal_idem_of_ne {Z Z' : Comp Xo c} (h : Z ≠ Z') : genVal Z (idem Z') = 0 :=
  evC_eq_zero (Reg.genFrEx_and_genFromTest E H Dw l Xo c).1 h (idem_mem_suppOn Z')

theorem genVal_idem (Z : Comp Xo c) : genVal Z (idem Z) = 1 := by
  have := CompFin.finite_comp Xo c
  have := Fintype.ofFinite (Comp Xo c)
  have h := congrArg (genVal Z) (sum_idem Xo c)
  rwa [map_sum, map_one, Finset.sum_eq_single Z (fun _ _ h => genVal_idem_of_ne h.symm) (by simp)] at h

theorem mul_idem_eq_zero {e : Ix Dw → ℤ} {d : Rul Xo c} (hd : d ∈ secZ Xo c e) {Z : Comp Xo c} (h : genVal Z d = 0) :
    d * idem Z = 0 :=
  secZ_eq_zero_of_genVal (mul_mem_secZ hd (idem_mem_secZ Z)) fun Z' => by
    rw [map_mul]
    by_cases e : Z' = Z
    · rw [e, h, zero_mul]
    · rw [genVal_idem_of_ne e, mul_zero]

theorem nonZeroDiv_iff {e₀ : Ix Dw → ℤ} {d : Rul Xo c} (hd : d ∈ secZ Xo c e₀) :
    (∀ f ∈ secRing Xo c, d * f = 0 → f = 0) ↔ ∀ Z : Comp Xo c, genVal Z d ≠ 0 := by
  classical
  refine ⟨fun h Z h0 => ?_, fun h f hf h0 => ?_⟩
  · have := genVal_idem Z
    rw [h _ (mem_secRing (idem_mem_secZ Z)) (mul_idem_eq_zero hd h0), map_zero] at this
    exact zero_ne_one this
  · obtain ⟨g, hg, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hf
    rw [Finsupp.sum, Finset.mul_sum] at h0
    refine Finset.sum_eq_zero fun e he => secZ_eq_zero_of_genVal (hg e) fun Z => ?_
    have := congrArg (genVal Z) (eq_zero_of_sum_secZ e₀ _ _ (fun e => mul_mem_secZ hd (hg e)) h0 e he)
    rw [map_mul, map_zero] at this
    exact (mul_eq_zero.1 this).resolve_left (h Z)

variable (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M)
include hpq hA

theorem comp_unique (γ : LevelAut Dw l) {W Z Z' : Comp Xo c} (h : genVal Z (pull Xo c γ (idem W)) ≠ 0)
    (h' : genVal Z' (pull Xo c γ (idem W)) ≠ 0) : Z = Z' := by
  have key : ∀ Z : Comp Xo c, genVal Z (pull Xo c γ (idem W)) ≠ 0 → genVal W (pull Xo c γ⁻¹ (idem Z)) ≠ 0 :=
    fun Z h h0 => h (by
      have h1 := congrArg (fun f => genVal Z (pull Xo c γ f))
        (mul_idem_eq_zero (pull_mem_secZ hpq hA γ⁻¹ (idem_mem_secZ Z)) h0)
      simp only [map_mul, map_zero] at h1
      rwa [← (isRightAct_pull hpq hA).2, inv_mul_cancel, (isRightAct_pull hpq hA).1, genVal_idem, one_mul] at h1)
  by_contra hne
  refine mul_ne_zero (key Z h) (key Z' h') ?_
  rw [← map_mul, ← map_mul, idem_mul_idem_of_ne hne, map_zero, map_zero]

theorem exists_nat_step (S : Subgroup (LevelAut Dw l)) (v w : Rul Xo c) {W : Comp Xo c} (hw : idem W * w = w) (a : c.F)
    (h : ∀ Z : Comp Xo c, genVal Z (levDet Xo c S (v + a • w)) ≠ 0) :
    ∃ n : ℕ, n ≤ Nat.card S ^ 2 ∧ ∀ Z : Comp Xo c, genVal Z (levDet Xo c S (v + (n : c.F) • w)) ≠ 0 := by
  classical
  have := CompFin.finite_comp Xo c
  have := Fintype.ofFinite (Comp Xo c)
  have hev : ∀ (Z : Comp Xo c) (t : c.F), genVal Z (levDet Xo c S (v + t • w)) =
      ((levMat Xo c S v).map (genVal Z) + algebraMap c.F (Om Z) t • (levMat Xo c S w).map (genVal Z)).det := fun Z t => by
    rw [levDet, AlgHom.map_det]
    congr 1
    ext g g'
    simp only [Matrix.map_apply, AlgHom.mapMatrix_apply, levMat_apply, map_add, map_smul, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul]
    rw [Algebra.smul_def]
  let B : Finset (Comp Xo c) := Finset.univ.biUnion fun γ : S =>
    Finset.univ.filter fun Z => genVal Z (pull Xo c γ (idem W)) ≠ 0
  have hB : B.card ≤ Nat.card S := by
    refine (Finset.card_biUnion_le_card_mul _ _ 1 fun γ _ => Finset.card_le_one.2 fun Z hZ Z' hZ' => ?_).trans (by simp)
    exact comp_unique hpq hA γ (Finset.mem_filter.1 hZ).2 (Finset.mem_filter.1 hZ').2
  let T : Comp Xo c → Finset ℕ := fun Z => (Finset.range (Nat.card S ^ 2 + 1)).filter fun n =>
    genVal Z (levDet Xo c S (v + (n : c.F) • w)) = 0
  have hT : ∀ Z, (T Z).card ≤ Nat.card S := fun Z => by
    haveI : CharZero (Om Z) := charZero_of_injective_algebraMap (algebraMap c.F (Om Z)).injective
    rw [Nat.card_eq_fintype_card]
    refine card_le_of_det_eq_zero _ _ (hev Z a ▸ h Z) _ fun n hn => ?_
    have := (Finset.mem_filter.1 hn).2
    rwa [hev, map_natCast] at this
  have hc : (B.biUnion T).card < (Finset.range (Nat.card S ^ 2 + 1)).card := by
    rw [Finset.card_range, Nat.lt_succ_iff, sq]
    exact (Finset.card_biUnion_le_card_mul _ _ _ fun Z _ => hT Z).trans (Nat.mul_le_mul_right _ hB)
  obtain ⟨n, hn, hn'⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  refine ⟨n, Nat.lt_succ_iff.1 (Finset.mem_range.1 hn), fun Z h0 => ?_⟩
  by_cases hZ : Z ∈ B
  · exact hn' (Finset.mem_biUnion.2 ⟨Z, hZ, Finset.mem_filter.2 ⟨hn, h0⟩⟩)
  · have hz : (levMat Xo c S w).map (genVal Z) = 0 := by
      ext g g'
      have : genVal Z (pull Xo c (g * g' : S) (idem W)) = 0 := by
        by_contra hne
        exact hZ (Finset.mem_biUnion.2 ⟨g * g', Finset.mem_univ _, Finset.mem_filter.2 ⟨Finset.mem_univ _, hne⟩⟩)
      show genVal Z (pull Xo c (g * g' : S) w) = 0
      rw [← hw, map_mul, map_mul, this, zero_mul]
    refine h Z ?_
    rw [hev, hz, smul_zero] at h0 ⊢
    exact h0

end Geo

section Norm

open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.LevDesc GlobalTheory.CompHS
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut LevelMod)

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c : Coeff l} {r : ℕ}

section One

variable {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (x : ℝ)

theorem homN_sum_le {ι : Type} (s : Finset ι) (G : WTZ D.host.E) (n : ι → ℕ) (w : ι → Rul Xo c)
    (z : Σ k, Frame (U.X k).Ψ r) : homN U x G (∑ i ∈ s, n i • w i) z ≤ ∑ i ∈ s, n i * homN U x G (w i) z := by
  simp only [homN, ptN, Data.pnorm, map_sum, map_nsmul, Finset.sum_apply, Pi.smul_apply]
  have h := (norm_sum_le s fun i => n i • rdU U (w i) z.1 z.2).trans
    (Finset.sum_le_sum fun i _ => norm_nsmul_le (n := n i) (a := rdU U (w i) z.1 z.2))
  refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h (by positivity)) (lieFacZ_pos x G).le).trans (le_of_eq ?_)
  rw [Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem homN_eq_zero {Z : Comp Xo c} (G : WTZ D.host.E) {f : Rul Xo c} (hf : f ∈ suppOn Z) {z : Σ k, Frame (U.X k).Ψ r}
    (hz : z ∉ framesOn U Z) : homN U x G f z = 0 := by
  simp only [homN, ptN, Data.pnorm, rdU_eq_zero U hf hz, norm_zero, zero_mul, mul_zero]

theorem eq_of_mem_framesOn {Z Z' : Comp Xo c} {z : Σ k, Frame (U.X k).Ψ r} (hz : z ∈ framesOn U Z)
    (hz' : z ∈ framesOn U Z') : Z = Z' := by
  by_contra h
  have s₀ : Sp (CAt σ) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
  exact Set.disjoint_left.1 (CompSplitPfD.cspD_comp_disj Xo c Z Z' h) (hz.2 s₀) (hz'.2 s₀)

theorem petAt_mul_le (V : HSp D) (dict : GA D V → Σ k, Frame (U.X k).Ψ r) (hd : ∀ g, (dict g).2 ∈ (U.X (dict g).1).dom)
    {G G₀ : WTZ D.host.E} (hG : Even G.2) (hG₀ : Even G₀.2) {f u : Rul Xo c} (hf : rdU U f ∈ holSub U.X (modelWt U G))
    {B : ℝ} (hB : 0 ≤ B) (hu : ∀ z, homN U x G₀ u z ≤ B) :
    petAt U x V dict (muQ1 V) (G + G₀) (f * u) ≤ B * petAt U x V dict (muQ1 V) G f := by
  have hfin : eLpNorm (fun q : AutQ V => homN U x G f (dict q.out)) 2 (muQ1 V) ≠ ⊤ := by
    have : (fun q : AutQ V => homN U x G f (dict q.out)) =
      lieFacZ Dw x G • fun q : AutQ V => ptN (modelWt U G) (rdU U f) (dict q.out) := rfl
    rw [this, eLpNorm_const_smul]
    exact ENNReal.mul_ne_top enorm_ne_top
      (petE_ne_top V dict _ (muPart_univ V dict ▸ muPart_univ_le V dict Set.univ) hd hf)
  rw [petAt_eq, petAt_eq, ← ENNReal.toReal_ofReal hB, ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin)
    (eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Filter.Eventually.of_forall fun q => ?_) 2)
  rw [Real.norm_of_nonneg (homN_nonneg _ _ _ _ _), Real.norm_of_nonneg (homN_nonneg _ _ _ _ _),
    homN_mul U x hG hG₀ _ _ _ (hd _), mul_comm]
  exact mul_le_mul_of_nonneg_right (hu _) (homN_nonneg _ _ _ _ _)

end One

variable {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} {V : (c.F →+* ℂ) → HSp D}
  {dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r}

theorem exists_short (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ))
    (S : Subgroup (LevelAut Dw l)) (la : AllWt.Weight Dw) {β Λ N : ℝ} (hβ : 1 ≤ β) (hΛ : 0 ≤ Λ) (hN : 0 ≤ N)
    (hsup : ∀ Z, SupBdWt U x V dict Z la β)
    (hspan : ∀ Z, Submodule.span c.F (latOn U Z (wtOf Dw la 0) : Set (cuspOn U Z (wtOf Dw la 0))) = ⊤)
    (hgen : ∀ Z, ∃ (n : ℕ) (w : Fin n → cuspOn U Z (wtOf Dw la 0)) (abelian₂ : ℝ),
      IsShortGen (normOn U x V dict Z (wtOf Dw la 0)) (latOn U Z (wtOf Dw la 0)) w abelian₂ ∧ abelian₂ ≤ Λ ∧ (n : ℝ) ≤ N)
    {u₀ : Rul Xo c} (h₀ : u₀ ∈ cuspW Xo c U (wtOf Dw la 0))
    (hd₀ : ∀ f ∈ secRing Xo c, levDet Xo c S u₀ * f = 0 → f = 0) :
    ∃ u : cuspW Xo c U (wtOf Dw la 0), u ∈ latW U _ ∧ (∀ f ∈ secRing Xo c, levDet Xo c S u * f = 0 → f = 0) ∧
      ∀ σ z, homN (U (goodOf c σ)) x (wtOf Dw la 0) u z ≤ N * (Nat.card S ^ 2 * (β * Λ)) := by
  classical
  have := CompFin.finite_comp Xo c
  have := Fintype.ofFinite (Comp Xo c)
  choose n w abelian₂ hw hLam hn using hgen
  let θ : (Σ Z, Fin (n Z)) → Rul Xo c := fun i => w i.1 i.2
  have hmem : u₀ ∈ Submodule.span c.F (Set.range θ) := by
    rw [← GlobalTheory.CuspSplit.iSup_cuspOn hU] at h₀
    refine (iSup_le fun Z f hf => ?_ : (⨆ Z, cuspOn U Z (wtOf Dw la 0)) ≤ _) h₀
    have h1 : (⊤ : Submodule c.F (cuspOn U Z (wtOf Dw la 0))) ≤
        (Submodule.span c.F (Set.range θ)).comap (cuspOn U Z _).subtype := by
      rw [← hspan Z, Submodule.span_le]
      intro g hg
      have h2 : Submodule.span ℤ (Set.range (w Z)) ≤
          ((Submodule.span c.F (Set.range θ)).comap (cuspOn U Z _).subtype).restrictScalars ℤ :=
        Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact Submodule.subset_span ⟨⟨Z, i⟩, rfl⟩)
      exact h2 (((hw Z).gen g).1 hg)
    exact h1 (Submodule.mem_top (x := ⟨f, hf⟩))
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun c.F).1 hmem
  obtain ⟨m, hm, hP⟩ := exists_nat_coeff (K := c.F) (fun v => ∀ Z : Comp Xo c, genVal Z (levDet Xo c S v) ≠ 0) θ
    (Nat.card S ^ 2) (fun v i a h => exists_nat_step hpq hA S v (θ i)
      (GlobalTheory.CuspSplit.idem_mul_of_mem_cuspOn (w i.1 i.2).2) a h) a
    ((nonZeroDiv_iff (levDet_mem_secZ hpq hA (cuspW_le_secZ _ h₀))).1 hd₀)
  let θ' : (Σ Z, Fin (n Z)) → cuspW Xo c U (wtOf Dw la 0) := fun i => ⟨θ i, cuspOn_le U _ _ (w i.1 i.2).2⟩
  have hcoe : ((∑ i, m i • θ' i : cuspW Xo c U (wtOf Dw la 0)) : Rul Xo c) = ∑ i, m i • θ i := by
    simp [θ']
  refine ⟨∑ i, m i • θ' i, Submodule.sum_mem _ fun i _ => nsmul_mem ?_ _, ?_, fun σ z => ?_⟩
  · exact (mem_latOn U).1 (((hw i.1).gen _).2 (Submodule.subset_span ⟨i.2, rfl⟩))
  · exact (nonZeroDiv_iff (levDet_mem_secZ hpq hA (cuspW_le_secZ _ (Subtype.prop _)))).2 (hcoe ▸ hP)
  · rw [hcoe]
    refine (homN_sum_le _ x _ _ _ _ z).trans ?_
    rw [Fintype.sum_sigma]
    have hoff : ∀ Z, z ∉ framesOn (U (goodOf c σ)) Z →
        ∑ i, (m ⟨Z, i⟩ : ℝ) * homN (U (goodOf c σ)) x (wtOf Dw la 0) (θ ⟨Z, i⟩) z = 0 := fun Z hz =>
      Finset.sum_eq_zero fun i _ => by rw [homN_eq_zero _ x _ (w Z i).2.2 hz, mul_zero]
    by_cases hz : ∃ Z, z ∈ framesOn (U (goodOf c σ)) Z
    · obtain ⟨Z, hz⟩ := hz
      rw [Finset.sum_eq_single Z (fun Z' _ h => hoff Z' fun h' => h (eq_of_mem_framesOn _ h' hz)) (by simp)]
      refine (Finset.sum_le_card_nsmul _ _ (Nat.card S ^ 2 * (β * Λ)) fun i _ => ?_).trans ?_
      · refine mul_le_mul (by exact_mod_cast hm _) ?_ (homN_nonneg _ _ _ _ _) (by positivity)
        have h1 := hsup Z σ z hz _ (w Z i).2
        have h2 : petOn U x V dict Z (wtOf Dw la 0) σ (w Z i) ≤ Λ := ((hw Z).le i σ).trans (hLam Z)
        have h3 : 0 ≤ petOn U x V dict Z (wtOf Dw la 0) σ (w Z i) := petAt_nonneg _ _ _ _ _ _ _
        refine (sq_le_sq₀ (homN_nonneg _ _ _ _ _) (by positivity)).1 (h1.trans ?_)
        rw [mul_pow]
        exact mul_le_mul (by nlinarith) (pow_le_pow_left₀ h3 h2 2) (by positivity) (by positivity)
      · rw [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (hn Z) (by positivity)
    · rw [Finset.sum_eq_zero fun Z _ => hoff Z fun h => hz ⟨Z, h⟩]
      positivity

theorem normW_mul_pull_le (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M)
    (hd : ∀ σ, GoodEmb c σ → ∀ g, (dict σ g).2 ∈ ((U σ).X (dict σ g).1).dom)
    (hk : ∀ G : WTZ D.host.E, Even G.2 → KeepsCusp U G ∧ ∀ (γ : LevelAut Dw l) (f g : cuspW Xo c U G),
      (g : Rul Xo c) = pull Xo c γ f → ∀ σ, normW U x V dict G σ g = normW U x V dict G σ f)
    {G₀ : WTZ D.host.E} (hG₀ : Even G₀.2) {u : Rul Xo c} {B : ℝ} (hB : 0 ≤ B)
    (hu : ∀ σ z, homN (U (goodOf c σ)) x G₀ u z ≤ B) (γ : LevelAut Dw l) (G : WTZ D.host.E) (f : cuspW Xo c U G)
    (g : cuspW Xo c U (G + G₀)) (hG : Even G.2) (hg : (g : Rul Xo c) = f * pull Xo c γ u) (σ : c.F →+* ℂ) :
    normW U x V dict _ σ g ≤ B * normW U x V dict G σ f := by
  obtain ⟨k₁, n₁⟩ := hk G hG
  obtain ⟨k₂, n₂⟩ := hk (G + G₀) (hG.add hG₀)
  rw [← n₁ γ⁻¹ f ⟨_, k₁ γ⁻¹ _ f.2⟩ rfl, ← n₂ γ⁻¹ g ⟨_, k₂ γ⁻¹ _ g.2⟩ rfl]
  have e : pull Xo c γ⁻¹ g = pull Xo c γ⁻¹ f * u := by
    rw [hg, map_mul, ← (isRightAct_pull hpq hA).2, mul_inv_cancel, (isRightAct_pull hpq hA).1]
  show petW U x V dict _ σ (pull Xo c γ⁻¹ g) ≤ B * petW U x V dict G σ (pull Xo c γ⁻¹ f)
  rw [e]
  exact petAt_mul_le _ x _ _ (hd _ (goodEmb_goodOf c σ)) hG hG₀
    ((mem_cuspW.1 (k₁ γ⁻¹ _ f.2)).2 _ (goodEmb_goodOf c σ)) hB (hu σ)

end Norm

end GlobalTheory.ShortDet
