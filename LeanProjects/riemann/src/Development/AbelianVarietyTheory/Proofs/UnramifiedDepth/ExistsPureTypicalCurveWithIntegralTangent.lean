import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.BlockAdmissibleChart
import Formalism.LocalToGlobal.CharacterGerms.NegMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugedFormalGroupCurveLogarithmsAddSubgroupRescaStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CurveLogarithmsInvNatCastSmulMemStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PowExponentPartMemGaugedCurveLogarithmsStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AdjointEndPairMemGaugedCurveLogarithmsStatement

noncomputable section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowLaw.PureTypical

variable {C : Type} [Field C]

theorem tyS_smul {l : ℕ} (hl : 2 ≤ l) (c : C) (a : ℕ → C) : tyS l (fun s => c * a s) = c • tyS l a := by
  apply tyS_eq hl
  · intro s
    rw [PowerSeries.coeff_smul, coeff_tyS_pow hl, smul_eq_mul]
  · intro m hm
    rw [PowerSeries.coeff_smul, coeff_tyS_of_ne a m hm, smul_zero]

theorem tyS_sum {l : ℕ} (hl : 2 ≤ l) {ι : Type} (S : Finset ι) (a : ι → ℕ → C) :
    tyS l (fun s => ∑ i ∈ S, a i s) = ∑ i ∈ S, tyS l (a i) := by
  apply tyS_eq hl
  · intro s
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => coeff_tyS_pow hl _ _
  · intro m hm
    rw [map_sum]
    exact Finset.sum_eq_zero fun i _ => coeff_tyS_of_ne _ m hm

theorem tyS_rescale {l : ℕ} (hl : 2 ≤ l) (c : C) (a : ℕ → C) :
    tyS l (fun s => c ^ (l ^ s) * a s) = PowerSeries.rescale c (tyS l a) := by
  apply tyS_eq hl
  · intro s
    rw [PowerSeries.coeff_rescale, coeff_tyS_pow hl]
  · intro m hm
    rw [PowerSeries.coeff_rescale, coeff_tyS_of_ne _ m hm, mul_zero]

theorem ge_of_pow_eq_one (V : VF C) {N : ℕ} (hN : N ≠ 0) {z : C} (hz : z ^ N = 1) : V.Ge 0 z := by
  have h := V.v.map_pow z N
  rw [hz, V.v.map_one] at h
  unfold VF.Ge
  induction hv : V.v z using WithTop.recTopCoe with
  | top => exact le_top
  | coe t =>
    rw [hv] at h
    have h' : ((0 : ℝ) : WithTop ℝ) = ((N • t : ℝ) : WithTop ℝ) := by
      rw [WithTop.coe_nsmul]; exact h
    have h'' : (0 : ℝ) = N • t := by exact_mod_cast h'
    rw [nsmul_eq_mul] at h''
    have : t = 0 := by
      rcases mul_eq_zero.1 h''.symm with h | h
      · exact absurd (by exact_mod_cast h) hN
      · exact h
    rw [this]

theorem mean_pow {N : ℕ} (hN : (N : C) ≠ 0) {z y : C} (hz : z ^ N = 1) (hy : y ^ N = 1) [Decidable (z = y)] :
    (N : C)⁻¹ * ∑ k ∈ Finset.range N, (z * y⁻¹) ^ k = if z = y then 1 else 0 := by
  have hN0 : N ≠ 0 := by rintro rfl; simp at hN
  have hy0 : y ≠ 0 := by rintro rfl; rw [zero_pow hN0] at hy; exact zero_ne_one hy
  split_ifs with h
  · rw [h, mul_inv_cancel₀ hy0]
    simp [hN]
  · have h1 : z * y⁻¹ ≠ 1 := by
      intro h1
      exact h ((mul_inv_eq_one₀ hy0).1 h1)
    rw [geom_sum_eq h1, mul_pow, inv_pow, hz, hy]
    simp

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]

def emb (X : RawChart C d I κ) (l : ℕ) (g : Fin 2) (b : ℕ → I g → C) (e : ℕ → JJ I g → C) :
    (κ → PowerSeries C) × (JJ I g → PowerSeries C) :=
  (fun i => tyS l fun s => ∑ c, X.u g c i * b s c, fun q => tyS l fun s => e s q)

theorem emb_add (X : RawChart C d I κ) {l : ℕ} (hl : 2 ≤ l) (g : Fin 2) (b b' : ℕ → I g → C)
    (e e' : ℕ → JJ I g → C) :
    emb X l g (fun s c => b s c + b' s c) (fun s q => e s q + e' s q) = emb X l g b e + emb X l g b' e' := by
  refine Prod.ext (funext fun i => ?_) (funext fun q => ?_)
  · simp only [emb, Prod.fst_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    exact tyS_add hl _ _
  · exact tyS_add hl _ _

theorem emb_smul (X : RawChart C d I κ) {l : ℕ} (hl : 2 ≤ l) (g : Fin 2) (r : C) (b : ℕ → I g → C)
    (e : ℕ → JJ I g → C) :
    emb X l g (fun s c => r * b s c) (fun s q => r * e s q) = r • emb X l g b e := by
  refine Prod.ext (funext fun i => ?_) (funext fun q => ?_)
  · simp only [emb, Prod.smul_fst, Pi.smul_apply]
    rw [← tyS_smul hl]
    congr 1
    funext s
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring
  · exact tyS_smul hl _ _

theorem emb_zero (X : RawChart C d I κ) (l : ℕ) (g : Fin 2) :
    emb X l g (fun _ _ => 0) (fun _ _ => 0) = 0 := by
  refine Prod.ext (funext fun i => ?_) (funext fun q => ?_)
  · simp only [emb, mul_zero, Finset.sum_const_zero]
    exact tyS_zero
  · exact tyS_zero

section Main

variable [NeZero d] {X : RawChart C d I κ} {V : VF C}

theorem exists_start (hR : RLaw X V) (hP : HasProj X V) (g : Fin 2) (w : I g → C) (hw : ∀ c, V.Ge 0 (w c)) :
    ∃ (b : ℕ → I g → C) (e : ℕ → JJ I g → C), emb X V.l g b e ∈ Cv X V g ∧ b 0 = w ∧
      ∀ q, e 0 q = -∑ c, X.sg1 (X.u g c) (X.u (1 - g) q) * w c := by
  classical
  obtain ⟨M, h01, h10, hfix, -, hspan⟩ := hP
  have hEnd : IsEnd X V (M g) (M (1 - g)) := by
    fin_cases g
    · exact h01
    · exact h10
  set v : κ → C := fun i => ∑ c, X.u g c i * w c with hv
  set γ : κ → PowerSeries C := fun i => v i • PowerSeries.X with hγ
  have hvint : ∀ i, V.Ge 0 (v i) := fun i => VF.Ge.sum fun c _ => (hR.uint g c i).mul_int (hw c)
  have hγcv : IsCv V γ := by
    intro i
    refine ⟨by simp [hγ], fun n => ?_⟩
    simp only [hγ]
    rw [PowerSeries.coeff_smul, PowerSeries.coeff_X]
    split_ifs
    · simpa using hvint i
    · simpa using VF.Ge.zero (V := V) 0
  have hγ0 : ∀ i, ∀ m < 1, PowerSeries.coeff m (γ i) = 0 := by
    intro i m hm
    have : m = 0 := by omega
    subst this
    simp [hγ]
  have hγ1 : ∀ i, PowerSeries.coeff 1 (γ i) = v i := by
    intro i
    simp [hγ]
  have hlg0 : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0 := fun i => by
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hR.lin i 0 (by simp),
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.constantCoeff_X]
  have hlg1 : ∀ i j, MvPowerSeries.coeff (Finsupp.single j 1) (X.lg i) = if j = i then 1 else 0 := fun i j => by
    rw [hR.lin i _ (by rw [Finsupp.degree_single]), MvPowerSeries.coeff_X]
    by_cases hji : j = i
    · rw [hji, if_pos rfl, if_pos rfl]
    · rw [if_neg hji, if_neg]
      intro h
      exact hji (Finsupp.single_left_injective one_ne_zero h)
  have h0 : ((fun i => alongCv γ (X.lg i), fun q => 0 - alongCv γ (X.sg (X.u (1 - g) q))) :
      (κ → PowerSeries C) × (JJ I g → PowerSeries C)) ∈ Cv X V g :=
    ⟨γ, fun _ => 0, hγcv, fun _ => ⟨map_zero _, fun n => by rw [map_zero]; exact VF.Ge.zero 0⟩,
      fun _ => rfl, fun _ => rfl⟩
  have h1 := GlobalTheory.T.adjointEndPair_mem_gaugedCurveLogarithms C V d I κ X hR g (M g) (M (1 - g)) (fun _ => 1) hEnd (fun _ => VF.Ge.one)
    (fun q => by rw [one_smul]; exact hfix (1 - g) q) _ h0
  have h2 := GlobalTheory.T.powExponentPart_mem_gaugedCurveLogarithms C V d I κ X hR g _ h1
  have hA1 : ∀ i, PowerSeries.coeff 1 (alongCv γ (X.lg i)) = v i := by
    intro i
    rw [coeff_alongCv_low le_rfl hγ0 (hlg0 i)]
    simp [hlg1, hγ1]
  have hb : ∀ s : ℕ, ∃ b : I g → C, (s = 0 → b = w) ∧
      ∀ i, ∑ j, M g i j * PowerSeries.coeff (V.l ^ s) (alongCv γ (X.lg j)) = ∑ c, X.u g c i * b c := by
    intro s
    by_cases hs : s = 0
    · subst hs
      refine ⟨w, fun _ => rfl, fun i => ?_⟩
      simp only [pow_zero, hA1, hv, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      have := congrFun (hfix g c) i
      rw [← this]
      simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc]
    · obtain ⟨b, hb⟩ := hspan g fun j => PowerSeries.coeff (V.l ^ s) (alongCv γ (X.lg j))
      refine ⟨b, fun h => absurd h hs, fun i => ?_⟩
      have := congrFun hb i
      simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
      rw [this]
      exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  choose b hb0 hb1 using hb
  refine ⟨b, fun s q => -PowerSeries.coeff (V.l ^ s) (alongCv γ (X.sg (X.u (1 - g) q))), ?_, hb0 0 rfl, ?_⟩
  · convert h2 using 1
    refine Prod.ext (funext fun i => ?_) (funext fun q => ?_)
    · simp only [emb, typ, map_sum, PowerSeries.coeff_smul, smul_eq_mul, hb1]
    · simp only [emb, typ, one_smul, zero_sub, map_neg]
  · intro q
    simp only [pow_zero]
    rw [coeff_alongCv_low le_rfl hγ0 (X.constantCoeff_sg (hR.axes 0) _)]
    congr 1
    simp only [hγ1, hv, RawChart.sg1, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun i _ => by ring

theorem pure_mem (hR : RLaw X V) {g : Fin 2} (hT : HasTeich X V g) (a : ZMod d) {b : ℕ → I g → C}
    {e : ℕ → JJ I g → C} (h : emb X V.l g b e ∈ Cv X V g) :
    emb X V.l g (fun s c => if X.ty g c = a + s then b s c else 0)
      (fun s q => if X.ty (1 - g) q = a + s then e s q else 0) ∈ Cv X V g := by
  classical
  have hl := V.l_prime.two_le
  obtain ⟨N, ζ, M, M', hN, hζN, hinj, hζl, hEnd, hM, hM'⟩ := hT
  obtain ⟨hzero, hadd, -, hres⟩ := GlobalTheory.T.gaugedFormalGroupCurveLogarithms_addSubgroup_rescale C V d I κ X hR g
  have hNC : (N : C) ≠ 0 := by
    intro h0
    rw [h0, V.v.map_zero] at hN
    exact WithTop.top_ne_zero hN
  have hN0 : N ≠ 0 := by rintro rfl; simp at hNC
  have hζs : ∀ s : ℕ, ζ a ^ (V.l ^ s) = ζ (a + s) := by
    intro s
    induction s with
    | zero => simp
    | succ s ih => rw [pow_succ, pow_mul, ih, Nat.cast_succ, ← add_assoc, hζl]
  have hstep : ∀ (b : ℕ → I g → C) (e : ℕ → JJ I g → C), emb X V.l g b e ∈ Cv X V g →
      emb X V.l g (fun s c => (ζ (X.ty g c) * (ζ (a + s))⁻¹) * b s c)
        (fun s q => (ζ (X.ty (1 - g) q) * (ζ (a + s))⁻¹) * e s q) ∈ Cv X V g := by
    intro b e h
    have h1 := hres (ζ a)⁻¹ (ge_of_pow_eq_one V hN0 (by rw [inv_pow, hζN, inv_one])) _ h
    have h2 := GlobalTheory.T.adjointEndPair_mem_gaugedCurveLogarithms C V d I κ X hR g M M' (fun q => ζ (X.ty (1 - g) q)) hEnd
      (fun q => ge_of_pow_eq_one V hN0 (hζN _)) hM' _ h1
    convert h2 using 1
    refine Prod.ext (funext fun i => ?_) (funext fun q => ?_)
    · simp only [emb, ← tyS_rescale hl, ← tyS_smul hl]
      rw [← tyS_sum hl]
      congr 1
      funext s
      simp only [inv_pow, hζs, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      have := congrFun (hM c) i
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
      calc X.u g c i * (ζ (X.ty g c) * (ζ (a + s))⁻¹ * b s c)
          = (ζ (X.ty g c) * X.u g c i) * ((ζ (a + s))⁻¹ * b s c) := by ring
        _ = _ := by
          rw [← this, Finset.sum_mul]
          exact Finset.sum_congr rfl fun j _ => by ring
    · simp only [emb, ← tyS_rescale hl, ← tyS_smul hl, inv_pow, hζs, mul_assoc]
  have hpow : ∀ k : ℕ, emb X V.l g (fun s c => (ζ (X.ty g c) * (ζ (a + s))⁻¹) ^ k * b s c)
        (fun s q => (ζ (X.ty (1 - g) q) * (ζ (a + s))⁻¹) ^ k * e s q) ∈ Cv X V g := by
    intro k
    induction k with
    | zero => simpa using h
    | succ k ih =>
      have := hstep _ _ ih
      simpa only [pow_succ', mul_assoc] using this
  have hsum : ∀ n : ℕ, emb X V.l g
      (fun s c => (∑ k ∈ Finset.range n, (ζ (X.ty g c) * (ζ (a + s))⁻¹) ^ k) * b s c)
      (fun s q => (∑ k ∈ Finset.range n, (ζ (X.ty (1 - g) q) * (ζ (a + s))⁻¹) ^ k) * e s q) ∈ Cv X V g := by
    intro n
    induction n with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, zero_mul, emb_zero]
      exact hzero
    | succ n ih =>
      simp only [Finset.sum_range_succ, add_mul]
      rw [emb_add X hl]
      exact hadd _ ih _ (hpow n)
  have hdiv := GlobalTheory.T.curveLogarithms_inv_natCast_smul_mem C V d I κ X hR g N hN _ (hsum N)
  rw [← emb_smul X hl] at hdiv
  simp only [← mul_assoc, mean_pow hNC (hζN _) (hζN _), hinj.eq_iff, ite_mul, one_mul, zero_mul] at hdiv
  exact hdiv

end Main

end GlobalTheory.RowLaw.PureTypical

namespace GlobalTheory.RowLaw

open PureTypical in

theorem exists_pure_typical : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → HasProj X V → ∀ g, HasTeich X V g → ∀ (a : ZMod d) (w : I g → C), (∀ c, V.Ge 0 (w c)) → (∀ c, X.tyC g (Sum.inl c) ≠ a → w c = 0) → ∃ x ∈ X.TySet V g, x 0 = Sum.elim w 0 ∧ ∀ (i : ℕ) n, X.tyC g n ≠ a + i → x i n = 0 := by
  intro C _ V d _ I _ κ _ X hR hP g hT a w hw hwa
  classical
  have hl := V.l_prime.two_le
  have hwa' : ∀ c, X.ty g c ≠ a → w c = 0 := hwa
  obtain ⟨b, e, hbe, hb0, he0⟩ := exists_start hR hP g w hw
  obtain ⟨γ, lam, hγ, hlam, h1, h2⟩ := pure_mem hR hT a hbe
  set b' : ℕ → I g → C := fun s c => if X.ty g c = a + s then b s c else 0 with hb'
  set e' : ℕ → JJ I g → C := fun s q => if X.ty (1 - g) q = a + s then e s q else 0 with he'
  have hb'0 : b' 0 = w := by
    funext c
    simp only [hb', Nat.cast_zero, add_zero, hb0]
    split_ifs with h
    · rfl
    · exact (hwa' c h).symm
  refine ⟨fun s => Sum.elim (b' s) fun q => e' s q +
    ∑ c, if X.ty g c = X.ty (1 - g) q then X.sg1 (X.u g c) (X.u (1 - g) q) * b' s c else 0,
    ⟨γ, lam, hγ, hlam, fun i => ?_, fun q => ?_⟩, ?_, ?_⟩
  · rw [h1 i]
    simp only [emb, Sum.elim_inl, ← tyS_smul hl]
    exact tyS_sum hl _ _
  · rw [← h2 q]
    simp only [emb, Sum.elim_inl, Sum.elim_inr]
    rw [tyS_add hl, tyS_sum hl]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs
    · exact tyS_smul hl _ _
    · exact tyS_zero
  · funext n
    cases n with
    | inl c => simp only [Sum.elim_inl, hb'0]
    | inr q =>
      simp only [Sum.elim_inr, hb'0, he', Nat.cast_zero, add_zero, Pi.zero_apply]
      split_ifs with h
      · rw [he0, neg_add_eq_zero]
        refine Finset.sum_congr rfl fun c _ => ?_
        split_ifs with hc
        · rfl
        · rw [hwa' c (by rwa [← h]), mul_zero]
      · rw [zero_add]
        refine Finset.sum_eq_zero fun c _ => ?_
        split_ifs with hc
        · rw [hwa' c (by rwa [hc]), mul_zero]
        · rfl
  · intro i n hn
    cases n with
    | inl c =>
      have hn' : X.ty g c ≠ a + i := hn
      simp only [Sum.elim_inl, hb', if_neg hn']
    | inr q =>
      have hn' : X.ty (1 - g) q ≠ a + i := hn
      simp only [Sum.elim_inr, he', if_neg hn', zero_add]
      refine Finset.sum_eq_zero fun c _ => ?_
      split_ifs with hc
      · simp only [hb', hc, if_neg hn', mul_zero]
      · rfl

end GlobalTheory.RowLaw
