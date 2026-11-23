import Formalism.SharpRestriction.LevelLetterCocycles.FinalLevelsOf

noncomputable section

namespace Formalism.MainNotions.N.Ln03.K8

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G TensorProduct

section Content

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem C_dvd_iff_dvd_coeffs (ϖ : O) (f : PowerSeries O) :
    PowerSeries.C ϖ ∣ f ↔ ∀ k, ϖ ∣ PowerSeries.coeff k f := by
  constructor
  · rintro ⟨g, rfl⟩ k
    rw [PowerSeries.coeff_C_mul]
    exact dvd_mul_right _ _
  · intro h
    choose g hg using h
    refine ⟨PowerSeries.mk g, ?_⟩
    ext k
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, hg]

theorem prime_C_uniformizer {ϖ : O} (hϖ : Irreducible ϖ) : Prime (PowerSeries.C ϖ : PowerSeries O) := by
  have : (Ideal.span {ϖ} : Ideal O).IsPrime := (Ideal.span_singleton_prime hϖ.ne_zero).2 hϖ.prime
  have key : ∀ f : PowerSeries O, PowerSeries.C ϖ ∣ f ↔
      PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) f = 0 := by
    intro f
    rw [C_dvd_iff_dvd_coeffs]
    constructor
    · intro h
      ext k
      rw [PowerSeries.coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
      exact h k
    · intro h k
      have h1 := congrArg (PowerSeries.coeff k) h
      rw [PowerSeries.coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h1
      exact h1
  refine ⟨?_, ?_, ?_⟩
  · intro h
    apply hϖ.ne_zero
    simpa using congrArg PowerSeries.constantCoeff h
  · intro hu
    apply hϖ.not_isUnit
    simpa using hu.map PowerSeries.constantCoeff
  · intro f g hfg
    rw [key, map_mul] at hfg
    rcases mul_eq_zero.1 hfg with h | h
    · exact Or.inl ((key f).2 h)
    · exact Or.inr ((key g).2 h)

theorem power_series_cancel_bounded (q : O) {f : PowerSeries O} (hf : f ≠ 0) :
    ∃ c₀ : ℕ, ∀ (k : ℕ) (g : PowerSeries O),
      (PowerSeries.C q) ^ (k + c₀) ∣ f * g → (PowerSeries.C q) ^ k ∣ g := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hP := prime_C_uniformizer hϖ
  set P : PowerSeries O := PowerSeries.C ϖ with hPdef
  have hex : ∃ v : ℕ, ¬ P ^ (v + 1) ∣ f := by
    obtain ⟨k, hk⟩ : ∃ k, PowerSeries.coeff k f ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hf (PowerSeries.ext fun k => by simpa using hall k)
    obtain ⟨e, he⟩ := IsDiscreteValuationRing.associated_pow_irreducible hk hϖ
    refine ⟨e, fun hd => ?_⟩
    rw [hPdef, ← map_pow, C_dvd_iff_dvd_coeffs] at hd
    have h1 : ϖ ^ (e + 1) ∣ ϖ ^ e := he.dvd_iff_dvd_right.1 (hd k)
    have h2 := (pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 h1
    omega
  classical
  set v := Nat.find hex with hv
  have hnot : ¬ P ^ (v + 1) ∣ f := Nat.find_spec hex
  have hdv : P ^ v ∣ f := by
    rcases Nat.eq_zero_or_pos v with h0 | hpos
    · rw [h0, pow_zero]
      exact one_dvd _
    · have h1 := not_not.1 (Nat.find_min hex (show v - 1 < v by omega))
      rwa [show v - 1 + 1 = v by omega] at h1
  obtain ⟨f', hf'⟩ := hdv
  have hf'P : ¬ P ∣ f' := by
    rintro ⟨u, hu⟩
    apply hnot
    exact ⟨u, by rw [hf', hu, pow_succ, mul_assoc]⟩
  have iter : ∀ (M : ℕ) (g : PowerSeries O), P ^ M ∣ f' * g → P ^ M ∣ g := by
    intro M
    induction M with
    | zero => intro g _; rw [pow_zero]; exact one_dvd _
    | succ M ih =>
      intro g hg
      have h1 : P ∣ f' * g := dvd_trans (dvd_pow_self P (Nat.succ_ne_zero M)) hg
      obtain ⟨g', rfl⟩ := (hP.dvd_or_dvd h1).resolve_left hf'P
      have h2 : P ^ M ∣ f' * g' := by
        rw [pow_succ', show f' * (P * g') = P * (f' * g') by ring] at hg
        exact (mul_dvd_mul_iff_left hP.ne_zero).1 hg
      rw [pow_succ']
      exact mul_dvd_mul_left P (ih g' h2)
  refine ⟨v, fun k g hg => ?_⟩
  by_cases hq : q = 0
  · rcases Nat.eq_zero_or_pos k with hk | hk
    · rw [hk, pow_zero]
      exact one_dvd _
    · rw [hq, map_zero, zero_pow (by omega), zero_dvd_iff] at hg
      rcases mul_eq_zero.1 hg with h | h
      · exact absurd h hf
      · rw [h]
        exact dvd_zero _
  · obtain ⟨e, he⟩ := IsDiscreteValuationRing.associated_pow_irreducible hq hϖ
    have hA : ∀ j : ℕ, Associated ((PowerSeries.C q) ^ j) (P ^ (e * j)) := fun j => by
      have h0 := (he.map PowerSeries.C).pow_pow (n := j)
      rw [map_pow, ← pow_mul] at h0
      exact h0
    rcases Nat.eq_zero_or_pos e with he0 | he0
    · rw [(hA k).dvd_iff_dvd_left, he0, zero_mul, pow_zero]
      exact one_dvd _
    · rw [(hA (k + v)).dvd_iff_dvd_left, hf'] at hg
      have h1 : P ^ v * P ^ (e * k) ∣ P ^ v * (f' * g) := by
        rw [← pow_add, ← mul_assoc]
        exact dvd_trans (pow_dvd_pow P (by nlinarith)) hg
      have h2 := (mul_dvd_mul_iff_left (pow_ne_zero v hP.ne_zero)).1 h1
      rw [(hA k).dvd_iff_dvd_left]
      exact iter _ g h2

end Content

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {Lb : LevB W} {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O}
    {T : LocLat G Qp LL O} {C : Coord W (baseIdOf hR) T} {c : ZMod n}

theorem isRegular_image_in_EE [IsDomain O] [IsDiscreteValuationRing O] (hR : Ring9 W)
    {κ : PowerSeries O} (hκ : κ ≠ 0) (x : W.EE)
    (hx : algebraMap (LetA O n) W.EE ((baseIdOf hR).d κ) * x = 0) : x = 0 := by
  have := W.EE_complete
  have hf : (baseIdOf hR).ι κ ≠ 0 := fun h => hκ (baseIdOf_inj hR (by rw [h, map_zero]))
  obtain ⟨c₀, hc₀⟩ := power_series_cancel_bounded ((PD.p : ℕ) : O) hf
  have key : ∀ k : ℕ, x ∈ Ideal.span {((PD.p : ℕ) : W.EE) ^ k} := by
    intro k
    obtain ⟨a, m, ham⟩ := W.EE_dense x (k + c₀)
    have h1 : algebraMap (LetA O n) W.EE ((baseIdOf hR).d κ * a) ∈
        Ideal.span {((PD.p : ℕ) : W.EE) ^ (k + c₀)} := by
      obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 ham
      rw [Ideal.mem_span_singleton']
      refine ⟨-(algebraMap (LetA O n) W.EE ((baseIdOf hR).d κ) * y), ?_⟩
      have e : algebraMap (LetA O n) W.EE a =
          x * algebraMap (LetA O n) W.EE (letπ ^ m) - y * ((PD.p : ℕ) : W.EE) ^ (k + c₀) := by
        rw [hy]; ring
      rw [map_mul, e, mul_sub, ← mul_assoc, hx, zero_mul]
      ring
    obtain ⟨b, hb⟩ := W.EE_sat _ _ h1
    have h2 : ∀ i, (PowerSeries.C ((PD.p : ℕ) : O)) ^ k ∣ a i := by
      intro i
      apply hc₀ k (a i)
      have h3 := congrFun hb i
      simp only [Pi.mul_apply, Pi.pow_apply, Pi.natCast_apply, BaseId.d_apply] at h3
      rw [map_natCast, h3]
      exact dvd_mul_right _ _
    choose d hd using h2
    have h4 : algebraMap (LetA O n) W.EE a ∈ Ideal.span {((PD.p : ℕ) : W.EE) ^ k} := by
      have h5 : a = ((PD.p : ℕ) : LetA O n) ^ k * d := by
        funext i
        simp only [Pi.mul_apply, Pi.pow_apply, Pi.natCast_apply]
        rw [hd i, map_natCast]
      rw [h5, map_mul, map_pow, map_natCast]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    have ham' : x * algebraMap (LetA O n) W.EE (letπ ^ m) - algebraMap (LetA O n) W.EE a ∈
        Ideal.span {((PD.p : ℕ) : W.EE) ^ k} :=
      Ideal.mem_span_singleton.2 (dvd_trans (pow_dvd_pow _ (Nat.le_add_right k c₀))
        (Ideal.mem_span_singleton.1 ham))
    have h6 := Ideal.add_mem _ ham' h4
    rw [sub_add_cancel, map_pow] at h6
    exact (Ideal.mul_unit_mem_iff_mem _ (W.EE_π.pow m)).1 h6
  refine IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {((PD.p : ℕ) : W.EE)}) W.EE) x
    fun k => ?_
  rw [SModEq.zero, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top]
  exact key k

theorem smul_cancel [IsDomain O] [IsDiscreteValuationRing O] (κ : PowerSeries O) (hκ : κ ≠ 0)
    (x y : C.V) (h : κ • x = κ • y) : x = y := by
  have hz : (baseIdOf hR).d κ • C.t 0 (x - y) = 0 := by
    rw [← C.t_smul, smul_sub, h, sub_self, C.t_zero]
  have hz' : algebraMap (LetA O n) W.EE ((baseIdOf hR).d κ) • C.t 0 (x - y) = 0 := by
    rw [algebraMap_smul]
    exact hz
  have := (W.DD_free T).1
  have h0 : C.t 0 (x - y) = 0 := by
    apply (Module.Free.chooseBasis W.EE (W.DD T)).repr.injective
    ext k
    have h2 := congrArg (fun z => (Module.Free.chooseBasis W.EE (W.DD T)).repr z k) hz'
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.zero_apply] at h2
    rw [map_zero, Finsupp.zero_apply]
    exact isRegular_image_in_EE hR hκ _ h2
  exact sub_eq_zero.1 (C.t_inj 0 (by rw [h0, C.t_zero]))

end Formalism.MainNotions.N.Ln03.K8
