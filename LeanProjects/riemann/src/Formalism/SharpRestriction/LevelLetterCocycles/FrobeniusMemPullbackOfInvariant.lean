import Formalism.SharpRestriction.LevelLetterCocycles.ExpRules
import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.Sh

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.LiftingTheory Formalism.MainNotions.CrystallineLiftingInputs

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem letE_mul_self_eq (i : ZMod n) : (letE i : LetA O n) * letE i = letE i := by
  unfold letE
  rw [← Pi.single_mul, mul_one]

theorem idempotent_smul_smul (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n)
    (x : W.DD T) : (letE i : LetA O n) • (letE i : LetA O n) • x = (letE i : LetA O n) • x := by
  rw [smul_smul, letE_mul_self_eq]

private theorem phiD_letA_smul_eq_phiA_smul_phiD (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)
    (a : LetA O n) (x : W.DD T) : W.φD T (a • x) = W.φA a • W.φD T x := by
  rw [← algebraMap_smul W.EE a x, W.φD_smul, W.φE_ext, algebraMap_smul] <;> rfl

private theorem phiA_letE_sub_one_eq_letE (W : LocWach PD LL O v n) (i : ZMod n) :
    W.φA (letE (i - 1) : LetA O n) = letE i := by
  funext j
  show W.φ₀ ((letE (i - 1) : LetA O n) (j - 1)) = (letE i : LetA O n) j
  by_cases h : j = i
  · subst h
    simp [letE]
  · have h' : j - 1 ≠ i - 1 := fun e => h (sub_left_inj.mp e)
    simp [letE, Pi.single_apply, h, h']

theorem frobenius_idempotent_shift (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (x : W.DD T) :
    W.φD T ((letE (i - 1) : LetA O n) • x) = (letE i : LetA O n) • W.φD T x := by
  rw [phiD_letA_smul_eq_phiA_smul_phiD, phiA_letE_sub_one_eq_letE]

private theorem letGamma_letE_eq_letE (W : LocWach PD LL O v n) (g : W.Gam) (i : ZMod n) :
    letγ (W.γ₀ g) (letE i : LetA O n) = letE i := by
  funext j
  show W.γ₀ g ((letE i : LetA O n) j) = (letE i : LetA O n) j
  by_cases h : j = i
  · subst h
    simp [letE]
  · simp [letE, Pi.single_apply, h]

theorem gammaD_idempotent_smul (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (g : W.Gam) (i : ZMod n)
    (x : W.DD T) : W.γD T g ((letE i : LetA O n) • x) = (letE i : LetA O n) • W.γD T g x := by
  rw [← algebraMap_smul W.EE (letE i : LetA O n) x, W.γD_smul, W.γE_ext, algebraMap_smul,
    letGamma_letE_eq_letE]

theorem natCast_pow_smul_eq_algebra (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (N : ℕ) (x : W.DD T) :
    ((PD.p : ℕ) : O) ^ N • x = ((PD.p : ℕ) : LetA O n) ^ N • x := by
  rw [← algebraMap_smul (LetA O n) (((PD.p : ℕ) : O) ^ N) x, map_pow, map_natCast]

theorem frobeniusA_natCast_pow (W : LocWach PD LL O v n) (N : ℕ) :
    W.φA (((PD.p : ℕ) : LetA O n) ^ N) = ((PD.p : ℕ) : LetA O n) ^ N := by
  rw [map_pow, map_natCast]

theorem gammaA_natCast_pow (W : LocWach PD LL O v n) (g : W.Gam) (N : ℕ) :
    W.γA g (((PD.p : ℕ) : LetA O n) ^ N) = ((PD.p : ℕ) : LetA O n) ^ N := by
  rw [map_pow, map_natCast]

theorem basis_vector_eq_zero_or_torsionFree (W : LocWach PD LL O v n) (e : W.DD W.one)
    (hspan : W.N W.one = Submodule.span (LetA O n) {e}) (π' : LetA O n)
    (hm : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W W.one π') : e = 0 ∨ ∀ β : LetA O n, β • e = 0 → β = 0 := by
  obtain ⟨⟨r, b, hb, huniq, -⟩, -⟩ := hm
  by_cases he : e = 0
  · exact Or.inl he
  right
  intro β hβ
  have heN : e ∈ W.N W.one := by
    rw [hspan]
    exact Submodule.mem_span_singleton_self e
  have hkill : ∀ y ∈ W.N W.one, β • y = 0 := by
    intro y hy
    rw [hspan] at hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [smul_smul, mul_comm, ← smul_smul, hβ, smul_zero]
  obtain ⟨a, ha, hu⟩ := huniq e heN
  have hr : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · subst h0
      exact (he (by simpa using ha)).elim
    · exact h0
  have hz : ∑ j, β • b j = 0 := Finset.sum_eq_zero fun j _ => hkill _ (hb j).1
  have h2 : e = ∑ j, (a j + β) • b j := by
    simp only [add_smul, Finset.sum_add_distrib]
    rw [← ha, hz, add_zero]
  have h3 := congrFun (hu (fun j => a j + β) h2) ⟨0, hr⟩
  simpa using h3

theorem eq_zero_of_natCast_pow_mul (hζ : ∃ ζ : LL, IsPrimitiveRoot ζ PD.p)
    (hO : ∃ _ : IsDomain O, IsDiscreteValuationRing O ∧ IsFractionRing O LL) (N : ℕ) (β : LetA O n)
    (h : ((PD.p : ℕ) : LetA O n) ^ N * β = 0) : β = 0 := by
  obtain ⟨hd, -, hf⟩ := hO
  haveI := hd
  haveI : NeZero PD.p := ⟨PD.hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := hζ
  have hLL : ((PD.p : ℕ) : LL) ≠ 0 := hζ.neZero'.out
  have hpO : ((PD.p : ℕ) : O) ≠ 0 := by
    intro h0
    apply hLL
    rw [← map_natCast (algebraMap O LL), h0, map_zero]
  have hpS : ((PD.p : ℕ) : PowerSeries O) ≠ 0 := by
    intro h0
    apply hpO
    have h1 := congrArg PowerSeries.constantCoeff h0
    rwa [map_natCast, map_zero] at h1
  funext j
  have hj := congrFun h j
  simp only [Pi.mul_apply, Pi.pow_apply, Pi.natCast_apply, Pi.zero_apply] at hj
  rcases mul_eq_zero.mp hj with h1 | h1
  · exact ((pow_ne_zero N hpS) h1).elim
  · exact h1

theorem frobenius_mem_pullback_of_invariant (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (π' : LetA O n)
    (hm : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T π') (i : ZMod n) (t : W.DD T) (ht : t ∈ W.N T)
    (hl : (letE (i - 1) : LetA O n) • t = t) : W.φD T t ∈ pullJ W T (i - 1) 1 := by
  obtain ⟨⟨r, b, hb, huniq, -⟩, -⟩ := hm
  obtain ⟨a, ha, -⟩ := huniq t ht
  have ht' : t = ∑ j, a j • ((letE (i - 1) : LetA O n) • b j) := by
    calc t = (letE (i - 1) : LetA O n) • t := hl.symm
      _ = (letE (i - 1) : LetA O n) • ∑ j, a j • b j := by rw [← ha]
      _ = _ := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [smul_smul, smul_smul, mul_comm]
  rw [ht', map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [phiD_letA_smul_eq_phiA_smul_phiD]
  apply Submodule.smul_mem
  unfold pullJ
  apply Submodule.subset_span
  refine ⟨(letE (i - 1) : LetA O n) • b j,
    ⟨(W.N T).smul_mem _ (hb j).1, idempotent_smul_smul W T (i - 1) (b j), fun δ hδ => ?_⟩, ?_⟩
  · rw [gammaD_idempotent_smul, (hb j).2 δ hδ]
  · simp

private theorem locWach_map_letA_smul_comm (W : LocWach PD LL O v n) {T Y : LocLat G Qp LL O}
    (f : LatHom T.L Y.L) (a : LetA O n) (x : W.DD T) : W.map f (a • x) = a • W.map f x := by
  rw [← algebraMap_smul W.EE a x, map_smul, algebraMap_smul]

theorem pullback_span_of_exact (W : LocWach PD LL O v n) {T Y : LocLat G Qp LL O} (ι : LatHom T.L Y.L)
    (π : LatHom Y.L W.one.L) (hY : IsCrys PD Y.ρ) (hO : IsCrys PD W.one.ρ)
    (hker : ∀ x, W.map π x = 0 ↔ ∃ y, W.map ι y = x) (hsat : ∀ x, W.map ι x ∈ W.N Y → x ∈ W.N T)
    (hinj : Function.Injective (W.map ι)) (π' : LetA O n) (hmT : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T π')
    (e' : W.DD W.one) (hspan : W.N W.one = Submodule.span (LetA O n) {e'}) (i : ZMod n) (N : ℕ)
    (ε : W.DD Y) (hεN : ε ∈ W.N Y)
    (hεπ : W.map π ε = ((PD.p : ℕ) : LetA O n) ^ N • (letE (i - 1) : LetA O n) • e') :
    ∀ x ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W Y (W.Nl Y (i - 1)), ∃ p ∈ pullJ W T (i - 1) 1, ∃ β : LetA O n,
      ((PD.p : ℕ) : LetA O n) ^ N • x = W.map ι p + β • W.φD Y ε ∧ (e' = 0 → β = 0) := by
  intro x hx
  unfold Formalism.MainNotions.DeltaInvariantLattices.φspan at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z0, hz0, rfl⟩ := hx
    obtain ⟨y, hy, rfl⟩ := (hz0 : z0 ∈ (W.N Y).map ((letE (i - 1) : LetA O n) • LinearMap.id))
    simp only [LinearMap.smul_apply, LinearMap.id_apply]
    set z : W.DD Y := (letE (i - 1) : LetA O n) • y with hzdef
    have hz_idem : (letE (i - 1) : LetA O n) • z = z := by
      rw [hzdef]
      exact idempotent_smul_smul W Y (i - 1) y
    have hzN : z ∈ W.N Y := (W.N Y).smul_mem _ hy
    have hπz := W.map_N π hY hO z hzN
    obtain ⟨c, hc, hc0⟩ : ∃ c : LetA O n, c • e' = W.map π z ∧ (e' = 0 → c = 0) := by
      by_cases he : e' = 0
      · rw [hspan, he, Submodule.span_zero_singleton, Submodule.mem_bot] at hπz
        exact ⟨0, by rw [zero_smul, hπz], fun _ => rfl⟩
      · rw [hspan] at hπz
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hπz
        exact ⟨c, hc, fun h => (he h).elim⟩
    have hπlet : W.map π z = (letE (i - 1) : LetA O n) • W.map π z := by
      rw [← locWach_map_letA_smul_comm, hz_idem]
    have hce : c • e' = ((letE (i - 1) : LetA O n) * c) • e' := by
      rw [← smul_smul, hc]
      exact hπlet
    have hw : W.map π (((PD.p : ℕ) : LetA O n) ^ N • z - c • ε) = 0 := by
      rw [map_sub, locWach_map_letA_smul_comm W π _ z, locWach_map_letA_smul_comm W π c ε, hεπ, ← hc, hce]
      simp only [smul_smul]
      rw [sub_eq_zero]
      congr 1
      ring
    obtain ⟨y', hy'⟩ := (hker _).mp hw
    have hι : W.map ι ((letE (i - 1) : LetA O n) • y') =
        ((PD.p : ℕ) : LetA O n) ^ N • z - c • ((letE (i - 1) : LetA O n) • ε) := by
      rw [locWach_map_letA_smul_comm, hy', smul_sub, smul_comm (letE (i - 1) : LetA O n) _ z, hz_idem,
        smul_comm (letE (i - 1) : LetA O n) c ε]
    have hyN : (letE (i - 1) : LetA O n) • y' ∈ W.N T := by
      apply hsat
      rw [hι]
      exact sub_mem ((W.N Y).smul_mem _ hzN) ((W.N Y).smul_mem _ ((W.N Y).smul_mem _ hεN))
    have hp := frobenius_mem_pullback_of_invariant W T π' hmT i _ hyN (idempotent_smul_smul W T (i - 1) y')
    have e1 : W.φD Y (((PD.p : ℕ) : LetA O n) ^ N • z) = ((PD.p : ℕ) : LetA O n) ^ N • W.φD Y z := by
      rw [phiD_letA_smul_eq_phiA_smul_phiD, frobeniusA_natCast_pow]
    have e2 : W.φD Y (c • (letE (i - 1) : LetA O n) • ε) =
        (W.φA c * (letE i : LetA O n)) • W.φD Y ε := by
      rw [phiD_letA_smul_eq_phiA_smul_phiD, frobenius_idempotent_shift, smul_smul]
    refine ⟨_, hp, W.φA c * (letE i : LetA O n), ?_, fun h => by rw [hc0 h, map_zero, zero_mul]⟩
    rw [W.map_φ, hι, map_sub, e1, e2, sub_add_cancel]
  | zero => exact ⟨0, Submodule.zero_mem _, 0, by simp, fun _ => rfl⟩
  | add a b _ _ ha hb =>
    obtain ⟨q1, hq1, β1, h11, h21⟩ := ha
    obtain ⟨q2, hq2, β2, h12, h22⟩ := hb
    refine ⟨q1 + q2, Submodule.add_mem _ hq1 hq2, β1 + β2, ?_, fun h => by rw [h21 h, h22 h, add_zero]⟩
    rw [smul_add, h11, h12, map_add, add_smul]
    abel
  | smul c a _ ha =>
    obtain ⟨q, hq, β, h1, h2⟩ := ha
    refine ⟨c • q, Submodule.smul_mem _ _ hq, c * β, ?_, fun h => by rw [h2 h, mul_zero]⟩
    rw [smul_comm, h1, smul_add, locWach_map_letA_smul_comm, smul_smul]

end Formalism.MainNotions.RamifiedCoefficientChains.Sh

end
