import Formalism.LocalToGlobal.InertKernelTheory.StatementKap
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.StdOK
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharactersFactTer
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OneLetterGaussSharpTranslateHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitDeterminantRoot.DetMemOfEntries
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitDeterminantRoot.NormLeOneOfRoot
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ChoiceOfModulusAndDiscriminant

noncomputable section
open scoped BigOperators ComplexConjugate
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.KerInert.Kap

open Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity
open Formalism.L2.Th1.F (cmTheta)

theorem kap_norm_add_of_lt {E : Type*} [NormedAddCommGroup E] [IsUltrametricDist E] {x y : E} (h : ‖y‖ < ‖x‖) :
    ‖x + y‖ = ‖x‖ := by
  apply le_antisymm
  · exact (IsUltrametricDist.norm_add_le_max x y).trans (max_le le_rfl h.le)
  · have h1 := IsUltrametricDist.norm_add_le_max (x + y) (-y)
    rw [add_neg_cancel_right, norm_neg] at h1
    rcases le_max_iff.1 h1 with h2 | h2
    · exact h2
    · exact absurd h2 (not_le.2 h)

theorem kap_coe_rat (l : ℕ) [Fact l.Prime] (q : ℚ) : (((q : ℚ_[l]) : ℂ_[l])) = (q : ℂ_[l]) := by
  show algebraMap (PadicAlgCl l) ℂ_[l] (algebraMap ℚ_[l] (PadicAlgCl l) (q : ℚ_[l])) = (q : ℂ_[l])
  rw [map_ratCast, map_ratCast]

theorem kap_one_le_norm (l : ℕ) [Fact l.Prime] (d : ℕ) (hj : jacobiSym (-(d : ℤ)) l = -1) (w : ℚ_[l]) :
    1 ≤ ‖(1 : ℚ_[l]) + (d : ℚ_[l]) * w ^ 2‖ := by
  have hleg : legendreSym l (-(d : ℤ)) = -1 := by rw [jacobiSym.legendreSym.to_jacobiSym]; exact hj
  have hdz : ((d : ℕ) : ZMod l) ≠ 0 := by
    intro h0
    have h1 : legendreSym l (-(d : ℤ)) = 0 := by
      rw [legendreSym.eq_zero_iff]; push_cast; rw [h0, neg_zero]
    rw [h1] at hleg; norm_num at hleg
  have hnd : ¬ l ∣ d := fun h => hdz ((ZMod.natCast_eq_zero_iff d l).2 h)
  have hd1 : ‖(d : ℚ_[l])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hnd)
  by_contra hlt
  push Not at hlt
  rcases lt_trichotomy ‖w‖ 1 with h | h | h
  · have h2 : ‖(d : ℚ_[l]) * w ^ 2‖ < ‖(1 : ℚ_[l])‖ := by
      rw [norm_mul, norm_pow, hd1, one_mul, norm_one]; nlinarith [norm_nonneg w]
    rw [kap_norm_add_of_lt h2, norm_one] at hlt
    exact lt_irrefl _ hlt
  · let W : ℤ_[l] := ⟨w, h.le⟩
    have hZ : ‖(1 : ℤ_[l]) + (d : ℤ_[l]) * W ^ 2‖ < 1 := by
      rw [PadicInt.norm_def]
      push_cast
      exact hlt
    have hmem : (1 : ℤ_[l]) + (d : ℤ_[l]) * W ^ 2 ∈ RingHom.ker (PadicInt.toZMod (p := l)) := by
      rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]
      exact hZ
    rw [RingHom.mem_ker, map_add, map_one, map_mul, map_pow, map_natCast] at hmem
    set z := PadicInt.toZMod W with hzdef
    have hz : z ≠ 0 := by
      intro h0
      rw [h0] at hmem
      simp at hmem
    have h0 : ((-(d : ℤ) : ℤ) : ZMod l) ≠ 0 := by push_cast; exact neg_ne_zero.2 hdz
    have hsq : IsSquare ((-(d : ℤ) : ℤ) : ZMod l) := by
      refine ⟨z⁻¹, ?_⟩
      push_cast
      field_simp
      linear_combination (-1 : ZMod l) * hmem
    have h3 := (legendreSym.eq_one_iff l h0).2 hsq
    rw [h3] at hleg
    norm_num at hleg
  · have h2 : ‖(1 : ℚ_[l])‖ < ‖(d : ℚ_[l]) * w ^ 2‖ := by
      rw [norm_mul, norm_pow, hd1, one_mul, norm_one]; nlinarith [norm_nonneg w]
    rw [add_comm, kap_norm_add_of_lt h2, norm_mul, norm_pow, hd1, one_mul] at hlt
    nlinarith [norm_nonneg w]

theorem kap_norm_ratCast (l : ℕ) [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l]) (q : ℚ) : ‖ι (q : ℂ)‖ = ‖(q : ℚ_[l])‖ := by
  rw [map_ratCast, ← kap_coe_rat, PadicComplex.norm_extends']

theorem kap_le_one (l : ℕ) [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l]) (z : ℂ) (hz : IsIntegral ℤ z) : ‖ι z‖ ≤ 1 := by
  obtain ⟨p, hp, hpz⟩ := hz
  apply PI.UnitaryGroupMassFormula.UnitDetRoot.norm_le_one_of_root p hp
  have h : (ι.toRingHom) (p.eval₂ (algebraMap ℤ ℂ) z) = 0 := by rw [hpz, map_zero]
  rw [Polynomial.hom_eval₂, RingHom.ext_int (ι.toRingHom.comp (algebraMap ℤ ℂ)) (Int.castRingHom _)] at h
  exact h

theorem kap_unit (l : ℕ) [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l]) (k : ℕ) (hk : ¬ l ∣ k) {x w : ℂ} (hx : IsIntegral ℤ x)
    (hw : IsIntegral ℤ w) (hm : (k : ℂ) = x * w) : ‖ι x‖ = 1 := by
  have e1 := kap_le_one l ι x hx
  have e2 := kap_le_one l ι w hw
  have e3 : ‖ι x‖ * ‖ι w‖ = 1 := by
    rw [← norm_mul, ← map_mul, ← hm, PI.UnitaryGroupMassFormula.UnitDetRoot.norm_iota_natCast l ι k hk]
  refine le_antisymm e1 ?_
  nlinarith [norm_nonneg (ι x), norm_nonneg (ι w)]

theorem kap_repr {a : ℕ} {b c : ℤ} {d : ℕ} (hok : PI.UnitDetRootDefs.CmOK a b c d) {x : ℂ}
    (hx : x ∈ PI.UnitaryGroupMassFormula.UnitDetRoot.KF b d) : ∃ u v : ℚ, x = u + v * PI.UnitDetRootDefs.cmTheta b d :=
  _root_.UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.kap_repr hok hx

theorem kap_norm_of_normOne {a : ℕ} {b c : ℤ} {d : ℕ} (hok : PI.UnitDetRootDefs.CmOK a b c d) (l : ℕ) [Fact l.Prime]
    (hj : jacobiSym (-(d : ℤ)) l = -1) (ι : ℂ ≃+* ℂ_[l]) {x : ℂ} (hx : x ∈ PI.UnitaryGroupMassFormula.UnitDetRoot.KF b d)
    (h1 : x * conj x = 1) : ‖ι x‖ = 1 := by
  obtain ⟨u, v, rfl⟩ := kap_repr hok hx
  have hsq := PI.UnitaryGroupMassFormula.UnitDetRoot.theta_sq hok
  set t := PI.UnitDetRootDefs.cmTheta b d with ht
  have hc : conj ((u : ℂ) + v * t) = (u : ℂ) + v * ((b : ℂ) - t) := by
    rw [map_add, map_mul, map_ratCast, map_ratCast, ht, PI.UnitaryGroupMassFormula.UnitDetRoot.conj_theta]
  rw [hc] at h1
  have hNC : (((u ^ 2 + b * u * v + a * c * v ^ 2 : ℚ)) : ℂ) = 1 := by
    push_cast
    linear_combination h1 + (v : ℂ) ^ 2 * hsq
  have hNq : (u ^ 2 + b * u * v + a * c * v ^ 2 : ℚ) = 1 := by exact_mod_cast hNC
  have h4 : (4 * a * c : ℚ) = b ^ 2 + d := by
    have := hok.1
    have h' : ((4 * (a : ℤ) * c : ℤ) : ℚ) = ((b ^ 2 + d : ℤ) : ℚ) := by rw [this]
    push_cast at h'
    linarith
  set T : ℚ := 2 * u + b * v with hT
  have hTv : T ^ 2 + d * v ^ 2 = 4 := by
    rw [hT]
    linear_combination 4 * hNq - v ^ 2 * h4
  set X := ι ((u : ℂ) + v * t) with hX
  set Y := ι ((u : ℂ) + v * ((b : ℂ) - t)) with hY
  have hXY : X * Y = 1 := by rw [hX, hY, ← map_mul, h1, map_one]
  have hsum : ‖X + Y‖ = ‖(T : ℚ_[l])‖ := by
    have e : (u : ℂ) + v * t + ((u : ℂ) + v * ((b : ℂ) - t)) = ((T : ℚ) : ℂ) := by
      rw [hT]; push_cast; ring
    rw [hX, hY, ← map_add, e, kap_norm_ratCast]
  by_contra hne
  have hn : ‖X‖ * ‖Y‖ = 1 := by rw [← norm_mul, hXY, norm_one]
  have hbig : 1 < ‖X + Y‖ := by
    rcases lt_or_gt_of_ne hne with h | h
    · have hY1 : 1 < ‖Y‖ := by
        by_contra hh
        push Not at hh
        nlinarith [norm_nonneg X, norm_nonneg Y]
      have hlt : ‖X‖ < ‖Y‖ := by linarith
      rw [add_comm, kap_norm_add_of_lt hlt]
      exact hY1
    · have hY1 : ‖Y‖ < 1 := by nlinarith [norm_nonneg X, norm_nonneg Y]
      have hlt : ‖Y‖ < ‖X‖ := by linarith
      rw [kap_norm_add_of_lt hlt]
      exact h
  rw [hsum] at hbig
  have hT0 : (T : ℚ_[l]) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hbig
    linarith
  have key := kap_one_le_norm l d hj ((v : ℚ_[l]) / (T : ℚ_[l]))
  have hTvq : (T : ℚ_[l]) ^ 2 + (d : ℚ_[l]) * (v : ℚ_[l]) ^ 2 = 4 := by exact_mod_cast hTv
  have e : (1 : ℚ_[l]) + (d : ℚ_[l]) * ((v : ℚ_[l]) / (T : ℚ_[l])) ^ 2 = 4 / (T : ℚ_[l]) ^ 2 := by
    field_simp
    linear_combination hTvq
  rw [e, norm_div, norm_pow] at key
  have h4n : ‖(4 : ℚ_[l])‖ ≤ 1 := by
    have := Padic.norm_int_le_one (p := l) 4
    simpa using this
  have hpos : 0 < ‖(T : ℚ_[l])‖ ^ 2 := by positivity
  have : ‖(4 : ℚ_[l])‖ / ‖(T : ℚ_[l])‖ ^ 2 < 1 := by
    rw [div_lt_one hpos]
    nlinarith
  linarith

theorem kap_norm_rt {D : D7} {γ₀ : IsoK D} (k : KapChoice γ₀) (l : ℕ) [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l]) (p : ℕ)
    (hp : p.Prime) (hs : SplitK D p) (hpl : p ≠ l) : ‖ι (k.rt p)‖ = 1 := by
  have hh := k.rt_pow p hp hs
  obtain ⟨w, hw⟩ : ∃ w : 𝓞 D.host.K, w * k.pi p = (p : 𝓞 D.host.K) ^ classNumber D.host.K := by
    have hmem : (p : 𝓞 D.host.K) ^ classNumber D.host.K ∈ (k.pp p).asIdeal ^ classNumber D.host.K :=
      Ideal.pow_mem_pow (k.pp_over p hp hs) _
    rw [k.pi_gen p hp hs, Ideal.mem_span_singleton'] at hmem
    exact hmem
  have hpl' : ¬ l ∣ p ^ classNumber D.host.K := by
    intro h
    have h1 : l ∣ p := (Fact.out : l.Prime).dvd_of_dvd_pow h
    exact hpl (((Nat.prime_dvd_prime_iff_eq Fact.out hp).1 h1).symm)
  have hwK : (w : D.host.K) * (k.pi p : D.host.K) = ((p ^ classNumber D.host.K : ℕ) : D.host.K) := by
    have := congrArg (algebraMap (𝓞 D.host.K) D.host.K) hw
    simpa using this
  let fK : D.host.K →+* ℂ := D.host.φ₀.comp (algebraMap D.host.K D.host.E)
  let fK' : D.host.K →+* ℂ := D.host.φ₀.comp ((D.host.conj : D.host.E →+* D.host.E).comp (algebraMap D.host.K D.host.E))
  have hint : ∀ (g : D.host.K →+* ℂ) (x : 𝓞 D.host.K), IsIntegral ℤ (g (x : D.host.K)) := fun g x =>
    map_isIntegral_int g (NumberField.RingOfIntegers.isIntegral_coe x)
  have e : ∀ g : D.host.K →+* ℂ, ((p ^ classNumber D.host.K : ℕ) : ℂ) = g (k.pi p : D.host.K) * g (w : D.host.K) := by
    intro g
    rw [← map_natCast g, ← hwK, map_mul, mul_comm]
  have h1 : ‖ι (D.host.φ₀ (((k.pi p : 𝓞 D.host.K) : D.host.K) : D.host.E))‖ = 1 :=
    kap_unit l ι _ hpl' (hint fK (k.pi p)) (hint fK w) (e fK)
  have h2 : ‖ι (D.host.φ₀ (D.host.conj (((k.pi p : 𝓞 D.host.K) : D.host.K) : D.host.E)))‖ = 1 :=
    kap_unit l ι _ hpl' (hint fK' (k.pi p)) (hint fK' w) (e fK')
  have hpow : ‖ι (k.rt p)‖ ^ (2 * classNumber D.host.K) = 1 := by
    rw [← norm_pow, ← map_pow, hh, map_div₀, norm_div, h1, h2, div_one]
  have hc := NumberField.classNumber_pos D.host.K
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by omega)).1 hpow

theorem kap_norm_kappa {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (l : ℕ) [Fact l.Prime]
    (hl : ∀ p : ℕ, p.Prime → SplitK D p → p ≠ l) (ι : ℂ ≃+* ℂ_[l]) : ‖ι B.kappa‖ = 1 := by
  show ‖ι (∏ᶠ p : {p : ℕ // p.Prime ∧ SplitK D p}, B.kc.rt p ^ (-(B.kc.yP p)))‖ = 1
  refine finprod_induction (fun z => ‖ι z‖ = 1) (by simp) (fun x y hx hy => ?_) (fun p => ?_)
  · simp only [map_mul, norm_mul, hx, hy, one_mul]
  · simp only [map_zpow₀, norm_zpow]
    rw [kap_norm_rt B.kc l ι p.1 p.2.1 p.2.2 (hl p.1 p.2.1 p.2.2), one_zpow]

theorem kap_notSplit (D : D7) (l : ℕ) (h5 : 5 ≤ l) (hj : jacobiSym (-(D.host.d : ℤ)) l = -1) :
    ∀ p : ℕ, p.Prime → SplitK D p → p ≠ l := by
  intro p _ hs hpl
  subst hpl
  rcases hs with h2 | h1
  · omega
  · rw [h1] at hj
    norm_num at hj

theorem kap_cmTheta_odd (b : ℤ) (hb : Odd b) (d : ℕ) : ∃ k : ℤ, cmTheta b d = cmTheta 1 d + (k : ℂ) := by
  obtain ⟨k, rfl⟩ := hb
  refine ⟨k, ?_⟩
  simp only [cmTheta]
  push_cast
  ring

theorem kap_stable_of_one {V : Type*} [AddCommGroup V] [Module ℂ V] (Λ : AddSubgroup V) (d : ℕ)
    (h : ∀ x ∈ Λ, cmTheta 1 d • x ∈ Λ) (b : ℤ) (hb : Odd b) : ∀ x ∈ Λ, cmTheta b d • x ∈ Λ := by
  intro x hx
  obtain ⟨k, hk⟩ := kap_cmTheta_odd b hb d
  rw [hk, add_smul]
  refine Λ.add_mem (h x hx) ?_
  rw [Int.cast_smul_eq_zsmul]
  exact Λ.zsmul_mem hx k

theorem kap_odd {a : ℕ} {b c : ℤ} {d : ℕ} (h : CmOK a b c d) : Odd b := by
  by_contra hb
  obtain ⟨k, rfl⟩ := Int.not_odd_iff_even.1 hb
  have h1 := h.1
  have h8 := h.2.2.1
  have h2 : (d : ℤ) = 4 * ((a : ℤ) * c - k * k) := by
    have : (k + k) ^ 2 = 4 * (k * k) := by ring
    rw [this] at h1
    linarith
  generalize (a : ℤ) * c - k * k = t at h2
  omega

theorem selfDual_of_fourth_power_block {n : Type} [Fintype n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ))
    (hsd : IsSelfDual (matH (blk4 h)) (pow4 Λ)) : IsSelfDual (matH h) Λ := by
  have key : ∀ (x : n → ℂ) (y : Fin 4 × n → ℂ), altE (matH (blk4 h)) (CmData.embA 0 x) y = altE (matH h) x (slice 0 y) := by
    intro x y
    simp only [altE, matrixForm_fourfoldBlock, CmData.slice_embA]
    rw [Finset.sum_eq_single (0 : Fin 4)]
    · simp
    · intro b _ hb
      simp [hb]
    · intro hh
      exact absurd (Finset.mem_univ _) hh
  ext x
  constructor
  · intro hx
    have h1 : CmData.embA 0 x ∈ dualLat (matH (blk4 h)) (pow4 Λ) := by
      intro y hy
      obtain ⟨m, hm⟩ := hx (slice 0 y) (hy 0)
      exact ⟨m, by rw [key, hm]⟩
    rw [hsd] at h1
    have h2 := h1 0
    rwa [CmData.slice_embA, if_pos rfl] at h2
  · intro hx y hy
    have h1 : CmData.embA 0 x ∈ dualLat (matH (blk4 h)) (pow4 Λ) := by
      rw [hsd]
      exact CmData.embA_mem Λ 0 hx
    obtain ⟨m, hm⟩ := h1 _ (CmData.embA_mem Λ 0 hy)
    refine ⟨m, ?_⟩
    rw [key, CmData.slice_embA, if_pos rfl] at hm
    exact hm

section Base

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ)

theorem kappa_selfDual_fourth_power_lattice (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) :
    IsSelfDual (matH (blk4 (hOne B.L D.what₂.Tau))) (pow4 B.lamM) := by
  have h := ((B.latAll hcc hδ (base_linkage_nonempty D cc δ B)).1 2 2 _ _
    (Formalism.MainNotions.GlobalTheoryTheory.Inhab.Adm_std D 2 2 even_two even_two)).1
  rw [show TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ) = _ from B.areaOK, show TaylorLogMetric.La D B.tor _ _ = _ from B.lat0OK 2 2] at h
  have h2 := SO.selfDual_img _ _ (SO.reix D.what₂.Tau) (SO.reix_isom B.L D.what₂.Tau) _ h
  rw [SO.reix_pow] at h2
  exact h2

theorem kap_selfDual_lamM (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) :
    IsSelfDual (matH (hOne B.L D.what₂.Tau)) B.lamM :=
  selfDual_of_fourth_power_block _ _ (kappa_selfDual_fourth_power_lattice B hcc hδ)

theorem kap_stable_lamM (b : ℤ) (hb : Odd b) : ∀ x ∈ B.lamM, cmTheta b D.host.d • x ∈ B.lamM := by
  refine kap_stable_of_one _ _ (fun x hx => ?_) b hb
  have := SO.lamMM_smul (AR.om D) hx
  rw [← SO.theta_eq] at this
  exact this

theorem kap_stable_latA (b : ℤ) (hb : Odd b) : ∀ x ∈ B.latA, cmTheta b D.host.d • x ∈ B.latA := by
  rintro x ⟨x', hx', rfl⟩
  refine ⟨cmTheta b D.host.d • x', fun a' => kap_stable_lamM B b hb _ (hx' a'), ?_⟩
  simp

end Base

theorem kappa_at_inert_prime : KapInert := by
  intro D cc δ B hcc hδ a₀ b₀ c₀ ha hd lam hlam hcm hB l _ h5 hj ι u hiso j1 _ j2
  rw [kap_norm_kappa B l (kap_notSplit D l h5 hj) ι, one_pow, one_mul]
  obtain ⟨hL, -⟩ := hB
  have hS : StdData B.L B.ω₀ (hOne B.L D.what₂.Tau) B.lamM (alphaQ B.cq (matH (hOne B.L D.what₂.Tau)))
    (alphaQ B.cq (stdH B.L (Fin 4 × D.what₂.Tau))) B.gC := B.stdOK hcc hδ
  have hsd : IsSelfDual (stdH B.L (Fin 4 × D.what₂.Tau)) B.latA := hS.selfDual
  have i1 : relIdx (stdLat B.L (Fin 4 × D.what₂.Tau)) B.latA ≠ 0 := hS.idx₁
  have i2 : relIdx B.latA (stdLat B.L (Fin 4 × D.what₂.Tau)) ≠ 0 := hS.idx₂
  have hsta := kap_stable_latA B b₀ (kap_odd hcm)
  rw [hL] at hiso j1 j2 hsd i1 i2
  obtain ⟨hmem, hone⟩ := PI.UnitaryGroupMassFormula.UnitDetRoot.detInK a₀ b₀ c₀ D.host.d ha hd lam hlam (Fin 4 × D.what₂.Tau) B.latA
    ⟨hcm, hsd, hsta, i1, i2⟩ u ⟨hiso, j1, j2⟩
  exact kap_norm_of_normOne hcm l hj ι hmem hone

theorem kappa_K1_hypothesis : KappaFirstKernelHypothesis := by
  intro D cc δ B hcc hδ a₀ b₀ c₀ ha hd lam hlam hcm hB l _ h5 hj ι
  have hK : B.KappaAt l ι := kappa_at_inert_prime D cc δ B hcc hδ a₀ b₀ c₀ ha hd lam hlam hcm hB l h5 hj ι
  obtain ⟨hL, hω⟩ := hB
  have hS : StdData B.L B.ω₀ (hOne B.L D.what₂.Tau) B.lamM (alphaQ B.cq (matH (hOne B.L D.what₂.Tau)))
    (alphaQ B.cq (stdH B.L (Fin 4 × D.what₂.Tau))) B.gC := B.stdOK hcc hδ
  have hsd := kap_selfDual_lamM B hcc hδ
  have hst := kap_stable_lamM B b₀ (kap_odd hcm)
  have hspec := B.thMM_spec (B.stdOK hcc hδ)
  have hmem : B.thMM ∈ Th (matH (hOne B.L D.what₂.Tau)) (alphaQ B.cq (matH (hOne B.L D.what₂.Tau))) B.lamM := hspec.1
  have h2 : tens4 B.thMM = B.kappa • kernel4 B.L B.ω₀ B.lamM
      (alphaQ (Real.sqrt D.host.d / 2) (stdH B.L (Fin 4 × D.what₂.Tau))) B.gC := hspec.2
  have iso := hS.isom
  have i1 := hS.idx₁
  have i2 := hS.idx₂
  unfold Base.KappaAt Base.latA at hK
  rw [hω] at h2 ⊢
  rw [hL] at h2 hK iso i1 i2 hsd hmem ⊢
  have hsda := CmData.selfDual_img _ _ B.gC iso _ (CmData.isSelfDual_matH_blk4_pow4 _ B.lamM hsd)
  have hsta : ∀ x ∈ imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM),
      cmTheta b₀ D.host.d • x ∈ imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM) := by
    rintro x ⟨x', hx', rfl⟩
    refine ⟨cmTheta b₀ D.host.d • x', fun a' => hst _ (hx' a'), ?_⟩
    simp
  obtain ⟨u, huiso, hufix, j1, jl, j2⟩ := localStandard a₀ b₀ c₀ D.host.d ha hd lam hlam hcm (Fin 4 × D.what₂.Tau) _
    hsda hsta i1 i2 l Fact.out
  have hκu := hK u huiso j1 jl j2
  rw [← KR.imgLat_trans] at j1 jl j2
  have hg₁ : IsIsom (matH (blk4 (hOne (cmL a₀ b₀ D.host.d ha hd lam hlam) D.what₂.Tau)))
      (stdH (cmL a₀ b₀ D.host.d ha hd lam hlam) (Fin 4 × D.what₂.Tau))
      ((B.gC.trans u : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) :
        (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) := by
    intro x y
    have h1 := huiso (B.gC x) (B.gC y)
    have h0 := iso x y
    simp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply] at h0 h1 ⊢
    rw [h1, h0]
  have D0 := stdDataCm a₀ b₀ c₀ D.host.d ha hd lam hlam hcm.1 hcm.2.1 hcm.2.2.1 D.what₂.Tau _ B.lamM B.gC iso hsd hst i1 i2
  have D1 := stdDataCm a₀ b₀ c₀ D.host.d ha hd lam hlam hcm.1 hcm.2.1 hcm.2.2.1 D.what₂.Tau _ B.lamM (B.gC.trans u) hg₁
    hsd hst j1 j2
  have hcomp : B.gC.symm.trans (B.gC.trans u) = u := by
    ext x
    simp
  have hfix : ∀ x, (B.gC.trans u) x = B.gC x → x = 0 := by
    intro x hx
    have h1 : B.gC x = 0 := hufix _ hx
    simpa using congrArg B.gC.symm h1
  rw [← hcomp] at hκu
  obtain ⟨c, hc8, hc⟩ := kernelRatio _ _ D.what₂.Tau _ B.lamM _ _ B.gC (B.gC.trans u) D0 D1 hfix
  exact ⟨B.gC.trans u, B.kappa * c, D1, jl, KR.norm_mul_eq_one ι B.kappa c _ hc8 hκu, hmem,
    by rw [h2, hc, smul_smul]; rfl⟩

theorem K1_theta_inert_prime : FirstKernelThetaInert := by
  intro D cc δ B hcc hδ a₀ b₀ c₀ ha hd lam hlam hcm hB l _ h5 hj ι
  obtain ⟨g, e, hS, hidx, he, hmem, ht⟩ := kappa_K1_hypothesis D cc δ B hcc hδ a₀ b₀ c₀ ha hd lam hlam hcm hB l h5 hj ι
  refine ⟨g, hS, hidx, fun g2 g3 ε s2 hN hg2 hg3 hD hε hth t N hN0 hlN hNt σ γ B' hF => ?_⟩
  exact Formalism.L2.Th1.Top.local_kappa_shape_holds l h5 B.L ι g2 g3 ε s2 hN hg2 hg3 hD hε hth B.ω₀ hS.per hS.half D.what₂.Tau
    (hOne B.L D.what₂.Tau) B.lamM _ _ g hS hidx e he.le B.thMM hmem ht t N hN0 hlN hNt σ γ B' hF

end Formalism.L2.KerInert.Kap
