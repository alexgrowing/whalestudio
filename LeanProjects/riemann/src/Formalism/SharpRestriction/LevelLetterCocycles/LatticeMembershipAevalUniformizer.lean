import Formalism.SharpRestriction.LevelLetterCocycles.InId0OfMem
import Formalism.SharpRestriction.LevelLetterCocycles.DvOZeroHigh

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.UGen

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.KL

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

local notation "ιE" => algebraMap (LetA O n) W.EE
local notation "aev" => Polynomial.aeval (AlgHom.toLinearMap (W.γE W.gam) : Module.End O W.EE)

theorem uniformizer_isUnit_etale (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) : IsUnit (ιE W.π₀) := by
  obtain ⟨w, hw⟩ := hR.2.2.1
  rw [hw, map_mul, map_pow]
  exact (w.isUnit.map _).mul (W.EE_π.pow _)

def πinv (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) : W.EE := (((uniformizer_isUnit_etale W hR).unit⁻¹ : W.EEˣ) : W.EE)

theorem πinv_mul (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) : πinv W hR * ιE W.π₀ = 1 := by
  unfold πinv
  nth_rewrite 2 [← (uniformizer_isUnit_etale W hR).unit_spec]
  exact Units.inv_mul _

theorem nl_of_pi0Lam (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) [IsDomain O]
    (hbij : Function.Bijective (algebraMap K₀ K)) (A : ArcP n) (hA : A.OK) (c : ZMod n)
    (hc : c ∈ A.cuts) (T : LocLat G Qp LL O) (hT : Win W A T) {d : ℕ} (b : Fin d → W.DD T)
    (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T (c - ((A.len c : ℕ) : ZMod n)) b) (f : Fin d → W.EE)
    (hf : ∀ k, InFr W c (W.π₀ * abelian₂ W A c (A.len c)) 1 (f k)) :
    ∃ g, InNL W T c (A.len c) (abelian₂ W A c (A.len c)) b g ∧ ∀ k, f k = ιE W.π₀ * g k := by
  set e := A.len c with he
  set Λ := abelian₂ W A c e with hΛ
  have hc' : c - ((e : ℕ) : ZMod n) ∈ A.cuts := ((hA.2.2.1 c hc).2.2).1
  have hce : c - ((e : ℕ) : ZMod n) + ((e : ℕ) : ZMod n) = c := sub_add_cancel _ _
  set g : Fin d → W.EE := fun k => πinv W hR * f k with hg
  have hfg : ∀ k, f k = ιE W.π₀ * g k := fun k => by
    rw [hg, ← mul_assoc, mul_comm (ιE W.π₀), πinv_mul, one_mul]
  have hgu : ∀ k, ∃ u ∈ W.AΔ, g k = ιE (letE c * Λ * u) := by
    intro k
    obtain ⟨u, hu, hfu⟩ := hf k
    refine ⟨u, hu, ?_⟩
    rw [map_one, one_mul] at hfu
    show πinv W hR * f k = _
    rw [hfu]
    simp only [map_mul]
    have := πinv_mul W hR
    linear_combination (ιE (letE c) * ιE Λ * ιE u) * this
  refine ⟨g, ⟨fun k => ?_, 0, ?_⟩, hfg⟩
  · obtain ⟨u, hu, hgk⟩ := hgu k
    have hΛm : Λ ∈ W.AΔ := W.AΔ.prod_mem fun t _ => W.AΔ.pow_mem
      (Formalism.MainNotions.UnusedSlot80.KL.ps_mem W (Formalism.MainNotions.UnusedSlot80.UnivC.uniformizer_mem_delta_invariants W) t) _
    refine ⟨Λ * Λ * u, W.AΔ.mul_mem (W.AΔ.mul_mem hΛm hΛm) hu, ?_⟩
    rw [hgk, ← map_mul]; congr 1; ring
  · refine ⟨d, g, fun i => Pi.single i 1, fun _ s => ((A.Hs c e s : ℕ) : ℤ), fun i => ⟨?_, ?_⟩, fun k => ?_⟩
    · obtain ⟨u, hu, hgk⟩ := hgu i
      unfold InId
      have h1 : (∏ s ∈ Finset.range e, ps W s ^ (-((A.Hs c e s : ℕ) : ℤ)).toNat) = 1 :=
        Finset.prod_eq_one fun s _ => by rw [show (-((A.Hs c e s : ℕ) : ℤ)).toNat = 0 by omega, pow_zero]
      have h2 : (∏ s ∈ Finset.range e, ps W s ^ (((A.Hs c e s : ℕ) : ℤ)).toNat) = Λ := by
        rw [hΛ, abelian₂]; exact Finset.prod_congr rfl fun s _ => by rw [Int.toNat_natCast]
      rw [h1, h2]
      exact ⟨u, hu, by rw [map_one, one_mul, hgk]⟩
    · intro s hs
      have := Formalism.MainNotions.UnusedSlot80.LevC.dvO_filLow W hbij A hA _ hc' T hT b hb e s hs (Pi.single i 1)
      rw [hce] at this
      exact this
    · simp only [lE, pow_zero, one_mul]
      rw [Finset.sum_eq_single k]
      · simp
      · intro i _ hik; simp [Pi.single_apply, Ne.symm hik]
      · simp

variable [IsDomain O]

include W in
theorem p_ne_zero_O' : ((PD.p : ℕ) : O) ≠ 0 := by
  intro h
  have h1 : ((PD.p : ℕ) : LL) = 0 := by rw [← map_natCast (algebraMap O LL), h, map_zero]
  have h2 := W.v_l
  rw [h1, AddValuation.map_zero] at h2
  exact absurd h2 (by simp)

theorem uniformizer_dvd_of_prime_power (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (a : ZMod n) {u v : LetA O n}
    (hu : u ∈ W.AΔ) (K : ℕ) (h : lA W ^ K * (letE a * u) = W.π₀ * (letE a * v)) :
    ∃ w ∈ W.AΔ, (letE a : LetA O n) * u = W.π₀ * (letE a * w) := by
  obtain ⟨o, w, hw, hval⟩ := value0 W hR a u hu
  have hrel : lA W ^ K * (letE a * algebraMap O (LetA O n) o) =
      W.π₀ * (letE a * v - lA W ^ K * (letE a * w)) := by
    rw [mul_sub, ← h, hval]; ring
  have h1 := congrArg (fun z : LetA O n => PowerSeries.constantCoeff (z a)) hrel
  simp only [Pi.mul_apply, Pi.pow_apply, lA, Pi.natCast_apply, letE, Pi.single_eq_same, one_mul,
    Algebra.algebraMap_eq_smul_one, Pi.smul_apply, Pi.one_apply, PowerSeries.smul_eq_C_mul, mul_one,
    map_mul, map_pow, map_natCast, PowerSeries.constantCoeff_C, LocWach.π₀,
    Formalism.MainNotions.UnusedSlot80.ToolsR.π₀₁_cc hR, zero_mul] at h1
  have ho : o = 0 := by
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact absurd h2 (pow_ne_zero K (p_ne_zero_O' W))
    · exact h2
  refine ⟨w, hw, ?_⟩
  rw [hval, ho, map_zero, zero_add]; ring

theorem sat_l (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (T : LocLat G Qp LL O) (A : ArcP n) (c : ZMod n)
    (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (K : ℕ) (f : Fin d → W.EE)
    (hf : ∀ k, InFr W c 1 (abelian₂ W A c e) (f k)) (g : Fin d → W.EE)
    (hg : InNL W T c e (abelian₂ W A c e) b g) (hfg : ∀ k, lE W K * f k = ιE W.π₀ * g k) :
    ∃ g', InNL W T c e (abelian₂ W A c e) b g' ∧ ∀ k, f k = ιE W.π₀ * g' k := by
  set Λ := abelian₂ W A c e with hΛ
  set g' : Fin d → W.EE := fun k => πinv W hR * f k with hg'
  have hfg' : ∀ k, f k = ιE W.π₀ * g' k := fun k => by
    rw [hg', ← mul_assoc, mul_comm (ιE W.π₀), πinv_mul, one_mul]
  have hcoef : ∀ k, InFr W c 1 Λ (g' k) := by
    intro k
    obtain ⟨u, hu, hfu⟩ := hf k
    obtain ⟨v', hv', hgv⟩ := hg.1 k
    have hrel : lA W ^ K * (letE c * u) = W.π₀ * (letE c * v') := by
      apply W.EE_inj
      have e1 := hfu; have e2 := hgv
      rw [mul_one] at e1 e2
      calc ιE (lA W ^ K * (letE c * u)) = lE W K * (ιE Λ * f k) := by
            rw [map_mul, ← e1, Formalism.MainNotions.UnusedSlot80.KL.ι_lE]
        _ = ιE Λ * (lE W K * f k) := by ring
        _ = ιE Λ * (ιE W.π₀ * g k) := by rw [hfg k]
        _ = ιE W.π₀ * (ιE Λ * g k) := by ring
        _ = ιE (W.π₀ * (letE c * v')) := by rw [e2]; simp only [map_mul]
    obtain ⟨w, hw, hwe⟩ := uniformizer_dvd_of_prime_power W hR c hu K hrel
    refine ⟨w, hw, ?_⟩
    show ιE Λ * (πinv W hR * f k) = ιE (letE c * 1 * w)
    rw [mul_left_comm, hfu]
    try simp only [mul_one]
    rw [hwe, map_mul, ← mul_assoc, πinv_mul, one_mul]
  obtain ⟨κ, hs⟩ := hg.2
  refine ⟨g', ⟨hcoef, κ + K, ?_⟩, hfg'⟩
  convert hs using 1
  funext k
  show lE W (κ + K) * (πinv W hR * f k) = lE W κ * g k
  rw [lE_add']
  linear_combination (lE W κ * πinv W hR) * hfg k + (lE W κ * g k) * πinv_mul W hR

theorem eval_one_dvd_prime_pow (hKL : KillerLevCore W) (hCA : Formalism.MainNotions.LiftingTheory.CaseA W)
    (hinj : Function.Injective (algebraMap O LL))
    (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x) (ell : ℕ) (JS : Finset ℤ) :
    ∃ (N : ℕ) (o : O), o * (PPO W ell JS).eval 1 = ((PD.p : ℕ) : O) ^ N := by
  obtain ⟨hv, -⟩ := hKL hCA ell JS
  set N := ell + ∑ i ∈ JS.erase 0, (ell + 1 + padicValInt PD.p i) with hN
  set z := algebraMap O LL ((PPO W ell JS).eval 1) with hz
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0, AddValuation.map_zero] at hv
    exact WithTop.top_ne_coe hv
  have hx : v (((PD.p : ℕ) : LL) ^ N * z⁻¹) = 0 := by
    rw [AddValuation.map_mul, AddValuation.map_pow, AddValuation.map_inv, hv]
    have hl : v ((PD.p : ℕ) : LL) = 1 := W.v_l
    rw [hl]
    have : (N • (1 : WithTop ℚ)) = ((N : ℚ) : WithTop ℚ) := by simp
    rw [this]
    have : ((N : ℕ) : WithTop ℚ) = ((N : ℚ) : WithTop ℚ) := by simp
    rw [this, ← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_add, add_neg_cancel]
    rfl
  obtain ⟨o, ho⟩ := hO2 _ (le_of_eq hx.symm)
  refine ⟨N, o, hinj ?_⟩
  rw [map_mul, ho, ← hz, map_pow, map_natCast, mul_assoc, inv_mul_cancel₀ hz0, mul_one]

theorem exists_gammaA_pi0_eq_pi0_mul_of_RingP (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u := by
  obtain ⟨w, hw⟩ := hR.2.2.2.2.2.2.1
  rw [Formalism.MainNotions.UnusedSlot80.ToolsR.eat_qP] at hw
  have hwq : (w : LetA O n) * Formalism.MainNotions.WachCoordinates.qP W ∈ W.AΔ := by
    refine Formalism.MainNotions.UnusedSlot80.ToolsR.cancel_AΔ hR.1 (fun i => Formalism.MainNotions.UnusedSlot80.ToolsR.π₀₁_ne hR) ?_
    have e : W.π₀ * ((w : LetA O n) * Formalism.MainNotions.WachCoordinates.qP W) = W.γA W.gam W.π₀ - W.π₀ := by rw [hw]; ring
    rw [e]
    exact W.AΔ.sub_mem (Formalism.MainNotions.UnusedSlot80.KL.γA_mem W W.gam hR.1) hR.1
  exact ⟨1 + (w : LetA O n) * Formalism.MainNotions.WachCoordinates.qP W, W.AΔ.add_mem W.AΔ.one_mem hwq, by
    linear_combination hw⟩

theorem lattice_membership_aeval_uniformizer (hS : PsStable W) (hP : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u)
    (T : LocLat G Qp LL O) (A : ArcP n) (a : ZMod n) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T)
    (P : Polynomial O) : ∀ g : Fin d → W.EE, InNL W T a e (abelian₂ W A a e) b g →
      ∃ g' : Fin d → W.EE, InNL W T a e (abelian₂ W A a e) b g' ∧
        ∀ k, aev P (ιE W.π₀ * g k) = ιE W.π₀ * g' k := by
  induction P using Polynomial.induction_on with
  | C c =>
    intro g hg
    refine ⟨fun k => c • g k, Formalism.MainNotions.UnusedSlot80.UnivC.inNL_smul W T A a e b c hg, fun k => ?_⟩
    simp only [Polynomial.aeval_C, Module.algebraMap_end_apply]
    exact (mul_smul_comm c (ιE W.π₀) (g k)).symm
  | add p q hp hq =>
    intro g hg
    obtain ⟨g₁, h₁, e₁⟩ := hp g hg
    obtain ⟨g₂, h₂, e₂⟩ := hq g hg
    refine ⟨g₁ + g₂, Formalism.MainNotions.UnusedSlot80.UnivC.inNL_add W T A a e b h₁ h₂, fun k => ?_⟩
    simp only [map_add, LinearMap.add_apply, e₁, e₂, Pi.add_apply, mul_add]
  | monomial k c ih =>
    intro g hg
    obtain ⟨u, hu, hγ⟩ := hP
    have hx : ∀ k', (AlgHom.toLinearMap (W.γE W.gam) : Module.End O W.EE) (ιE W.π₀ * g k') =
        ιE W.π₀ * (ιE u * W.γE W.gam (g k')) := by
      intro k'
      rw [AlgHom.toLinearMap_apply, map_mul, W.γE_ext]
      show ιE (W.γA W.gam W.π₀) * _ = _
      rw [hγ, map_mul]
      ring
    obtain ⟨g', hg', e'⟩ := ih (fun k' => ιE u * W.γE W.gam (g k'))
      (Formalism.MainNotions.UnusedSlot80.UnivC.inNL_mulι W T A a e b hu (Formalism.MainNotions.UnusedSlot80.UnivC.inNL_γ W T A a e b hS hg))
    refine ⟨g', hg', fun k' => ?_⟩
    rw [pow_succ, ← mul_assoc, Polynomial.aeval_mul, Module.End.mul_apply, Polynomial.aeval_X, hx, e']

theorem pp_inv (hS : PsStable W) (hP : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u)
    (T : LocLat G Qp LL O) (A : ArcP n) (a : ZMod n) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T)
    (P : Polynomial O) (f : Fin d → W.EE) (hf : InvNL W T a e (abelian₂ W A a e) b f) :
    ∃ g, InNL W T a e (abelian₂ W A a e) b g ∧ ∀ k, aev P (f k) - P.eval 1 • f k = ιE W.π₀ * g k := by
  obtain ⟨g, hg, hfg⟩ := hf
  set p' : Polynomial O := P - Polynomial.C (P.eval 1) with hp'
  have hroot : p'.IsRoot 1 := by simp [hp']
  set S := p' /ₘ (Polynomial.X - Polynomial.C 1) with hSdef
  have hS' : (Polynomial.X - Polynomial.C 1) * S = p' := (Polynomial.mul_divByMonic_eq_iff_isRoot).2 hroot
  obtain ⟨g', hg', e'⟩ := lattice_membership_aeval_uniformizer W hS hP T A a e b S g hg
  refine ⟨g', hg', fun k => ?_⟩
  have h1 : aev P (f k) - P.eval 1 • f k = aev p' (f k) := by
    rw [hp', map_sub, LinearMap.sub_apply, Polynomial.aeval_C, Module.algebraMap_end_apply]
  rw [h1, ← hS', mul_comm, map_mul, Module.End.mul_apply, map_sub, LinearMap.sub_apply,
    Polynomial.aeval_X, Polynomial.aeval_C, map_one, Module.End.one_apply, AlgHom.toLinearMap_apply,
    hfg k, e' k]

end Formalism.MainNotions.UnusedSlot80.UGen
