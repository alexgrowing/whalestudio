import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.HeisLineTheta

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM

variable {F : Type} [Field F] [NumberField F]

def embInf (x : InfiniteAdeleRing F) : AF F := (x, 0)

def embFin (y : FiniteAdeleRing (𝓞 F) F) : AF F := (0, y)

theorem eq_embInf_add_embFin (x : AF F) : x = embInf (Prod.fst x) + embFin (Prod.snd x) := by
  show x = ((x.1 + 0, 0 + x.2) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
  rw [add_zero, zero_add]
  rfl

theorem embFin_natCast_mul (n : ℕ) (a : FiniteAdeleRing (𝓞 F) F) :
    embFin ((n : FiniteAdeleRing (𝓞 F) F) * a) = n • embFin a := by
  show ((0, (n : FiniteAdeleRing (𝓞 F) F) * a) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) =
    ((n • (0 : InfiniteAdeleRing F), n • a) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
  rw [smul_zero, nsmul_eq_mul]

theorem embFin_add_neg (a : FiniteAdeleRing (𝓞 F) F) : embFin a + embFin (-a) = 0 := by
  show ((0 + 0, a + -a) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) = 0
  rw [add_zero, add_neg_cancel]
  rfl

theorem at_embInf (x : InfiniteAdeleRing F) : At (evI F) (embInf x) := by
  intro s hs
  have hs' : InfiniteAdeleRing.ringEquiv_mixedSpace F s.1 = 0 := hs
  have h1 : s.1 = 0 := (map_eq_zero_iff _ (RingEquiv.injective _)).1 hs'
  show ((s.1 * x, s.2 * 0) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) = 0
  rw [h1, zero_mul, mul_zero]
  rfl

theorem norm_of_at {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {a : AF F} (ha : At (evI F) a) : ‖ψ a‖ = 1 := by
  rw [hψ.2.2 a ha, Complex.norm_exp]
  simp

theorem norm_fin {ψ : AddChar (AF F) ℂ} (hc : Continuous ψ) (y : FiniteAdeleRing (𝓞 F) F) :
    ‖ψ (embFin y)‖ = 1 := by
  set K := {a : FiniteAdeleRing (𝓞 F) F | ∀ v, a v ∈ HeightOneSpectrum.adicCompletionIntegers F v} with hKdef
  have hK : IsCompact K := GlobalTheory.AdeleCocompact.isCompact_integral F
  have hφ : Continuous fun a : FiniteAdeleRing (𝓞 F) F => ψ (embFin a) :=
    hc.comp (continuous_const.prodMk continuous_id)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hφ.continuousOn
  have hmul : ∀ (n : ℕ) (a : FiniteAdeleRing (𝓞 F) F),
      ψ (embFin ((n : FiniteAdeleRing (𝓞 F) F) * a)) = ψ (embFin a) ^ n := by
    intro n a
    rw [embFin_natCast_mul, AddChar.map_nsmul_eq_pow]
  have hKn : ∀ a ∈ K, ∀ n : ℕ, (n : FiniteAdeleRing (𝓞 F) F) * a ∈ K := fun a ha n v => by
    rw [GlobalTheory.IntegralFinAdele.mul_apply', GlobalTheory.IntegralFinAdele.natCast_apply]
    exact mul_mem (HeightOneSpectrum.coe_mem_adicCompletionIntegers v _) (ha v)
  have hle : ∀ a ∈ K, ‖ψ (embFin a)‖ ≤ 1 := by
    intro a ha
    by_contra h
    push_neg at h
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M h
    have := hM _ (hKn a ha n)
    rw [hmul, norm_pow] at this
    linarith
  have hneg : ∀ a ∈ K, -a ∈ K := fun a ha v => by
    have : (-a) v = -(a v) := rfl
    rw [this]
    exact neg_mem (ha v)
  have h1 : ∀ a ∈ K, ‖ψ (embFin a)‖ = 1 := by
    intro a ha
    have e : ψ (embFin a) * ψ (embFin (-a)) = 1 := by
      rw [← AddChar.map_add_eq_mul, embFin_add_neg, AddChar.map_zero_eq_one]
    have e2 := congrArg norm e
    rw [norm_mul, norm_one] at e2
    have := hle a ha
    have := hle (-a) (hneg a ha)
    nlinarith [norm_nonneg (ψ (embFin a)), norm_nonneg (ψ (embFin (-a)))]
  obtain ⟨N, hN, hNa⟩ := GlobalTheory.IntegralFinAdele.exists_nat_mul_integral F y
  have := h1 _ hNa
  rw [hmul, norm_pow] at this
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hN.ne').1 this

theorem norm_psi {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (x : AF F) : ‖ψ x‖ = 1 := by
  rw [eq_embInf_add_embFin x, AddChar.map_add_eq_mul, norm_mul, norm_of_at hψ (at_embInf _), norm_fin hψ.1, one_mul]

end GlobalTheory.HeisLineTheta

namespace GlobalTheory.HeisLineTheta

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM

variable {F : Type} [Field F] [NumberField F]
variable {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ]

theorem e_smul (d : Darboux B κ) (r : AF F) (u : W) : d.e (r • u) = (r • (d.e u).1, r • (d.e u).2) := by
  rw [map_smul]
  rfl

theorem realAd_add (s h : ℝ) : realAd F (s + h) = realAd F s + realAd F h := by
  simp only [realAd, map_add]
  rfl

theorem realAd_zero : realAd F 0 = 0 := by
  simp only [realAd, map_zero]
  rfl

theorem rho_line_add (d : Darboux B κ) (ψ : AddChar (AF F) ℂ) (u : W) (s h : ℝ) (Ψ : (κ → AF F) → ℂ)
    (z : κ → AF F) :
    d.rho ψ (realAd F (s + h) • u) Ψ z = d.rho ψ (realAd F s • u) (d.rho ψ (realAd F h • u) Ψ) z := by
  simp only [Darboux.rho, schr, e_smul, realAd_add]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  · simp only [dotProduct_smul, smul_dotProduct, add_dotProduct, dotProduct_add, smul_eq_mul, add_smul]
    have h2 : ⅟(2 : AF F) * 2 = 1 := invOf_mul_self 2
    linear_combination (realAd F s * realAd F h * ((d.e u).1 ⬝ᵥ (d.e u).2)) * h2
  · simp only [add_smul]
    abel

theorem rho_zero (d : Darboux B κ) (ψ : AddChar (AF F) ℂ) (u : W) (Ψ : (κ → AF F) → ℂ) :
    d.rho ψ (realAd F 0 • u) Ψ = Ψ := by
  funext z
  simp [Darboux.rho, schr, realAd_zero]

theorem hasDerivAt_line (d : Darboux B κ) (ψ : AddChar (AF F) ℂ) (u : W) {Φ Φ' : (κ → AF F) → ℂ}
    (hd : ∀ x, HasDerivAt (fun t : ℝ => d.rho ψ (realAd F t • u) Φ x) (Φ' x) 0) (z : κ → AF F) (t : ℝ) :
    HasDerivAt (fun s : ℝ => d.rho ψ (realAd F s • u) Φ z) (d.rho ψ (realAd F t • u) Φ' z) t := by
  have h1 : HasDerivAt (fun h : ℝ => d.rho ψ (realAd F (t + h) • u) Φ z) (d.rho ψ (realAd F t • u) Φ' z) (t - t) := by
    have e : (fun h : ℝ => d.rho ψ (realAd F (t + h) • u) Φ z) = fun h =>
        ψ (z ⬝ᵥ (d.e (realAd F t • u)).2 + ⅟(2 : AF F) * ((d.e (realAd F t • u)).1 ⬝ᵥ (d.e (realAd F t • u)).2)) *
          d.rho ψ (realAd F h • u) Φ (z + (d.e (realAd F t • u)).1) := by
      funext h
      rw [rho_line_add]
      rfl
    rw [e, sub_self]
    exact (hd (z + (d.e (realAd F t • u)).1)).const_mul _
  have h2 := h1.comp_sub_const t t
  simpa only [add_sub_cancel] using h2

theorem norm_rho {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (d : Darboux B κ) (w : W) (Ψ : (κ → AF F) → ℂ)
    (z : κ → AF F) : ‖d.rho ψ w Ψ z‖ = ‖Ψ (z + (d.e w).1)‖ := by
  simp only [Darboux.rho, schr, norm_mul, norm_psi hψ, one_mul]

end GlobalTheory.HeisLineTheta

namespace GlobalTheory.HeisLineTheta

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM
open scoped Classical

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem summable_one_add_norm_inv_pow (L : Submodule ℤ (κ → mixedEmbedding.mixedSpace F)) [DiscreteTopology L] :
    Summable fun z : L => (1 + ‖z‖)⁻¹ ^ (Module.finrank ℤ L + 1) := by
  refine Summable.of_norm_bounded_eventually (ZLattice.summable_norm_pow_inv L _ (Nat.lt_succ_self _)) ?_
  refine (Set.finite_singleton (0 : L)).subset fun z hz => ?_
  by_contra h0
  apply hz
  have hz0 : 0 < ‖z‖ := norm_pos_iff.2 h0
  show ‖(1 + ‖z‖)⁻¹ ^ (Module.finrank ℤ L + 1)‖ ≤ ‖z‖⁻¹ ^ (Module.finrank ℤ L + 1)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  gcongr
  linarith

theorem pureA_add (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (ξ : κ → F)
    (y : κ → AF F) :
    pureA F f g ((fun i => algebraMap F (AF F) (ξ i)) + y) =
      f ((fun i => mixedEmbedding F (ξ i)) + fun i => evI F (y i)) *
        g (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i) + Prod.snd (y i)) := by
  unfold pureA
  congr 2
  funext i
  simp only [Pi.add_apply]
  rw [show ((algebraMap F (AF F) (ξ i) + y i) : AF F).1 = (algebraMap F (AF F) (ξ i)).1 + (y i).1 from rfl, map_add,
    InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  rfl

theorem majorant_pure (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) (yf : κ → FiniteAdeleRing (𝓞 F) F) (R : ℝ) :
    ∃ c : (κ → F) → ℝ, Summable c ∧ ∀ (ξ : κ → F) (y : κ → AF F), (∀ i, Prod.snd (y i) = yf i) →
      ‖fun i => evI F (y i)‖ ≤ R → ‖pureA F f g ((fun i => algebraMap F (AF F) (ξ i)) + y)‖ ≤ c ξ := by
  obtain ⟨Bg, hB⟩ := hg.1.continuous.bounded_above_of_compact_support hg.2
  set K := (fun x => x - yf) '' tsupport g with hKdef
  have hKc : IsCompact K := hg.2.isCompact.image (continuous_id.sub continuous_const)
  obtain ⟨N, hN, hK⟩ := exists_nat_mul_integral_of_isCompact F hKc
  haveI := discreteTopology_denomLattice F κ hN
  set L := denomLattice F κ N with hL
  set k := Module.finrank ℤ L + 1 with hk
  have hw := summable_one_add_norm_inv_pow L
  set C := 2 ^ k * ((Finset.Iic (k, 0)).sup fun m => SchwartzMap.seminorm ℂ m.1 m.2) f with hCdef
  have hC : ∀ x, (1 + ‖x‖) ^ k * ‖f x‖ ≤ C := fun x => by
    have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k, 0)) le_rfl le_rfl f x
    rwa [norm_iteratedFDeriv_zero] at this
  have hC0 : 0 ≤ C := le_trans (by positivity) (hC 0)
  set R' := max R 0 with hR'
  set ι : (κ → F) → (κ → mixedEmbedding.mixedSpace F) := fun ξ i => mixedEmbedding F (ξ i) with hι
  set S : Set (κ → F) := {ξ | ι ξ ∈ L} with hS
  set h : (κ → F) → ℝ := fun ξ => max Bg 0 * C * (1 + R') ^ k * (1 + ‖ι ξ‖)⁻¹ ^ k with hh
  refine ⟨S.indicator h, ?_, fun ξ y hyf hyR => ?_⟩
  · rw [← summable_subtype_iff_indicator]
    let j : S → L := fun ξ => ⟨ι ξ.1, ξ.2⟩
    have hj : Function.Injective j := fun a b hab => Subtype.ext (funext fun i =>
      mixedEmbedding_injective F (congrFun (congrArg Subtype.val hab) i))
    have := (hw.comp_injective hj).mul_left (max Bg 0 * C * (1 + R') ^ k)
    exact this
  · rw [pureA_add, norm_mul]
    by_cases hg0 : g (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i) + Prod.snd (y i)) = 0
    · rw [hg0, norm_zero, mul_zero]
      exact Set.indicator_nonneg (fun ξ _ => by positivity) ξ
    have hmem : ξ ∈ S := by
      show ∀ i, _
      intro i
      have hsupp : (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i) + yf i) ∈ tsupport g := by
        apply subset_tsupport
        simpa [hyf] using hg0
      have hKm : (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ K :=
        ⟨_, hsupp, by funext i; simp⟩
      obtain ⟨z, hz⟩ := (GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties F).2.2.2.1 ((N : F) * ξ i) fun v => by
        rw [map_mul, map_natCast]
        exact hK _ hKm i v
      refine ⟨z, ?_⟩
      have h2 := congrArg (mixedEmbedding F) hz
      rw [← nsmul_eq_mul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ] at h2
      exact h2.symm
    rw [Set.indicator_of_mem hmem]
    set x := ι ξ + fun i => evI F (y i) with hx
    have hxR : ‖ι ξ‖ ≤ ‖x‖ + R' := by
      have : ι ξ = x - fun i => evI F (y i) := by rw [hx]; abel
      rw [this]
      exact (norm_sub_le _ _).trans (add_le_add le_rfl (hyR.trans (le_max_left _ _)))
    have hR0 : 0 ≤ R' := le_max_right _ _
    have h1 : 1 + ‖ι ξ‖ ≤ (1 + R') * (1 + ‖x‖) := by nlinarith [norm_nonneg x]
    have hfx : ‖f x‖ * (1 + ‖ι ξ‖) ^ k ≤ C * (1 + R') ^ k := by
      calc ‖f x‖ * (1 + ‖ι ξ‖) ^ k ≤ ‖f x‖ * ((1 + R') * (1 + ‖x‖)) ^ k := by
            gcongr
        _ = (1 + R') ^ k * ((1 + ‖x‖) ^ k * ‖f x‖) := by rw [mul_pow]; ring
        _ ≤ (1 + R') ^ k * C := by gcongr; exact hC x
        _ = C * (1 + R') ^ k := by ring
    have hpos : 0 < (1 + ‖ι ξ‖) ^ k := by positivity
    have hf : ‖f x‖ ≤ C * (1 + R') ^ k * (1 + ‖ι ξ‖)⁻¹ ^ k := by
      rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ hpos]
      exact hfx
    calc ‖f x‖ * ‖g _‖ ≤ (C * (1 + R') ^ k * (1 + ‖ι ξ‖)⁻¹ ^ k) * max Bg 0 :=
          mul_le_mul hf (le_max_of_le_left (hB _)) (norm_nonneg _) (by positivity)
      _ = h ξ := by rw [hh]; ring

theorem majorant {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) (yf : κ → FiniteAdeleRing (𝓞 F) F) (R : ℝ) :
    ∃ c : (κ → F) → ℝ, Summable c ∧ ∀ (ξ : κ → F) (y : κ → AF F), (∀ i, Prod.snd (y i) = yf i) →
      ‖fun i => evI F (y i)‖ ≤ R → ‖Φ ((fun i => algebraMap F (AF F) (ξ i)) + y)‖ ≤ c ξ := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    exact majorant_pure f hg yf R
  | zero => exact ⟨0, summable_zero, fun ξ y _ _ => by simp⟩
  | add Φ Ψ _ _ h1 h2 =>
    obtain ⟨c1, hs1, hb1⟩ := h1
    obtain ⟨c2, hs2, hb2⟩ := h2
    exact ⟨c1 + c2, hs1.add hs2, fun ξ y hy hyR =>
      (norm_add_le _ _).trans (add_le_add (hb1 ξ y hy hyR) (hb2 ξ y hy hyR))⟩
  | smul a Φ _ h =>
    obtain ⟨c, hs, hb⟩ := h
    refine ⟨fun ξ => ‖a‖ * c ξ, hs.mul_left _, fun ξ y hy hyR => ?_⟩
    rw [Pi.smul_apply, smul_eq_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (hb ξ y hy hyR) (norm_nonneg _)

end GlobalTheory.HeisLineTheta

namespace GlobalTheory.HeisLineTheta

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM
open scoped Classical

variable {F : Type} [Field F] [NumberField F]

theorem evI_add_realAd_mul (t : ℝ) (x z : AF F) : evI F (x + realAd F t * z) = evI F x + t • evI F z := by
  unfold evI
  rw [show Prod.fst (x + realAd F t * z) = Prod.fst x + Prod.fst (realAd F t) * Prod.fst z from rfl, map_add, map_mul,
    show Prod.fst (realAd F t) = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ t) from rfl,
    RingEquiv.apply_symm_apply, Algebra.smul_def]

theorem snd_add_realAd_mul (t : ℝ) (x z : AF F) : Prod.snd (x + realAd F t * z) = Prod.snd x := by
  rw [show Prod.snd (x + realAd F t * z) = Prod.snd x + Prod.snd (realAd F t) * Prod.snd z from rfl,
    show Prod.snd (realAd F t) = 0 from rfl, zero_mul, add_zero]

end GlobalTheory.HeisLineTheta

open GlobalTheory.HeisLineTheta in

theorem GlobalTheory.HeisLineTheta.hasDerivAt_thetaSum_line : ∀ {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F}
    {κ : Type} [Fintype κ] (d : GlobalTheory.WeilM.Darboux B κ) (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ →
    ∀ u : W, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u →
    ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∀ Φ' ∈ GlobalTheory.WeilM.schA F κ,
      (∀ x, HasDerivAt (fun t : ℝ => d.rho ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd F t • u) Φ x) (Φ' x) 0) →
      ∀ u' : W, HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (d.rho ψ u' (d.rho ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd F t • u) Φ)))
        (GlobalTheory.WeilM.thetaSum F (d.rho ψ u' Φ')) 0 := by
  intro F _ _ W _ _ B κ _ d ψ hψ u hu Φ hΦ Φ' hΦ' hd u'
  classical
  set a' := (d.e u').1 with ha'
  set a := (d.e u).1 with ha
  set y : ℝ → κ → AF F := fun t i => a' i + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd F t * a i with hy
  have hyf : ∀ t i, Prod.snd (y t i) = Prod.snd (a' i) := fun t i => snd_add_realAd_mul t _ _
  set R := ‖fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (a' i)‖ + ‖fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (a i)‖ with hR
  have hyR : ∀ t : ℝ, |t| ≤ 1 → ‖fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (y t i)‖ ≤ R := by
    intro t ht
    have e : (fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (y t i)) =
        (fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (a' i)) + t • (fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (a i)) := by
      funext i
      simp only [hy, evI_add_realAd_mul, Pi.add_apply, Pi.smul_apply]
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) ht
  have hval : ∀ (Ψ : (κ → AF F) → ℂ) (ξ : κ → F) (t : ℝ),
      ‖d.rho ψ u' (d.rho ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd F t • u) Ψ) (fun i => algebraMap F (AF F) (ξ i))‖ =
        ‖Ψ ((fun i => algebraMap F (AF F) (ξ i)) + y t)‖ := by
    intro Ψ ξ t
    rw [norm_rho hψ, norm_rho hψ, e_smul]
    congr 2
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hy, add_assoc]
    rfl
  obtain ⟨c, hc, hcb⟩ := majorant hΦ' (fun i => Prod.snd (a' i)) R
  obtain ⟨c0, hc0, hcb0⟩ := majorant hΦ (fun i => Prod.snd (a' i)) R
  have hmem : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  set G : (κ → F) → ℝ → ℂ := fun ξ s =>
    d.rho ψ u' (d.rho ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd F s • u) Φ) (fun i => algebraMap F (AF F) (ξ i)) with hG
  set G' : (κ → F) → ℝ → ℂ := fun ξ s =>
    d.rho ψ u' (d.rho ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd F s • u) Φ') (fun i => algebraMap F (AF F) (ξ i)) with hG'
  have hv : GlobalTheory.WeilM.thetaSum F (d.rho ψ u' Φ') = ∑' ξ : κ → F, G' ξ 0 := by
    simp only [hG', rho_zero]
    rfl
  rw [hv]
  show HasDerivAt (fun t : ℝ => ∑' ξ : κ → F, G ξ t) (∑' ξ : κ → F, G' ξ 0) 0
  refine hasDerivAt_tsum_of_isPreconnected (g := G) (g' := G') hc isOpen_Ioo isPreconnected_Ioo
    (fun ξ t _ => ?_) (fun ξ t ht => ?_) hmem ?_ hmem
  · exact (hasDerivAt_line d ψ u hd _ t).const_mul _
  · rw [hG', hval]
    exact hcb ξ (y t) (hyf t) (hyR t (abs_le.2 ⟨ht.1.le, ht.2.le⟩))
  · refine Summable.of_norm_bounded hc0 fun ξ => ?_
    rw [hG, hval]
    exact hcb0 ξ (y 0) (hyf 0) (hyR 0 (by simp))
