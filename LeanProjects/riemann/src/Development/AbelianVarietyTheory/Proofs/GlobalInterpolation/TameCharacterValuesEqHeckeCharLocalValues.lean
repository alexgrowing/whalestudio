import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfCongSet
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinAfMemIntUIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalIdeleSndSelf
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CharacterValueAtT
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemDivsOfMem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemZmuOfPowPred
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLocalIdele

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker
open Formalism.L2.Host (HChar atFin IsUnitAt IsUnifAt)
open GlobalTheory.Mem.Col2 GlobalTheory.Mem.ReadEx GlobalTheory.Mem.LocTriv Neutral.B1

namespace GlobalTheory.TwistVal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {K : Type} [Field K] {σ : K →+* ℂ} {μ : Chr F E K} {ξ : HChar E}

theorem evP_toRInt (P : HeightOneSpectrum (𝓞 E)) (b : 𝓞 E) :
    evP F P (toRInt F E b : AfE F E) = algebraMap E (P.adicCompletion E) (b : E) := by
  change afIso F E ((b : E) ⊗ₜ[F] 1) P = _
  rw [afIso_tmul_one]
  rfl

theorem valued_lt_of_mem {P : HeightOneSpectrum (𝓞 E)} {w : RInt F E} (h : w ∈ P.asIdeal.map (toRInt F E)) :
    Valued.v (evP F P (w : AfE F E)) < 1 := by
  induction h using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    rw [evP_toRInt, Formalism.UG.P.levelaf_valued_algebraMap]
    exact (HeightOneSpectrum.valuation_lt_one_iff_mem _ _).2 hb
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Subring.coe_add, map_add]
    exact Valuation.map_add_lt _ hx hy
  | smul a x _ hx =>
    rw [smul_eq_mul, Subring.coe_mul, map_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' ((mem_rInt_iff F E _).1 a.2 P)) hx

theorem val_le_two {P : HeightOneSpectrum (𝓞 E)} {z : RInt F E} (hz : z ∈ (P.asIdeal ^ 2).map (toRInt F E)) :
    Valued.v (evP F P (z : AfE F E)) ≤ WithZero.exp (-((2 : ℕ) : ℤ)) :=
  GlobalTheory.UnifConj.val_le_of_mem (afIso F E) (afIso_tmul_one F E) (mem_rInt_iff F E) P 2 z hz

theorem exp_neg_two_lt {P : HeightOneSpectrum (𝓞 E)} {b : 𝓞 E} (hb2 : b ∉ P.asIdeal ^ 2) :
    WithZero.exp (-((2 : ℕ) : ℤ)) < Valued.v (algebraMap E (P.adicCompletion E) (b : E)) := by
  rw [GlobalTheory.SuppIdele.val_algebraMap, ← not_le, P.intValuation_le_pow_iff_mem]
  exact hb2

theorem value_of_congr2 (h : Reads σ μ ξ) (ht : ∀ P, ξ.TameAt P) {P : HeightOneSpectrum (𝓞 E)} {u : (AfE F E)ˣ}
    {y : RInt F E} (hy : (y : AfE F E) = u) {b : 𝓞 E} (hb2 : b ∉ P.asIdeal ^ 2) {x : Eˣ} (hx : (x : E) = b)
    (h1 : y - toRInt F E b ∈ (P.asIdeal ^ 2).map (toRInt F E))
    (h2 : ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → y - 1 ∈ Q.asIdeal.map (toRInt F E)) :
    σ ((μ u : Kˣ) : K) = ((ξ.locK P x : ℂˣ) : ℂ) := by
  have hb := exp_neg_two_lt hb2
  have a1 : Valued.v (evP F P (u : AfE F E) - algebraMap E (P.adicCompletion E) (b : E)) ≤
      WithZero.exp (-((2 : ℕ) : ℤ)) := by
    have := val_le_two h1
    rwa [AddSubgroupClass.coe_sub, map_sub, evP_toRInt, hy] at this
  have a2 : ∀ Q, Q ≠ P → Valued.v (evP F Q (u : AfE F E) - 1) < 1 := fun Q hQ => by
    have := valued_lt_of_mem (h2 Q hQ)
    rwa [AddSubgroupClass.coe_sub, map_sub, Subring.coe_one, map_one, hy] at this
  set l := finAf F E (localIdele E P (atFin P x)) with hl
  have key : ∀ Q, Valued.v (evP F Q ((u / l : (AfE F E)ˣ) : AfE F E) - 1) < 1 := fun Q => by
    have e1 : evP F Q ((u / l : (AfE F E)ˣ) : AfE F E) * evP F Q (l : AfE F E) = evP F Q (u : AfE F E) := by
      rw [← map_mul, ← Units.val_mul, div_mul_cancel]
    have e2 : evP F Q (l : AfE F E) = ev Q (localIdele E P (atFin P x) : AdeleRing (𝓞 E) E) :=
      GlobalTheory.Mem.ReadTwist.afIso_finAf_apply _ Q
    by_cases hQ : Q = P
    · subst hQ
      rw [ev_local_self] at e2
      have e3 : ((atFin Q x : (Q.adicCompletion E)ˣ) : Q.adicCompletion E) = algebraMap E _ (b : E) := by
        rw [← hx]; rfl
      rw [e2, e3] at e1
      rw [← e1, ← sub_one_mul, map_mul] at a1
      by_contra hn
      push_neg at hn
      exact absurd (lt_of_lt_of_le hb (le_mul_of_one_le_left' hn)) (not_lt.2 a1)
    · rw [ev_local_ne hQ] at e2
      rw [e2, mul_one] at e1
      rw [e1]
      exact a2 Q hQ
  have hu : u / l ∈ intU F E := by
    refine (mem_intU_iff (u / l)).2 fun Q => ?_
    change Valued.v (evP F Q ((u / l : (AfE F E)ˣ) : AfE F E)) = 1
    have := key Q
    rw [← map_one (Valued.v : Valuation (Q.adicCompletion E) _)] at this ⊢
    exact Valuation.map_eq_of_sub_lt _ (by simpa using this)
  have hk : u / l ∈ μ.ker := by
    refine ker_of_reads h (map_toIdl_eq_one ht hu fun Q _ => le_exp_neg_one ?_)
    rw [map_sub, map_one]
    exact key Q
  rw [MonoidHom.mem_ker, map_div, div_eq_one] at hk
  rw [hk]
  exact (h _).symm

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (K : Type) [Field K] (σ : K →+* ℂ) (μ : Chr F E K) (ξ : Formalism.L2.Host.HChar E), GlobalTheory.Mem.Col2.Reads σ μ ξ → (∀ P, ξ.TameAt P) → ∀ P : HeightOneSpectrum (𝓞 E), (ξ.UnrAt P → σ ((unifVal μ P : Kˣ) : K) = ((ξ.val P : ℂˣ) : ℂ)) ∧ (((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 → ∀ q : Eˣ, (q : E) = ((Ideal.absNorm P.asIdeal : ℕ) : E) → σ ((qVal μ P : Kˣ) : K) = ((ξ.locK P q : ℂˣ) : ℂ)) := by
  intro F E _ _ _ _ _ K _ σ μ ξ h ht P
  have hne : ∀ {b : 𝓞 E}, b ∉ P.asIdeal ^ 2 → (b : E) ≠ 0 := fun {b} hb e =>
    hb ((RingOfIntegers.coe_eq_zero_iff.1 e) ▸ zero_mem _)
  constructor
  · intro hunr
    have hv : ∀ {c : 𝓞 E}, c ∈ P.asIdeal → (hc2 : c ∉ P.asIdeal ^ 2) →
        ((ξ.locK P (Units.mk0 _ (hne hc2)) : ℂˣ) : ℂ) = ((ξ.val P : ℂˣ) : ℂ) := fun {c} hc hc2 => by
      refine congrArg _ (ξ.val_eq hunr _ ?_)
      show Valued.v (algebraMap E (P.adicCompletion E) (c : E)) = _
      exact GlobalTheory.UnifConj.val_of_cong P _ c hc hc2 (by rw [sub_self, map_zero]; exact zero_le')
    obtain ⟨b, hb, hb2⟩ : ∃ b ∈ P.asIdeal, b ∉ P.asIdeal ^ 2 := by
      have := Ideal.exists_mem_pow_notMem_pow_succ P.asIdeal P.ne_bot P.isPrime.ne_top 1
      simpa using this
    obtain ⟨y, y₀, a1, a2, a3, a4⟩ := GlobalTheory.SuppIdele.exists_supported_idele F E P (P.under (𝓞 F)) b rfl
    have hy : σ ((μ y : Kˣ) : K) = ((ξ.val P : ℂˣ) : ℂ) :=
      (value_of_congr2 h ht a1 hb2 (x := Units.mk0 _ (hne hb2)) rfl a3 a4).trans (hv hb hb2)
    have hex : ∃ k, IsUnifVal μ P k := by
      refine ⟨μ y, fun w _ z z₀ c f1 hc hc2 _ f3 f4 => Units.ext (σ.injective ?_)⟩
      rw [hy, ← hv hc hc2]
      exact value_of_congr2 h ht f1 hc2 rfl f3 f4
    unfold unifVal
    rw [dif_pos hex, ← (hex.choose_spec (P.under (𝓞 F)) rfl y y₀ b a1 hb hb2 a2 a3 a4)]
    exact hy
  · intro hq q hqe
    set b : 𝓞 E := ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) with hbdef
    have hqb : (q : E) = (b : E) := by rw [hqe, hbdef]; simp
    obtain ⟨y, y₀, a1, a2, a3, a4⟩ := GlobalTheory.SuppIdele.exists_supported_idele F E P (P.under (𝓞 F)) b rfl
    have hy : σ ((μ y : Kˣ) : K) = ((ξ.locK P q : ℂˣ) : ℂ) := value_of_congr2 h ht a1 hq hqb a3 a4
    have hex : ∃ k, IsQValC μ P k := by
      refine ⟨μ y, fun w _ z z₀ f1 _ f3 f4 => Units.ext (σ.injective ?_)⟩
      rw [hy]
      exact value_of_congr2 h ht f1 hq hqb f3 f4
    unfold qVal qValC
    rw [dif_pos hex, ← (hex.choose_spec (P.under (𝓞 F)) rfl y y₀ a1 a2 a3 a4)]
    exact hy

end GlobalTheory.TwistVal
