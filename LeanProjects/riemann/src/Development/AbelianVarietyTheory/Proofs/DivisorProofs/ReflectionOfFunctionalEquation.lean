import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimitiveHeckeLFunctionInvOfTrivialOnMaxRealStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.IsValCharTwist
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMulPowIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateLocalEpsilonFactorMulTameCharStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalEpsilonFactorTameFiniteOrderTwistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinprodNuValuesTwistOnlyRamifiedEqOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistAndNuRamifiedPlaceDegreeOneExponentTwoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistOnlyRamifiedPlacePrimeResidueDvdNormStatement

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.HeckeEps

namespace GlobalTheory.ReflVal

variable {E : Type} [Field E] [NumberField E]

theorem reflect_of_finEps (hFE : GlobalTheory.Published.HeckeTateFunctionalEquation) [IsCMField E] {I : Type} [Fintype I]
    {φ : I → E →+* ℂ} (hφ : IsCMType φ) {m : I → ℤ} (hm0 : ∃ i, m i ≠ 0) {χ χ₀ : HChar E} (hu : IsUnitary χ)
    (hu₀ : IsUnitary χ₀) (hi : HasInf χ φ m) (hi₀ : HasInf χ₀ φ m) (ht : TrivOnF χ) (ht₀ : TrivOnF χ₀)
    {a a₀ : HeightOneSpectrum (𝓞 E) →₀ ℕ} (ha : ∀ w, ExpAt χ w (a w)) (ha₀ : ∀ w, ExpAt χ₀ w (a₀ w)) {Λ Λ₀ : ℂ → ℂ}
    (hΛ : IsHeckeL χ Λ) (hΛ₀ : IsHeckeL χ₀ Λ₀) {s e : ℂ} (hs : ∀ (i : I) (k : ℕ), s + ((|m i| : ℤ) : ℂ) ≠ -k)
    (hs' : ∀ (i : I) (k : ℕ), 1 - s + ((|m i| : ℤ) : ℂ) ≠ -k) (he : finEps χ a s = e * finEps χ₀ a₀ s) :
    Λ s * Λ₀ (1 - s) = e * (Λ (1 - s) * Λ₀ s) := by
  have hcm := hFE.cm
  have h1 := hcm E I φ m χ a Λ Λ hφ hu hi hm0 ha hΛ (GlobalTheory.T.isPrimitiveHeckeLFunction_inv_of_trivialOnMaxReal E χ Λ ht hΛ) s hs hs'
  have h0 := hcm E I φ m χ₀ a₀ Λ₀ Λ₀ hφ hu₀ hi₀ hm0 ha₀ hΛ₀ (GlobalTheory.T.isPrimitiveHeckeLFunction_inv_of_trivialOnMaxReal E χ₀ Λ₀ ht₀ hΛ₀) s hs hs'
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)
  have hL : LInf m s ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun i _ => mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Complex.Gamma_ne_zero (hs i))
    rw [Ne, Complex.cpow_eq_zero_iff]; tauto
  rw [he] at h1
  refine mul_left_cancel₀ hL ?_
  linear_combination Λ₀ (1 - s) * h1 - e * Λ (1 - s) * h0

end GlobalTheory.ReflVal

namespace GlobalTheory.ReflVal

variable {E : Type} [Field E] [NumberField E]

theorem finEps_eq_of_local {K : Type} [Field K] (σ : K →+* ℂ) (P : K → Prop) (h1 : P 1)
    (hmul : ∀ x y, P x → P y → P (x * y)) (χ χ₀ : HChar E) (a a₀ : HeightOneSpectrum (𝓞 E) →₀ ℕ) (s : ℂ)
    (c : HeightOneSpectrum (𝓞 E) → ℂ) (hcf : (Function.mulSupport c).Finite) (hc : ∏ᶠ w, c w = 1)
    (h : ∀ w, ∃ g, P g ∧ locEps χ w (a w) s = σ g * c w * locEps χ₀ w (a₀ w) s) :
    ∃ g, P g ∧ finEps χ a s = σ g * finEps χ₀ a₀ s := by
  classical
  choose g hg he using h
  set S := (finite_mulSupport_locEps χ a s).toFinset ∪ (finite_mulSupport_locEps χ₀ a₀ s).toFinset ∪ hcf.toFinset
  have hS1 : Function.mulSupport (fun w => locEps χ w (a w) s) ⊆ S := fun w hw => by simp [S, hw]
  have hS2 : Function.mulSupport (fun w => locEps χ₀ w (a₀ w) s) ⊆ S := fun w hw => by simp [S, hw]
  have hS3 : Function.mulSupport c ⊆ S := fun w hw => by simp [S, hw]
  have hP : ∀ T : Finset (HeightOneSpectrum (𝓞 E)), P (∏ w ∈ T, g w) := fun T => by
    induction T using Finset.induction_on with
    | empty => simpa using h1
    | insert x T hx ih => rw [Finset.prod_insert hx]; exact hmul _ _ (hg x) ih
  refine ⟨∏ w ∈ S, g w, hP S, ?_⟩
  rw [finEps, finEps, finprod_eq_prod_of_mulSupport_subset _ hS1, finprod_eq_prod_of_mulSupport_subset _ hS2,
    finprod_eq_prod_of_mulSupport_subset _ hS3] at *
  rw [Finset.prod_congr rfl fun w _ => he w, Finset.prod_mul_distrib, Finset.prod_mul_distrib, hc, mul_one, map_prod]

theorem exists_finsupp_expAt (χ : HChar E) : ∃ a : HeightOneSpectrum (𝓞 E) →₀ ℕ, ∀ w, ExpAt χ w (a w) := by
  classical
  have h := GlobalTheory.Mem.UnrAe.exists_levelLe χ
  have hE : ∀ w, ExpAt χ w (Nat.find (h w)) := fun w m =>
    ⟨fun hm => Nat.find_min' (h w) hm, fun hm x hx hx' => Nat.find_spec (h w) x hx (hx'.trans (by
      rw [WithZero.exp_le_exp]; omega))⟩
  have hsub : Function.support (fun w => Nat.find (h w)) ⊆ {v | ¬ χ.UnrAt v} := fun w hw hu =>
    hw ((hE w).unique ((expAt_zero_iff χ w).2 hu))
  exact ⟨Finsupp.ofSupportFinite _ ((GlobalTheory.Mem.UnrAe.finite_ramified χ).subset hsub), fun w => hE w⟩

theorem expAt_mul_of_unrAt {χ ξ : HChar E} {w : HeightOneSpectrum (𝓞 E)} (h : ξ.UnrAt w) {n : ℕ} (hn : ExpAt χ w n) :
    ExpAt (χ * ξ) w n := fun m => by
  rw [← hn m]
  constructor
  · intro h' x hx hx'
    have := h' x hx hx'
    rwa [Formalism.L2.Host.HChar.loc_mul, h x hx, mul_one] at this
  · intro h' x hx hx'
    rw [Formalism.L2.Host.HChar.loc_mul, h' x hx hx', h x hx, one_mul]

theorem expAt_one_of_tame {ξ : HChar E} {w : HeightOneSpectrum (𝓞 E)} (ht : ξ.TameAt w) (hr : ¬ ξ.UnrAt w) :
    ExpAt ξ w 1 := fun m => by
  constructor
  · intro h
    by_contra c
    obtain rfl : m = 0 := by omega
    exact hr ((ξ.unrAt_iff w).2 h)
  · intro hm x hx hx'
    exact ht x hx (hx'.trans (by rw [WithZero.exp_le_exp]; omega))

end GlobalTheory.ReflVal

namespace GlobalTheory.ReflVal

open Formalism.L2.Host (unif atFin)

theorem locEps_mul_of_unrAt : ∀ (E : Type) [Field E] [NumberField E] (χ ξ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (a : ℕ)
    (s : ℂ), ξ.UnrAt w → locEps (χ * ξ) w a s = ((ξ.locK w (unif w ^ (a + diffExp w)) : ℂˣ) : ℂ) * locEps χ w a s := by
  intro E _ _ χ ξ w a s hU
  have hloc : ∀ x : Eˣ, (χ * ξ).locK w x = χ.locK w x * ξ.locK w x := fun x => rfl
  have hG : a ≠ 0 → gaussSumAt (χ * ξ) w a (unif w ^ (a + diffExp w)) = gaussSumAt χ w a (unif w ^ (a + diffExp w)) := by
    intro ha
    unfold gaussSumAt
    congr 1
    funext y
    have hy := out_notMem w ha y
    set z : 𝓞 E := Quotient.out (y : 𝓞 E ⧸ w.asIdeal ^ a)
    have hz1 : w.valuation E (z : E) = 1 := (w.valuation_eq_one_iff_notMem (K := E)).2 hy
    have hz0 : (z : E) ≠ 0 := fun h => by rw [h, map_zero] at hz1; exact zero_ne_one hz1
    unfold gaussTerm
    rw [dif_neg hz0, dif_neg hz0, hloc]
    have h1 : ξ.locK w (Units.mk0 _ hz0) = 1 := hU _ (by
      show Valued.v (((z : E) : w.adicCompletion E)) = 1
      rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hz1])
    rw [h1, mul_one]
  unfold locEps
  split_ifs with ha
  · rw [hloc, Units.val_mul]; ring
  · rw [hloc, Units.val_mul, hG ha]; ring

end GlobalTheory.ReflVal

namespace GlobalTheory.ReflVal

open Formalism.L2.Host (unif atFin)

variable {E : Type} [Field E] [NumberField E]

theorem locK_pow_eq_one {ξ : HChar E} {N : ℕ} (hf : ξ.OrderDvd N) (w : HeightOneSpectrum (𝓞 E)) (y : Eˣ) :
    ((ξ.locK w y : ℂˣ) : ℂ) ^ N = 1 := by
  have h : (ξ ^ N).locK w y = 1 := by rw [show ξ ^ N = 1 from hf]; rfl
  have h2 : (ξ ^ N).locK w y = ξ.locK w y ^ N := by
    show (ξ.1 ^ N) _ = _
    rw [MonoidHom.pow_apply]; rfl
  rw [← Units.val_pow_eq_pow_val, ← h2, h, Units.val_one]

theorem isAwayUnit_of_locK {K : Type} [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) {ξ : HChar E} {N : ℕ}
    (hN : 0 < N) (hf : ξ.OrderDvd N) (w : HeightOneSpectrum (𝓞 E)) (y : Eˣ) {g : K} (hg : σ g = ((ξ.locK w y : ℂˣ) : ℂ))
    {m : ℕ} (hm : 0 < m) : GlobalTheory.Square.IsAwayUnit m g := by
  refine (GlobalTheory.Square.isAwayUnit_closure K m hm).1 g N hN (σ.injective ?_)
  rw [map_pow, hg, locK_pow_eq_one hf, map_one]

end GlobalTheory.ReflVal

namespace GlobalTheory.SqTop

open Formalism.BasicNotions Formalism.IndefR.Links GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.ReflVal
open Formalism.L2.Host (unif atFin)

theorem refl_square (hFE : GlobalTheory.Published.HeckeTateFunctionalEquation) {D : D7} {T : Type} {Lc : LevCh D T}
    {sc : GlobalTheory.ChiGrid.Consts} [IsCMField D.host.E] (hφ : IsCMType (cmPhi D)) {μ₀ : T} (hL : Lc.Is μ₀)
    (G : GridData Lc sc) (hb : IsBaseCond (condF G.pl)) (hc : CharsIn G D.what₂.embLL)
    (hr : ∀ t, ∀ w ∈ locPl G t, RootsIn D.what₂.embLL (Ideal.absNorm w.asIdeal ^ depthAt G w))
    (i j : Fin D.R.m) (t : T) {Λ Λ₀ : ℂ → ℂ} (hΛ : IsHeckeL (nuH G t i j) Λ) (hΛ₀ : IsHeckeL (nuH G μ₀ i j) Λ₀)
    (s : ℤ) (hs1 : 1 - (e0 D i j : ℤ) ≤ s) (hs0 : s ≤ 0) :
    ∃ Ep : D.what₂.LL, GlobalTheory.Square.IsAwayUnit (Qn G t) Ep ∧
      Λ s * Λ₀ ((1 - s : ℤ) : ℂ) = D.what₂.embLL Ep * (Λ ((1 - s : ℤ) : ℂ) * Λ₀ s) := by
  classical
  set ξ := Lc.xiH t with hξ
  set ν₀ := nuH G μ₀ i j with hν₀
  have e : nuH G t i j = ν₀ * ξ := by
    simp only [ν₀, ξ, nuH, hL.xi_base, mul_one]
    exact mul_div_right_comm _ _ _
  have hv := GlobalTheory.FunObj.SqNum.Model.isValChar_nu hL G i j (Nat.zero_le (halfRank D i j))
  obtain ⟨N, hN, hf⟩ := hL.xi_fin t
  have hu : IsUnitary (nuH G t i j) := GlobalTheory.ChrEqUnique.isUnitary_of_chrEq D _ _ (chrEq_nu G t i j hL)
  have hm : HasInf (nuH G t i j) (cmPhi D) (fun τ => ((kap D sc.cGap i j 0 τ : ℕ) : ℤ) + ((0 : ℕ) : ℤ)) := by
    intro k
    rw [e, Formalism.L2.Host.HChar.inf_mul, GlobalTheory.TypeValues.inf_eq_one ξ hN hf k, mul_one]
    exact hv.1.2.2.1 k
  have ht : TrivOnF (nuH G t i j) := by rw [e]; exact hv.1.2.1.mul (hL.xi_triv t)
  obtain ⟨a, ha⟩ := exists_finsupp_expAt (nuH G t i j)
  obtain ⟨a₀, ha₀⟩ := exists_finsupp_expAt ν₀
  have hbig : ∀ τ, (e0 D i j : ℤ) < ((kap D sc.cGap i j 0 τ : ℕ) : ℤ) := fun τ => by
    have a0 := (GlobalTheory.FunObj.SqNum.Model.kap_add D sc.cGap i j τ (Nat.zero_le (halfRank D i j))).1
    have a1 := GlobalTheory.FunObj.SqNum.Model.kap_add D sc.cGap i j τ (le_refl (halfRank D i j))
    have a2 : e0 D i j ≤ halfRank D i j := by unfold e0 halfRank botBig botSmall; omega
    omega
  obtain ⟨τ₀⟩ : Nonempty D.what₂.Tau := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace D.host.E) := inferInstance
    obtain ⟨τ, -⟩ := hφ w.embedding
    exact ⟨τ⟩
  have hm0 : ∃ τ, ((kap D sc.cGap i j 0 τ : ℕ) : ℤ) + ((0 : ℕ) : ℤ) ≠ 0 := ⟨τ₀, by have := hbig τ₀; omega⟩
  have hs : ∀ τ (k : ℕ), (s : ℂ) + ((|((kap D sc.cGap i j 0 τ : ℕ) : ℤ) + ((0 : ℕ) : ℤ)| : ℤ) : ℂ) ≠ -k := by
    intro τ k h
    have h2 : ((s + |((kap D sc.cGap i j 0 τ : ℕ) : ℤ) + ((0 : ℕ) : ℤ)| + k : ℤ) : ℂ) = 0 := by
      push_cast; linear_combination h
    have h3 := Int.cast_eq_zero.1 h2
    have := hbig τ
    rw [abs_of_nonneg (by omega)] at h3
    omega
  have hs' : ∀ τ (k : ℕ), 1 - (s : ℂ) + ((|((kap D sc.cGap i j 0 τ : ℕ) : ℤ) + ((0 : ℕ) : ℤ)| : ℤ) : ℂ) ≠ -k := by
    intro τ k h
    have h2 : ((1 - s + |((kap D sc.cGap i j 0 τ : ℕ) : ℤ) + ((0 : ℕ) : ℤ)| + k : ℤ) : ℂ) = 0 := by
      push_cast; linear_combination h
    have h3 := Int.cast_eq_zero.1 h2
    have := hbig τ
    rw [abs_of_nonneg (by omega)] at h3
    omega
  have hQn : 0 < Qn G t := Finset.prod_pos fun w _ =>
    Nat.pos_of_ne_zero fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  let c : HeightOneSpectrum (𝓞 D.host.E) → ℂ := fun w => ∏ᶠ (_ : ¬ ξ.UnrAt w ∧ ν₀.UnrAt w), ((ν₀.val w : ℂˣ) : ℂ)
  have hc1 : ∀ w, ξ.UnrAt w → c w = 1 := fun w h => by
    simp only [c]; rw [finprod_eq_if, if_neg (fun h' => h'.1 h)]
  have hcf : (Function.mulSupport c).Finite :=
    (GlobalTheory.Mem.UnrAe.finite_ramified ξ).subset fun w hw h => hw (hc1 w h)
  have hcprod : ∏ᶠ w, c w = 1 := GlobalTheory.T.finprod_nu_values_twist_only_ramified_eq_one G hL i j t
  have hloc : ∀ w, ∃ g, GlobalTheory.Square.IsAwayUnit (Qn G t) g ∧
      locEps (nuH G t i j) w (a w) (s : ℂ) = D.what₂.embLL g * c w * locEps ν₀ w (a₀ w) (s : ℂ) := by
    intro w
    have hxi : ∀ y : D.host.Eˣ, ((ξ.locK w y : ℂˣ) : ℂ) ∈ Set.range D.what₂.embLL := fun y => hc.xi t w (atFin w y)
    by_cases hU : ξ.UnrAt w
    · have hE := expAt_mul_of_unrAt hU (ha₀ w)
      rw [← e] at hE
      rw [(ha w).unique hE, e, locEps_mul_of_unrAt _ ν₀ ξ w _ _ hU, hc1 w hU]
      obtain ⟨g, hg⟩ := hxi (unif w ^ (a₀ w + diffExp w))
      exact ⟨g, isAwayUnit_of_locK D.what₂.embLL hN hf w _ hg hQn, by rw [hg, mul_one]⟩
    by_cases hU0 : ν₀.UnrAt w
    · obtain ⟨q, hq, hcard, hqQ, w', hw', hw'N⟩ := GlobalTheory.T.twist_only_ramified_place_prime_residue_dvd_norm G hL i j t w hU hU0
      have h1 := expAt_one_of_tame (hL.xi_tame t w) hU
      have hroot : ∀ z : ℂ, z ^ q = 1 → z ∈ Set.range D.what₂.embLL := fun z hz => by
        refine hr t w' hw' z ?_
        have hd : 1 ≤ depthAt G w' := le_max_right _ _
        rw [hw'N, ← Nat.sub_add_cancel hd, pow_succ, pow_mul', hz, one_pow]
      obtain ⟨hE, g, hg, hge⟩ := GlobalTheory.T.localEpsilonFactor_tame_finiteOrder_twist _ _ D.what₂.embLL ν₀ ξ w q (Qn G t) N s hq hcard hqQ hN hf hU0 h1 hxi hroot hs0
      rw [← e] at hE
      have h0 : ExpAt ν₀ w 0 := (expAt_zero_iff ν₀ w).2 hU0
      rw [(ha w).unique hE, (ha₀ w).unique h0, e, hge]
      have hcw : c w = ((ν₀.val w : ℂˣ) : ℂ) := by
        simp only [c]; rw [finprod_eq_if, if_pos ⟨hU, hU0⟩]
      exact ⟨g, hg, by rw [hcw]⟩
    · obtain ⟨q, hq, hcard, hsq, h2⟩ := GlobalTheory.T.twist_and_nu_ramified_place_degree_one_exponent_two G hL hb i j t w hU hU0
      obtain ⟨hE, y, hy⟩ := GlobalTheory.T.tateLocalEpsilonFactor_mul_tameChar _ ν₀ ξ w q (s : ℂ) hq hcard hsq h2 (hL.xi_tame t w)
      rw [← e] at hE
      rw [(ha w).unique hE, (ha₀ w).unique h2, e, hy]
      have hcw : c w = 1 := by simp only [c]; rw [finprod_eq_if, if_neg (fun h' => hU0 h'.2)]
      obtain ⟨g, hg⟩ := hxi y
      exact ⟨g, isAwayUnit_of_locK D.what₂.embLL hN hf w y hg hQn, by rw [hcw, hg, mul_one]⟩
  obtain ⟨g, hg, hge⟩ := finEps_eq_of_local D.what₂.embLL (GlobalTheory.Square.IsAwayUnit (Qn G t))
    (GlobalTheory.Square.IsAwayUnit.one _) (fun x y hx hy => hx.mul hy) (nuH G t i j) ν₀ a a₀ (s : ℂ) c hcf hcprod hloc
  refine ⟨g, hg, ?_⟩
  have := reflect_of_finEps hFE hφ hm0 hu hv.1.1 hm hv.1.2.2.1 ht hv.1.2.1 ha ha₀ hΛ hΛ₀ hs hs' hge
  push_cast
  exact this

theorem refl_of_functionalEquation : GlobalTheory.Published.HeckeTateFunctionalEquation → FieldDat → LNe → Refl := by
  intro hFE hFD _
  obtain ⟨CF0, h⟩ := hFD
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x₀, h'⟩ := h ε CF hCF
  refine ⟨C0, x₀, fun C hC D large₂ he hx hR T Lc μ₀ hL G => ?_⟩
  obtain ⟨hCM, -, hFd, hb, -⟩ := h' C hC D large₂ he hx hR T Lc μ₀ hL G
  obtain ⟨-, -, -, -, -, -, hφ, -⟩ := hFd
  intro W S hN i j t Λ Λ₀ hΛ hΛ₀ s hs1 hs0
  exact refl_square hFE hφ hL G hb hN.chars hN.roots i j t hΛ hΛ₀ s hs1 hs0

end GlobalTheory.SqTop

end
