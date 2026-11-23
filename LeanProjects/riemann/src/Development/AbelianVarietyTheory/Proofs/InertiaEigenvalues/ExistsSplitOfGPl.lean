import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDoubleCosetOperatorsStandardFacts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMaxCompactOfTrivOutsideLocalIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankLeAleph0SmoothIrreducibleUnitaryAdelic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimPartsAtIffBadAndOff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSplitPlaceEqFixedTypePrimePlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOrIsConjPlaceOfOverSplitPlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain GlobalTheory.HeightCounting
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.FormInner

section Plain

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

open GlobalTheory.InertUmax

omit [IsCMField L] in

theorem exists_trunc (b : AFplus L) : ∃ c : AFplus L, (∀ w, c w ∈ w.adicCompletionIntegers (maximalRealSubfield L)) ∧
    ∀ w, b w ∈ w.adicCompletionIntegers (maximalRealSubfield L) → c w = b w := by
  have h : ∀ w : HeightOneSpectrum (𝓞 (maximalRealSubfield L)), ∃ z : w.adicCompletion (maximalRealSubfield L),
      z ∈ w.adicCompletionIntegers (maximalRealSubfield L) ∧ (b w ∈ w.adicCompletionIntegers (maximalRealSubfield L) → z = b w) := by
    intro w
    by_cases hw : b w ∈ w.adicCompletionIntegers (maximalRealSubfield L)
    · exact ⟨b w, hw, fun _ => rfl⟩
    · exact ⟨0, zero_mem _, fun h => absurd h hw⟩
  choose z h1 h2 using h
  exact ⟨⟨z, Filter.Eventually.of_forall h1⟩, h1, h2⟩

theorem exists_int_off (z : AL L) : ∃ S : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield L))), ∃ Y ∈ ALint L,
    ∀ w ∉ S, ReciprocityTheory.Aut.compAt L w z = ReciprocityTheory.Aut.compAt L w Y := by
  classical
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨∅, 0, zero_mem _, fun _ _ => rfl⟩
  | add x y hx hy =>
    obtain ⟨S, Y, hY, h⟩ := hx
    obtain ⟨S', Y', hY', h'⟩ := hy
    refine ⟨S ∪ S', Y + Y', add_mem hY hY', fun w hw => ?_⟩
    rw [Finset.mem_union, not_or] at hw
    rw [map_add, map_add, h w hw.1, h' w hw.2]
  | tmul x a =>
    obtain ⟨m, hm, o, ho⟩ := GlobalTheory.FinTypCount.exists_nat_smul_int x
    have hm' : (m : maximalRealSubfield L) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
    obtain ⟨b, hb⟩ : ∃ b : AFplus L, b = (m : maximalRealSubfield L)⁻¹ • a := ⟨_, rfl⟩
    have e : (x ⊗ₜ[maximalRealSubfield L] a : AL L) = (o : L) ⊗ₜ[maximalRealSubfield L] b := by
      rw [ho, hb, ← Nat.cast_smul_eq_nsmul (maximalRealSubfield L), TensorProduct.smul_tmul, smul_inv_smul₀ hm']
    have hfin : {w : HeightOneSpectrum (𝓞 (maximalRealSubfield L)) |
        b w ∉ w.adicCompletionIntegers (maximalRealSubfield L)}.Finite := Filter.eventually_cofinite.1 b.2
    obtain ⟨c, hc, hc'⟩ := exists_trunc b
    refine ⟨hfin.toFinset, (o : L) ⊗ₜ[maximalRealSubfield L] c, GlobalTheory.FinTypCount.tmul_mem_ALint o hc, fun w hw => ?_⟩
    rw [e, compAt_tmul, compAt_tmul, hc' w (by simpa using hw)]

theorem mem_ALint_of_comp (z : AL L) (h : ∀ w, ∃ Y ∈ ALint L, ReciprocityTheory.Aut.compAt L w Y = ReciprocityTheory.Aut.compAt L w z) : z ∈ ALint L := by
  classical
  obtain ⟨S, Y, hY, hS⟩ := exists_int_off z
  choose Z hZ e using h
  have key : z - (Y + ∑ v ∈ S, (Z v - Y) * ((1 : L) ⊗ₜ[maximalRealSubfield L] sgl L v 1)) = 0 := by
    apply eq_zero_of_compAt
    intro w
    rw [map_sub, map_add, map_sum]
    simp only [map_mul, compAt_tmul]
    by_cases hw : w ∈ S
    · rw [Finset.sum_eq_single w (fun v _ hv => by rw [sgl_ne L v 1 (Ne.symm hv), TensorProduct.tmul_zero, mul_zero])
        (fun h => absurd hw h), sgl_same, ← Algebra.TensorProduct.one_def, mul_one, map_sub, e]
      ring
    · rw [Finset.sum_eq_zero fun v hv => by
        rw [sgl_ne L v 1 (fun h : w = v => hw (h ▸ hv)), TensorProduct.tmul_zero, mul_zero], hS w hw]
      ring
  rw [sub_eq_zero.1 key]
  exact add_mem hY (Subring.sum_mem _ fun v _ => mul_mem (sub_mem (hZ v) hY) (one_tmul_sgl_mem L v 1 (one_mem _)))

theorem le_Umax_of_prod {J : Subgroup (GAf L n)} (hJ : NG.IsProdLevel J)
    (h : ∀ v, ∀ κ ∈ J, TrivOutside {v} κ → κ ∈ Umax L n) : J ≤ Umax L n := by
  intro κ hκ i j
  refine mem_ALint_of_comp _ fun w => ?_
  obtain ⟨κ', h1, h2, h3⟩ := hJ κ hκ w
  exact ⟨_, h w κ' h1 h2 i j, congrFun (congrFun h3 i) j⟩

theorem mem_Umax_of_para (s : SplitPlace L) {r : ℕ} {κ : GAf L n} (h1 : TrivOutside {s.v} κ) (h2 : NG.ParaRT s r (s.loc n κ)) :
    κ ∈ Umax L n := by
  have h := GlobalTheory.HeckeStdFacts.mem_GLint_iff.1 h2.1
  refine GlobalTheory.HeckeStdFacts.mem_Umax_of_loc s κ h1 h.1 fun i j => ?_
  rw [map_inv]
  exact h.2 i j

end Plain

theorem exists_split_of_gPl (D : D7) : ∀ v ∈ Formalism.L2.gPl D, ∃ (k : Fin 2) (u : D.nd.PlG k) (s : SplitPlace D.host.E),
    s.v = v ∧ s.w = D.naut.plGw k u := by
  rintro v ⟨w, hw, k, hk⟩
  obtain ⟨u, hu⟩ := GlobalTheory.DimPartsCompare.cover k w hk
  obtain ⟨s, hs⟩ := GlobalTheory.SplitPlaceOfFixed.exists_splitPlace_plGw D ⟨k, u⟩
  refine ⟨k, u, s, HeightOneSpectrum.ext ?_, hs⟩
  rw [← s.w_under, hs]
  refine Eq.trans ?_ hw
  rcases hu with rfl | rfl
  · rfl
  · ext a
    refine GlobalTheory.DimPartsCompare.isConjPl_cPl _ _ _ ?_
    rw [GlobalTheory.SplitPlaceOver.host_conj_eq']
    exact ((IsCMField.complexConj D.host.E).commutes (a : maximalRealSubfield D.host.E)).symm

theorem level_le_Umax {D : D7} {M : MtFam D} {tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E}
    {Q : D.what₂.places.Pl → Finset (PlE D.host)} (h : MtInput D M tup Q) (w : D.what₂.places.Pl) (j : Fin D.R.m) :
    (M (D.what₂.muTw w) (j.1 + 1) (by omega) (by omega)).J ≤ Umax D.host.E D.R.nV := by
  refine le_Umax_of_prod (h.prod w j) fun v κ hκ hv => ?_
  by_cases hg : v ∈ Formalism.L2.gPl D
  · obtain ⟨k, u, s, rfl, hs⟩ := exists_split_of_gPl D v hg
    obtain ⟨ψ₀, ξ, -, -, hl⟩ := h.uni w j k u s hs
    exact mem_Umax_of_para s hv ((hl.mem κ hv).1 hκ).1
  by_cases hq : v ∈ qPl D (tup (D.what₂.muTw w) j)
  · obtain ⟨s, ξ, rfl, -, hl⟩ := h.para w j v hq
    exact mem_Umax_of_para s hv ((hl.mem κ hv).1 hκ)
  · refine (h.hyp w j κ fun u hu => hv u ?_).1.1 hκ
    rintro rfl
    exact hu fun h' => h'.elim hg hq

end GlobalTheory.FormInner

end
