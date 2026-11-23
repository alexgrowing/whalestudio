import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisOfRegularForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankWeightComponentEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DivisorsAtInvDualLabelAndStabilizerMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DenseFrobeniusSplitPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LinearCoefficientData
import ReciprocityTheory.GaloisValuations.Global
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceOffLevelSetProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRepresentativesOfSupportStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorSupportTransferRankStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalCoefficientElementarySymmStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalFunctionDualLabelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryDivisorDualLabelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyScaledInverse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedConjugatePlaceUniformiserStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularWeightsOfGapTwo

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta
open Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.L2.DIV Polynomial GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem GlobalTheory.HeckeParts
open Formalism.IndefR.Bridge (SplitOff)
open scoped TensorProduct

namespace GlobalTheory.SphPar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Par

open Formalism.UG

theorem exists_enum {n : ℕ} {s : Multiset ℂ} (h : s.card = n) : ∃ α : Fin n → ℂ, Finset.univ.val.map α = s := by
  induction s using Quotient.inductionOn with
  | h l =>
    have hl : l.length = n := by simpa using h
    subst hl
    refine ⟨l.get, ?_⟩
    rw [Fin.univ_val_map, List.ofFn_get]
    rfl

theorem eq_of_esymm {n : ℕ} {s s' : Multiset ℂ} (h : s.card = n) (h' : s'.card = n) (he : ∀ k, k ≤ n → s.esymm k = s'.esymm k) :
    s = s' := by
  rw [← roots_multiset_prod_X_sub_C s, ← roots_multiset_prod_X_sub_C s', Multiset.prod_X_sub_X_eq_sum_esymm,
    Multiset.prod_X_sub_X_eq_sum_esymm, h, h']
  congr 1
  exact Finset.sum_congr rfl fun k hk => by rw [he k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))]

theorem kap_ne {q : ℕ} (hq : q ≠ 0) (n : ℕ) : (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero hq)) _).ne'

theorem frobPoly_inj {q n : ℕ} (hq : q ≠ 0) {s s' : Multiset ℂ} (h : frobPoly q n s = frobPoly q n s') : s = s' := by
  have e : ∀ u : Multiset ℂ, (frobPoly q n u).roots = u.map (· * (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ)) := fun u => by
    rw [← roots_multiset_prod_X_sub_C (u.map _), Multiset.map_map]
    rfl
  have := congrArg roots h
  rw [e, e] at this
  exact Multiset.map_injective (mul_left_injective₀ (kap_ne hq n)) this

variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {n : ℕ} {lab lab' : List ℤ → Prop}
  {c c' : List ℤ → ℂ} {s : Multiset ℂ}

theorem ParGL.eq (h : ParGL P n lab c s) (h' : ParGL P n lab c' s) {d : List ℤ} (hd : lab d) : c d = c' d := by
  obtain ⟨α, hα⟩ := exists_enum h.1
  obtain ⟨φ, h1, h2, -⟩ := Formalism.UG.Final.SphericalExists E P n α fun i e =>
    h.2.1 (hα ▸ Multiset.mem_map.2 ⟨i, Finset.mem_univ_val i, e⟩)
  have := (h.2.2 α hα φ h1 d hd).symm.trans (h'.2.2 α hα φ h1 d hd)
  rwa [h2, mul_one, mul_one] at this

theorem ParGL.dual (h : ParGL P n lab (fun d => c (dualLab d)) s) (hl : ∀ d, lab' d → d.length = n ∧ lab (dualLab d)) :
    ParGL P n lab' c (s.map (·⁻¹)) := by
  have h0 : (0 : ℂ) ∉ s.map (·⁻¹) := fun e => by
    obtain ⟨a, ha, e⟩ := Multiset.mem_map.1 e
    exact h.2.1 (inv_eq_zero.1 e ▸ ha)
  refine ⟨by rw [Multiset.card_map, h.1], h0, fun α hα φ hφ d hd => ?_⟩
  obtain ⟨φ', h1, h2, h3⟩ := GlobalTheory.T.spherical_function_dual_label E P n α φ
    (fun i e => h0 (hα ▸ Multiset.mem_map.2 ⟨i, Finset.mem_univ_val i, e⟩)) hφ
  have e : Finset.univ.val.map (fun i : Fin n => (α i.rev)⁻¹) = s := by
    have e1 : Finset.univ.val.map (fun i : Fin n => (α i.rev)⁻¹) = (Finset.univ.val.map α).map (·⁻¹) := by
      conv_rhs => rw [← Multiset.map_univ_val_equiv Fin.revPerm]
      simp only [Multiset.map_map, Function.comp_def, Fin.revPerm_apply]
    rw [e1, hα, Multiset.map_map]
    simp
  have := h.2.2 _ e φ' h1 _ (hl d hd).2
  beta_reduce at this
  rwa [h3 d (hl d hd).1, dualLab_dualLab, h2] at this

section U

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {ϖ : L} {σ : L →+* L} {q : ℕ}

theorem ParU.eq [CompleteSpace L] (hU : IsUnramInv ϖ σ q) (h : ParU σ q n lab c s) (h' : ParU σ q n lab c' s) {d : List ℤ}
    (hd : lab d) : c d = c' d := by
  obtain ⟨α, hα⟩ := h.2.1
  obtain ⟨φ, h1, h2, -⟩ := Formalism.UG.Final.SphericalExistsU L ϖ σ q n (n / 2) hU (by omega) (by omega) α fun i e =>
    h.1 (hα ▸ Multiset.mem_add.2 (Or.inl (Multiset.mem_add.2 (Or.inl (Multiset.mem_map.2 ⟨i, Finset.mem_univ_val i, e⟩)))))
  have := (h.2.2 α hα φ h1 d hd).symm.trans (h'.2.2 α hα φ h1 d hd)
  rwa [h2, mul_one, mul_one] at this

theorem ParU.dual (hU : IsUnramInv ϖ σ q) (h : ParU σ q n lab (fun d => c (dualLab d)) s)
    (hl : ∀ d, lab' d → d.length = n ∧ lab (dualLab d)) : ParU σ q n lab' c (s.map (·⁻¹)) := by
  obtain ⟨α₀, hα₀⟩ := h.2.1
  have hs : s.map (·⁻¹) = s := by rw [← hα₀, bcPar_map_inv]
  rw [hs]
  refine ⟨h.1, h.2.1, fun α hα φ hφ d hd => ?_⟩
  have := h.2.2 α hα φ hφ _ (hl d hd).2
  beta_reduce at this
  rw [dualLab_dualLab] at this
  rw [← this]
  congr 1
  funext g
  have hiff : HasDiv (intL L) d (g : GL (Fin n) L) ↔ HasDiv (intL L) (dualLab d) (g : GL (Fin n) L) :=
    ⟨GlobalTheory.T.unitary_divisor_dual_label L σ n d g hU.2.1 (hl d hd).1 g.2, fun h1 => by
      have := GlobalTheory.T.unitary_divisor_dual_label L σ n _ g hU.2.1 (by simpa [dualLab] using (hl d hd).1) g.2 h1
      rwa [dualLab_dualLab] at this⟩
  classical
  simp only [divInd, Set.indicator_apply, Set.mem_ofPred_eq, hiff, Pi.one_apply]

end U

variable [StarRing E]

theorem IsPar.dual (h : IsPar P n lab (fun d => c (dualLab d)) s) (hl : ∀ d, lab' d → d.length = n ∧ lab (dualLab d)) :
    IsPar P n lab' c (s.map (·⁻¹)) :=
  ⟨fun hP => (h.1 hP).dual hl, fun hP σ ϖ q h1 h2 => (h.2 hP σ ϖ q h1 h2).dual h2 hl⟩

end Par

theorem IsPar.eq {D : D7} {P : HeightOneSpectrum (𝓞 D.host.E)} {n : ℕ} {lab : List ℤ → Prop} {c c' : List ℤ → ℂ}
    {s : Multiset ℂ} (h : IsPar P n lab c s) (h' : IsPar P n lab c' s) {d : List ℤ} (hd : lab d) : c d = c' d := by
  by_cases hP : Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal = P.asIdeal
  · obtain ⟨σ, ϖ, q, h1, h2⟩ := GlobalTheory.T.unramified_conjugate_place_uniformiser P hP
    exact (h.2 hP σ ϖ q h1 h2).eq h2 (h'.2 hP σ ϖ q h1 h2) hd
  · exact (h.1 hP).eq (h'.1 hP) hd

section Galois

open Formalism.ConjugateSelfDual

variable {D : D7}

abbrev GE (D : D7) : Type := G D.host.E (AlgebraicClosure D.host.E)

theorem normV_ne (P : HeightOneSpectrum (𝓞 D.host.E)) : normV P ≠ 0 :=
  show Ideal.absNorm P.asIdeal ≠ 0 from fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)

theorem finite_over {l : ℕ} (hl : l ≠ 0) : {P : HeightOneSpectrum (𝓞 D.host.E) | ((l : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal}.Finite := by
  have h0 : ((l : ℕ) : 𝓞 D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hl
  refine (Ideal.finite_factors (I := Ideal.span {((l : ℕ) : 𝓞 D.host.E)})
    (by simpa [Ideal.span_singleton_eq_bot] using h0)).subset fun v hv => ?_
  exact Ideal.dvd_span_singleton.2 hv

theorem dense_frob (hC : GlobalTheory.TwSys.Cheb) {X : Set (HeightOneSpectrum (𝓞 D.host.E))} (hX : X.Finite) :
    Dense {g : GE D | ∃ P, P ∉ X ∧ Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal ≠ P.asIdeal ∧
      ∃ B : ValuationSubring (AlgebraicClosure D.host.E), IsPlaceOver (F := D.host.E) B P ∧ IsFrob (F := D.host.E) B (normV P) g} := by
  classical
  rw [dense_iff_inter_open]
  rintro W hW ⟨g, hg⟩
  have hV : IsOpen {s : GE D | s * g ∈ W} := hW.preimage (continuous_mul_const g)
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hV (by simpa using hg)
  obtain ⟨A, hA, hsp⟩ := GlobalTheory.FrobDense.exists_finite_split D.host
  obtain ⟨v, hv, hd, -, B, hB, -, σ, hσ, hU'⟩ := hC D.host.E (AlgebraicClosure D.host.E) U.toSubgroup U.isOpen U.isNormal' g
    (hA.toFinset ∪ hX.toFinset)
  simp only [Finset.mem_union, Set.Finite.mem_toFinset, not_or] at hv
  have := hU hU'
  simp only [Set.mem_ofPred_eq, inv_mul_cancel_right] at this
  refine ⟨σ, this, v, hv.2, fun e => ?_, B, hB, hσ⟩
  obtain ⟨x, hx, hx'⟩ := hsp v hv.1 hd
  rw [← e, Formalism.L2.Col.mem_conjIdeal] at hx
  refine hx' _ (D.host.φ₀.injective ?_) hx
  exact (D.sp.cm.cmUnram.2.1 D.host.φ₀ x).trans (D.host.conjE_apply D.host.φ₀ x).symm

def FrobFam (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (lab : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → Prop)
    (c : Sys D) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ), ∃ f : GE D → Matrix (Fin n) (Fin n) (Qbar l), Continuous f ∧
    ∀ P : HeightOneSpectrum (𝓞 D.host.E), OffS D S P → ((l : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal →
      ∃ s, IsPar P n (lab P) (c P) s ∧ ∀ (A : ValuationSubring (AlgebraicClosure D.host.E)) (g : GE D),
        IsPlaceOver (F := D.host.E) A P → IsFrob (F := D.host.E) A (normV P) g →
          (f g).charpoly.map (ι : Qbar l →+* ℂ) = frobPoly (normV P) n s

variable {V : HSp D} {J : Set (GA D V)} {χ : GA D V → ℂ} {S : Finset (HeightOneSpectrum (𝓞 D.host.F))}
  {lab : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → Prop} {c c' : Sys D}

theorem exists_prime_notMem (P : HeightOneSpectrum (𝓞 D.host.E)) : ∃ l : ℕ, l.Prime ∧ ((l : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
  by_contra h
  push Not at h
  have := P.asIdeal.sub_mem (h 3 Nat.prime_three) (h 2 Nat.prime_two)
  norm_num at this
  exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 this)

theorem FrobFam.eq (hC : GlobalTheory.TwSys.Cheb) {n : ℕ} (h : FrobFam n S lab c) (h' : FrobFam n S lab c')
    {X : Set (HeightOneSpectrum (𝓞 D.host.E))} (hX : X.Finite)
    (he : ∀ P, P ∉ X → Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal ≠ P.asIdeal → OffS D S P ∧ ∀ k, k ≤ n →
      lab P (dualLab (splitLab n k)) ∧ c P (dualLab (splitLab n k)) = c' P (dualLab (splitLab n k)))
    {P : HeightOneSpectrum (𝓞 D.host.E)} (hP : OffS D S P) {d : List ℤ} (hd : lab P d) : c P d = c' P d := by
  obtain ⟨l, hl, hlP⟩ := exists_prime_notMem P
  have : Fact l.Prime := ⟨hl⟩
  obtain ⟨ι⟩ := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex l
  obtain ⟨f, hf, h⟩ := h l ι
  obtain ⟨f', hf', h'⟩ := h' l ι
  have key : ∀ g, (f g).charpoly = (f' g).charpoly := fun g => by
    refine Polynomial.funext fun x => ?_
    rw [Matrix.eval_charpoly, Matrix.eval_charpoly]
    refine congrFun (Continuous.ext_on (dense_frob hC (hX.union (finite_over hl.ne_zero)))
      (f := fun g => (Matrix.scalar (Fin n) x - f g).det) (g := fun g => (Matrix.scalar (Fin n) x - f' g).det)
      (continuous_const.sub hf).matrix_det (continuous_const.sub hf').matrix_det ?_) g
    rintro g ⟨Q, hQ, hs, B, hB, hg⟩
    rw [Set.mem_union, not_or] at hQ
    obtain ⟨ho, hk⟩ := he Q hQ.1 hs
    obtain ⟨s, h1, h2⟩ := h Q ho hQ.2
    obtain ⟨s', h1', h2'⟩ := h' Q ho hQ.2
    have e : s = s' := eq_of_esymm (h1.1 hs).1 (h1'.1 hs).1 fun k hkn => by
      have a := GlobalTheory.T.spherical_coefficient_elementary_symm _ Q n _ _ s k (h1.1 hs) hkn (hk k hkn).1
      have b := GlobalTheory.T.spherical_coefficient_elementary_symm _ Q n _ _ s' k (h1'.1 hs) hkn (hk k hkn).1
      rw [(hk k hkn).2, b] at a
      refine (mul_left_cancel₀ (fun e0 => ?_) a).symm
      exact normV_ne Q (Nat.cast_eq_zero.1 ((Complex.cpow_eq_zero_iff _ _).1 e0).1)
    have e2 : (f g).charpoly = (f' g).charpoly :=
      Polynomial.map_injective (ι : Qbar l →+* ℂ) ι.injective ((h2 B g hB hg).trans (e ▸ (h2' B g hB hg).symm))
    show (Matrix.scalar (Fin n) x - f g).det = (Matrix.scalar (Fin n) x - f' g).det
    rw [← Matrix.eval_charpoly, ← Matrix.eval_charpoly, e2]
  obtain ⟨s, h1, h2⟩ := h P hP hlP
  obtain ⟨s', h1', h2'⟩ := h' P hP hlP
  obtain ⟨B, hB⟩ := ReciprocityTheory.Gal.exists_isPlaceOver (AlgebraicClosure D.host.E) P
  obtain ⟨g, hg⟩ := ReciprocityTheory.Gal.exists_isFrob hB
  have e : s = s' := frobPoly_inj (normV_ne P) (by rw [← h2 B g hB hg, ← h2' B g hB hg, key])
  subst e
  exact h1.eq h1' hd

end Galois

section Labels

variable {D : D7} {V V' : HSp D} {S : Finset (HeightOneSpectrum (𝓞 D.host.F))} {P : HeightOneSpectrum (𝓞 D.host.E)}
  {d : List ℤ}

theorem lab_of_div {J : Subgroup (GA D V)} {χ : GA D V → ℂ} (h : SphAt J χ P) (hS : OffS D S P) {e f : Formalism.L2.Theta.AE D}
    (hef : IsPrimeIdem P e f) {ϖ : 𝓞 D.host.E} (h1 : ϖ ∈ P.asIdeal) (h2 : ϖ ∉ P.asIdeal ^ 2)
    (hd : d.Pairwise (fun a b => b ≤ a)) {α : GA D V} (hα : SuppF V f α) (hdiv : DivAt V e (ϖ : D.host.E) d α) :
    Lab V (J : Set (GA D V)) χ S P d := by
  obtain ⟨R, hR, hc⟩ := GlobalTheory.T.coset_representatives_of_support V P e f α hef hα
  refine ⟨R, e, f, ϖ, α, hS, hef, h1, h2, hd, (h e f hef).1, (h e f hef).2.1, hα, hdiv, hR, ?_⟩
  have : {k | k ∈ (J : Set (GA D V)) ∧ SuppF V f k} = {k | k ∈ KsphC V ∅ ∧ SuppF V f k} :=
    Set.ext fun k => and_congr_left fun hk => (h e f hef).1 k hk
  rwa [this]

theorem Lab.off {J : Set (GA D V)} {χ : GA D V → ℂ} (h : Lab V J χ S P d) : OffS D S P ∧ d.length = V.rank := by
  obtain ⟨R, e, f, ϖ, α, hS, -, -, -, -, -, -, -, hdiv, -⟩ := h
  exact ⟨hS, hdiv.1⟩

theorem Lab.move {J : Set (GA D V)} {χ : GA D V → ℂ} (h : Lab V J χ S P d) (hr : V'.rank = V.rank) {J' : Subgroup (GA D V')}
    {χ' : GA D V' → ℂ} (h' : SphAt J' χ' P) : Lab V' (J' : Set (GA D V')) χ' S P d := by
  obtain ⟨R, e, f, ϖ, α, hS, hef, h1, h2, hd, -, -, hα, hdiv, -⟩ := h
  obtain ⟨α', h3, h4⟩ := GlobalTheory.T.divisor_support_transfer_rank V V' P e f ϖ d α hr hef hα hdiv
  exact lab_of_div h' hS hef h1 h2 hd h3 h4

theorem Lab.dual {J : Subgroup (GA D V)} {χ : GA D V → ℂ} (h : Lab V (J : Set (GA D V)) χ S P d) (h' : SphAt J χ P) :
    Lab V (J : Set (GA D V)) χ S P (dualLab d) := by
  obtain ⟨R, e, f, ϖ, α, hS, hef, h1, h2, hd, -, -, hα, hdiv, -⟩ := h
  obtain ⟨g1, -, g3, -⟩ := GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V
  obtain ⟨a, b, -⟩ := g3 P e f hef
  obtain ⟨⟨L, hL⟩, -⟩ := g1 f a b
  have he : e * e = e := by
    rcases hef with h | h
    · exact h.1.1.1
    · rw [← h.1]; exact a
  have hϖ : (ϖ : D.host.E) ≠ 0 := fun e0 => h2 (by rw [show ϖ = 0 from Subtype.ext e0]; exact zero_mem _)
  refine lab_of_div h' hS hef h1 h2 ?_ ((hL _).1 (L.inv_mem ((hL α).2 hα)))
    (GlobalTheory.DivDual.divAt_inv_and_mul V e ϖ d α he hϖ hdiv).1
  unfold dualLab
  rw [List.pairwise_reverse, List.pairwise_map]
  exact hd.imp fun hab => neg_le_neg hab

end Labels

section Record

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} {s : ℕ}

variable (R) in

def LabY : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → Prop :=
  Lab (Yc D 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) (badF R)

variable (R F) in

def GaloisRow : Prop :=
  R.Char F →
    (∀ c, OccE R c → HasGalois (Yc D 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) (badF R)
      (dualSys c)) ∧
    ∀ i c, OccW R i c → HasGalois (Wc D i) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) (badF R) c

end Record

end GlobalTheory.SphPar

end
