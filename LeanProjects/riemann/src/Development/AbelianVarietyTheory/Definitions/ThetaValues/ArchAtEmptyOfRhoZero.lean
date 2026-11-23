import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.NotJInjRdOfConst
import Formalism.LocalToGlobal.ProjectiveLattices.CuspMulOf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero
import Development.AbelianVarietyTheory.Counterexamples.UpperHalfSurvey.SumPnormMonAll

noncomputable section

namespace GlobalTheory.Shares.Model

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.RunIn

section Record

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j)

def rdRing : T.R j →+* (DomPt T j → ℂ) where
  toFun f y := rdU (T.U j T.σ₀) f y.1 y.2.1
  map_zero' := by funext y; rw [map_zero]; rfl
  map_add' f g := by funext y; rw [map_add]; rfl
  map_mul' f g := by funext y; rw [rdU_mul]; rfl
  map_one' := by
    funext y
    rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.rdU_apply_dom]
    exact congrArg (toC (σ := T.σ₀)) (evalAt_one _ _ ((T.U j T.σ₀).un y.1 y.2) (h.unTest j hj T.σ₀ T.good_σ₀ y.1 y.2))

def evG : AddMonoidAlgebra (T.R j) (Deg D j) →+* (DomPt T j → ℂ) :=
  AddMonoidAlgebra.liftNCRingHom (rdRing h j hj) 1 (fun _ _ => Commute.all _ _)

theorem evG_single (m : Deg D j) (f : T.R j) : evG h j hj (AddMonoidAlgebra.single m f) = rdRing h j hj f := by
  simp [evG, AddMonoidAlgebra.liftNCRingHom]

theorem evG_smul (a : T.Q.c.F) (F : AddMonoidAlgebra (T.R j) (Deg D j)) :
    evG h j hj (a • F) = T.σ₀ a • evG h j hj F := by
  induction F using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add F G hF hG => rw [smul_add, map_add, map_add, hF, hG, smul_add]
  | single m f =>
    rw [AddMonoidAlgebra.smul_single, evG_single, evG_single]
    funext y
    change rdU (T.U j T.σ₀) (a • f) y.1 y.2.1 = _
    rw [map_smulₛₗ]; rfl

set_option synthInstance.maxHeartbeats 200000 in
theorem evG_indep (u : WeightFamilies.Wt D j) (m : ℕ) (F : Fin m → (recB h.toLawsCore).Cusp j u) (hF : LinearIndependent (recB h.toLawsCore).KO F) :
    LinearIndependent ℂ fun i => evG h j hj (incG deg (cutR T.C j) u (F i)) := by
  have hJ := GlobalTheory.ReadingIndependence.jInjRd_of_laws T h.toLawsCore.toLawsM hj (wtA u) u.n m
    (fun i => Submodule.inclusion (cutR_le T.C j u) (F i))
    (hF.map' (Submodule.inclusion (cutR_le T.C j u)) (Submodule.ker_inclusion _ _ _))
  rw [Fintype.linearIndependent_iff] at hJ ⊢
  intro g hg
  refine hJ g ?_
  funext k x
  by_cases hx : x ∈ ((T.U j T.σ₀).X k).dom
  · have := congrFun hg ⟨k, x, hx⟩
    simp only [incG_apply, evG_single, Finset.sum_apply, Pi.smul_apply] at this ⊢
    exact this
  · simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    have : rdC (T.U j) T.σ₀ (wtA u) u.n (Submodule.inclusion (cutR_le T.C j u) (F i)) k x = 0 := dif_neg hx
    rw [this, smul_zero]

def rdgU (n : SecNorm (recB h.toLawsCore)) : Rdg (recPlusN h j hj n) where
  Y := DomPt T j
  σ := T.σ₀
  ev := evG h j hj
  ev_smul := evG_smul h j hj
  indep := evG_indep h j hj

theorem isRdgU_rdgU (n : SecNorm (recB h.toLawsCore)) : IsRdgU h j hj n (rdgU h j hj n) (Equiv.refl _) :=
  ⟨fun _ => rfl, fun u F y => congrFun (evG_single h j hj (deg u) F.1) y⟩

end Record

theorem li_congr {ι M : Type} [AddCommGroup M] [Module ℂ M] {v v' : ι → M} (h : LinearIndependent ℂ v)
    (e : ∀ i, v i = v' i) : LinearIndependent ℂ v' := by
  rw [← show v = v' from funext e]; exact h

section Poly

open MvPolynomial

variable {n : ℕ}

def ex (a : ℕ) (α : Fin n → ℕ) : Fin (n + 1) →₀ ℕ := Finsupp.equivFunOnFinite.symm (Fin.cons a α)

@[simp] theorem ex_zero (a : ℕ) (α : Fin n → ℕ) : ex a α 0 = a := rfl
@[simp] theorem ex_succ (a : ℕ) (α : Fin n → ℕ) (i : Fin n) : ex a α i.succ = α i := rfl

def tl (β : Fin (n + 1) →₀ ℕ) : ℕ := ∑ i : Fin n, β i.succ

theorem degree_eq (β : Fin (n + 1) →₀ ℕ) : β.degree = β 0 + tl β := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_succ]; rfl

theorem mono_ex (a : ℕ) (α : Fin n → ℕ) :
    (monomial (ex a α) (1 : ℂ)) = (∏ i, X i.succ ^ α i) * X 0 ^ a := by
  rw [monomial_eq, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_succ]
  simp [mul_comm]

theorem exists_le_sum (γ : Fin n → ℕ) (a : ℕ) (h : a ≤ ∑ i, γ i) : ∃ α : Fin n → ℕ, α ≤ γ ∧ ∑ i, α i = a := by
  induction a with
  | zero => exact ⟨0, fun _ => Nat.zero_le _, by simp⟩
  | succ a ih =>
    obtain ⟨α, h1, h2⟩ := ih (by omega)
    have : ∃ i, α i < γ i := by
      by_contra hc
      push Not at hc
      have := Finset.sum_le_sum (s := Finset.univ) fun i _ => hc i
      omega
    obtain ⟨i, hi⟩ := this
    refine ⟨α + Pi.single i 1, fun k => ?_, ?_⟩
    · by_cases hk : k = i
      · subst hk; simp; omega
      · simpa [hk] using h1 k
    · simp [Finset.sum_add_distrib, h2]

def supp (q : (Fin (n + 1) →₀ ℕ) → Prop) : Submodule ℂ (MvPolynomial (Fin (n + 1)) ℂ) where
  carrier := {p | ∀ β, ¬ q β → coeff β p = 0}
  zero_mem' := fun _ _ => by simp
  add_mem' := fun hp hq β hβ => by simp [hp β hβ, hq β hβ]
  smul_mem' := fun c p hp β hβ => by simp [hp β hβ]

theorem eval_single_eq_coeff (p : MvPolynomial (Fin (n + 1)) ℂ) {k : ℕ} (hp : p.IsHomogeneous k) :
    eval (Pi.single 0 1) p = coeff (ex k 0) p := by
  rw [eval_eq', Finset.sum_eq_single (ex k 0)]
  · rw [Fin.prod_univ_succ]; simp
  · intro β hβ hne
    have hd : β.degree = k := by
      by_contra hc
      exact (mem_support_iff.1 hβ) (hp.coeff_eq_zero hc)
    have : ∃ i : Fin n, β i.succ ≠ 0 := by
      by_contra hc
      push Not at hc
      apply hne
      have : tl β = 0 := Finset.sum_eq_zero fun i _ => hc i
      rw [degree_eq] at hd
      ext i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp; omega
      · simp [hc i]
    obtain ⟨i, hi⟩ := this
    rw [Finset.prod_eq_zero (Finset.mem_univ i.succ) (by simp [hi]), mul_zero]
  · intro hn; rw [notMem_support_iff.1 hn, zero_mul]

end Poly

section Proj

open MvPolynomial

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} (R : Rdg X)
  (φ : MvPolynomial (Fin (WeightFamilies.dimY D j + 1)) ℂ →ₐ[ℂ] (R.Y → ℂ))
  (hsp : ∀ u : WeightFamilies.Wt D j, R.sp u Set.univ = (homogeneousSubmodule _ ℂ (u.n / 2)).map φ.toLinearMap)
  {N : ℕ} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL) (t : Idx D j N → ℂ)
  (hs : ∀ i, R.s w t i = φ (MvPolynomial.X i))

include hs in
theorem mon_eq (α : Fin (WeightFamilies.dimY D j) → ℕ) (a : ℕ) :
    R.mon w t α * R.s w t 0 ^ a = φ (monomial (ex a α) 1) := by
  simp [Rdg.mon, hs, mono_ex]

include hs hsp in
theorem mono_mem_deep (u : WeightFamilies.Wt D j) (a : ℕ) (β : Fin (WeightFamilies.dimY D j + 1) →₀ ℕ) (c : ℂ)
    (hd : β.degree = u.n / 2 + a) (ha : a ≤ tl β) : φ (monomial β c) ∈ R.deep w t u a := by
  obtain ⟨α, h1, h2⟩ := exists_le_sum (fun i => β i.succ) a ha
  have hle : ex 0 α ≤ β := fun i => Fin.cases (by simp) (fun i => by simpa using h1 i) i
  have hdeg : (ex 0 α).degree = a := by rw [degree_eq]; simpa [tl] using h2
  have hsum : ex 0 α + (β - ex 0 α) = β := add_tsub_cancel_of_le hle
  refine Submodule.subset_span ⟨α, φ (monomial (β - ex 0 α) c), h2, ?_, ?_⟩
  · rw [hsp]
    refine ⟨_, isHomogeneous_monomial c ?_, rfl⟩
    have := congrArg Finsupp.degree hsum
    rw [map_add] at this
    omega
  · have := mon_eq R φ w t hs α 0
    rw [pow_zero, mul_one] at this
    rw [this, ← map_mul, monomial_mul, hsum, one_mul]

include hs hsp in
theorem deep_le (u : WeightFamilies.Wt D j) (a : ℕ) : R.deep w t u a ≤ (supp fun β => a ≤ tl β).map φ.toLinearMap := by
  refine Submodule.span_le.2 ?_
  rintro g ⟨α, f, hα, hf, rfl⟩
  rw [hsp] at hf
  obtain ⟨q, -, rfl⟩ := hf
  have := mon_eq R φ w t hs α 0
  rw [pow_zero, mul_one] at this
  refine ⟨monomial (ex 0 α) 1 * q, fun β hβ => ?_, by simp [this]⟩
  rw [coeff_monomial_mul', if_neg]
  intro hle
  apply hβ
  rw [← hα]
  exact Finset.sum_le_sum fun i _ => by simpa using hle i.succ

include hs hsp in
theorem anFacts_of_poly (hφ : Function.Injective φ) (x0 : R.Y) (hx : ∀ p, φ p x0 = eval (Pi.single 0 1) p)
    (hL : wL.n = 2) (ka wF : WeightFamilies.Wt D j) (hF : wF.n = 0) (T : ℕ) (hT : WeightFamilies.dimY D j ≤ T) (hk : ka.n = 2 * T) :
    AnFacts R w t ka wF T ⊤ (fun _ : Fin 1 => x0) := by
  have hconst : ∀ f ∈ R.sp wF Set.univ, f = φ (C (f x0)) := by
    intro f hf
    rw [hsp, hF] at hf
    obtain ⟨q, hq, rfl⟩ := hf
    have h0 : q.totalDegree = 0 := Nat.le_zero.1 (IsHomogeneous.totalDegree_le hq)
    rw [totalDegree_eq_zero_iff_eq_C] at h0
    change φ q = φ (C (φ q x0))
    rw [hx, h0]; simp
  have hlead : ∀ {m : ℕ} (θ : Fin m → R.Y → ℂ), (∀ i, θ i ∈ R.sp wF Set.univ) → ∀ p,
      R.lead w t T (a0 D j T) θ p = φ (monomial (ex (T - ∑ i, p.1.1 i) p.1.1) (θ p.2 x0)) := by
    intro m θ hθ p
    rw [Rdg.lead, mon_eq R φ w t hs, hconst _ (hθ p.2), ← map_mul, mul_comm, C_mul_monomial, ← hconst _ (hθ p.2),
      mul_one]
  have hrk : Module.finrank ℂ (R.sp ka Set.univ) = (T + WeightFamilies.dimY D j).choose (WeightFamilies.dimY D j) := by
    rw [hsp, (Submodule.equivMapOfInjective _ hφ _).symm.finrank_eq, GlobalTheory.ProjCut.finrank_homogeneousSubmodule, hk,
      Fintype.card_fin, show 2 * T / 2 = T by omega,
      show T + (WeightFamilies.dimY D j + 1) - 1 = T + WeightFamilies.dimY D j by omega, Nat.choose_symm_add]
  refine ⟨fun _ => ⟨?_, fun i => ?_⟩, fun v => ⟨φ (C (v 0)), ?_, fun q => ?_⟩, fun k g hg h0 => ⟨0, ?_⟩,
    fun m θ hθ hi => ⟨?_, ?_⟩, ?_, ?_, fun m θ hθ hspan => ?_⟩
  · simp [hs, hx]
  · simp [hs, hx]
  · rw [hsp, hF]; exact ⟨_, isHomogeneous_C _ _, rfl⟩
  · rw [hx, Subsingleton.elim q 0]; simp
  · have hn : (addL wF wL k).n / 2 = k := by
      change (wF.n + k * wL.n) / 2 = k
      rw [hF, hL]; omega
    rw [hsp, hn] at hg
    obtain ⟨q, hq, rfl⟩ := hg
    have h1 : coeff (ex k 0) q = 0 := by rw [← eval_single_eq_coeff q hq, ← hx]; exact h0 0
    change R.s w t 0 ^ (0 + 1) * φ q ∈ _
    rw [zero_add, pow_one, hs, ← map_mul, q.as_sum, Finset.mul_sum, map_sum]
    refine Submodule.sum_mem _ fun β hβ => ?_
    have hd : β.degree = k := by
      by_contra hc
      exact (mem_support_iff.1 hβ) (hq.coeff_eq_zero hc)
    rw [MvPolynomial.X, monomial_mul]
    refine mono_mem_deep R φ hsp w t hs _ _ _ _ ?_ ?_
    · rw [map_add, add_zero, hn, hd]; simp [add_comm]
    · by_contra hc
      have h2 : tl β = 0 := by
        have : tl β ≤ tl (Finsupp.single 0 1 + β) := Finset.sum_le_sum fun i _ => by simp
        omega
      apply mem_support_iff.1 hβ
      rw [← h1]
      congr 1
      rw [degree_eq] at hd
      ext i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp; omega
      · simpa using (Finset.sum_eq_zero_iff.1 h2) i (Finset.mem_univ _)
  · have hm : m ≤ 1 := by simpa using hi.fintype_card_le_finrank
    have hsub : Subsingleton (Fin m) := Fin.subsingleton_iff_le_one.2 hm
    have hne : ∀ i, θ i x0 ≠ 0 := fun i h => hi.ne_zero i (by funext q; exact h)
    have h1 : LinearIndependent ℂ fun p : {α : Fin (WeightFamilies.dimY D j) → ℕ // ∑ i, α i < a0 D j T} × Fin m =>
        (monomial (ex (T - ∑ i, p.1.1 i) p.1.1) (1 : ℂ)) := by
      have := (basisMonomials (Fin (WeightFamilies.dimY D j + 1)) ℂ).linearIndependent.comp
        (fun p : {α : Fin (WeightFamilies.dimY D j) → ℕ // ∑ i, α i < a0 D j T} × Fin m => ex (T - ∑ i, p.1.1 i) p.1.1)
        (fun p q hpq => Prod.ext (Subtype.ext (funext fun i => by simpa using DFunLike.congr_fun hpq i.succ))
          (Subsingleton.elim _ _))
      simpa [Function.comp_def] using this
    have h2 := (h1.units_smul fun p => Units.mk0 _ (hne p.2)).map' φ.toLinearMap (LinearMap.ker_eq_bot.2 hφ)
    refine li_congr h2 fun p => ?_
    rw [hlead θ hθ]
    simp [Units.smul_def, smul_monomial, ← map_smul]
  · have h1 : Submodule.span ℂ (Set.range (R.lead w t T (a0 D j T) θ)) ≤
        (supp fun β => tl β < a0 D j T).map φ.toLinearMap := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨p, rfl⟩
      refine ⟨_, fun β hβ => ?_, (hlead θ hθ p).symm⟩
      rw [coeff_monomial, if_neg]
      rintro rfl
      exact hβ (by simpa [tl] using p.1.2)
    refine Disjoint.mono h1 (deep_le R φ hsp w t hs _ _) ?_
    rw [disjoint_iff, ← Submodule.map_inf _ hφ, eq_bot_iff]
    rintro _ ⟨p, ⟨hp1, hp2⟩, rfl⟩
    have : p = 0 := by
      ext β
      by_cases hβ : tl β < a0 D j T
      · exact hp2 β (by omega)
      · exact hp1 β hβ
    simp [this]
  · rw [hrk, one_mul]; exact Nat.choose_le_choose _ (by omega)
  · rw [one_mul, ← hrk]; rfl
  · have hex : ∃ i, θ i x0 ≠ 0 := by
      by_contra hc
      push Not at hc
      have : Submodule.span ℂ (Set.range (vals (fun _ : Fin 1 => x0) θ)) ≤ ⊥ := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨i, rfl⟩
        funext q; exact hc i
      rw [hspan] at this
      have := congrFun (show (1 : Fin 1 → ℂ) = 0 from this Submodule.mem_top) 0
      simp at this
    obtain ⟨i, hi⟩ := hex
    change R.sp ka Set.univ ≤ _
    rw [hsp, hk, show 2 * T / 2 = T by omega]
    rintro _ ⟨q, hq, rfl⟩
    change φ q ∈ _
    rw [q.as_sum, map_sum]
    refine Submodule.sum_mem _ fun β hβ => ?_
    have hd : β.degree = T := by
      by_contra hc
      exact (mem_support_iff.1 hβ) (hq.coeff_eq_zero hc)
    by_cases hb : tl β < a0 D j T
    · refine Submodule.mem_sup_left ?_
      have h1 := hlead θ hθ (⟨fun i => β i.succ, hb⟩, i)
      have h2 : ex (T - ∑ i : Fin (WeightFamilies.dimY D j), β i.succ) (fun i => β i.succ) = β := by
        rw [degree_eq, tl] at hd
        ext i
        refine Fin.cases ?_ (fun i => ?_) i
        · simp; omega
        · simp
      simp only [h2] at h1
      have h3 : φ (monomial β (coeff β q)) =
          (coeff β q / θ i x0) • R.lead w t T (a0 D j T) θ (⟨fun i => β i.succ, hb⟩, i) := by
        rw [h1, ← map_smul, smul_monomial, smul_eq_mul, div_mul_cancel₀ _ hi]
      rw [h3]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
    · refine Submodule.mem_sup_right (mono_mem_deep R φ hsp w t hs _ _ _ _ ?_ (by omega))
      change _ = (wF.n + WeightFamilies.dimY D j * wL.n) / 2 + (T - WeightFamilies.dimY D j)
      rw [hd, hF, hL]; omega

end Proj

section Examples₂

open MvPolynomial

variable {D : D7} (B₀ : WeightFamilies.Prov D)

def hC (j : ℕ) (w : WeightFamilies.Wt D j) : Submodule B₀.KO (MvPolynomial (Fin (WeightFamilies.dimY D j + 1)) B₀.KO) :=
  homogeneousSubmodule _ _ (w.n / 2)

def hN (j : ℕ) (w : WeightFamilies.Wt D j) (σ : B₀.KO →+* ℂ) (f : MvPolynomial (Fin (WeightFamilies.dimY D j + 1)) B₀.KO) : ℝ :=
  ∑ m ∈ Finset.finsuppAntidiag Finset.univ (w.n / 2), ‖σ (coeff m f)‖

theorem hN_norm (j : ℕ) (_ : InR D j) (w : WeightFamilies.Wt D j) (σ : B₀.KO →+* ℂ) : IsNormOn (hC B₀ j w) σ (hN B₀ j w σ) where
  nonneg f _ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  defin f hf h0 := by
    ext m
    by_cases hm : m.degree = w.n / 2
    · have := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => norm_nonneg _).1 h0 m
        (by rw [Finset.mem_finsuppAntidiag]; exact ⟨by rw [← hm, Finsupp.degree_eq_sum], Finset.subset_univ _⟩)
      simpa using this
    · exact IsHomogeneous.coeff_eq_zero hf hm
  smul a f _ := by simp [hN, Finset.mul_sum]
  add f _ g _ := by
    rw [hN, hN, hN, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun m _ => by rw [coeff_add, map_add]; exact norm_add_le _ _

theorem hC_fd (j : ℕ) (_ : InR D j) (w : WeightFamilies.Wt D j) : FiniteDimensional B₀.KO (hC B₀ j w) :=
  Module.Finite.iff_fg.2 (homogeneousSubmodule_fg _ _ _)

abbrev exampleB : WeightFamilies.Prov D :=
  mkB B₀.eO (hC B₀) (hC_fd B₀) (fun _ _ => ∅) (fun _ _ _ h => h.elim) (hN B₀) (hN B₀) (hN_norm B₀) (hN_norm B₀)
    (fun _ _ _ _ _ _ => le_rfl) (fun _ => Empty) (fun _ c => c.elim) (fun _ c => c.elim) (fun _ _ _ _ => PUnit)
    (fun _ _ _ _ => 0)

variable {B₀} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X₀ : PJ D B₀ P j) (hj : InR D j)

def toyX : PJ D (exampleB B₀) P j :=
  mkX B₀.eO (hC B₀) (hC_fd B₀) (fun _ _ => ∅) (fun _ _ _ h => h.elim) (hN B₀) (hN B₀) (hN_norm B₀) (hN_norm B₀)
    (fun _ _ _ _ _ _ => le_rfl) (fun _ => Empty) (fun _ c => c.elim) (fun _ c => c.elim) (fun _ _ _ _ => PUnit)
    (fun _ _ _ _ => 0) P j hj
    (fun w w' f hf g hg => by
      have h : (wadd w w').n / 2 = w.n / 2 + w'.n / 2 := by
        obtain ⟨a, ha⟩ := w.n_even
        obtain ⟨b, hb⟩ := w'.n_even
        change (w.n + w'.n) / 2 = _
        omega
      rw [hC, h]; exact IsHomogeneous.mul hf hg)
    X₀.dat X₀.dat_rk X₀.dat_jj (fun _ => Empty) (fun _ y => y.elim) (fun _ y => y.elim) (fun _ y => y.elim)
    (fun _ _ _ => ⟨fun _ _ y => y.elim, fun _ _ _ h => h.elim⟩) (fun _ => ∅) (fun _ => ∅)

def fn (n : ℕ) : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ((Fin n → ℂ) → ℂ) := aeval fun i y => y i

theorem fn_apply {n : ℕ} (p : MvPolynomial (Fin n) ℂ) (y : Fin n → ℂ) : fn n p y = eval y p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [fn]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => rw [map_mul, Pi.mul_apply, hp]; simp [fn]

theorem fn_inj (n : ℕ) : Function.Injective (fn n) := fun p q h =>
  MvPolynomial.funext fun y => by rw [← fn_apply, ← fn_apply, h]

variable {K : Type} [Field K] (σ : K →+* ℂ)

def evP (n : ℕ) (M : Type) [AddCommMonoid M] : AddMonoidAlgebra (MvPolynomial (Fin n) K) M →+* ((Fin n → ℂ) → ℂ) :=
  AddMonoidAlgebra.liftNCRingHom ((fn n).toRingHom.comp (MvPolynomial.map σ)) 1 (fun _ _ => Commute.all _ _)

theorem evalEmbedding_single {n : ℕ} {M : Type} [AddCommMonoid M] (m : M) (f : MvPolynomial (Fin n) K) :
    evP σ n M (AddMonoidAlgebra.single m f) = fn n (MvPolynomial.map σ f) := by
  simp [evP, AddMonoidAlgebra.liftNCRingHom]

theorem evalEmbedding_smul {n : ℕ} {M : Type} [AddCommMonoid M] (a : K) (F : AddMonoidAlgebra (MvPolynomial (Fin n) K) M) :
    evP σ n M (a • F) = σ a • evP σ n M F := by
  induction F using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add F G hF hG => rw [smul_add, map_add, map_add, hF, hG, smul_add]
  | single m f =>
    rw [AddMonoidAlgebra.smul_single, evalEmbedding_single, evalEmbedding_single, ← map_smul, smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C]

theorem map_indep {n m : ℕ} (F : Fin m → MvPolynomial (Fin n) K) (hF : LinearIndependent K F) :
    LinearIndependent ℂ fun i => MvPolynomial.map σ (F i) := by
  letI : Algebra K ℂ := σ.toAlgebra
  have h1 := (Module.Flat.linearIndependent_one_tmul (S := ℂ) hF).map'
    (algebraTensorAlgEquiv K ℂ (σ := Fin n)).toLinearEquiv.toLinearMap (LinearEquiv.ker _)
  refine li_congr h1 fun i => ?_
  simp
  rfl

def exampleEvaluation (σ : B₀.KO →+* ℂ) : Rdg (toyX X₀ hj) where
  Y := Fin (WeightFamilies.dimY D j + 1) → ℂ
  σ := σ
  ev := evP σ _ (Deg D j)
  ev_smul := evalEmbedding_smul σ
  indep u m F hF := by
    have h1 := (map_indep σ _ (hF.map' (cutR (hC B₀) j u).subtype (Submodule.ker_subtype _))).map'
      (fn _).toLinearMap (LinearMap.ker_eq_bot.2 (fn_inj _))
    exact li_congr h1 fun i => (evalEmbedding_single σ (deg u) (F i).1).symm

theorem exampleEvaluation_span_univ (σ : B₀.KO →+* ℂ) (u : WeightFamilies.Wt D j) :
    (exampleEvaluation X₀ hj σ).sp u Set.univ = (homogeneousSubmodule _ ℂ (u.n / 2)).map (fn _).toLinearMap := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨F, -, rfl⟩
    exact ⟨_, IsHomogeneous.map (cutR_le (hC B₀) j u F.2) σ, (evalEmbedding_single σ (deg u) F.1).symm⟩
  · rintro _ ⟨q, hq, rfl⟩
    change fn _ q ∈ _
    rw [q.as_sum, map_sum]
    refine Submodule.sum_mem _ fun β hβ => ?_
    have hd : β.degree = u.n / 2 := by
      by_contra hc
      exact (mem_support_iff.1 hβ) (IsHomogeneous.coeff_eq_zero hq hc)
    have hm : (monomial β (1 : B₀.KO)) ∈ cutR (hC B₀) j u := by
      rw [cutR_eq _ hj]; exact isHomogeneous_monomial _ hd
    have : fn _ (monomial β (coeff β q)) = coeff β q • fn _ (MvPolynomial.map σ (monomial β 1)) := by
      rw [← map_smul, map_monomial, map_one, smul_monomial, smul_eq_mul, mul_one]
    have h2 : fn _ (MvPolynomial.map σ (monomial β 1)) ∈ (exampleEvaluation X₀ hj σ).sp u Set.univ :=
      Submodule.subset_span ⟨⟨_, hm⟩, trivial, evalEmbedding_single σ (deg u) _⟩
    rw [this]
    exact ((exampleEvaluation X₀ hj σ).sp u Set.univ).smul_mem (coeff β q) h2

def toyW (k : Fin (WeightFamilies.dimY D j + 1)) : (exampleB B₀).Cusp j (wscalar D j 2 even_two) :=
  ⟨MvPolynomial.X k, by rw [cutR_eq _ hj]; rw [hC, show (wscalar D j 2 even_two).n / 2 = 1 from Nat.div_self two_pos]; exact isHomogeneous_X B₀.KO k⟩

theorem toy (σ : B₀.KO →+* ℂ) (T : ℕ) (hT : WeightFamilies.dimY D j ≤ T) :
    AnFacts (exampleEvaluation X₀ hj σ) (toyW hj) (fun p => if p.1 = p.2 then 1 else 0) (wscalar D j (2 * T) (even_two_mul T))
      (wscalar D j 0 Even.zero) T ⊤ (fun _ : Fin 1 => (Pi.single 0 1 : Fin (WeightFamilies.dimY D j + 1) → ℂ)) := by
  refine anFacts_of_poly (exampleEvaluation X₀ hj σ) (fn _) (exampleEvaluation_span_univ X₀ hj σ) _ _ (fun i => ?_) (fn_inj _) _
    (fun p => fn_apply p _) rfl _ _ rfl T hT rfl
  have h : ∀ k, (exampleEvaluation X₀ hj σ).ev ((toyX X₀ hj).inc _ (toyW hj k)) = fn _ (MvPolynomial.X k) := fun k =>
    (evalEmbedding_single σ _ _).trans (congrArg _ (map_X σ k))
  simp only [Rdg.s, h]
  rw [Finset.sum_eq_single i (fun b _ hb => by rw [if_neg hb.symm]; exact zero_smul ℂ _) (by simp), if_pos rfl]
  exact one_smul ℂ _

end Examples₂

section Lines

open ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MvPolynomial

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {K : Type} [Field K]

theorem homRel_of_monomials (σ : K →+* ℂ) (X : Data E r) {m d : ℕ} (hm : 3 < m) (hd : 0 < d)
    (v : Fin 4 → Frame X.Ψ r → ℂ) (u : Fin m → Frame X.Ψ r → ℂ)
    (hu : ∀ a, ∃ e : Fin 4 → ℕ, e 0 + e 1 = d ∧ e 2 + e 3 = d ∧ ∀ x, u a x = ∏ k, v k x ^ e k) : HomRel σ X u := by
  choose e h1 h2 hu using hu
  have hdep : ¬ LinearIndependent ℤ fun a (k : Fin 3) => (e a k.castSucc : ℤ) := fun h => by
    have := h.fintype_card_le_finrank
    simp at this; omega
  obtain ⟨c, hc, a0, ha0⟩ := Fintype.not_linearIndependent_iff.1 hdep
  have hk : ∀ k : Fin 3, ∑ a, c a * e a k.castSucc = 0 := fun k => by simpa using congrFun hc k
  have hs : ∑ a, c a = 0 := by
    have : (∑ a, c a) * d = ∑ a, c a * e a 0 + ∑ a, c a * e a 1 := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a _ => by rw [← h1 a]; push_cast; ring
    rw [show ∑ a, c a * e a 0 = 0 from hk 0, show ∑ a, c a * e a 1 = 0 from hk 1, add_zero] at this
    exact (mul_eq_zero.1 this).resolve_right (by exact_mod_cast hd.ne')
  have hall : ∀ k : Fin 4, ∑ a, c a * e a k = 0 := by
    intro k
    refine Fin.lastCases ?_ hk k
    have : (∑ a, c a) * d = ∑ a, c a * e a 2 + ∑ a, c a * e a 3 := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a _ => by rw [← h2 a]; push_cast; ring
    rw [hs, zero_mul, show ∑ a, c a * e a 2 = 0 from hk 2, zero_add] at this
    exact this.symm
  let cp : Fin m →₀ ℕ := Finsupp.equivFunOnFinite.symm fun a => (c a).toNat
  let cm : Fin m →₀ ℕ := Finsupp.equivFunOnFinite.symm fun a => (-c a).toNat
  have hpm : ∀ a, c a = (cp a : ℤ) - cm a := fun a => (Int.toNat_sub_toNat_neg (c a)).symm
  have hne : cp ≠ cm := fun h => ha0 (by rw [hpm, h, sub_self])
  have hdeg : cp.degree = cm.degree := by
    rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum]
    simp only [hpm, Finset.sum_sub_distrib, sub_eq_zero] at hs
    exact_mod_cast hs
  have hexp : ∀ k, ∑ a, e a k * cp a = ∑ a, e a k * cm a := fun k => by
    have := hall k
    simp only [hpm, sub_mul, Finset.sum_sub_distrib, sub_eq_zero] at this
    simp only [mul_comm (e _ k)]
    exact_mod_cast this
  have hev : ∀ (β : Fin m →₀ ℕ) x, eval₂ σ (fun i => u i x) (monomial β 1) = ∏ k, v k x ^ ∑ a, e a k * β a := by
    intro β x
    rw [eval₂_monomial, map_one, one_mul, Finsupp.prod_fintype _ _ (by simp)]
    simp only [hu, ← Finset.prod_pow, ← pow_mul]
    rw [Finset.prod_comm]
    exact Finset.prod_congr rfl fun k _ => Finset.prod_pow_eq_pow_sum _ _ _
  refine ⟨monomial cp 1 - monomial cm 1, cm.degree, fun h => ?_,
    (isHomogeneous_monomial _ hdeg).sub (isHomogeneous_monomial _ rfl), fun x _ => ?_⟩
  · have := congrArg (coeff cp) h
    simp [coeff_monomial, hne.symm] at this
  · rw [eval₂_sub, hev, hev]; simp [hexp]

theorem margins_of_definite (X : Data E r) (hp : X.p0 = 0 ∨ X.p0 = r) (Xa : ArchInM X)
    (hC : ∃ C : ℝ, ∀ x ∈ X.dom, Xa.ps0 x ≤ C) (hiso : ∀ ξ, ¬ X.IsIso ξ) : Margins X Xa := by
  obtain ⟨⟨_, _, -, -, h1⟩, ⟨_, _, -, -, h2⟩⟩ := GlobalTheory.InterpCheck.margins_definite X hp Xa
  have hR := GlobalTheory.InterpCheck.leviRh_definite X hp
  have hL := GlobalTheory.InterpCheck.leviL_nonneg X Xa
  refine ⟨⟨_, _, lt_add_one _, lt_add_one _, fun τ hτ x0 ho z hz ξ => ?_⟩,
    ⟨_, _, lt_add_one _, lt_add_one _, fun x0 ho z hz ξ => ?_⟩, hL, hC,
    fun k P hP => ⟨hP, fun ξ hξ => (hiso ξ hξ).elim⟩⟩
  · have a1 := h1 x0 ho z hz ξ
    have a2 := h2 x0 ho z hz ξ
    rw [hR x0 ho, mul_zero] at a1 a2 ⊢
    rcases hτ with rfl | rfl
    · simpa using a1
    · exact a2
  · have a1 := h1 x0 ho z hz ξ
    rw [hR x0 ho, mul_zero] at a1 ⊢
    have := mul_nonneg (Nat.cast_nonneg (α := ℝ) (nd X)) (hL x0 ho z hz ξ)
    linarith

open GlobalTheory.TwoLines GlobalTheory.InterpCheck.Lines in

theorem relIn_margins_lines (σ : K →+* ℂ) (h : Module.finrank ℚ E = 4) :
    ∃ (X : Data E 2) (Xa : ArchInM X) (Fl : FlatM X Xa), Fl.δ = 2 ∧ RelIn σ X Xa ∧ Margins X Xa := by
  obtain ⟨τ₁, τ₂, hne, hall⟩ := exists_two (defData E) h
  have hn := GlobalTheory.InterpCheck.Lines.nd_eq_two hne hall
  let v : Fin 4 → Frame (defData E).Ψ 2 → ℂ :=
    ![fun x => x τ₁ 0 0, fun x => x τ₁ 1 0, fun x => x τ₂ 0 0, fun x => x τ₂ 1 0]
  have hw : ∀ (k : Fin 4) (d : ℕ), ∃ e : Fin 4 → ℕ, e 0 + e 1 = d ∧ e 2 + e 3 = d ∧
      ∀ x, GlobalTheory.InterpCheck.Lines.monAll τ₁ τ₂ k x ^ d = ∏ i, v i x ^ e i := by
    intro k d
    fin_cases k
    · exact ⟨![d, 0, d, 0], rfl, rfl, fun x => by
        simp [v, GlobalTheory.InterpCheck.Lines.monAll, GlobalTheory.InterpCheck.Lines.mon, Fin.prod_univ_four, mul_pow]⟩
    · exact ⟨![d, 0, 0, d], rfl, by simp, fun x => by
        simp [v, GlobalTheory.InterpCheck.Lines.monAll, GlobalTheory.InterpCheck.Lines.mon, Fin.prod_univ_four, mul_pow]⟩
    · exact ⟨![0, d, d, 0], by simp, rfl, fun x => by
        simp [v, GlobalTheory.InterpCheck.Lines.monAll, GlobalTheory.InterpCheck.Lines.mon, Fin.prod_univ_four, mul_pow]⟩
    · exact ⟨![0, d, 0, d], by simp, by simp, fun x => by
        simp [v, GlobalTheory.InterpCheck.Lines.monAll, GlobalTheory.InterpCheck.Lines.mon, Fin.prod_univ_four, mul_pow]⟩
  refine ⟨defData E, GlobalTheory.InterpCheck.Lines.thetaIn rfl rfl rfl hne hall,
    GlobalTheory.InterpCheck.Lines.flatIn rfl rfl rfl hne hall, rfl, ⟨fun jj => ?_, fun jj => ?_⟩,
    margins_of_definite _ (Or.inr rfl) _ ⟨0, fun _ _ => le_rfl⟩ (not_isIso rfl)⟩
  · refine homRel_of_monomials σ _ (by omega) one_pos v _ fun a => ?_
    obtain ⟨e, h1, h2, h3⟩ := hw (jj a) 1
    exact ⟨e, h1, h2, fun x => by rw [← h3, pow_one]; rfl⟩
  · refine homRel_of_monomials σ _ (by omega) two_pos v _ fun a => ?_
    refine Fin.cases ?_ (fun a => ?_) a
    · obtain ⟨e, h1, h2, h3⟩ := hw 0 2
      refine ⟨e, h1, h2, fun x => ?_⟩
      rw [← h3]
      change GlobalTheory.InterpCheck.Lines.mon τ₁ τ₂ 0 0 x ^ 0 * (GlobalTheory.InterpCheck.Lines.mon τ₁ τ₂ 0 0 x ^ 2) ^ (1 * (2 / 2)) =
        GlobalTheory.InterpCheck.Lines.mon τ₁ τ₂ 0 0 x ^ 2
      norm_num
    · obtain ⟨e, h1, h2, h3⟩ := hw (jj a) 2
      refine ⟨e, h1, h2, fun x => ?_⟩
      rw [← h3]
      change GlobalTheory.InterpCheck.Lines.monAll τ₁ τ₂ (jj a) x ^ (2 * (1 * (2 / 2))) = _
      norm_num

end Lines

theorem archAt_empty_of_rho_zero {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) {N : ℕ} {wL wF : WeightFamilies.Wt D j}
    (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Tn : ℕ) (CR Tt c : ℝ) (h0 : WeightFamilies.rho D j = 0)
    (k : (T.U j T.σ₀).Comp) : IsEmpty (ArchAt h j w wF Tn (WeightFamilies.c1 D CR Tt c j)) :=
  ⟨fun A => by
    have := (A.Xa k).frame_theta_const_pos
    rw [A.hc k, WeightFamilies.c1, h0] at this
    simp at this⟩

end GlobalTheory.Shares.Model
