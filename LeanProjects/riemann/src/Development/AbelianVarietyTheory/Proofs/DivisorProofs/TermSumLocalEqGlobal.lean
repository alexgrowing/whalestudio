import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHtFunGenericIff
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonomialEqProd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArTopTrue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagAtWholeSymbolReindexedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairStatementOfHeightAlterationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainStatementOfPublishedInputsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOfHasChainAtPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootLetterInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleModelCommutes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenAwayAgree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LetterHeightDifferenceBounded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialNumeratorLinearExtension

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx
open scoped Classical
open MvPolynomial

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HodgeLat

section Cover

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

theorem sum_num_cons_eq_zero (hP : Hypotheses2) (V : Cover Y) (num : Form (Cl V.p) Y.dim) (hn : IsArForm Y.dim num)
    (M : HermLB V.p) (lg : ∀ v : HeightOneSpectrum (𝓞 F), TrueGeo.Ext v → AlgPt Y → ℝ)
    (hM : Norms V M (fun _ => 1) (fun _ _ => 0) lg) (S : Finset ℕ) (b : ℕ → ℝ) (hb : ∀ p ∈ S, p.Prime ∧ 0 ≤ b p)
    (hlg : ∀ v e y, |lg v e y| ≤ (if resP v ∈ S then b (resP v) else 0) * (-Real.log (e.w (resP v : AlgebraicClosure F))))
    {T : Type} [Fintype T] (N : T → Fin Y.dim → HermLB V.p)
    (h : ∀ p ∈ S, ∀ [Fact p.Prime] (Z : Scheme.{0}) (i : Z ⟶ V.X) [IsClosedImmersion i] [IsIntegral Z] [Algebra (ZMod p) Γ(Z, ⊤)],
      topologicalKrullDim Z = Y.dim → ∑ t, interNum (ZMod p) (structureModule Z) (fun j => (N t j).B.pull i) = 0) :
    ∑ t, num (Fin.cons (cl M) fun j => cl (N t j)) = 0 := by
  haveI : IsLocallyNoetherian V.X := V.ar.isLocallyNoetherian
  haveI : IsNoetherian V.X := V.ar.isNoetherian
  obtain ⟨r, hr, h1, hmult⟩ := GlobalTheory.T.local_height_bounded_by_prime_weights F Y V M lg hM S b hb hlg
  have key (z : V.X) : ∃ (p : ℕ) (d : T → ℝ), ∑ t, d t = 0 ∧ ((M.div hr).mult z ≠ 0 → ∀ t,
      ∃ (_ : Fact p.Prime) (Z : Scheme.{0}) (i : Z ⟶ V.X) (_ : IsClosedImmersion i) (_ : IsIntegral Z)
        (_ : Algebra (ZMod p) Γ(Z, ⊤)), i (genericPoint Z) = z ∧ topologicalKrullDim Z = Y.dim ∧
          d t = interNum (ZMod p) (structureModule Z) (fun j => (N t j).B.pull i)) := by
    by_cases hz : (M.div hr).mult z = 0
    · exact ⟨0, 0, by simp, fun h => absurd hz h⟩
    obtain ⟨p, hpS, hpos⟩ : ∃ p ∈ S, 0 < Scheme.ord ((p : V.X.functionField)) z := by
      by_contra hc
      push_neg at hc
      refine hz ?_
      have := hmult z
      rw [Finset.sum_eq_zero fun l hl => by
        rw [le_antisymm (hc l hl) ((GlobalTheory.T.prime_divisors_effective_finite_disjoint _ V.X V.p _ V.ar l (hb l hl).1).1 z), Int.cast_zero, mul_zero]] at this
      exact_mod_cast abs_nonpos_iff.1 this
    haveI := Fact.mk (hb p hpS).1
    obtain ⟨Z, i, hi, hZ, hA, e₁, e₂⟩ := GlobalTheory.T.exists_integral_subscheme_prime_fibre _ V.X V.p _ V.ar p z hpos
    exact ⟨p, fun t => interNum (ZMod p) (structureModule Z) fun j => (N t j).B.pull i,
      by beta_reduce; exact_mod_cast h p hpS Z i e₂, fun _ t => ⟨‹_›, Z, i, hi, hZ, hA, e₁, e₂, rfl⟩⟩
  choose q d hd₀ hd using key
  have hfin : (Function.support (M.div hr).mult).Finite := (M.div hr).finite_support_mult
  have e (t : T) : num (Fin.cons (cl M) fun j => cl (N t j)) =
      ∑ z ∈ hfin.toFinset, ((M.div hr).mult z : ℝ) * d z t * Real.log (q z) := by
    rw [GlobalTheory.T.height_of_rational_section_via_divisor hP _ V.X V.p _ V.ar num hn M r hr h1 (N t) q (fun z => d z t) fun z hz => hd z hz t]
    exact finsum_eq_sum_of_support_subset _ fun z hz => hfin.mem_toFinset.2 fun h0 => hz (by simp [h0])
  rw [Finset.sum_congr rfl fun t _ => e t, Finset.sum_comm]
  exact Finset.sum_eq_zero fun z _ => by rw [← Finset.sum_mul, ← Finset.mul_sum, hd₀, mul_zero, zero_mul]

theorem exists_cover_forall (V₀ : Cover Y) (S : Finset ℕ)
    (Q : ℕ → ∀ V' : Cover Y, Prop)
    (h : ∀ p ∈ S, ∃ V : Cover Y, ∀ (V' : Cover Y) (π : V'.X ⟶ V.X), π ≫ V.p = V'.p → Lies V' V π → Q p V') :
    ∃ V : Cover Y, ∀ (V' : Cover Y) (π : V'.X ⟶ V.X), π ≫ V.p = V'.p → Lies V' V π → ∀ p ∈ S, Q p V' := by
  induction S using Finset.induction_on with
  | empty => exact ⟨V₀, fun _ _ _ _ p hp => absurd hp (Finset.notMem_empty p)⟩
  | insert p S hp ih =>
    obtain ⟨V₁, h₁⟩ := h p (Finset.mem_insert_self _ _)
    obtain ⟨V₂, h₂⟩ := ih fun q hq => h q (Finset.mem_insert_of_mem hq)
    obtain ⟨V, π₁, π₂, e₁, e₂, l₁, l₂⟩ := GlobalTheory.T.common_refinement_covers F Y V₁ V₂
    have tr : ∀ (V' W : Cover Y) (π : V'.X ⟶ V.X) (ρ : V.X ⟶ W.X), Lies V' V π → Lies V W ρ → Lies V' W (π ≫ ρ) := by
      rintro V' W π ρ ⟨g, a, b⟩ ⟨g', a', b'⟩
      exact ⟨g ≫ g', by rw [Category.assoc, a', ← Category.assoc, a, Category.assoc], by rw [Category.assoc, b', b]⟩
    refine ⟨V, fun V' π e l q hq => ?_⟩
    rcases Finset.mem_insert.1 hq with rfl | hq
    · exact h₁ V' (π ≫ π₁) (by rw [Category.assoc, e₁, e]) (tr _ _ _ _ l l₁)
    · exact h₂ V' (π ≫ π₂) (by rw [Category.assoc, e₂, e]) (tr _ _ _ _ l l₂) q hq

theorem powerSum_mul_vertical (hP : Hypotheses2) (M : TrueGeo.Model Y) {ι : Type} [Fintype ι]
    (A : ι → Adl (cxSt F) Y) (L : ι → HermLB M.p) (m : ℕ+) (Ψ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ)
    (hI : ∀ i, (A i).Induced M (L i) m 0) (hΨ : haveI := M.ar.isIntegral; IsArFun L Y.dim Ψ) (S : Finset ℕ)
    (b : ℕ → ℝ) (hb : ∀ p ∈ S, p.Prime ∧ 0 ≤ b p) {κ : Type} [Fintype κ]
    (s : κ → ι) (hfl : ∀ p ∈ S, ∃ (N : ℕ) (ε : Fin N ≃ κ), FlagAt (fun a => A (s (ε a))) p) (i₀ i₁ : ι)
    (e : A i₁ = { A i₀ with lg := (A i₁).lg })
    (hlg : ∀ v e y, |(A i₀).lg v e y - (A i₁).lg v e y| ≤
      (if resP v ∈ S then b (resP v) else 0) * (-Real.log (e.w (resP v : AlgebraicClosure F)))) (k : ℕ) (hk : 1 ≤ k)
    (g : MvPolynomial ι ℝ) :
    Ψ ((∑ a, X (s a) ^ k) * ((X i₀ - X i₁) * g)) = 0 := by
  have hC := hP.p4
  obtain ⟨Q₀, -, -, hQ₀, -⟩ := GlobalTheory.ModelDom.exists_normal_dominating F Y M M
  obtain ⟨V, hF⟩ := exists_cover_forall (Cover.ofModel Q₀ hQ₀) S
    (fun p V' => ∃ (N : ℕ) (ε : Fin N ≃ κ), ∀ (L : Fin N → LB V'.X) (hL : ∀ i, (L i).IsLB) (m : ℕ),
      (∀ i, NormsAt V' (L i) p ⊤ (fun x => genAt (A (s (ε i))).D x ^ m) fun v e y => m * (A (s (ε i))).lg v e y) →
      ∀ (Z : Scheme.{0}) [IsIntegral Z] (ι : Z ⟶ V'.X), (p : Γ(Z, ⊤)) = 0 →
        ∃ g : Fin N → Pic Z, FlagOfTriv g ∧ ∀ i, CechPic.pull ι (cls (L i) (hL i)) = m • g i)
    fun p hp => by
      obtain ⟨N, ε, V, hV⟩ := hfl p hp
      exact ⟨V, fun V' π h₁ h₂ => ⟨N, ε, hV V' π h₁ h₂⟩⟩
  obtain ⟨V', π, L', d, hπ, hl, hd, hL', hΦ⟩ := GlobalTheory.T.exists_cover_induced_metrics_arith hC F Y M V ι A L m Ψ hI hΨ
  refine (mul_eq_zero.1 (show d * _ = 0 from ?_)).resolve_left hd
  change (d • Ψ) _ = 0
  generalize d • Ψ = Φ at hΦ
  obtain ⟨num, hn, -⟩ := GlobalTheory.T.arith_intersection_form_exists hC _ _ V'.p _ V'.ar
  obtain ⟨rt, rd, -, -⟩ := GlobalTheory.T.arith_class_form_properties hC _ _ V'.p _ V'.ar num hn
  induction g using MvPolynomial.induction_on' with
  | add P Q hP hQ => rw [mul_add, mul_add, map_add, hP, hQ, add_zero]
  | monomial u a =>
    obtain ⟨n, ν, hν⟩ := exists_monomial_eq_prod u
    have e₁ : (monomial u a : MvPolynomial ι ℝ) = a • ∏ j, X (ν j) := by rw [← hν, smul_monomial, smul_eq_mul, mul_one]
    rw [e₁, mul_smul_comm, mul_smul_comm, map_smul, smul_eq_zero]
    refine .inr ?_
    by_cases hD : Y.dim = k + n
    swap
    · refine hΦ.2 _ (k + (1 + ∑ _j : Fin n, 1)) (by simp; omega) ?_
      exact (IsHomogeneous.sum _ _ _ fun a _ => isHomogeneous_X_pow _ _).mul
        (((isHomogeneous_X _ _).sub (isHomogeneous_X _ _)).mul (IsHomogeneous.prod _ _ _ fun j _ => isHomogeneous_X _ _))
    obtain ⟨ν', hν'⟩ := exists_prod_ite hD i₀ ν
    have hv := sum_num_cons_eq_zero hP V' num hn _ _ (norms_div e (hL' i₀) (hL' i₁)) S (fun p => (m : ℕ) * b p)
      (fun p hp => ⟨(hb p hp).1, mul_nonneg (Nat.cast_nonneg _) (hb p hp).2⟩)
      (fun v ε y => by
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
        refine (mul_le_mul_of_nonneg_left (hlg v ε y) (Nat.cast_nonneg _)).trans_eq ?_
        split_ifs <;> ring)
      (fun a j => L' (if (j : ℕ) < k then s a else ν' j)) (fun p hp _ Z i _ _ _ hZ => by
        have h0 : (p : Γ(Z, ⊤)) = 0 := by rw [← map_natCast (algebraMap (ZMod p) Γ(Z, ⊤)), ZMod.natCast_self, map_zero]
        obtain ⟨N, ε, hF'⟩ := hF V' π hπ hl p hp
        obtain ⟨g, hg, hg'⟩ := hF' (fun a => (L' (s (ε a))).B) (fun a => (L' (s (ε a))).isLB) m
          (fun a => normsAt_of_norms (hL' (s (ε a))) p ⊤) Z i h0
        rw [← ε.sum_comp]
        refine sum_interNum_eq_zero p Z (GlobalTheory.T.closed_subscheme_proj_over_mod_l _ _ _ _ V'.ar Z i p) hZ hg m
          (Finset.univ.filter fun j => (j : ℕ) < k) ⟨⟨0, by omega⟩, by simpa using Nat.lt_of_succ_le hk⟩ _
          (fun a j => LB.isLB_pull (L' _).isLB i) (fun j => CechPic.pull i (cls _ (L' (ν' j)).isLB)) fun a j => ?_
        rw [cls_pull (L' _).isLB i]
        by_cases hj : (j : ℕ) < k
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and, hj, if_true, hg']
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and, hj, if_false])
    rw [← hv, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have := hn ι L' Φ hΦ (Fin.cons (Pi.single i₀ 1 - Pi.single i₁ 1) fun j =>
      Pi.single (if (j : ℕ) < k then s a else ν' j) 1)
    have e₂ : lin (Pi.single i₀ 1 - Pi.single i₁ 1 : ι → ℝ) = X i₀ - X i₁ := by
      rw [← TrivFlag.lin_single, ← TrivFlag.lin_single]
      simp only [lin, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]
    rw [Fin.prod_univ_succ, Fin.cons_zero, e₂] at this
    simp only [Fin.cons_succ, TrivFlag.lin_single, hν'] at this
    rw [mul_left_comm, this]
    refine map_congr_rad num fun j => Fin.cases ?_ (fun j => ?_) j
    · have h₁ := neg_mem (add_mem (rt (L' i₀) (L' i₁).dual) (rd (L' i₁)))
      convert h₁ using 1
      simp only [Fin.cons_zero, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, Pi.single_apply, ite_smul, one_smul,
        zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      abel
    · simp [Pi.single_apply]

end Cover

section Syms

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F}
  (Y : FlagCpt Z e)

omit [NumberField E] [IsCMField E] in

theorem parOf_single (a : Sym E) {n : ℤ} (hn : n ≠ 0) : parOf (Finsupp.single a n) = a.2.1 := by
  unfold parOf
  have h : (Finsupp.single a n).support.Nonempty := ⟨a, by simp [hn]⟩
  rw [dif_pos h, Finset.mem_singleton.1 (Finsupp.support_single_subset h.choose_spec)]

theorem expo_single_eq {a a' : Sym E} (h : letterOf Dw a.2.2 = letterOf Dw a'.2.2) (n : ℤ) :
    expo Dw (Finsupp.single a n) = expo Dw (Finsupp.single a' n) := by
  funext x
  unfold expo
  rw [Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp), h]

theorem adlOf_single_eq {C : CxSt F} (hm : Mets Y C) {a a' : Sym E} (h : letterOf Dw a.2.2 = letterOf Dw a'.2.2)
    (h' : a.2.1 = a'.2.1) {n : ℤ} (hn : n ≠ 0) :
    adlOf Y hm (Finsupp.single a' n) =
      { adlOf Y hm (Finsupp.single a n) with lg := (adlOf Y hm (Finsupp.single a' n)).lg } := by
  have key (n n' : Letter Dw → ℤ) (h : n = n') (r r' : Option ℝ) (h' : r = r') (lg) :
      (⟨divOf Y n, 1, fun σ => hm r σ n, 0, lg⟩ : Adl C Y.Y) = ⟨divOf Y n', 1, fun σ => hm r' σ n', 0, lg⟩ := by
    rw [h, h']
  exact key _ _ (expo_single_eq h n).symm _ _ (by rw [parOf_single _ hn, parOf_single _ hn, h']) _

theorem abs_lgOf_single_sub_le {a a' : Sym E} (he : letterOf Dw a.2.2 = letterOf Dw a'.2.2) (n : ℤ)
    (v : HeightOneSpectrum (𝓞 F)) (ε : TrueGeo.Ext v) (y : AlgPt Y.Y) (B : ℝ)
    (h : ∀ (_ : Fact (resP v).Prime) (R : Type) [CommRing R] (φ : c.F →+* R) (x₀ : Sp R ⟶ Z.X) (f : EigFrame Z φ x₀)
      (ψ : R →+* ℂ_[resP v]),
      |lnStep Z.t (spMap ψ ≫ x₀) (fun τ i => spMap (dualMap ψ) ≫ f.v τ i) (resP v) (a.1 (resP v)) a.2.2 -
        lnStep Z.t (spMap ψ ≫ x₀) (fun τ i => spMap (dualMap ψ) ≫ f.v τ i) (resP v) (a'.1 (resP v)) a'.2.2| ≤ B) :
    |lgOf Y (Finsupp.single a n) v ε y - lgOf Y (Finsupp.single a' n) v ε y| ≤
      (|(n : ℝ)| * B / Real.log (resP v)) * (-Real.log (ε.w (resP v : AlgebraicClosure F))) := by
  have hw : 0 ≤ -Real.log (ε.w (resP v : AlgebraicClosure F)) :=
    neg_nonneg.2 (Real.log_nonpos (ε.w.nonneg _) ((ε.mem_O _).1 (natCast_mem _ _)))
  have hp : (resP v).Prime := CharP.char_prime_of_ne_zero (𝓞 F ⧸ v.asIdeal) (CharP.ringChar_ne_zero_of_finite _)
  have hs (a : Sym E) (Φ : Sym E → ℝ) : ((Finsupp.single a n).sum fun b n => (n : ℝ) * Φ b) = n * Φ a := by
    rw [Finsupp.sum_single_index (by simp)]
  have key (A k s s' : ℝ) (hk : 0 ≤ k) (h : |s - s'| ≤ B) :
      |A + k / Real.log (resP v) * (n * s) - (A + k / Real.log (resP v) * (n * s'))| ≤
        (|(n : ℝ)| * B / Real.log (resP v)) * k := by
    have hl := Real.log_natCast_nonneg (resP v)
    rw [add_sub_add_left_eq_sub, ← mul_sub, ← mul_sub, abs_mul, abs_mul, abs_of_nonneg (div_nonneg hk hl)]
    refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h (abs_nonneg _)) (div_nonneg hk hl)).trans_eq ?_
    ring
  simp only [lgOf, dif_pos hp]
  rewrite [expo_single_eq he, hs, hs]
  exact key _ _ _ _ hw (h _ _ _ _ _ _)

theorem exists_lnStep_bound (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) (p : ℕ) : ∃ B : ℝ, 0 ≤ B ∧
    ∀ (_ : Fact p.Prime) (R : Type) [CommRing R] (φ : c.F →+* R) (x₀ : Sp R ⟶ Z.X) (f : EigFrame Z φ x₀)
      (ψ : R →+* ℂ_[p]) (b : Bool) (st : ((E →+* ℂ) × ℕ) ⊕ ℕ) (z : Letter Dw), letterOf Dw st = some z →
      |lnStep Z.t (spMap ψ ≫ x₀) (fun τ i => spMap (dualMap ψ) ≫ f.v τ i) p b st -
        lnStep Z.t (spMap ψ ≫ x₀) (fun τ i => spMap (dualMap ψ) ≫ f.v τ i) p false (.inl (z.1, (z.2 : ℕ)))| ≤ B := by
  obtain ⟨N, -, hN⟩ := GlobalTheory.ConcatStep.abs_lnStep_bc_le Dw c
  refine ⟨|Real.log p / ((p : ℝ) - 1) + vDiff E p * Real.log p| + (|Real.log p * (1 / ((p : ℝ) - 1))| + |Real.log N|),
    by positivity, fun hp R _ φ x₀ f ψ b st z hz => ?_⟩
  have h0 := abs_nonneg (Real.log p / ((p : ℝ) - 1) + vDiff E p * Real.log p)
  have h1 := abs_nonneg (Real.log p * (1 / ((p : ℝ) - 1)))
  have h2 := abs_nonneg (Real.log N)
  rcases st with ⟨τ, k⟩ | k
  · have hk : k < Dw.mult τ := by
      by_contra hk
      simp [letterOf, hk] at hz
    obtain rfl : (⟨τ, ⟨k, hk⟩⟩ : Letter Dw) = z := Option.some.inj ((dif_pos hk).symm.trans hz)
    cases b
    · rw [sub_self, abs_zero]; positivity
    · refine ((LgDiff.abs_lnStep_sub_le HTBound.htBound Z p _ _ τ k).trans (le_abs_self _)).trans ?_
      linarith
  · obtain ⟨hk, rfl⟩ := List.getElem?_eq_some_iff.1 hz
    have h₃ := hN Z ⟨k, hk⟩ p hp inferInstance R φ x₀ f ψ
    have h₄ : (if p ∈ N.primeFactors then Real.log N else 0) ≤ |Real.log N| := by
      split_ifs
      · exact le_abs_self _
      · exact h2
    cases b
    · exact (h₃.trans h₄).trans (by linarith)
    · have h₅ : |lnStep Z.t (spMap ψ ≫ x₀) (fun τ i => spMap (dualMap ψ) ≫ f.v τ i) p true (.inr k) -
          lnStep Z.t (spMap ψ ≫ x₀) (fun τ i => spMap (dualMap ψ) ≫ f.v τ i) p false (.inr k)| ≤
            Real.log p * (1 / ((p : ℝ) - 1)) := by
        rw [abs_sub_comm]
        simp only [lnStep, dif_pos hk, lat]
        exact LgDiff.abs_log_grNorm_DR_HT_le HTBound.htBound Z p _ _ _
      refine (abs_sub_le _ _ _).trans ((add_le_add (h₅.trans (le_abs_self _)) (h₃.trans h₄)).trans ?_)
      linarith

theorem exists_lgOf_bound {a a' : Sym E} {z : Letter Dw} (h : letterOf Dw a.2.2 = some z) (h' : letterOf Dw a'.2.2 = some z)
    (n : ℤ) (S : Finset ℕ)
    (hS : ∀ q ∉ S, q.Prime → (a.1 q = a'.1 q ∧ (a.2.2 = a'.2.2 ∨ ¬ q ∣ (NumberField.discr E).natAbs))) :
    ∃ b : ℕ → ℝ, (∀ p, 0 ≤ b p) ∧ ∀ (v : HeightOneSpectrum (𝓞 F)) (ε : TrueGeo.Ext v) (y : AlgPt Y.Y),
      |lgOf Y (Finsupp.single a n) v ε y - lgOf Y (Finsupp.single a' n) v ε y| ≤
        (if resP v ∈ S then b (resP v) else 0) * (-Real.log (ε.w (resP v : AlgebraicClosure F))) := by
  choose B hB₀ hB using exists_lnStep_bound Z
  refine ⟨fun p => |(n : ℝ)| * (B p + B p) / Real.log p,
    fun p => div_nonneg (mul_nonneg (abs_nonneg _) (add_nonneg (hB₀ p) (hB₀ p))) (Real.log_natCast_nonneg _), fun v ε y => ?_⟩
  split_ifs with hv
  · refine abs_lgOf_single_sub_le Y (h.trans h'.symm) n v ε y _ fun hp R _ φ x₀ f ψ => ?_
    refine (abs_sub_le _ _ _).trans (add_le_add (hB _ hp R φ x₀ f ψ _ _ z h) ?_)
    rw [abs_sub_comm]
    exact hB _ hp R φ x₀ f ψ _ _ z h'
  · refine (abs_lgOf_single_sub_le Y (h.trans h'.symm) n v ε y 0 fun hp R _ φ x₀ f ψ => ?_).trans_eq (by simp)
    obtain ⟨e₁, e₂ | e₂⟩ := hS _ hv hp.out
    · rw [e₁, e₂, sub_self, abs_zero]
    · have key (b : Bool) (st : ((E →+* ℂ) × ℕ) ⊕ ℕ) (hz : letterOf Dw st = some z) :
          lnStep Z.t (spMap ψ ≫ x₀) (fun τ i => spMap (dualMap ψ) ≫ f.v τ i) (resP v) b st =
            lnStep Z.t (spMap ψ ≫ x₀) (fun τ i => spMap (dualMap ψ) ≫ f.v τ i) (resP v) b (.inl (z.1, (z.2 : ℕ))) := by
        rcases st with ⟨τ, k⟩ | k
        · have hk : k < Dw.mult τ := by
            by_contra hk
            simp [letterOf, hk] at hz
          obtain rfl : (⟨τ, ⟨k, hk⟩⟩ : Letter Dw) = z := Option.some.inj ((dif_pos hk).symm.trans hz)
          rfl
        · exact EigWhole.lnStep_frame _ _ _ hp.out (EigWhole.norm_p_lt_one_padicComplex _ _) e₂ _ k z hz
      rw [key _ _ h, key _ _ h', e₁, sub_self, abs_zero]

end Syms

section Comp

open Formalism.DegreeFormula Formalism.BasicNotions.DV GlobalTheory.VdmRec GlobalTheory.Published

def Good {E : Type} [Field E] (R : ℝ) (w : Sym E →₀ ℤ) : Prop :=
  ∀ a ∈ w.support, {q | a.1 q = true}.Finite ∧ a.2.1 = some R

variable {D : D7} {O : Setup D}

theorem kill (h2 : Hypotheses2) (hH : HypothesesH) (hRA : RegularAlteration) (hSW : ScholzeWeinsteinB) (hO : O.Core)
    (R : ℝ) (hR : 2 ≤ R) (c : O.s.Comp) {ι : Type} [Fintype ι] (w : ι → Sym D.host.E →₀ ℤ) (hw : ∀ i, Good R (w i))
    (T S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ∈ T) (s : Fin (D.R.f * O.N) ⊕ Fin (D.R.f * O.N) → ι)
    (hs : ∀ l, w (s l) = wholeSym (ArIn.ind T) (some R) l) (i₀ i₁ : ι) {a a' : Sym D.host.E} {n : ℤ} (hn : n ≠ 0)
    (h₀ : w i₀ = Finsupp.single a n) (h₁ : w i₁ = Finsupp.single a' n) {z : Letter O.S.Dw}
    (h : letterOf O.S.Dw a.2.2 = some z) (h' : letterOf O.S.Dw a'.2.2 = some z)
    (hq : ∀ q ∉ S, q.Prime → (a.1 q = a'.1 q ∧ (a.2.2 = a'.2.2 ∨ ¬ q ∣ (NumberField.discr D.host.E).natAbs)))
    (G : MvPolynomial ι ℝ) :
    cNum O c (rename w ((∑ l, X (s l) ^ 2) * ((X i₀ - X i₁) * G))) = 0 := by
  have hfl (p : ℕ) (hp : p ∈ S) := GlobalTheory.T.flag_at_whole_symbol_reindexed h2 hH hRA hSW D O hO T R hR p (hS p hp).1 c
  obtain ⟨x, P, hW⟩ := hO
  obtain ⟨M, L, m, Ψ, hI, hΨ, hnum⟩ := (GlobalTheory.ArTopTrue.arTop_true h2.p4 hH.deg HTBound.htBound D _ _ _ _ _ O.s x O.Φ c R hR).2
    ι w hw
  obtain ⟨b, hb, hlg⟩ := exists_lgOf_bound (O.Φ.C c) h h' n S hq
  rw [cNum, hW.hm_eq, ← O.dim_eq c]
  rw [hW.hm_eq] at hfl
  refine (numL_rename w _ _ Ψ _ hΨ.2 hnum _).trans (div_eq_zero_iff.2 (.inl ?_))
  refine powerSum_mul_vertical h2 M _ L m Ψ hI hΨ S b (fun p hp => ⟨(hS p hp).1, hb p⟩) s (fun p hp => ?_) i₀ i₁ ?_ ?_ 2
    (by norm_num) G
  · obtain ⟨e, he⟩ := hfl p hp
    have eT : Function.update (ArIn.ind T) p true = ArIn.ind T := by
      rw [Function.update_eq_self_iff]
      simp [ArIn.ind, (hS p hp).2]
    refine ⟨_, e, ?_⟩
    simp only [hs]
    rwa [eT] at he
  · beta_reduce
    rw [h₀, h₁]
    refine adlOf_single_eq _ _ (h.trans h'.symm) ?_ hn
    rw [(hw i₀ a (by simp [h₀, hn])).2, (hw i₁ a' (by simp [h₁, hn])).2]
  · beta_reduce
    rw [h₀, h₁]
    exact hlg

theorem neg_cancel (h2 : Hypotheses2) (hH : HypothesesH) (hO : O.Core)
    (R : ℝ) (hR : 2 ≤ R) (c : O.s.Comp) {ι : Type} [Fintype ι] (w : ι → Sym D.host.E →₀ ℤ) (hw : ∀ i, Good R (w i))
    (i₀ i₁ : ι) (hne : i₀ ≠ i₁) (h : w i₁ = -w i₀) (G : MvPolynomial ι ℝ) :
    cNum O c (rename w ((X i₀ + X i₁) * G)) = 0 := by
  obtain ⟨x, P, hW⟩ := hO
  obtain ⟨M, L, m, Ψ, hI, hΨ, hnum⟩ := (GlobalTheory.ArTopTrue.arTop_true h2.p4 hH.deg HTBound.htBound D _ _ _ _ _ O.s x O.Φ c R hR).2
    ι w hw
  haveI := M.ar.isIntegral
  have hsum : ∀ n : ι → ℤ, (adlOf (O.Φ.C c) (metsOf x O.Φ c) (∑ i, n i • w i)).arTop =
      Ψ (lin (fun i => (n i : ℝ)) ^ ((O.Φ.C c).Y.dim + 1)) / ((m : ℕ) : ℝ) ^ ((O.Φ.C c).Y.dim + 1) /
        (Module.finrank ℚ D.what₂.LL : ℝ) := by
    intro n
    have hI' := GlobalTheory.T.adelic_divisor_induced_linear D _ _ _ _ _ O.s x O.Φ c R M ι w L m (fun i a ha => (hw i a ha).2) hI n
    have ht : (adlOf (O.Φ.C c) (metsOf x O.Φ c) (∑ i, n i • w i)).IsArTop
        (Ψ (lin (fun i => (n i : ℝ)) ^ ((O.Φ.C c).Y.dim + 1)) / ((m : ℕ) : ℝ) ^ ((O.Φ.C c).Y.dim + 1) /
        (Module.finrank ℚ D.what₂.LL : ℝ)) := by
      refine ⟨M, _, m, 0, _, hI', hΨ.1 n, ?_⟩
      have hn : (adlOf (O.Φ.C c) (metsOf x O.Φ c) (∑ i, n i • w i)).n = 1 := rfl
      simp [hn]
    have hex : ∃ t, (adlOf (O.Φ.C c) (metsOf x O.Φ c) (∑ i, n i • w i)).IsArTop t := ⟨_, ht⟩
    rw [Adl.arTop, dif_pos hex]
    exact GlobalTheory.TrueGeo.ArUniq.isArTop_unique h2.p4 hH.deg _ _ _ _ _ _ hex.choose_spec ht
  let σ : MvPolynomial ι ℝ →ₐ[ℝ] MvPolynomial ι ℝ := aeval fun i => if i = i₁ then -X i₀ else X i
  have hσ (n : ι → ℤ) : σ (lin fun i => (n i : ℝ)) =
      lin fun i => ((n - n i₁ • Pi.single i₁ 1 - n i₁ • Pi.single i₀ 1 : ι → ℤ) i : ℝ) := by
    have e (i : ι) : σ (C (n i : ℝ) * X i) = C (n i : ℝ) * X i -
        (if i = i₁ then C (n i₁ : ℝ) * X i₁ + C (n i₁ : ℝ) * X i₀ else 0) := by
      simp only [σ, map_mul, aeval_X, algHom_C, algebraMap_eq]
      split_ifs with hi
      · subst hi; ring
      · ring
    simp only [lin, map_sum, e, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, Pi.sub_apply,
      Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Int.cast_sub, Int.cast_ite, Int.cast_zero,
      map_sub, sub_mul, apply_ite C, ite_mul, map_zero, zero_mul]
    ring
  have hw' (n : ι → ℤ) : ∑ i, (n - n i₁ • Pi.single i₁ 1 - n i₁ • Pi.single i₀ 1 : ι → ℤ) i • w i = ∑ i, n i • w i := by
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, sub_smul,
      Finset.sum_sub_distrib, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true, h, smul_neg]
    abel
  have hnum' := GlobalTheory.T.polarization_of_homogeneous ι (Sym D.host.E →₀ ℤ) w (fun v => (adlOf (O.Φ.C c) (metsOf x O.Φ c) v).arTop)
    ((O.Φ.C c).Y.dim + 1) (Ψ ∘ₗ σ.toLinearMap) (1 / ((((m : ℕ) : ℝ)) ^ ((O.Φ.C c).Y.dim + 1) * (Module.finrank ℚ D.what₂.LL : ℝ)))
    (fun n => by
      rw [← hw', hsum, LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_pow σ, hσ]; ring)
  rw [cNum, hW.hm_eq, ← O.dim_eq c]
  refine (numL_rename w _ _ (Ψ ∘ₗ σ.toLinearMap)
    ((((m : ℕ) : ℝ)) ^ ((O.Φ.C c).Y.dim + 1) * (Module.finrank ℚ D.what₂.LL : ℝ)) (fun Q e he hQ => ?_)
    (fun μ hμ => (hnum' μ hμ).trans (by ring)) _).trans (div_eq_zero_iff.2 (.inl ?_))
  · refine hΨ.2 _ e he ?_
    have := hQ.aeval (fun i => if i = i₁ then -X i₀ else X i : ι → MvPolynomial ι ℝ) (n := 1) fun i => by
      split_ifs
      · exact (isHomogeneous_X _ _).neg
      · exact isHomogeneous_X _ _
    rwa [one_mul] at this
  · rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul, map_add]
    simp [σ, hne]

end Comp

section Alg

theorem exists_monomial_eq_prod' {K α : Type} [CommSemiring K] (u : α →₀ ℕ) :
    ∃ (n : ℕ) (ν : Fin n → α), n = u.degree ∧ (monomial u 1 : MvPolynomial α K) = ∏ j, X (ν j) := by
  induction u using Finsupp.induction_linear with
  | zero => exact ⟨0, Fin.elim0, by simp, by simp⟩
  | add u v hu hv =>
    obtain ⟨n, ν, e, h⟩ := hu
    obtain ⟨n', ν', e', h'⟩ := hv
    refine ⟨n + n', Fin.append ν ν', by rw [map_add, e, e'], ?_⟩
    rw [Fin.prod_univ_add]
    simp only [Fin.append_left, Fin.append_right, ← h, ← h', monomial_mul, mul_one]
  | single a n => exact ⟨n, fun _ => a, by simp, by simp [X_pow_eq_monomial]⟩

theorem numL_X_mul_prod {A : Type} (num : Multiset A → ℝ) {n : ℕ} (a : A) (b : Fin n → A) :
    numL num (n + 1) (X a * ∏ j, X (b j)) = num (a ::ₘ Finset.univ.val.map b) := by
  have e : (X a * ∏ j, X (b j) : MvPolynomial A ℝ) =
      ((Finsupp.toMultiset (Multiset.toFinsupp (a ::ₘ Finset.univ.val.map b))).map X).prod := by
    rw [Multiset.toFinsupp_toMultiset, Multiset.map_cons, Multiset.prod_cons, Multiset.map_map]
    rfl
  rw [e, NumLRename.prod_map_X_toMultiset, NumLRename.numL_monomial, if_pos, one_mul, Multiset.toFinsupp_toMultiset]
  have := Finsupp.card_toMultiset (Multiset.toFinsupp (a ::ₘ Finset.univ.val.map b))
  rw [Multiset.toFinsupp_toMultiset] at this
  refine Eq.trans (this.symm) ?_
  simp

theorem map_rename_sub {α β : Type} (f g : α → β) (φ : MvPolynomial β ℝ →ₗ[ℝ] ℝ)
    (h : ∀ v G, φ ((X (f v) - X (g v)) * G) = 0) (P : MvPolynomial α ℝ) (G : MvPolynomial β ℝ) :
    φ ((rename f P - rename g P) * G) = 0 := by
  induction P using MvPolynomial.induction_on generalizing G with
  | C a => simp
  | add P Q hP hQ => rw [map_add, map_add, add_sub_add_comm, add_mul, map_add, hP, hQ, add_zero]
  | mul_X P v hP =>
    have e : (rename f (P * X v) - rename g (P * X v)) * G =
        (rename f P - rename g P) * (X (f v) * G) + (X (f v) - X (g v)) * (rename g P * G) := by
      simp only [map_mul, rename_X]; ring
    rw [e, map_add, hP, h, add_zero]

open Formalism.DegreeFormula Formalism.BasicNotions.DV GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison in

theorem ck_add_ck_eq_zero {D : D7} {p : ℕ} [Fact p.Prime] {N : ℕ} {rk : Emb D p → ℕ} (M : DV.Mdl D p N rk)
    (hL : LocalW M) (hc : Comm M) {m : ℕ} (hm : m + 2 = dimFl D.what₂.Tau N + 1) (Q : MvPolynomial M.Z.LB ℚ)
    (hQ : Q.IsHomogeneous m) (V : M.Z.VDiv) (a : M.Z.Ch) (e : evQ _ Q = M.Z.cD V * a) :
    ck M.lieW 2 (evQ _ Q) + ck M.omW 2 (evQ _ Q) = 0 := by
  have h := hL 2 (by norm_num) m hm Q hQ
  have h0 : chDiv M.lieW.x (2 - 1) (evQ _ Q) = 0 := by
    rw [chDiv, e, mul_left_comm, hc, M.Z.cD_divP, zero_mul, map_zero, Rat.cast_zero, zero_div]
  rw [h0, mul_zero, chk, chk, ← add_div, div_eq_zero_iff] at h
  rcases h with h | h
  · exact_mod_cast h
  · norm_num at h

theorem pair_abstract {Comp A ι La : Type} [Fintype Comp] [Fintype La] (num : Comp → Multiset A → ℝ) (n : ℕ) (w : ι → A)
    (i₀ i₁ : ι) (t : ℝ) (Z : La → DV.ITh) (V : ∀ la, (Z la).VDiv) (ev : ∀ la, ι → (Z la).Ch) (wt cv : La → ℝ)
    (h : ∀ ν : Fin n → ι, ∑ c, (num c (w i₀ ::ₘ Finset.univ.val.map fun j => w (ν j)) -
      num c (w i₁ ::ₘ Finset.univ.val.map fun j => w (ν j))) =
        t * ∑ la, wt la * ((((Z la).capDeg (V la) (∏ j, ev la (ν j)) : ℚ) : ℝ) / cv la))
    (Q : MvPolynomial ι ℚ) (hQ : Q.IsHomogeneous n) :
    ∑ c, numL (num c) (n + 1) (rename w ((X i₀ - X i₁) * map (algebraMap ℚ ℝ) Q)) =
      t * ∑ la, wt la * ((((Z la).capDeg (V la) (aeval (ev la) Q) : ℚ) : ℝ) / cv la) := by
  have key (d : ι →₀ ℕ) (hd : d.degree = n) (q : ℚ) :
      ∑ c, numL (num c) (n + 1) (rename w ((X i₀ - X i₁) * map (algebraMap ℚ ℝ) (monomial d q))) =
      t * ∑ la, wt la * ((((Z la).capDeg (V la) (aeval (ev la) (monomial d q)) : ℚ) : ℝ) / cv la) := by
    obtain ⟨k, ν, hn, hν⟩ := exists_monomial_eq_prod' (K := ℚ) d
    rw [hd] at hn
    subst hn
    have e : (monomial d q : MvPolynomial ι ℚ) = C q * ∏ j, X (ν j) := by rw [← hν, C_mul_monomial, mul_one]
    have e₁ (c : Comp) : numL (num c) (k + 1) (rename w ((X i₀ - X i₁) * map (algebraMap ℚ ℝ) (monomial d q))) = q *
        (num c (w i₀ ::ₘ Finset.univ.val.map fun j => w (ν j)) - num c (w i₁ ::ₘ Finset.univ.val.map fun j => w (ν j))) := by
      rw [e, map_mul (map (algebraMap ℚ ℝ)), map_C, mul_left_comm, C_mul', map_smul, map_smul, smul_eq_mul]
      simp only [map_mul, map_sub, map_prod, map_X, rename_X, sub_mul, numL_X_mul_prod]
      rfl
    rw [Finset.sum_congr rfl fun c _ => e₁ c, ← Finset.mul_sum, h, mul_left_comm, Finset.mul_sum]
    refine congrArg _ (Finset.sum_congr rfl fun la _ => ?_)
    rw [e, C_mul', map_smul, map_smul, map_prod (aeval (R := ℚ) (ev la)), smul_eq_mul, Rat.cast_mul]
    simp only [aeval_X]
    ring
  conv_lhs => rw [Q.as_sum]
  conv_rhs => rw [Q.as_sum]
  simp only [map_sum, Finset.mul_sum, Rat.cast_sum, Finset.sum_div]
  rw [Finset.sum_comm]
  refine Eq.trans ?_ Finset.sum_comm
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [key d (by rw [Finsupp.degree_eq_weight_one]; exact hQ (mem_support_iff.1 hd)), Finset.mul_sum]

end Alg

section Pair

open Formalism.DegreeFormula Formalism.BasicNotions.DV GlobalTheory.VdmRec GlobalTheory.Published GlobalTheory.PairTerm GlobalTheory.ShFam.Pad.LieGen GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison Formalism.L2.Geo

variable {D : D7} (O : Setup D)

theorem pair_poly (hP : PairSt) (hO : O.Core) (p : ℕ) [Fact p.Prime]
    (W : Formalism.L2.Geo.PlL D p → ValuationSubring ℂ) (hW : ∀ la, (p : ℂ) ∈ (W la).nonunits)
    (hWL : ∀ la (x : D.what₂.LL), D.what₂.embLL x ∈ W la ↔ IsDedekindDomain.HeightOneSpectrum.valuation D.what₂.LL la.1 x ≤ 1)
    (z : ∀ la, AdmAt O.S O.κ (Fact.out : p.Prime) (hW la)) (Sx : Finset ℕ) (R : ℝ) (hR : 2 ≤ R)
    {ι : Type} (u : ι → Bool × Ln O.S.Dw) (l : Ln O.S.Dw) (i₀ i₁ : ι) (h₀ : u i₀ = (false, l)) (h₁ : u i₁ = (true, l))
    (Q : MvPolynomial ι ℚ) (hQ : Q.IsHomogeneous (dimFl D.what₂.Tau O.N)) :
    ∑ c, cNum O c (rename (fun i => lnSym (Function.update (ArIn.ind Sx) p (u i).1) (some R) (u i).2)
        ((X i₀ - X i₁) * map (algebraMap ℚ ℝ) Q)) =
      Real.log p * (letI := Formalism.L2.Geo.finPl D p; ∑ la, Formalism.L2.Geo.wtL D p la *
        ((((ithOf Fact.out (hW la) (z la).Z (dimFl D.what₂.Tau O.N)).capDeg
          (vdiv Fact.out (hW la) _ _ _ (lnId (z la) Fact.out (hW la) l))
          (aeval (fun i => (ithOf Fact.out (hW la) (z la).Z (dimFl D.what₂.Tau O.N)).c1 (lnLB (z la) (u i).1 (u i).2)) Q) : ℚ) : ℝ) /
            (cov (z la) : ℝ))) := by
  letI := Formalism.L2.Geo.finPl D p
  refine pair_abstract (fun c => (arIn O.s O.Φ O.met.hm).num c) _ _ i₀ i₁ _
    (fun la => ithOf Fact.out (hW la) (z la).Z (dimFl D.what₂.Tau O.N)) _ _ _ _ (fun ν => ?_) Q hQ
  have h := hP D O hO p W hW hWL z Sx R hR l fun j => u (ν j)
  simp only [h₀, h₁]
  exact h

end Pair

section Lines

open Formalism.DegreeFormula Formalism.BasicNotions.DV GlobalTheory.VdmRec GlobalTheory.Published GlobalTheory.PairTerm GlobalTheory.ShFam.Pad.LieGen GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison Formalism.L2.Geo

variable {D : D7} (O : Setup D)

abbrev Vr : Type := Rt D.what₂.Tau O.N ⊕ (Fin (D.R.f * O.N) ⊕ Fin (D.R.f * O.N))

def ln : Vr O → Ln O.S.Dw
  | .inl r => (decide ¬ (r.2 : ℕ) < O.j, ⟨.inl ((rootLetter O.S r).1, (rootLetter O.S r).2), by
      rw [AdmTest.letterOf_inl]; rfl⟩)
  | .inr (.inl k) => (false, ⟨.inr k, by rw [letterOf_whole]; rfl⟩)
  | .inr (.inr k) => (true, ⟨.inr k.rev, by rw [letterOf_whole]; rfl⟩)

def fa (a : ℕ → Bool) (R : ℝ) (v : Vr O) : Sym D.host.E →₀ ℤ := lnSym a (some R) (ln O v)

theorem lnSym_eq (a : ℕ → Bool) (R : Option ℝ) (l : Ln O.S.Dw) :
    lnSym a R l = Finsupp.single (a, R, l.2.1) (if l.1 then -1 else 1) := by
  obtain ⟨_ | _, st⟩ := l <;> rfl

theorem rootLetter_lt {r : Rt D.what₂.Tau O.N} (h : (r.2 : ℕ) < O.j) :
    ((rootLetter O.S r).1, ((rootLetter O.S r).2 : ℕ)) = (tauEmb D r.1, (r.2 : ℕ)) := by
  unfold rootLetter
  rw [dif_pos h]

theorem rootLetter_ge {r : Rt D.what₂.Tau O.N} (h : ¬ (r.2 : ℕ) < O.j) :
    ((rootLetter O.S r).1, ((rootLetter O.S r).2 : ℕ)) = (conjEmb (tauEmb D r.1), O.S.Dw.p + O.S.Dw.q - 1 - (r.2 : ℕ)) := by
  have hq := O.S.rank_eq
  unfold rootLetter
  rw [dif_neg h]
  simp only [Prod.mk.injEq, true_and]
  omega

theorem fa_inl (a : ℕ → Bool) (R : ℝ) (r : Rt D.what₂.Tau O.N) :
    fa O a R (.inl r) = rootSym O.S.Dw a (some R) (tauEmb D r.1) r.2 := by
  have hp := O.S.p_eq
  rw [fa, lnSym_eq, rootSym]
  by_cases h : (r.2 : ℕ) < O.j
  · rw [if_pos (show (r.2 : ℕ) < O.S.Dw.p by omega)]
    simp only [ln, rootLetter_lt O h, h]
    rfl
  · rw [if_neg (show ¬ (r.2 : ℕ) < O.S.Dw.p by omega)]
    simp only [ln, rootLetter_ge O h, h]
    rfl

theorem fa_inr (a : ℕ → Bool) (R : ℝ) (l : Fin (D.R.f * O.N) ⊕ Fin (D.R.f * O.N)) :
    fa O a R (.inr l) = wholeSym a (some R) l := by
  rcases l with k | k <;> rfl

theorem good_fa (T : Finset ℕ) (R : ℝ) (v : Vr O) : Good R (fa O (ArIn.ind T) R v) := by
  intro a ha
  rw [fa, lnSym_eq] at ha
  obtain rfl := Finset.mem_singleton.1 (Finsupp.support_single_subset ha)
  exact ⟨by simpa [ArIn.ind] using T.finite_toSet, rfl⟩

def dl (K : Type) [CommRing K] : MvPolynomial (Vr O) K :=
  ∑ r : Rt D.what₂.Tau O.N, (if (r.2 : ℕ) < O.j then -X (.inl r) else X (.inl r)) - ∑ k, X (.inr (.inr k))

theorem dl_isHomogeneous (K : Type) [CommRing K] : (dl O K).IsHomogeneous 1 :=
  (IsHomogeneous.sum _ _ _ fun r _ => by
    split_ifs
    · exact (isHomogeneous_X _ _).neg
    · exact isHomogeneous_X _ _).sub (IsHomogeneous.sum _ _ _ fun _ _ => isHomogeneous_X _ _)

theorem map_dl : map (algebraMap ℚ ℝ) (dl O ℚ) = dl O ℝ := by
  simp only [dl, map_sub, map_sum, apply_ite (map (algebraMap ℚ ℝ)), map_neg, map_X]

section Model

variable {p : ℕ} [Fact p.Prime] {W : ValuationSubring ℂ} {hW : (p : ℂ) ∈ W.nonunits}
  (z : AdmAt O.S O.κ (Fact.out : p.Prime) hW) (jc : KW p →+* ℂ)

def lb (x : Bool × Vr O) : (mdlOf z jc).Z.LB := lnLB z x.1 (ln O x.2)

theorem lb_root (r : Rt D.what₂.Tau O.N) : lb O z jc (false, .inl r) = rootOf z jc (false, r) := by
  have hp := O.S.p_eq
  unfold lb rootOf admitted.rootLB
  by_cases h : (r.2 : ℕ) < O.j
  · rw [if_pos (show (r.2 : ℕ) < O.S.Dw.p by omega), ← rootLetter_lt O h]
    have e : ln O (.inl r) = (false, (ln O (.inl r)).2) := Prod.ext (by simp [ln, h]) rfl
    exact (congrArg (lnLB z false) e).trans (lnLB_false _ _ _)
  · rw [if_neg (show ¬ (r.2 : ℕ) < O.S.Dw.p by omega), ← rootLetter_ge O h]
    have e : ln O (.inl r) = (true, (ln O (.inl r)).2) := Prod.ext (by simpa [ln] using h) rfl
    exact (congrArg (lnLB z false) e).trans (lnLB_true _ _ _)

theorem lb_lie (k : Fin (D.R.f * O.N)) : lb O z jc (false, .inr (.inl k)) = (mdlOf z jc).lieW.x k ∧
    lb O z jc (true, .inr (.inl k)) = (mdlOf z jc).lieW.x' k :=
  ⟨(lnLB_false _ _ _).trans (mdlOf_lieW z jc k).1.symm, (lnLB_false _ _ _).trans (mdlOf_lieW z jc k).2.symm⟩

theorem lb_om (k : Fin (D.R.f * O.N)) : lb O z jc (false, .inr (.inr k)) = (mdlOf z jc).omW.x k ∧
    lb O z jc (true, .inr (.inr k)) = (mdlOf z jc).omW.x' k :=
  ⟨(lnLB_true _ _ _).trans (mdlOf_omW z jc k).1.symm, (lnLB_true _ _ _).trans (mdlOf_omW z jc k).2.symm⟩

def dv (l : Fin (D.R.f * O.N) ⊕ Fin (D.R.f * O.N)) : (mdlOf z jc).Z.VDiv :=
  vdiv Fact.out hW (dimFl D.what₂.Tau O.N) _ _ (lnId z Fact.out hW (ln O (.inr l)))

theorem dv_lie (k : Fin (D.R.f * O.N)) : dv O z jc (.inl k) = (mdlOf z jc).lieW.Dv k :=
  vdiv_lnId_false z _ hW _ _ (letterOf_whole O.S k)

theorem dv_om (k : Fin (D.R.f * O.N)) : dv O z jc (.inr k) = (mdlOf z jc).omW.Dv k :=
  (vdiv_lnId_true z _ hW _ _ (letterOf_whole O.S k.rev)).trans (mdlOf_omW_Dv z jc k).symm

theorem exists_dl_eq : ∃ V : (mdlOf z jc).Z.VDiv,
    aeval (fun v => (mdlOf z jc).Z.c1 (lb O z jc (false, v))) (dl O ℚ) = (mdlOf z jc).Z.cD V := by
  obtain ⟨e, V, h⟩ := lieW_gen D O.A O.N O.j O.S O.κ p Fact.out W hW z jc
  obtain ⟨e', h'⟩ := (mdlOf z jc).omW_dual
  refine ⟨∑ k, V k, ?_⟩
  simp only [dl, map_sub, map_sum, apply_ite (aeval fun v => (mdlOf z jc).Z.c1 (lb O z jc (false, v))), map_neg, aeval_X,
    lb_root, fun k => (lb_om O z jc k).1, h']
  rw [e'.sum_comp fun k => -(mdlOf z jc).Z.c1 ((mdlOf z jc).lieW.x k), ← e.sum_comp, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [h k]
  split_ifs <;> simp

theorem sum_capDeg_eq_zero (hL : LocalW (mdlOf z jc)) {m : ℕ} (hm : 1 + m + 2 = dimFl D.what₂.Tau O.N + 1)
    (G : MvPolynomial (Vr O) ℚ) (hG : G.IsHomogeneous m) :
    ∑ l, (mdlOf z jc).Z.capDeg (dv O z jc l) (aeval (fun x => (mdlOf z jc).Z.c1 (lb O z jc x))
      ((X (false, .inr l) + X (true, .inr l)) * rename (Prod.mk false) (dl O ℚ * G) : MvPolynomial (Bool × Vr O) ℚ)) = 0 := by
  obtain ⟨V, hV⟩ := exists_dl_eq O z jc
  have e : evQ _ (rename (fun v => lb O z jc (false, v)) (dl O ℚ * G)) =
      aeval (fun v => (mdlOf z jc).Z.c1 (lb O z jc (false, v))) (dl O ℚ * G) := by
    rw [evQ, aeval_rename]; rfl
  have h := ck_add_ck_eq_zero (mdlOf z jc) hL
    (GlobalTheory.VertCommAdm.comm_mdlOf D O.A O.N O.j O.S O.κ p Fact.out W hW z jc) hm
    (rename (fun v => lb O z jc (false, v)) (dl O ℚ * G)) ((dl_isHomogeneous O ℚ).mul hG).rename_isHomogeneous V _
    (by rw [e, map_mul, hV])
  rw [e] at h
  rw [← h, Fintype.sum_sum_type, ck, ck]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun k _ => ?_) (Finset.sum_congr rfl fun k _ => ?_)
  · rw [dv_lie, map_mul, aeval_rename, map_add, aeval_X, aeval_X, (lb_lie O z jc k).1, (lb_lie O z jc k).2]
    simp [Gk, Finset.sum_range_succ, add_comm, Function.comp_def]
  · rw [dv_om, map_mul, aeval_rename, map_add, aeval_X, aeval_X, (lb_om O z jc k).1, (lb_om O z jc k).2]
    simp [Gk, Finset.sum_range_succ, add_comm, Function.comp_def]

end Model

end Lines

section Main

open Formalism.DegreeFormula Formalism.BasicNotions.DV GlobalTheory.VdmRec GlobalTheory.Published GlobalTheory.PairTerm GlobalTheory.ShFam.Pad.LieGen GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison Formalism.L2.Geo
open GlobalTheory.FlagPoly GlobalTheory.CovTestDR

variable {D : D7} (O : Setup D)

def pw : MvPolynomial (Vr O) ℝ := ∑ l, X (.inr l) ^ 2

def fb (S : Finset ℕ) (p : ℕ) (R : ℝ) (x : Bool × Vr O) : Sym D.host.E →₀ ℤ :=
  fa O (Function.update (ArIn.ind S) p x.1) R x.2

variable {O}

theorem dr_sub_ht (hX : HypothesesXH) (h2 : Hypotheses2) (hH : HypothesesH) (hRA : RegularAlteration) (hSW : ScholzeWeinsteinB)
    (hO : O.Core) (R : ℝ) (hR : 2 ≤ R) (S : Finset ℕ) (p : ℕ) (hp : p.Prime) (G : MvPolynomial (Vr O) ℝ) :
    ∑ c, cNum O c (rename (fb O S p R) ((rename (Prod.mk false) (pw O) - rename (Prod.mk true) (pw O)) *
      rename (Prod.mk false) (dl O ℝ * G))) = 0 := by
  induction G using MvPolynomial.induction_on' with
  | add P Q hP hQ => simp only [mul_add, map_add, Finset.sum_add_distrib, hP, hQ, add_zero]
  | monomial u a =>
    have e₁ : (monomial u a : MvPolynomial (Vr O) ℝ) = a • map (algebraMap ℚ ℝ) (monomial u 1) := by
      rw [map_monomial, map_one, smul_monomial, smul_eq_mul, mul_one]
    simp only [e₁, mul_smul_comm, map_smul, ← Finset.smul_sum]
    refine smul_eq_zero_of_right _ ?_
    have hu : (monomial u 1 : MvPolynomial (Vr O) ℚ).IsHomogeneous u.degree := isHomogeneous_monomial _ rfl
    generalize (monomial u 1 : MvPolynomial (Vr O) ℚ) = G at hu
    generalize u.degree = m at hu
    have e₂ : (rename (Prod.mk false) (pw O) - rename (Prod.mk true) (pw O)) *
        rename (Prod.mk false) (dl O ℝ * map (algebraMap ℚ ℝ) G) = ∑ l, (X (false, .inr l) - X (true, .inr l)) *
          map (algebraMap ℚ ℝ) ((X (false, .inr l) + X (true, .inr l)) * rename (Prod.mk false) (dl O ℚ * G)) := by
      simp only [pw, map_sum, map_pow, rename_X, map_mul, map_add, map_X, map_rename, map_dl, ← Finset.sum_sub_distrib,
        Finset.sum_mul]
      exact Finset.sum_congr rfl fun l _ => by ring
    have hQ (l : Fin (D.R.f * O.N) ⊕ Fin (D.R.f * O.N)) : ((X (false, .inr l) + X (true, .inr l)) *
        rename (Prod.mk false) (dl O ℚ * G) : MvPolynomial (Bool × Vr O) ℚ).IsHomogeneous (1 + (1 + m)) :=
      ((isHomogeneous_X _ _).add (isHomogeneous_X _ _)).mul ((dl_isHomogeneous O ℚ).mul hu).rename_isHomogeneous
    simp only [e₂, map_sum]
    by_cases hm : 1 + (1 + m) = dimFl D.what₂.Tau O.N
    swap
    · refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun l _ => numL_homog _ _ (1 + (1 + (1 + m))) (by omega) _ ?_
      exact (((isHomogeneous_X _ _).sub (isHomogeneous_X _ _)).mul ((hQ l).map _)).rename_isHomogeneous
    haveI := Fact.mk hp
    letI := Formalism.L2.Geo.finPl D p
    choose jc hjc hW using fun la => AdmTest.exists_placeW_nonunit D p la
    choose z _ using fun la => admEx O.S O.κ p hp _ (hW la) 3 (one_add_lt_three hp)
    have hL (la) : LocalW (mdlOf (z la) (jc la)) := GlobalTheory.T.local_of_has_chain_at_prime D _ _ _ _ _ p Fact.out _ (hW la) (z la) (jc la)
      (GlobalTheory.T.chainW_of_alteration_prismatic hX h2 hH hRA hSW hX.y.perfd D O hO p _ (hW la) (jc la) (AdmTest.placeW_spec (hjc la)).2 (z la))
    have key (l : Fin (D.R.f * O.N) ⊕ Fin (D.R.f * O.N)) := pair_poly O (GlobalTheory.T.pair_statement_of_height_alteration h2 hH hRA) hO p _ hW
      (fun la => (AdmTest.placeW_spec (hjc la)).1) z S R hR (fun x : Bool × Vr O => (x.1, ln O x.2)) (ln O (.inr l))
      (false, .inr l) (true, .inr l) rfl rfl _ (hm ▸ hQ l)
    rw [Finset.sum_comm]
    refine (Finset.sum_congr rfl fun l _ => key l).trans ?_
    rw [← Finset.mul_sum, Finset.sum_comm]
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun la _ => ?_)
    rw [← Finset.mul_sum, ← Finset.sum_div, ← Rat.cast_sum]
    have h0 := sum_capDeg_eq_zero O (z la) (jc la) (hL la) (by omega) G hu
    exact mul_eq_zero_of_right _ (div_eq_zero_iff.2 (.inl (Rat.cast_eq_zero.2 h0)))

theorem update_false {S : Finset ℕ} {q : ℕ} (h : q ∉ S) : Function.update (ArIn.ind S) q false = ArIn.ind S := by
  rw [Function.update_eq_self_iff]
  simp [ArIn.ind, h]

theorem update_true (S : Finset ℕ) (q : ℕ) : Function.update (ArIn.ind S) q true = ArIn.ind (insert q S) := by
  funext r
  by_cases hr : r = q <;> simp [ArIn.ind, hr]

theorem ht_kill (h2 : Hypotheses2) (hH : HypothesesH) (hRA : RegularAlteration) (hSW : ScholzeWeinsteinB)
    (hO : O.Core) (R : ℝ) (hR : 2 ≤ R) (S : Finset ℕ) (p : ℕ) (hp : p.Prime) (hpS : p ∉ S) (c : O.s.Comp)
    (P : MvPolynomial (Vr O) ℝ) :
    cNum O c (rename (fb O S p R) (rename (Prod.mk true) (pw O) *
      (rename (Prod.mk false) P - rename (Prod.mk true) P))) = 0 := by
  have h := map_rename_sub (Prod.mk false) (Prod.mk true)
    (cNum O c ∘ₗ (rename (fb O S p R)).toLinearMap ∘ₗ LinearMap.mulLeft ℝ (rename (Prod.mk true) (pw O))) (fun v G => ?_) P 1
  · rwa [mul_one] at h
  obtain ⟨z, hz⟩ := Option.isSome_iff_exists.1 (ln O v).2.2
  have hg (x : Bool × Vr O) : Good R (fb O S p R x) := by
    obtain ⟨_ | _, v⟩ := x
    · rw [fb, update_false hpS]; exact good_fa O _ _ _
    · rw [fb, update_true]; exact good_fa O _ _ _
  have := kill h2 hH hRA hSW hO R hR c (fb O S p R) hg (insert p S) {p} (by simpa using hp) (fun l => (true, .inr l))
    (fun l => by rw [fb, update_true, fa_inr]) (false, v) (true, v) (n := if (ln O v).1 then -1 else 1)
    (by split_ifs <;> simp) (lnSym_eq O _ _ _) (lnSym_eq O _ _ _) hz hz
    (fun q hq _ => ⟨by
      have hq' : q ≠ p := by simpa using hq
      simp only [Function.update_of_ne hq'], .inl rfl⟩) G
  have e : rename (Prod.mk true) (pw O) = ∑ l, X (true, .inr l) ^ 2 := by simp only [pw, map_sum, map_pow, rename_X]
  rw [e]
  exact this

theorem ram_kill (h2 : Hypotheses2) (hH : HypothesesH) (hRA : RegularAlteration) (hSW : ScholzeWeinsteinB)
    (hO : O.Core) (R : ℝ) (hR : 2 ≤ R) (T : Finset ℕ) (hT : (NumberField.discr D.host.E).natAbs.primeFactors ⊆ T)
    (c : O.s.Comp) (G : MvPolynomial (Vr O) ℝ) : cNum O c (rename (fa O (ArIn.ind T) R) (pw O * (dl O ℝ * G))) = 0 := by
  have hd : (NumberField.discr D.host.E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero _)
  have K (k : Fin (D.R.f * O.N)) (l : Fin (D.R.f * O.N) ⊕ Fin (D.R.f * O.N)) (n : ℤ) (hn : n ≠ 0)
      (h₀ : (if (ln O (.inl (rootEquiv O.S k))).1 then -1 else 1) = n)
      (h₁ : fa O (ArIn.ind T) R (.inr l) = Finsupp.single (ArIn.ind T, some R, .inr k) n) :
      cNum O c (rename (fa O (ArIn.ind T) R) (pw O * ((X (.inl (rootEquiv O.S k)) - X (.inr l)) * G))) = 0 :=
    kill h2 hH hRA hSW hO R hR c (fa O (ArIn.ind T) R) (good_fa O T R) T _
      (fun p hp => ⟨Nat.prime_of_mem_primeFactors hp, hT hp⟩) .inr (fa_inr O _ _) (.inl (rootEquiv O.S k)) (.inr l) hn
      ((lnSym_eq O _ _ _).trans (congrArg _ h₀)) h₁ (AdmTest.letterOf_inl _) (letterOf_rootEquiv O.S k)
      (fun q hq hq' => ⟨rfl, .inr fun h => hq (Nat.mem_primeFactors.2 ⟨hq', h, hd⟩)⟩) G
  rw [dl, ← (rootEquiv O.S).sum_comp, ← Equiv.sum_comp Fin.revPerm fun k => (X (.inr (.inr k)) : MvPolynomial (Vr O) ℝ), ← Finset.sum_sub_distrib,
    Finset.sum_mul, Finset.mul_sum, map_sum, map_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  split_ifs with h
  · have h₁ := K k (.inl k) 1 one_ne_zero (by simp [ln, h]) rfl
    have h₂ := neg_cancel h2 hH hO R hR c (fa O (ArIn.ind T) R) (good_fa O T R) (.inr (.inl k)) (.inr (.inr k.rev))
      (by simp) (by simp [fa_inr, wholeSym]) (pw O * G)
    have e : pw O * ((-X (.inl (rootEquiv O.S k)) - X (.inr (.inr (Fin.revPerm k)))) * G) =
        -(pw O * ((X (.inl (rootEquiv O.S k)) - X (.inr (.inl k))) * G)) -
          (X (.inr (.inl k)) + X (.inr (.inr k.rev))) * (pw O * G) := by
      rw [Fin.revPerm_apply]; ring
    rw [e, map_sub, map_sub, map_neg, map_neg, h₁, h₂, neg_zero, sub_zero]
  · exact K k (.inr k.rev) (-1) (by simp) (by simpa [ln] using h) (by simp [fa_inr, wholeSym])

theorem sum_kill (hX : HypothesesXH) (h2 : Hypotheses2) (hH : HypothesesH) (hRA : RegularAlteration) (hSW : ScholzeWeinsteinB)
    (hO : O.Core) (R : ℝ) (hR : 2 ≤ R) (G : MvPolynomial (Vr O) ℝ) (S : Finset ℕ) :
    ∑ c, cNum O c (rename (fa O (ArIn.ind S) R) (pw O * (dl O ℝ * G))) = 0 := by
  have step (S : Finset ℕ) (p : ℕ) (hp : p.Prime)
      (h : ∑ c, cNum O c (rename (fa O (ArIn.ind (insert p S)) R) (pw O * (dl O ℝ * G))) = 0) :
      ∑ c, cNum O c (rename (fa O (ArIn.ind S) R) (pw O * (dl O ℝ * G))) = 0 := by
    by_cases hpS : p ∈ S
    · rwa [Finset.insert_eq_of_mem hpS] at h
    have e₀ : fa O (ArIn.ind S) R = fb O S p R ∘ Prod.mk false := funext fun v => by
      rw [Function.comp_apply, fb, update_false hpS]
    have e₁ : fa O (ArIn.ind (insert p S)) R = fb O S p R ∘ Prod.mk true := funext fun v => by
      rw [Function.comp_apply, fb, update_true]
    have hA := dr_sub_ht hX h2 hH hRA hSW hO R hR S p hp G
    have hB := Finset.sum_eq_zero (s := Finset.univ) fun c _ => ht_kill h2 hH hRA hSW hO R hR S p hp hpS c (dl O ℝ * G)
    rw [e₁] at h
    rw [e₀]
    simp only [← rename_rename] at h ⊢
    rw [← add_zero (0 : ℝ), ← add_zero (0 + 0 : ℝ)]
    nth_rewrite 3 [← h]
    nth_rewrite 2 [← hB]
    nth_rewrite 1 [← hA]
    simp only [← Finset.sum_add_distrib, ← map_add]
    refine Finset.sum_congr rfl fun c _ => congrArg _ (congrArg _ ?_)
    rw [map_mul (rename (Prod.mk false)) (pw O), map_mul (rename (Prod.mk true)) (pw O)]
    ring
  have all (U : Finset ℕ) (hU : ∀ p ∈ U, p.Prime)
      (h : ∑ c, cNum O c (rename (fa O (ArIn.ind (U ∪ S)) R) (pw O * (dl O ℝ * G))) = 0) :
      ∑ c, cNum O c (rename (fa O (ArIn.ind S) R) (pw O * (dl O ℝ * G))) = 0 := by
    induction U using Finset.induction_on with
    | empty => rwa [Finset.empty_union] at h
    | insert p U _ ih =>
      rw [Finset.insert_union] at h
      exact ih (fun q hq => hU q (Finset.mem_insert_of_mem hq)) (step _ p (hU p (Finset.mem_insert_self _ _)) h)
  exact all _ (fun p hp => Nat.prime_of_mem_primeFactors hp)
    (Finset.sum_eq_zero fun c _ => ram_kill h2 hH hRA hSW hO R hR _ Finset.subset_union_left c G)

theorem rename_lamA : rename (Sum.inl : _ → Vr O) (lamA D.what₂.Tau O.N O.j) = dl O ℝ + ∑ k, X (.inr (.inr k)) := by
  rw [dl, sub_add_cancel, lamA, map_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [pHigh, pLow, map_sub, map_sum, pow_one, rename_X, Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : (i : ℕ) < O.j
  · simp [h, not_le.2 h]
  · simp [h, not_lt.1 h]

theorem mixEv_empty (R : ℝ) (c : O.s.Comp) (P : Pol D.what₂.Tau O.N) :
    (arIn O.s O.Φ O.met.hm).mixEv ∅ R 1 c (X (Sum.inr (false, 2)) * DV.tagDR D.what₂.Tau O.N P) =
      rename (fa O (ArIn.ind ∅) R) (C (1 / 2 : ℝ) * pw O * rename Sum.inl P) := by
  have hT := update_false (Finset.notMem_empty 1)
  have e1 : ((arIn O.s O.Φ O.met.hm).mixEv ∅ R 1 c).comp (DV.tagDR D.what₂.Tau O.N) =
      rename (fa O (ArIn.ind ∅) R ∘ Sum.inl) := by
    ext x : 1
    simp [ArIn.mixEv, DV.tagDR, hT]
    exact (congrArg X (fa_inl O _ R x).symm).trans (rename_X (R := ℝ) (fa O (ArIn.ind ∅) R ∘ Sum.inl) x).symm
  have e2 := congrArg (fun f => f P) e1
  simp only [AlgHom.comp_apply] at e2
  rw [map_mul, e2, map_mul, map_mul, rename_rename]
  congr 1
  simp only [ArIn.mixEv, aeval_X, hT, pw, map_sum, map_pow, rename_X, map_mul, algHom_C, fa_inr]
  norm_num
  rfl

end Main

open Formalism.DegreeFormula Formalism.BasicNotions.DV GlobalTheory.VdmRec GlobalTheory.Published GlobalTheory.FlagPoly GlobalTheory.CovTestDR in

theorem sum_termL_eq_sum_termW : ScholzeWeinsteinB → HypothesesXH → Hypotheses2 → HypothesesH → RegularAlteration →
    OnObj fun _ O _ _ _ _ => ∀ R : ℝ, 2 ≤ R → ∑ c, termL O c R = ∑ c, termW O c R := by
  intro hSW hX h2 hH hRA D O hO _ _ _ _ _ R hR
  obtain ⟨G, hG⟩ := sub_dvd_pow_sub_pow (rename (Sum.inl : _ → Vr O) (lamA D.what₂.Tau O.N O.j))
    (∑ k, X (.inr (.inr k))) (dimGr D.what₂.Tau O.N O.j - 1)
  rw [show rename (Sum.inl : _ → Vr O) (lamA D.what₂.Tau O.N O.j) - ∑ k, X (.inr (.inr k)) = dl O ℝ by
    rw [rename_lamA, add_sub_cancel_right]] at hG
  have h := sum_kill hX h2 hH hRA hSW hO R hR (C (1 / 2 : ℝ) * rename Sum.inl (vdmCl D.what₂.Tau O.N O.j) * G) ∅
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib, ← h]
  refine Finset.sum_congr rfl fun c _ => ?_
  have e : (∑ i : Fin (D.R.f * O.N), X (wholeSym (fun _ => false) (some R)
      (.inr i : Fin (D.R.f * O.N) ⊕ Fin (D.R.f * O.N))) : MvPolynomial (Sym D.host.E →₀ ℤ) ℝ) =
      rename (fa O (ArIn.ind ∅) R) (∑ k, X (.inr (.inr k))) := by
    simp only [map_sum, rename_X, fa_inr]
    rfl
  have e₁ : termL O c R = cNum O c (rename (fa O (ArIn.ind ∅) R)
      (C (1 / 2 : ℝ) * pw O * rename Sum.inl (curveV D.what₂.Tau O.N O.j))) := congrArg (cNum O c) (mixEv_empty R c _)
  have e₂ : termW O c R = cNum O c (rename (fa O (ArIn.ind ∅) R)
      (C (1 / 2 : ℝ) * pw O * rename Sum.inl (vdmCl D.what₂.Tau O.N O.j)) *
      rename (fa O (ArIn.ind ∅) R) (∑ k, X (.inr (.inr k))) ^ (dimGr D.what₂.Tau O.N O.j - 1)) :=
    congrArg (cNum O c) (congrArg₂ (fun a b : MvPolynomial (Sym D.host.E →₀ ℤ) ℝ => a * b) (mixEv_empty R c _) (congrArg (· ^ _) e))
  rw [e₁, e₂, ← map_pow, ← map_mul, ← map_sub, ← map_sub]
  congr 2
  rw [curveV, map_mul, map_pow]
  linear_combination (C (1 / 2 : ℝ) * pw O * rename Sum.inl (vdmCl D.what₂.Tau O.N O.j)) * hG

end GlobalTheory.HodgeLat

end
