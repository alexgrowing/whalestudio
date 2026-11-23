import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithIntersectionFormExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithClassFormPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsTensorProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsDualBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalHeightBoundedByPrimeWeightsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeDivisorsEffectiveFiniteDisjointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralSubschemePrimeFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightOfRationalSectionViaDivisorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogGreenDifferenceDeterminantLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ScaleZeroComp
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsAtOfNorms
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumEulerCharTwistsFlagTrivialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagTrivialNsmulCharPStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiDifferenceVanishesOfInvarianceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedSubschemeProjOverModLStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoverInducedMetricsArithStatement

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx
open scoped Classical
open MvPolynomial

namespace GlobalTheory.TrivFlag

theorem exists_prod_ite {α : Type} {D k n : ℕ} (h : D = k + n) (a₀ : α) (ν : Fin n → α) :
    ∃ ν' : Fin D → α, ∀ b : α, ∏ j : Fin D, (X (if (j : ℕ) < k then b else ν' j) : MvPolynomial α ℝ) =
      X b ^ k * ∏ j, X (ν j) := by
  subst h
  refine ⟨Fin.append (fun _ => a₀) ν, fun b => ?_⟩
  rw [Fin.prod_univ_add]
  simp

theorem exists_monomial_eq_prod {α : Type} (u : α →₀ ℕ) :
    ∃ (n : ℕ) (ν : Fin n → α), (monomial u 1 : MvPolynomial α ℝ) = ∏ j, X (ν j) := by
  induction u using Finsupp.induction_linear with
  | zero => exact ⟨0, Fin.elim0, by simp⟩
  | add u v hu hv =>
    obtain ⟨n, ν, h⟩ := hu
    obtain ⟨n', ν', h'⟩ := hv
    refine ⟨n + n', Fin.append ν ν', ?_⟩
    rw [Fin.prod_univ_add]
    simp only [Fin.append_left, Fin.append_right, ← h, ← h', monomial_mul, mul_one]
  | single a n => exact ⟨n, fun _ => a, by simp [X_pow_eq_monomial]⟩

theorem lin_single {ι : Type} [Fintype ι] (i : ι) : lin (Pi.single i 1 : ι → ℝ) = X i := by
  simp [lin, Pi.single_apply, apply_ite, ite_mul]

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

theorem norms_div {V : Cover Y} {A A' : Adl (cxSt F) Y} {L L' : HermLB V.p} {m : ℕ} (e : A' = { A with lg := A'.lg })
    (h : Norms V L (fun x => genAt A.D x ^ m) (fun σ y => m * lnAdl A σ y) fun v e y => m * A.lg v e y)
    (h' : Norms V L' (fun x => genAt A'.D x ^ m) (fun σ y => m * lnAdl A' σ y) fun v e y => m * A'.lg v e y) :
    Norms V (L.tens L'.dual) (fun _ => 1) (fun _ _ => 0) fun v ε y => (m : ℝ) * (A.lg v ε y - A'.lg v ε y) := by
  obtain ⟨_, _, _, _, lg'⟩ := A'
  cases e
  refine (GlobalTheory.T.norms_tensor_product F Y V _ _ _ _ _ _ _ _ h (GlobalTheory.T.norms_dual_bundle F Y V _ _ _ _ h')).congr (fun x => ?_) (fun σ y => ?_)
    fun v ε y => ?_
  · exact mul_inv_cancel₀ (pow_ne_zero _ (Units.ne_zero _))
  · exact add_neg_cancel _
  · ring

theorem sum_interNum_eq_zero (p : ℕ) [hp : Fact p.Prime] (Z : Scheme.{0}) [IsIntegral Z] [Algebra (ZMod p) Γ(Z, ⊤)]
    (hZ : IsProjOver (strHom (ZMod p) Z)) {D : ℕ} (hd : topologicalKrullDim Z = D) {N : ℕ} {g : Fin N → Pic Z}
    (hg : FlagOfTriv g) (m : ℕ) (S : Finset (Fin D)) (hS : S.Nonempty) (B : Fin N → Fin D → LB Z)
    (hB : ∀ i j, (B i j).IsLB) (P : Fin D → Pic Z) (h : ∀ i j, cls (B i j) (hB i j) = if j ∈ S then m • g i else P j) :
    ∑ i, interNum (ZMod p) (structureModule Z) (B i) = 0 := by
  have h0 : (p : Γ(Z, ⊤)) = 0 := by rw [← map_natCast (algebraMap (ZMod p) Γ(Z, ⊤)), ZMod.natCast_self, map_zero]
  have hf := finiteCohTwists_of_isProjOver (f := strHom (ZMod p) Z) (algebraMap_eq_strHom _ Z) (structureModule Z) hZ
  have HD := diffVanish_chiPic_of_isProjOver (f := strHom (ZMod p) Z) (algebraMap_eq_strHom _ Z)
    (structureModule Z) hZ (d := D) (by rw [QCoh.suppDim_structureModule, hd])
  have key (a : ℕ) : FlagOfTriv fun i => p ^ a • g i := by
    induction a with
    | zero => simpa using hg
    | succ a ih => simpa only [smul_smul, pow_succ'] using GlobalTheory.T.flag_trivial_nsmul_char_p p hp.out Z h0 N _ ih
  rw [← GlobalTheory.T.multi_difference_vanishes_of_invariance _ _ D HD N g p hp.out.two_le (fun a => GlobalTheory.T.sum_euler_char_twists_flag_trivial _ Z hf N _ (key a)) m D S hS P]
  exact Finset.sum_congr rfl fun i _ => by rw [interNum_eq_multiDiff _ _ (hB i), funext (h i)]

theorem sum_num_cons_eq_zero (hP : Hypotheses2) (V : Cover Y) (num : Form (Cl V.p) Y.dim) (hn : IsArForm Y.dim num)
    (M : HermLB V.p) (lg : ∀ v : HeightOneSpectrum (𝓞 F), TrueGeo.Ext v → AlgPt Y → ℝ)
    (hM : Norms V M (fun _ => 1) (fun _ _ => 0) lg) (p : ℕ) [hp : Fact p.Prime] (b : ℝ) (hb : 0 ≤ b)
    (hlg : ∀ v e y, |lg v e y| ≤ (if resP v = p then b else 0) * (-Real.log (e.w (resP v : AlgebraicClosure F))))
    {T : Type} [Fintype T] (N : T → Fin Y.dim → HermLB V.p)
    (h : ∀ (Z : Scheme.{0}) (i : Z ⟶ V.X) [IsClosedImmersion i] [IsIntegral Z] [Algebra (ZMod p) Γ(Z, ⊤)],
      topologicalKrullDim Z = Y.dim → ∑ t, interNum (ZMod p) (structureModule Z) (fun j => (N t j).B.pull i) = 0) :
    ∑ t, num (Fin.cons (cl M) fun j => cl (N t j)) = 0 := by
  haveI : IsLocallyNoetherian V.X := V.ar.isLocallyNoetherian
  haveI : IsNoetherian V.X := V.ar.isNoetherian
  obtain ⟨r, hr, h1, hmult⟩ := GlobalTheory.T.local_height_bounded_by_prime_weights F Y V M lg hM {p} (fun _ => b) (by simpa using ⟨hp.out, hb⟩)
    (by simpa only [Finset.mem_singleton] using hlg)
  have key (z : V.X) : ∃ d : T → ℝ, ∑ t, d t = 0 ∧ ((M.div hr).mult z ≠ 0 → ∀ t,
      ∃ (_ : Fact p.Prime) (Z : Scheme.{0}) (i : Z ⟶ V.X) (_ : IsClosedImmersion i) (_ : IsIntegral Z)
        (_ : Algebra (ZMod p) Γ(Z, ⊤)), i (genericPoint Z) = z ∧ topologicalKrullDim Z = Y.dim ∧
          d t = interNum (ZMod p) (structureModule Z) (fun j => (N t j).B.pull i)) := by
    by_cases hz : (M.div hr).mult z = 0
    · exact ⟨0, by simp, fun h => absurd hz h⟩
    have hpos : 0 < Scheme.ord ((p : V.X.functionField)) z := by
      refine lt_of_le_of_ne ((GlobalTheory.T.prime_divisors_effective_finite_disjoint _ V.X V.p _ V.ar p hp.out).1 z) fun e => hz ?_
      have := hmult z
      rw [Finset.sum_singleton, ← e, Int.cast_zero, mul_zero] at this
      exact_mod_cast abs_nonpos_iff.1 this
    obtain ⟨Z, i, hi, hZ, hA, e₁, e₂⟩ := GlobalTheory.T.exists_integral_subscheme_prime_fibre _ V.X V.p _ V.ar p z hpos
    exact ⟨fun t => interNum (ZMod p) (structureModule Z) fun j => (N t j).B.pull i, by beta_reduce; exact_mod_cast h Z i e₂,
      fun _ t => ⟨hp, Z, i, hi, hZ, hA, e₁, e₂, rfl⟩⟩
  choose d hd₀ hd using key
  have hfin : (Function.support (M.div hr).mult).Finite := (M.div hr).finite_support_mult
  have e (t : T) : num (Fin.cons (cl M) fun j => cl (N t j)) =
      ∑ z ∈ hfin.toFinset, ((M.div hr).mult z : ℝ) * d z t * Real.log p := by
    rw [GlobalTheory.T.height_of_rational_section_via_divisor hP _ V.X V.p _ V.ar num hn M r hr h1 (N t) (fun _ => p) (fun z => d z t) fun z hz => hd z hz t]
    exact finsum_eq_sum_of_support_subset _ fun z hz => hfin.mem_toFinset.2 fun h0 => hz (by simp [h0])
  rw [Finset.sum_congr rfl fun t _ => e t, Finset.sum_comm]
  exact Finset.sum_eq_zero fun z _ => by rw [← Finset.sum_mul, ← Finset.mul_sum, hd₀, mul_zero, zero_mul]

theorem powerSum_mul_vertical (hP : Hypotheses2) (M : TrueGeo.Model Y) {ι : Type} [Fintype ι]
    (A : ι → Adl (cxSt F) Y) (L : ι → HermLB M.p) (m : ℕ+) (Ψ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ)
    (hI : ∀ i, (A i).Induced M (L i) m 0) (hΨ : haveI := M.ar.isIntegral; IsArFun L Y.dim Ψ) (p : ℕ) (hp : p.Prime)
    {N : ℕ} (s : Fin N → ι) (hfl : FlagAt (fun a => A (s a)) p) (i₀ i₁ : ι) (e : A i₁ = { A i₀ with lg := (A i₁).lg })
    (b : ℝ) (hb : 0 ≤ b) (hlg : ∀ v e y, |(A i₀).lg v e y - (A i₁).lg v e y| ≤
      (if resP v = p then b else 0) * (-Real.log (e.w (resP v : AlgebraicClosure F)))) (k : ℕ) (hk : 1 ≤ k) (g : MvPolynomial ι ℝ) :
    Ψ ((∑ a, X (s a) ^ k) * ((X i₀ - X i₁) * g)) = 0 := by
  haveI := Fact.mk hp
  have hC := hP.p4
  obtain ⟨V, hF⟩ := hfl
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
    have hv := sum_num_cons_eq_zero hP V' num hn _ _ (norms_div e (hL' i₀) (hL' i₁)) p ((m : ℕ) * b) (by positivity)
      (fun v ε y => by
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
        refine (mul_le_mul_of_nonneg_left (hlg v ε y) (Nat.cast_nonneg _)).trans_eq ?_
        split_ifs <;> ring)
      (fun a j => L' (if (j : ℕ) < k then s a else ν' j)) (fun Z i _ _ _ hZ => by
        have h0 : (p : Γ(Z, ⊤)) = 0 := by rw [← map_natCast (algebraMap (ZMod p) Γ(Z, ⊤)), ZMod.natCast_self, map_zero]
        obtain ⟨g, hg, hg'⟩ := hF V' π hπ hl (fun a => (L' (s a)).B) (fun a => (L' (s a)).isLB) m
          (fun a => normsAt_of_norms (hL' (s a)) p ⊤) Z i h0
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
      rw [← lin_single, ← lin_single]
      simp only [lin, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]
    rw [Fin.prod_univ_succ, Fin.cons_zero, e₂] at this
    simp only [Fin.cons_succ, lin_single, hν'] at this
    rw [mul_left_comm, this]
    refine map_congr_rad num fun j => Fin.cases ?_ (fun j => ?_) j
    · have h₁ := neg_mem (add_mem (rt (L' i₀) (L' i₁).dual) (rd (L' i₁)))
      convert h₁ using 1
      simp only [Fin.cons_zero, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, Pi.single_apply, ite_smul, one_smul,
        zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      abel
    · simp [Pi.single_apply]

end GlobalTheory.TrivFlag

namespace GlobalTheory.TrivFlag

theorem numL_rename {ι B : Type} (w : ι → B) (num : Multiset B → ℝ) (d : ℕ) (Ψ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ) (c : ℝ)
    (h₀ : ∀ (P : MvPolynomial ι ℝ) (e : ℕ), e ≠ d → P.IsHomogeneous e → Ψ P = 0)
    (h : ∀ μ : Multiset ι, Multiset.card μ = d → num (μ.map w) = Ψ (μ.map X).prod / c) (P : MvPolynomial ι ℝ) :
    numL num d (rename w P) = Ψ P / c := by
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ => rw [map_add, map_add, map_add, hP, hQ, add_div]
  | monomial u a =>
    have e₁ : (monomial u a : MvPolynomial ι ℝ) = a • monomial u 1 := by rw [smul_monomial, smul_eq_mul, mul_one]
    rw [e₁, map_smul, map_smul, map_smul, smul_eq_mul, smul_eq_mul, mul_div_assoc]
    congr 1
    by_cases hd : u.degree = d
    · have e₂ : (monomial u 1 : MvPolynomial ι ℝ) = ((Finsupp.toMultiset u).map X).prod := by
        rw [monomial_eq, C_1, one_mul, Finsupp.toMultiset_map, Finsupp.prod_toMultiset,
          Finsupp.prod_mapDomain_index (fun _ => pow_zero _) fun _ _ _ => pow_add _ _ _]
      have e₃ : Multiset.card (Finsupp.toMultiset u) = d := by
        rw [Finsupp.card_toMultiset, ← hd]; rfl
      rw [rename_monomial, ← congrFun (coe_basisMonomials B ℝ), numL, Module.Basis.constr_basis, if_pos, e₂, ← h _ e₃,
        Finsupp.toMultiset_map]
      rw [Finsupp.degree_mapDomain, hd]
    · have hh : (monomial u 1 : MvPolynomial ι ℝ).IsHomogeneous u.degree := isHomogeneous_monomial _ rfl
      rw [numL_homog _ _ _ hd _ hh.rename_isHomogeneous, h₀ _ _ hd hh, zero_div]

section Syms

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem mem_support_rootSym {a : ℕ → Bool} {R : Option ℝ} {τ : E →+* ℂ} {i : ℕ} {b : Sym E}
    (h : b ∈ (rootSym Dw a R τ i).support) : b.1 = a ∧ b.2.1 = R := by
  unfold rootSym at h
  split_ifs at h <;> rw [Finset.mem_singleton.1 (Finsupp.support_single_subset h)] <;> exact ⟨rfl, rfl⟩

theorem mem_support_wholeSym {a : ℕ → Bool} {R : Option ℝ} {g : ℕ} {x : Fin g ⊕ Fin g} {b : Sym E}
    (h : b ∈ (wholeSym a R x).support) : b.1 = a ∧ b.2.1 = R := by
  rcases x with x | x <;> rw [Finset.mem_singleton.1 (Finsupp.support_single_subset h)] <;> exact ⟨rfl, rfl⟩

theorem parOf_rootSym (a : ℕ → Bool) (R : Option ℝ) (τ : E →+* ℂ) (i : ℕ) : parOf (rootSym Dw a R τ i) = R := by
  have h : (rootSym Dw a R τ i).support.Nonempty := by
    unfold rootSym
    split_ifs <;> simp [Finsupp.support_single_ne_zero]
  rw [parOf, dif_pos h]
  exact (mem_support_rootSym h.choose_spec).2

variable {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)

theorem adlOf_rootSym_eq {C : CxSt F} (hm : Mets Y C) (a a' : ℕ → Bool) (R : Option ℝ) (τ : E →+* ℂ) (i : ℕ) :
    adlOf Y hm (rootSym Dw a' R τ i) =
      { adlOf Y hm (rootSym Dw a R τ i) with lg := (adlOf Y hm (rootSym Dw a' R τ i)).lg } := by
  have key (n n' : Letter Dw → ℤ) (h : n = n') (r r' : Option ℝ) (h' : r = r') (lg) :
      (⟨divOf Y n, 1, fun σ => hm r σ n, 0, lg⟩ : Adl C Y.Y) = ⟨divOf Y n', 1, fun σ => hm r' σ n', 0, lg⟩ := by
    rw [h, h']
  exact key _ _ ((expo_rootSym _ _ _ _ _).trans (expo_rootSym _ _ _ _ _).symm) _ _
    ((parOf_rootSym _ _ _ _).trans (parOf_rootSym _ _ _ _).symm) _

theorem abs_lgOf_update_sub_le {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)} (Y : FlagCpt Z e)
    (a : ℕ → Bool) (p : ℕ) (R : Option ℝ) (τ : E →+* ℂ) (i : ℕ) (v : HeightOneSpectrum (𝓞 F))
    (ε : TrueGeo.Ext v) (y : AlgPt Y.Y) :
    |lgOf Y (rootSym Dw (Function.update a p false) R τ i) v ε y -
        lgOf Y (rootSym Dw (Function.update a p true) R τ i) v ε y| ≤
      (if resP v = p then 1 / ((p : ℝ) - 1) + vDiff E p else 0) * (-Real.log (ε.w (resP v : AlgebraicClosure F))) := by
  have hw : 0 ≤ -Real.log (ε.w (resP v : AlgebraicClosure F)) :=
    neg_nonneg.2 (Real.log_nonpos (ε.w.nonneg _) ((ε.mem_O _).1 (natCast_mem _ _)))
  have hp : (resP v).Prime := CharP.char_prime_of_ne_zero (𝓞 F ⧸ v.asIdeal) (CharP.ringChar_ne_zero_of_finite _)
  haveI := Fact.mk hp
  have hs (a : ℕ → Bool) (Φ : Sym E → ℝ) : ((rootSym Dw a R τ i).sum fun b n => (n : ℝ) * Φ b) =
      if i < Dw.p then Φ (a, R, .inl (τ, i)) else -Φ (a, R, .inl (conjEmb τ, Dw.p + Dw.q - 1 - i)) := by
    unfold rootSym
    split_ifs <;> rw [Finsupp.sum_single_index (by simp)] <;> push_cast <;> ring
  simp only [lgOf, dif_pos hp]
  rewrite [expo_rootSym Dw (Function.update a p false), expo_rootSym Dw (Function.update a p true),
    add_sub_add_left_eq_sub, ← mul_sub, abs_mul, hs, hs]
  dsimp only
  by_cases h : resP v = p
  · subst h
    have hl := Real.log_pos (show (1 : ℝ) < resP v by exact_mod_cast hp.one_lt)
    rewrite [if_pos rfl, Function.update_self, Function.update_self]
    have key (t : ℝ) (ht : t ≤ Real.log (resP v) / ((resP v : ℝ) - 1) + vDiff E (resP v) * Real.log (resP v)) :
        |-Real.log (ε.w (resP v : AlgebraicClosure F)) / Real.log (resP v)| * t ≤
          (1 / ((resP v : ℝ) - 1) + vDiff E (resP v)) * (-Real.log (ε.w (resP v : AlgebraicClosure F))) := by
      refine (mul_le_mul_of_nonneg_left ht (abs_nonneg _)).trans_eq ?_
      rw [abs_of_nonneg (div_nonneg hw hl.le)]
      field_simp
    refine key _ ?_
    split_ifs
    · rw [abs_sub_comm]
      exact LgDiff.abs_lnStep_sub_le HTBound.htBound _ _ _ _ _ _
    · rw [neg_sub_neg]
      exact LgDiff.abs_lnStep_sub_le HTBound.htBound _ _ _ _ _ _
  · have hb : Function.update a p false (resP v) = Function.update a p true (resP v) :=
      (Function.update_of_ne h _ _).trans (Function.update_of_ne h _ _).symm
    rewrite [hb, sub_self, abs_zero, mul_zero, if_neg h, zero_mul]
    exact le_rfl

end Syms

end GlobalTheory.TrivFlag
