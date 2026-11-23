import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumLogDivPredLeReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FRSubEqTopSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncatedPotentialSmooth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetric
import Development.AbelianVarietyTheory.Definitions.Divisors.DualRef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsComb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsPullbackAlongCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverRefinementGenericDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogGreenDifferenceDeterminantLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ScaleZeroComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithIntersectionFormExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithClassFormPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithFormPullbackDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommonRefinementCoversStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefFibreTwistExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithFormDifferenceBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormLogBoundPrimeWeightsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithFormVanishTrivialMetricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefFibreOfNormsPowerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefOverAntitoneCombStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm

noncomputable section

namespace GlobalTheory.VertObj

theorem abs_lgOf_single_sub_le {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}
    {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)}
    {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : ShFam.FlagCpt Z e) {Q₀ Q : Finset ℕ} (hQ : Q₀ ⊆ Q)
    (hd : (NumberField.discr E).natAbs.primeFactors ⊆ Q₀) (τ : E →+* ℂ) (k : ℕ) (n : ℤ) (hn : |(n : ℝ)| = 1)
    (v : HeightOneSpectrum (𝓞 F)) (ε : TrueGeo.Ext v) (y : AlgPt Y.Y) :
    |lgOf Y (Finsupp.single (ArIn.ind Q, none, .inl (τ, k)) n) v ε y -
      lgOf Y (Finsupp.single (ArIn.ind Q₀, none, .inl (τ, k)) n) v ε y| ≤
      (if resP v ∈ Q \ Q₀ then 1 / ((resP v : ℝ) - 1) else 0) * (-Real.log (ε.w (resP v : AlgebraicClosure F))) := by
  have hw : 0 ≤ -Real.log (ε.w (resP v : AlgebraicClosure F)) :=
    neg_nonneg.2 (Real.log_nonpos (ε.w.nonneg _) ((ε.mem_O _).1 (natCast_mem _ _)))
  by_cases hp : (resP v).Prime
  swap
  · simp only [lgOf, dif_neg hp, sub_self, abs_zero]
    refine mul_nonneg ?_ hw
    split_ifs
    · rcases Nat.eq_zero_or_pos (resP v) with h | h
      · exact absurd (CharP.char_prime_of_ne_zero (𝓞 F ⧸ v.asIdeal) (CharP.ringChar_ne_zero_of_finite _)) hp
      · exact div_nonneg zero_le_one (sub_nonneg.2 (by exact_mod_cast h))
    · exact le_rfl
  haveI := Fact.mk hp
  have he : expo Dw (Finsupp.single (ArIn.ind Q, none, .inl (τ, k)) n) =
      expo Dw (Finsupp.single (ArIn.ind Q₀, none, .inl (τ, k)) n) := funext fun x => by simp only [expo_single]
  simp only [lgOf, dif_pos hp]
  rw [he, add_sub_add_left_eq_sub, ← mul_sub, Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp),
    ← mul_sub, abs_mul, abs_mul, hn, one_mul]
  have h1 : (1 : ℝ) < resP v := by exact_mod_cast hp.one_lt
  have hl := Real.log_pos h1
  split_ifs with h
  · obtain ⟨h₁, h₂⟩ := Finset.mem_sdiff.1 h
    have hv : vDiff E (resP v) = 0 := by
      rw [vDiff, padicValNat.eq_zero_of_not_dvd fun h => h₂ (hd (Nat.mem_primeFactors.2
        ⟨hp, h, Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero _)⟩))]
      simp
    simp only [ArIn.ind, h₁, h₂, decide_true, decide_false]
    refine (mul_le_mul_of_nonneg_left (GlobalTheory.LgDiff.abs_lnStep_sub_le HTBound.htBound Z _ _ _ τ k) (abs_nonneg _)).trans_eq ?_
    rw [hv, abs_of_nonneg (div_nonneg hw hl.le)]
    field_simp
    ring
  · have : ArIn.ind Q (resP v) = ArIn.ind Q₀ (resP v) := by
      simp only [ArIn.ind, decide_eq_decide]
      exact ⟨fun h₁ => by_contra fun h₂ => h (Finset.mem_sdiff.2 ⟨h₁, h₂⟩), fun h₁ => hQ h₁⟩
    simp [this]

theorem abs_lg_root0_sub_le : ∀ (D : D7) (O : Setup D) (c : O.s.Comp) (Q₀ Q : Finset ℕ), Q₀ ⊆ Q → (NumberField.discr D.host.E).natAbs.primeFactors ⊆ Q₀ → ∀ (x : DV.Rt D.what₂.Tau O.N) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (e : TrueGeo.Ext v) (y : AlgPt (O.var c)), |(O.root0 c Q x).lg v e y - (O.root0 c Q₀ x).lg v e y| ≤ (if resP v ∈ Q \ Q₀ then 1 / ((resP v : ℝ) - 1) else 0) * (-Real.log (e.w (resP v : AlgebraicClosure D.what₂.LL))) := by
  intro D O c Q₀ Q hQ hd x v e y
  change |lgOf _ (rootSym _ _ _ _ _) v e y - lgOf _ (rootSym _ _ _ _ _) v e y| ≤ _
  unfold rootSym
  split_ifs with h₁ h₂ h₂
  all_goals first
    | simpa only [if_pos h₂] using abs_lgOf_single_sub_le _ hQ hd _ _ _ (by simp) v e y
    | simpa only [if_neg h₂] using abs_lgOf_single_sub_le _ hQ hd _ _ _ (by simp) v e y

end GlobalTheory.VertObj

namespace GlobalTheory.VertObj

section Glue

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

abbrev Reads (V : Cover Y) (A : Adl (cxSt F) Y) (L : HermLB V.p) (k : ℕ) : Prop :=
  Norms V L (fun x => genAt A.D x ^ k) (fun σ y => k * lnAdl A σ y) (fun v e y => k * A.lg v e y)

theorem map_genericPoint {V' V : Cover Y} (g : V'.G ⟶ V.G) (h : g ≫ V.π = V'.π) :
    g (genericPoint V'.G) = genericPoint V.G := by
  have key (W : Cover Y) : W.π (genericPoint W.G) = genericPoint Y.X := by
    have := (genericPoint_spec W.G).image W.π.continuous
    rw [Set.image_univ, W.π.surjective.range_eq, closure_univ] at this
    exact this.eq (genericPoint_spec _)
  obtain ⟨U, hU, e⟩ := isDiscrete_iff_forall_exists_isOpen.mp (V.π.isDiscrete_preimage_singleton (genericPoint Y.X))
    (g (genericPoint V'.G)) (by rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, h, key]; rfl)
  have h₁ : g (genericPoint V'.G) ∈ U := (e.ge rfl).1
  exact (e.le ⟨(genericPoint_specializes _).mem_open hU h₁, key V⟩).symm

theorem lies {V' V : Cover Y} (π : V'.X ⟶ V.X) (hπ : π ≫ V.p = V'.p) (h : Lies V' V π) :
    π (genericPoint V'.X) = genericPoint V.X ∧ π.residueDegree (genericPoint V'.X) * V.deg = V'.deg ∧
      ∀ (A : Adl (cxSt F) Y) (L : HermLB V.p) (k : ℕ), Reads V A L k → Reads V' A (L.pull π hπ) k := by
  obtain ⟨g, h₁, h₂⟩ := h
  obtain ⟨a, b⟩ := GlobalTheory.T.cover_refinement_generic_degree F Y V V' π hπ g h₁.symm h₂ (map_genericPoint g h₂)
  exact ⟨a, b, fun A L k => GlobalTheory.T.norms_pullback_along_cover F Y V V' π hπ g h₁.symm h₂ (map_genericPoint g h₂) L _ _ _⟩

theorem norms_diff {V : Cover Y} {A A' : Adl (cxSt F) Y} {L L' : HermLB V.p} {k k' : ℕ} (e : A' = { A with lg := A'.lg })
    (h : Reads V A L k) (h' : Reads V A' L' k') :
    Norms V (ArInt.comb (fun b : Bool => bif b then L else L') fun b => bif b then (k' : ℤ) else -k) (fun _ => 1)
      (fun _ _ => 0) fun v ε y => (k : ℝ) * k' * (A.lg v ε y - A'.lg v ε y) := by
  obtain ⟨_, _, _, _, lg'⟩ := A'
  cases e
  refine (norms_comb (f := fun b x => genAt A.D x ^ (bif b then k else k'))
    (a := fun b σ y => (bif b then k else k' : ℕ) * lnAdl A σ y)
    (l := fun b v ε y => bif b then k * A.lg v ε y else k' * lg' v ε y)
    (fun b => by cases b <;> assumption) _).congr (fun x => ?_) (fun σ y => ?_) fun v ε y => ?_
  · have : genAt A.D x ≠ 0 := Units.ne_zero _
    simp only [Fintype.prod_bool, cond_true, cond_false, zpow_neg, zpow_natCast, ← pow_mul, mul_comm k']
    exact mul_inv_cancel₀ (pow_ne_zero _ this)
  · simp only [Fintype.sum_bool, cond_true, cond_false]
    push_cast
    ring
  · simp only [Fintype.sum_bool, cond_true, cond_false]
    push_cast
    ring

theorem cl_diff (hP : Hypotheses2) {V : Cover Y} {D : ℕ} (hD : Y.dim = D) {num : Form (Cl V.p) D} (hn : IsArForm D num)
    (L L' : HermLB V.p) (k k' : ℕ) : ((k' : ℝ) • cl L - (k : ℝ) • cl L') -
      cl (ArInt.comb (fun b : Bool => bif b then L else L') fun b => bif b then (k' : ℤ) else -k) ∈ rad num := by
  rw [← neg_sub]
  refine neg_mem ?_
  simpa [sub_eq_add_neg] using (GlobalTheory.T.arith_class_form_properties hP.p4 _ _ V.p D (hD ▸ V.ar) num hn).2.2.2 _
    (fun b : Bool => bif b then L else L') fun b => bif b then (k' : ℤ) else -k

theorem vert (hP : Hypotheses2) (V : Cover Y) {D : ℕ} (hD : Y.dim = D) (num : Form (Cl V.p) D) (hn : IsArForm D num)
    (A A' : Adl (cxSt F) Y) (L L' : HermLB V.p) (k k' : ℕ) (e : A' = { A with lg := A'.lg }) (h : Reads V A L k)
    (h' : Reads V A' L' k') (S : Finset ℕ) (a : ℕ → ℝ) (hS : ∀ l ∈ S, l.Prime ∧ 0 ≤ a l)
    (hb : ∀ (v : HeightOneSpectrum (𝓞 F)) (e : TrueGeo.Ext v) (y : AlgPt Y), |A.lg v e y - A'.lg v e y| ≤
      (if resP v ∈ S then a (resP v) else 0) * (-Real.log (e.w (resP v : AlgebraicClosure F))))
    (N : Fin D → HermLB V.p) (hN : ∀ j, ∀ l ∈ S, NefOver (N j) l) :
    |num (Fin.cons ((k' : ℝ) • cl L - (k : ℝ) • cl L') fun j => cl (N j))| ≤
      (k : ℝ) * k' * (∑ l ∈ S, a l * Real.log l) * num (Fin.cons (cl (oneB V.p)) fun j => cl (N j)) := by
  have := GlobalTheory.T.norm_log_bound_prime_weights hP F Y V D hD num hn _ _ (norms_diff e h h') S (fun l => k * k' * a l)
    (fun l hl => ⟨(hS l hl).1, mul_nonneg (by positivity) (hS l hl).2⟩) (fun v ε y => by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ k * k')]
      refine (mul_le_mul_of_nonneg_left (hb v ε y) (by positivity)).trans_eq ?_
      split_ifs <;> ring) N hN
  refine (le_of_eq_of_le (congrArg abs (map_congr_rad num
    fun j => Fin.cases (cl_diff hP hD hn L L' k k') (fun j => by simp) j)) this).trans_eq ?_
  simp only [Finset.mul_sum, mul_assoc]

theorem vertDeg (hP : Hypotheses2) (V : Cover Y) {D : ℕ} (hD : Y.dim = D) (num : Form (Cl V.p) D) (hn : IsArForm D num)
    (A A' : Adl (cxSt F) Y) (L L' : HermLB V.p) (k k' : ℕ) (e : A' = { A with lg := A'.lg }) (h : Reads V A L k)
    (h' : Reads V A' L' k') (v : Fin D → Cl V.p) (j : Fin D) :
    num (Fin.cons (cl (oneB V.p)) (Function.update v j ((k' : ℝ) • cl L - (k : ℝ) • cl L'))) = 0 := by
  rw [← GlobalTheory.T.arith_form_vanish_trivial_metric hP F Y V D hD num hn _ _ (norms_diff e h h') v j]
  refine map_congr_rad num fun i => Fin.cases (by simp) (fun i => ?_) i
  by_cases hi : i = j
  · subst hi
    simpa using cl_diff hP hD hn L L' k k'
  · simp [hi]

end Glue

end GlobalTheory.VertObj

namespace GlobalTheory.VertObj

theorem exists_bound {E : Type 1} [AddCommGroup E] [Module ℝ E] {D : ℕ} (num : Form E D) {ι : Type} [Fintype ι] (g : ι → E)
    (w : Fin (D + 1) → E) : ∃ C : ℝ, ∀ c : Fin (D + 1) → ι → ℝ, (∀ j i, |c j i| ≤ 1) →
      |num fun j => w j + ∑ i, c j i • g i| ≤ C := by
  let g' : Fin (D + 1) → Option ι → E := fun j o => o.elim (w j) g
  refine ⟨∑ r : Fin (D + 1) → Option ι, |num fun j => g' j (r j)|, fun c h => ?_⟩
  let c' : Fin (D + 1) → Option ι → ℝ := fun j o => o.elim 1 (c j)
  have e : (fun j => w j + ∑ i, c j i • g i) = fun j => ∑ o, c' j o • g' j o := by
    funext j
    simp [c', g', Fintype.sum_option]
  rw [e, num.map_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  rw [num.map_smul_univ, smul_eq_mul, abs_mul, Finset.abs_prod]
  refine mul_le_of_le_one_left (abs_nonneg _) (Finset.prod_le_one (fun _ _ => abs_nonneg _) fun j _ => ?_)
  cases hr : r j
  · simp [c']
  · simpa [c'] using h j _

def wtCl {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {R : Type} [Fintype R] (amp : HermLB p) (m : ℕ)
    (L : R → HermLB p) (u : R → ℝ) (t : ℝ) : Cl p := (t / m) • cl amp - ∑ r, u r • cl (L r)

theorem pullCl_wtCl {k : Type} [CommRing k] {X X' : Scheme.{0}} {p : X ⟶ Sp k} {q : X' ⟶ Sp k} {R : Type} [Fintype R]
    (π : X' ⟶ X) (hπ : π ≫ p = q) (amp : HermLB p) (m : ℕ) (L : R → HermLB p) (u : R → ℝ) (t : ℝ) :
    pullCl π hπ (wtCl amp m L u t) = wtCl (amp.pull π hπ) m (fun r => (L r).pull π hπ) u t := by
  simp only [wtCl, map_sub, map_smul, map_sum, pullCl_cl]

theorem wtCl_sub {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {R : Type} [Fintype R] (amp amp' : HermLB p)
    {m m' : ℕ} (hm : 0 < m) (hm' : 0 < m') (L L' : R → HermLB p) (u : R → ℝ) (t : ℝ) :
    wtCl amp m L u t - wtCl amp' m' L' u t = (t / (m * m')) • ((m' : ℝ) • cl amp - (m : ℝ) • cl amp') -
      ∑ r, u r • (((1 : ℕ) : ℝ) • cl (L r) - ((1 : ℕ) : ℝ) • cl (L' r)) := by
  have h₁ : (m : ℝ) ≠ 0 := by positivity
  have h₂ : (m' : ℝ) ≠ 0 := by positivity
  simp only [wtCl, smul_sub, smul_smul, Nat.cast_one, Finset.sum_sub_distrib, mul_one]
  rw [show t / (m * m') * m' = t / m by field_simp, show t / (m * m') * m = t / m' by field_simp]
  abel

theorem cons_comb {E : Type 1} [AddCommGroup E] [Module ℝ E] {D : ℕ} (num : Form E D) {R : Type} [Fintype R] (a : ℝ) (x : E)
    (u : R → ℝ) (z : R → E) (N : Fin D → E) :
    num (Fin.cons (a • x - ∑ r, u r • z r) N) = a * num (Fin.cons x N) - ∑ r, u r * num (Fin.cons (z r) N) := by
  let f : E →ₗ[ℝ] ℝ := { toFun := fun x => num (Fin.cons x N), map_add' := num.cons_add N, map_smul' := num.cons_smul N }
  change f _ = a * f x - ∑ r, u r * f (z r)
  simp only [map_sub, map_smul, map_sum, smul_eq_mul]

theorem update_comb {E : Type 1} [AddCommGroup E] [Module ℝ E] {D : ℕ} (num : Form E D) {R : Type} [Fintype R] (a : ℝ) (x : E)
    (u : R → ℝ) (z : R → E) (o : E) (v : Fin D → E) (j : Fin D) :
    num (Fin.cons o (Function.update v j (a • x - ∑ r, u r • z r))) = a * num (Fin.cons o (Function.update v j x)) -
      ∑ r, u r * num (Fin.cons o (Function.update v j (z r))) := by
  let f : E →ₗ[ℝ] ℝ := (num.curryLeft o).toLinearMap v j
  change f _ = a * f x - ∑ r, u r * f (z r)
  simp only [map_sub, map_smul, map_sum, smul_eq_mul]

end GlobalTheory.VertObj

namespace GlobalTheory.VertObj

theorem general (hP : Hypotheses2) {F : Type} [Field F] [NumberField F] {Y : Var F} {D : ℕ} (hD : Y.dim = D) {R : Type} [Fintype R]
    (ab : Adl (cxSt F) Y) (hab : ab.NefFib) (V₀ : Cover Y) (ρ₀ : R → Adl (cxSt F) Y) (L₀ : R → HermLB V₀.p)
    (h₀ : ∀ r, Reads V₀ (ρ₀ r) (L₀ r) 1) (amp₀ : HermLB V₀.p) {k₀ : ℕ} (hk₀ : 0 < k₀) (ha₀ : Reads V₀ ab amp₀ k₀)
    (num₀ : Form (Cl V₀.p) D) (hn₀ : IsArForm D num₀) :
    ∃ C : ℝ, ∀ (V : Cover Y) (ρ : R → Adl (cxSt F) Y) (L : R → HermLB V.p), (∀ r, Reads V (ρ r) (L r) 1) →
      ∀ (amp : HermLB V.p) (k : ℕ), 0 < k → Reads V ab amp k → ∀ num : Form (Cl V.p) D, IsArForm D num →
      ∀ (S : Finset ℕ) (a : ℕ → ℝ), (∀ l ∈ S, l.Prime ∧ 0 ≤ a l) → (∀ r, ρ₀ r = { ρ r with lg := (ρ₀ r).lg }) →
      (∀ r (v : HeightOneSpectrum (𝓞 F)) (e : TrueGeo.Ext v) (y : AlgPt Y), |(ρ r).lg v e y - (ρ₀ r).lg v e y| ≤
        (if resP v ∈ S then a (resP v) else 0) * (-Real.log (e.w (resP v : AlgebraicClosure F)))) →
      ∀ (u : R → ℝ) (t : ℝ), (∀ r, |u r| ≤ 1) → t ∈ Set.Icc (0 : ℝ) 1 →
      (∀ (V' : Cover Y) (L' : R → HermLB V'.p), (∀ r, Reads V' (ρ r) (L' r) 1) → ∀ num' : Form (Cl V'.p) D,
        IsArForm D num' → -∑ r, u r • cl (L' r) ∈ cone num' (cl '' {N | ∀ l ∈ S, NefOver N l})) →
      |num (fun _ => wtCl amp k L u t) / V.deg - num₀ (fun _ => wtCl amp₀ k₀ L₀ u t) / V₀.deg| ≤
        C * ∑ l ∈ S, a l * Real.log l := by
  have hA := hP.p4
  obtain ⟨H, hH⟩ := GlobalTheory.T.nef_fibre_twist_exists F V₀.X V₀.p V₀.ar.isProjOver R L₀
  set h0 : Cl V₀.p := (Fintype.card R : ℝ) • cl H with hh0
  choose C hC using fun i : Fin (D + 1) => exists_bound num₀
    (fun o : Option R => o.elim (((1 : ℝ) / k₀) • cl amp₀) fun r => -cl (L₀ r))
    (Fin.cons (cl (oneB V₀.p)) fun j : Fin D => if (j : ℕ) < i then 0 else (2 : ℝ) • h0)
  refine ⟨Fintype.card R * (∑ i, C i) / V₀.deg, fun V ρ L hL amp k hk ha num hn S a hS hρ hlg u t hu ht hnef => ?_⟩
  obtain ⟨V', π, π₀, hπ, hπ₀, l₁, l₀⟩ := GlobalTheory.T.common_refinement_covers F Y V V₀
  obtain ⟨g₁, d₁, i₁⟩ := lies π hπ l₁
  obtain ⟨g₀, d₀, i₀⟩ := lies π₀ hπ₀ l₀
  have ar (W : Cover Y) : IsArithVar W.p D := hD ▸ W.ar
  obtain ⟨num', hn', hs'⟩ := GlobalTheory.T.arith_intersection_form_exists hA _ _ V'.p D (ar V')
  have hd' := V'.deg_pos
  obtain ⟨p₁, -⟩ := GlobalTheory.T.arith_form_pullback_degree hA _ _ _ V.p V'.p D (ar V) (ar V') π hπ g₁ (fun h => by simp [h] at d₁; omega) num num' hn hn'
  obtain ⟨p₀, o₀⟩ := GlobalTheory.T.arith_form_pullback_degree hA _ _ _ V₀.p V'.p D (ar V₀) (ar V') π₀ hπ₀ g₀ (fun h => by simp [h] at d₀; omega)
    num₀ num' hn₀ hn'
  obtain ⟨rt, rd, -, -⟩ := GlobalTheory.T.arith_class_form_properties hA _ _ V'.p D (ar V') num' hn'
  obtain ⟨nH, nL⟩ := hH V'.X V'.p V'.ar.isProjOver π₀ hπ₀
  set G : Set (Cl V'.p) := cl '' {N | ∀ l ∈ S, NefOver N l}
  have nef {N : HermLB V'.p} (h : NefFib N) : cl N ∈ cone num' G :=
    mem_cone_of_mem ⟨N, fun l hl => (nefFib_iff N).1 h l (hS l hl).1, rfl⟩
  set σ : ℝ := ∑ l ∈ S, a l * Real.log l
  have hσ : 0 ≤ σ := Finset.sum_nonneg fun l hl => mul_nonneg (hS l hl).2 (Real.log_natCast_nonneg l)
  set H' := H.pull π₀ hπ₀
  set M : R → HermLB V'.p := fun r => (L r).pull π hπ
  set M₀ : R → HermLB V'.p := fun r => (L₀ r).pull π₀ hπ₀
  have hx : wtCl (amp.pull π hπ) k M u t ∈ cone num' G := by
    rw [wtCl, sub_eq_add_neg]
    exact add_mem_cone (smul_mem_cone (div_nonneg ht.1 (Nat.cast_nonneg _))
      (nef (GlobalTheory.T.nef_fibre_of_norms_power hP F Y ab hab V' _ k hk (i₁ _ _ _ ha)))) (hnef V' M (fun r => i₁ _ _ _ (hL r)) num' hn')
  have hh : pullCl π₀ hπ₀ h0 ∈ cone num' G := by
    rw [hh0, map_smul, pullCl_cl]
    exact smul_mem_cone (Nat.cast_nonneg _) (nef nH)
  have hy : wtCl (amp₀.pull π₀ hπ₀) k₀ M₀ u t + pullCl π₀ hπ₀ h0 ∈ cone num' G := by
    have e : wtCl (amp₀.pull π₀ hπ₀) k₀ M₀ u t + pullCl π₀ hπ₀ h0 = (t / k₀) • cl (amp₀.pull π₀ hπ₀) +
        ∑ r, (((1 - u r) / 2) • (cl H' + cl (M₀ r)) + ((1 + u r) / 2) • (cl H' - cl (M₀ r))) := by
      have e' (r) : ((1 - u r) / 2) • (cl H' + cl (M₀ r)) + ((1 + u r) / 2) • (cl H' - cl (M₀ r)) =
          cl H' - u r • cl (M₀ r) := by module
      rw [Finset.sum_congr rfl fun r _ => e' r, hh0, map_smul, pullCl_cl, wtCl, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, Nat.cast_smul_eq_nsmul]
      exact (sub_add_eq_add_sub _ _ _).trans (add_sub_assoc _ _ _)
    rw [e]
    refine add_mem_cone (smul_mem_cone (div_nonneg ht.1 (Nat.cast_nonneg _))
      (nef (GlobalTheory.T.nef_fibre_of_norms_power hP F Y ab hab V' _ k₀ hk₀ (i₀ _ _ _ ha₀)))) (sum_mem_cone _ fun r _ => ?_)
    have hr := abs_le.1 (hu r)
    refine add_mem_cone (smul_mem_cone (by linarith) (mem_cone_of_rad (nef (nL r).1) ?_))
      (smul_mem_cone (by linarith) (mem_cone_of_rad (nef (nL r).2) ?_))
    · rw [← neg_sub]
      exact neg_mem (rt _ _)
    · have := add_mem (rt H' (M₀ r).dual) (rd (M₀ r))
      rw [← neg_sub]
      refine neg_mem ?_
      convert this using 1
      abel
  have hab' : ab = { ab with lg := ab.lg } := rfl
  have key := GlobalTheory.T.arith_form_difference_bound _ D num' hs' G (cl (oneB V'.p)) _ _ _ ((∑ r, |u r|) * σ) hx hy hh (fun N hN => by
    choose N' hN' e using hN
    obtain rfl : N = fun j => cl (N' j) := funext fun j => (e j).symm
    rw [wtCl_sub _ _ hk hk₀, cons_comb]
    have z := vert hP V' hD num' hn' ab ab _ _ k k₀ hab' (i₁ _ _ _ ha) (i₀ _ _ _ ha₀) ∅ 0 (by simp)
      (by simp) N' (by simp)
    simp only [Finset.sum_empty, mul_zero, zero_mul, abs_nonpos_iff] at z
    rw [z, mul_zero, zero_sub, abs_neg, Finset.sum_mul, Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r _ => ?_)
    rw [abs_mul, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    simpa using vert hP V' hD num' hn' (ρ r) (ρ₀ r) _ _ 1 1 (hρ r) (i₁ _ _ _ (hL r))
      (i₀ _ _ _ (h₀ r)) S a hS (hlg r) N' hN') (fun v j => by
    rw [wtCl_sub _ _ hk hk₀, update_comb,
      vertDeg hP V' hD num' hn' ab ab _ _ k k₀ hab' (i₁ _ _ _ ha) (i₀ _ _ _ ha₀)]
    simp only [fun r => vertDeg hP V' hD num' hn' (ρ r) (ρ₀ r) _ _ 1 1 (hρ r) (i₁ _ _ _ (hL r))
      (i₀ _ _ _ (h₀ r)) v j, M, M₀, mul_zero, Finset.sum_const_zero, sub_zero])
  set e₁ : ℝ := (π.residueDegree (genericPoint V'.X) : ℝ)
  set e₀ : ℝ := (π₀.residueDegree (genericPoint V'.X) : ℝ)
  have hb (i : Fin (D + 1)) : num' (Fin.cons (cl (oneB V'.p)) fun j : Fin D => if (j : ℕ) < i then
      wtCl (amp₀.pull π₀ hπ₀) k₀ M₀ u t else wtCl (amp₀.pull π₀ hπ₀) k₀ M₀ u t + (2 : ℝ) • pullCl π₀ hπ₀ h0) ≤ e₀ * C i := by
    have h₁ := hC i (Fin.cons 0 fun _ o => o.elim t u) fun j o => by
      refine Fin.cases (by simp) (fun j => ?_) j
      cases o
      · simpa [abs_of_nonneg ht.1] using ht.2
      · simpa using hu _
    refine le_of_eq_of_le ?_ (mul_le_mul_of_nonneg_left ((le_abs_self _).trans h₁) (Nat.cast_nonneg _))
    rw [← p₀]
    refine map_congr_rad num' fun j => Fin.cases ?_ (fun j => ?_) j
    · rw [← neg_sub]
      refine neg_mem ?_
      simpa using o₀
    · have e : ∑ o : Option R, (o.elim t u : ℝ) • (o.elim (((1 : ℝ) / k₀) • cl amp₀) fun r => -cl (L₀ r) : Cl V₀.p) =
          wtCl amp₀ k₀ L₀ u t := by
        simp [Fintype.sum_option, wtCl, smul_smul, sub_eq_add_neg, div_eq_mul_inv]
      simp only [Fin.cons_succ, e, map_add, pullCl_wtCl]
      split_ifs
      · simp [M₀]
      · simp [M₀, add_comm]
  rw [← pullCl_wtCl, ← pullCl_wtCl, p₁, p₀] at key
  have hsum : ∑ r, |u r| ≤ Fintype.card R := by simpa using Finset.sum_le_sum fun r (_ : r ∈ Finset.univ) => hu r
  have hC0 : 0 ≤ ∑ i, C i := Finset.sum_nonneg fun i _ => (abs_nonneg _).trans (hC i 0 (by simp))
  have k2 := key.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => by
    simpa only [pullCl_wtCl] using hb i) (mul_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) hσ))
  rw [← Finset.mul_sum] at k2
  have c₁ : e₁ * V.deg = V'.deg := by simp only [e₁]; exact_mod_cast d₁
  have c₀ : e₀ * V₀.deg = V'.deg := by simp only [e₀]; exact_mod_cast d₀
  have b₁ : (0 : ℝ) < V.deg := Nat.cast_pos.2 V.deg_pos
  have b₀ : (0 : ℝ) < V₀.deg := Nat.cast_pos.2 V₀.deg_pos
  have b' : (0 : ℝ) < V'.deg := Nat.cast_pos.2 hd'
  have f₀ : 0 ≤ e₀ := Nat.cast_nonneg _
  have q (x e d : ℝ) (hd : 0 < d) (h : e * d = V'.deg) : x / d = e * x / V'.deg := by
    rw [div_eq_div_iff hd.ne' b'.ne', ← h]; ring
  rw [q _ _ _ b₁ c₁, q _ _ _ b₀ c₀, q _ _ _ b₀ c₀, ← sub_div, abs_div, abs_of_pos b', div_mul_eq_mul_div]
  refine div_le_div_of_nonneg_right (k2.trans ?_) b'.le
  calc _ = (∑ r, |u r|) * (σ * (e₀ * ∑ i, C i)) := by ring
    _ ≤ Fintype.card R * (σ * (e₀ * ∑ i, C i)) := mul_le_mul_of_nonneg_right hsum (by positivity)
    _ = _ := by ring

end GlobalTheory.VertObj

namespace GlobalTheory.VertObj

theorem dominant_mem_cone {E : Type 1} [AddCommGroup E] [Module ℝ E] {D : ℕ} {num : Form E D} {G : Set E} {T : Type}
    [Fintype T] {N : ℕ} (z : T × Fin N → E)
    (h : ∀ n : T → Fin N → ℤ, (∀ τ, Antitone (n τ)) → -∑ x : T × Fin N, (n x.1 x.2 : ℝ) • z x ∈ cone num G)
    (u : T → Fin N → ℝ) (hu : ∀ τ, Antitone (u τ)) : -∑ x : T × Fin N, u x.1 x.2 • z x ∈ cone num G := by
  have e : -∑ x : T × Fin N, u x.1 x.2 • z x =
      ∑ τ, ∑ i, ShFam.coef u τ i • (-∑ x : T × Fin N, ShFam.fund τ i x.1 x.2 • z x) := by
    simp only [smul_neg, Finset.sum_neg_distrib, Finset.smul_sum, smul_smul, neg_inj]
    rw [Finset.sum_congr rfl fun τ _ => Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [← Finset.sum_smul, ShFam.sum_coef_fund]
  rw [e]
  refine sum_mem_cone _ fun τ _ => sum_mem_cone _ fun i _ => ?_
  have key (s : ℤ) (hs : 0 ≤ s ∨ ¬ (i : ℕ) + 1 < N) :
      (s : ℝ) • (-∑ x : T × Fin N, ShFam.fund τ i x.1 x.2 • z x) ∈ cone num G := by
    have := h (fun τ' a => if τ' = τ ∧ a ≤ i then s else 0) fun τ' a b hab => by
      have := a.2
      have := b.2
      have : (a : ℕ) ≤ b := hab
      have := i.2
      by_cases hτ : τ' = τ
      · simp only [hτ, true_and, Fin.le_def]
        split_ifs <;> omega
      · simp [hτ]
    convert this using 1
    simp only [smul_neg, Finset.smul_sum, smul_smul, ShFam.fund]
    refine congrArg _ (Finset.sum_congr rfl fun x _ => ?_)
    split_ifs <;> simp
  rcases le_total 0 (ShFam.coef u τ i) with hc | hc
  · simpa using smul_mem_cone hc (key 1 (.inl zero_le_one))
  · by_cases hi : (i : ℕ) + 1 < N
    · rw [le_antisymm hc (ShFam.coef_nonneg hu τ hi), zero_smul]
      exact zero_mem_cone
    · simpa using smul_mem_cone (neg_nonneg.2 hc) (key (-1) (.inr hi))

theorem top_eq (hA : GlobalTheory.Published.ArCalc) {D : D7} {O : Setup D} {T : Real0 O.Y} {c : O.s.Comp} (I : ManIs (T.M c) (O.var c))
    {B : ℝ} (W : O.LatModel (FlagAr.setB O.Y B) c) (hnum : O.NumIs I B W) (num : Form (Cl W.V.p) (WeightThresholdDefs.dimY O.Y))
    (hn : IsArForm _ num) (u : GlobalTheory.Mean4.Wt O.Y) (s : ℝ) :
    (T.K B c).top (T.L B c u + s • T.a B c) = (Module.finrank ℚ D.what₂.LL : ℝ)⁻¹ *
      (num (fun _ => wtCl W.amp W.k (W.root (FlagAr.setB O.Y B)) (fun x => u x.1 x.2) (s / ((O.met.ab c).n : ℕ))) /
        W.V.deg) := by
  have hdim : (O.var c).dim = WeightThresholdDefs.dimY O.Y := O.dim_eq c
  have ar : IsArithVar W.V.p (WeightThresholdDefs.dimY O.Y) := hdim ▸ W.V.ar
  obtain ⟨ε, π, hd⟩ := W.V.exists_isDown I
  have e0 : (T.M c).pull ε π ((2 : ℝ) • 0) = fun _ _ => 0 := by rw [smul_zero]; rfl
  have hu : ∀ σ z, CxPts.CInfAt ((T.M c).pull ε π ((2 : ℝ) • 0) σ) z := by
    rw [e0]; exact fun _ z => CxPts.cInfAt_const 0 z
  have hc : ∀ σ σ', (Weight.ofFun ((T.M c).pull ε π ((2 : ℝ) • 0) σ)).IsConj
      (Weight.ofFun ((T.M c).pull ε π ((2 : ℝ) • 0) σ')) := by
    rw [e0]; exact fun _ _ _ _ _ _ _ => rfl
  obtain ⟨Φ, hΦ⟩ := ((hA.arExists _ _ W.V.p _ ar).2 _
    fun o : Option (Option (DV.Rt D.what₂.Tau O.N)) => o.elim (fnB _ hu hc) (W.gens (FlagAr.setB O.Y B))).1
  let a : Option (Option (DV.Rt D.what₂.Tau O.N)) → ℝ := fun o => o.elim 0 fun o => o.elim (s / W.mult) fun x => u x.1 x.2
  have k1 := hnum ε π hd 0 (fun σ j => contDiffOn_const) hu hc Φ hΦ a
  have k2 := hn _ _ Φ hΦ fun _ => a
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, k1] at k2
  have hm : (W.mult : ℝ) ≠ 0 := Nat.cast_ne_zero.2 W.mult_pos.ne'
  have e1 : ∑ i, a (some i) • T.gen B c W.mult i + a none • (T.K B c).ar 0 = T.L B c u + s • T.a B c := by
    have : T.L B c u = ∑ x : D.what₂.Tau × Fin O.Y.N, u x.1 x.2 • T.L B c (Pi.single x.1 (Pi.single x.2 1)) := by
      simp only [← map_smul, ← map_sum]
      congr 1
      funext τ i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single (τ, i)]
      · simp
      · rintro ⟨τ', i'⟩ _ hne
        by_cases h₁ : τ = τ'
        · subst h₁
          have : i ≠ i' := fun h₂ => hne (by rw [h₂])
          simp [this]
        · simp [h₁]
      · simp
    rw [this, Fintype.sum_option]
    simp only [a, Real0.gen, Option.elim, zero_smul, add_zero, smul_smul, div_mul_cancel₀ _ hm]
    exact add_comm _ _
  obtain ⟨-, rd, -, -⟩ := GlobalTheory.T.arith_class_form_properties hA _ _ W.V.p _ ar num hn
  rw [e1, map_congr_rad num (w := fun _ => wtCl W.amp W.k (W.root (FlagAr.setB O.Y B)) (fun x => u x.1 x.2)
    (s / ((O.met.ab c).n : ℕ))) fun _ => ?_] at k2
  · rw [← k2, Cover.ν]
    have : (W.V.deg : ℝ) ≠ 0 := Nat.cast_ne_zero.2 W.V.deg_pos.ne'
    have : (Module.finrank ℚ D.what₂.LL : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
    field_simp
  · have := Submodule.sum_mem (rad num) (t := Finset.univ) fun (x : DV.Rt D.what₂.Tau O.N) _ =>
      Submodule.smul_mem _ (u x.1 x.2) (rd (W.root (FlagAr.setB O.Y B) x))
    convert this using 1
    simp only [Fintype.sum_option, a, Option.elim, zero_smul, zero_add, Setup.LatModel.gens, wtCl, Setup.LatModel.mult,
      smul_add, Finset.sum_add_distrib, Nat.cast_mul, div_div, mul_comm (W.k : ℝ)]
    abel

end GlobalTheory.VertObj

namespace GlobalTheory.VertObj

theorem log_div_pred_nonneg (p : ℕ) : 0 ≤ Real.log p / ((p : ℝ) - 1) := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp
  · have : (1 : ℝ) ≤ p := by exact_mod_cast hp
    exact div_nonneg (Real.log_natCast_nonneg p) (by linarith)

theorem sum_diff_le (D : D7) (Y : DV.ShimX D.what₂.Tau) (B : ℝ) (hB : 2 ≤ B) :
    ∑ p ∈ GlobalTheory.FlagAr.setB Y B \ GlobalTheory.FlagAr.setB Y 2, Real.log p / ((p : ℝ) - 1) ≤
      (1 + 3 / Real.log 2) * Real.log B := by
  have hsub : GlobalTheory.FlagAr.setB Y B \ GlobalTheory.FlagAr.setB Y 2 ⊆ Finset.filter Nat.Prime (Finset.range (⌊B⌋₊ + 1)) := by
    intro p hp
    simp only [GlobalTheory.FlagAr.setB, Finset.mem_sdiff, Finset.mem_union] at hp
    tauto
  have h1 := Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => log_div_pred_nonneg p
  have h2 := GlobalTheory.PrimeLogSum.sum_log_div_pred_le_real B (by linarith)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlB : Real.log 2 ≤ Real.log B := Real.log_le_log (by norm_num) hB
  have h3 : 3 ≤ 3 / Real.log 2 * Real.log B := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hl2]; nlinarith
  calc _ ≤ _ := h1
    _ ≤ Real.log B + 3 := h2
    _ ≤ _ := by nlinarith

theorem root0_eq_with_lg_of_primes {D : D7} (O : Setup D) (c : O.s.Comp) (Q Q' : Finset ℕ) (x : DV.Rt D.what₂.Tau O.N) :
    O.root0 c Q' x = { O.root0 c Q x with lg := (O.root0 c Q' x).lg } := by
  have key (n n' : Letter O.S.Dw → ℤ) (h : n = n') (lg) :
      (⟨divOf (O.Φ.C c) n, 1, fun σ => O.met.h0 c σ n, 0, lg⟩ : Adl (cxSt D.what₂.LL) (O.var c)) =
        ⟨divOf (O.Φ.C c) n', 1, fun σ => O.met.h0 c σ n', 0, lg⟩ := by rw [h]
  exact key _ _ ((expo_rootSym _ _ _ _ _).trans (expo_rootSym _ _ _ _ _).symm) _

theorem top_sub_le : Hypotheses2 → HypothesesH → OnObj fun _ O _ T _ _ => ∃ C : ℝ, ∀ B : ℝ, 2 ≤ B →
    ∀ (c : O.Y.Comp) (u : GlobalTheory.Mean4.Wt O.Y), WeightThresholdDefs.Dominant O.Y u → ‖u‖ ≤ 1 → ∀ s ∈ Set.Icc (0 : ℝ) 1,
      |(T.K B c).top (T.L B c u + s • T.a B c) - (T.K 2 c).top (T.L 2 c u + s • T.a 2 c)| ≤
        C * ∑ p ∈ GlobalTheory.FlagAr.setB O.Y B \ GlobalTheory.FlagAr.setB O.Y 2, Real.log p / ((p : ℝ) - 1) := by
  intro h1 h2 D O hO hf A T H h
  have hA := h1.p4
  have hdim (c : O.s.Comp) : (O.var c).dim = WeightThresholdDefs.dimY O.Y := O.dim_eq c
  have ar (c : O.s.Comp) (V : Cover (O.var c)) : IsArithVar V.p (WeightThresholdDefs.dimY O.Y) := hdim c ▸ V.ar
  have hab (c : O.s.Comp) : (O.met.ab c).NefFib := by
    obtain ⟨x, P, hc⟩ := hO
    rw [hc.ab_eq]
    exact P.nefFib_ab c
  choose num hn _ using fun (c : O.s.Comp) (V : Cover (O.var c)) => GlobalTheory.T.arith_intersection_form_exists hA _ _ V.p _ (ar c V)
  choose C hC using fun c : O.s.Comp => general h1 (hdim c) (O.met.ab c) (hab c) (h.mdl (FlagAr.setB O.Y 2) c).V
    (O.root0 c (FlagAr.setB O.Y 2)) _ (fun x => norms_of_induces (Setup.induces_root0 D O hO.dualRef _ c _ _ subset_rfl x)) _
    (h.mdl _ c).k_pos (norms_of_induces (h.mdl _ c).amp_spec) _ (hn c _)
  refine ⟨∑ c : O.Y.Comp, |C c|, fun B hB c u hu hu1 s hs => ?_⟩
  have hsub : FlagAr.setB O.Y 2 ⊆ FlagAr.setB O.Y B :=
    Finset.union_subset_union_left (Finset.filter_subset_filter _
      (Finset.range_mono (Nat.succ_le_succ (Nat.floor_le_floor hB))))
  have hdisc : (NumberField.discr D.host.E).natAbs.primeFactors ⊆ FlagAr.setB O.Y 2 :=
    (Nat.primeFactors_mono (dvd_mul_left _ 2) (mul_ne_zero two_ne_zero
      (Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero _)))).trans (Finset.subset_union_left.trans Finset.subset_union_right)
  have hpr : ∀ l ∈ FlagAr.setB O.Y B \ FlagAr.setB O.Y 2, l.Prime := fun l hl => by
    simp only [FlagAr.setB, Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter] at hl
    tauto
  have hn1 : (1 : ℝ) ≤ ((O.met.ab c).n : ℕ) := by exact_mod_cast (O.met.ab c).n.2
  have key := hC c (h.mdl (FlagAr.setB O.Y B) c).V (O.root0 c (FlagAr.setB O.Y B)) _
    (fun x => norms_of_induces (Setup.induces_root0 D O hO.dualRef _ c _ _ subset_rfl x)) _ _ (h.mdl _ c).k_pos (norms_of_induces (h.mdl _ c).amp_spec) _ (hn c _)
    (FlagAr.setB O.Y B \ FlagAr.setB O.Y 2) (fun l => 1 / ((l : ℝ) - 1))
    (fun l hl => ⟨hpr l hl, div_nonneg zero_le_one (sub_nonneg.2 (by exact_mod_cast (hpr l hl).one_le))⟩)
    (root0_eq_with_lg_of_primes O c _ _) (abs_lg_root0_sub_le D O c _ _ hsub hdisc) (fun x => u x.1 x.2) (s / ((O.met.ab c).n : ℕ))
    (fun x => ((norm_le_pi_norm (u x.1) x.2).trans (norm_le_pi_norm u x.1)).trans hu1)
    ⟨div_nonneg hs.1 (by linarith), (div_le_one (by linarith)).2 (hs.2.trans hn1)⟩ fun V' L' hL' num' hn' => by
      refine dominant_mem_cone (fun x => cl (L' x)) (fun n hn => ?_) u fun τ a b hab => hu τ a b hab
      refine mem_cone_of_rad (mem_cone_of_mem ⟨_, fun l hl => GlobalTheory.T.nef_over_antitone_comb h1 h2 D O hO hf A T H h c _ V' L'
        (fun x => (hL' x).congr (fun _ => pow_one _) (fun _ _ => by simp) fun _ _ _ => by simp) n hn l
        (Finset.mem_sdiff.1 hl).1 (hpr l hl), rfl⟩) ?_
      rw [← neg_sub]
      refine neg_mem ?_
      simpa using (GlobalTheory.T.arith_class_form_properties hA _ _ V'.p _ (ar c V') num' hn').2.2.2 _ L' fun x => -n x.1 x.2
  rw [top_eq hA _ _ (h.num B hB c) _ (hn c _), top_eq hA _ _ (h.num 2 le_rfl c) _ (hn c _), ← mul_sub, abs_mul]
  have hS := Finset.sum_nonneg fun p (_ : p ∈ GlobalTheory.FlagAr.setB O.Y B \ GlobalTheory.FlagAr.setB O.Y 2) => log_div_pred_nonneg p
  have hF : (1 : ℝ) ≤ Module.finrank ℚ D.what₂.LL := by exact_mod_cast Module.finrank_pos
  refine (mul_le_of_le_one_left (abs_nonneg _) ?_).trans (key.trans ?_)
  · rw [abs_of_nonneg (by positivity)]
    exact inv_le_one_of_one_le₀ hF
  · simp only [one_div_mul_eq_div]
    exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun c : O.Y.Comp => |C c|) (fun _ _ => abs_nonneg _) (Finset.mem_univ c))) hS

theorem vertBd_onObj : Hypotheses2 → HypothesesH → OnObj fun _ _ _ T _ _ => VertBd T := by
  intro h1 h2 D O hc hf A T H h
  obtain ⟨C, hC⟩ := top_sub_le h1 h2 D O hc hf A T H h
  have hsm := GlobalTheory.InterpChgSmooth.smooth_phR h1 h2 D O hc hf A T H h
  refine ⟨max C 0 * (1 + 3 / Real.log 2), fun B hB c u hu hn s hs R hR => ?_⟩
  have hR2 : 2 ≤ R := by linarith [Real.add_one_le_exp (2 : ℝ)]
  rw [fR_sub_eq_top_sub D O.Y T B 2 c u s R fun σ => hsm c u σ R hR2]
  have h3 := hC B hB c u hu hn s hs
  have hS := sum_diff_le D O.Y B hB
  have hS0 := Finset.sum_nonneg fun p (_ : p ∈ GlobalTheory.FlagAr.setB O.Y B \ GlobalTheory.FlagAr.setB O.Y 2) =>
    log_div_pred_nonneg p
  calc _ ≤ C * _ := h3
    _ ≤ max C 0 * _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hS0
    _ ≤ max C 0 * ((1 + 3 / Real.log 2) * Real.log B) := mul_le_mul_of_nonneg_left hS (le_max_right _ _)
    _ = _ := by ring

end GlobalTheory.VertObj

end
