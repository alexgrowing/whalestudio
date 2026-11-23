import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ConstantCoeffAddSecondThird
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.MulGenScaleRight
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.JetSubstPSTrunc

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2c

open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix ReciprocityTheory.ChartRestriction.G.TB Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2b
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw FB)
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing (ev_ev ev_X hasSubst_pts exp_add subst_exp exp_zero)

section Series

variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}

private lemma cc_pt_lemma {n : ℕ} (j : Fin n) (i : Fin d) :
    MvPowerSeries.constantCoeff (pt S d j i) = 0 := by
  simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt]

private lemma cc_logOf_lemma_2 (G : FGLaw S d) (i : Fin d) :
    MvPowerSeries.constantCoeff (ReciprocityTheory.ChartRestriction.G.TB.LogPf.logOf G i) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  show ReciprocityTheory.ChartRestriction.G.TB.LogPf.prim _ 0 = 0
  simp [ReciprocityTheory.ChartRestriction.G.TB.LogPf.prim]

private lemma germEval_oneStandardPoint_self_lemma_3 {n : ℕ} (b : Fin 2 → Pt S n d)
    (hb : ∀ j i, MvPowerSeries.constantCoeff (b j i) = 0) (j : Fin 2) (f : PS S 1 d) :
    ev b (ev (n := 2) ![pt S d j] f) = ev ![b j] f := by
  rw [ev_ev _ _ (fun j' i => by fin_cases j'; exact cc_pt_lemma j i) hb]
  congr 1
  funext j' i
  fin_cases j'
  exact ev_X b hb j i

private lemma ev_hom_lemma_4 {m n : ℕ} (a : Fin m → Pt S n d)
    (ha : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0) (f : PS S m d) :
    ev a f = MvPowerSeries.substAlgHom (hasSubst_pts a ha) f := by
  rw [MvPowerSeries.coe_substAlgHom]
  rfl

private lemma ev_neg_lemma_5 {m n : ℕ} (a : Fin m → Pt S n d)
    (ha : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0) (f : PS S m d) :
    ev a (-f) = -ev a f := by
  rw [ev_hom_lemma_4 a ha, ev_hom_lemma_4 a ha, map_neg]

private lemma eval_expSeries {m n : ℕ} (a : Fin m → Pt S n d)
    (ha : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0) (f : PS S m d)
    (hf : MvPowerSeries.constantCoeff f = 0) : ev a (expP f) = expP (ev a f) :=
  subst_exp (fun p : Fin m × Fin d => a p.1 p.2) (fun s => ha s.1 s.2) hf

private lemma cc_lg_lemma_7 {n : ℕ} (G : FGLaw S d) (j : Fin n) (i : Fin d) :
    MvPowerSeries.constantCoeff (Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix.lg G j i) = 0 :=
  ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.cc_ev (a := ![pt S d j])
    (fun j' i' => by fin_cases j'; exact cc_pt_lemma j i') (cc_logOf_lemma_2 G i)

private lemma cc_bilL_lemma_8 (G : FGLaw S d) (c : Fin d → Fin d → S) :
    MvPowerSeries.constantCoeff (bilL G c) = 0 := by
  simp [Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix.bilL, MvPowerSeries.smul_eq_C_mul, cc_lg_lemma_7]

private lemma ev_bilL_lemma_9 {n : ℕ} (G : FGLaw S d) (c : Fin d → Fin d → S) (x y : Pt S n d)
    (ha : ∀ j i, MvPowerSeries.constantCoeff ((![x, y] : Fin 2 → Pt S n d) j i) = 0) :
    ev ![x, y] (bilL G c) = ∑ i, ∑ l, c i l •
      (ev ![x] (ReciprocityTheory.ChartRestriction.G.TB.LogPf.logOf G i) * ev ![y] (ReciprocityTheory.ChartRestriction.G.TB.LogPf.logOf G l)) := by
  have key : ∀ f, ev ![x, y] f = MvPowerSeries.substAlgHom (hasSubst_pts _ ha) f :=
    fun f => ev_hom_lemma_4 _ ha f
  have hl : ∀ (j : Fin 2) i, ev ![x, y] (Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix.lg G j i) =
      ev ![(![x, y] : Fin 2 → Pt S n d) j] (ReciprocityTheory.ChartRestriction.G.TB.LogPf.logOf G i) :=
    fun j i => germEval_oneStandardPoint_self_lemma_3 _ ha j _
  rw [key]
  unfold Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix.bilL
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_smul, map_mul, ← key, ← key, hl, hl]
  all_goals rfl

theorem formal_log_add_first_two (G : FGLaw S d) (l : Fin d) :
    ev (n := 3) ![G.add (pt S d 0) (pt S d 1)] (LogPf.logOf G l) =
      ev (n := 3) ![pt S d 0] (LogPf.logOf G l) + ev (n := 3) ![pt S d 1] (LogPf.logOf G l) := by
  have hb : ∀ j i, MvPowerSeries.constantCoeff ((![pt S d 0, pt S d 1] : Fin 2 → Pt S 3 d) j i) = 0 := by
    intro j i
    fin_cases j
    · exact cc_pt_lemma _ i
    · exact cc_pt_lemma _ i
  have hF : ∀ j i, MvPowerSeries.constantCoeff ((![G.F] : Fin 1 → Pt S 2 d) j i) = 0 := by
    intro j i
    fin_cases j
    exact G.const i
  have e1 : ev (n := 3) ![G.add (pt S d 0) (pt S d 1)] (LogPf.logOf G l) =
      ev ![pt S d 0, pt S d 1] (ev (n := 2) ![G.F] (LogPf.logOf G l)) := by
    rw [ev_ev _ _ hF hb]
    congr 1
    funext j i
    fin_cases j
    rfl
  rw [e1, ReciprocityTheory.ChartRestriction.G.TB.LogPf.logOf_add (G := G), ev_hom_lemma_4 _ hb, map_add,
    ← ev_hom_lemma_4 _ hb, ← ev_hom_lemma_4 _ hb, germEval_oneStandardPoint_self_lemma_3 _ hb, germEval_oneStandardPoint_self_lemma_3 _ hb]
  all_goals rfl

theorem constantCoeff_add_first_second (G : FGLaw S d) (i : Fin d) :
    MvPowerSeries.constantCoeff (G.add (pt S (n := 3) d 0) (pt S d 1) i) = 0 :=
  ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.cc_ev (a := ![pt S d 0, pt S d 1]) (f := G.F i)
    (fun j i' => by fin_cases j <;> exact cc_pt_lemma _ i') (G.const i)

theorem twist_mul_first_argument (G : FGLaw S d) (cc : Fin d → Fin d → S) :
    ev (n := 3) ![G.add (pt S d 0) (pt S d 1), pt S d 2] (expP (-bilL G cc)) =
      ev (n := 3) ![pt S d 0, pt S d 2] (expP (-bilL G cc)) * ev (n := 3) ![pt S d 1, pt S d 2] (expP (-bilL G cc)) := by
  have ha : ∀ j i, MvPowerSeries.constantCoeff
      ((![G.add (pt S d 0) (pt S d 1), pt S d 2] : Fin 2 → Pt S 3 d) j i) = 0 := by
    intro j i
    fin_cases j
    · exact constantCoeff_add_first_second G i
    · exact cc_pt_lemma _ i
  have h0 : ∀ j i, MvPowerSeries.constantCoeff ((![pt S d 0, pt S d 2] : Fin 2 → Pt S 3 d) j i) = 0 := by
    intro j i
    fin_cases j
    · exact cc_pt_lemma _ i
    · exact cc_pt_lemma _ i
  have h1 : ∀ j i, MvPowerSeries.constantCoeff ((![pt S d 1, pt S d 2] : Fin 2 → Pt S 3 d) j i) = 0 := by
    intro j i
    fin_cases j
    · exact cc_pt_lemma _ i
    · exact cc_pt_lemma _ i
  have hB := cc_bilL_lemma_8 G cc
  have hneg : MvPowerSeries.constantCoeff (-bilL G cc) = 0 := by rw [map_neg, hB, neg_zero]
  have hsplit : ev (n := 3) ![G.add (pt S d 0) (pt S d 1), pt S d 2] (bilL G cc) =
      ev (n := 3) ![pt S d 0, pt S d 2] (bilL G cc) + ev (n := 3) ![pt S d 1, pt S d 2] (bilL G cc) := by
    rw [ev_bilL_lemma_9 G cc _ _ ha, ev_bilL_lemma_9 G cc _ _ h0, ev_bilL_lemma_9 G cc _ _ h1,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [formal_log_add_first_two G i, add_mul, smul_add]
  have c0 : MvPowerSeries.constantCoeff (-ev (n := 3) ![pt S d 0, pt S d 2] (bilL G cc)) = 0 := by
    rw [map_neg, ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.cc_ev _ h0 hB, neg_zero]
  have c1 : MvPowerSeries.constantCoeff (-ev (n := 3) ![pt S d 1, pt S d 2] (bilL G cc)) = 0 := by
    rw [map_neg, ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.cc_ev _ h1 hB, neg_zero]
  rw [eval_expSeries _ ha _ hneg, eval_expSeries _ h0 _ hneg, eval_expSeries _ h1 _ hneg,
    ev_neg_lemma_5 _ ha, ev_neg_lemma_5 _ h0, ev_neg_lemma_5 _ h1, hsplit, neg_add]
  exact exp_add c0 c1

theorem twist_sym (G : FGLaw S d) (cc : Fin d → Fin d → S) (hs : ∀ i l, cc i l = cc l i) :
    ev (n := 2) ![pt S d 1, pt S d 0] (expP (-bilL G cc)) = expP (-bilL G cc) := by
  have ha : ∀ j i, MvPowerSeries.constantCoeff ((![pt S d 1, pt S d 0] : Fin 2 → Pt S 2 d) j i) = 0 := by
    intro j i
    fin_cases j
    · exact cc_pt_lemma _ i
    · exact cc_pt_lemma _ i
  have hneg : MvPowerSeries.constantCoeff (-bilL G cc) = 0 := by
    rw [map_neg, cc_bilL_lemma_8 G cc, neg_zero]
  have hsw : ev (n := 2) ![pt S d 1, pt S d 0] (bilL G cc) = bilL G cc := by
    rw [ev_bilL_lemma_9 G cc _ _ ha]
    conv_rhs => rw [Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix.bilL]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
    rw [hs l i, mul_comm] <;> rfl
  rw [eval_expSeries _ ha _ hneg, ev_neg_lemma_5 _ ha, hsw]

theorem bilL_add (G : FGLaw S d) (c c' : Fin d → Fin d → S) : bilL G (c + c') = bilL G c + bilL G c' := by
  simp only [Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix.bilL, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem bilL_zero (G : FGLaw S d) : bilL G 0 = 0 := by
  simp [Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix.bilL]

theorem twist_add (G : FGLaw S d) (c c' : Fin d → Fin d → S) :
    expP (-bilL G (c + c')) = expP (-bilL G c) * expP (-bilL G c') := by
  rw [bilL_add, neg_add]
  exact exp_add (by rw [map_neg, cc_bilL_lemma_8, neg_zero]) (by rw [map_neg, cc_bilL_lemma_8, neg_zero])

theorem twist_zero (G : FGLaw S d) : expP (-bilL G 0) = 1 := by
  rw [bilL_zero, neg_zero]
  exact exp_zero

end Series

section Jet

variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}

private lemma mkX_lemma_10 {ι : Type} [Fintype ι] [DecidableEq ι] (m : ℕ) (s : ι) :
    Ideal.Quotient.mk (Formalism.L2.Pj.orig S ι ^ (m + 1)) (MvPolynomial.X s) =
      psJet m (MvPowerSeries.X s : MvPowerSeries ι S) := by
  unfold Formalism.L2.Pj.psJet
  rw [Ideal.Quotient.eq]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [zero_add, pow_one]
    refine Ideal.sub_mem _ (Ideal.subset_span ⟨s, rfl⟩) ?_
    exact Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.psTrunc_mem_orig 0 _ (MvPowerSeries.constantCoeff_X s)
  · have hmem : (Finsupp.single s 1 : ι →₀ ℕ) ∈ Formalism.L2.Pj.degLE m := by
      unfold Formalism.L2.Pj.degLE
      rw [Finset.mem_filter, Finset.mem_image]
      refine ⟨⟨fun i => ⟨if i = s then 1 else 0, by split_ifs <;> omega⟩, Finset.mem_univ _, ?_⟩, ?_⟩
      · ext i
        by_cases h : i = s
        · subst h
          simp
        · simp [h, Ne.symm h, Finsupp.single_apply]
      · rw [Finsupp.sum_single_index rfl]
        exact hm
    have htr : Formalism.L2.Pj.psTrunc m (MvPowerSeries.X s : MvPowerSeries ι S) = MvPolynomial.X s := by
      unfold Formalism.L2.Pj.psTrunc
      rw [Finset.sum_eq_single_of_mem _ hmem
        (fun b _ hb => by rw [MvPowerSeries.coeff_X, if_neg hb, map_zero])]
      rw [MvPowerSeries.coeff_X, if_pos rfl]
      rfl
    rw [htr, sub_self]
    exact Ideal.zero_mem _

private lemma jetSubstP_mk_eq_mk_aeval {κ κ' : Type} (m : ℕ) (φ : κ → MvPolynomial κ' S) (P : MvPolynomial κ S) :
    jetSubstP m φ (Ideal.Quotient.mk (Formalism.L2.Pj.orig S κ ^ (m + 1)) P) =
      Ideal.Quotient.mk (Formalism.L2.Pj.orig S κ' ^ (m + 1))
        (MvPolynomial.aeval (fun i => φ i - MvPolynomial.C (MvPolynomial.constantCoeff (φ i))) P) :=
  rfl

private lemma ccOrig_lemma_12 {κ : Type} (P : MvPolynomial κ S) (hP : P ∈ Formalism.L2.Pj.orig S κ) :
    MvPolynomial.constantCoeff P = 0 := by
  have hle : Formalism.L2.Pj.orig S κ ≤ RingHom.ker (MvPolynomial.constantCoeff (σ := κ) (R := S)) := by
    unfold Formalism.L2.Pj.orig
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp
  exact hle hP

private lemma mkIn_lemma_13 (G : FGLaw S d) (m : ℕ) (j : Fin d) :
    Ideal.Quotient.mk (Formalism.L2.Pj.orig S (Fin 3 × Fin d) ^ (m + 1)) (psIn d m ![0, 1] (G.F j)) =
      psJet m (G.add (pt S (n := 3) d 0) (pt S d 1) j) := by
  have hcc : ∀ p : Fin 2 × Fin d,
      MvPowerSeries.constantCoeff ((![pt S d 0, pt S d 1] : Fin 2 → Pt S 3 d) p.1 p.2) = 0 := by
    rintro ⟨j', i'⟩
    fin_cases j'
    · exact cc_pt_lemma _ i'
    · exact cc_pt_lemma _ i'
  have hX : ∀ p : Fin 2 × Fin d, Ideal.Quotient.mk (Formalism.L2.Pj.orig S (Fin 3 × Fin d) ^ (m + 1))
      (MvPolynomial.X ((![0, 1] : Fin 2 → Fin 3) p.1, p.2) : MvPolynomial (Fin 3 × Fin d) S) =
        psJet m ((![pt S d 0, pt S d 1] : Fin 2 → Pt S 3 d) p.1 p.2) := by
    rintro ⟨j', i'⟩
    fin_cases j'
    · exact mkX_lemma_10 m _
    · exact mkX_lemma_10 m _
  have e := jetSubstP_psJet (d := d) m
    (fun p : Fin 2 × Fin d => (MvPolynomial.X ((![0, 1] : Fin 2 → Fin 3) p.1, p.2) : MvPolynomial (Fin 3 × Fin d) S))
    (![pt S d 0, pt S d 1] : Fin 2 → Pt S 3 d) hcc (fun p => MvPolynomial.constantCoeff_X S _) hX (G.F j)
  show _ = psJet m (ev (n := 3) ![pt S d 0, pt S d 1] (G.F j))
  rw [← e]
  unfold Formalism.L2.Pj.psJet Formalism.L2.Pj.psIn
  rw [jetSubstP_mk_eq_mk_aeval]
  congr 1
  simp only [MvPolynomial.constantCoeff_X, map_zero, sub_zero]
  have hr : (MvPolynomial.rename fun p : Fin 2 × Fin d => ((![0, 1] : Fin 2 → Fin 3) p.1, p.2) :
      MvPolynomial (Fin 2 × Fin d) S →ₐ[S] MvPolynomial (Fin 3 × Fin d) S) =
      MvPolynomial.aeval fun i : Fin 2 × Fin d => MvPolynomial.X ((![0, 1] : Fin 2 → Fin 3) i.1, i.2) :=
    MvPolynomial.algHom_ext fun i => by rw [MvPolynomial.rename_X, MvPolynomial.aeval_X]
  rw [hr]

theorem twist_mul_first_argument_jet (G : FGLaw S d) (cc : Fin d → Fin d → S) (m : ℕ) :
    jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => psIn d m ![0, 1] (G.F j), fun j => X ((2 : Fin 3), j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) p.1 p.2) (psJet m (expP (-bilL G cc))) =
      jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) p.1 p.2) (psJet m (expP (-bilL G cc))) *
      jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => X ((1 : Fin 3), j), fun j => X ((2 : Fin 3), j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) p.1 p.2) (psJet m (expP (-bilL G cc))) := by
  have hcc : ∀ (x y : Pt S 3 d), (∀ i, MvPowerSeries.constantCoeff (x i) = 0) →
      (∀ i, MvPowerSeries.constantCoeff (y i) = 0) →
      ∀ p : Fin 2 × Fin d, MvPowerSeries.constantCoeff ((![x, y] : Fin 2 → Pt S 3 d) p.1 p.2) = 0 := by
    intro x y hx hy
    rintro ⟨j', i'⟩
    fin_cases j'
    · exact hx i'
    · exact hy i'
  have hpt : ∀ k : Fin 3, ∀ i, MvPowerSeries.constantCoeff ((pt S d k : Pt S 3 d) i) = 0 :=
    fun k i => cc_pt_lemma k i
  have hXc : ∀ (k k' : Fin 3), ∀ p : Fin 2 × Fin d, MvPolynomial.constantCoeff
      ((![fun j => X (k, j), fun j => X (k', j)] : Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) p.1 p.2) = 0 := by
    intro k k'
    rintro ⟨j', i'⟩
    fin_cases j'
    · exact MvPolynomial.constantCoeff_X S _
    · exact MvPolynomial.constantCoeff_X S _
  have hXm : ∀ (k k' : Fin 3), ∀ p : Fin 2 × Fin d, Ideal.Quotient.mk (Formalism.L2.Pj.orig S (Fin 3 × Fin d) ^ (m + 1))
      ((![fun j => X (k, j), fun j => X (k', j)] : Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) p.1 p.2) =
        psJet m ((![pt S d k, pt S d k'] : Fin 2 → Pt S 3 d) p.1 p.2) := by
    intro k k'
    rintro ⟨j', i'⟩
    fin_cases j'
    · exact mkX_lemma_10 m _
    · exact mkX_lemma_10 m _
  have hφ : ∀ p : Fin 2 × Fin d, MvPolynomial.constantCoeff
      ((![fun j => psIn d m ![0, 1] (G.F j), fun j => X ((2 : Fin 3), j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) p.1 p.2) = 0 := by
    rintro ⟨j', i'⟩
    fin_cases j'
    · show MvPolynomial.constantCoeff (MvPolynomial.rename _ _) = 0
      rw [MvPolynomial.constantCoeff_rename]
      exact ccOrig_lemma_12 _ (Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.psTrunc_mem_orig m _ (G.const i'))
    · exact MvPolynomial.constantCoeff_X S _
  have hmk : ∀ p : Fin 2 × Fin d, Ideal.Quotient.mk (Formalism.L2.Pj.orig S (Fin 3 × Fin d) ^ (m + 1))
      ((![fun j => psIn d m ![0, 1] (G.F j), fun j => X ((2 : Fin 3), j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) p.1 p.2) =
        psJet m ((![G.add (pt S d 0) (pt S d 1), pt S d 2] : Fin 2 → Pt S 3 d) p.1 p.2) := by
    rintro ⟨j', i'⟩
    fin_cases j'
    · exact mkIn_lemma_13 G m i'
    · exact mkX_lemma_10 m _
  have hA := hcc (G.add (pt S d 0) (pt S d 1)) (pt S d 2) (fun i => constantCoeff_add_first_second G i) (hpt 2)
  rw [jetSubstP_psJet m _ _ hA hφ hmk, jetSubstP_psJet m _ _ (hcc _ _ (hpt 0) (hpt 2)) (hXc 0 2) (hXm 0 2),
    jetSubstP_psJet m _ _ (hcc _ _ (hpt 1) (hpt 2)) (hXc 1 2) (hXm 1 2), twist_mul_first_argument G cc,
    Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.psJet_mul]

theorem twist_sym_jet (G : FGLaw S d) (cc : Fin d → Fin d → S) (hs : ∀ i l, cc i l = cc l i) (m : ℕ) :
    jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) p.1 p.2) (psJet m (expP (-bilL G cc))) =
      psJet m (expP (-bilL G cc)) := by
  have hcc : ∀ p : Fin 2 × Fin d,
      MvPowerSeries.constantCoeff ((![pt S d 1, pt S d 0] : Fin 2 → Pt S 2 d) p.1 p.2) = 0 := by
    rintro ⟨j', i'⟩
    fin_cases j'
    · exact cc_pt_lemma _ i'
    · exact cc_pt_lemma _ i'
  have hXc : ∀ p : Fin 2 × Fin d, MvPolynomial.constantCoeff
      ((![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) p.1 p.2) = 0 := by
    rintro ⟨j', i'⟩
    fin_cases j'
    · exact MvPolynomial.constantCoeff_X S _
    · exact MvPolynomial.constantCoeff_X S _
  have hXm : ∀ p : Fin 2 × Fin d, Ideal.Quotient.mk (Formalism.L2.Pj.orig S (Fin 2 × Fin d) ^ (m + 1))
      ((![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) p.1 p.2) =
        psJet m ((![pt S d 1, pt S d 0] : Fin 2 → Pt S 2 d) p.1 p.2) := by
    rintro ⟨j', i'⟩
    fin_cases j'
    · exact mkX_lemma_10 m _
    · exact mkX_lemma_10 m _
  rw [jetSubstP_psJet m _ _ hcc hXc hXm, twist_sym G cc hs]

def twU (G : FGLaw S d) (c : Fin d → Fin d → S) (m : ℕ) : (Jet S (Fin 2 × Fin d) m)ˣ where
  val := psJet m (expP (-bilL G c))
  inv := psJet m (expP (-bilL G (-c)))
  val_inv := by rw [← FBIdJet.psJet_mul, ← twist_add, add_neg_cancel, twist_zero, FBIdJet.psJet_one]
  inv_val := by rw [← FBIdJet.psJet_mul, ← twist_add, neg_add_cancel, twist_zero, FBIdJet.psJet_one]

theorem twU_val (G : FGLaw S d) (c : Fin d → Fin d → S) (m : ℕ) :
    (twU G c m : Jet S (Fin 2 × Fin d) m) = psJet m (expP (-bilL G c)) := rfl

end Jet

section Chart

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S)

theorem fixTw [StarRing (𝓞 E)] (C : ChartAt Xo c y) (cc : ℕ → Fin C.d → Fin C.d → S) (h0 : cc 0 = 0)
    (hsym : ∀ m i j, cc m i j = cc m j i)
    (hbal : ∀ m (a : 𝓞 E), Matrix.transpose (dLin (C.B.A.act a)) * Matrix.of (cc m) =
      Matrix.of (cc m) * dLin (C.B.A.act (H.bar a)))
    (hstep : ∀ m, ∃ U : (Jet S (Fin 2 × Fin C.d) m)ˣ,
      (U : Jet S (Fin 2 × Fin C.d) m) = psJet m (expP (-bilL C.B.G (cc m - cc (m + 1)))) ∧
      LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
        (LB.pullGen Xo.univ.t.PP.L _ _ (C.e (m + 1))
          (homAt y.x (jetTrunc : Jet S (Fin 2 × Fin C.d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin C.d) m)).left)
        (scaleGen _ _ (unitΓ U) (C.e m))) :
    ∃ (e' : ∀ m, FrTy y C.d C.x m) (hfr : IsFrame y C.d C.x C.B.G.F C.B.A.act C.B.ph1 C.B.ph2 C.B.sy C.B.ad e')
      (hrig : LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
        (LB.pullGen Xo.univ.t.PP.L _ _ (eL y C.d C.x C.B.A.act e' C.wP 0)
          (homAt y.x (jetAug : Jet S (Fin 1 × Fin C.d) 0 →ₐ[S] S)).left)
        (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt y.x S) 1)),
      FrTruncC y { C with e := e', frame := hfr, rig0 := hrig } ∧
      ∀ m, ∃ u : (Jet S (Fin 2 × Fin C.d) m)ˣ,
        (u : Jet S (Fin 2 × Fin C.d) m) = psJet m (expP (-bilL C.B.G (cc m))) ∧
        LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (e' m) (scaleGen (Xo := Xo) _ _ (unitΓ u) (C.e m)) := by
  choose U hU hc using hstep
  let T : ∀ m, (Jet S (Fin 2 × Fin C.d) m)ˣ := fun m => twU C.B.G (cc m) m
  have hm1 : ∀ m, sub C.d m ![fun j => psIn C.d m ![0, 1] (C.B.G.F j), fun j => X ((2 : Fin 3), j)] (T m) =
      sub C.d m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)] (T m) *
        sub C.d m ![fun j => X ((1 : Fin 3), j), fun j => X ((2 : Fin 3), j)] (T m) := fun m =>
    Units.ext (by rw [Units.val_mul]; exact twist_mul_first_argument_jet C.B.G (cc m) m)
  have hm2 : ∀ m, sub C.d m ![fun j => X ((0 : Fin 3), j), fun j => psIn C.d m ![1, 2] (C.B.G.F j)] (T m) =
      sub C.d m ![fun j => X ((0 : Fin 3), j), fun j => X ((1 : Fin 3), j)] (T m) *
        sub C.d m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)] (T m) := fun m =>
    Units.ext (by rw [Units.val_mul]; exact twist_mul_second_argument_jet C.B.G (cc m) m)
  have hs : ∀ m, sub C.d m ![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)] (T m) = T m := fun m =>
    Units.ext (twist_sym_jet C.B.G (cc m) (hsym m) m)
  have hb : ∀ m a, sub C.d m ![fun j => psIn C.d m ![0] (C.B.A.act a j), fun j => X ((1 : Fin 2), j)] (T m) =
      sub C.d m ![fun j => X ((0 : Fin 2), j), fun j => psIn C.d m ![1] (C.B.A.act (H.bar a) j)] (T m) :=
    fun m a => Units.ext (twist_bal_jet C.B (cc m) a (H.bar a) (hbal m a) m)
  have hT : ∀ m, Units.map (jetTrunc : Jet S (Fin 2 × Fin C.d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin C.d) m).toMonoidHom
      (T (m + 1)) * U m = T m := fun m => Units.ext (by
    rw [Units.val_mul, Units.coe_map, hU m]
    show (jetTrunc : Jet S (Fin 2 × Fin C.d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin C.d) m)
      (psJet (m + 1) (expP (-bilL C.B.G (cc (m + 1))))) * _ = psJet m (expP (-bilL C.B.G (cc m)))
    rw [ExpGB.jetTrunc_psJet, ← FBIdJet.psJet_mul, ← twist_add, add_sub_cancel])
  have hT0 : T 0 = 1 := Units.ext (by
    show psJet 0 (expP (-bilL C.B.G (cc 0))) = 1
    rw [h0, twist_zero, FBIdJet.psJet_one])
  obtain ⟨e', hfr, hrig, htr, hcorr⟩ := fixTw_of y C T U hm1 hm2 hs hb hc hT hT0
  exact ⟨e', hfr, hrig, htr, fun m => ⟨T m, twU_val _ _ _, hcorr m⟩⟩

end Chart

end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2c
