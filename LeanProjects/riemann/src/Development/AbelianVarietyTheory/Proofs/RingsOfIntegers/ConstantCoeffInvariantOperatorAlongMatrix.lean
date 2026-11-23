import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.GermPointsNoConstantTermFirstZero
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MvPowerSeriesSubstConstTermsLocalAlgHomSpec
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FoldPermutation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.FormalGroupLawPointMaps

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MatChain

section General

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB Formalism.L2.Pj GlobalTheory.DerivEndo
open ReciprocityTheory.ChartRestriction.G.TB.LogPf (Jac Ar jac_F)

variable {k : Type} [CommRing k] {d n : ℕ}

theorem dofN_chain {m : ℕ} (F : Fin d → PS k 2 d) (b : Fin n) (u : Fin d → k) {a : Fin m → Pt k n d}
    (ha : NoConst a) (g : PS k m d) :
    DofN F b u (ev a g) = ∑ c : Fin m, ∑ l : Fin d, ev a (pderiv k (c, l) g) * DofN F b u (a c l) := by
  unfold DofN
  simp only [pderiv_ev ha]
  simp only [Finset.mul_sum (s := (Finset.univ : Finset (Fin m))), Finset.mul_sum (f := fun l => ev a _ * _)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem dofN_add (F : Fin d → PS k 2 d) (b : Fin n) (u : Fin d → k) (f g : PS k n d) :
    DofN F b u (f + g) = DofN F b u f + DofN F b u g := by
  simp only [DofN, map_add, mul_add, Finset.sum_add_distrib]

theorem dofN_C_mul (F : Fin d → PS k 2 d) (b : Fin n) (u : Fin d → k) (r : k) (g : PS k n d) :
    DofN F b u (C r * g) = C r * DofN F b u g :=
  Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies.dofN_mul_left F b u _ _ (fun j => by simp)

theorem dofN_smul (F : Fin d → PS k 2 d) (b : Fin n) (u : Fin d → k) (r : k) (g : PS k n d) :
    DofN F b (r • u) g = C r * DofN F b u g := by
  simp only [DofN, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, Finset.sum_mul, mul_assoc]

def jv (G : FGLaw k d) (a : Pt k n d) (w : Fin d → k) : Pt k n d :=
  fun c => ∑ i, C (w i) * ev ![a] (Jac G c i)

theorem dof_X (G : FGLaw k d) (w : Fin d → k) (c : Fin d) :
    Dof G.F w (pt k d 0 c) = ∑ i, C (w i) * Jac G c i := by
  unfold Dof
  rw [Finset.sum_eq_single c]
  · simp [pt, Jac]
  · intro j _ hj
    rw [pt, pderiv_X_of_ne (fun h => hj (congrArg Prod.snd h).symm), mul_zero]
  · simp

theorem ev_jac (G : FGLaw k d) {a : Pt k n d} (ha : ∀ i, constantCoeff (a i) = 0) (c i : Fin d) :
    ev ![a] (Jac G c i) = ev ![a, 0] (pderiv k ((1 : Fin 2), i) (G.F c)) := by
  rw [Jac, ev_ev (noConst_one ha) germPointsNoConstantTerm_first_zero]
  congr 1
  funext j l
  fin_cases j
  · exact ev_pt (noConst_one ha) 0 l
  · exact ev_zero (noConst_one ha)

theorem dofN_eq (G : FGLaw k d) (b : Fin n) (w : Fin d → k) (g : PS k n d) :
    DofN G.F b w g = ∑ l, jv G (pt k d b) w l * pderiv k (b, l) g := by
  simp only [DofN, jv, ev_jac G (cc_pt b)]

theorem ev_jv (G : FGLaw k d) {m : ℕ} {M : Fin m → Pt k n d} (hM : NoConst M) {a : Pt k m d}
    (ha : ∀ i, constantCoeff (a i) = 0) (w : Fin d → k) (c : Fin d) :
    ev M (jv G a w c) = jv G (fun i => ev M (a i)) w c := by
  simp only [jv, ev_sum hM, ev_mul hM, DerivEndo.ev_C, ev_ev hM (noConst_one ha)]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  funext j l
  fin_cases j
  rfl

variable (G : FGLaw k d) (j : Fin n) (v : Fin d → k)

def Tan (a : Pt k n d) (w : Fin d → k) : Prop :=
  (∀ i, constantCoeff (a i) = 0) ∧ ∀ c, DofN G.F j v (a c) = jv G a w c

theorem tan_zero : Tan G j v 0 0 := ⟨fun _ => by simp, fun _ => by simp [DofN, jv]⟩

theorem tan_pt (b : Fin n) : Tan G j v (pt k d b) (if b = j then v else 0) := by
  refine ⟨cc_pt b, fun c => ?_⟩
  rw [dofN_eq]
  split_ifs with h
  · subst h
    rw [Finset.sum_eq_single c]
    · simp [pt]
    · intro l _ hl
      rw [pt, pderiv_X_of_ne (fun h => hl (congrArg Prod.snd h).symm), mul_zero]
    · simp
  · rw [Finset.sum_eq_zero]
    · simp [jv]
    · intro l _
      rw [pt, pderiv_X_of_ne (fun h' => h (congrArg Prod.fst h')), mul_zero]

variable {G j v}

theorem dofN_ev_of_tan {m : ℕ} {M : Fin m → Pt k n d} {w : Fin m → Fin d → k} (h : ∀ b, Tan G j v (M b) (w b))
    (g : PS k m d) : DofN G.F j v (ev M g) = ev M (∑ b, DofN G.F b (w b) g) := by
  have hM : NoConst M := fun b => (h b).1
  rw [dofN_chain _ _ _ hM, ev_sum hM]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [dofN_eq, ev_sum hM]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [ev_mul hM, ev_jv G hM (cc_pt b), (h b).2, mul_comm]
  simp only [ev_pt hM]

theorem Tan.comp {a : Pt k n d} {w : Fin d → k} (h : Tan G j v a w) (φ : Pt k 1 d)
    (hφ : ∀ i, constantCoeff (φ i) = 0)
    (hom : comp1 φ (G.add (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
      G.add (comp1 φ (pt k (n := 2) d 0)) (comp1 φ (pt k (n := 2) d 1))) :
    Tan G j v (comp1 φ a) ((dLin φ).mulVec w) := by
  have ha := noConst_one h.1
  have h1 := noConst_one hφ
  refine ⟨fun i => (cc_ev ha _).trans (hφ i), fun c => ?_⟩
  have e := dofN_ev_of_tan (M := ![a]) (w := ![w]) (fun b => by fin_cases b; exact h) (φ c)
  have e2 := dof_comp_endo k d G φ hφ hom w (pt k d 0 c)
  rw [ev_pt h1, dof_X] at e2
  rw [Fin.sum_univ_one] at e
  refine e.trans ((congrArg (ev ![a]) e2).trans ?_)
  simp only [jv, ev_sum h1, ev_mul h1, DerivEndo.ev_C, ev_sum ha, ev_mul ha, ev_ev ha h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  funext j l
  fin_cases j
  rfl

theorem jv_add_right (G : FGLaw k d) {a b : Pt k n d} (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) (w : Fin d → k) (c : Fin d) :
    ∑ l, ev ![a, b] (pderiv k ((1 : Fin 2), l) (G.F c)) * jv G b w l = jv G (G.add a b) w c := by
  have hab := noConst_two ha hb
  have key : ∀ i, ev ![G.add a b] (Jac G c i) =
      ∑ l, ev ![a, b] (pderiv k ((1 : Fin 2), l) (G.F c)) * ev ![b] (Jac G l i) := by
    intro i
    have e := congrArg (ev ![a, b]) (jac_F G c i)
    rw [ev_ev hab (noConst_one G.const), ev_sum hab] at e
    refine Eq.trans ?_ (e.trans (Finset.sum_congr rfl fun l _ => ?_))
    · congr 1
      funext j l
      fin_cases j
      rfl
    · rw [ev_mul hab, ev_ev hab (noConst_one (cc_pt 1))]
      congr 2
      funext j l
      fin_cases j
      exact ev_pt hab 1 l
  simp only [jv, key, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem ev_swap {a b : Pt k n d} (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0)
    (f : PS k 2 d) : ev ![a, b] (ev (n := 2) ![pt k d 1, pt k d 0] f) = ev ![b, a] f := by
  have hab := noConst_two ha hb
  rw [ev_ev hab (noConst_two (cc_pt 1) (cc_pt 0))]
  congr 1
  funext j l
  fin_cases j
  · exact ev_pt hab 1 l
  · exact ev_pt hab 0 l

theorem pderiv_law_left (G : FGLaw k d) (c l : Fin d) :
    pderiv k ((0 : Fin 2), l) (G.F c) = ev (n := 2) ![pt k d 1, pt k d 0] (pderiv k ((1 : Fin 2), l) (G.F c)) := by
  conv_lhs => rw [← G.comm c]
  rw [pderiv_ev (noConst_two (cc_pt 1) (cc_pt 0)), Fin.sum_univ_two]
  simp [LogPf.pderiv_pt]

theorem Tan.add {a b : Pt k n d} {w w' : Fin d → k} (h : Tan G j v a w) (h' : Tan G j v b w') :
    Tan G j v (G.add a b) (w + w') := by
  have hab := noConst_two h.1 h'.1
  refine ⟨fun i => (cc_ev hab _).trans (G.const i), fun c => ?_⟩
  have hc : G.add b a = G.add a b := by
    funext i
    have := ev_swap h.1 h'.1 (G.F i)
    rw [G.comm] at this
    exact this.symm
  change DofN G.F j v (ev ![a, b] (G.F c)) = _
  rw [dofN_chain _ _ _ hab, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, h.2, h'.2, pderiv_law_left, ev_swap h.1 h'.1]
  rw [jv_add_right G h'.1 h.1, jv_add_right G h.1 h'.1, hc]
  simp only [jv, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem foldr_add_single {ι β : Type} [DecidableEq ι] (D : ι → β → β) (hD : ∀ a b g, D a (D b g) = D b (D a g))
    (m : ι →₀ ℕ) (l : ι) (L : List ι) (hL : L.Nodup) (g : β) :
    L.foldr (fun a g => (D a)^[(m + Finsupp.single l 1 : ι →₀ ℕ) a] g) g =
      if l ∈ L then D l (L.foldr (fun a g => (D a)^[m a] g) g) else L.foldr (fun a g => (D a)^[m a] g) g := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.nodup_cons] at hL
    rw [List.foldr_cons, List.foldr_cons, ih hL.2]
    by_cases h : l = a
    · subst h
      rw [if_neg hL.1, if_pos List.mem_cons_self, Finsupp.add_apply, Finsupp.single_eq_same,
        Function.iterate_succ_apply']
    · rw [Finsupp.add_apply, Finsupp.single_eq_of_ne' h, add_zero]
      by_cases h2 : l ∈ L
      · rw [if_pos h2, if_pos (List.mem_cons_of_mem _ h2)]
        have hc : Function.Commute (D a) (D l) := fun g => hD a l g
        exact (hc.iterate_left (m a)) _
      · rw [if_neg h2, if_neg (by simp [h, h2])]

open Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies in
theorem dpoly_mul_X (G : FGLaw k d) {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → k)
    (P : MvPolynomial ι k) (l : ι) (g : PS k n d) :
    DpolyN G.F cp u (P * MvPolynomial.X l) g = DofN G.F (cp l) (u l) (DpolyN G.F cp u P g) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial m a =>
    rw [MvPolynomial.X, MvPolynomial.monomial_mul, mul_one, dpoly_monomial, dpoly_monomial, dofN_C_mul]
    congr 1
    unfold DmonN
    rw [foldr_add_single (fun l => DofN G.F (cp l) (u l))
      (fun a b g => Formalism.MainNotions.ModuliIntegralCharts.H1.FoldPermutation.dofN_comm G _ _ _ _ g) m l _ (Finset.nodup_toList _),
      if_pos (Finset.mem_toList.2 (Finset.mem_univ l))]
  | add P Q hP hQ => rw [add_mul, dpoly_add, dpoly_add, dofN_add, hP, hQ]

open Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies in
theorem dpoly_C_mul (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → k)
    (r : k) (P : MvPolynomial ι k) (g : PS k n d) :
    DpolyN F cp u (MvPolynomial.C r * P) g = C r * DpolyN F cp u P g := by
  induction P using MvPolynomial.induction_on' with
  | monomial m a => rw [MvPolynomial.C_mul_monomial, dpoly_monomial, dpoly_monomial, map_mul, mul_assoc]
  | add P Q hP hQ => rw [mul_add, dpoly_add, dpoly_add, mul_add, hP, hQ]

open Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies in

theorem dpoly_ev (G : FGLaw k d) {ι κ : Type} [Fintype ι] [Fintype κ] (cp : ι → Fin n) (u : ι → Fin d → k)
    {M : Fin n → Pt k n d} (hM : NoConst M) (co : ι → κ → k) (t : ι → κ → ι)
    (h : ∀ l g, DofN G.F (cp l) (u l) (ev M g) = ev M (∑ b, C (co l b) * DofN G.F (cp (t l b)) (u (t l b)) g))
    (P : MvPolynomial ι k) (g : PS k n d) :
    DpolyN G.F cp u P (ev M g) = ev M (DpolyN G.F cp u
      (MvPolynomial.aeval (fun l => ∑ b, MvPolynomial.C (co l b) * MvPolynomial.X (t l b)) P) g) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, MvPolynomial.C_apply, dpoly_monomial, dpoly_monomial,
      dmon_zero, dmon_zero, ev_mul hM, DerivEndo.ev_C]
  | add P Q hP hQ => rw [map_add, dpoly_add, dpoly_add, ev_add hM, hP, hQ]
  | mul_X P l hP =>
    rw [dpoly_mul_X, hP, h, map_mul, MvPolynomial.aeval_X, Finset.mul_sum]
    congr 1
    refine Eq.trans ?_ (map_sum (dpolyHom G.F cp u g) _ _).symm
    refine Finset.sum_congr rfl fun b _ => ?_
    change _ = DpolyN G.F cp u _ g
    rw [mul_left_comm, dpoly_C_mul, dpoly_mul_X]

end General

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open ReciprocityTheory.ChartRestriction.G.TB.PointMapComposition ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab

section Place

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V]
  {d : ℕ}

theorem evV_eq {m n : ℕ} {a : Fin m → Pt V n d} (ha : GlobalTheory.DerivEndo.NoConst a) (f : PS V m d) : evV a f = ev a f :=
  (GlobalTheory.PlaceInt.evC_spec V (Fin m × Fin d) (Fin n × Fin d) Unit (fun p => a p.1 p.2)
    (fun p => by rw [ha p.1 p.2]; exact Ideal.zero_mem _)).2.2.1 (fun p => ha p.1 p.2) f

variable {O : Type} [CommRing O] [StarRing O] (B : FB V d O) (K : Type) [Field K] [Algebra ℚ K] [Algebra V K]

theorem tan_foldr {n : ℕ} (j : Fin n) (v : Fin d → K) {Ix : Type} (x : Ix → Pt V n d) (w : Ix → Fin d → K)
    (hx : ∀ s i, MvPowerSeries.constantCoeff (x s i) = 0) (h : ∀ s, Tan (lawK K B) j v (mapPt K (x s)) (w s))
    (L : List Ix) :
    (∀ i, MvPowerSeries.constantCoeff ((L.map x).foldr (addV B.G.F) 0 i) = 0) ∧
      Tan (lawK K B) j v (mapPt K ((L.map x).foldr (addV B.G.F) 0)) (L.map w).sum := by
  induction L with
  | nil =>
    refine ⟨fun i => by simp, ?_⟩
    have : mapPt K (0 : Pt V n d) = 0 := by funext i; simp [mapPt]
    simpa [this] using tan_zero (lawK K B) j v
  | cons s L ih =>
    have hn := GlobalTheory.DerivEndo.noConst_two (hx s) ih.1
    have e : addV B.G.F (x s) ((L.map x).foldr (addV B.G.F) 0) =
        addOf B.G.F (x s) ((L.map x).foldr (addV B.G.F) 0) := funext fun i => evV_eq hn _
    rw [List.map_cons, List.map_cons, List.foldr_cons, List.sum_cons, e]
    refine ⟨fun i => (GlobalTheory.DerivEndo.cc_ev hn _).trans (B.G.const i), ?_⟩
    rw [mapPt_addOf K _ _ _ (hx s) ih.1]
    exact (h s).add ih.2

theorem tan_matV {n : ℕ} (mu : Matrix (Fin n) (Fin n) O) (j : Fin n) (v : Fin d → K) (b : Fin n) :
    Tan (lawK K B) j v (mapPt K (matV B mu (fun j => pt V (n := n) d j) b)) ((dAct K B (mu b j)).mulVec v) := by
  have e : ∀ s, compV (B.A.act (mu b s)) (pt V (n := n) d s) = comp1 (B.A.act (mu b s)) (pt V (n := n) d s) :=
    fun s => funext fun i => evV_eq (GlobalTheory.DerivEndo.noConst_one (GlobalTheory.DerivEndo.cc_pt s)) _
  have h := (tan_foldr B K j v (fun s => comp1 (B.A.act (mu b s)) (pt V (n := n) d s))
    (fun s => (dAct K B (mu b s)).mulVec (if s = j then v else 0))
    (fun s i => (GlobalTheory.DerivEndo.cc_ev (GlobalTheory.DerivEndo.noConst_one (GlobalTheory.DerivEndo.cc_pt s)) _).trans (B.A.const _ i))
    (fun s => by
      rw [mapPt_comp1 K _ _ (GlobalTheory.DerivEndo.cc_pt s), mapPt_pt]
      exact (tan_pt (lawK K B) j v s).comp _ ((actKO K B).const (mu b s)) ((actKO K B).hom (mu b s)))
    (List.finRange n)).2
  rw [← Fin.sum_univ_def, Finset.sum_eq_single j (fun s _ hs => by rw [if_neg hs, Matrix.mulVec_zero]) (by simp),
    if_pos rfl] at h
  unfold matV
  simp only [e, List.ofFn_eq_map]
  exact h

end Place

theorem constantCoeff_dpolyN_matV : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O) (K : Type) [Field K] [Algebra ℚ K] [Algebra V K] (n : ℕ) (mu : Matrix (Fin n) (Fin n) O) (Ty : Type) [Fintype Ty] (r : Ty → ℕ) (σ : Ty → O →+* K) (u : (Σ τ : Ty, Fin (r τ)) → Fin d → K), (∀ ℓ a, (dAct K B a).mulVec (u ℓ) = σ ℓ.1 a • u ℓ) → ∀ (P : MvPolynomial (Letter Ty r n) K) (g : PS K n d), MvPowerSeries.constantCoeff (DpolyN (B.FK K) (fun ℓ : Letter Ty r n => ℓ.2.2) (fun ℓ => u ⟨ℓ.1, ℓ.2.1⟩) P (ev (n := n) (fun b i => FB.toK K (matV B mu (fun j => pt V (n := n) d j) b i)) g)) = MvPowerSeries.constantCoeff (DpolyN (B.FK K) (fun ℓ : Letter Ty r n => ℓ.2.2) (fun ℓ => u ⟨ℓ.1, ℓ.2.1⟩) (MvPolynomial.aeval (fun ℓ : Letter Ty r n => ∑ b, MvPolynomial.C (σ ℓ.1 (mu b ℓ.2.2)) * MvPolynomial.X (⟨ℓ.1, ℓ.2.1, b⟩ : Letter Ty r n)) P) g) := by
  intro V _ _ _ _ _ d O _ _ B K _ _ _ n mu Ty _ r σ u hu P g
  focus
    have hM : GlobalTheory.DerivEndo.NoConst (fun b => mapPt K (matV B mu (fun j => pt V (n := n) d j) b)) :=
      fun b => (tan_matV B K mu b 0 b).1
    have key := dpoly_ev (lawK K B) (fun ℓ : Letter Ty r n => ℓ.2.2) (fun ℓ => u ⟨ℓ.1, ℓ.2.1⟩) hM
      (fun ℓ b => σ ℓ.1 (mu b ℓ.2.2)) (fun ℓ b => (⟨ℓ.1, ℓ.2.1, b⟩ : Letter Ty r n)) (fun ℓ g => by
        rw [dofN_ev_of_tan (tan_matV B K mu ℓ.2.2 (u ⟨ℓ.1, ℓ.2.1⟩))]
        simp only [hu, dofN_smul]) P g
    exact (congrArg MvPowerSeries.constantCoeff key).trans (GlobalTheory.DerivEndo.cc_ev hM _)

end GlobalTheory.MatChain
