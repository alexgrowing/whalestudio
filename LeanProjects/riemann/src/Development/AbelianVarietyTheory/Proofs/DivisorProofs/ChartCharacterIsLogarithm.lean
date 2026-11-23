import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ESmall
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupExpTwoSidedInverseUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntProdRename
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.NatCastMulCoeffOfPderivEq

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CharLogOfChar

section Series

open MvPowerSeries ReciprocityTheory.PGsh GlobalTheory.FGDepth GlobalTheory.FormalCalc

variable {C : Type} [Field C]

theorem cc_pderiv {σ : Type} (i : σ) (f : MvPowerSeries σ C) :
    constantCoeff (pderiv C i f) = coeff (Finsupp.single i 1) f := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv]
  simp

theorem subst_zero_fun {σ τ : Type} [Finite σ] (f : MvPowerSeries σ C) :
    subst (fun _ : σ => (0 : MvPowerSeries τ C)) f = MvPowerSeries.C (constantCoeff f) := by
  classical
  have hs : HasSubst (fun _ : σ => (0 : MvPowerSeries τ C)) :=
    hasSubst_of_constantCoeff_zero fun _ => map_zero _
  ext e
  rw [coeff_subst hs, finsum_eq_single _ 0]
  · simp [coeff_C, coeff_one]
  · intro D hD
    obtain ⟨s, hs'⟩ := Finsupp.support_nonempty_iff.mpr hD
    rw [Finsupp.prod, Finset.prod_eq_zero hs' (zero_pow (Finsupp.mem_support_iff.mp hs'))]
    simp

theorem coeff_single_subst {σ τ : Type} [Fintype σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (f : MvPowerSeries σ C) (i : τ) :
    coeff (Finsupp.single i 1) (subst a f) =
      ∑ s, coeff (Finsupp.single s 1) f * coeff (Finsupp.single i 1) (a s) := by
  have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
  rw [← cc_pderiv, pderiv_subst hs, map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_mul, constantCoeff_subst_of_zero hs ha, cc_pderiv, cc_pderiv]
  rfl

variable {d : ℕ}

theorem pderiv_of_mul (g : MvPowerSeries (Fin d) C)
    (h : subst (fun a : Fin d => (X (Sum.inl a) + X (Sum.inr a) : MvPowerSeries (Fin d ⊕ Fin d) C)) g =
      subst (fun a : Fin d => (X (Sum.inl a) : MvPowerSeries (Fin d ⊕ Fin d) C)) g *
        subst (fun a : Fin d => (X (Sum.inr a) : MvPowerSeries (Fin d ⊕ Fin d) C)) g) (i : Fin d) :
    pderiv C i g = coeff (Finsupp.single i 1) g • g := by
  classical
  have hS : HasSubst (fun a : Fin d => (X (Sum.inl a) + X (Sum.inr a) : MvPowerSeries (Fin d ⊕ Fin d) C)) :=
    hasSubst_of_constantCoeff_zero fun _ => by simp
  have hL : HasSubst (fun a : Fin d => (X (Sum.inl a) : MvPowerSeries (Fin d ⊕ Fin d) C)) :=
    hasSubst_of_constantCoeff_zero fun _ => by simp
  have hR : HasSubst (fun a : Fin d => (X (Sum.inr a) : MvPowerSeries (Fin d ⊕ Fin d) C)) :=
    hasSubst_of_constantCoeff_zero fun _ => by simp
  let Z : Fin d ⊕ Fin d → MvPowerSeries (Fin d) C := Sum.elim X fun _ => 0
  have hZ : HasSubst Z := hasSubst_of_constantCoeff_zero fun s => by cases s <;> simp [Z]
  have hd := congrArg (fun f => subst Z (pderiv C (Sum.inr i) f)) h
  simp only [Derivation.leibniz, pderiv_subst hS, pderiv_subst hL, pderiv_subst hR, map_add, pderiv_X,
    Pi.single_apply, reduceCtorEq, if_false, Sum.inr.injEq, zero_add, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero, smul_zero, add_zero,
    smul_eq_mul] at hd
  rw [subst_mul hZ, subst_comp_subst_apply hS hZ, subst_comp_subst_apply hL hZ,
    subst_comp_subst_apply hR hZ] at hd
  simp only [subst_add hZ, subst_X hZ, Z, Sum.elim_inl, Sum.elim_inr, add_zero] at hd
  rw [subst_zero_fun, cc_pderiv] at hd
  have e : (fun s : Fin d => (X s : MvPowerSeries (Fin d) C)) = X := rfl
  rw [e, subst_self] at hd
  rw [show pderiv C i g = id (pderiv C i g) from rfl, hd, id, mul_comm, smul_eq_C_mul]

variable [CharZero C]

open Formalism.L2.Th1.C in

theorem coeff_of_pderiv (g : MvPowerSeries (Fin d) C) (c : Fin d → C) (h0 : constantCoeff g = 1)
    (h : ∀ i, pderiv C i g = c i • g) (α : Fin d →₀ ℕ) :
    coeff α g = α.prod fun e n => c e ^ n / (n.factorial : C) := by
  classical
  rw [← CharBound.coeff_mvExp_lin]
  set L : MvPowerSeries (Fin d) C := ∑ s, c s • (X s : MvPowerSeries (Fin d) C) with hLdef
  have hL : constantCoeff L = 0 := by simp [hLdef]
  have hnL : constantCoeff (-L) = 0 := by rw [map_neg, hL, neg_zero]
  have hpL : ∀ i, pderiv C i L = c i • (1 : MvPowerSeries (Fin d) C) := fun i => by
    simp [hLdef, pderiv_X, Pi.single_apply]
  have key : g * mvExp (-L) = 1 := by
    refine pderiv.ext (fun i => ?_) ?_
    · rw [Derivation.leibniz, pderiv_mvExp hnL, map_neg, hpL, h, pderiv_one]
      simp only [smul_eq_mul, Algebra.smul_def]
      ring
    · rw [map_mul, h0, constantCoeff_mvExp hnL, map_one, mul_one]
  have hE : mvExp L = g := by
    calc mvExp L = (g * mvExp (-L)) * mvExp L := by rw [key, one_mul]
      _ = g := by rw [mul_assoc, mvExp_neg hL, mul_one]
  rw [hE]

variable {v : AddValuation C (WithTop ℝ)}

theorem coeff_single_expOf (G : LogFGL v d) (a i : Fin d) :
    coeff (Finsupp.single i 1) (expOf G a) = if a = i then 1 else 0 := by
  classical
  have h := congrArg (coeff (Finsupp.single i 1)) ((expOf_twoSided_unique C v d G).2.1 a)
  rw [coeff_single_subst G.lg_const] at h
  simp only [G.lg_lin, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  rw [h, ← cc_pderiv, pderiv_X, Pi.single_apply]
  split_ifs <;> simp

theorem mul_of_char (G : LogFGL v d) (χ : MvPowerSeries (Fin d) C)
    (h : subst G.F χ = subst (fun a : Fin d => (X (Sum.inl a) : MvPowerSeries (Fin d ⊕ Fin d) C)) χ *
        subst (fun a : Fin d => (X (Sum.inr a) : MvPowerSeries (Fin d ⊕ Fin d) C)) χ) :
    subst (fun a : Fin d => (X (Sum.inl a) + X (Sum.inr a) : MvPowerSeries (Fin d ⊕ Fin d) C))
        (subst (expOf G) χ) =
      subst (fun a : Fin d => (X (Sum.inl a) : MvPowerSeries (Fin d ⊕ Fin d) C)) (subst (expOf G) χ) *
        subst (fun a : Fin d => (X (Sum.inr a) : MvPowerSeries (Fin d ⊕ Fin d) C)) (subst (expOf G) χ) := by
  obtain ⟨⟨hE0, hE1⟩, hE2, -⟩ := expOf_twoSided_unique C v d G
  have hE : HasSubst (expOf G) := hasSubst_of_constantCoeff_zero hE0
  have hS : HasSubst (fun a : Fin d => (X (Sum.inl a) + X (Sum.inr a) : MvPowerSeries (Fin d ⊕ Fin d) C)) :=
    hasSubst_of_constantCoeff_zero fun _ => by simp
  have hL : HasSubst (fun a : Fin d => (X (Sum.inl a) : MvPowerSeries (Fin d ⊕ Fin d) C)) :=
    hasSubst_of_constantCoeff_zero fun _ => by simp
  have hR : HasSubst (fun a : Fin d => (X (Sum.inr a) : MvPowerSeries (Fin d ⊕ Fin d) C)) :=
    hasSubst_of_constantCoeff_zero fun _ => by simp
  have hF : HasSubst G.F := hasSubst_of_constantCoeff_zero G.F_const
  have hlg : HasSubst G.lg := hasSubst_of_constantCoeff_zero G.lg_const
  let P : Fin d ⊕ Fin d → MvPowerSeries (Fin d ⊕ Fin d) C :=
    Sum.elim (fun b => subst (fun a : Fin d => (X (Sum.inl a) : MvPowerSeries (Fin d ⊕ Fin d) C)) (expOf G b))
      (fun b => subst (fun a : Fin d => (X (Sum.inr a) : MvPowerSeries (Fin d ⊕ Fin d) C)) (expOf G b))
  have hP0 : ∀ s, constantCoeff (P s) = 0 := fun s => by
    cases s with
    | inl b => exact constantCoeff_subst_eq_zero hL (fun _ => by simp) (hE0 b)
    | inr b => exact constantCoeff_subst_eq_zero hR (fun _ => by simp) (hE0 b)
  have hP : HasSubst P := hasSubst_of_constantCoeff_zero hP0
  have eL : ∀ f : MvPowerSeries (Fin d) C,
      subst P (subst (fun a : Fin d => (X (Sum.inl a) : MvPowerSeries (Fin d ⊕ Fin d) C)) f) =
        subst (fun a : Fin d => (X (Sum.inl a) : MvPowerSeries (Fin d ⊕ Fin d) C)) (subst (expOf G) f) := by
    intro f
    rw [subst_comp_subst_apply hL hP, subst_comp_subst_apply hE hL]
    simp only [subst_X hP, P, Sum.elim_inl]
  have eR : ∀ f : MvPowerSeries (Fin d) C,
      subst P (subst (fun a : Fin d => (X (Sum.inr a) : MvPowerSeries (Fin d ⊕ Fin d) C)) f) =
        subst (fun a : Fin d => (X (Sum.inr a) : MvPowerSeries (Fin d ⊕ Fin d) C)) (subst (expOf G) f) := by
    intro f
    rw [subst_comp_subst_apply hR hP, subst_comp_subst_apply hE hR]
    simp only [subst_X hP, P, Sum.elim_inr]
  have hQ : HasSubst (fun a => (subst P (G.F a) : MvPowerSeries (Fin d ⊕ Fin d) C)) :=
    hasSubst_of_constantCoeff_zero fun a => constantCoeff_subst_eq_zero hP hP0 (G.F_const a)
  have e1 : (fun a : Fin d => (X (Sum.inl a) + X (Sum.inr a) : MvPowerSeries (Fin d ⊕ Fin d) C)) =
      fun a => subst (fun b => (subst P (G.F b) : MvPowerSeries (Fin d ⊕ Fin d) C)) (G.lg a) := by
    funext a
    rw [← subst_comp_subst_apply hF hP, G.lg_F, subst_add hP, eL, eR, hE1, subst_X hL, subst_X hR]
  have e2 : (fun b => (subst (fun a : Fin d => (X (Sum.inl a) + X (Sum.inr a) :
      MvPowerSeries (Fin d ⊕ Fin d) C)) (expOf G b) : MvPowerSeries (Fin d ⊕ Fin d) C)) =
      fun b => subst P (G.F b) := by
    funext b
    rw [e1, ← subst_comp_subst_apply hlg hQ, hE2, subst_X hQ]
  rw [subst_comp_subst_apply hE hS, e2, ← subst_comp_subst_apply hF hP, h, subst_mul hP, eL, eR]

theorem isCharLog_of_char (G : LogFGL v d) (χ : MvPowerSeries (Fin d) C) (hi : MvIsInt v χ)
    (h0 : constantCoeff χ = 1)
    (h : subst G.F χ = subst (fun a : Fin d => (X (Sum.inl a) : MvPowerSeries (Fin d ⊕ Fin d) C)) χ *
        subst (fun a : Fin d => (X (Sum.inr a) : MvPowerSeries (Fin d ⊕ Fin d) C)) χ) :
    IsCharLog G fun j => coeff (Finsupp.single j 1) χ := by
  classical
  have hE0 := (expOf_twoSided_unique C v d G).1.1
  have hE : HasSubst (expOf G) := hasSubst_of_constantCoeff_zero hE0
  refine ⟨χ, hi, coeff_of_pderiv _ _ ?_ fun i => ?_⟩
  · rw [constantCoeff_subst_of_zero hE hE0, h0, map_one]
  · rw [pderiv_of_mul _ (mul_of_char G χ h), coeff_single_subst hE0]
    simp [coeff_single_expOf]

end Series

open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

theorem isCharLog_dl : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p), ∀ χ : PS X.O 1 (chD Ch.ch), ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.IsCh (fun i => MvPowerSeries.map X.ι (Ch.FT i)) χ → IsCharLog (fgl Ch X) (fun j => algebraMap X.O X.C (ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.dl χ j)) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro p _ T io y Ch X χ hχ
  obtain ⟨h0, hm⟩ := hχ
  set φ := algebraMap X.O X.C with hφ
  have hj : φ.comp X.ι = jX X := RingHom.ext fun r => (X.comp r).symm
  have hFe : ∀ i, MvPowerSeries.map φ (MvPowerSeries.map X.ι (Ch.FT i)) = (lawX Ch X).F i := fun i => by
    rw [lawX_F, ← hj, MvPowerSeries.map_comp]; rfl
  have hinj : Function.Injective φ := X.ints.hom_inj
  have hF0 : ∀ i, MvPowerSeries.constantCoeff (MvPowerSeries.map X.ι (Ch.FT i)) = 0 := fun i => hinj (by
    have h := (lawX Ch X).const i
    rw [← hFe, MvPowerSeries.constantCoeff_map] at h
    rw [h, map_zero])
  have hadd : addOf (fun i => MvPowerSeries.map X.ι (Ch.FT i)) (pt X.O (n := 2) _ 0) (pt X.O (n := 2) _ 1) =
      fun i => MvPowerSeries.map X.ι (Ch.FT i) := by
    funext i
    have e : (fun q : Fin 2 × Fin (chD Ch.ch) =>
        (![pt X.O (n := 2) _ 0, pt X.O _ 1] : Fin 2 → Pt X.O 2 _) q.1 q.2) = MvPowerSeries.X := by
      funext q
      obtain ⟨j, i⟩ := q
      fin_cases j <;> rfl
    unfold addOf ev
    rw [e, MvPowerSeries.subst_self]
    rfl
  have hmap : ∀ a : Pt X.O 2 (chD Ch.ch), (∀ i, MvPowerSeries.constantCoeff (a i) = 0) →
      MvPowerSeries.map φ (ev ![a] χ) = ev ![fun i => MvPowerSeries.map φ (a i)] (MvPowerSeries.map φ χ) := by
    intro a ha
    unfold ev
    rw [MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => by
      obtain ⟨j, i⟩ := q
      fin_cases j; exact ha i)]
    congr 1
    funext q
    obtain ⟨j, i⟩ := q
    fin_cases j; rfl
  have hp : ∀ (k : Type) [CommRing k] (j : Fin 2) i,
      MvPowerSeries.constantCoeff (pt k (n := 2) (chD Ch.ch) j i) = 0 := fun k _ j i => by simp [pt]
  have hpm : ∀ j : Fin 2, (fun i => MvPowerSeries.map φ (pt X.O (n := 2) (chD Ch.ch) j i)) = pt X.C _ j :=
    fun j => funext fun i => by simp [pt]
  have hm' := congrArg (MvPowerSeries.map φ) hm
  rw [hadd, map_mul, hmap _ hF0, hmap _ (hp _ 0), hmap _ (hp _ 1), hpm, hpm, funext hFe] at hm'
  have key := isCharLog_of_char (fgl Ch X)
    (MvPowerSeries.subst (GlobalTheory.LawLog.oneVar X.C _) (MvPowerSeries.map φ χ)) ?_ ?_ ?_
  · simp only [GlobalTheory.LawLog.coeff_single_oneVar, MvPowerSeries.coeff_map] at key
    exact key
  · refine CharBound.mvIsInt_subst' GlobalTheory.LawLog.hs_oneVar (fun q => CharBound.mvIsInt_X' _) fun α => ?_
    rw [MvPowerSeries.coeff_map, isIntV_iff]
    exact X.ints.map_le_one _
  · rw [GlobalTheory.FormalCalc.constantCoeff_subst_of_zero GlobalTheory.LawLog.hs_oneVar GlobalTheory.LawLog.cc_oneVar]
    simp [h0]
  · have e0 : (fun b => (MvPowerSeries.X (Sum.inl b) : MvPowerSeries (Fin (chD Ch.ch) ⊕ Fin (chD Ch.ch)) X.C)) =
        fun i => MvPowerSeries.subst (GlobalTheory.LawLog.twoVars X.C _) (pt X.C (n := 2) _ 0 i) := by
      funext i; rw [pt, MvPowerSeries.subst_X GlobalTheory.LawLog.hs_twoVars]; simp [GlobalTheory.LawLog.twoVars]
    have e1 : (fun b => (MvPowerSeries.X (Sum.inr b) : MvPowerSeries (Fin (chD Ch.ch) ⊕ Fin (chD Ch.ch)) X.C)) =
        fun i => MvPowerSeries.subst (GlobalTheory.LawLog.twoVars X.C _) (pt X.C (n := 2) _ 1 i) := by
      funext i; rw [pt, MvPowerSeries.subst_X GlobalTheory.LawLog.hs_twoVars]; simp [GlobalTheory.LawLog.twoVars]
    have eF : (fgl Ch X).F = fun i => MvPowerSeries.subst (GlobalTheory.LawLog.twoVars X.C _) ((lawX Ch X).F i) := rfl
    rw [e0, e1, eF, GlobalTheory.LawLog.subst_oneVar _ GlobalTheory.LawLog.cc_twoVars _ (lawX Ch X).const,
      GlobalTheory.LawLog.subst_oneVar _ GlobalTheory.LawLog.cc_twoVars _ (hp _ 0),
      GlobalTheory.LawLog.subst_oneVar _ GlobalTheory.LawLog.cc_twoVars _ (hp _ 1), ← MvPowerSeries.subst_mul GlobalTheory.LawLog.hs_twoVars, hm']

end GlobalTheory.CharLogOfChar
