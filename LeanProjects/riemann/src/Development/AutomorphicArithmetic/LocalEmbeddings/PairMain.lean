import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VdivLnIdFalse
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimComponent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSetResidueLogBound
import Development.AutomorphicArithmetic.LocalEmbeddings.VertCmp
import Development.AutomorphicArithmetic.DivisorFrames.PdegEqOfIsDeg
import Development.AutomorphicArithmetic.DivisorFrames.GenericIsoSectionsLog
import Development.AutomorphicArithmetic.DivisorFrames.ExistsMetricGenericOpen
import Development.AutomorphicArithmetic.DivisorFrames.ArithmeticFunctionInducedBound
import Development.AutomorphicArithmetic.DivisorFrames.AdmissiblePointDiscreteValuation
import Development.AutomorphicArithmetic.DivisorFrames.AdmissiblePointCharts
import Development.AutomorphicArithmetic.DivisorFrames.NormalModelComplexCompatAlt
import Development.AutomorphicArithmetic.DivisorFrames.AdmissiblePointLatticeNorm
import Development.AutomorphicArithmetic.DivisorFrames.AdmissiblePointHeightCompat

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.Toroidal
open GlobalTheory.VertCmp GlobalTheory.Mean4O
open scoped Classical

namespace GlobalTheory.PairMain

open GlobalTheory.PairTerm

section Read

private theorem pull_dual_g {X Z : Scheme.{0}} (f : Z ⟶ X) (L : LB X) (i j : (L.pull f).ι) :
    ((CechPic.dual L).pull f).g i j = ((L.pull f).g i j)⁻¹ := by
  have le : (L.pull f).U i ⊓ (L.pull f).U j ≤ f ⁻¹ᵁ (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) :=
    fun x hx => ⟨LB.pull_U_le f i hx.1, LB.pull_U_le f j hx.2⟩
  have h₁ := InducedPull.val_pull_g L f i j le
  have h₂ := InducedPull.val_pull_g (CechPic.dual L) f i j le
  have e : (L.pull f).g i j = Units.map (f.appLE _ _ le).hom.toMonoidHom (L.g (i PUnit.unit) (j PUnit.unit)) :=
    Units.ext h₁
  rw [e, ← map_inv]
  exact Units.ext h₂

private theorem reads_dual {F : Type} [Field F] [NumberField F] {Y : Var F} {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {b : 𝓞 F →+* O} {B : Vert.Model O} (μ : Match Y b B) (v : HeightOneSpectrum (𝓞 F))
    {X : Scheme.{0}} (f : B.X ⟶ X) (L : LB X) (s : (L.pull f).ι → B.X.functionFieldˣ) (l l' : Ext v → AlgPt Y → ℝ)
    (W : Y.X.Opens) (hW : genericPoint Y.X ∈ W) (hl : ∀ e y, below y.1 ∈ W → l' e y = -l e y)
    (h : Reads μ v (L.pull f) s l) : Reads μ v ((CechPic.dual L).pull f) (fun i => (s i)⁻¹) l' := by
  obtain ⟨hr, W₀, hW₀, H⟩ := h
  refine ⟨fun i j h => ?_, W ⊓ W₀, ⟨hW, hW₀⟩, fun e y z zt i hy hz hzt hi => ?_⟩
  · erw [pull_dual_g, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_units_inv, hr i j h, mul_inv]
    rfl
  · obtain ⟨hu, hv⟩ := H e y z zt i hy.2 hz hzt hi
    rw [Units.val_inv_eq_inv_val]
    refine ⟨hu.inv, ?_⟩
    rw [GlobalTheory.LineNorm.Neg.valAt_inv hu, map_inv₀, Real.log_inv, hv, hl e y hy.1]

private theorem dual_rel {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Z : NModel O} (C : Z.Comp)
    {L L' : LB Z.X} (u : Z.GenIso L L') (i : L.ι) (j : L'.ι)
    (h : genericPoint (Z.comp C).X ∈ Z.compι C ⁻¹ᵁ (Z.gen ⊓ (L.U i ⊓ L'.U j))) (a b : (Z.comp C).X.functionFieldˣ)
    (e : fnOf _ h ((Z.compι C).app _ (u.u i j).val) = (a : (Z.comp C).X.functionField) / b) :
    fnOf _ h ((Z.compι C).app _ (u.dual.u i j).val) =
      ((a⁻¹ : (Z.comp C).X.functionFieldˣ) : (Z.comp C).X.functionField) / (b⁻¹ : (Z.comp C).X.functionFieldˣ) := by
  have := map_units_inv ((fnOf _ h).comp ((Z.compι C).app _).hom) (u.u i j)
  refine this.trans ((congrArg (·⁻¹) e).trans ?_)
  simp only [Units.val_inv_eq_inv_val]
  rw [inv_div, inv_div_inv]

private theorem isNormal_comp {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Z : NModel O}
    (C : Z.Comp) : GlobalTheory.IsNormalScheme (Z.comp C).X :=
  show GlobalTheory.IsNormalScheme C.opens.toScheme from GlobalTheory.IsNormalScheme.of_isOpenImmersion (Scheme.Opens.ι C.opens)

end Read

section Syms

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

private theorem lnSym_eq (l : Ln Dw) : ∃ n : ℤ, (n = 1 ∨ n = -1) ∧ ∀ a R, lnSym a R l = Finsupp.single (a, R, l.2.1) n := by
  rcases l with ⟨_ | _, st⟩
  · exact ⟨1, .inl rfl, fun _ _ => rfl⟩
  · exact ⟨-1, .inr rfl, fun _ _ => rfl⟩

private theorem mem_support_lnSym {a : ℕ → Bool} {R : Option ℝ} {l : Ln Dw} {b : Sym E}
    (h : b ∈ (lnSym a R l).support) : b.1 = a ∧ b.2.1 = R := by
  obtain ⟨n, -, e⟩ := lnSym_eq l
  rw [e] at h
  rw [Finset.mem_singleton.1 (Finsupp.support_single_subset h)]
  exact ⟨rfl, rfl⟩

private theorem parOf_lnSym (a : ℕ → Bool) (R : Option ℝ) (l : Ln Dw) : parOf (lnSym a R l) = R := by
  have h : (lnSym a R l).support.Nonempty := by
    obtain ⟨n, hn, e⟩ := lnSym_eq l
    rw [e]
    rcases hn with rfl | rfl <;> simp [Finsupp.support_single_ne_zero]
  rw [parOf, dif_pos h]
  exact (mem_support_lnSym h.choose_spec).2

private theorem expo_lnSym (a a' : ℕ → Bool) (R : Option ℝ) (l : Ln Dw) :
    expo Dw (lnSym a R l) = expo Dw (lnSym a' R l) := by
  obtain ⟨n, -, e⟩ := lnSym_eq l
  funext x
  rw [e, e, expo, expo, Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]

variable {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F}

private theorem adlOf_lnSym_eq {O : Type} [CommRing O] {β : O →+* c.F} {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β}
    (Y : FlagCpt Z e) {C : CxSt F} (hm : Mets Y C) (a a' : ℕ → Bool) (R : Option ℝ) (x : Ln Dw) :
    adlOf Y hm (lnSym a' R x) = { adlOf Y hm (lnSym a R x) with lg := (adlOf Y hm (lnSym a' R x)).lg } := by
  have key (n n' : Pad.Letter Dw → ℤ) (h : n = n') (r r' : Option ℝ) (h' : r = r') (lg) :
      (⟨divOf Y n, 1, fun σ => hm r σ n, 0, lg⟩ : Adl C Y.Y) = ⟨divOf Y n', 1, fun σ => hm r' σ n', 0, lg⟩ := by
    rw [h, h']
  exact key _ _ (expo_lnSym _ _ _ _) _ _ ((parOf_lnSym _ _ _).trans (parOf_lnSym _ _ _).symm) _

private theorem abs_lnStep_le (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) (p : ℕ) [hp : Fact p.Prime]
    (x : Sp ℂ_[p] ⟶ Z.X) (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber ℂ_[p]) ⟶ Z.t.G.left))
    (st : ((E →+* ℂ) × ℕ) ⊕ ℕ) : |lnStep Z.t x u p false st - lnStep Z.t x u p true st| ≤
      Real.log p / ((p : ℝ) - 1) + vDiff E p * Real.log p := by
  rcases st with ⟨τ, k⟩ | k
  · rw [abs_sub_comm]
    exact LgDiff.abs_lnStep_sub_le HTBound.htBound _ _ _ _ _ _
  have hv : 0 ≤ vDiff E p * Real.log p := mul_nonneg (by unfold vDiff; positivity) (Real.log_natCast_nonneg p)
  have hL : 0 ≤ Real.log p / ((p : ℝ) - 1) := by
    have : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
    exact div_nonneg (Real.log_natCast_nonneg p) (by linarith)
  simp only [lnStep, lat]
  split_ifs with h
  · refine (LgDiff.abs_log_grNorm_DR_HT_le HTBound.htBound Z p x _ _).trans ?_
    rw [mul_one_div]
    linarith
  · rw [sub_self, abs_zero]
    linarith

private theorem abs_lgOf_lnSym_le {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)} (Y : FlagCpt Z e)
    (a : ℕ → Bool) (p : ℕ) (R : Option ℝ) (x : Ln Dw) (v : HeightOneSpectrum (𝓞 F))
    (ε : TrueGeo.Ext v) (y : AlgPt Y.Y) :
    |lgOf Y (lnSym (Function.update a p false) R x) v ε y - lgOf Y (lnSym (Function.update a p true) R x) v ε y| ≤
      (if resP v = p then 1 / ((p : ℝ) - 1) + vDiff E p else 0) * (-Real.log (ε.w (resP v : AlgebraicClosure F))) := by
  have hw : 0 ≤ -Real.log (ε.w (resP v : AlgebraicClosure F)) :=
    neg_nonneg.2 (Real.log_nonpos (ε.w.nonneg _) ((ε.mem_O _).1 (natCast_mem _ _)))
  have hp : (resP v).Prime := CharP.char_prime_of_ne_zero (𝓞 F ⧸ v.asIdeal) (CharP.ringChar_ne_zero_of_finite _)
  haveI := Fact.mk hp
  obtain ⟨n, hn, hx⟩ := lnSym_eq x
  have hs (a : ℕ → Bool) (Φ : Sym E → ℝ) : ((lnSym a R x).sum fun b n => (n : ℝ) * Φ b) = n * Φ (a, R, x.2.1) := by
    rw [hx, Finsupp.sum_single_index (by simp)]
  have hn' : |(n : ℝ)| = 1 := by rcases hn with rfl | rfl <;> simp
  simp only [lgOf, dif_pos hp]
  rewrite [expo_lnSym (Function.update a p false) (Function.update a p true),
    add_sub_add_left_eq_sub, ← mul_sub, abs_mul, hs, hs, ← mul_sub, abs_mul, hn', one_mul]
  dsimp only
  by_cases h : resP v = p
  · subst h
    have hl := Real.log_pos (show (1 : ℝ) < resP v by exact_mod_cast hp.one_lt)
    rewrite [if_pos rfl, Function.update_self, Function.update_self]
    refine (mul_le_mul_of_nonneg_left (abs_lnStep_le _ _ _ _ _) (abs_nonneg _)).trans_eq ?_
    rw [abs_of_nonneg (div_nonneg hw hl.le)]
    field_simp
  · have hb : Function.update a p false (resP v) = Function.update a p true (resP v) :=
      (Function.update_of_ne h _ _).trans (Function.update_of_ne h _ _).symm
    rewrite [hb, sub_self, abs_zero, mul_zero, if_neg h, zero_mul]
    exact le_rfl

end Syms

section Up

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ} {hp : p.Prime} {W : ValuationSubring ℂ}
  {hW : (p : ℂ) ∈ W.nonunits} (z : AdmAt S κ hp hW)

private theorem exists_up (v : HeightOneSpectrum (𝓞 D.what₂.LL))
    (hv : ∀ x : D.what₂.LL, D.what₂.embLL x ∈ W ↔ v.valuation D.what₂.LL x ≤ 1) :
    ∃ (ε : D.what₂.LL →+* z.Z.i.c.F) (b : 𝓞 D.what₂.LL →+* z.Z.i.c.V W),
      (∀ x, ((ε x : z.Z.i.c.F) : ℂ) = D.what₂.embLL x) ∧ IsUp v ε (z.Z.i.c.V W) b := by
  have hle : κ.c.F ≤ z.Z.i.c.F := z.Z.le
  let ε : D.what₂.LL →+* z.Z.i.c.F := (IntermediateField.inclusion hle).toRingHom.comp κ.e.toRingHom
  have hε (x) : ((ε x : z.Z.i.c.F) : ℂ) = D.what₂.embLL x := κ.e_emb x
  have hV (x : D.what₂.LL) : ε x ∈ z.Z.i.c.V W ↔ v.valuation D.what₂.LL x ≤ 1 := by
    rw [← hv, ← hε]
    simp [Coeff.V]
  refine ⟨ε, (ε.comp (algebraMap (𝓞 D.what₂.LL) D.what₂.LL)).codRestrict (z.Z.i.c.V W).toSubring
    fun x => (hV _).2 (v.valuation_le_one x), hε, fun x => rfl, fun x => ?_⟩
  rw [← ValuationSubring.coe_mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or, ← v.valuation_lt_one_iff_mem (K := D.what₂.LL)]
  change _ ↔ ε x = 0 ∨ (ε x)⁻¹ ∉ _
  rw [← map_inv₀, hV, map_inv₀, map_eq_zero]
  by_cases h0 : (x : D.what₂.LL) = 0
  · simp only [h0, true_or, iff_true]
    rw [map_zero]
    exact zero_lt_one
  · have hpos : 0 < v.valuation D.what₂.LL (x : D.what₂.LL) := zero_lt_iff.2 ((map_ne_zero _).2 h0)
    rw [not_le, one_lt_inv₀ hpos]
    simp only [h0, false_or]

end Up

section Sums

private theorem finsum_eq_sum_places {X ι T : Type} [Fintype ι] (f : X → ℝ) (hf : (Function.support f).Finite)
    (π : X → T) (v : ι → T) (hv : Function.Injective v) (h : ∀ x, f x ≠ 0 → ∃ i, π x = v i) :
    ∑ᶠ x, f x = ∑ i, ∑ᶠ x, if π x = v i then f x else 0 := by
  have e (i : ι) : (∑ᶠ x, if π x = v i then f x else 0) = ∑ x ∈ hf.toFinset, if π x = v i then f x else 0 :=
    finsum_eq_sum_of_support_subset _ fun x hx => by
      simp only [Set.Finite.coe_toFinset, Function.mem_support]
      intro h0
      exact hx (by simp [h0])
  rw [finsum_eq_sum _ hf, Finset.sum_congr rfl fun i _ => e i, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x hx => ?_
  obtain ⟨i, hi⟩ := h x (hf.mem_toFinset.1 hx)
  rw [Finset.sum_eq_single i (fun k _ hk => if_neg fun e => hk (hv (e.symm.trans hi))) (by simp), if_pos hi]

private theorem sum_filter_partition {X T : Type} [Fintype X] [Fintype T] (f : X → ℝ) (r : X → T → Prop)
    (h : ∀ x, ∃! t, r x t) : ∑ t, ∑ x ∈ Finset.univ.filter fun x => r x t, f x = ∑ x, f x := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  obtain ⟨t, ht, hu⟩ := h x
  rw [Finset.sum_eq_single t (fun k _ hk => if_neg fun e => hk (hu k e)) (by simp), if_pos ht]

end Sums

section Place

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} (fl : s.Flag)
  (hd : ∀ k, (fl.C k).Y.dim = Formalism.DegreeFormula.dimFl D.what₂.Tau N) {p : ℕ} (hp : p.Prime) {W : ValuationSubring ℂ}
  (hW : (p : ℂ) ∈ W.nonunits) (z : AdmAt S κ hp hW) [IsDiscreteValuationRing (z.Z.i.c.V W)]
  (ε : D.what₂.LL →+* z.Z.i.c.F) (b : 𝓞 D.what₂.LL →+* z.Z.i.c.V W)
  (hε : ∀ x, ((ε x : z.Z.i.c.F) : ℂ) = D.what₂.embLL x)
  (hb : ∀ x : 𝓞 D.what₂.LL, ((b x : z.Z.i.c.V W) : z.Z.i.c.F) = ε (x : D.what₂.LL))

include hd hε hb in

private theorem reads_ln (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (hv : resP v = p) (C : (nmodel z.Z).Comp) (c : s.Comp)
    (μ : Match (fl.C c).Y b ((nmodel z.Z).comp C)) (hμ : Link z.Z C (fl.C c) μ) (Cx : CxSt D.what₂.LL)
    (hm : Mets (fl.C c) Cx) (a : Bool → ℕ → Bool) (ha : ∀ k, a k p = k) (R : Option ℝ) (l : Ln S.Dw) :
    ∃ t : ∀ k : Bool, ((lnLB z k l).lb.pull ((nmodel z.Z).compι C)).ι → ((nmodel z.Z).comp C).X.functionFieldˣ,
      (∀ k : Bool, Reads μ v ((lnLB z k l).lb.pull ((nmodel z.Z).compι C)) (t k)
        (lam (adlOf (fl.C c) hm (lnSym (a k) R l)) v)) ∧
      ∀ i j (h : genericPoint ((nmodel z.Z).comp C).X ∈ (nmodel z.Z).compι C ⁻¹ᵁ
          ((nmodel z.Z).gen ⊓ ((lnLB z false l).lb.U i ⊓ (lnLB z true l).lb.U j))),
        fnOf _ h (((nmodel z.Z).compι C).app _ ((lnId z hp hW l).u i j).val) =
          (t false (fun _ => i) : ((nmodel z.Z).comp C).X.functionField) /
            (t true (fun _ => j) : ((nmodel z.Z).comp C).X.functionField) := by
  obtain ⟨sg, st⟩ := l
  obtain ⟨t, ht, hu⟩ := UpperTheory.admissible_point_height_compat D A N j S κ s fl hd p hp W hW z ε b hε hb v hv C c μ hμ Cx hm st.1 _
    (Option.some_get st.2).symm
  rcases sg with _ | _
  · exact ⟨t, fun k => ht k (a k) R (ha k), hu⟩
  refine ⟨fun k i => (t k i)⁻¹, fun k => ?_, fun i j h => ?_⟩
  · obtain ⟨W', hW', e⟩ := UpperTheory.exists_metric_generic_open _ _ _ _ _ _ _ _ _ _ _ (fl.C c) Cx hm (a k, R, st.1)
    exact reads_dual μ v _ _ (t k) _ _ W' hW' (e v) (ht k (a k) R (ha k))
  · exact dual_rel (Z := nmodel z.Z) C (z.genId hp hW (Option.some_get st.2).symm) i j h _ _ (hu i j h)

end Place

private theorem loc_gen {F : Type} [Field F] [NumberField F] {Y : Var F} (v : HeightOneSpectrum (𝓞 F)) (p : ℕ) [Fact p.Prime]
    (hpv : (p : 𝓞 F) ∈ v.asIdeal) {F' : Type} [Field F'] [NumberField F'] (ε : F →+* F') (O : ValuationSubring F')
    [IsDiscreteValuationRing O] [CharP (ResidueField O) p] (b : 𝓞 F →+* O) (hup : IsUp v ε O b) (σ : F' →+* ℂ)
    (Q : TrueGeo.Model Y) [AlgebraicGeometry.IsIntegral Q.X] [IsLocallyNoetherian Q.X]
    (hQ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Q.X) {d : ℕ} (hd : Y.dim = d) (m : ℕ)
    (M : LB Q.X) (hM : M.IsLB) (r : M.ι → Q.X.functionFieldˣ) (hr : IsRatSec M r) (l₀ l₁ : Ext v → AlgPt Y → ℝ)
    (h₀ : GReads Q v M r fun e y => (m : ℝ) * (l₀ e y - l₁ e y)) (L : Fin d → LB Q.X) (hL : ∀ k, (L k).IsLB)
    (u : ∀ k, (L k).ι → Q.X.functionFieldˣ) (l : Fin d → Ext v → AlgPt Y → ℝ)
    (h₁ : ∀ k, GReads Q v (L k) (u k) fun e y => (m : ℝ) * l k e y) (Z : NModel O) (hZ : ∀ C, (Z.comp C).relDim = d)
    (q : Z.Comp → Prop) (μ : ∀ j : {C // q C}, Match Y b (Z.comp j.1)) (n : ℕ) (hn : 0 < n) (hc : Count μ ε σ n)
    (B₀ B₁ : FinLB Z.X) (w : Z.GenIso B₀.lb B₁.lb) (B : Fin d → FinLB Z.X)
    (h₂ : ∀ j : {C // q C}, ∃ t₀ t₁, Reads (μ j) v (B₀.lb.pull (Z.compι j.1)) t₀ l₀ ∧
      Reads (μ j) v (B₁.lb.pull (Z.compι j.1)) t₁ l₁ ∧
      ∀ i i' (h : genericPoint (Z.comp j.1).X ∈ Z.compι j.1 ⁻¹ᵁ (Z.gen ⊓ (B₀.lb.U i ⊓ B₁.lb.U i'))),
        fnOf _ h ((Z.compι j.1).app _ (w.u i i').val) =
          (t₀ (fun _ => i) : (Z.comp j.1).X.functionField) / (t₁ (fun _ => i') : (Z.comp j.1).X.functionField))
    (h₃ : ∀ (j : {C // q C}) k, ∃ t, Reads (μ j) v ((B k).lb.pull (Z.compι j.1)) t (l k)) :
    (m : ℝ) ^ (d + 1) * placeDeg p v * ∑ C ∈ Finset.univ.filter q,
        (((Z.comp C).capDeg_vp p (NModel.vResQ C (Z.vdiv B₀ B₁ w)) (picSymPull (Z.compι C) (∏ k, (B k).c1)) : ℚ) : ℝ) =
      (n : ℝ) * ∑ᶠ x : Q.X, if (Q.p x).asIdeal = v.asIdeal then
        (((divOfRatSec hM hr).mult x * pdeg p L x : ℤ) : ℝ) else 0 := by
  choose t₀ t₁ a₀ a₁ a₂ using h₂
  choose t ht using h₃
  choose P s hP hs hPr using fun j : {C // q C} => UpperTheory.generic_iso_sections_log F Y O b Z j.1 (μ j) v _ _ B₀.isLB B₁.isLB w
    (t₀ j) (t₁ j) l₀ l₁ (a₀ j) (a₁ j) (a₂ j)
  have key := UpperTheory.normal_model_complex_compat_alt F Y v p hpv F' ε O b hup σ Q hQ d hd m M hM r hr _ h₀ L hL u l h₁ {C // q C}
    (fun j => Z.comp j.1) (fun j => isNormal_comp j.1) (fun j => hZ j.1) μ n hn hc P s hs hPr
    (fun j k => (B k).lb.pull (Z.compι j.1)) (fun j k => LB.isLB_pull (B k).isLB _) t ht
  refine Eq.trans ?_ key
  congr 1
  rw [Finset.sum_subtype (p := q) _ (by simp)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hP, map_prod]
  exact congrArg₂ (fun x y => (((Z.comp j.1).capDeg_vp p x y : ℚ) : ℝ)) (NModel.vResQ_toQ _ _)
    (Finset.prod_congr rfl fun k _ => pullback_firstChern _ _ _)

section Place

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} (fl : s.Flag)
  (hd : ∀ k, (fl.C k).Y.dim = Formalism.DegreeFormula.dimFl D.what₂.Tau N) {p : ℕ} (hp : p.Prime) {W : ValuationSubring ℂ}
  (hW : (p : ℂ) ∈ W.nonunits) (z : AdmAt S κ hp hW) [IsDiscreteValuationRing (z.Z.i.c.V W)]
  (ε : D.what₂.LL →+* z.Z.i.c.F) (b : 𝓞 D.what₂.LL →+* z.Z.i.c.V W)
  (hε : ∀ x, ((ε x : z.Z.i.c.F) : ℂ) = D.what₂.embLL x)

include hd hε in

private theorem loc_cmp [Fact p.Prime] [CharP (ResidueField (z.Z.i.c.V W)) p] (v : HeightOneSpectrum (𝓞 D.what₂.LL))
    (hpv : (p : 𝓞 D.what₂.LL) ∈ v.asIdeal) (hup : IsUp v ε (z.Z.i.c.V W) b) (c : s.Comp) (Cx : CxSt D.what₂.LL)
    (hm : Mets (fl.C c) Cx) (a : Bool → ℕ → Bool) (ha : ∀ k, a k p = k) (R : Option ℝ) (l : Ln S.Dw)
    (ν : Fin (Formalism.DegreeFormula.dimFl D.what₂.Tau N) → Bool × Ln S.Dw) (Q : TrueGeo.Model (fl.C c).Y)
    [AlgebraicGeometry.IsIntegral Q.X] [IsLocallyNoetherian Q.X] (hQ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Q.X) (m : ℕ)
    (M : LB Q.X) (hM : M.IsLB) (r : M.ι → Q.X.functionFieldˣ) (hr : IsRatSec M r)
    (h₀ : GReads Q v M r fun e y => (m : ℝ) * (lam (adlOf (fl.C c) hm (lnSym (a false) R l)) v e y -
      lam (adlOf (fl.C c) hm (lnSym (a true) R l)) v e y))
    (L : Fin (Formalism.DegreeFormula.dimFl D.what₂.Tau N) → LB Q.X) (hL : ∀ k, (L k).IsLB)
    (u : ∀ k, (L k).ι → Q.X.functionFieldˣ)
    (h₁ : ∀ k, GReads Q v (L k) (u k) fun e y =>
      (m : ℝ) * lam (adlOf (fl.C c) hm (lnSym (a (ν k).1) R (ν k).2)) v e y) :
    (m : ℝ) ^ (Formalism.DegreeFormula.dimFl D.what₂.Tau N + 1) * placeDeg p v *
      ∑ C ∈ Finset.univ.filter fun C : (nmodel z.Z).Comp =>
          ∃ μ : Match (fl.C c).Y b ((nmodel z.Z).comp C), Link z.Z C (fl.C c) μ,
        ((((nmodel z.Z).comp C).capDeg_vp p (NModel.vResQ C ((nmodel z.Z).vdiv _ _ (lnId z hp hW l)))
          (picSymPull ((nmodel z.Z).compι C) (∏ k, (lnLB z (ν k).1 (ν k).2).c1)) : ℚ) : ℝ) =
      (cov z : ℝ) * ∑ᶠ x : Q.X, if (Q.p x).asIdeal = v.asIdeal then
        (((divOfRatSec hM hr).mult x * pdeg p L x : ℤ) : ℝ) else 0 := by
  haveI := z.Z.i.c.fin
  haveI : NumberField z.Z.i.c.F := {}
  have hv : resP v = p := (PlaceSum.residueCharacteristic_eq_iff v hp).2 hpv
  let J := {C : (nmodel z.Z).Comp // ∃ μ : Match (fl.C c).Y b ((nmodel z.Z).comp C), Link z.Z C (fl.C c) μ}
  choose μ hμ using fun j : J => j.2
  choose t ht hu using fun (j : J) (x : Ln S.Dw) =>
    reads_ln fl hd hp hW z ε b hε hup.1 v hv j.1 c (μ j) (hμ j) Cx hm a ha R x
  exact loc_gen v p hpv ε (z.Z.i.c.V W) b hup z.Z.i.c.F.val.toRingHom Q hQ (hd c) m M hM r hr _ _ h₀ L hL u _ h₁
    (nmodel z.Z) (RelDim.relDim_comp D A N _ S κ p hp W hW z) _ μ (cov z) (cov_pos z)
    (UpperTheory.admissible_point_lattice_norm D A N _ S κ s fl hd p hp W hW z ε b hε hup.1 c μ hμ) (lnLB z false l) (lnLB z true l) (lnId z hp hW l)
    (fun k => lnLB z (ν k).1 (ν k).2) (fun j => ⟨_, _, ht j l false, ht j l true, hu j l⟩)
    fun j k => ⟨_, ht j (ν k).2 (ν k).1⟩

end Place

private theorem adl_eq_of {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {F : Type} [Field F] [NumberField F]
    {e : F ≃+* c.F} {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)} (Y : FlagCpt Z e) {C : CxSt F}
    (hm : Mets Y C) (a : ℕ → Bool) (p : ℕ) (R : Option ℝ) (x : Ln Dw) {A₀ A₁ : Adl C Y.Y}
    (h₀ : A₀ = adlOf Y hm (lnSym (Function.update a p false) R x))
    (h₁ : A₁ = adlOf Y hm (lnSym (Function.update a p true) R x)) :
    A₁ = { A₀ with lg := A₁.lg } ∧ ∀ v e y, |A₀.lg v e y - A₁.lg v e y| ≤
      (if resP v = p then 1 / ((p : ℝ) - 1) + vDiff E p else 0) * (-Real.log (e.w (resP v : AlgebraicClosure F))) := by
  subst h₀ h₁
  exact ⟨adlOf_lnSym_eq Y hm _ _ R x, abs_lgOf_lnSym_le Y a p R x⟩

private theorem greads_congr {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F} {Q : TrueGeo.Model Y}
    [AlgebraicGeometry.IsIntegral Q.X] {v : HeightOneSpectrum (𝓞 F)} {L : LB Q.X} {s : L.ι → Q.X.functionFieldˣ} {m : ℝ}
    {A A' : Adl C Y} (e : A = A') (h : GReads Q v L s fun e y => m * lam A v e y) :
    GReads Q v L s fun e y => m * lam A' v e y := e ▸ h

private theorem greads_congr₂ {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F} {Q : TrueGeo.Model Y}
    [AlgebraicGeometry.IsIntegral Q.X] {v : HeightOneSpectrum (𝓞 F)} {L : LB Q.X} {s : L.ι → Q.X.functionFieldˣ} {m : ℝ}
    {A A' B B' : Adl C Y} (e : A = A') (e' : B = B') (h : GReads Q v L s fun e y => m * (lam A v e y - lam B v e y)) :
    GReads Q v L s fun e y => m * (lam A' v e y - lam B' v e y) := e ▸ e' ▸ h

private theorem places_sum (D : D7) (p : ℕ) [Fact p.Prime] [Fintype (Formalism.L2.Geo.PlL D p)] {Y : Var D.what₂.LL}
    (Q : TrueGeo.Model Y) [AlgebraicGeometry.IsIntegral Q.X] [IsLocallyNoetherian Q.X] (Dv : CartierDiv Q.X)
    (g : Q.X → ℤ) (hmult : ∀ x, Dv.mult x ≠ 0 → (p : 𝓞 D.what₂.LL) ∈ (Q.p x).asIdeal) (m : ℕ+) (d : ℕ)
    (T cv : Formalism.L2.Geo.PlL D p → ℝ) (hcv : ∀ la, cv la ≠ 0)
    (key : ∀ la, ((m : ℕ) : ℝ) ^ (d + 1) * placeDeg p la.1 * T la =
      cv la * ∑ᶠ x : Q.X, if (Q.p x).asIdeal = la.1.asIdeal then ((Dv.mult x * g x : ℤ) : ℝ) else 0) :
    (Real.log p * ∑ᶠ x : Q.X, ((Dv.mult x * g x : ℤ) : ℝ)) /
        (((m : ℕ) : ℝ) ^ (d + 1) * (Module.finrank ℚ D.what₂.LL : ℝ)) =
      Real.log p * ∑ la, Formalism.L2.Geo.wtL D p la * (T la / cv la) := by
  have hp : p.Prime := Fact.out
  haveI : AlgebraicGeometry.IsNoetherian Q.X := Q.ar.isNoetherian
  rw [finsum_eq_sum_places _ (Dv.finite_support_mult.subset fun x hx h0 => hx (by simp [h0]))
    (fun x => (Q.p x).asIdeal) (fun la : Formalism.L2.Geo.PlL D p => la.1.asIdeal)
    (fun la la' e => Subtype.ext (HeightOneSpectrum.ext e)) fun x hx => ?_, mul_div_assoc, Finset.sum_div]
  · congr 1
    refine Finset.sum_congr rfl fun la _ => ?_
    have h₁ : cv la ≠ 0 := hcv la
    have h₂ : ((m : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 m.ne_zero
    have h₃ : (Module.finrank ℚ D.what₂.LL : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
    have h₄ : Formalism.L2.Geo.wtL D p la = placeDeg p la.1 / (Module.finrank ℚ D.what₂.LL : ℝ) := by
      rw [Formalism.L2.Geo.wtL, placeDeg, div_div]
    have h₅ := (div_eq_iff h₁).2 ((key la).trans (mul_comm _ _))
    rw [h₄]
    refine (congrArg (· / _) h₅.symm).trans ?_
    field_simp
  · have hx' := hmult x fun h0 => hx (by simp [h0])
    refine ⟨⟨⟨(Q.p x).asIdeal, (Q.p x).2, fun e => ?_⟩, hx'⟩, rfl⟩
    rw [e, Ideal.mem_bot] at hx'
    exact Nat.cast_ne_zero.2 hp.ne_zero hx'

private theorem bound_nonneg (E : Type) [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) :
    0 ≤ 1 / ((p : ℝ) - 1) + vDiff E p := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  exact add_nonneg (div_nonneg zero_le_one (by linarith)) (by unfold vDiff; positivity)

private theorem glob_gen (h2 : GlobalTheory.CovTop.Hypotheses2) (D : D7) (p : ℕ) [Fact p.Prime] [Fintype (Formalism.L2.Geo.PlL D p)]
    {Y : Var D.what₂.LL} (M : TrueGeo.Model Y) {ι : Type} [Fintype ι] (A : ι → Adl (cxSt D.what₂.LL) Y)
    (L : ι → HermLB M.p) (m : ℕ+) (Ψ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ) (hI : ∀ i, (A i).Induced M (L i) m 0)
    (hΨ : haveI := M.ar.isIntegral; GlobalTheory.ArInt.IsArFun L Y.dim Ψ) (i₀ i₁ : ι)
    (e₁ : A i₁ = { A i₀ with lg := (A i₁).lg }) (c : ℝ) (hc : 0 ≤ c)
    (e₂ : ∀ v e y, |(A i₀).lg v e y - (A i₁).lg v e y| ≤
      (if resP v = p then c else 0) * (-Real.log (e.w (resP v : AlgebraicClosure D.what₂.LL))))
    {d : ℕ} (hd : Y.dim = d) (ν : Fin d → ι) (T cv : Formalism.L2.Geo.PlL D p → ℝ) (hcv : ∀ la, cv la ≠ 0)
    (key : ∀ (la : Formalism.L2.Geo.PlL D p) (Q : TrueGeo.Model Y) [AlgebraicGeometry.IsIntegral Q.X] [IsLocallyNoetherian Q.X]
      (_ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Q.X) (M₀ : LB Q.X) (hM₀ : M₀.IsLB) (r : M₀.ι → Q.X.functionFieldˣ)
      (hr : IsRatSec M₀ r) (_ : GReads Q la.1 M₀ r fun e y => ((m : ℕ) : ℝ) * (lam (A i₀) la.1 e y - lam (A i₁) la.1 e y))
      (N : Fin d → LB Q.X) (_ : ∀ k, (N k).IsLB) (s : ∀ k, (N k).ι → Q.X.functionFieldˣ)
      (_ : ∀ k, GReads Q la.1 (N k) (s k) fun e y => ((m : ℕ) : ℝ) * lam (A (ν k)) la.1 e y),
      ((m : ℕ) : ℝ) ^ (d + 1) * placeDeg p la.1 * T la = cv la * ∑ᶠ x : Q.X, if (Q.p x).asIdeal = la.1.asIdeal then
        (((divOfRatSec hM₀ hr).mult x * pdeg p N x : ℤ) : ℝ) else 0) :
    Ψ ((MvPolynomial.X i₀ - MvPolynomial.X i₁) * ∏ i, MvPolynomial.X (ν i)) /
        (((m : ℕ) : ℝ) ^ (d + 1) * (Module.finrank ℚ D.what₂.LL : ℝ)) =
      Real.log p * ∑ la, Formalism.L2.Geo.wtL D p la * (T la / cv la) := by
  obtain ⟨Q, _, _, Nb, sb, M₀, hM₀, r, hr, hQ, hN, hs, h₀, hmult, hΨ'⟩ :=
    UpperTheory.arithmetic_function_induced_bound h2 _ _ M _ A L m Ψ hI hΨ p i₀ i₁ e₁ c hc e₂ d hd
  rw [hΨ' ν]
  exact places_sum D p Q _ _ hmult m d T cv hcv fun la => key la Q hQ M₀ hM₀ r hr (h₀ la.1) (fun k => Nb (ν k))
    (fun k => hN _) (fun k => sb (ν k)) fun k => hs la.1 (ν k)

section Main

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} (fl : s.Flag)
  (hd : ∀ k, (fl.C k).Y.dim = Formalism.DegreeFormula.dimFl D.what₂.Tau N) {p : ℕ} [Fact p.Prime]
  {W : Formalism.L2.Geo.PlL D p → ValuationSubring ℂ} (hW : ∀ la, (p : ℂ) ∈ (W la).nonunits)
  (z : ∀ la, AdmAt S κ (Fact.out : p.Prime) (hW la)) [∀ la, IsDiscreteValuationRing ((z la).Z.i.c.V (W la))]
  [∀ la, CharP (ResidueField ((z la).Z.i.c.V (W la))) p]
  (ε : ∀ la, D.what₂.LL →+* (z la).Z.i.c.F) (b : ∀ la, 𝓞 D.what₂.LL →+* (z la).Z.i.c.V (W la))
  (hε : ∀ la x, ((ε la x : (z la).Z.i.c.F) : ℂ) = D.what₂.embLL x)
  (hup : ∀ la, IsUp la.1 (ε la) ((z la).Z.i.c.V (W la)) (b la))

include hd hε hup in

private theorem comp_cmp [Fintype (Formalism.L2.Geo.PlL D p)] (h2 : GlobalTheory.CovTop.Hypotheses2) (c : s.Comp)
    (hm : Mets (fl.C c) (cxSt D.what₂.LL)) (a₀ : ℕ → Bool) (R : Option ℝ) (l : Ln S.Dw)
    (ν : Fin (Formalism.DegreeFormula.dimFl D.what₂.Tau N) → Bool × Ln S.Dw) (M : TrueGeo.Model (fl.C c).Y)
    (L : Bool ⊕ Fin (Formalism.DegreeFormula.dimFl D.what₂.Tau N) → HermLB M.p) (m : ℕ+)
    (Ψ : MvPolynomial (Bool ⊕ Fin (Formalism.DegreeFormula.dimFl D.what₂.Tau N)) ℝ →ₗ[ℝ] ℝ)
    (A' : Bool ⊕ Fin (Formalism.DegreeFormula.dimFl D.what₂.Tau N) → Adl (cxSt D.what₂.LL) (fl.C c).Y)
    (hA₀ : ∀ k, A' (.inl k) = adlOf (fl.C c) hm (lnSym (Function.update a₀ p k) R l))
    (hA₁ : ∀ i, A' (.inr i) = adlOf (fl.C c) hm (lnSym (Function.update a₀ p (ν i).1) R (ν i).2))
    (hI : ∀ i, (A' i).Induced M (L i) m 0)
    (hΨ : haveI := M.ar.isIntegral; GlobalTheory.ArInt.IsArFun L (fl.C c).Y.dim Ψ) :
    Ψ ((MvPolynomial.X (.inl false) - MvPolynomial.X (.inl true)) * ∏ i, MvPolynomial.X (.inr i)) /
        (((m : ℕ) : ℝ) ^ (Formalism.DegreeFormula.dimFl D.what₂.Tau N + 1) * (Module.finrank ℚ D.what₂.LL : ℝ)) =
      Real.log p * ∑ la, Formalism.L2.Geo.wtL D p la * ((∑ C ∈ Finset.univ.filter fun C : (nmodel (z la).Z).Comp =>
          ∃ μ : Match (fl.C c).Y (b la) ((nmodel (z la).Z).comp C), Link (z la).Z C (fl.C c) μ,
        ((((nmodel (z la).Z).comp C).capDeg_vp p
          (NModel.vResQ C ((nmodel (z la).Z).vdiv _ _ (lnId (z la) Fact.out (hW la) l)))
          (picSymPull ((nmodel (z la).Z).compι C) (∏ k, (lnLB (z la) (ν k).1 (ν k).2).c1)) : ℚ) : ℝ)) /
        (cov (z la) : ℝ)) := by
  have e₀ := adl_eq_of (fl.C c) hm a₀ p R l (hA₀ false) (hA₀ true)
  refine glob_gen h2 D p M A' L m Ψ hI hΨ (.inl false) (.inl true) e₀.1 _ (bound_nonneg _ Fact.out) e₀.2 (hd c) Sum.inr _
    (fun la => (cov (z la) : ℝ)) (fun la => Nat.cast_ne_zero.2 (cov_pos (z la)).ne') ?_
  intro la Q _ _ hQ M₀ hM₀ r hr h₀ Nb hN sb hs
  have k₀ := greads_congr₂ (hA₀ false) (hA₀ true) h₀
  have k₁ (k) := greads_congr (hA₁ k) (hs k)
  have key := loc_cmp fl hd Fact.out (hW la) (z la) (ε la) (b la) (hε la) la.1 la.2 (hup la) c _ hm
    (Function.update a₀ p) (fun _ => Function.update_self _ _ _) R l ν Q hQ m M₀ hM₀ r hr k₀ Nb hN sb k₁
  exact key

end Main

private theorem sum_part {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Z : NModel O) (p d : ℕ)
    (hZ : ∀ C, (Z.comp C).relDim = d) {T : Type} [Fintype T] (r : Z.Comp → T → Prop) (h : ∀ C, ∃! t, r C t)
    (Dv : Z.VDivQ) (G : PicSym Z.X) :
    ∑ t, ∑ C ∈ Finset.univ.filter fun C => r C t,
      (((Z.comp C).capDeg_vp p (NModel.vResQ C Dv) (picSymPull (Z.compι C) G) : ℚ) : ℝ) =
      ((Z.capDeg_vp p d Dv G : ℚ) : ℝ) := by
  rw [sum_filter_partition _ _ h, NModel.capDeg_vp_eq_sum, Finset.filter_true_of_mem fun C _ => hZ C, Rat.cast_sum]

private theorem num_sub {B : Type} {d d' : ℕ} (hd : d' = d) (num : Multiset B → ℝ) (w₀ : Bool → B) (w₁ : Fin d → B)
    (Ψ : MvPolynomial (Bool ⊕ Fin d) ℝ →ₗ[ℝ] ℝ) (m c : ℝ)
    (h : ∀ μ : Multiset (Bool ⊕ Fin d), Multiset.card μ = d' + 1 →
      num (μ.map (Sum.elim w₀ w₁)) = Ψ (μ.map MvPolynomial.X).prod / (m ^ (d' + 1) * c)) :
    num (w₀ false ::ₘ Finset.univ.val.map w₁) - num (w₀ true ::ₘ Finset.univ.val.map w₁) =
      Ψ ((MvPolynomial.X (.inl false) - MvPolynomial.X (.inl true)) * ∏ i, MvPolynomial.X (.inr i)) /
        (m ^ (d + 1) * c) := by
  subst hd
  have e (k : Bool) : num (w₀ k ::ₘ Finset.univ.val.map w₁) =
      Ψ (MvPolynomial.X (.inl k) * ∏ i, MvPolynomial.X (.inr i)) / (m ^ (d' + 1) * c) := by
    have := h (.inl k ::ₘ Finset.univ.val.map Sum.inr) (by simp)
    rw [Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons, Multiset.map_map, Multiset.map_map] at this
    exact this
  rw [e, e, ← sub_div, ← map_sub, ← sub_mul]

private theorem sum_link {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} (fl : s.Flag) [Fintype s.Comp]
    (hd : ∀ k, (fl.C k).Y.dim = Formalism.DegreeFormula.dimFl D.what₂.Tau N) {p : ℕ} (hp : p.Prime) {W : ValuationSubring ℂ}
    (hW : (p : ℂ) ∈ W.nonunits) (z : AdmAt S κ hp hW) [IsDiscreteValuationRing (z.Z.i.c.V W)]
    (ε : D.what₂.LL →+* z.Z.i.c.F) (b : 𝓞 D.what₂.LL →+* z.Z.i.c.V W)
    (hε : ∀ x, ((ε x : z.Z.i.c.F) : ℂ) = D.what₂.embLL x)
    (hb : ∀ x : 𝓞 D.what₂.LL, ((b x : z.Z.i.c.V W) : z.Z.i.c.F) = ε (x : D.what₂.LL))
    (Dv : (nmodel z.Z).VDivQ) (G : PicSym (nmodel z.Z).X) :
    ∑ c : s.Comp, ∑ C ∈ Finset.univ.filter fun C : (nmodel z.Z).Comp =>
        ∃ μ : Match (fl.C c).Y b ((nmodel z.Z).comp C), Link z.Z C (fl.C c) μ,
      ((((nmodel z.Z).comp C).capDeg_vp p (NModel.vResQ C Dv) (picSymPull ((nmodel z.Z).compι C) G) : ℚ) : ℝ) =
      (((nmodel z.Z).capDeg_vp p (Formalism.DegreeFormula.dimFl D.what₂.Tau N) Dv G : ℚ) : ℝ) := by
  refine sum_part (nmodel z.Z) p _ (RelDim.relDim_comp D A N j S κ p hp W hW z)
    (fun C c => ∃ μ : Match (fl.C c).Y b ((nmodel z.Z).comp C), Link z.Z C (fl.C c) μ) (fun C => ?_) Dv G
  have h := UpperTheory.admissible_point_discrete_valuation D A N j S κ s fl hd p hp W hW z ε b hε hb C
  exact h.imp fun c h => ⟨h, fun c' h' => h.elim fun μ hμ => h'.elim fun μ' hμ' =>
    UpperTheory.admissible_point_charts D A N j S κ s fl hd p hp W hW z ε b hε hb C c' c μ' μ hμ' hμ⟩

private theorem sum_comp {Cp ι : Type} [Fintype Cp] [Fintype ι] (n₀ n₁ : Cp → ℝ) (lg : ℝ) (w cv T : ι → ℝ) (t : ι → Cp → ℝ)
    (h : ∀ c, n₀ c - n₁ c = lg * ∑ i, w i * (t i c / cv i)) (ht : ∀ i, ∑ c, t i c = T i) :
    ∑ c, (n₀ c - n₁ c) = lg * ∑ i, w i * (T i / cv i) := by
  simp only [h, ← ht]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp only [← Finset.mul_sum, ← Finset.sum_div]

section OnePlace

private theorem place_arith {Cp : Type} [Fintype Cp] (pd T cv : ℝ) (hcv : cv ≠ 0) (t f mm : Cp → ℝ) (hm : ∀ c, mm c ≠ 0)
    (h : ∀ c, mm c * pd * t c = cv * f c) (ht : ∑ c, t c = T) : pd * (T / cv) = ∑ c, f c / mm c := by
  rw [← ht, Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  have := hm c
  rw [eq_div_iff this, ← mul_right_inj' hcv, ← h c]
  field_simp

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} {p : ℕ} [Fact p.Prime]
  {W : ValuationSubring ℂ} {hW : (p : ℂ) ∈ W.nonunits}

private theorem place (z : AdmAt S κ (Fact.out : p.Prime) hW) (fl : s.Flag)
    (hd : ∀ k, (fl.C k).Y.dim = Formalism.DegreeFormula.dimFl D.what₂.Tau N) (v : HeightOneSpectrum (𝓞 D.what₂.LL))
    (hpv : (p : 𝓞 D.what₂.LL) ∈ v.asIdeal)
    (hv : ∀ x : D.what₂.LL, D.what₂.embLL x ∈ W ↔ v.valuation D.what₂.LL x ≤ 1) {Cx : CxSt D.what₂.LL}
    (hm : ∀ c, Mets (fl.C c) Cx) (a₀ : ℕ → Bool) (R : Option ℝ) (l : Ln S.Dw)
    (ν : Fin (Formalism.DegreeFormula.dimFl D.what₂.Tau N) → Bool × Ln S.Dw) (Q : ∀ c, TrueGeo.Model (fl.C c).Y)
    [∀ c, AlgebraicGeometry.IsIntegral (Q c).X] [∀ c, IsLocallyNoetherian (Q c).X]
    (hQ : ∀ c, ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Q c).X) (m : s.Comp → ℕ) (hm0 : ∀ c, m c ≠ 0)
    (M : ∀ c, LB (Q c).X) (hM : ∀ c, (M c).IsLB) (r : ∀ c, (M c).ι → (Q c).X.functionFieldˣ)
    (hr : ∀ c, IsRatSec (M c) (r c))
    (h₀ : ∀ c, GReads (Q c) v (M c) (r c) fun e y => (m c : ℝ) *
      (lam (adlOf (fl.C c) (hm c) (lnSym (Function.update a₀ p false) R l)) v e y -
        lam (adlOf (fl.C c) (hm c) (lnSym (Function.update a₀ p true) R l)) v e y))
    (L : ∀ c, Fin (Formalism.DegreeFormula.dimFl D.what₂.Tau N) → LB (Q c).X) (hL : ∀ c k, (L c k).IsLB)
    (u : ∀ c k, (L c k).ι → (Q c).X.functionFieldˣ)
    (h₁ : ∀ c k, GReads (Q c) v (L c k) (u c k) fun e y =>
      (m c : ℝ) * lam (adlOf (fl.C c) (hm c) (lnSym (Function.update a₀ p (ν k).1) R (ν k).2)) v e y) :
    placeDeg p v * ((((ithOf Fact.out hW z.Z (Formalism.DegreeFormula.dimFl D.what₂.Tau N)).capDeg
        (vdiv Fact.out hW _ _ _ (lnId z Fact.out hW l)) (∏ i, (lnLB z (ν i).1 (ν i).2).c1) : ℚ) : ℝ) / (cov z : ℝ)) =
      ∑ c, (∑ᶠ y : (Q c).X, if ((Q c).p y).asIdeal = v.asIdeal then
        (((divOfRatSec (hM c) (hr c)).mult y * pdeg p (L c) y : ℤ) : ℝ) else 0) /
          (m c : ℝ) ^ (Formalism.DegreeFormula.dimFl D.what₂.Tau N + 1) := by
  haveI := isDiscreteValuationRing_V z.Z.i.c Fact.out hW
  haveI := charP_residueField_of_mem_nonunits z.Z.i.c Fact.out hW
  have H := exists_up z v hv
  obtain ⟨ε, b, hε, hup⟩ := H
  have k₁ (c : s.Comp) := loc_cmp fl hd Fact.out hW z ε b hε v hpv hup c Cx (hm c) (Function.update a₀ p)
    (fun _ => Function.update_self _ _ _) R l ν (Q c) (hQ c) (m c) (M c) (hM c) (r c) (hr c) (h₀ c) (L c) (hL c) (u c)
    (h₁ c)
  have k₂ := sum_link fl hd Fact.out hW z ε b hε hup.1
    ((nmodel z.Z).vdiv _ _ (lnId z Fact.out hW l)) (∏ k, (lnLB z (ν k).1 (ν k).2).c1)
  exact place_arith _ _ _ (Nat.cast_ne_zero.2 (cov_pos z).ne') _ _ _
    (fun c => pow_ne_zero _ (Nat.cast_ne_zero.2 (hm0 c))) k₁ k₂

end OnePlace

theorem pairSt : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.CovHt.HypothesesH → GlobalTheory.PairTerm.PairSt := by
  intro h2 hH D O hO p _ W hW hWv z Sx R hR l ν
  obtain ⟨x, P, h⟩ := hO
  letI := Formalism.L2.Geo.finPl D p
  haveI : ∀ la, IsDiscreteValuationRing ((z la).Z.i.c.V (W la)) :=
    fun la => isDiscreteValuationRing_V (z la).Z.i.c Fact.out (hW la)
  haveI : ∀ la, CharP (ResidueField ((z la).Z.i.c.V (W la))) p :=
    fun la => charP_residueField_of_mem_nonunits (z la).Z.i.c Fact.out (hW la)
  choose ε b hε hup using fun la => exists_up (z la) la.1 (hWv la)
  let w : Bool ⊕ Fin (Formalism.DegreeFormula.dimFl D.what₂.Tau O.N) → Sym D.host.E →₀ ℤ :=
    Sum.elim (fun k => lnSym (Function.update (ArIn.ind Sx) p k) (some R) l)
      (fun i => lnSym (Function.update (ArIn.ind Sx) p (ν i).1) (some R) (ν i).2)
  have hw : ∀ k, ∀ b ∈ (w k).support, {q | b.1 q = true}.Finite ∧ b.2.1 = some R := by
    have ha (b : Bool) : {q | Function.update (ArIn.ind Sx) p b q = true}.Finite :=
      (insert p Sx).finite_toSet.subset fun q hq => by
        by_cases e : q = p
        · simp [e]
        · simpa [ArIn.ind, e] using hq
    rintro (q | q) b hb <;> obtain ⟨e₁, e₂⟩ := mem_support_lnSym hb <;> exact ⟨e₁ ▸ ha _, e₂⟩
  choose M L m Ψ hI hΨ hnum using fun c =>
    (GlobalTheory.ArTopTrue.arTop_true h2.p4 hH.deg HTBound.htBound D _ _ _ _ _ O.s x O.Φ c R hR).2 _ w hw
  have key (c : O.s.Comp) := comp_cmp O.Φ O.dim_eq hW z ε b hε hup h2 c (metsOf x O.Φ c) (ArIn.ind Sx) (some R) l ν
    (M c) (L c) (m c) (Ψ c) (fun i => adlOf (O.Φ.C c) (metsOf x O.Φ c) (w i)) (fun _ => rfl) (fun _ => rfl) (hI c) (hΨ c)
  rw [h.hm_eq]
  have k₁ (c : O.s.Comp) := (num_sub (O.dim_eq c) ((arIn O.s O.Φ (metsOf x O.Φ)).num c)
    (fun k => lnSym (Function.update (ArIn.ind Sx) p k) (some R) l)
    (fun i => lnSym (Function.update (ArIn.ind Sx) p (ν i).1) (some R) (ν i).2) (Ψ c) _ _ (hnum c)).trans (key c)
  have k₂ (la) := sum_link O.Φ O.dim_eq Fact.out (hW la) (z la) (ε la) (b la) (hε la) (hup la).1
    ((nmodel (z la).Z).vdiv _ _ (lnId (z la) Fact.out (hW la) l)) (∏ k, (lnLB (z la) (ν k).1 (ν k).2).c1)
  exact sum_comp _ _ _ _ _ _ _ k₁ k₂

end GlobalTheory.PairMain

end
