import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.VertCmp
import Development.AutomorphicArithmetic.DivisorFrames.ExistsUnitTriAndDiagCoeffMulEqOfCarries
import Development.AutomorphicArithmetic.DivisorFrames.ExistsStalkPointLift
import Development.AutomorphicArithmetic.DivisorFrames.MetricLetterHeight
import Development.AutomorphicArithmetic.DivisorFrames.GenericStalkSectionUnit
import Development.AutomorphicArithmetic.DivisorFrames.AdmissibleModelValuationAlt
import Development.AutomorphicArithmetic.DivisorFrames.AdmissibleFlagValuation
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ScaledTwistingSheafSpec
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.Toroidal
open GlobalTheory.VertCmp
open scoped Classical

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  {Z : LocM.Mdl Y i₀} {k : Bool} {st : ((E →+* ℂ) × ℕ) ⊕ ℕ} {x : Pad.Letter Dw}

private theorem top_le_gen {X X' : Scheme.{0}} [IsIntegral X] {q : X ⟶ X'} {V : X'.Opens}
    (h : genericPoint X ∈ q ⁻¹ᵁ V) : ⊤ ≤ (X.fromSpecStalk (genericPoint X) ≫ q) ⁻¹ᵁ V := by
  refine (Scheme.preimage_eq_top_of_closedPoint_mem _ ?_).ge
  have e : (X.fromSpecStalk (genericPoint X) ≫ q) (closedPoint (X.presheaf.stalk (genericPoint X))) =
      q (genericPoint X) := (Scheme.Hom.comp_apply _ _ _).trans (congrArg q Scheme.fromSpecStalk_closedPoint)
  exact e ▸ h

private theorem exists_sec (M : LineModel Z k st x) {X : Scheme.{0}} [IsIntegral X] (q : X ⟶ Z.X) (a : Fin Z.m)
    (ha : genericPoint X ∈ q ⁻¹ᵁ (Z.U a).1) (c₀ : X.functionFieldˣ) :
    ∃ t : (M.L.lb.pull q).ι → X.functionFieldˣ, IsRatSec (M.L.lb.pull q) t ∧
      ∀ i, genericPoint X ∈ q ⁻¹ᵁ M.L.U (i PUnit.unit) → (t i : X.functionField) *
        valF (F := X.functionField) (X.fromSpecStalk (genericPoint X) ≫ q) _ (M.r a (i PUnit.unit)).val = c₀ := by
  let ρ : Fin M.L.n → X.functionField := fun i =>
    valF (F := X.functionField) (X.fromSpecStalk (genericPoint X) ≫ q) _ (M.r a i).val
  have n : ∀ i, genericPoint X ∈ q ⁻¹ᵁ M.L.U i → ρ i ≠ 0 := fun i hi =>
    left_ne_zero_of_mul_eq_one (Pull.valF_mul_inv (F := X.functionField)
      (top_le_gen (V := (Z.U a).1 ⊓ M.L.U i) ⟨ha, hi⟩) (M.r a i))
  let t : (M.L.lb.pull q).ι → X.functionFieldˣ := fun i =>
    if h : ρ (i PUnit.unit) ≠ 0 then c₀ * (Units.mk0 _ h)⁻¹ else 1
  have ht : ∀ i, genericPoint X ∈ q ⁻¹ᵁ M.L.U (i PUnit.unit) → (t i : X.functionField) * ρ (i PUnit.unit) = c₀ :=
    fun i hi => by
      have := n _ hi
      simp only [t, dif_pos this, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
      field_simp
  refine ⟨t, fun i j hij => ?_, ht⟩
  have le : (M.L.lb.pull q).U i ⊓ (M.L.lb.pull q).U j ≤ q ⁻¹ᵁ (M.L.U (i PUnit.unit) ⊓ M.L.U (j PUnit.unit)) :=
    fun x hx => ⟨LB.pull_U_le q i hx.1, LB.pull_U_le q j hx.2⟩
  have e₁ := M.trans X.functionField (X.fromSpecStalk (genericPoint X) ≫ q) a (i PUnit.unit) (j PUnit.unit)
    (top_le_gen ⟨ha, le hij⟩)
  have e₂ : fnOf _ hij ((M.L.lb.pull q).g i j).val = valF (F := X.functionField)
      (X.fromSpecStalk (genericPoint X) ≫ q) _ (M.L.g (i PUnit.unit) (j PUnit.unit)).val := by
    rw [(UpperTheory.generic_stalk_section_unit X Z.X q _ _).1 (le hij), InducedPull.val_pull_g M.L.lb q i j le]
    exact fnOf_resG le hij _
  refine mul_right_cancel₀ (n _ (le hij).1) ?_
  rw [ht i (le hij).1, e₂, ← ht j (le hij).2]
  simp only [ρ]
  rw [e₁]
  ring

private theorem bc_comp {X : Scheme.{0}} {t : SAB H X} {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    (χ : B →+* C) (ρ : A →+* B) (u : Vecs Dw t A) :
    (fun σ m => spMap (dualMap (χ.comp ρ)) ≫ u σ m) = Vecs.bc χ (Vecs.bc ρ u) := by
  funext σ m
  rw [Vecs.bc, Vecs.bc, ← Category.assoc, ModelRelProbe.spMap_comp]
  congr 2
  ext w <;> simp [dualMap]

private theorem lnStep_congr {X : Scheme.{0}} {t : SAB H X} {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]
    {x x' : Sp C ⟶ X} {u u' : Vecs Dw t C} (hx : x = x') (hu : u = u') (p : ℕ) (b : Bool)
    (st : ((E →+* ℂ) × ℕ) ⊕ ℕ) : lnStep t x u p b st = lnStep t x' u' p b st := by
  rw [hx, hu]

private theorem symLog_eq {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
    {T : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Φ : FlagCpt T e)
    (a : ℕ → Bool) (st : ((E →+* ℂ) × ℕ) ⊕ ℕ) (v : HeightOneSpectrum (𝓞 F)) (ε : TrueGeo.Ext v) (y : AlgPt Φ.Y)
    (hp : (resP v).Prime) : ∃ _ : Fact (resP v).Prime,
    GlobalTheory.LineNorm.symLog Φ a st v ε y = (-Real.log (ε.w (resP v)) / Real.log (resP v)) *
      lnStep T.t (spMap ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom) ≫ stalkPt Φ.Y (below y.1) ≫ Φ.π ≫
        genι T) (Vecs.bc (ioOf (resP v) ε) (Vecs.bc (Scheme.stalkClosedPointTo y.1).hom (GlobalTheory.LineNorm.fr Φ (below y.1)).v)) (resP v) (a (resP v)) st := by
  apply Exists.intro
  refine (dif_pos hp).trans ?_
  refine congrArg (HMul.hMul _) ?_
  exact lnStep_congr rfl (bc_comp _ _ _) _ _ _

private theorem reads_sec {O : Type} [CommRing O] {β : O →+* i₀.c.F}
    {T : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model (Xo i₀.l) i₀.c β} {b₀ : O →+* i₀.c.V W} (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits)
    (hb : (i₀.c.V W).subtype.comp b₀ = β) (hD : Dominates T (Y i₀) b₀) {F : Type} [Field F] [NumberField F]
    {e : F ≃+* i₀.c.F} {Φ : FlagCpt T e} {O' : Type} [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O']
    {b : 𝓞 F →+* O'} {B : Vert.Model O'} (μ : Match Φ.Y b B) (q : B.X ⟶ Z.X) (a : Fin Z.m)
    {τ : (Y Z.i).X ⟶ (Y i₀).X} {mu : SABMap (Y Z.i).t (Y i₀).t τ} {y : μ.U.toScheme ⟶ (Xo i₀.l).XF i₀.c}
    (hT : LocM.IsTrans i₀ Z.i τ mu) (h₁ : y ≫ (Y i₀).j = μ.U.ι ≫ q ≫ Z.π ≫ τ) (h₂ : y ≫ T.jQ = μ.h ≫ Φ.π)
    (hx : letterOf Dw st = some x) (M : LineModel Z k st x) (c₀ : B.X.functionFieldˣ)
    (hB : ∀ (k : Type) [Field k] (z : Sp k ⟶ μ.U.toScheme) (y₁ : Sp k ⟶ Φ.Y.X), z ≫ μ.h = y₁ → ∃ (s : B.X.functionField) (φ' : Γ(Z.X, (Z.U a).1) →+* k) (f' : i₀.c.F →+* k) (u : Vecs Dw T.t k) (cf : Fin (Dw.mult x.1) → k), UnitAt (below (z ≫ μ.U.ι)) s ∧ s * (c₀ : B.X.functionField) = μ.φ (GlobalTheory.LineNorm.dg Φ (below y₁) x.1 x.2 : Φ.Y.Fn) ∧ TrueGeo.valAt (z ≫ μ.U.ι) s = cf x.2 ∧ spMap φ' ≫ Z.chart a = (z ≫ μ.U.ι) ≫ q ∧ (z ≫ y) ≫ pullback.snd _ _ = spMap f' ∧ LocM.IsFrame T.t f' ((z ≫ y) ≫ T.j) u ∧ LocM.IsFrame T.t f' ((z ≫ y) ≫ T.j) (Vecs.bc (Scheme.stalkClosedPointTo y₁).hom (GlobalTheory.LineNorm.fr Φ (below y₁)).v) ∧ (∀ σ m, Transp T (Y i₀) (z ≫ y) (u σ m) ((Z.fr a).bc φ' σ m ≫ mu.φ)) ∧ (∀ σ, Pull.Tri T.t ((z ≫ y) ≫ T.j) (Vecs.bc (Scheme.stalkClosedPointTo y₁).hom (GlobalTheory.LineNorm.fr Φ (below y₁)).v σ) (u σ)) ∧ IsCombAtG T.t ((z ≫ y) ≫ T.j) (Vecs.bc (Scheme.stalkClosedPointTo y₁).hom (GlobalTheory.LineNorm.fr Φ (below y₁)).v x.1) cf (u x.1 x.2))
    {t : (M.L.lb.pull q).ι → B.X.functionFieldˣ} (ht₀ : IsRatSec (M.L.lb.pull q) t)
    (ht : ∀ i, genericPoint B.X ∈ q ⁻¹ᵁ M.L.U (i PUnit.unit) → (t i : B.X.functionField) *
        valF (F := B.X.functionField) (B.X.fromSpecStalk (genericPoint B.X) ≫ q) _ (M.r a (i PUnit.unit)).val = c₀)
    {v : HeightOneSpectrum (𝓞 F)} (hv : resP v = p) {Cx : CxSt F} (hm : Mets Φ Cx) (a' : ℕ → Bool) (R : Option ℝ)
    (ha' : a' p = k) : Reads μ v (M.L.lb.pull q) t (lam (adlOf Φ hm (Finsupp.single (a', R, st) 1)) v) := by
  subst hv
  refine ⟨ht₀, (Φ.gr x.1 x.2).supp.compl, CartierDiv.genericPoint_notMem_supp _, fun ε y₁ z zt i hy hz hzt hi => ?_⟩
  obtain ⟨s, φ', f', u, cf, s₁, s₂, s₃, k₁, k₂, F₁, F₂, k₃, k₄, k₅⟩ := hB _ z y₁.1 hz
  obtain ⟨d₁, d₂⟩ := UpperTheory.metric_letter_height E H Dw _ _ _ O β T F e Φ Cx hm a' R st x hx v ε y₁ hy
  obtain ⟨-, -, -, -, -, -, -, hD'⟩ := UpperTheory.exists_stalk_point_lift F O' Φ.Y b B μ _ z y₁.1 hz
  obtain ⟨d₃, d₄⟩ := hD' _ d₁
  obtain ⟨_, sy⟩ := symLog_eq Φ a' st v ε y₁ hp
  have io₁ := ioOf_le_one_iff (resP v) (residueCharacteristic_mem v) ε
  have io₂ := log_w_eq (resP v) ε _ io₁
  have hi' : ⊤ ≤ (zt ≫ q) ⁻¹ᵁ M.L.U (i PUnit.unit) := fun w hw => LB.pull_U_le q i (hi hw)
  have w₀ : spMap ε.O.subtype ≫ zt ≫ q = (z ≫ μ.U.ι) ≫ q := by rw [← hzt, Category.assoc]
  have w₁ : ⊤ ≤ ((z ≫ μ.U.ι) ≫ q) ⁻¹ᵁ ((Z.U a).1 ⊓ M.L.U (i PUnit.unit)) := fun w hw =>
    ⟨Pull.le_of_fromSpec (Z.U a).2 k₁ hw, by rw [← w₀]; exact hi' (Set.mem_univ (spMap ε.O.subtype w))⟩
  obtain ⟨r₁, r₂⟩ := (UpperTheory.generic_stalk_section_unit B.X Z.X q _ (M.r a (i PUnit.unit)).val).2 _ (z ≫ μ.U.ι) w₁ (Units.isUnit _)
  have N := UpperTheory.admissible_model_valuation_alt E H Dw Xo _ W Y i₀ Z O β T b₀ hp hW hb hD k st x hx M a (i PUnit.unit) τ mu hT _ ε.O
    (ioOf (resP v) ε) io₁ (zt ≫ q) φ' (z ≫ y) f' u _ cf (k₁.trans w₀.symm) hi'
    (by rw [w₀, Category.assoc, h₁]; simp only [Category.assoc]) k₂ F₁ F₂ k₃ k₄ k₅
  have g₀ : genericPoint B.X ∈ q ⁻¹ᵁ M.L.U (i PUnit.unit) :=
    gen_mem (x := below (z ≫ μ.U.ι)) (w₁ (Set.mem_univ (closedPoint _))).2
  have t₁ := ht i g₀
  rw [w₀] at N
  rw [← r₂, ← s₃] at N
  generalize valF (F := B.X.functionField) (B.X.fromSpecStalk (genericPoint B.X) ≫ q) _
    (M.r a (i PUnit.unit)).val = ρ at r₁ t₁ N
  have t₂ : μ.φ (GlobalTheory.LineNorm.dg Φ (below y₁.1) x.1 x.2 : Φ.Y.Fn) = (t i : B.X.functionField) * (s * ρ) := by
    rw [← s₂, ← t₁]; ring
  have t₃ : UnitAt (below (z ≫ μ.U.ι)) (t i : B.X.functionField) := by
    have := d₃.mul (s₁.mul r₁).inv
    rwa [t₂, mul_inv_cancel_right₀ (s₁.mul r₁).ne_zero] at this
  refine ⟨t₃, ?_⟩
  have pt : spMap ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y₁.1).hom) ≫ stalkPt Φ.Y (below y₁.1) ≫ Φ.π ≫
      genι T = spMap (ioOf (resP v) ε) ≫ (z ≫ y) ≫ T.j := by
    have e₀ : spMap (Scheme.stalkClosedPointTo y₁.1).hom ≫ stalkPt Φ.Y (below y₁.1) = y₁.1 :=
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk _
    rw [← ModelRelProbe.spMap_comp, Category.assoc, reassoc_of% e₀, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model.j, Category.assoc,
      reassoc_of% h₂, reassoc_of% hz]
  rw [pt, ha'] at sy
  rw [d₂, sy, N, ← d₄, t₂, SmallSec.valAt_mul t₃.regAt (s₁.mul r₁).regAt, SmallSec.valAt_mul s₁.regAt r₁.regAt,
    map_mul, map_mul, Real.log_mul (ε.w.ne_zero (SmallSec.valAt_ne_zero t₃))
      (mul_ne_zero (ε.w.ne_zero (SmallSec.valAt_ne_zero s₁)) (ε.w.ne_zero (SmallSec.valAt_ne_zero r₁))),
    Real.log_mul (ε.w.ne_zero (SmallSec.valAt_ne_zero s₁)) (ε.w.ne_zero (SmallSec.valAt_ne_zero r₁)),
    io₂ (TrueGeo.valAt _ s), io₂ (TrueGeo.valAt _ ρ)]
  ring

private theorem succ_mul_succ_sub_one_div_succ {K : Type} [Field K] {c u r r' t t' : K} (hc : c ≠ 0) (ht : t' ≠ 0) (e₁ : u * r = r')
    (e₂ : t * r = c) (e₃ : t' * r' = c) : u = t / t' := by
  rw [eq_div_iff ht]
  refine mul_right_cancel₀ (right_ne_zero_of_mul (e₂ ▸ hc)) ?_
  rw [e₂, ← e₃, ← e₁]
  ring

private theorem main_free (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (z : admitted Y i₀)
    [IsDiscreteValuationRing (z.Z.i.c.V W)] {O : Type} [CommRing O] {β : O →+* i₀.c.F}
    {T : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model (Xo i₀.l) i₀.c β} {b₀ : O →+* i₀.c.V W}
    (hb : (i₀.c.V W).subtype.comp b₀ = β) (hD : Dominates T (Y i₀) b₀) {F : Type} [Field F] [NumberField F]
    {e : F ≃+* i₀.c.F} {Φ : FlagCpt T e} {b : 𝓞 F →+* z.Z.i.c.V W} {v : HeightOneSpectrum (𝓞 F)} (hv : resP v = p)
    (C : (nmodel z.Z).Comp) (μ : Match Φ.Y b ((nmodel z.Z).comp C)) (hL : Link z.Z C Φ μ) {Cx : CxSt F}
    (hm : Mets Φ Cx) (hx : letterOf Dw st = some x) :
    ∃ t : ∀ k : Bool, ((z.line k st x hx).L.lb.pull ((nmodel z.Z).compι C)).ι → ((nmodel z.Z).comp C).X.functionFieldˣ, (∀ (k : Bool) (a : ℕ → Bool) (R : Option ℝ), a p = k → Reads μ v ((z.line k st x hx).L.lb.pull ((nmodel z.Z).compι C)) (t k) (lam (adlOf Φ hm (Finsupp.single (a, R, st) 1)) v)) ∧ ∀ i j (h : genericPoint ((nmodel z.Z).comp C).X ∈ (nmodel z.Z).compι C ⁻¹ᵁ ((nmodel z.Z).gen ⊓ ((z.line false st x hx).L.lb.U i ⊓ (z.line true st x hx).L.lb.U j))), fnOf _ h (((nmodel z.Z).compι C).app _ ((z.genId hp hW hx).u i j).val) = (t false (fun _ => i) : ((nmodel z.Z).comp C).X.functionField) / (t true (fun _ => j) : ((nmodel z.Z).comp C).X.functionField) := by
  obtain ⟨a, τ, mu, y, ψ, f, g, hU, hT, h₁, h₂, h₃, h₄, h₅⟩ := hL
  obtain ⟨c₀, hc⟩ := UpperTheory.exists_unit_tri_and_diag_coeff_mul_eq_of_carries E H Dw _ _ _ O β T F e Φ _ μ.φ _ f g x μ.φ_spec h₅
  have hB := UpperTheory.admissible_flag_valuation E H Dw Xo p W Y i₀ z.Z O β T F e Φ _ b _ μ ((nmodel z.Z).compι C) a τ mu y ψ f g x c₀
    hU hT h₁ h₂ h₃ h₄ hc
  choose t ht₀ ht using fun k => exists_sec (z.line k st x hx) ((nmodel z.Z).compι C) a (hU μ.mem) c₀
  refine ⟨t, fun k a' R ha' => reads_sec hp hW hb hD μ _ a hT h₁ h₂ hx _ c₀ hB (ht₀ k) (ht k) hv hm a' R ha',
    fun i j h => ?_⟩
  have e₁ := z.isGenId_genId hp hW hx ((nmodel z.Z).comp C).X.functionField
    (((nmodel z.Z).comp C).X.fromSpecStalk (genericPoint _) ≫ (nmodel z.Z).compι C) a i j
    (top_le_gen ⟨hU μ.mem, h.2⟩)
  have e₂ := ht false (fun _ => i) h.2.1
  have e₃ := ht true (fun _ => j) h.2.2
  refine ((UpperTheory.generic_stalk_section_unit _ _ ((nmodel z.Z).compι C) _ ((z.genId hp hW hx).u i j).val).1 h).symm.trans ?_
  exact succ_mul_succ_sub_one_div_succ c₀.ne_zero (Units.ne_zero _) e₁ e₂ e₃

end SlopeTestRemainingChoices

theorem UpperTheory.admissible_point_height_compat :
    ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (fl : s.Flag), (∀ k, (fl.C k).Y.dim = Formalism.DegreeFormula.dimFl D.what₂.Tau N) → ∀ (p : ℕ) (hp : p.Prime) (W : ValuationSubring ℂ) (hW : (p : ℂ) ∈ W.nonunits) (z : AdmAt S κ hp hW) [IsDiscreteValuationRing (z.Z.i.c.V W)] (ε : D.what₂.LL →+* z.Z.i.c.F) (b : 𝓞 D.what₂.LL →+* z.Z.i.c.V W), (∀ x, ((ε x : z.Z.i.c.F) : ℂ) = D.what₂.embLL x) → (∀ x : 𝓞 D.what₂.LL, ((b x : z.Z.i.c.V W) : z.Z.i.c.F) = ε (x : D.what₂.LL)) → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), resP v = p → ∀ (C : (nmodel z.Z).Comp) (c : s.Comp) (μ : Match (fl.C c).Y b ((nmodel z.Z).comp C)), Link z.Z C (fl.C c) μ → ∀ (Cx : CxSt D.what₂.LL) (hm : Mets (fl.C c) Cx) (st : ((D.host.E →+* ℂ) × ℕ) ⊕ ℕ) (x : Pad.Letter S.Dw) (hx : letterOf S.Dw st = some x), ∃ t : ∀ k : Bool, ((z.line k st x hx).L.lb.pull ((nmodel z.Z).compι C)).ι → ((nmodel z.Z).comp C).X.functionFieldˣ, (∀ (k : Bool) (a : ℕ → Bool) (R : Option ℝ), a p = k → Reads μ v ((z.line k st x hx).L.lb.pull ((nmodel z.Z).compι C)) (t k) (lam (adlOf (fl.C c) hm (Finsupp.single (a, R, st) 1)) v)) ∧ ∀ i j (h : genericPoint ((nmodel z.Z).comp C).X ∈ (nmodel z.Z).compι C ⁻¹ᵁ ((nmodel z.Z).gen ⊓ ((z.line false st x hx).L.lb.U i ⊓ (z.line true st x hx).L.lb.U j))), fnOf _ h (((nmodel z.Z).compι C).app _ ((z.genId hp hW hx).u i j).val) = (t false (fun _ => i) : ((nmodel z.Z).comp C).X.functionField) / (t true (fun _ => j) : ((nmodel z.Z).comp C).X.functionField) := by
  intro D A N j S κ s fl _ p hp W hW z _ ε b _ _ v hv C c μ hL Cx hm st x hx
  let b₀ : 𝓞 κ.c.F →+* κ.c.V W := (algebraMap (𝓞 κ.c.F) κ.c.F).codRestrict (κ.c.V W) fun x => by
    have hx : IsIntegral ℤ (x : κ.c.F) := x.2
    have h₂ : IsIntegral (κ.c.V W) (x : κ.c.F) := hx.tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h₂
    exact (show ((y : κ.c.V W) : κ.c.F) = algebraMap _ _ x from hy) ▸ y.2
  have hD := dominates_tor s.T (s.glob.2.1 p W hp hW b₀ fun _ => rfl)
  exact main_free hp hW z (b₀ := b₀) (RingHom.ext fun _ => rfl) hD hv C μ hL hm hx
