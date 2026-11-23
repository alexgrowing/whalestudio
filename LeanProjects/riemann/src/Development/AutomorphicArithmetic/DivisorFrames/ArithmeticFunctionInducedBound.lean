import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.VertCmp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonomialEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoverInducedMetricsArith
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalHeightBoundedByPrimeWeights
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.Toroidal
open GlobalTheory.VertCmp
open scoped Classical

namespace UpperTheory.VertGlob

open GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.ArInt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrivFlag GlobalTheory.CoverNorm.Isom GlobalTheory.CompHt GlobalTheory.AllWt

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

private def CReads (V : Mean4O.Cover Y) (L : LB V.X) (s : L.ι → V.X.functionFieldˣ) (f : Y.X → Y.Fn)
    (l : ∀ v : HeightOneSpectrum (𝓞 F), TrueGeo.Ext v → AlgPt Y → ℝ) : Prop :=
  ∀ (v : HeightOneSpectrum (𝓞 F)) (e : TrueGeo.Ext v) (y : AlgPt Y) (z : Sp (AlgebraicClosure F) ⟶ V.G)
    (yt : Sp e.O ⟶ V.X) (i : L.ι), z ≫ V.π = y.1 → spMap e.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ L.U i →
    UnitAt (below z) (V.φ (f (below y.1)) * SmallSec.fnMap V.j (j_gen_specializes V) (s i)) ∧
      l v e y = Real.log (e.w (TrueGeo.valAt z
        (V.φ (f (below y.1)) * SmallSec.fnMap V.j (j_gen_specializes V) (s i))))

private theorem exists_lift (V : Mean4O.Cover Y) (M : HermLB V.p) {f : Y.X → Y.Fn} {a : ∀ σ : F →+* ℂ, Pts Y σ → ℝ}
    {l : ∀ v : HeightOneSpectrum (𝓞 F), TrueGeo.Ext v → AlgPt Y → ℝ} (h : Norms V M f a l) :
    ∃ (s : M.B.ι → V.X.functionFieldˣ) (_ : IsRatSec M.B s), CReads V M.B s f l ∧
      ((∀ x, f x = 1) → (∀ σ y, a σ y = 0) → ∀ σ y, logNorm (M.φ σ) s y = 0) := by
  obtain ⟨r, hr, hu, hc, hf⟩ := h
  haveI := CoverHt.isPreimmersion_j V
  have hη := j_gen_specializes V
  let ρ : V.X.functionField ≃+* V.G.functionField := RingEquiv.ofBijective (SmallSec.fnMap V.j hη)
    ⟨(SmallSec.fnMap V.j hη).injective, SmallSec.fnMap_surjective V.j hη⟩
  have hρ : ∀ (U : V.X.Opens) (hU : genericPoint V.X ∈ U) (hU' : genericPoint V.G ∈ V.j ⁻¹ᵁ U)
      (s : Γ(V.X, U)), ρ (fnOf U hU s) = fnOf (V.j ⁻¹ᵁ U) hU' (V.j.app U s) :=
    fun U hU hU' s => SmallSec.fnMap_fnOf V.j hη hU hU' s
  have hj : V.j (genericPoint V.G) = genericPoint V.X := (hη.antisymm (genericPoint_specializes _)).eq
  have hv : ∀ {K : Type} [Field K] (y : Sp K ⟶ V.G) (g : V.X.functionField),
      TrueGeo.valAt (y ≫ V.j) g = TrueGeo.valAt y (ρ g) :=
    fun y g => ModelFn.valAt_comp V.j hη y g
  have hR := InducedIsom.isRatSec_lift V.j ρ hρ hj M.B hr
  have eρ : ∀ i, ρ ((Units.map ρ.symm.toMonoidHom (r fun _ => i) : V.X.functionFieldˣ) :
      V.X.functionField) = (r fun _ => i : V.G.functionField) := fun i => ρ.apply_symm_apply _
  refine ⟨_, hR, fun v e y z yt i e₁ e₂ hU => ?_, fun hf1 ha0 τ y => ?_⟩
  · have eρ' : SmallSec.fnMap V.j (j_gen_specializes V)
        ((Units.map ρ.symm.toMonoidHom (r fun _ => i) : V.X.functionFieldˣ) :
        V.X.functionField) = (r fun _ => i : V.G.functionField) := eρ i
    rw [eρ']
    have hpt : (z ≫ V.j) (IsLocalRing.closedPoint _) ∈ M.B.U i := by
      rw [← e₂]
      exact hU (Set.mem_univ _)
    have m₁ : below z ∈ (M.B.pull V.j).U (fun _ => i) := Set.mem_iInter.2 fun _ => hpt
    have hw := hu _ _ m₁
    have hb : V.π (below z) = below y.1 := by rw [← e₁]; rfl
    rw [hb] at hw
    exact ⟨hw, hf v e y z yt (fun _ => i) e₁ e₂ hU⟩
  · obtain ⟨σ, rfl, z, hz⟩ := cxPts_from_generic_fibre V τ y
    rw [logNorm]
    have hyj := CxPts.mem_pick (M.φ (σ.comp (algebraMap (𝓞 F) F))).isLB y
    generalize CxPts.pick (M.φ (σ.comp (algebraMap (𝓞 F) F))).isLB y = j at hyj ⊢
    let y₀ : Pts Y σ := ⟨z.1 ≫ V.π, by rw [Category.assoc]; exact z.2⟩
    have hun : under y = V.j (under z) := by
      change y.1 _ = _
      rw [hz]
      rfl
    have m₁ : under z ∈ (M.B.pull V.j).U fun _ => j := Set.mem_iInter.2 fun _ => by
      change V.j (under z) ∈ M.B.U j
      rw [← hun]
      exact CxPts.mem_ptsIn.1 hyj
    have H := hc σ z y₀ y (fun _ => j) rfl hz m₁
    have hq : ratVal ((Units.map ρ.symm.toMonoidHom (r fun _ => j) : V.X.functionFieldˣ) :
        V.X.functionField) y = ratVal (r fun _ => j : V.G.functionField) z := by
      rw [ModelFn.ratVal_eq, ModelFn.ratVal_eq, hz, hv, eρ]
    simp only [hf1, ha0, map_one, one_mul] at H
    rw [hq]
    linarith

private theorem ord_pos (V : Mean4O.Cover Y) [IsLocallyNoetherian V.X] {L : LB V.X} (hL : L.IsLB)
    {s : L.ι → V.X.functionFieldˣ} (hs : IsRatSec L s)
    {lg : ∀ v : HeightOneSpectrum (𝓞 F), TrueGeo.Ext v → AlgPt Y → ℝ} (h : CReads V L s (fun _ => 1) lg)
    (p : ℕ) (hp : p.Prime) (b : ℝ)
    (hlg : ∀ v e y, |lg v e y| ≤ (if resP v = p then b else 0) * (-Real.log (e.w (resP v : AlgebraicClosure F))))
    (z : V.X) (hz : (divOfRatSec hL hs).mult z ≠ 0) : 0 < Scheme.ord (p : V.X.functionField) z := by
  haveI := CoverHt.isPreimmersion_j V
  haveI := VertOrd.charZero_fn V.ar
  have hη := j_gen_specializes V
  obtain ⟨i, hi⟩ := exists_chart hL z
  have hmult := ((presents_divOfRatSec hL hs).isEqn i z hi).mult_eq
  have hg0 : (s i : V.X.functionField) ≠ 0 := Units.ne_zero _
  have hp0 : (p : V.X.functionField) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hstep : ∀ u : V.X.functionField, (u = s i ∨ u = (s i : V.X.functionField)⁻¹) →
      RegAt z (((p ^ ⌈b⌉₊ : ℕ) : V.X.functionField) * u) := by
    intro u hu0
    refine GlobalTheory.Mean4O.Cover.RegCrit.regAt_of_integral_values F Y V (L.U i) _ (fun v e z' yt hz' e₂ hU => ?_) z hi
    let y : AlgPt Y := ⟨z' ≫ V.π, by rw [Category.assoc]; exact hz'⟩
    obtain ⟨hw, H⟩ := h v e y z' yt i rfl e₂ hU
    simp only [map_one, one_mul] at hw H
    have hρu : UnitAt (below z') (SmallSec.fnMap V.j hη u) ∧
        |Real.log (e.w (TrueGeo.valAt z' (SmallSec.fnMap V.j hη u)))| = |lg v e y| := by
      rcases hu0 with rfl | rfl
      · exact ⟨hw, by rw [H]⟩
      · refine ⟨by rw [map_inv₀]; exact hw.inv, ?_⟩
        rw [map_inv₀, LineNorm.Neg.valAt_inv hw, map_inv₀, Real.log_inv, abs_neg, H]
    rw [ModelFn.valAt_comp V.j hη, map_mul, map_natCast,
      SmallSec.valAt_mul (VertOrd.regAt_natCast _ _) hρu.1.regAt, VertOrd.valAt_natCast, map_mul, Nat.cast_pow,
      AbsoluteValue.map_pow]
    have hW : 0 < e.w (p : AlgebraicClosure F) ∧ e.w (p : AlgebraicClosure F) ≤ 1 := by
      have e₁ : e.w (p : AlgebraicClosure F) = NumberField.HeightOneSpectrum.adicAbv F v (p : F) := by
        rw [← e.w_alg, map_natCast (algebraMap F (AlgebraicClosure F))]
      have hl' : (p : F) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
      rw [e₁]
      exact ⟨AbsoluteValue.pos _ hl', NumberField.HeightOneSpectrum.adicAbv_natCast_le_one F v p⟩
    have ht : 0 < e.w (TrueGeo.valAt z' (SmallSec.fnMap V.j hη u)) := e.w.pos (Res.valAt_ne_zero hρu.1)
    have hsum := VertOrd.sum_log_add_le {p} (fun _ => b) (fun _ => ⌈b⌉₊) 1 (fun l => e.w (l : AlgebraicClosure F))
      (by simpa using hW) (resP v) (lg v e y) (by simpa using Nat.le_ceil b)
      (by simpa only [Finset.mem_singleton] using hlg v e y)
    rw [Finset.sum_singleton, Nat.cast_one, one_mul] at hsum
    have hlog : Real.log (e.w (p : AlgebraicClosure F) ^ ⌈b⌉₊ *
        e.w (TrueGeo.valAt z' (SmallSec.fnMap V.j hη u))) ≤ 0 := by
      rw [Real.log_mul (pow_pos hW.1 _).ne' ht.ne', Real.log_pow]
      have h5 := le_abs_self (Real.log (e.w (TrueGeo.valAt z' (SmallSec.fnMap V.j hη u))))
      rw [hρu.2] at h5
      linarith
    by_contra hgt
    exact absurd hlog (not_le.2 (Real.log_pos (not_le.1 hgt)))
  have hN0 : ((p ^ ⌈b⌉₊ : ℕ) : V.X.functionField) ≠ 0 := by rw [Nat.cast_pow]; exact pow_ne_zero _ hp0
  have h₁ := VertOrd.ord_nonneg_of_regAt (hstep _ (Or.inl rfl)) (mul_ne_zero hN0 hg0)
  have h₂ := VertOrd.ord_nonneg_of_regAt (hstep _ (Or.inr rfl)) (mul_ne_zero hN0 (inv_ne_zero hg0))
  rw [Scheme.ord_mul hN0 hg0, Nat.cast_pow, VertOrd.ord_pow' hp0] at h₁
  rw [Scheme.ord_mul hN0 (inv_ne_zero hg0), Nat.cast_pow, VertOrd.ord_pow' hp0, VertOrd.ord_inv' hg0] at h₂
  refine lt_of_le_of_ne (VertOrd.ord_nonneg_of_regAt (VertOrd.regAt_natCast z p) hp0) fun e => hz ?_
  rw [← e, mul_zero, zero_add] at h₁ h₂
  rw [hmult]
  omega

private theorem mem_asIdeal {R : Type} [CommRing R] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (q : X ⟶ Sp R) (p : ℕ) (z : X) (h : 0 < Scheme.ord (p : X.functionField) z) : (p : R) ∈ (q z).asIdeal := by
  by_contra hc
  have h₁ : q z ∈ (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv (p : R)) := by
    rw [basicOpen_eq_of_affine]
    exact hc
  have h₂ : z ∈ X.basicOpen (p : Γ(X, ⊤)) := by
    have h₃ : z ∈ q ⁻¹ᵁ (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv (p : R)) := h₁
    rwa [Scheme.preimage_basicOpen_top, map_natCast, map_natCast] at h₃
  have h₄ := (unitAt_fnOf_iff (U := ⊤) (TopologicalSpace.Opens.mem_top z) (TopologicalSpace.Opens.mem_top _) _).2 h₂
  rw [map_natCast] at h₄
  exact h.ne' h₄.ord_eq_zero

private theorem gReads (Q : TrueGeo.Model Y) [IsIntegral Q.X] (hQ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Q.X)
    {L : LB Q.X} {s : L.ι → Q.X.functionFieldˣ} (hs : IsRatSec L s) {f : Y.X → Y.Fn}
    {l : ∀ v : HeightOneSpectrum (𝓞 F), TrueGeo.Ext v → AlgPt Y → ℝ}
    (h : CReads (Cover.ofModel Q hQ) L s f l) (W : Y.X.Opens) (hW : genericPoint Y.X ∈ W)
    (hf : ∀ x ∈ W, UnitAt x (f x)) (v : HeightOneSpectrum (𝓞 F)) (l' : TrueGeo.Ext v → AlgPt Y → ℝ)
    (hl : ∀ e y, below y.1 ∈ W → l' e y = l v e y - Real.log (e.w (TrueGeo.valAt y.1 (f (below y.1))))) :
    GReads Q v L s l' := by
  refine ⟨hs, W, hW, fun e y yt i hy e₂ hU => ?_⟩
  haveI := SmallSec.isPreimmersion_j Q
  have hη : Q.j (genericPoint Y.X) ⤳ genericPoint Q.X := j_gen_specializes (Cover.ofModel Q hQ)
  obtain ⟨hw, H⟩ := h v e y y.1 yt i (Category.comp_id _) e₂ hU
  change UnitAt (below y.1) (f (below y.1) * SmallSec.fnMap Q.j hη (s i)) at hw
  change _ = Real.log (e.w (TrueGeo.valAt y.1 (f (below y.1) * SmallSec.fnMap Q.j hη (s i)))) at H
  have hfy := hf _ hy
  have hu : UnitAt (below y.1) (SmallSec.fnMap Q.j hη (s i)) := by
    have := hfy.inv.mul hw
    rwa [inv_mul_cancel_left₀ hfy.ne_zero] at this
  refine ⟨?_, ?_⟩
  · rw [unitAt_iff (Units.ne_zero _)]
    refine ⟨(SmallSec.regAt_fnMap_iff Q.j hη).1 hu.regAt, (SmallSec.regAt_fnMap_iff Q.j hη).1 ?_⟩
    rw [map_inv₀]
    exact hu.inv.regAt
  · rw [hl e y hy, H, ModelFn.valAt_comp Q.j hη, SmallSec.valAt_mul hfy.regAt hu.regAt, map_mul,
      Real.log_mul (e.w.pos (Res.valAt_ne_zero hfy)).ne' (e.w.pos (Res.valAt_ne_zero hu)).ne']
    ring

end UpperTheory.VertGlob

open UpperTheory.VertGlob GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.ArInt GlobalTheory.TrivFlag MvPolynomial in
theorem UpperTheory.arithmetic_function_induced_bound :
    GlobalTheory.CovTop.Hypotheses2 → ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M : TrueGeo.Model Y) (ι : Type) [Fintype ι] (A : ι → Adl (cxSt F) Y) (L : ι → HermLB M.p) (m : ℕ+) (Ψ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ), (∀ i, (A i).Induced M (L i) m 0) → (haveI := M.ar.isIntegral; GlobalTheory.ArInt.IsArFun L Y.dim Ψ) → ∀ (p : ℕ) [Fact p.Prime] (i₀ i₁ : ι), A i₁ = { A i₀ with lg := (A i₁).lg } → ∀ (c : ℝ), 0 ≤ c → (∀ v e y, |(A i₀).lg v e y - (A i₁).lg v e y| ≤ (if resP v = p then c else 0) * (-Real.log (e.w (resP v : AlgebraicClosure F)))) → ∀ d : ℕ, Y.dim = d → ∃ (Q : TrueGeo.Model Y) (_ : IsIntegral Q.X) (_ : IsLocallyNoetherian Q.X) (N : ι → LB Q.X) (s : ∀ k, (N k).ι → Q.X.functionFieldˣ) (M₀ : LB Q.X) (hM₀ : M₀.IsLB) (r : M₀.ι → Q.X.functionFieldˣ) (hr : IsRatSec M₀ r), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Q.X ∧ (∀ k, (N k).IsLB) ∧ (∀ v k, GReads Q v (N k) (s k) (fun e y => ((m : ℕ) : ℝ) * lam (A k) v e y)) ∧ (∀ v, GReads Q v M₀ r (fun e y => ((m : ℕ) : ℝ) * (lam (A i₀) v e y - lam (A i₁) v e y))) ∧ (∀ z, (divOfRatSec hM₀ hr).mult z ≠ 0 → (p : 𝓞 F) ∈ (Q.p z).asIdeal) ∧ ∀ ν : Fin d → ι, Ψ ((MvPolynomial.X i₀ - MvPolynomial.X i₁) * ∏ j, MvPolynomial.X (ν j)) = Real.log p * ∑ᶠ z : Q.X, (((divOfRatSec hM₀ hr).mult z * pdeg p (fun j => N (ν j)) z : ℤ) : ℝ) := by
  intro hP F _ _ Y M ι _ A L m Ψ hI hΨ p hp i₀ i₁ hA c _ hlg d hd
  subst hd
  have hC := hP.p4
  haveI := M.ar.isIntegral
  obtain ⟨Q, ρ, -, hQ, hρ, -, hj, -, -, -⟩ := GlobalTheory.ModelDom.exists_normal_dominating F Y M M
  haveI iQ : IsIntegral Q.X := Q.ar.isIntegral
  haveI nQ : IsLocallyNoetherian Q.X := Q.ar.isLocallyNoetherian
  haveI : IsNoetherian Q.X := Q.ar.isNoetherian
  haveI : IsLocallyNoetherian (Cover.ofModel Q hQ).X := nQ
  obtain ⟨eρ, dρ⟩ := GlobalTheory.CoverModelDeg.map_genericPoint_and_deg F Y (Cover.ofModel Q hQ) M ρ hρ
    (by simpa [Cover.ofModel] using hj)
  rw [Cover.deg_ofModel] at dρ
  have d₁ : ρ.residueDegree (genericPoint Q.X) = 1 := dρ
  let L' : ι → HermLB Q.p := fun i => (L i).pull ρ hρ
  have hΦ : IsArFun L' Y.dim Ψ := by
    have h₁ := (hC.arProj (𝓞 F) M.X Q.X M.p Q.p Y.dim M.ar Q.ar ρ hρ eρ (d₁ ▸ one_ne_zero)).2 ι L Ψ hΨ
    rwa [d₁, Nat.cast_one, one_smul] at h₁
  have hL' (i : ι) := norms_of_induces
    (Cover.induces_ofModel hQ (GlobalTheory.T.induced_metric_pullback F _ Y (A i) M Q ρ hρ hj (L i) m 0 (hI i)))
  choose s hs hR _ using fun i => exists_lift (Cover.ofModel Q hQ) (L' i) (hL' i)
  obtain ⟨r, hr, hRr, h1⟩ := exists_lift (Cover.ofModel Q hQ) _ (norms_div hA (hL' i₀) (hL' i₁))
  have hpos (z : Q.X) (hz : (divOfRatSec ((L' i₀).tens (L' i₁).dual).isLB hr).mult z ≠ 0) :
      0 < Scheme.ord (p : Q.X.functionField) z :=
    ord_pos (Cover.ofModel Q hQ) _ hr hRr p hp.out ((m : ℕ) * c) (fun v ε y => by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      refine (mul_le_mul_of_nonneg_left (hlg v ε y) (Nat.cast_nonneg _)).trans_eq ?_
      split_ifs <;> ring) z hz
  refine ⟨Q, iQ, nQ, fun k => (L' k).B, s, ((L' i₀).tens (L' i₁).dual).B, ((L' i₀).tens (L' i₁).dual).isLB, r, hr, hQ,
    fun k => (L' k).isLB, fun v k => ?_, fun v => ?_, fun z hz => mem_asIdeal Q.p p z (hpos z hz), fun ν => ?_⟩
  · obtain ⟨W, hW, hE⟩ := ((A k).D.isEqn_genericPoint 1).exists_nhds
    have hu (x : Y.X) (hx : x ∈ W) : UnitAt x (eqn (A k).D x : Y.Fn) := by
      simpa using (hE x hx).iff_unitAt.1 (Base.isEqn_eqn (A k).D x)
    refine gReads Q hQ (hs k) (hR k) W hW (fun x hx => ?_) v _ fun e y hy => ?_
    · rw [genAt, Units.val_inv_eq_inv_val]
      induction (m : ℕ) with
      | zero => simpa using unitAt_one x
      | succ n ih => rw [pow_succ]; exact ih.mul (hu x hx).inv
    · rw [genAt, Units.val_inv_eq_inv_val, Res.valAt_pow (hu _ hy).inv.regAt, LineNorm.Neg.valAt_inv (hu _ hy),
        AbsoluteValue.map_pow, map_inv₀, Real.log_pow, Real.log_inv, VertCmp.lam]
      ring
  · refine gReads Q hQ hr hRr ⊤ trivial (fun x _ => unitAt_one x) v _ fun e y _ => ?_
    have hD : (A i₁).D = (A i₀).D := by rw [hA]
    have h0 := VertOrd.valAt_natCast y.1 1
    rw [Nat.cast_one, Nat.cast_one] at h0
    rw [h0, map_one, Real.log_one, VertCmp.lam, VertCmp.lam, hD]
    ring
  · obtain ⟨num, hn, -⟩ := GlobalTheory.T.arith_intersection_form_exists hC _ _ Q.p _ Q.ar
    obtain ⟨rt, rd, -, -⟩ := GlobalTheory.T.arith_class_form_properties hC _ _ Q.p _ Q.ar num hn
    have hv := GlobalTheory.T.height_of_rational_section_via_divisor hP _ Q.X Q.p _ Q.ar num hn ((L' i₀).tens (L' i₁).dual) r hr
      (fun σ y _ => h1 (fun _ => rfl) (fun _ _ => rfl) σ y) (fun j => L' (ν j)) (fun _ => p)
      (fun z => (pdeg p (fun j => (L' (ν j)).B) z : ℝ)) fun z hz => by
        obtain ⟨Z, i, hi, hZ, hAl, e₁, e₂⟩ := GlobalTheory.T.exists_integral_subscheme_prime_fibre _ Q.X Q.p _ Q.ar p z (hpos z hz)
        have hex : ∃ a, IsDeg p (fun j => (L' (ν j)).B) z a := ⟨_, Z, i, hi, hZ, hAl, e₁, e₂, rfl⟩
        obtain ⟨Z', i', hi', hZ', hAl', e₁', e₂', e₃⟩ := hex.choose_spec
        exact ⟨hp, Z', i', hi', hZ', hAl', e₁', e₂', by rw [pdeg, dif_pos hex, e₃]⟩
    have := hn ι L' Ψ hΦ (Fin.cons (Pi.single i₀ 1 - Pi.single i₁ 1) fun j => Pi.single (ν j) 1)
    have e₂ : lin (Pi.single i₀ 1 - Pi.single i₁ 1 : ι → ℝ) = X i₀ - X i₁ := by
      rw [← TrivFlag.lin_single, ← TrivFlag.lin_single]
      simp only [lin, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]
    rw [Fin.prod_univ_succ, Fin.cons_zero, e₂] at this
    simp only [Fin.cons_succ, TrivFlag.lin_single] at this
    rw [this, mul_finsum]
    refine Eq.trans ?_ (hv.trans (finsum_congr fun z => ?_))
    · refine map_congr_rad num fun j => Fin.cases ?_ (fun j => ?_) j
      · have h₁ := neg_mem (add_mem (rt (L' i₀) (L' i₁).dual) (rd (L' i₁)))
        convert h₁ using 1
        simp only [Fin.cons_zero, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, Pi.single_apply, ite_smul, one_smul,
          zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        abel
      · simp [Pi.single_apply]
    · rw [Int.cast_mul, mul_comm]
