import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.CurveComp
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.GenFrExAndGenFromTest
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EqualVolumeMeanCorrection

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHt

open MvPolynomial NumberField IsDedekindDomain Module Filter GlobalTheory.ChowHt GlobalTheory.AllWt
open scoped ENNReal

section Generic

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]

theorem frameNorm_conj {N : ℕ} {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.det ≠ 0) (x : Fin N → ℂ) :
    frameNorm (A.map (starRingEnd ℂ)) (fun j => starRingEnd ℂ (x j)) = frameNorm A x := by
  have h : (A.map (starRingEnd ℂ))⁻¹ = A⁻¹.map (starRingEnd ℂ) := Matrix.inv_eq_left_inv (by
    rw [← Matrix.map_mul, A.nonsing_inv_mul hA.isUnit, Matrix.map_one _ (map_zero _) (map_one _)])
  rw [frameNorm, frameNorm, h]
  refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
  rw [← Complex.norm_conj (A⁻¹.mulVec x i), RingHom.map_mulVec]
  rfl

theorem exists_isFrame [IsScalarTower (𝓞 K) K V] (hK : ∀ σ : K →+* ℂ, (starRingEnd ℂ).comp σ ≠ σ)
    {Nm : (K →+* ℂ) → V → ℝ} (hc : ∀ σ x, Nm ((starRingEnd ℂ).comp σ) x = Nm σ x) (hG : HasGram Nm)
    {L : Submodule (𝓞 K) V} (hL : L.FG) (hs : Submodule.span K (L : Set V) = ⊤) :
    ∃ (N n : ℕ) (b : Basis (Fin N) K V) (w : Matrix (Fin N) (Fin n) K) (A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ),
      IsFrame Nm L b w A := by
  classical
  obtain ⟨N, ⟨b, X⟩, hX⟩ := hG
  obtain ⟨n, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hL
  have hd : ∀ v, (X v).det ≠ 0 := fun v => (hX v).1.ne_zero
  have hdc : ∀ v, ((X v).map (starRingEnd ℂ)).det ≠ 0 := fun v => by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact (map_ne_zero _).2 (hd v)
  have hmk : ∀ σ : K →+* ℂ, InfinitePlace.mk ((starRingEnd ℂ).comp σ) = InfinitePlace.mk σ :=
    InfinitePlace.mk_conjugate_eq
  have hor : ∀ σ : K →+* ℂ, (InfinitePlace.mk σ).embedding ≠ σ →
      (InfinitePlace.mk σ).embedding = (starRingEnd ℂ).comp σ := fun σ h =>
    (InfinitePlace.embedding_mk_eq σ).resolve_left h
  have hn : ∀ (v : InfinitePlace K) x, frameNorm (X v) (fun j => v.embedding (b.repr x j)) = Nm v.embedding x :=
    fun v x => (hX v).2 x
  refine ⟨N, n, b, Matrix.of fun j k => b.repr (g k) j, fun σ => if (InfinitePlace.mk σ).embedding = σ then
    X (InfinitePlace.mk σ) else (X (InfinitePlace.mk σ)).map (starRingEnd ℂ), ?_, ?_, fun σ => ?_, fun σ x => ?_,
    fun σ x => ?_⟩
  · simp only [Matrix.of_apply, Basis.sum_repr]; exact hg
  · have h1 : Submodule.span K (Set.range g) = ⊤ := by rw [← hs, ← hg, Submodule.span_span_of_tower]
    have h2 := congrArg (Submodule.map b.equivFun.toLinearMap) h1
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, LinearEquiv.range] at h2
    exact h2
  · split_ifs
    exacts [hd _, hdc _]
  · simp only [hmk]
    by_cases h : (InfinitePlace.mk σ).embedding = σ
    · rw [if_pos h, if_neg fun h' => hK σ (h'.symm.trans h), frameNorm_conj (hd _)]
    · rw [if_neg h, if_pos (hor σ h), ← frameNorm_conj (hd _)]
      simp only [Complex.conj_conj]
  · by_cases h : (InfinitePlace.mk σ).embedding = σ
    · rw [if_pos h]
      have := hn (InfinitePlace.mk σ) x
      rwa [h] at this
    · have := hn (InfinitePlace.mk σ) x
      rw [hor σ h, hc, ← frameNorm_conj (hd _)] at this
      rw [if_neg h, ← this]
      simp only [RingHom.comp_apply, Complex.conj_conj]

structure IsShortGen {κ : Type} (Nm : κ → V → ℝ) (L : Submodule (𝓞 K) V) {n : ℕ} (w : Fin n → V) (abelian₂ : ℝ) : Prop where

  gen : ∀ x, x ∈ L ↔ x ∈ Submodule.span ℤ (Set.range w)

  le : ∀ i k, Nm k (w i) ≤ abelian₂

  one_le : 1 ≤ abelian₂

theorem exists_isShortGen {κ : Type} [Finite κ] (Nm : κ → V → ℝ) {L : Submodule (𝓞 K) V} (hL : L.FG) :
    ∃ (n : ℕ) (w : Fin n → V) (abelian₂ : ℝ), IsShortGen Nm L w abelian₂ := by
  obtain ⟨n, w, hw⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (hL.restrictScalars (R := ℤ))
  obtain ⟨B, hB⟩ := (Set.finite_range fun p : Fin n × κ => Nm p.2 (w p.1)).bddAbove
  exact ⟨n, w, max B 1, fun x => by rw [hw]; rfl, fun i k => (hB ⟨(i, k), rfl⟩).trans (le_max_left _ _),
    le_max_right _ _⟩

omit [NumberField K] [Module K V] in

theorem IsShortGen.log_le_cStar {κ : Type} {Nm : κ → V → ℝ} {L : Submodule (𝓞 K) V} {n : ℕ} {w : Fin n → V} {abelian₂ : ℝ}
    (h : IsShortGen Nm L w abelian₂) (hL : L ≠ ⊥) : 0 ≤ Real.log abelian₂ ∧ Real.log abelian₂ ≤ cStar n abelian₂ := by
  refine CompHt.log_le_cStar (Nat.pos_of_ne_zero ?_) h.one_le
  rintro rfl
  exact hL ((Submodule.eq_bot_iff _).2 fun x hx => by simpa using (h.gen x).1 hx)

example : ∃ (n : ℕ) (w : Fin n → Fin 2 → ℚ) (abelian₂ : ℝ), IsShortGen (stdNorm 2) (stdLat 2) w abelian₂ :=
  exists_isShortGen _ (Submodule.fg_span (Set.finite_range _))

end Generic

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

instance fintypePsi : Fintype (Psi H) := Fintype.ofFinite _

def dimFlag (Dw : Datum H) : ℕ := Formalism.DegreeFormula.dimFl (Psi H) (Dw.p + Dw.q)

def hodgeWt (Dw : Datum H) : Weight Dw := barWt (Psi H) (Dw.p + Dw.q) Dw.p

def uPrime (Dw : Datum H) (u : Weight Dw) : Weight Dw := u - (3 * ((Dw.p + Dw.q : ℕ) : ℤ)) • hodgeWt Dw

theorem uPrime_apply (u : Weight Dw) (τ : Psi H) (i : Fin (Dw.p + Dw.q)) :
    uPrime Dw u τ i = if (i : ℕ) < Dw.p then u τ i else u τ i + 3 * ((Dw.p + Dw.q : ℕ) : ℤ) := by
  simp only [uPrime, hodgeWt, barWt, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

def rhoB (Dw : Datum H) (u : Weight Dw) : ℝ := rhoOf (uPrime Dw u) u

theorem nsmul_wtOf (t : ℕ) (la : Weight Dw) (m : ℤ) : t • wtOf Dw la m = wtOf Dw (t • la) (t • m) := by
  induction t with
  | zero => simp only [zero_smul, wtOf_zero]
  | succ t ih => rw [succ_nsmul, succ_nsmul, succ_nsmul, ih, wtOf_add]

def genVal (Z : Comp Xo c) : Rul Xo c →ₐ[c.F] Om Z :=
  evCAlg (Reg.genFrEx_and_genFromTest E H Dw l Xo c).1 ((Reg.genFrEx_and_genFromTest E H Dw l Xo c).2 _) Z

theorem genVal_apply (h : GenFrEx Xo c) (Z : Comp Xo c) (f : Rul Xo c) : genVal Z f = evC h Z f := rfl

variable (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) {D : D7} (V : (c.F →+* ℂ) → HSp D)
  (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r)

def genPoint (Z : Comp Xo c) (C : Submodule c.F (Rul Xo c)) : C →ₗ[c.F] Om Z := (genVal Z).toLinearMap ∘ₗ C.subtype

theorem mem_imageIdeal_genPoint (Z : Comp Xo c) {C : Submodule c.F (Rul Xo c)} {N : ℕ} (b : Basis (Fin N) c.F C) {d : ℕ}
    {g : MvPolynomial (Fin N) c.F} (hg : g.IsHomogeneous d) :
    g ∈ imageIdeal (genPoint Z C) b ↔ genVal Z (aeval (fun j => (b j : Rul Xo c)) g) = 0 := by
  rw [imageIdeal, mem_coneIdeal_of_isHomogeneous _ hg, ← AlgHom.comp_apply, comp_aeval]
  rfl

def compIdeal (Z : Comp Xo c) (G : WTZ E) {N : ℕ} (b : Basis (Fin N) c.F (cuspOn U Z G)) :
    Ideal (MvPolynomial (Fin N) c.F) := imageIdeal (genPoint Z (cuspOn U Z G)) b

theorem isPrime_compIdeal (Z : Comp Xo c) (G : WTZ E) {N : ℕ} (b : Basis (Fin N) c.F (cuspOn U Z G)) :
    (compIdeal U Z G b).IsPrime := isPrime_coneIdeal _

attribute [local instance] MvPolynomial.gradedAlgebra in

theorem isHomogeneous_compIdeal (Z : Comp Xo c) (G : WTZ E) {N : ℕ} (b : Basis (Fin N) c.F (cuspOn U Z G)) :
    (compIdeal U Z G b).IsHomogeneous (homogeneousSubmodule (Fin N) c.F) := isHomogeneous_coneIdeal _

def compDeg (Z : Comp Xo c) (G : WTZ E) : ℕ := imageDeg (genPoint Z (cuspOn U Z G)) (dimFlag Dw)

theorem compDeg_eq {Z : Comp Xo c} {G : WTZ E} {N δ : ℕ} {b : Basis (Fin N) c.F (cuspOn U Z G)}
    {f : MvPolynomial (Fin (dimFlag Dw + 1) × Fin N) c.F} (hf : IsChowFormInt (compIdeal U Z G b) (dimFlag Dw) δ f) :
    compDeg U Z G = δ := IsImageDeg.imageDeg_eq ⟨N, b, f, hf⟩

def IsCompHeight (Z : Comp Xo c) (G : WTZ E) (h : ℝ) : Prop :=
  IsImageHeight (normOn U x V dict Z G) (latOn U Z G) (genPoint Z (cuspOn U Z G)) (dimFlag Dw) h

def compHeight (Z : Comp Xo c) (G : WTZ E) : ℝ :=
  imageHeight (normOn U x V dict Z G) (latOn U Z G) (genPoint Z (cuspOn U Z G)) (dimFlag Dw)

def CompPresents (Z : Comp Xo c) (G : WTZ E) (T : Adelic.HermSys c.F) : Prop :=
  T.D = dimFlag Dw ∧ Presents T (normOn U x V dict Z G) (latOn U Z G) (genPoint Z (cuspOn U Z G))

theorem not_goodEmb_conj {σ : c.F →+* ℂ} (h : GoodEmb c σ) : ¬ GoodEmb c ((starRingEnd ℂ).comp σ) := fun h' => by
  have h1 : starRingEnd ℂ H.rt0 = H.rt0 := (congrArg (starRingEnd ℂ) h).symm.trans h'
  have him : H.rt0.im = 0 := Complex.conj_eq_iff_im.1 h1
  have hre := congrArg Complex.re H.sqrt_neg_disc_sq
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  simp only [sq, Complex.mul_re, him, Complex.neg_re, Complex.natCast_re] at hre
  nlinarith [mul_self_nonneg H.rt0.re]

theorem goodOf_conj (σ : c.F →+* ℂ) : goodOf c ((starRingEnd ℂ).comp σ) = goodOf c σ := by
  have e : (starRingEnd ℂ).comp ((starRingEnd ℂ).comp σ) = σ := RingHom.ext fun a => Complex.conj_conj _
  by_cases h : GoodEmb c σ
  · rw [goodOf, goodOf, if_pos h, if_neg (not_goodEmb_conj h), e]
  · have h' := goodEmb_goodOf c σ
    rw [goodOf, if_neg h] at h'
    rw [goodOf, goodOf, if_neg h, if_pos h']

theorem conj_comp_ne (σ : c.F →+* ℂ) : (starRingEnd ℂ).comp σ ≠ σ := fun e => by
  have h := goodEmb_goodOf c σ
  have e' : goodOf c σ = σ := by rw [goodOf, e, ite_self]
  rw [e'] at h
  exact not_goodEmb_conj h (e.symm ▸ h)

theorem petOn_conj (Z : Comp Xo c) (G : WTZ E) (σ : c.F →+* ℂ) (f : Rul Xo c) :
    petOn U x V dict Z G ((starRingEnd ℂ).comp σ) f = petOn U x V dict Z G σ f :=
  congrArg (fun s => petAt (U s) x (V s) (dict s) (muOn (U s) (V s) (dict s) Z) G f) (goodOf_conj σ)

variable {U x V dict} in

theorem isCompHeight_compHeight {Z : Comp Xo c} {G : WTZ E} (h : GoodOn U x V dict Z G) (hd : 0 < compDeg U Z G) :
    IsCompHeight U x V dict Z G (compHeight U x V dict Z G) :=
  isImageHeight_imageHeight (exists_isImageHeight_iff.2
    ⟨exists_isFrame (Nm := normOn U x V dict Z G) conj_comp_ne (fun σ f => petOn_conj U x V dict Z G σ f) h.1 h.2.1 h.2.2, hd⟩)

variable {U x V dict} in

theorem CompPresents.isCompHeight {Z : Comp Xo c} {G : WTZ E} {T : Adelic.HermSys c.F}
    (hT : CompPresents U x V dict Z G T) {h : ℝ} (hh : T.IsHeight h) : IsCompHeight U x V dict Z G h := by
  rw [IsCompHeight, ← hT.1]
  exact hT.2.isImageHeight hh

def CompShortGen (G : WTZ E) {n : ℕ} (w : Fin n → cuspW Xo c U G) (abelian₂ : ℝ) : Prop :=
  IsShortGen (fun (k : (c.F →+* ℂ) × Comp Xo c) (f : cuspW Xo c U G) => petOn U x V dict k.2 G k.1 f) (latW U G) w abelian₂

def depth_vw (G : WTZ E) (v : Rul Xo c → EReal) : EReal := ⨅ w ∈ latW U G, v w

theorem depth_vw_nonneg (G : WTZ E) {la : HeightOneSpectrum (𝓞 c.F)} {v : Rul Xo c → EReal}
    (hv : v ∈ valSet Xo c (algCls Xo c) la) : 0 ≤ depth_vw U G v :=
  le_iInf₂ fun _ hw => hw la v hv

def valL_vw (G : WTZ E) (τ : ℕ) (v : Rul Xo c → EReal) (t : Rul Xo c) : EReal := v t - (τ : EReal) * depth_vw U G v

def normL_sq (Z : Comp Xo c) (G : WTZ E) (τ : ℕ) (σ : c.F →+* ℂ) (t : Rul Xo c) (y : FPt (U σ).X) : ℝ≥0∞ :=
  ENNReal.ofReal (homN (U σ) x (τ • G) t ⟨y.1, y.2.1⟩) ^ 2 / bergOn (U σ) (V σ) (dict σ) Z G y ^ τ

def growthOn (Z : Comp Xo c) (G : WTZ E) : ℝ≥0∞ :=
  growth (dimFlag Dw) fun τ => Cardinal.toENat (Module.rank c.F (cuspOn U Z (τ • G)))

def vZero (Z : Comp Xo c) : ℝ :=
  (growthOn U Z (wtOf Dw (stdWt (Psi H) (Dw.p + Dw.q)) 0)).toReal / (vdm (stdWt (Psi H) (Dw.p + Dw.q)) : ℤ)

theorem vZero_nonneg (Z : Comp Xo c) : 0 ≤ vZero U Z :=
  div_nonneg ENNReal.toReal_nonneg (Int.cast_pos.2 (vdm_pos strictAnti_stdWt)).le

def topDeg (Z : Comp Xo c) (la : Weight Dw) : ℝ := vZero U Z * (vdm la : ℤ)

theorem topDeg_stdWt (Z : Comp Xo c) : topDeg U Z (stdWt (Psi H) (Dw.p + Dw.q)) =
    (growthOn U Z (wtOf Dw (stdWt (Psi H) (Dw.p + Dw.q)) 0)).toReal :=
  div_mul_cancel₀ _ (Int.cast_pos.2 (vdm_pos strictAnti_stdWt)).ne'

def delPrime (Z : Comp Xo c) (u : Weight Dw) : ℝ := topDeg U Z (uPrime Dw u)

theorem delPrime_eq (Z : Comp Xo c) {u : Weight Dw} (h : vdm u ≠ 0) :
    delPrime U Z u = (1 - rhoB Dw u) * topDeg U Z u := by
  rw [delPrime, topDeg, topDeg, ← one_sub_rhoOf_mul (u' := uPrime Dw u) h, rhoB]
  ring

variable (Xo c) in

def ValFam : Type :=
  {Vs : HeightOneSpectrum (𝓞 c.F) → Set (Rul Xo c → EReal) // ∀ la, ∀ v ∈ Vs la, IsVal la v}

variable (Xo c) in

def recVals : ValFam Xo c := ⟨valSet Xo c (algCls Xo c), isVal_valSet⟩

open Classical in

def ValFam.patch (S : Set ℕ) (A B : ValFam Xo c) : ValFam Xo c :=
  ⟨fun la => if ∃ p ∈ S, ((p : ℕ) : 𝓞 c.F) ∈ la.asIdeal then A.1 la else B.1 la, fun la v hv => by
    beta_reduce at hv
    split_ifs at hv
    exacts [A.2 la v hv, B.2 la v hv]⟩

example (A B : ValFam Xo c) : ValFam.patch ∅ A B = B := Subtype.ext (funext fun la => by simp [ValFam.patch])

def latVal (Vs : ValFam Xo c) (Z : Comp Xo c) (G : WTZ E) : Submodule (𝓞 c.F) (cuspOn U Z G) :=
  latOf (cuspOn U Z G) Vs.1 Vs.2

theorem latVal_recVals (Z : Comp Xo c) (G : WTZ E) : latVal U (recVals Xo c) Z G = latOn U Z G := rfl

def smallOn (Vs : ValFam Xo c) (Z : Comp Xo c) (G : WTZ E) (R : ℝ) : Set (cuspOn U Z G) :=
  {f | f ∈ latVal U Vs Z G ∧ ∀ σ, GoodEmb c σ → ∀ z ∈ framesOn (U σ) Z, homN (U σ) x G f z ≤ R}

theorem smallOn_mono (Vs : ValFam Xo c) (Z : Comp Xo c) (G : WTZ E) : Monotone (smallOn U x Vs Z G) :=
  fun _ _ h _ hf => ⟨hf.1, fun σ hσ z hz => (hf.2 σ hσ z hz).trans h⟩

def compVol (a : ℕ) (Vs : ValFam Xo c) (Z : Comp Xo c) (G : WTZ E) (t : ℝ) : ℝ≥0∞ :=
  countVol (dimFlag Dw) (finrank ℚ c.F) a fun τ => (smallOn U x Vs Z (τ • G) (Real.exp (τ * t))).encard

theorem compVol_mono (a : ℕ) (Vs : ValFam Xo c) (Z : Comp Xo c) (G : WTZ E) : Monotone (compVol U x a Vs Z G) :=
  fun _ _ h => countVol_mono _ _ _ fun τ => Set.encard_le_encard (smallOn_mono U x Vs Z _
    (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left h τ.cast_nonneg)))

def compVolSlope (a : ℕ) (Vs : ValFam Xo c) (Z : Comp Xo c) (la : Weight Dw) : EReal :=
  volSlope (topDeg U Z la) (compVol U x a Vs Z (wtOf Dw la 0))

theorem le_compVolSlope_iff (a : ℕ) (Vs : ValFam Xo c) {Z : Comp Xo c} {la : Weight Dw} (h : 0 < topDeg U Z la) (s : ℝ) :
    (s : EReal) ≤ compVolSlope U x a Vs Z la ↔
      ∀ t : ℝ, ENNReal.ofReal (topDeg U Z la * (s + t)) ≤ compVol U x a Vs Z (wtOf Dw la 0) t :=
  le_volSlope_iff h _ s

def compDegSlope (a : ℕ) (Vs : ValFam Xo c) (Z : Comp Xo c) (la : Weight Dw) : EReal :=
  degSlope a (fun τ => AllWt.deg (normOn U x V dict Z (τ • wtOf Dw la 0)) (latVal U Vs Z (τ • wtOf Dw la 0)))
    fun τ => Formalism.HN.rkK (latVal U Vs Z (τ • wtOf Dw la 0))

theorem isLimSlope_iff {D' : D7} (Y : Formalism.BasicNotions.DV.ShimX D'.what₂.Tau) (B : ℝ) (u : D'.what₂.Tau → Fin Y.N → ℝ) (k : Y.Comp)
    (s : ℝ) : IsLimSlope (Formalism.MainNotions.WeightThresholdDefs.dimY Y) (fun t => Y.arSelfC (Y.Mbar B u t) k) (fun t => Y.geoC (Y.Mbar B u t) k) s ↔
      IndefiniteRowSideFullHecke.EqualVolumeMeanCorrection.IsSlope Y B u k s := Iff.rfl

end GlobalTheory.CompHt
