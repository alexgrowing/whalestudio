import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthCond
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceLatticeLeThetaLatticeAtPlace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GoodLiftOnto
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFullLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTieCoordBase
import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.PhaseBreaksTargetParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerConjFormsEqCsumAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanEqTopOfTie
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerLeSpanImageKerOfSemilinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateTransposeMajorant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapConjTransposeTwist
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsRingEquivOfIsTranscendenceBasis

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn
open GlobalTheory.LiftLower GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LowForm

section Abstract

variable {K X Y : Type} [Field K] [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]

theorem exists_descent {H W : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup W] [Module ℂ W] {σ₁ σ₂ : K →+* ℂ} (e : σ₁ = σ₂)
    (φ : Y →ₛₗ[σ₁] W) (ψ : X →ₛₗ[σ₂] H) (T : H →ₗ[ℂ] W) (c : ℂ) (h : ∀ x, ∃! y, φ y = c • T (ψ x)) :
    ∃ θ : X →ₗ[K] Y, ∀ x, φ (θ x) = c • T (ψ x) := by
  subst e
  choose f hf hu using h
  refine ⟨⟨⟨f, fun x x' => (hu _ _ ?_).symm⟩, fun a x => (hu _ _ ?_).symm⟩, hf⟩
  · simp only [map_add, hf, smul_add]
  · simp only [map_smulₛₗ, hf, RingHom.id_apply, smul_comm c]

theorem mem_orth_ker [FiniteDimensional K X] {H W : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] {σ : K →+* ℂ} (θ : X →ₗ[K] Y) (j : X →ₛₗ[σ] H) (jW : Y →ₛₗ[σ] W) (th : H →ₗ[ℂ] W)
    (U : W ≃ₗᵢ[ℂ] W) (g : W →ₗ[ℂ] W) (κ : ℂ) (h1 : Submodule.span ℂ (Set.range j) = ⊤)
    (h2 : ∀ (n : ℕ) (b : Fin n → Y), LinearIndependent K b → LinearIndependent ℂ fun k => jW (b k))
    (h3 : ∀ x, U (jW (θ x)) = κ • g (th (j x))) {x : X} (h4 : ∀ u, θ u = 0 → ⟪j x, j u⟫_ℂ = 0) :
    j x ∈ (LinearMap.ker th)ᗮ := by
  have key := GlobalTheory.ker_le_span_image_ker_of_semilinear K X Y H W σ θ j jW
    ((U.symm.toLinearEquiv : W →ₗ[ℂ] W) ∘ₗ (κ • (g ∘ₗ th))) h1 h2 fun x => by
      show U.symm (κ • g (th (j x))) = _
      rw [← h3, U.symm_apply_apply]
  have h5 : LinearMap.ker th ≤ Submodule.span ℂ (j '' (LinearMap.ker θ : Set X)) := fun w hw => key (by
    show U.symm (κ • g (th w)) = 0
    rw [LinearMap.mem_ker.1 hw, map_zero, smul_zero, map_zero])
  refine Submodule.orthogonal_le h5 ((Submodule.mem_orthogonal' _ _).2 fun w hw => ?_)
  have h6 : Submodule.span ℂ (j '' (LinearMap.ker θ : Set X)) ≤ LinearMap.ker (innerₛₗ ℂ (j x)) := by
    rw [Submodule.span_le]
    rintro _ ⟨u, hu, rfl⟩
    exact h4 u hu
  exact h6 hw

theorem re_inner_self {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (x : H) : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 :=
  inner_self_eq_norm_sq (𝕜 := ℂ) x

theorem csumAt_conj [NumberField K] [StarRing K] (S : CSD K) (σ : K →+* ℂ) (f g : S.Forms) :
    csumAt S ((starRingEnd ℂ).comp σ) f g = starRingEnd ℂ (csumAt S σ f g) := by
  unfold csumAt
  simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply, map_sum, map_mul, RingHom.comp_apply]
  rfl

end Abstract

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem toF_mem (i : Fin D.R.m) (t : T0) (y : Fin ((A.fam.L i t).dZ (liftLvl F) (liftSub R F i t)) → D.what₂.LL) :
    (A.fam.L i t).toF (liftLvl F) (liftSub R F i t) y ∈ liftSub R F i t := by
  obtain ⟨f, hf, e⟩ : ((A.fam.L i t).zE (liftLvl F) (liftSub R F i t)).mulVec y ∈
    (A.fam.L i t).Z0 (liftLvl F) (liftSub R F i t) := (subspace_image_spec _ _ _).2.le ⟨y, rfl⟩
  have : (A.fam.L i t).toF (liftLvl F) (liftSub R F i t) y = f :=
    (congrArg (A.fam.L i t).S.basis.equivFun.symm e.symm).trans ((A.fam.L i t).S.basis.equivFun.symm_apply_apply f)
  exact this ▸ hf

theorem norm_wC (i : Fin D.R.m) (v : InfinitePlace D.what₂.LL) (z : Fin (finrank D.what₂.LL (R.WL F false i)) → D.what₂.LL) :
    ‖(R.toCx F).wC false i v (cpt v.embedding z)‖ ^ 2 =
      (RealDat.nP F false)⁻¹ * ‖(R.FW i).j (sgAt D.what₂.embLL v) (coordMap R F i z)‖ ^ 2 := by
  have e : ((Tw.out (s := twAt D.what₂.embLL v) ((R.toCx F).wC false i v (cpt v.embedding z)) :
      R.WS F false i (sgAt D.what₂.embLL v)) : (R.HW i (sgAt D.what₂.embLL v)).H) =
      (((Real.sqrt (RealDat.nP F false))⁻¹ : ℝ) : ℂ) • (R.FW i).j (sgAt D.what₂.embLL v) (coordMap R F i z) := by
    have e0 : (R.toCx F).wC false i v (cpt v.embedding z) = ∑ k, v.embedding (z k) • (R.toCx F).bW false i v k := rfl
    refine (congrArg (fun a => ((Tw.out (s := twAt D.what₂.embLL v) a : R.WS F false i (sgAt D.what₂.embLL v)) :
      (R.HW i (sgAt D.what₂.embLL v)).H)) e0).trans ?_
    refine (congrArg Subtype.val (out_sum _)).trans ((Submodule.coe_sum _ _ _).trans ?_)
    unfold coordMap
    rw [Fintype.linearCombination_apply, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    show cj (twAt D.what₂.embLL v) (v.embedding (z k)) •
      ((((Real.sqrt (RealDat.nP F false))⁻¹ : ℝ) : ℂ) • (R.FW i).j (sgAt D.what₂.embLL v) (R.bL F false i k)) = _
    rw [map_smulₛₗ, emb_eq D.what₂.embLL v, cj_cj, smul_comm]
  have e2 := congrArg norm e
  refine (congrArg (· ^ 2) e2).trans ?_
  show ‖_ • _‖ ^ 2 = _
  rw [norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt (RealDat.nP_pos false).le]

theorem lower_overK (hA : GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.AdelicLiftScalar R F) (h : R.Char F) (hU : R.LUnif) (i : Fin D.R.m) {b : ℝ}
    (hb : GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.Sizes D i b) (ht : GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.PrimeToHost R A.μ0) {σ : D.what₂.LL →+* ℂ} (hσ : OverK σ)
    {v : (R.MW i σ).Vec} (hv : IsExtVec (R.MW i σ) v) {gramR c0R c0L}
    (hT : Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ)
      (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L)
    (hu : ∀ x, ∃! y, IsRatLift R i 1 x y) (hC : ConjAt R i σ 1 (c0L i)) {x : A.fam.amb.FL i A.μ0}
    {y : Fin (R.nW i) → D.what₂.LL} (hy : IsRatLift R i 1 x y)
    (hx : ∀ u, R.thG i A.μ0 (R.jV i A.μ0 u) = 0 → csumAt (A.MtCSD i A.μ0) σ x u = 0) :
    Real.exp (lowB D i b) * (csumAt (A.MtCSD i A.μ0) σ x x).re ≤ ‖(R.FW i).j σ y‖ ^ 2 := by
  have : Countable D.what₂.LL := Countable.of_equiv _ (Module.finBasis ℚ D.what₂.LL).equivFun.toEquiv.symm
  have : FiniteDimensional D.what₂.LL (A.fam.amb.FL i A.μ0) := Module.Finite.of_basis (A.MtCSD i A.μ0).basis
  refine (GlobalTheory.GaloisDescent.exists_complex_ringEquiv_comp_eq D.what₂.embLL σ).elim fun s hs => ?_
  have hs' : GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsEmbOverK D σ s := ⟨fun a => (hs a).symm, hσ⟩
  refine hC.2.1.elim fun μ' a => a.elim fun η' a => a.elim fun c a => a.elim fun c₁ a => a.elim fun H a =>
    a.elim fun j a => a.elim fun th hd => ?_
  refine hC.2.2.elim fun u a => a.elim fun U a => a.elim fun z a => a.elim fun ζ a => ?_
  refine (a.2.2.2 μ' η' c c₁ H j th hd).2.elim fun κ hκ => ?_
  refine (exists_descent (sgAt_mk _ R.hv0) ((R.FW i).j (sg0 D A)) (R.jV i A.μ0) (R.thG i A.μ0) 1 hu).elim fun θ hθ => ?_
  have m1 := inner_conjForms_eq_csumAt R h.models.jV gramR c0R c0L hT i σ c c₁ H j hd.2.2.1
  have m2 := GlobalTheory.ConjSpan.span_conjForms R h.models.jV gramR c0R c0L hT i σ c c₁ H j hd.2.2.1
  have m3 : ∀ u, θ u = 0 → ⟪j x, j u⟫_ℂ = 0 := fun u h0 =>
    (m1 x u).trans (hx u ((one_smul ℂ _).symm.trans ((hθ u).symm.trans
      ((congrArg ((R.FW i).j (sg0 D A)) h0).trans (LinearMap.map_zero _)))))
  have m4 := mem_orth_ker θ j ((R.FW i).j σ) th U (R.gW i σ z) κ m2 (hU i σ).1 (fun x => hκ.2 x _ (hθ x)) m3
  have m5 := conjLift_lower hA h i hb ht hs' hv hC.1 hd _ m4
  have m6 := congrArg Complex.re (GlobalTheory.ConjLiftCounterexample.gram_of_conjAt hC hd hy hy)
  have m7 := (re_inner_self _).symm.trans (m6.trans (re_inner_self _))
  have m8 := (re_inner_self _).symm.trans (congrArg Complex.re (m1 x x))
  exact (congrArg (Real.exp (lowB D i b) * ·) m8).ge.trans (m5.trans m7.ge)

theorem lowForm_of_emb {s : ℕ} (hOk : A.fam.Ok s) (h : R.Char F) (hB : BaseLinks R F) {b : ℝ}
    (hE : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (x : A.fam.amb.FL i A.μ0) (y : Fin (R.nW i) → D.what₂.LL),
      IsRatLift R i 1 x y → (∀ σ' u, R.thG i A.μ0 (R.jV i A.μ0 u) = 0 → csumAt (A.MtCSD i A.μ0) σ' x u = 0) →
      Real.exp (lowB D i b) * (csumAt (A.MtCSD i A.μ0) σ x x).re ≤ ‖(R.FW i).j σ y‖ ^ 2) : LowForm R F b := by
  intro i v hv x
  have hR : IsRatHerm (cmMax D.what₂.LL) ((A.fam.L i A.μ0).HZ (liftLvl F) (liftSub R F i A.μ0))
    ((A.fam.L i A.μ0).XQ (liftLvl F) (liftSub R F i A.μ0)) := hB.2.2 i
  have hf := GlobalTheory.QuotRational.fE_mem_cmMax _ _ _ _ _ (blockHyp (F := F) hOk i A.μ0) hR
  have hm := GlobalTheory.Proof.ConjugateTransposeMajorant.majAt_eq_csumAt _ _ _ hR hf
  have h1 := (GlobalTheory.BigOnBase.j_thetaMat_base hB i A.μ0 x).trans (one_smul ℂ _).symm
  have h2 := hE i (sgAt D.what₂.embLL v) _ _ h1 fun σ' u hu =>
    hm.2 u (fun x' => csum_eq_zero h.models.HV h.models.jV i A.μ0 (toF_mem i A.μ0 x') hu) σ' x
  have e : sgAt D.what₂.embLL v = v.embedding := if_neg fun h0 => hv (h0.trans R.hv0.symm)
  have h3 := congrArg (fun σ => csumAt (A.MtCSD i A.μ0) σ ((A.fam.L i A.μ0).toF (liftLvl F) (liftSub R F i A.μ0) x)
    ((A.fam.L i A.μ0).toF (liftLvl F) (liftSub R F i A.μ0) x)) e
  have h4 := norm_wC (R := R) (F := F) i v ((thetaMat R F i A.μ0).mulVec x)
  have h5 := hm.1 v x x
  have key : ∀ (E n a : ℝ) (N : ℕ) (p q r : ℂ), 0 < n → n = N → E * p.re ≤ a → p = q → r = ((N : ℕ) : ℂ)⁻¹ * q →
      E * r.re ≤ n⁻¹ * a := by
    intro E n a N p q r k0 k1 k2 k3 k4
    rw [k4, ← k3, ← Complex.ofReal_natCast, ← k1, ← Complex.ofReal_inv, Complex.re_ofReal_mul, mul_left_comm]
    exact mul_le_mul_of_nonneg_left k2 (inv_pos.2 k0).le
  exact (key _ _ _ _ _ _ _ (RealDat.nP_pos (F := F) false) rfl h2 h3 h5).trans h4.ge

theorem lowForm : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : RealDat D A J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie J R κ v₀) (Od : ∀ i, OMDat J.toCore R i Unit (fun _ => A.μ0)) (s : ℕ) (b : ℝ), GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.AdelicLiftScalar R F → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.GalLiftFor J R F κ v₀ Od (fun _ => 1) → R.Char F → A.fam.Ok s → BarTie fw → (∀ i, OMPins J R κ v₀ Od i) → (∀ i, PhaseTie J R κ v₀ Od (fun _ => 1) i) → R.LUnif → BaseLinks R F → GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.PrimeToHost R A.μ0 → (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.Sizes D i b) → LowForm R F b := by
  intro D G _ _ Pl0 T0 A J _ R F κ v₀ fw Od s b hA hG h hOk hbar hO hP hU hB ht hb
  refine h.fam.tie.elim fun gramR a => a.elim fun c0R a => a.elim fun c0L hT => ?_
  refine lowForm_of_emb hOk h hB fun i σ x y hy hx => ?_
  have g := hG h fw i (hO i) (hP i)
  by_cases hσ : OverK σ
  · exact lower_overK hA h hU i (hb i) ht hσ (fw.hv₀ i σ).1 hT g.1 (g.2.1 gramR c0R c0L hT σ hσ) hy (hx σ)
  · have g2 := g.2.2 σ hσ
    have k1 := lower_overK hA h hU i (hb i) ht g2.1 (fw.hv₀ i _).1 hT g.1 (g.2.1 gramR c0R c0L hT _ g2.1) hy (hx _)
    have k2 := congrArg Complex.re (g2.2 hbar y y)
    have k3 := (re_inner_self _).symm.trans ((k2.trans (Complex.conj_re _)).trans (re_inner_self _))
    have k4 := (congrArg Complex.re (csumAt_conj (A.MtCSD i A.μ0) σ x x)).trans (Complex.conj_re _)
    exact (congrArg (Real.exp (lowB D i b) * ·) k4).ge.trans (k1.trans k3.ge)

end GlobalTheory.LowForm

end
