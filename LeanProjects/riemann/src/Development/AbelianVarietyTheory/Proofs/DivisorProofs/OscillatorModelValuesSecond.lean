import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightTranslationLiftEqLevelMoveUnitConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActLevMemCuspA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisOApplyZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermCColMulVec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualCHLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepLatticeStabilizerVacuumEqDetCharSmulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DictionaryComponentFrameMarkingUniformisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPairCharactersAtLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelFormCompatBaseEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevAgreesOfIsLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramNegTransposeDiag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstRelIffTwistFactorAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelAtEachIndex
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrMoveValues
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsLetterRowWeightDictionary
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnalyticFibreUnitFrameUniformisation
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnFibLift
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CastFrMemDom

noncomputable section

namespace GlobalTheory.FrameConstMove

section Geo

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.Dict.Lift
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {r g : ℕ} {X : Data E r} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ}
  {idx : Fin g ≃ X.Ψ × Fin r} {e : Fin g ≃ Lt1 Dw} {x : Frame X.Ψ r} {L : Lt E r}

theorem anFib_frMove (σ : c.F →+* ℂ) {ρ : Xo.X ⟶ Xo.X} {ν : SABMap Xo.univ.t Xo.univ.t ρ} :
    letI : Algebra c.F ℂ := σ.toAlgebra
    ∀ (y y' : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y), FrMove ρ ν y y' →
      ∃ A' : AnFib X bas idx e x L y', ∀ θ, A.Reads 1 y.s θ → A'.Reads 1 y'.s θ := by
  letI : Algebra c.F ℂ := σ.toAlgebra
  intro y y' A hm
  obtain ⟨O, ω, o1, o2, o3, o4, o5⟩ := GlobalTheory.MoveValues.frMove_values E H Dw l Xo c σ ρ ν y y' hm
  obtain ⟨Φ, hΦ⟩ := exists_mulEquiv ν.cart y.x y'.x hm.1.symm
  have hL := Xo.univ.t.PP.isLB
  choose ch hch using fun z => exists_chart (A.ex z).left _ hL
  have mem : ∀ {i j z}, ⊤ ≤ (Φ (A.ex z)).left ⁻¹ᵁ Xo.univ.t.PP.L.U i → ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      ⊤ ≤ (A.ex z).left ⁻¹ᵁ O i j := fun hi hj => (o1 _ _ _).2 ⟨by rw [hΦ] at hi; exact hi, hj⟩
  let fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ := fun i z =>
    valAt' (A.ex z).left (O i (ch z)) (ω i (ch z)) * A.fr (ch z) z
  have key : ∀ i j z, ⊤ ≤ (A.ex z).left ⁻¹ᵁ O i j → fr i z = valAt' (A.ex z).left (O i j) (ω i j) * A.fr j z := by
    intro i j z h
    obtain ⟨hi, hj⟩ := (o1 _ _ _).1 h
    have h1 := o3 i (ch z) i j _ ((o1 _ _ _).2 ⟨hi, hch z⟩) h
    rw [val_g_self _ _ hL i hi, _root_.one_mul] at h1
    simp only [fr]
    rw [A.fr_g (ch z) j z ((top_le_preimage_inf _ _ _).2 ⟨hch z, hj⟩), ← _root_.mul_assoc, h1]
  have hex0 : A.ex 0 = 1 := GlobalTheory.HolHom.map_zero_eq_one A.ex_add
  have hl : (fun z => (Φ (A.ex z)).left) = fun z => (A.ex z).left ≫ ν.φ := funext fun z => hΦ _
  have hol : IsHolTo Set.univ (fun z => (Φ (A.ex z)).left) := by
    rw [hl]
    exact GlobalTheory.CMSpreadCompare.isHolTo_postcomp A.hol _
  refine ⟨{ ex := fun z => Φ (A.ex z)
            ex_add := fun z w => by rw [A.ex_add, map_mul]
            ex_onto := Φ.surjective.comp A.ex_onto
            ex_ker := fun z => Φ.map_eq_one_iff.trans (A.ex_ker z)
            ex_lin := fun a z => ?_
            hol := hol
            der := fun ℓ => ?_
            fr := fr
            fr_hol := fun i z₀ hz₀ => ?_
            fr_ne := fun i z h => mul_ne_zero (o2 _ _ _ (mem h (hch z))) (A.fr_ne _ z (hch z))
            fr_g := fun i i' z h => ?_
            fr_0 := fun i h => ?_
            χ := A.χ
            χ_norm := A.χ_norm
            fr_per := fun v hv i z h => ?_ }, fun θ hθ i z pt h1 h2 h => ?_⟩
  · apply Over.OverMorphism.ext
    rw [hΦ, A.ex_lin, Over.comp_left, Over.comp_left, hΦ, Category.assoc, Category.assoc]
    exact congrArg _ (ν.act a)
  · rw [hl, hm.2.1]
    exact FibreDeriv.isDerivAt0_comp (A.der ℓ) ν.φ
  · have hN := A.hol (O i (ch z₀)) (ω i (ch z₀))
    have hn := hN.1.mem_nhds (x := z₀) ⟨trivial, mem hz₀ (hch z₀)⟩
    have d1 : DifferentiableAt ℂ (A.fr (ch z₀)) z₀ :=
      (A.fr_hol (ch z₀)).differentiableAt (Filter.mem_of_superset hn fun z hz => ((o1 _ _ _).1 hz.2).2)
    refine (((hN.2.differentiableAt hn).mul d1).congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [hn] with z hz
    exact key _ _ z hz.2
  · obtain ⟨hi, hi'⟩ := (top_le_preimage_inf _ _ _).1 h
    have h1 := o3 i (ch z) i' (ch z) _ (mem hi (hch z)) (mem hi' (hch z))
    rw [val_g_self _ _ hL _ (hch z), _root_.mul_one] at h1
    simp only [fr]
    rw [h1, hΦ, _root_.mul_assoc]
  · have h1 := o4 i (ch 0) y.x (A.ex 0).left (by rw [hex0]; exact one_left _) (mem h (hch 0))
    simp only [fr]
    rw [A.fr_0 _ (hch 0), ← h1, hm.1]
  · have hz : A.ex (z + pv X idx x v) = A.ex z := by
      rw [A.ex_add, (A.ex_ker _).2 ⟨v, hv, rfl⟩, _root_.mul_one]
    have h2 := key i (ch z) (z + pv X idx x v) (by rw [hz]; exact mem h (hch z))
    rw [h2, hz]
    simp only [fr]
    rw [A.fr_per v hv (ch z) z (hch z)]
    ring
  · have e1 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_snd (𝟙 _) (A.ex z))
    have e2 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_fst (𝟙 _) (A.ex z))
    have v1 := hθ (ch z) z _ e1 e2 (hch z)
    have v2 := o5 i (ch z) _ pt _ e1 e2 (h1.trans (hΦ _)) h2 (mem h (hch z))
    refine v2.trans ((congrArg (_ * ·) v1).trans ?_)
    simp only [fr, zpow_one]
    ring

theorem anFib_of_eq (σ : c.F →+* ℂ) :
    letI : Algebra c.F ℂ := σ.toAlgebra
    ∀ (y y' : FrPt Xo c ℂ), y'.x = y.x → y'.u = y.u → ∃ t : ℂ, t ≠ 0 ∧
      (∀ a n, ∀ f ∈ sec Xo c a n, evR Xo c f y' = t ^ n * evR Xo c f y) ∧
      ∀ A' : AnFib X bas idx e x L y', ∃ A : AnFib X bas idx e x L y,
        ∀ θ, A'.Reads 1 y'.s θ → A.Reads 1 y.s (fun z => t⁻¹ * θ z) := by
  letI : Algebra c.F ℂ := σ.toAlgebra
  intro y y' hx hu
  obtain ⟨x', hover', u', tan', eig', basis', s', gen'⟩ := y'
  simp only at hx hu
  subst hx
  subst hu
  obtain ⟨u0, hu0⟩ := GlobalTheory.CongrOrbit.exists_unit_of_generators (x := y.x) y.s s' y.gen gen'
  refine ⟨u0, u0.ne_zero, fun a n f hf => ?_, fun A => ⟨⟨A.ex, A.ex_add, A.ex_onto, A.ex_ker, A.ex_lin, A.hol, A.der, A.fr,
    A.fr_hol, A.fr_ne, A.fr_g, A.fr_0, A.χ, A.χ_norm, A.fr_per⟩, fun θ hθ j z pt h1 h2 h => ?_⟩⟩
  · obtain ⟨N, _, _, v, ρ, hinj, htan, hcomb, -, -⟩ := GlobalTheory.TanMod.exists_tangent_module E H Dw l Xo ℂ y.x
    have hb : ∀ τ i, ∃ m, v m = y.u τ i := fun τ i => (htan _).1 (y.tan τ i)
    choose b hb using hb
    have hu : ∀ τ, y.u τ = fun i => v (b τ i) := fun τ => funext fun i => (hb τ i).symm
    have hB : FrBor (fun o : Ix Dw => o.elim u0 fun _ => 1) y ⟨y.x, hover', y.u, tan', eig', basis', s', gen'⟩ := by
      refine ⟨rfl, fun τ i => ⟨Pi.single i 1, by simp, fun j hj => Pi.single_eq_of_ne hj.ne' _, ?_⟩,
        𝟙 _, Category.id_comp _, Category.id_comp _, ?_⟩
      · dsimp only
        rw [hu τ, hcomb]
        simp [Pi.single_apply]
      · intro i h
        simp only
        rw [hu0 i]
        simp only [Scheme.Hom.appLE]
        have e : (homOfLE h).op = 𝟙 _ := Subsingleton.elim _ _
        rw [e]
        erw [CategoryTheory.Functor.map_id, Category.comp_id]
        rfl
    rw [(GlobalTheory.Frames.algebraic_laws GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c).2.2.2.2.2.2 ℂ inferInstance a n f hf _ _ _ hB]
    congr 1
    simp [wchar, Fintype.prod_option, ex]
  · have v1 := hθ j z pt h1 h2 h
    have v2 := (GlobalTheory.sec_values_complex_fibre GlobalTheory.abelianSchemeLaws_all.2.secTwist E H Dw l Xo y.x y.s).1 (u0 : ℂ)
      (fun _ => j) pt h2
    have v3 := (congrArg (valAt' pt ((PPx y.x).U (fun _ => j))) (hu0 (fun _ => j))).trans v2
    have v4 := v1.symm.trans v3
    change valAt' pt ((PPx y.x).U (fun _ => j)) (y.s.f fun _ => j) = _
    rw [_root_.mul_assoc, v4, inv_mul_cancel_left₀ u0.ne_zero]

end Geo

section Classical

open NumberField Matrix Complex ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.LevelCusp
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} {X X' : Data E r}

theorem exists_idx {H : Geo.Tor.Host E} {Dw : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} {σ : c.F →+* ℂ}
    (h : SameSp X X') {idx : Fin g ≃ X.Ψ × Fin r} {e : Fin g ≃ Lt1 Dw} (hi : IdxIs c σ X idx e) :
    ∃ idx' : Fin g ≃ X'.Ψ × Fin r, IdxIs c σ X' idx' e ∧ (∀ x v, pv X idx x v = pv X' idx' (castFr h.psi x) v) ∧
      (∀ j, rowType X (idx j) = rowType X' (idx' j)) ∧
      ∀ j, idx' j = (⟨(idx j).1.1, h.psi.le (idx j).1.2⟩, (idx j).2) := by
  obtain ⟨h1, h2, h3, -, -⟩ := h
  cases X
  cases X'
  dsimp only at h1 h2 h3
  subst h1 h2 h3
  exact ⟨idx, hi, fun _ _ => rfl, fun _ => rfl, fun _ => rfl⟩

theorem perC_match {δ : GL (Fin r) E} (h : IsMatch X X' δ) (x : Frame X.Ψ r) (u : (E →+* ℂ) → Fin r → ℂ)
    (τ : X.Ψ) (a : Fin r) :
    perC X' (lact δ (castFr h.psi x)) (fun τ => δ.1.map τ.1 *ᵥ u τ.1) (⟨τ.1, h.psi.le τ.2⟩, a) =
      perC X x (fun τ => u τ.1) (τ, a) := by
  have hd : IsUnit (δ.1.map τ.1).det := by
    rw [show (δ.1.map τ.1).det = τ.1 δ.1.det from (RingHom.map_det τ.1 _).symm]
    exact (Matrix.isUnits_det_units δ).map τ.1
  have e : mat (lact δ (castFr h.psi x)) ⟨τ.1, h.psi.le τ.2⟩ = δ.1.map τ.1 * mat x τ := rfl
  simp only [perC, ← h.p0]
  split_ifs
  · exact h.hermC_eq τ.1 (FD.col (mat x τ) a) (u τ.1)
  · rw [e, Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec (u τ.1), Matrix.nonsing_inv_mul _ hd,
      Matrix.one_mulVec]

theorem hx_match (h : SameSp X X') {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r}
    {bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X'.Λ} {idx' : Fin g ≃ X'.Ψ × Fin r} (hs : IsSympl X bas) (hs' : IsSympl X' bas')
    {x : Frame X.Ψ r} (hxd : x ∈ X.dom) (hpv : ∀ v, pv X idx x v = pv X' idx' (castFr h.psi x) v)
    {δ : GL (Fin r) E} (hδ : IsUn X' δ) (z w : Fin g → ℂ) :
    hx X' bas' idx' (lact δ (castFr h.psi x)) z w = hx X bas idx x z w := by
  obtain ⟨-, -, him, -⟩ := hx_laws E r X g bas idx 0 hs Even.zero x hxd
  obtain ⟨-, -, -, -, -, -, huniq, hinv⟩ := hx_laws E r X' g bas' idx' 0 hs' Even.zero _ (h.castFr_mem_dom hxd)
  rw [(hinv δ hδ).2.2.2, hx_eq_hermForm idx]
  refine ((huniq X'.Λ X'.Λ_span).2 _ (Hm_isHermitian idx hs hxd) (fun u _ v _ => ?_) z w).symm
  rw [← hpv, ← hpv, ← hx_eq_hermForm, him, h.EF_eq]

theorem exists_ne_zero_of_meanOne {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r} {x : Frame X.Ψ r}
    {L : Lt E r} {ϑ : (Fin g → ℂ) → ℂ} (h : MeanOne X bas idx x L ϑ) : ∃ z, ϑ z ≠ 0 := by
  obtain ⟨_, _, -, -, h⟩ := h
  by_contra h0
  push Not at h0
  simp [h0] at h

end Classical

section Adelic

open NumberField Matrix Complex ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.LevelCusp GlobalTheory.DictMove
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem actO_one_left (V W : HSp D) (k : GA D W) (u : WO V W) :
    actO V W 1 k u = HMul.hMul (Formalism.L2.Theta.mt W k) (u : Matrix (Fin W.rank) (Fin V.rank) (AE D)) := by
  unfold actO
  rw [inv_one, show Formalism.L2.Theta.mt V 1 = 1 from rfl, Matrix.mul_one]

theorem realM_mul (θ : InfFam D) {m n p : ℕ} (u : Mx D m n) (v : Mx D n p) (τ : D.host.E →+* ℂ) :
    realM θ (HMul.hMul (u : Matrix (Fin m) (Fin n) (AE D)) (v : Matrix (Fin n) (Fin p) (AE D))) τ =
      realM θ u τ * realM θ v τ := by
  unfold realM
  split_ifs with h
  · exact Matrix.map_mul (f := (θ h.choose).comp (infPart D))
  · rw [Matrix.zero_mul]

def ReadsGen (θ : InfFam D) (V W : HSp D) {H : Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Geo.Tor.Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} (U : Unf Xo c σ W.rank) (k : U.Comp) (x : (U.X k).dom)
    (F : WO V W → ℂ) (a : ℂ) : Prop :=
  ∀ (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (U.X k).Λ) (idx : Fin g ≃ (U.X k).Ψ × Fin W.rank) (e : Fin g ≃ Lt1 Dw),
    IsSympl (U.X k) bas → IdxIs c σ (U.X k) idx e → ∀ ϑ : (Fin g → ℂ) → ℂ, GenReads U k bas idx e x ϑ →
      ∀ w : WO V W, w.map (finPart D) = 0 →
        F w = a * cexp (-(Real.pi / 2 : ℂ) * ∑ b, hx (U.X k) bas idx x.1
            (zOf θ V W rfl (U.X k) idx x.1 w b) (zOf θ V W rfl (U.X k) idx x.1 w b)) *
          ∏ b, ϑ (zOf θ V W rfl (U.X k) idx x.1 w b)

set_option maxHeartbeats 1000000 in

theorem const_move {H : Geo.Tor.Host D.host.E} {Dw : Datum H} {W : HSp D} {l : Geo.Tor.Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {U : Unf Xo c σ W.rank} {g : ℕ}
    {e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ)}
    {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)}
    {ik : U.Comp → Fin F.n} {φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ}
    (hσ : GoodEmb c σ) (hU : IsUnf U) (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A = 1) (hM : ∀ k, IsMod W rfl (U.X k))
    (hP' : HasPeriods φ) {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V : HSp D} {χV χW : (AE D)ˣ →* Circle}
    {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} (hP : IsPair ψ θ V W χV χW om)
    {s s' : Dw.La →ₗ[𝓞 D.host.E] Dw.La} {k k' : U.Comp} {δ : GL (Fin W.rank) D.host.E} (hc : Carries φ s k k' δ)
    {x : Frame (U.X k).Ψ W.rank} {x' : Frame (U.X k').Ψ W.rank} (hx : x ∈ (U.X k).dom) (hx' : x' ∈ (U.X k').dom)
    (hu : IsUnitFr (U.X k) x) (hfr : x' = lact δ (castFr hc.mt.psi x)) {γ : GA D W}
    (hδa : ∀ τ : (U.X k').Ψ, realM θ (Formalism.L2.Theta.mt W γ) τ.1 = δ.1.map τ.1) {F₁ F₂ : WO V W → ℂ} {m₁ m₂ : ℂ}
    (c₁ : ReadsGen θ V W U k ⟨x, hx⟩ F₁ m₁) (c₂ : ReadsGen θ V W U k' ⟨x', hx'⟩ F₂ m₂)
    (hF : ∀ w, F₂ (actO V W 1 γ w) = F₁ w) {ρ : Xo.X ⟶ Xo.X} {ν : SABMap Xo.univ.t Xo.univ.t ρ}
    {y' : FrPt Xo c (CAt σ)} (hν : IsLevMove ρ ν s s') (hm : FrMove ρ ν (U.un k ⟨x, hx⟩) y')
    {a : (D.host.E →+* ℂ) × ℕ → ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c a V.rank) :
    m₁ * toC (evR Xo c f y') = m₂ * toC (evR Xo c f (U.un k' ⟨x', hx'⟩)) := by
  subst hfr
  letI : Algebra c.F ℂ := σ.toAlgebra
  have hmt := hc.mt
  have hr1 : 1 ≤ W.rank := hU.1 ▸ hpq
  obtain ⟨Wt⟩ := nonempty_uw (U := Formalism.L2.PjFree.Unf.ofPj U) hU
  have hSD := fun k => (GlobalTheory.T.uniformisation_component_lattices_markings _ H Dw l Xo c σ _ (Formalism.L2.PjFree.Unf.ofPj U) hσ hU hr1 Wt k).2.1
  have hS : SameSp (U.X k) (U.X k') := ⟨hmt.psi, hc.gm.symm, hmt.p0, hmt.xi, (hM k).kap.trans (hM k').kap.symm⟩
  obtain ⟨Dc, hDc, -⟩ := GlobalTheory.Dict.exists_dic _ H Dw l c σ _ Wt.g 0 (U.X k) 0 Wt.e hσ hU.1 (hU.2.1 k).1 (hU.2.1 k).2
    (hSD k) ⟨fun _ => antitone_const, Even.zero⟩
  have hi : IdxIs c σ (U.X k) Dc.idx Wt.e := hDc ▸ ⟨Dc.per_eq, Dc.ty_eq⟩
  obtain ⟨idx', hi', hpv, hty, hidx⟩ := exists_idx hS hi
  obtain ⟨bas', hb'⟩ := GlobalTheory.Dict.Letters.exists_isSympl (U.X k') (hSD k') idx'
  obtain ⟨A, -, ϑ, hϑ, hone⟩ := GlobalTheory.Dict.uw_anFib _ H Dw l Xo c σ _ (Formalism.L2.PjFree.Unf.ofPj U) hσ hU hr1 Wt k Dc.bas Dc.idx
    Dc.sympl hi.1 hi.2 ⟨x, hx⟩ hu
  obtain ⟨a₁, b₁⟩ := move_eq hσ hpq hA hP' hc hν ⟨x, hx⟩ hm
  obtain ⟨A₁, r₁⟩ := anFib_frMove σ _ y' A hm
  have hδ : IsUn (U.X k') δ := fun u v => (hmt.iso u v).trans (by rw [hc.gm])
  obtain ⟨-, -, -, A₂, r₂, -⟩ := GlobalTheory.Dict.anFib_move _ H Dw l Xo c _ _ (U.X k) (U.X k') hS Dc.bas Dc.idx bas' idx' Wt.e x _
    y' A₁ δ Dc.sympl hb' hx (hSD k) hδ (hpv x) hty
  have hlat : mapL δ (U.X k).Λ = (U.X k').Λ := by
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact (hmt.lat u).1 hu
    · intro hv
      have e : δ.1 *ᵥ ((δ⁻¹).1 *ᵥ v) = v := by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      exact ⟨_, (hmt.lat _).2 (e.symm ▸ hv), e⟩
  obtain ⟨t, ht, hval, hA₃⟩ := anFib_of_eq (X := U.X k') (bas := bas') (idx := idx') (e := Wt.e)
    (x := lact δ (castFr hmt.psi x)) (L := mapL δ (U.X k).Λ) σ (U.un k' ⟨_, hx'⟩) y' a₁ b₁
  obtain ⟨A₃, r₃⟩ := hA₃ A₂
  have g₂ : GenReads U k' bas' idx' Wt.e ⟨_, hx'⟩ fun z => t⁻¹ * ϑ z := by
    have := r₃ _ (r₂ _ (r₁ _ hϑ))
    clear r₃
    revert A₃
    rw [hlat]
    exact fun A₃ h => ⟨A₃, h⟩
  obtain ⟨z, hz⟩ := exists_ne_zero_of_meanOne hone
  obtain ⟨pt, -, hpt, -⟩ := (GlobalTheory.AdTh.RealCoord.zOf_coordinates D ψ θ V W _ _ rfl (U.X k) Dc.bas Dc.idx hP.weil.std hP.inf
    hP.std hP.even (hM k) Dc.sympl x).2.2.2.2 hx
  obtain ⟨w0, wz⟩ := hpt fun _ => z
  generalize pt (fun _ => z) = w at w0 wz
  have wz' : zOf θ V W rfl (U.X k') idx' (lact δ (castFr hmt.psi x)) (actO V W 1 γ w) = fun _ => z := by
    rw [← wz]
    funext b j
    refine Eq.trans ?_ (perC_match hmt x (fun τ a => realM θ w τ a b) (Dc.idx j).1 (Dc.idx j).2)
    rw [← hidx]
    refine congrArg (fun u => perC _ _ u _) (funext fun τ => ?_)
    rw [actO_one_left, realM_mul, hδa]
    rfl
  have v₁ := c₁ _ Dc.bas Dc.idx Wt.e Dc.sympl hi ϑ ⟨A, hϑ⟩ w w0
  have v₂ := c₂ _ bas' idx' Wt.e hb' hi' _ g₂ (actO V W 1 γ w) (by
    rw [actO_one_left, Matrix.map_mul, w0, Matrix.mul_zero])
  rw [hF, v₁, wz, wz'] at v₂
  simp only [hx_match hS Dc.sympl hb' hx (hpv x) hδ, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    mul_pow, inv_pow] at v₂
  have key : m₁ * t ^ V.rank = m₂ := by
    have h1 := pow_ne_zero V.rank ht
    have h2 := pow_ne_zero V.rank hz
    field_simp at v₂
    linear_combination v₂
  rw [← key, mul_assoc]
  exact congrArg _ (hval a _ f hf)

set_option maxHeartbeats 1000000 in

theorem value_move {H : Geo.Tor.Host D.host.E} {Dw : Datum H} {W₀ W : HSp D} (hV : W₀ = W) {l : Geo.Tor.Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (hr : W₀.rank = r) (hr' : W.rank = r) {U : Unf Xo c σ r}
    {dict : GA D W₀ → Σ k, Frame (U.X k).Ψ r} (io : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)) {g : ℕ}
    {e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ)}
    {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)}
    {ik : U.Comp → Fin F.n} {φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ}
    {th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}
    {x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ}
    (hσ : GoodEmb c σ) (hU : IsUnf U) (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A = 1) (hM : ∀ k, IsMod W hr' (U.X k))
    (hL : DictLat U W₀ hr dict (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ io) e F ik φ th x₀)
    (hth : ∀ k τ, IsInfEmb τ.1 (th k τ)) (hdom : ∀ h, (dict h).2 ∈ (U.X (dict h).1).dom)
    (hunit : ∀ h, IsUnitFr (U.X (dict h).1) (dict h).2)
    {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V : HSp D} {χV χW : (AE D)ˣ →* Circle}
    {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} (hP : IsPair ψ θ V W χV χW om) {f₀ : WO V W → ℂ}
    (hf₀ : IsThetaFunO ψ V W f₀) {mu : GA D W → ℂ} (hmu : ∀ a b, mu (a * b) = mu a * mu b) (hmu0 : ∀ a, mu a ≠ 0)
    {cc : U.Comp → ℂ} (hcc : CcIs θ V W hr' U (castDict hV dict) mu x₀ om f₀ cc)
    {s s' : Dw.La →ₗ[𝓞 D.host.E] Dw.La} {κ : GA D W}
    (hκ : Induces W l (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr') ∘ₗ io) s κ)
    (hvac : om (1, κ) f₀ = mu κ • f₀) {a : (D.host.E →+* ℂ) × ℕ → ℕ} {f f' : Rul Xo c} (hf : f ∈ sec Xo c a V.rank)
    (hmv : ∀ y : FrPt Xo c (CAt σ), ∃ (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (y' : FrPt Xo c (CAt σ)),
      IsLevMove ρ ν s s' ∧ FrMove ρ ν y y' ∧ evR Xo c f' y = evR Xo c f y') (h : GA D W) :
    cc (castDict hV dict h).1 * rdU U f' (castDict hV dict h).1 (castDict hV dict h).2 =
      cc (castDict hV dict (h * κ)).1 * rdU U f (castDict hV dict (h * κ)).1 (castDict hV dict (h * κ)).2 := by
  subst hV
  subst hr
  change DictLat U W₀ rfl dict io e F ik φ th x₀ at hL
  change CcIs θ V W₀ rfl U dict mu x₀ om f₀ cc at hcc
  change Induces W₀ l io s κ at hκ
  change cc (dict h).1 * rdU U f' (dict h).1 (dict h).2 = cc (dict (h * κ)).1 * rdU U f (dict (h * κ)).1 (dict (h * κ)).2
  have hG : ∀ k, (U.X k).Gm = -W₀.gramᵀ := fun k => (hM k).model.1
  have hxi : ∀ k k', (U.X k).ξ0 = (U.X k').ξ0 := fun k k' => (hM k).model.2.trans (hM k').model.2.symm
  obtain ⟨θ', hθ'⟩ := (GlobalTheory.Member.infiniteAdele_bijective D).1
  obtain ⟨hAr, -, -⟩ := GlobalTheory.T.archimedeanMatrix_unitary_continuous_multiplicative D W₀ θ' hθ'
  obtain ⟨γ₁, hγ₁, hΛ₁, hm₁, hf₁⟩ := hL.2 h
  obtain ⟨γ₂, hγ₂, hΛ₂, hm₂, hf₂⟩ := hL.2 (h * κ)
  have hat : ∀ h γ, γ ∈ GQ W₀ → ((U.X (dict h).1).Λ : Set (Fin W₀.rank → D.host.E)) =
      (fun v : Fin W₀.rank → D.host.E => v ∘ Fin.cast rfl) '' (latG W₀ (γ * h) : Set _) →
      (∀ τ : (U.X (dict h).1).Ψ, mat (dict h).2 τ = archM W₀ (th (dict h).1 τ) (γ * h) * x₀ τ.1) →
      AtComp θ W₀ rfl U.X dict x₀ h γ := fun h γ h1 h2 h3 =>
    ⟨h1, SetLike.coe_injective h2.symm, funext fun τ => (h3 τ).trans (by
      rw [← GlobalTheory.AdTh.MarkUniq.realM_mt hP.inf W₀ _ τ.1 (((hM _).psi τ.1).1 τ.2) _ (hth _ τ)]
      rfl)⟩
  have c₁ := hcc.2 h γ₁ (hat h γ₁ hγ₁ hΛ₁ hf₁)
  have c₂ := hcc.2 (h * κ) γ₂ (hat _ γ₂ hγ₂ hΛ₂ hf₂)
  have e₀ : γ₂ * (h * κ) = γ₂ * γ₁⁻¹ * (γ₁ * h) * κ := by group
  have hγ := mul_mem hγ₂ (inv_mem hγ₁)
  obtain ⟨δ, hδu, hδf, hδa⟩ := GlobalTheory.MarkCoset.rational_matrix W₀ (γ₂ * γ₁⁻¹) hγ
  obtain ⟨gam, e₁, t₁, hgam⟩ := GlobalTheory.TwistTie.marked_isometry_half W₀ l io (U.X (dict h).1) (U.X (dict (h * κ)).1) _ _
    (φ _) (φ _) (F.t _) (F.t _) s (γ₁ * h) (γ₂ * γ₁⁻¹) κ (hM _).model (hM _).model (hL.1.1 _) (hL.1.1 _) δ hδu hδf
    hκ.2.1 hκ.2.2 ⟨hΛ₁, hm₁⟩ (by rw [← e₀]; exact ⟨hΛ₂, hm₂⟩)
  have hmt : IsMatch (U.X (dict h).1) (U.X (dict (h * κ)).1) δ := by
    refine ⟨Finset.ext fun τ => ((hU.2.1 _).2 τ).trans ((hU.2.1 _).2 τ).symm, (hU.2.1 _).1.trans (hU.2.1 _).1.symm,
      hxi _ _, fun u v => by rw [hG, hG]; exact hδu u v, fun v => ⟨fun hv => ?_, fun hv => ?_⟩⟩
    · obtain ⟨a, ha⟩ := (φ _).surjective ⟨v, hv⟩
      rw [show v = (φ (dict h).1 a : Fin W₀.rank → D.host.E) by rw [ha], ← hgam]
      exact (φ _ _).2
    · obtain ⟨a, ha⟩ := (φ _).surjective ⟨_, hv⟩
      obtain ⟨b, rfl⟩ := gam.surjective a
      have h1 := congrArg (fun u => (δ⁻¹).1 *ᵥ u) ((hgam b).symm.trans (congrArg Subtype.val ha))
      simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at h1
      rw [← h1]
      exact (φ _ _).2
  have hc : Carries φ s (dict h).1 (dict (h * κ)).1 δ := ⟨hmt, by rw [hG, hG], gam, e₁, t₁, hgam⟩
  have hfr : (dict (h * κ)).2 = lact δ (castFr hmt.psi (dict h).2) := funext fun τ => by
    change mat (dict (h * κ)).2 τ = δ.1.map τ.1 * mat (dict h).2 ⟨τ.1, hmt.mem τ⟩
    rw [hf₁, hf₂, GlobalTheory.LettersCheck.isInfEmb_unique τ.1 _ _ (hth _ τ) (hθ' τ.1),
      GlobalTheory.LettersCheck.isInfEmb_unique τ.1 _ _ (hth _ ⟨τ.1, hmt.mem τ⟩) (hθ' τ.1), e₀, (hAr τ.1).2.1, (hAr τ.1).2.1,
      (hAr τ.1).2.2.1 κ hκ.1, hδa τ.1 _ (hθ' τ.1), Matrix.mul_one, ← Matrix.mul_assoc]
    rfl
  obtain ⟨ρ, ν, y', hν, hm, hv⟩ := hmv (U.un _ ⟨_, hdom h⟩)
  have hm2 : ∀ a b : GA D W₀, om (1, a * b) = om (1, a) * om (1, b) := fun a b => by
    rw [← map_mul, Prod.mk_mul_mk, one_mul]
  have key := const_move hσ hU hpq hA hM hL.1.2 hP hc (hdom h) (hdom _) (hunit h) hfr (γ := γ₂ * γ₁⁻¹)
    (fun τ => (GlobalTheory.AdTh.MarkUniq.realM_mt hP.inf W₀ _ τ.1 (((hM _).psi τ.1).1 τ.2) _ (hθ' τ.1)).trans (hδa _ _ (hθ' τ.1)))
    (F₁ := fun w => mu κ * om (1, γ₁ * h) f₀ w) (m₁ := mu κ * (cc (dict h).1 * mu h))
    (fun g bas idx e h1 h2 ϑ h3 w h4 => by
      beta_reduce
      rw [c₁ (hdom h) g bas idx e h1 h2 ϑ h3 w h4]
      ring) (c₂ (hdom _))
    (fun w => by
      rw [e₀, hm2, hm2, Module.End.mul_apply, Module.End.mul_apply, hvac, map_smul, map_smul, Pi.smul_apply,
        GlobalTheory.WeilRat.om_rat_actO D ψ hP.weil.std V W₀ χV χW om hP.weil 1 (one_mem _) _ hγ _ (hP.weil.om_pres _ _ hf₀)]
      rfl) hν hm hf
  have u₁ : rdU U f' (dict h).1 (dict h).2 = toC (evR Xo c f' (U.un _ ⟨_, hdom h⟩)) := dif_pos (hdom h)
  have u₂ : rdU U f (dict (h * κ)).1 (dict (h * κ)).2 = toC (evR Xo c f (U.un _ ⟨_, hdom (h * κ)⟩)) := dif_pos (hdom _)
  rw [u₁, u₂, hv]
  apply mul_left_cancel₀ (mul_ne_zero (hmu0 h) (hmu0 κ))
  rw [hmu] at key
  linear_combination key

end Adelic

end GlobalTheory.FrameConstMove

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameConstMove

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem chi_mul_mu (hR : R.toLevCh.Is A.μ0) (i : Fin D.R.m) {mu : GA D (Wc D i) → ℂ}
    (hmu : MuVal (Wc D i) (R.mu0 ((i : ℕ) + 1)) mu) {g : G} {k : GA D (Wc D i)}
    (hk : Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k) :
    (∏ PP : R.Pg, ((R.chi ((i : ℕ) + 1) PP.1 (Matrix.GeneralLinearGroup.det (R.eG g PP)) : ℂˣ) : ℂ)) * mu k = 1 := by
  obtain ⟨l, ⟨hM, -⟩, hMb⟩ := Formalism.L2.Pj.levelPb_exists D R.C.P.pb R.C.P.pb_over
  obtain ⟨a, b, s, s', hb, hs, hs', hin, hout⟩ := GlobalTheory.GeoLevel.exists_half_elements l R.Pg fun P => by
    rw [hMb, GlobalTheory.LiftLevel.prod_le_iff]
    exact hR.Pg P
  obtain ⟨x, -, hroot, hval⟩ := GlobalTheory.GeoLevel.exists_root_char (L := R.datWp i R.triv) (rank_Wc i).symm hk (hR.mu0 i)
    (R.C.isMu0 i).tame l.M (fun P hP => (R.C.isMu0 i).unr P fun n hn => hP (by
      have hn' : ((D.host.g n : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := hn
      rw [hM, Nat.cast_mul]
      fin_cases n
      · exact Ideal.mul_mem_right _ _ hn'
      · exact Ideal.mul_mem_left _ _ hn'))
    (fun P => (R.chi ((i : ℕ) + 1) P)⁻¹) (hR.chi i) a b s s' hb hs hs' hin hout
  rw [hmu.2 k x hroot, hval]
  exact Finset.prod_mul_distrib.symm.trans (Finset.prod_eq_one fun P _ => Units.mul_inv _)

theorem om_lift_vac {F : Face D A} (hR : R.Char F) (i : Fin D.R.m) (hV : VStd D i) (H : Geo.Tor.Host D.host.E)
    {mu : GA D (Wc D i) → ℂ} (hmu : MuVal (Wc D i) (R.mu0 ((i : ℕ) + 1)) mu) {g : G} {k : GA D (Wc D i)}
    (hk : Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k) :
    R.ωP i A.μ0 (1, k) (R.vacP i) = mu k • R.vacP i := by
  obtain ⟨hP, hV0, -, -, sV, sW, -⟩ := GlobalTheory.AdTh.RecPair.isPair_record D G Pl0 T0 A Ks R F hR i A.μ0 hV
  have hχ : (Lift.chrTh (R.toLevCh.mu A.μ0) R.eta ((i : ℕ) + 1)).1 = R.mu0 ((i : ℕ) + 1) := MonoidHom.ext fun x => by
    show R.mu0 ((i : ℕ) + 1) x * R.xi A.μ0 x = _
    rw [GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (χ := R.xi A.μ0) (hR.lev.xi_base ▸ hR.lev.xi A.μ0) x, mul_one]
  have hl : Formalism.L2.Pj.latHat (Wc D i) = GlobalTheory.AdLat.hat D.host.F (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) := by
    rw [GlobalTheory.PrincInLevel.eq_latC (hR.lev.βW i)]
    exact (GlobalTheory.Member.latHat_eq_hat_and_gram D _).1
  have mv : ∀ {g k}, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g k → ∀ u, u ∈ _ → actO (Vc D i) (Wc D i) 1 k u ∈ _ :=
    fun hk => GlobalTheory.MovedLat.actO_mem (Vc D i) (Wc D i) 1 _ (R.ΛV i) (R.ΛV i) (R.ΛW i) (R.ΛW i)
      (fun z hz => by rw [map_one, Units.val_one, Matrix.one_mulVec]; exact hz)
      (fun z hz => by rw [← hl] at hz ⊢; exact GlobalTheory.DictMove.mulVec_mem_latHat (hR.lev.βW i) hk hz)
  refine GlobalTheory.T.weilRep_lattice_stabilizer_vacuum_eq_det_char_smul D _ _ _ _ _ _ _ hP mu (hχ ▸ hmu) H _ _ hV0 sV sW _
    (GlobalTheory.FrameEquiv.isCartanInv_cart_model (R.MW i (sg0 D A))) _ (hR.thP.vP i A.μ0).1 k hk.1 fun u => ⟨mv hk u, fun hu => ?_⟩
  have h := mv (GlobalTheory.ProjComm.isLift_inv hk) _ hu
  rw [actO_one_left, actO_one_left, ← Matrix.mul_assoc] at h
  unfold Formalism.L2.Theta.mt at h
  rwa [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mul] at h

theorem eq_add_nsmul_neg {M : Type} [AddCommGroup M] {a b w : M} {n : ℕ} (h : a - b = n • w) : b = a + n • -w := by
  rw [smul_neg, ← h]
  abel

theorem muVal_cast {V W : HSp D} (hV : V = W) {χ : (AE D)ˣ →* Circle} {mu : GA D V → ℂ} (h : MuVal V χ mu) :
    MuVal W χ (castDict hV mu) := by
  subst hV
  exact h

set_option maxHeartbeats 1000000 in

theorem equivAt_of_ccIs : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.Char F → TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∀ cc, CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.U ((i : ℕ) + 1) O.s0) O.dict O.mu (T.x₀ ((i : ℕ) + 1) O.s0) (R.ωP i A.μ0) (R.vacP i) cc → ∀ u : ℂ, O.EquivAt (κ i) (u • cc) := by
  intro _ D G _ _ Pl0 T0 A T _ R F κ v₀ hR ht i Tp tup O hO cc hcc u g k hk f hf
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have h := ht.laws
  have hact := hO.act.1
  refine ⟨GlobalTheory.GeoLevel.actLev_mem_cuspA h.toLawsM hj hact (κ i) g hf, fun p => ?_⟩
  have hσ : GoodEmb T.Q.c O.s0 := T.good_σ₀
  obtain ⟨_, _, -, hd⟩ := h.dictU _ hj _ hσ
  obtain ⟨hr, g₀, e, F₀, ik, φ, th, -, -, hth, hL⟩ := h.adPin _ hj _ hσ
  obtain ⟨-, hA, -, -, -, -, hnum⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q h.pins
  have hU := h.unf _ hj _ hσ
  have hpq := hU.1 ▸ (show 1 ≤ D.R.r from (hnum _ hj).2.1)
  have hmod := GlobalTheory.AdTh.models_at_record D G Pl0 T0 A T R F κ v₀ hR ht i O.s0 rfl
  have hn : (κ i).n = (Vc D i).rank := (hmod (O.dict p).1).2.2.2.2.2.2.2.2.2.2.2.1
  have hmu : MuVal (Wc D i) (R.mu0 ((i : ℕ) + 1)) O.mu := by
    rw [← chiTie_of_chiR T R ht.alg h.pins.2.2.1 ht.chiR i]
    exact muVal_cast O.hV (h.muVal _ hj _ hσ)
  have hmul : ∀ a b, O.mu (a * b) = O.mu a * O.mu b := GlobalTheory.GeoLevel.castDict_mu_mul (h.muUnit _ hj _ hσ).1 O.hV
  have hag := GlobalTheory.LiftAgrees.levAgrees_of_isLift R i hR.lev _ (iotaW T i) (Mfr T.Q.l) O.lev
    (GlobalTheory.LevelAction.latEmb_iotaW T h i) (h.pins.2.1.1 ▸ hO.lift.lev) g k hk
  have hs : f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (wtA (κ i)) (Vc D i).rank := hn ▸ ((mem_cusp _ _ _ _ _ _).1 hf).1
  have key := value_move O.hV hr (rank_Wc i) (T.iota _) hσ hU hpq hA (fun c => (hmod c).1) hL hth hd.2.2.2.1
    (h.muUnit _ hj _ hσ).2.2.2 (GlobalTheory.AdTh.RecPair.isPair_record D G Pl0 T0 A _ R F hR i A.μ0 hO.lift.std).1
    (hR.thP.vP i A.μ0).1.2.theta hmul (fun a => norm_ne_zero_iff.1 ((hmu.norm a).trans_ne one_ne_zero)) hcc
    (s := O.lev g) (s' := LinearMap.id) (κ := k)
    ⟨hk.1, GlobalTheory.DictMove.latGHat_eq (hR.lev.βW i) hk, fun a ha => by
      obtain ⟨w, hw, ew⟩ := hag a ha
      refine ⟨-w, neg_mem hw, ?_⟩
      rw [h.pins.2.1.1]
      exact eq_add_nsmul_neg ew⟩
    (om_lift_vac hR i hO.lift.std T.Q.H hmu hk) (f' := actLev T.Q.c O.lev2 g f) hs (fun y => by
      obtain ⟨ρ, ν, -, hν, hm⟩ := mvPt_spec hact.total g y
      exact ⟨ρ, ν, _, hν, hm, evalAt_actL hact (h.evalWD _ hj) frMap_trans_id g hs.1 y⟩) p
  have h1 := chi_mul_mu hR.lev i hmu hk
  change u * cc (O.dict p).1 * O.mu p * rdU _ _ (O.dict p).1 (O.dict p).2 =
    _ * (u * cc (O.dict (p * k)).1 * O.mu (p * k) * rdU _ f (O.dict (p * k)).1 (O.dict (p * k)).2)
  rw [hmul]
  linear_combination u * O.mu p * key - u * O.mu p * cc (O.dict (p * k)).1 *
    rdU (T.U ((i : ℕ) + 1) O.s0) f (O.dict (p * k)).1 (O.dict (p * k)).2 * h1

end GlobalTheory.FrameConstMove
