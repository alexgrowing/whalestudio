import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitOfCocompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteUnitaryCocompact
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBoundedUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaFunNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumOfSplittingCharacters
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsEtaTildeUnramified
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisOApplyZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilRepresentationContinuous
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SphericalSectionOfMemCompact

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unf.Inhab

variable {D : D7}

theorem nonempty_vol (V : HSp D) : Nonempty (Vol V) :=
  let ⟨μ, 𝓕, h1, h2⟩ := GlobalTheory.RawLift.exists_haar_fundDomain V
  ⟨⟨μ, 𝓕, h1, h2⟩⟩

theorem nonempty_volN {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) : Nonempty (VolN d) :=
  let ⟨ν, 𝓝, h⟩ := GlobalTheory.Per.UnitN.exists_isUnitN D S ρ d.e (isIsoSub_e d)
  ⟨⟨ν, 𝓝, h⟩⟩

theorem nonempty_volM (D : D7) (m n : ℕ) : Nonempty (VolM D m n) :=
  let ⟨μ, 𝓕, h⟩ := exists_isCovolOne D m n
  ⟨⟨μ, 𝓕, h⟩⟩

theorem nonempty_volU (D : D7) (ρ : ℕ) : Nonempty (VolU D ρ) :=
  let ⟨ν, h⟩ := (GlobalTheory.UnitU.isUnitU_exists_unique_rightInvariant D ρ).1
  ⟨⟨ν, h⟩⟩

theorem coCpt_of_mul {V : HSp D} (h : ∃ K : Set (GA D V), IsCompact K ∧ ∀ g, ∃ γ ∈ GQ V, ∃ k ∈ K, g = γ * k) : CoCpt V := by
  obtain ⟨K, hK, h⟩ := h
  refine ⟨K, hK, fun g => ?_⟩
  obtain ⟨γ, hγ, k, hk, rfl⟩ := h g
  exact ⟨γ⁻¹, inv_mem hγ, by rwa [inv_mul_cancel_left]⟩

theorem coCpt_of_isAniso {V : HSp D} (h : IsAniso V) : CoCpt V :=
  coCpt_of_mul (GlobalTheory.Mem.AnisoQuotient.exists_compact D V h)

theorem coCpt_of_posDef {V : HSp D} (h : ∀ τ, (gramAt D V τ).PosDef) : CoCpt V :=
  coCpt_of_mul (GlobalTheory.definite_unitary_cocompact V h)

theorem exists_weil {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D) {χS χT : (AE D)ˣ →* Circle}
    (h1 : IsHeckeChar D χS) (h2 : IsHeckeChar D χT) (h3 : ResEta D χS S.rank) (h4 : ResEta D χT T.rank) :
    ∃ om, IsWeilDatumO ψ S T χS χT om :=
  GlobalTheory.WeilExist.exists_isWeilDatumO D ψ hψ S T χS χT (GlobalTheory.WeilParts.exists_isEtaTilde_unramified D) h1 h2 h3 h4

theorem exists_weil_pair {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D) :
    ∃ χS χT om, IsWeilDatumO ψ S T χS χT om :=
  let ⟨χS, a1, a2⟩ := GlobalTheory.RawLift.exists_hecke_resEta D S.rank
  let ⟨χT, b1, b2⟩ := GlobalTheory.RawLift.exists_hecke_resEta D T.rank
  ⟨χS, χT, exists_weil hψ S T a1 b1 a2 b2⟩

theorem nonempty_step {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (V V₀ W W₀ : HSp D) (ρ σ : ℕ)
    (hV : V.rank % 2 = V₀.rank % 2) (hW : W.rank % 2 = W₀.rank % 2) : Nonempty (Step ψ V V₀ W W₀ ρ σ) := by
  obtain ⟨χV, a1, a2⟩ := GlobalTheory.RawLift.exists_hecke_resEta D V.rank
  obtain ⟨χW, b1, b2⟩ := GlobalTheory.RawLift.exists_hecke_resEta D W.rank
  obtain ⟨om, h⟩ := exists_weil hψ V W a1 b1 a2 b2
  obtain ⟨om₀, h₀⟩ := exists_weil hψ V₀ W₀ a1 b1 (resEta_parity a2 hV) (resEta_parity b2 hW)
  obtain ⟨vW⟩ := nonempty_vol W
  obtain ⟨vS⟩ := nonempty_volM D W.rank ρ
  obtain ⟨vT⟩ := nonempty_volM D σ V₀.rank
  obtain ⟨vU⟩ := nonempty_volU D ρ
  exact ⟨⟨χV, χW, om, om₀, h, h₀, vW, vS, vT, vU⟩⟩

theorem even_im_hermitian_sub {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) : S.rank % 2 = S₀.rank % 2 := by
  have := d.rank_add
  omega

theorem nonempty_stepBF {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {ρ : ℕ} (B : BesLev D ρ) (J : JacLev D ρ) :
    Nonempty (StepBF ψ B J) :=
  nonempty_step hψ _ _ _ _ _ _ (even_im_hermitian_sub B.d) (even_im_hermitian_sub J.d)

theorem nonempty_stepFB {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {σ : ℕ} (J : JacLev D (σ + 1))
    (B : BesLev D σ) : Nonempty (StepFB ψ J B) :=
  nonempty_step hψ _ _ _ _ _ _ (even_im_hermitian_sub J.d) (even_im_hermitian_sub B.d)

theorem cmHost_imaginaryGenerator_ne_zero (D : D7) : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D

def selfLink {ρ : ℕ} (B : BesLev D ρ) : Link B B.L (D.host.xi0⁻¹ • B.ζ) where
  τ := -(D.host.xi0 • (1 : Matrix (Fin B.L.rank) (Fin B.L.rank) D.host.E))
  map := by
    rw [neg_mulVec, smul_mulVec, one_mulVec, smul_smul, mul_inv_cancel₀ (cmHost_imaginaryGenerator_ne_zero D), one_smul]
  norm := by
    have h := cmHost_imaginaryGenerator_ne_zero D
    have h' : star D.host.xi0 ≠ 0 := star_ne_zero.2 h
    rw [star_smul, mulVec_smul, dotProduct_smul, smul_dotProduct, star_inv₀, smul_eq_mul, smul_eq_mul]
    field_simp

def hypRefl (S : HSp D) : HypDec S S 0 where
  e := 0
  e' := 0
  i₀ := 1
  ee := by ext i; exact i.elim0
  e'e' := by ext i; exact i.elim0
  e'e := by ext i; exact i.elim0
  iso := by rw [conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  i₀e := by ext i j; exact j.elim0
  i₀e' := by ext i j; exact j.elim0
  rank_add := rfl

abbrev posLine (D : D7) : HSp D := diagSp D 1 ![false] 1 0

abbrev negLine (D : D7) : HSp D := diagSp D 1 ![true] 0 1

abbrev plane (D : D7) : HSp D := diagSp D 2 ![false, true] 1 1

theorem posDef_posLine (D : D7) (τ : D.what₂.Tau) : (gramAt D (posLine D) τ).PosDef := by
  have h : gramAt D (posLine D) τ = 1 := by
    rw [gramAt, diagSp_gram]
    ext i j
    rw [Subsingleton.elim (α := Fin 1) i j, Subsingleton.elim (α := Fin 1) j (0 : Fin 1)]
    exact (congrArg (tauE D τ) (Matrix.diagonal_apply_eq _ _)).trans ((map_one (tauE D τ)).trans (Matrix.one_apply_eq _).symm)
  rw [h]
  exact Matrix.PosDef.one

theorem coCpt_posLine (D : D7) : CoCpt (posLine D) := coCpt_of_posDef (posDef_posLine D)

theorem isLineVec_negLine {c : D.host.E} (hc : c ≠ 0) : IsLineVec (negLine D) (fun _ => c) := by
  refine ⟨rfl, ?_⟩
  rw [diagSp_gram]
  change ∑ i : Fin 1, star c * ∑ j : Fin 1, Matrix.diagonal (fun i => Examples₂.sgn (![true] i)) i j * c ≠ 0
  simp [Examples₂.sgn, hc]

def besPlane {V : HSp D} {ρ : ℕ} (d : HypDec V (plane D) ρ) {c : D.host.E} (hc : c ≠ 0) : BesLev D ρ where
  V := V
  V₀ := plane D
  A := posLine D
  L := negLine D
  d := d
  o := orthDecPlane D
  ζ := fun _ => c
  line := isLineVec_negLine hc
  cpt := coCpt_posLine D
  vA := (nonempty_vol _).some
  vN := (nonempty_volN d).some

def jacLine {W : HSp D} {ρ : ℕ} (d : HypDec W (posLine D) ρ) : JacLev D ρ where
  W := W
  W₀ := posLine D
  d := d
  cpt := coCpt_posLine D
  v0 := (nonempty_vol _).some
  vN := (nonempty_volN d).some

theorem exists_last {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (B : BesLev D 0) (J : JacLev D 0)
    (hJ : CoCpt J.W) {T : HSp D} (hT : CoCpt T) : ∃ t : Last ψ T B, t.J = J := by
  obtain ⟨s⟩ := nonempty_stepBF hψ B J
  obtain ⟨χS, χT, om, h⟩ := exists_weil_pair hψ J.W T
  obtain ⟨vT⟩ := nonempty_vol T
  exact ⟨⟨J, s, hJ, hT, χS, χT, om, h, vT⟩, rfl⟩

noncomputable def AllNonzero {ψ : AddChar (AF D.host.F) ℂ} {T : HSp D} :
    {ρ : ℕ} → {B : BesLev D ρ} → (c : Chain ψ T ρ B) → c.Data → Prop
  | _, _, .last _, Φ => Φ.1 ≠ 0 ∧ Φ.2 ≠ 0
  | _, _, .step _ _ _ _ _ _ c, Φ => Φ.1 ≠ 0 ∧ Φ.2.1 ≠ 0 ∧ AllNonzero c Φ.2.2

noncomputable def CoresPos {ψ : AddChar (AF D.host.F) ℂ} {T : HSp D} : {ρ : ℕ} → {B : BesLev D ρ} → Chain ψ T ρ B → Prop
  | _, _, .last t => 0 < t.J.W₀.rank
  | _, _B, .step J B' _ _ _ _ c => 0 < J.W₀.rank ∧ 0 < B'.A.rank ∧ CoresPos c

theorem exists_data {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {T : HSp D} {ρ : ℕ} {B : BesLev D ρ}
    (c : Chain ψ T ρ B) : ∃ Φ : c.Data, c.IsTheta Φ ∧ AllNonzero c Φ := by
  induction c with
  | @last B t =>
    obtain ⟨f, hf, f0⟩ := GlobalTheory.Mem.ThetaNonzero.exists_thetaO_ne_zero hψ B.V t.J.W
    obtain ⟨g, hg, g0⟩ := GlobalTheory.Mem.ThetaNonzero.exists_thetaO_ne_zero hψ t.J.W T
    exact ⟨(f, g), ⟨hf, hg⟩, f0, g0⟩
  | @step σ B J B' s₁ s₂ l vL c ih =>
    obtain ⟨f, hf, f0⟩ := GlobalTheory.Mem.ThetaNonzero.exists_thetaO_ne_zero hψ B.V J.W
    obtain ⟨g, hg, g0⟩ := GlobalTheory.Mem.ThetaNonzero.exists_thetaO_ne_zero hψ J.W B'.V
    obtain ⟨Φ, h, h0⟩ := ih
    exact ⟨(f, g, Φ), ⟨hf, hg, h⟩, f0, g0, h0⟩

theorem exists_chain_of_isStdChar {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) :
    ∃ (T : HSp D) (B : BesLev D 1) (c : Chain ψ T 1 B), 0 < B.A.rank ∧ 0 < T.rank ∧ CoresPos c ∧
      ∃ Φ : c.Data, c.IsTheta Φ ∧ AllNonzero c Φ := by
  let B : BesLev D 1 := besPlane (GlobalTheory.RegSW.Model.hypFour D) (cmHost_imaginaryGenerator_ne_zero D)
  let J : JacLev D 1 := jacLine (hypDecThree D)
  let B' : BesLev D 0 := besPlane (hypRefl (plane D)) one_ne_zero
  obtain ⟨t, ht⟩ := exists_last hψ B' (jacLine (hypRefl (posLine D))) (coCpt_posLine D) (coCpt_posLine D)
  obtain ⟨s₁⟩ := nonempty_stepBF hψ B J
  obtain ⟨s₂⟩ := nonempty_stepFB (σ := 0) hψ J B'
  have e : D.host.xi0⁻¹ • B.ζ = B'.ζ := funext fun _ => inv_mul_cancel₀ (cmHost_imaginaryGenerator_ne_zero D)
  have l : Link B B.L B'.ζ := e ▸ selfLink B
  obtain ⟨vL⟩ := nonempty_volM D B'.L.rank J.W₀.rank
  refine ⟨posLine D, B, .step J B' s₁ s₂ l vL (.last t), Nat.one_pos, Nat.one_pos, ⟨Nat.one_pos, Nat.one_pos, ?_⟩,
    exists_data hψ _⟩
  show 0 < t.J.W₀.rank
  rw [ht]
  exact Nat.one_pos

theorem isThetaFam_om {ψ : AddChar (AF D.host.F) ℂ} {S L : HSp D} {χS χL : (AE D)ˣ →* Circle} {om : Om S L}
    (hom : IsWeilDatumO ψ S L χS χL om) {Φ₀ : WO S L → ℂ} (hΦ : IsThetaFunO ψ S L Φ₀) :
    IsThetaFam ψ S L fun h => om (h, 1) Φ₀ where
  theta h := hom.om_pres _ _ hΦ
  cont := (GlobalTheory.ThetaJointCont.continuous_om_oriented hom hΦ).comp
    ((continuous_fst.prodMk continuous_const).prodMk continuous_snd)
  left γ hγ h w := by
    have h1 : ∀ V : HSp D, Formalism.L2.Theta.mt V 1 = 1 := fun V => by simp [Formalism.L2.Theta.mt]
    have e : actO S L γ 1 (w ⬝ Formalism.L2.Theta.mt S γ) = w := by
      rw [actO, h1, Matrix.one_mul, Matrix.mul_assoc, ← mt_mul, mul_inv_cancel, h1, Matrix.mul_one]
    have e' : ((γ * h, 1) : GA D S × GA D L) = (γ, 1) * (h, 1) := by simp
    rw [e', map_mul, Module.End.mul_apply,
      ← GlobalTheory.WeilRat.om_rat_actO D ψ hom.std S L χS χL om hom γ hγ 1 (one_mem _) _ (hom.om_pres _ _ hΦ) (w ⬝ Formalism.L2.Theta.mt S γ), e]

theorem exists_isThetaFam {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S L : HSp D) :
    ∃ Y, IsThetaFam ψ S L Y ∧ ∀ h, Y h ≠ 0 := by
  obtain ⟨χS, χL, om, hom⟩ := exists_weil_pair hψ S L
  obtain ⟨f, hf, f0⟩ := GlobalTheory.Mem.ThetaNonzero.exists_thetaO_ne_zero hψ S L
  refine ⟨_, isThetaFam_om hom hf, fun h h0 => f0 ?_⟩
  have : om (h, 1)⁻¹ (om (h, 1) f) = f := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [← this, show om (h, 1) f = 0 from h0, map_zero]

theorem exists_chain (D : D7) : (∃ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1)) ∧
    ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) →
      (∃ (T : HSp D) (B : BesLev D 1) (c : Chain ψ T 1 B), 0 < B.A.rank ∧ 0 < T.rank ∧ CoresPos c ∧
        ∃ Φ : c.Data, c.IsTheta Φ ∧ AllNonzero c Φ) ∧
      ∀ S L : HSp D, ∃ Y, IsThetaFam ψ S L Y ∧ ∀ h, Y h ≠ 0 :=
  ⟨(GlobalTheory.Ker.exists_infFam_and_stdChar D).2, fun _ hψ => ⟨exists_chain_of_isStdChar hψ, exists_isThetaFam hψ⟩⟩

end GlobalTheory.Unf.Inhab

end
