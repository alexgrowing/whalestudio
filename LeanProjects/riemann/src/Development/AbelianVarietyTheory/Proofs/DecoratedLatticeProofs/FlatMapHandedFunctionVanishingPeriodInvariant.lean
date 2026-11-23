import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentAnisotropicProjectionEqOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentBesselCharacterLaws
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsSatisfyFlatLawsFinitePlacesStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MixModel MeasureTheory Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 200000

namespace GlobalTheory.FlatRInv

variable {D : D7}

theorem addChar_ne_zero {A : Type} [AddGroup A] (ψ : AddChar A ℂ) (a : A) : ψ a ≠ 0 := by
  intro h
  have := ψ.map_add_eq_mul a (-a)
  rw [add_neg_cancel, ψ.map_zero_eq_one, h, zero_mul] at this
  exact one_ne_zero this

theorem mem_congGrp_iff (V : HSp D) (I : Ideal (AE D)) (g : GA D V) :
    g ∈ congGrp V I ↔ (mt V g).map (Ideal.Quotient.mk I) = 1 := by
  unfold congGrp
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Units.ext_iff]
  rfl

theorem unitaryMatrix_wittCoreEmbedding {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (h : GA D S₀) :
    mt S (d.emb0 h) = d.jX ⬝ d.pX + d.j0 ⬝ mt S₀ h ⬝ d.p0 + d.jY ⬝ d.pY := by
  conv_lhs => rw [← Matrix.mul_one (mt S (d.emb0 h)), ← d.sum_eq_one]
  simp only [Matrix.mul_add, ← Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclX, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, d.wittDecomp_anisotropicEmbedding_inclY]

theorem wittCoreEmbedding_preserves_supportedUnitarySubgroup {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (P : Pl D → Prop) {h : GA D S₀}
    (hh : h ∈ grpAt S₀ P) : d.emb0 h ∈ grpAt S P := by
  rw [grpAt, mem_congGrp_iff] at hh ⊢
  have key : (mt S (d.emb0 h)).map (Ideal.Quotient.mk (idAt D P)) =
      (d.jX ⬝ d.pX + d.j0 ⬝ d.p0 + d.jY ⬝ d.pY).map (Ideal.Quotient.mk (idAt D P)) := by
    have hadd : ∀ A B : Matrix (Fin S.rank) (Fin S.rank) (AE D), (A + B).map (Ideal.Quotient.mk (idAt D P)) =
        A.map (Ideal.Quotient.mk (idAt D P)) + B.map (Ideal.Quotient.mk (idAt D P)) :=
      fun A B => Matrix.map_add _ (Ideal.Quotient.mk (idAt D P)).map_add A B
    rw [unitaryMatrix_wittCoreEmbedding]; simp only [hadd, Matrix.map_mul, hh, Matrix.mul_one]
  rw [key, d.sum_eq_one]; exact Matrix.map_one _ (Ideal.Quotient.mk (idAt D P)).map_zero (Ideal.Quotient.mk (idAt D P)).map_one

theorem comp_mem_grpAt {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (P : Pl D → Prop) {n : GA D S}
    (hn : n ∈ flagN d) {h : GA D S₀} (hr : n * d.emb0 h ∈ grpAt S P) : h ∈ grpAt S₀ P := by
  rw [grpAt, mem_congGrp_iff] at hr ⊢
  rw [← GlobalTheory.BesClosed.witt_anisotropic_block_flag_mul_embedded d hn h]
  simp only [Matrix.map_mul, hr, Matrix.one_mul]
  rw [← Matrix.map_mul, d.p0_j0]; exact Matrix.map_one _ (Ideal.Quotient.mk (idAt D P)).map_zero (Ideal.Quotient.mk (idAt D P)).map_one

theorem jac_decomp {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (P : Pl D → Prop) {r : GA D S}
    (hr : r ∈ jacGrp d) (hP : r ∈ grpAt S P) :
    ∃ n ∈ flagN d, n ∈ grpAt S P ∧ ∃ h ∈ grpAt S₀ P, r = n * d.emb0 h := by
  obtain ⟨n, hn, h, rfl⟩ := (GlobalTheory.MixPer.Decomp.mem_jacGrp_iff d).1 hr
  have hh := comp_mem_grpAt d P hn hP
  refine ⟨n, hn, ?_, h, hh, rfl⟩
  have e : n = n * d.emb0 h * (d.emb0 h)⁻¹ := by group
  rw [e]; exact mul_mem hP (inv_mem (wittCoreEmbedding_preserves_supportedUnitarySubgroup d P hh))

theorem heisO_eq_zero_iff (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w₀ : WO S T) (F : WO S T → ℂ) :
    heisO ψ S T w₀ F = 0 ↔ F = 0 := by
  constructor
  · intro h; funext w
    have := congrFun h (w - w₀)
    simp only [heisO, Pi.zero_apply, sub_add_cancel] at this
    exact (mul_eq_zero.1 this).resolve_left (addChar_ne_zero ψ _)
  · rintro rfl; funext w; simp [heisO]

theorem om_eq_zero_iff {S T : HSp D} (om : Om S T) (g : GA D S × GA D T) (F : WO S T → ℂ) :
    om g F = 0 ↔ F = 0 := by
  constructor
  · intro h0
    have e : om g⁻¹ (om g F) = F := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [← e, h0, map_zero]
  · rintro rfl; exact map_zero _

theorem orth_comp_mem {S₀ A L : HSp D} (o : OrthDec S₀ A L) (P : Pl D → Prop) {h : GA D A}
    (hh : o.emb (h, 1) ∈ grpAt S₀ P) : h ∈ grpAt A P := by
  rw [grpAt, mem_congGrp_iff] at hh ⊢
  have e : mt A h = o.pA ⬝ mt S₀ (o.emb (h, 1)) ⬝ o.jA := by
    rw [o.pA_emb, Matrix.mul_assoc, o.pA_jA, Matrix.mul_one]
  rw [e, Matrix.map_mul, Matrix.map_mul, hh, Matrix.mul_one, ← Matrix.map_mul, o.pA_jA]
  exact Matrix.map_one _ (Ideal.Quotient.mk (idAt D P)).map_zero (Ideal.Quotient.mk (idAt D P)).map_one

theorem bes_decomp {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) (P : Pl D → Prop)
    {r : GA D S} (hr : r ∈ besGrp d o) (hP : r ∈ grpAt S P) :
    ∃ n ∈ flagN d, n ∈ grpAt S P ∧ ∃ h ∈ grpAt A P, r = n * embA d o h := by
  obtain ⟨n, hn, h, rfl⟩ := (GlobalTheory.CharLaws.mem_besGrp d o r).1 hr
  have hP' : n * d.emb0 (o.emb (h, 1)) ∈ grpAt S P := by rwa [embA_apply] at hP
  have h0 := comp_mem_grpAt d P hn hP'
  refine ⟨n, hn, ?_, h, orth_comp_mem o P h0, rfl⟩
  have e : n = n * embA d o h * (embA d o h)⁻¹ := by group
  rw [e]; exact mul_mem hP (inv_mem (wittCoreEmbedding_preserves_supportedUnitarySubgroup d P h0))

theorem opA_eq_zero_iff (ψ : AddChar (AF D.host.F) ℂ) {W W₀ V₀ A L : HSp D} {ρ : ℕ} (dW : HypDec W W₀ ρ)
    (o : OrthDec V₀ A L) (ζ : Fin L.rank → D.host.E) (om : Om V₀ W₀) (n : GA D W) (h : GA D W₀)
    (Ξ : WO V₀ W₀ → ℂ) : opA ψ dW o ζ om n h Ξ = 0 ↔ Ξ = 0 := by
  unfold opA jacT
  rw [smul_eq_zero_iff_right (addChar_ne_zero ψ _), heisO_eq_zero_iff, om_eq_zero_iff]

theorem handFB_smul_om_at {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {J : JacLev D (σ + 1)} {B : BesLev D σ}
    (s : StepFB ψ J B) (vL : VolM D B.L.rank J.W₀.rank) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (Ξ : WO J.W₀ B.V₀ → ℂ)
    (c : ℂ) (h₁ g : GA D B.A) :
    handFB s vL Y (c • s.om₀ (1, B.o.emb (h₁, 1)) Ξ) g = c * handFB s vL Y Ξ (g * h₁) := by
  unfold handFB
  rw [← integral_const_mul]
  congr 1
  funext h₀
  have e : s.om₀ (h₀, B.o.emb (g, 1)) (c • s.om₀ (1, B.o.emb (h₁, 1)) Ξ) = c • s.om₀ (h₀, B.o.emb (g * h₁, 1)) Ξ := by
    rw [map_smul, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, ← map_mul, Prod.mk_mul_mk]
    simp only [mul_one]
  unfold pairKer
  rw [e]
  simp only [contractT, thPair, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  funext w
  ring

theorem vanish_invariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (P : Pl D → Prop), (∀ (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (f : WO B.V J.W → ℂ), IsThetaFunO ψ B.V J.W f → ∀ r ∈ jacGrp J.d, r ∈ grpAt J.W P → (flatBF s (s.om (1, r) f) = 0 ↔ flatBF s f = 0)) ∧ ∀ (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B) (vL : VolM D B.L.rank J.W₀.rank) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (f : WO J.W B.V → ℂ), IsThetaFunO ψ J.W B.V f → ∀ r ∈ besGrp B.d B.o, r ∈ grpAt B.V P → (handFB s vL Y (flatFB s (s.om (1, r) f)) = 0 ↔ handFB s vL Y (flatFB s f) = 0) := by
  intro D ψ P
  have hL := GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D ψ P
  refine ⟨fun ρ B J s f hf r hr hrP => ?_, fun σ J B s vL Y f hf r hr hrP => ?_⟩
  · obtain ⟨n, hn, hnP, h, hh, rfl⟩ := jac_decomp J.d P hr hrP
    rw [(hL.1 ρ B J s).equiv f hf n hn hnP h hh]
    have hc : star (psiFlag ψ J.d n) ≠ 0 := star_ne_zero.2 (by unfold psiFlag psiE; exact addChar_ne_zero ψ _)
    rw [smul_eq_zero_iff_right hc, opA_eq_zero_iff]
  · obtain ⟨n, hn, hnP, h, hh, rfl⟩ := bes_decomp B.d B.o P hr hrP
    rw [(hL.2 σ J B s).equiv f hf n hn hnP h hh]
    have hc : star (psiBes ψ B.d 1 (vecB B.o B.ζ) n) ≠ 0 :=
      star_ne_zero.2 (by unfold psiBes psiE; exact addChar_ne_zero ψ _)
    constructor
    · intro h0; funext g
      have := congrFun h0 (g * h⁻¹)
      rw [handFB_smul_om_at, inv_mul_cancel_right, Pi.zero_apply] at this
      exact (mul_eq_zero.1 this).resolve_left hc
    · intro h0; funext g
      rw [handFB_smul_om_at, h0, Pi.zero_apply, Pi.zero_apply, mul_zero]

end GlobalTheory.FlatRInv
