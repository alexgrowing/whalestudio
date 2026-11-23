import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConeRepresentatives
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousCA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaStabilizerExists

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ConeSmallMeas

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem mat_mul (a b : UA σ J) : mat (a * b) = mat a * mat b := rfl

theorem mat_one : mat (1 : UA σ J) = 1 := rfl

theorem continuous_mat : Continuous (mat : UA σ J → Matrix (Fin n) (Fin n) (AE F E)) :=
  Units.continuous_val.comp continuous_subtype_val

theorem mulVec_inv_of (p : UA σ J) (v : Fin n → AE F E) (l : (AE F E)ˣ) (hl : mat p *ᵥ v = l.1 • v) :
    mat p⁻¹ *ᵥ v = (l⁻¹).1 • v := by
  have h : mat p⁻¹ *ᵥ (mat p *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, ← mat_mul, inv_mul_cancel, mat_one, Matrix.one_mulVec]
  rw [hl, Matrix.mulVec_smul] at h
  calc mat p⁻¹ *ᵥ v = (l⁻¹).1 • l.1 • (mat p⁻¹ *ᵥ v) := by
        rw [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
    _ = (l⁻¹).1 • v := by rw [h]

variable (σ J) in

def lineStab (x : Fin n → E) : Subgroup (UA σ J) where
  carrier := {p | ∃ l : (AE F E)ˣ, mat p *ᵥ incV F x = l.1 • incV F x}
  one_mem' := ⟨1, by rw [mat_one, Matrix.one_mulVec, Units.val_one, one_smul]⟩
  mul_mem' := by
    rintro a b ⟨l, hl⟩ ⟨l', hl'⟩
    refine ⟨l' * l, ?_⟩
    rw [mat_mul, ← Matrix.mulVec_mulVec, hl', Matrix.mulVec_smul, hl, smul_smul, Units.val_mul]
  inv_mem' := by
    rintro a ⟨l, hl⟩
    exact ⟨l⁻¹, mulVec_inv_of a _ l hl⟩

def cf (x : Fin n → E) (i : Fin n) (p : UA σ J) : AE F E :=
  (mat p *ᵥ incV F x) i * inclR (F := F) (AF F) (x i)⁻¹

theorem incV_mul_inv (x : Fin n → E) {i : Fin n} (hxi : x i ≠ 0) :
    incV F x i * inclR (F := F) (AF F) (x i)⁻¹ = 1 := by
  rw [incV, ← map_mul, mul_inv_cancel₀ hxi, map_one]

theorem cf_eq (x : Fin n → E) {i : Fin n} (hxi : x i ≠ 0) (p : UA σ J) (l : AE F E)
    (hl : mat p *ᵥ incV F x = l • incV F x) : cf x i p = l := by
  rw [cf, hl, Pi.smul_apply, smul_eq_mul, mul_assoc, incV_mul_inv x hxi, mul_one]

theorem continuous_cf (x : Fin n → E) (i : Fin n) : Continuous (cf (σ := σ) (J := J) x i) := by
  haveI := (GlobalTheory.LeviModulus.topAE F E).1
  exact ((continuous_apply i).comp (continuous_mat.matrix_mulVec continuous_const)).mul continuous_const

def lP (x : Fin n → E) {i : Fin n} (hxi : x i ≠ 0) (p : lineStab σ J x) : (AE F E)ˣ where
  val := cf x i p.1
  inv := cf x i p.1⁻¹
  val_inv := by
    obtain ⟨l, hl⟩ := p.2
    rw [cf_eq x hxi _ _ hl, cf_eq x hxi _ _ (mulVec_inv_of _ _ l hl), ← Units.val_mul, mul_inv_cancel, Units.val_one]
  inv_val := by
    obtain ⟨l, hl⟩ := p.2
    rw [cf_eq x hxi _ _ hl, cf_eq x hxi _ _ (mulVec_inv_of _ _ l hl), ← Units.val_mul, inv_mul_cancel, Units.val_one]

theorem localPart_spec (x : Fin n → E) {i : Fin n} (hxi : x i ≠ 0) (p : lineStab σ J x) :
    mat p.1 *ᵥ incV F x = (lP x hxi p).1 • incV F x := by
  obtain ⟨l, hl⟩ := p.2
  show _ = cf x i p.1 • _
  rw [cf_eq x hxi _ _ hl, hl]

theorem continuous_lP (x : Fin n → E) {i : Fin n} (hxi : x i ≠ 0) : Continuous (lP (σ := σ) (J := J) x hxi) :=
  haveI := (GlobalTheory.LeviModulus.topUA σ J).1
  Units.continuous_iff.2 ⟨(continuous_cf x i).comp continuous_subtype_val,
    (continuous_cf x i).comp (continuous_inv.comp continuous_subtype_val)⟩

theorem isClosed_lineStab (x : Fin n → E) {i : Fin n} (hxi : x i ≠ 0) :
    IsClosed (lineStab σ J x : Set (UA σ J)) := by
  haveI := (GlobalTheory.LeviModulus.topAE F E).1
  haveI := (GlobalTheory.LeviModulus.topAE F E).2.2.2
  have e : (lineStab σ J x : Set (UA σ J)) =
      ⋂ j, {p | (mat p *ᵥ incV F x) j * incV F x i = (mat p *ᵥ incV F x) i * incV F x j} := by
    ext p
    simp only [Set.mem_iInter, Set.mem_setOf_eq, SetLike.mem_coe]
    constructor
    · rintro ⟨l, hl⟩ j
      rw [hl, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
      ring
    · intro h
      have key : mat p *ᵥ incV F x = cf x i p • incV F x := by
        funext j
        rw [Pi.smul_apply, smul_eq_mul, cf]
        calc (mat p *ᵥ incV F x) j
            = (mat p *ᵥ incV F x) j * (incV F x i * inclR (F := F) (AF F) (x i)⁻¹) := by
              rw [incV_mul_inv x hxi, mul_one]
          _ = ((mat p *ᵥ incV F x) j * incV F x i) * inclR (F := F) (AF F) (x i)⁻¹ := by ring
          _ = ((mat p *ᵥ incV F x) i * incV F x j) * inclR (F := F) (AF F) (x i)⁻¹ := by rw [h j]
          _ = _ := by ring
      have h2 : incV F x = cf x i p • (mat p⁻¹ *ᵥ incV F x) := by
        have h3 : mat p⁻¹ *ᵥ (mat p *ᵥ incV F x) = incV F x := by
          rw [Matrix.mulVec_mulVec, ← mat_mul, inv_mul_cancel, mat_one, Matrix.one_mulVec]
        rw [key, Matrix.mulVec_smul] at h3
        exact h3.symm
      have hu : cf x i p * cf x i p⁻¹ = 1 := by
        have h4 := congrFun h2 i
        rw [Pi.smul_apply, smul_eq_mul] at h4
        have e5 : cf x i p⁻¹ = (mat p⁻¹ *ᵥ incV F x) i * inclR (F := F) (AF F) (x i)⁻¹ := rfl
        rw [e5, ← mul_assoc, ← h4, incV_mul_inv x hxi]
      exact ⟨⟨cf x i p, cf x i p⁻¹, hu, by rw [mul_comm, hu]⟩, key⟩
  rw [e]
  exact isClosed_iInter fun j => isClosed_eq
    (((continuous_apply j).comp (continuous_mat.matrix_mulVec continuous_const)).mul continuous_const)
    (((continuous_apply i).comp (continuous_mat.matrix_mulVec continuous_const)).mul continuous_const)

theorem continuous_ht (K : Subgroup (UA σ J)) (hK : IsCompact (K : Set (UA σ J))) (x : Fin n → E) (hf : UA σ J → ℝ)
    (hiw : GlobalTheory.ConeSmall.IsIwaHt K x hf)
    (hdec : ∀ g, ∃ (p k : UA σ J) (l : (AE F E)ˣ), k ∈ K ∧ mat p *ᵥ incV F x = l.1 • incV F x ∧ g = p * k) :
    Continuous hf := by
  haveI := (GlobalTheory.LeviModulus.topUA σ J).1
  by_cases hx : ∃ i, x i ≠ 0
  · obtain ⟨i, hxi⟩ := hx
    refine GlobalTheory.Doubling.continuous_of_prod (K := K) (P := lineStab σ J x) (isClosed_lineStab x hxi) hK ?_ ?_
    · intro g
      obtain ⟨p, k, l, hk, hl, rfl⟩ := hdec g
      exact ⟨⟨p, l, hl⟩, k, hk, rfl⟩
    · have e : (fun y : lineStab σ J x × K => hf (y.1.1 * y.2.1)) =
          fun y => ((absE F E (lP x hxi y.1) : ℝ≥0) : ℝ) := funext fun y =>
        hiw y.1.1 y.2.1 (lP x hxi y.1) y.2.2 (localPart_spec x hxi y.1)
      rw [e]
      exact NNReal.continuous_coe.comp (GlobalTheory.Doubling.continuous_absE.comp ((continuous_lP x hxi).comp continuous_fst))
  · push_neg at hx
    have hw : incV F x = 0 := funext fun i => by rw [incV, hx i, map_zero, Pi.zero_apply]
    have e : hf = fun _ => 1 := funext fun g => by
      have := hiw g 1 1 (one_mem K) (by rw [hw, Matrix.mulVec_zero, smul_zero])
      rw [mul_one, map_one] at this
      exact this.trans NNReal.coe_one
    rw [e]
    exact continuous_const

theorem eis_measurable : GlobalTheory.ThK.KP → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E) {n : ℕ} (X : Spc F E n) (r s' : ℕ), B.IsGood σ → X.IsHerm σ B r s' →
    ∀ K : Subgroup (UA σ X.J), IsStab B K → ∀ (x : Fin n → E) (Eis : ℂ → UA σ X.J → ℂ), GlobalTheory.ConeSmall.IsEisSer K x Eis →
    ∀ s : ℂ, ((n : ℝ) - 1) / 2 < s.re → Measurable (Eis s) := by
  intro hKP F E _ _ _ _ _ σ B n X r s' hB hX K hK x Eis hE s hs
  obtain ⟨hf, hiw, hdec, hsum⟩ := hE
  obtain ⟨K', -, -, hK'stab, hK'cpt, -, -⟩ := GlobalTheory.StabHaar.stabEx hKP.base F E σ B n X r s' hB hX
  have hKK : K = K' := Subgroup.ext fun g => (hK g).trans (hK'stab g).symm
  subst hKK
  have hcont : Continuous hf := continuous_ht K hK'cpt x hf hiw hdec
  obtain ⟨T, hTsub, hT⟩ := GlobalTheory.ConeSmallCT.exists_isReps F E σ n X.J x
  haveI hR := GlobalTheory.UnitaryVol.countable_ratU σ X.J
  haveI : Countable T := Set.Countable.to_subtype ((Set.countable_coe_iff.1 hR).mono hTsub)
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  haveI := (GlobalTheory.LeviModulus.topUA σ X.J).1
  refine measurable_of_tendsto_metrizable' atTop
    (f := fun S : Finset T => fun g => ∑ t ∈ S, ((hf (t.1 * g) : ℝ) : ℂ) ^ (s + ((n : ℂ) - 1) / 2))
    (fun S => ?_) (tendsto_pi_nhds.2 fun g => hsum T hTsub hT s hs g)
  exact Finset.measurable_sum _ fun t _ =>
    (Complex.measurable_ofReal.comp (hcont.comp (continuous_const.mul continuous_id)).measurable).pow_const _

end GlobalTheory.ConeSmallMeas
