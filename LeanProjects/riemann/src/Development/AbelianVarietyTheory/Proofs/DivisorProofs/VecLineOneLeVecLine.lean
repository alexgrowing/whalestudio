import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinResidueHolomorphicRegion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightInvariantUnderStabilizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinSettingHeightContinuous
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineReps
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.EisUnfold

open GlobalTheory.EisMidHt (adVec)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

omit [NumberField E] in
theorem inv_mulVec_cancel (p : GAd σ J) (y : Fin n → AF F ⊗[F] E) :
    (matHom _ σ J p⁻¹).1 *ᵥ (matHom _ σ J p).1 *ᵥ y = y := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mulVec]

def vecStab (z : Fin n → AF F ⊗[F] E) (H : Subgroup (AF F ⊗[F] E)ˣ) : Subgroup (GAd σ J) where
  carrier := {p | ∃ l ∈ H, (matHom _ σ J p).1 *ᵥ z = l.1 • z}
  one_mem' := ⟨1, one_mem _, by simp⟩
  mul_mem' := by
    rintro p q ⟨l, hl, e⟩ ⟨l', hl', e'⟩
    refine ⟨l * l', mul_mem hl hl', ?_⟩
    rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, e', Matrix.mulVec_smul, e, smul_smul, Units.val_mul, mul_comm]
  inv_mem' := by
    rintro p ⟨l, hl, e⟩
    refine ⟨l⁻¹, inv_mem hl, ?_⟩
    have h := inv_mulVec_cancel σ J p z
    rw [e, Matrix.mulVec_smul] at h
    conv_rhs => rw [← h, smul_smul, Units.inv_mul, one_smul]

def vecFix (z : Fin n → AF F ⊗[F] E) : Subgroup (GAd σ J) := vecStab σ J z ⊥

def vecLine (z : Fin n → AF F ⊗[F] E) : Subgroup (GAd σ J) := vecStab σ J z ⊤

def vecLineOne (z : Fin n → AF F ⊗[F] E) : Subgroup (GAd σ J) := vecStab σ J z (absE F E).ker

variable {σ J}

omit [NumberField E] in
theorem mem_vecFix {z : Fin n → AF F ⊗[F] E} {p : GAd σ J} : p ∈ vecFix σ J z ↔ (matHom _ σ J p).1 *ᵥ z = z :=
  ⟨fun ⟨l, hl, e⟩ => by rw [e, Subgroup.mem_bot.1 hl, Units.val_one, one_smul], fun e => ⟨1, one_mem _, by simpa using e⟩⟩

omit [NumberField E] in
theorem mem_vecLine {z : Fin n → AF F ⊗[F] E} {p : GAd σ J} :
    p ∈ vecLine σ J z ↔ ∃ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J p).1 *ᵥ z = l.1 • z :=
  ⟨fun ⟨l, _, e⟩ => ⟨l, e⟩, fun ⟨l, e⟩ => ⟨l, trivial, e⟩⟩

theorem mem_vecLineOne {z : Fin n → AF F ⊗[F] E} {p : GAd σ J} :
    p ∈ vecLineOne σ J z ↔ ∃ l : (AF F ⊗[F] E)ˣ, absE F E l = 1 ∧ (matHom _ σ J p).1 *ᵥ z = l.1 • z := Iff.rfl

theorem vecFix_le_vecLineOne (z : Fin n → AF F ⊗[F] E) : vecFix σ J z ≤ vecLineOne σ J z :=
  fun _ ⟨l, hl, e⟩ => ⟨l, bot_le (a := (absE F E).ker) hl, e⟩

theorem vecLineOne_le_vecLine (z : Fin n → AF F ⊗[F] E) : vecLineOne σ J z ≤ vecLine σ J z :=
  fun _ ⟨l, _, e⟩ => ⟨l, trivial, e⟩

omit [NumberField E] in

theorem conj_mem_vecStab {z : Fin n → AF F ⊗[F] E} {H : Subgroup (AF F ⊗[F] E)ˣ} {p q : GAd σ J} (hp : p ∈ vecLine σ J z)
    (hq : q ∈ vecStab σ J z H) : p * q * p⁻¹ ∈ vecStab σ J z H := by
  obtain ⟨l, -, e⟩ := hp
  obtain ⟨l', -, e'⟩ := inv_mem (show p ∈ vecLine σ J z from ⟨l, trivial, e⟩)
  obtain ⟨k, hk, ek⟩ := hq
  refine ⟨k, hk, ?_⟩
  have h := inv_mulVec_cancel σ J p⁻¹ z
  rw [inv_inv] at h
  rw [map_mul, map_mul, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e', Matrix.mulVec_smul, ek,
    smul_comm, ← e', Matrix.mulVec_smul, h]

omit [NumberField E] in

theorem conj_mem_vecStab_iff {z w : Fin n → AF F ⊗[F] E} {H : Subgroup (AF F ⊗[F] E)ˣ} {γ p : GAd σ J} {c : (AF F ⊗[F] E)ˣ}
    (e : (matHom _ σ J γ).1 *ᵥ z = c.1 • w) : γ⁻¹ * p * γ ∈ vecStab σ J z H ↔ p ∈ vecStab σ J w H := by
  refine exists_congr fun l => and_congr_right fun _ => ?_
  have h := inv_mulVec_cancel σ J γ⁻¹
  rw [inv_inv] at h
  rw [map_mul, map_mul, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e]
  constructor
  · intro h1
    have h2 := congrArg ((matHom _ σ J γ).1 *ᵥ ·) h1
    simp only [h, Matrix.mulVec_smul, e] at h2
    rw [smul_comm] at h2
    exact (c.isUnit.smul_left_cancel).1 h2
  · intro h1
    rw [Matrix.mulVec_smul, h1, smul_comm, ← e, Matrix.mulVec_smul, inv_mulVec_cancel]

theorem isClosed_vecFix (z : Fin n → AF F ⊗[F] E) : IsClosed (vecFix σ J z : Set (GAd σ J)) := by
  obtain ⟨_, _⟩ := GlobalTheory.StdPar.ring_facts (F := F) (E := E)
  have : (vecFix σ J z : Set (GAd σ J)) = {p | (matHom _ σ J p).1 *ᵥ z = z} := Set.ext fun _ => mem_vecFix
  exact this ▸ isClosed_eq (GlobalTheory.StdPar.continuous_mat.matrix_mulVec continuous_const) continuous_const

def IsStart {r : ℕ} (S : Finset (Fin r)) (j : Fin r) : Prop := j.val = 0 ∨ ∃ k ∈ S, k.val + 1 = j.val

def IsStdVec {r : ℕ} (X Y : Matrix (Fin n) (Fin r) E) (S : Finset (Fin r)) (z : Fin n → E) : Prop :=
  (∃ j, IsStart S j ∧ z = Xᵀ j) ∨ ∃ j ∈ S, z = Yᵀ j

example {r : ℕ} (X Y : Matrix (Fin n) (Fin (r + 1)) E) (S : Finset (Fin (r + 1))) : IsStdVec X Y S (Xᵀ 0) :=
  Or.inl ⟨0, Or.inl rfl, rfl⟩

omit [NumberField E] in
theorem col0_eq_iff {r : ℕ} {X : Matrix (Fin n) (Fin (r + 1)) E} {m : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)} {l : AF F ⊗[F] E} :
    m * adMat F (col0 X) = l • adMat F (col0 X) ↔ m *ᵥ adVec F (Xᵀ 0) = l • adVec F (Xᵀ 0) :=
  ⟨fun h => funext fun i => congrFun (congrFun h i) 0, fun h => Matrix.ext fun i _ => congrFun h i⟩

variable (σ J) in

abbrev Lines {r : ℕ} (X : Matrix (Fin n) (Fin (r + 1)) E) : Type := ratPts σ J ⧸ lineStab σ J (col0 X)

def term {r : ℕ} (X : Matrix (Fin n) (Fin (r + 1)) E) (h : GAd σ J → ℝ) (e : ℂ) (q : Lines σ J X) (g : GAd σ J) : ℂ :=
  (h ((q.out : ratPts σ J).1⁻¹ * g) : ℂ) ^ e

theorem mem_lineStab_iff {r : ℕ} {X : Matrix (Fin n) (Fin (r + 1)) E} {γ : ratPts σ J} :
    γ ∈ lineStab σ J (col0 X) ↔ γ.1 ∈ vecLine σ J (adVec F (Xᵀ 0)) :=
  (exists_congr fun _ => col0_eq_iff).trans mem_vecLine.symm

theorem smul_mk_eq_iff {r : ℕ} {X : Matrix (Fin n) (Fin (r + 1)) E} {γ δ : ratPts σ J} {w : Fin n → AF F ⊗[F] E}
    {c : (AF F ⊗[F] E)ˣ} (e : (matHom _ σ J γ.1).1 *ᵥ adVec F (Xᵀ 0) = c.1 • w) :
    δ • (γ : Lines σ J X) = γ ↔ δ.1 ∈ vecLine σ J w := by
  rw [eq_comm, MulAction.Quotient.smul_coe, QuotientGroup.eq, mem_lineStab_iff, smul_eq_mul, ← mul_assoc]
  exact conj_mem_vecStab_iff e

section HidaSetting

variable {r : ℕ} {X Y : Matrix (Fin n) (Fin (r + 1)) E} {L : Submodule (𝓞 E) (Fin n → E)} {a : GL (Fin n) (AF F ⊗[F] E)}
  {h : GAd σ J → ℝ} (hS : HidaSetting σ J X Y L a h)
include hS

theorem ht_mul_left {p : GAd σ J} (hp : p ∈ vecLineOne σ J (adVec F (Xᵀ 0))) (g : GAd σ J) : h (p * g) = h g := by
  obtain ⟨l, hl, e⟩ := mem_vecLineOne.1 hp
  obtain ⟨p', l', e', k, hk, rfl⟩ := hS.2.2.2.2.2.2.1 g
  rw [← mul_assoc, hS.2.2.2.2.2.2.2 p' l' e' k hk, hS.2.2.2.2.2.2.2 (p * p') (l * l') ?_ k hk, map_mul, hl, one_mul]
  rw [map_mul, Units.val_mul, Matrix.mul_assoc, e', Matrix.mul_smul, col0_eq_iff.2 e, smul_smul, Units.val_mul, mul_comm]

theorem ht_pos (g : GAd σ J) : 0 < h g := by
  obtain ⟨p, l, e, k, hk, rfl⟩ := hS.2.2.2.2.2.2.1 g
  rw [hS.2.2.2.2.2.2.2 p l e k hk]
  exact_mod_cast GlobalTheory.Doubling.hom_pos _ l

theorem term_mk (e : ℂ) (γ : ratPts σ J) (g : GAd σ J) : term X h e (γ : Lines σ J X) g = (h (γ.1⁻¹ * g) : ℂ) ^ e := by
  obtain ⟨p, hp⟩ := QuotientGroup.mk_out_eq_mul (lineStab σ J (col0 X)) γ
  rw [term, hp, Subgroup.coe_mul, mul_inv_rev, mul_assoc]
  exact congrArg (fun x : ℝ => (x : ℂ) ^ e) (GlobalTheory.EisCT.iwaHt_mul_rat_stabL F E σ n J r X Y L a h hS _ (p⁻¹).1.2 (p⁻¹).2 _)

theorem term_smul (e : ℂ) (γ : ratPts σ J) (q : Lines σ J X) (g : GAd σ J) : term X h e (γ • q) (γ.1 * g) = term X h e q g := by
  induction q using QuotientGroup.induction_on with
  | H δ => rw [MulAction.Quotient.smul_coe, term_mk hS, term_mk hS, smul_eq_mul, Subgroup.coe_mul, mul_inv_rev, mul_assoc,
      inv_mul_cancel_left]

theorem continuous_term (e : ℂ) (q : Lines σ J X) : Continuous (term X h e q) :=
  (Complex.continuous_ofReal.comp ((HtCont.continuous_iwaHt F E σ n J r X Y L a h hS).comp (continuous_mul_left _))).cpow
    continuous_const fun _ => Complex.ofReal_mem_slitPlane.2 (ht_pos hS _)

theorem term_mul_left (e : ℂ) {γ : ratPts σ J} {w : Fin n → AF F ⊗[F] E} {c : (AF F ⊗[F] E)ˣ}
    (hγ : (matHom _ σ J γ.1).1 *ᵥ adVec F (Xᵀ 0) = c.1 • w) {p : GAd σ J} (hp : p ∈ vecLineOne σ J w) (g : GAd σ J) :
    term X h e (γ : Lines σ J X) (p * g) = term X h e (γ : Lines σ J X) g := by
  rw [term_mk hS, term_mk hS, ← ht_mul_left hS ((conj_mem_vecStab_iff hγ).2 hp) (γ.1⁻¹ * g)]
  simp only [mul_assoc, mul_inv_cancel_left]

theorem norm_term (e : ℂ) (q : Lines σ J X) (g : GAd σ J) : ‖term X h e q g‖ = h ((q.out : ratPts σ J).1⁻¹ * g) ^ e.re :=
  Complex.norm_cpow_eq_rpow_re_of_pos (ht_pos hS _) e

end HidaSetting

theorem hasSum_term {r : ℕ} {X : Matrix (Fin n) (Fin (r + 1)) E} {h : GAd σ J → ℝ} {Eis : ℂ → GAd σ J → ℂ}
    (hE : IsSerG σ J (col0 X) h Eis) {s : ℂ} (hs : ((n : ℝ) - 1) / 2 < s.re) (g : GAd σ J) :
    HasSum (fun q : Lines σ J X => term X h (s + ((n : ℂ) - 1) / 2) q g) (Eis s g) := by
  let f : Lines σ J X → ratPts σ J := fun q => (q.out)⁻¹
  have hf : Function.Injective f := fun q q' e => Quotient.out_injective (inv_injective e)
  have := hE (Set.range f) (fun γ => ⟨f (γ⁻¹ : ratPts σ J), ⟨⟨_, rfl⟩, ?_⟩, ?_⟩) s hs g
  · exact (Equiv.ofInjective f hf).hasSum_iff.2 this
  · obtain ⟨p, hp⟩ := QuotientGroup.mk_out_eq_mul (lineStab σ J (col0 X)) γ⁻¹
    have : γ * (f (γ⁻¹ : ratPts σ J))⁻¹ = p := by simp only [f, inv_inv, hp, mul_inv_cancel_left]
    rw [this]
    exact p.2
  · rintro _ ⟨⟨q, rfl⟩, ht⟩
    refine congrArg f ?_
    rw [← QuotientGroup.out_eq' q, eq_comm, QuotientGroup.eq, inv_inv]
    simp only [f, inv_inv] at ht
    exact ht

end GlobalTheory.EisUnfold

end
