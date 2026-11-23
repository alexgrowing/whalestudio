import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpanRationalTranslatesVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApplyAt0Smul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunctionRationalTranslateMemStatement

noncomputable section

open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField Polynomial
open scoped Pointwise nonZeroDivisors
open Formalism.L2.Host (HChar embTau)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

namespace GlobalTheory.FunObj.CosetTheta

variable {D : D7}

theorem conj_ne_bot {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) : D.host.conj • 𝔪 ≠ ⊥ := by
  intro h
  apply h𝔪
  have := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h
  simpa [inv_smul_smul] using this

theorem mul_mem_one {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) {y : D.host.E}
    (hy : y ∈ (((𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) /
      ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :
        FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) D.host.E)) :
    ((Ideal.absNorm (D.host.conj • 𝔪) : ℕ) : D.host.E) * y ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  have hJ : ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (conj_ne_bot h𝔪)
  rw [FractionalIdeal.coe_div hJ, Submodule.mem_div_iff_forall_mul_mem] at hy
  have hn : ((Ideal.absNorm (D.host.conj • 𝔪) : ℕ) : D.host.E) ∈
      ((((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)) :
        Submodule (𝓞 D.host.E) D.host.E) := by
    rw [FractionalIdeal.coe_coeIdeal, IsLocalization.mem_coeSubmodule]
    exact ⟨_, Ideal.absNorm_mem _, by simp⟩
  have h2 := hy _ hn
  rw [FractionalIdeal.coe_coeIdeal, IsLocalization.mem_coeSubmodule] at h2
  obtain ⟨z, -, hz⟩ := h2
  rw [Submodule.mem_one]
  exact ⟨z, by rw [hz, mul_comm]⟩

theorem nsmul_mem_homL {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) {a d : ℕ} {A : Matrix (Fin d) (Fin a) D.host.E}
    (hA : A ∈ homL D (stdL D a) (skewLat D 𝔪 d)) :
    Ideal.absNorm (D.host.conj • 𝔪) • A ∈ homL D (stdL D a) (stdL D d) := by
  induction hA using Submodule.span_induction with
  | mem A hA =>
    apply Submodule.subset_span
    intro x hx
    have h := hA x hx
    rw [skewLat, Submodule.mem_pi] at h
    rw [stdL, Submodule.mem_pi]
    intro i _
    rw [Matrix.smul_mulVec, Pi.smul_apply, nsmul_eq_mul]
    exact mul_mem_one h𝔪 (h i trivial)
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul c x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ c hx

theorem nsmul_mem_YYl {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) {a d : ℕ} {B : Matrix (Fin d) (Fin a) D.host.E}
    (hB : B ∈ YYl D (stdL D a) (skewLat D 𝔪 d)) :
    Ideal.absNorm (D.host.conj • 𝔪) • B ∈ YYl D (stdL D a) (stdL D d) := by
  induction hB using Submodule.span_induction with
  | mem B hB =>
    obtain ⟨c, hc, A, hA, rfl⟩ := hB
    apply Submodule.subset_span
    exact ⟨c, hc, _, nsmul_mem_homL h𝔪 hA, smul_comm _ _ _⟩
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul c x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ c hx

theorem absNormConj_smul_mem_stdThetaLattice {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {a d : ℕ}
    {x : VC D a d} (hx : x ∈ La D (tor0 D cc δ) (stdL D a) (skewLat D 𝔪 d)) :
    Ideal.absNorm (D.host.conj • 𝔪) • x ∈ La0 D (tor0 D cc δ) a d := by
  induction hx using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨w, hw, A, hA, rfl⟩ := hz
    apply AddSubgroup.subset_closure
    refine ⟨w, hw, _, nsmul_mem_YYl h𝔪 hA, ?_⟩
    funext τ i j
    simp only [embV, tor0, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul, map_mul, map_natCast]
    ring
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem u_mem_TT {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hc : Crv D cc δ) {N N' : ℕ} {x : VC D N N'} {M : ℕ}
    (hM : 0 < M) (hx : M • x ∈ La0 D (tor0 D cc δ) N N') {F : VC D N N' → ℂ} (hF : F ∈ TT D (tor0 D cc δ) N N') :
    U D (tor0 D cc δ) x F ∈ TT D (tor0 D cc δ) N N' := by
  have hw : wdPh D (tor0 D cc δ) x ≠ 0 := by simp [wdPh, ee, Complex.exp_ne_zero]
  have e : U D (tor0 D cc δ) x F = (wdPh D (tor0 D cc δ) x)⁻¹ • Wd D (tor0 D cc δ) x F := by
    funext z
    simp only [Wd, Pi.smul_apply, smul_eq_mul]
    rw [inv_mul_cancel_left₀ hw]
  rw [e]
  exact NormUniq.tt_smul (GlobalTheory.T.thetaFunction_rationalTranslate_mem hc hM hx hF) _

theorem iop_mem_TT {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hc : Crv D cc δ) {N N' : ℕ} {La₂ : AddSubgroup (VC D N N')}
    {M : ℕ} (hM : 0 < M) (hLa : ∀ x ∈ La₂, M • x ∈ La0 D (tor0 D cc δ) N N') {F : VC D N N' → ℂ}
    (hF : F ∈ TT D (tor0 D cc δ) N N') :
    Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') La₂ F ∈ TT D (tor0 D cc δ) N N' := by
  classical
  by_cases h : ((La0 D (tor0 D cc δ) N N').addSubgroupOf La₂).index = 0
  · have e : Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') La₂ F = 0 := by
      funext z
      simp [Iop, h]
    rw [e]
    exact NormUniq.tt_zero _
  · have : ((La0 D (tor0 D cc δ) N N').addSubgroupOf La₂).FiniteIndex := ⟨h⟩
    haveI : Fintype (La₂ ⧸ (La0 D (tor0 D cc δ) N N').addSubgroupOf La₂) := Fintype.ofFinite _
    have e : Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') La₂ F =
        ((Real.sqrt (((La0 D (tor0 D cc δ) N N').addSubgroupOf La₂).index : ℝ))⁻¹ : ℂ) •
          ∑ q : La₂ ⧸ (La0 D (tor0 D cc δ) N N').addSubgroupOf La₂,
            al D (tor0 D cc δ) ((Quotient.out q : La₂) : VC D N N') •
              U D (tor0 D cc δ) ((Quotient.out q : La₂) : VC D N N') F := by
      funext z
      simp only [Iop, finsum_eq_sum_of_fintype, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    rw [e]
    exact NormUniq.tt_smul (NormUniq.tt_sum _ fun q _ =>
      NormUniq.tt_smul (u_mem_TT hc hM (hLa _ (Quotient.out q : La₂).2) hF) _) _

theorem cosetVec_mem_TT : ∀ {D : D7} {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) {𝔪 : Ideal (𝓞 D.host.E)}, 𝔪 ≠ ⊥ →
    ∀ o : ℕ, cosetVec P 𝔪 o ∈ TT D (tor0 D ⊤ δ) P.a P.d := by
  intro D δ t0 Q P 𝔪 h𝔪 o
  have h1 := (GlobalTheory.InducedType.induced_type D).1
  have he : P.e0 ∈ TT D (tor0 D ⊤ δ) P.a P.d := VacMove.vac_TT h1 P.crv P.vac.1
  have hM : 0 < Ideal.absNorm (D.host.conj • 𝔪) :=
    Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact conj_ne_bot h𝔪)
  have hI := iop_mem_TT P.crv hM (fun x hx => absNormConj_smul_mem_stdThetaLattice h𝔪 hx) he
  unfold cosetVec
  exact NormUniq.tt_smul (GlobalTheory.T.thetaFunction_rationalTranslate_mem P.crv one_pos
    (by rw [one_smul]; exact pt_unitBlock_mem δ o P.a P.d) hI) _

end GlobalTheory.FunObj.CosetTheta
