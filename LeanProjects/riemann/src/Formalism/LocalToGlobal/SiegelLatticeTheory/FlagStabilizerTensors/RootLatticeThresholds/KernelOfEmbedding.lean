import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ParametersTermRelations

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.PackageTie2

namespace Formalism.L2.SG.Pf.KernelOfEmbedding

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section HS

variable {Wq Wp : Type*} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

def cl (U : Wq ≃ₗᵢ[ℂ] Wq) : Wq →L[ℂ] Wq := U.toLinearIsometry.toContinuousLinearMap

theorem cl_apply (U : Wq ≃ₗᵢ[ℂ] Wq) (x : Wq) : cl U x = U x := rfl

theorem sum_inner_eq_trace {ι : Type*} [Fintype ι] (f : OrthonormalBasis ι ℂ Wq) (A B : Wq →L[ℂ] Wp) :
    ∑ i, inner ℂ (B (f i)) (A (f i)) =
      LinearMap.trace ℂ Wq (((ContinuousLinearMap.adjoint B).comp A : Wq →L[ℂ] Wq) : Wq →ₗ[ℂ] Wq) := by
  rw [LinearMap.trace_eq_sum_inner _ f]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [ContinuousLinearMap.adjoint_inner_right]

theorem hsInner_comp_isom (A B : Wq →L[ℂ] Wp) (U : Wq ≃ₗᵢ[ℂ] Wq) :
    Formalism.MainNotions.S.hsInner (A.comp (cl U)) (B.comp (cl U)) = Formalism.MainNotions.S.hsInner A B := by
  unfold Formalism.MainNotions.S.hsInner
  calc ∑ i, inner ℂ ((B.comp (cl U)) (stdOrthonormalBasis ℂ Wq i)) ((A.comp (cl U)) (stdOrthonormalBasis ℂ Wq i))
      = ∑ i, inner ℂ (B (((stdOrthonormalBasis ℂ Wq).map U) i)) (A (((stdOrthonormalBasis ℂ Wq).map U) i)) := by
        simp [OrthonormalBasis.map_apply, cl_apply]
    _ = _ := sum_inner_eq_trace _ A B
    _ = ∑ i, inner ℂ (B (stdOrthonormalBasis ℂ Wq i)) (A (stdOrthonormalBasis ℂ Wq i)) :=
        (sum_inner_eq_trace _ A B).symm

theorem hsInner_smul_left (c : ℂ) (A B : Wq →L[ℂ] Wp) :
    Formalism.MainNotions.S.hsInner (c • A) B = c * Formalism.MainNotions.S.hsInner A B := by
  unfold Formalism.MainNotions.S.hsInner
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

theorem hsInner_smul_right (c : ℂ) (A B : Wq →L[ℂ] Wp) :
    Formalism.MainNotions.S.hsInner A (c • B) = (starRingEnd ℂ) c * Formalism.MainNotions.S.hsInner A B := by
  unfold Formalism.MainNotions.S.hsInner
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp
  ring

theorem hsInner_form (J₁ J₂ : Wq →L[ℂ] Wp) (c₁ c₂ : ℂ) (U₁ U₂ : Wq ≃ₗᵢ[ℂ] Wq) :
    Formalism.MainNotions.S.hsInner (c₁ • J₁.comp (cl U₁)) (c₂ • J₂.comp (cl U₂)) =
      c₁ * (starRingEnd ℂ) c₂ * Formalism.MainNotions.S.hsInner (J₁.comp (cl (U₂.symm.trans U₁))) J₂ := by
  have h : J₁.comp (cl U₁) = (J₁.comp (cl (U₂.symm.trans U₁))).comp (cl U₂) := by
    ext x
    simp [cl_apply]
  rw [hsInner_smul_left, hsInner_smul_right, h, hsInner_comp_isom]
  ring

theorem hsInner_eq_emb {Wq' Wp' : Type} [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq']
    [NormedAddCommGroup Wp'] [InnerProductSpace ℂ Wp'] (A B : Wq' →L[ℂ] Wp') :
    Formalism.MainNotions.S.hsInner A B = inner ℂ (Formalism.L2.SG.PackageTie.hsEmb B) (Formalism.L2.SG.PackageTie.hsEmb A) := by
  unfold Formalism.MainNotions.S.hsInner
  simp [Formalism.L2.SG.PackageTie.hsEmb, PiLp.inner_apply]

end HS

section Stmt

variable {D : D7} {X : HidaSetting D} (Y : Formalism.L2.SG.Full.Full X)

abbrev amp {u u' : D.what₂.Word} (s : TT Y u u') : X.Vpi u' →L[ℂ] X.Vpi u :=
  ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') s

abbrev row {u u' : D.what₂.Word} (s : TT Y u u') :=
  rowOf Y.TR (Y.cs u) (Y.cs u') s

def AmpCov : Prop :=
  ∀ (u u' : D.what₂.Word) (t : RT Y u u') (s s' : fib Y t),
    ∃ (c : ℂ) (U : X.Vpi u' ≃ₗᵢ[ℂ] X.Vpi u'), ‖c‖ = 1 ∧ amp Y s'.1 = c • (amp Y s.1).comp (cl U)

def PairAmpConst : Prop :=
  ∀ (u u' : D.what₂.Word) (t₁ t₂ : RT Y u u') (r r' : fib Y t₁ × fib Y t₂),
    row Y r.1.1 = row Y r.2.1 → row Y r'.1.1 = row Y r'.2.1 →
      Formalism.MainNotions.S.hsInner (amp Y r.1.1) (amp Y r.2.1) = Formalism.MainNotions.S.hsInner (amp Y r'.1.1) (amp Y r'.2.1)

variable {Y} in

def FibreCountEq (hF : FinX Y) : Prop :=
  ∀ (u u' : D.what₂.Word) (q : RP Y u u'),
    haveI := hF.fibFT q.1.1
    haveI := hF.fibFT q.1.2
    ∑ r : fib Y q.1.1 × fib Y q.1.2,
      (if row Y r.1.1 = row Y r.2.1 then Formalism.MainNotions.S.wRow D (X.Fu u') r.1.1.lam' else 0) = 1

end Stmt

section Val

variable {D : D7} {X : HidaSetting D} {Y : Formalism.L2.SG.Full.Full X}

theorem wRow_nonneg {T : D.host.E} (F0 : Formalism.MainNotions.S.FlagG (Formalism.MainNotions.S.VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (Formalism.MainNotions.S.VS D).V) :
    0 ≤ Formalism.MainNotions.S.wRow D F0 Λ := by
  unfold Formalism.MainNotions.S.wRow; exact inv_nonneg.2 (Nat.cast_nonneg _)

theorem lam_eq_of_row {u u' : D.what₂.Word} {s₁ s₂ : TT Y u u'} (h : row Y s₁ = row Y s₂) :
    s₁.lam = s₂.lam ∧ s₁.lam' = s₂.lam' := by
  unfold row rowOf at h
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
  exact ⟨h.1, h.2.1⟩

theorem inner_vT {u u' : D.what₂.Word} (s₁ s₂ : TT Y u u') (h : row Y s₁ = row Y s₂) :
    inner ℂ (vT Y u u' s₂) (vT Y u u' s₁) =
      ((Formalism.MainNotions.S.wRow D (X.Fu u) s₁.lam * Formalism.MainNotions.S.wRow D (X.Fu u') s₁.lam' : ℝ) : ℂ) *
        Formalism.MainNotions.S.hsInner (amp Y s₁) (amp Y s₂) := by
  obtain ⟨hl, hl'⟩ := lam_eq_of_row h
  have hposition : ((⟨s₂.lam, s₂.mem⟩ : {Λ // Λ ∈ Y.what₂ u}), (⟨s₂.lam', s₂.mem'⟩ : {Λ' // Λ' ∈ Y.what₂ u'})) =
      (⟨s₁.lam, s₁.mem⟩, ⟨s₁.lam', s₁.mem'⟩) := by
    simp [hl, hl']
  have hwt : wt s₂ = wt s₁ := by unfold wt; rw [hl, hl']
  have hw2 : wt s₁ * wt s₁ = Formalism.MainNotions.S.wRow D (X.Fu u) s₁.lam * Formalism.MainNotions.S.wRow D (X.Fu u') s₁.lam' :=
    Real.mul_self_sqrt (mul_nonneg (wRow_nonneg _ _) (wRow_nonneg _ _))
  unfold vT vec
  rw [PiLp.inner_apply, Finset.sum_eq_single (⟨s₁.lam, s₁.mem⟩, ⟨s₁.lam', s₁.mem'⟩)]
  · simp only [if_true, hposition, hwt]
    rw [inner_smul_left, inner_smul_right, ← Formalism.L2.SG.Pf.KernelOfEmbedding.hsInner_eq_emb, ← hw2]
    simp only [Complex.conj_ofReal, Complex.ofReal_mul]
    ring
  · intro b _ hb
    simp [hb]
  · intro hb; exact absurd (Finset.mem_univ _) hb

theorem pvR_eq (hF : FinX Y) (hK : PairAmpConst Y) (hN : FibreCountEq hF) {u u' : D.what₂.Word} (q : RP Y u u') :
    pvR hF u u' q = (Formalism.MainNotions.S.wRow D (X.Fu u) q.1.1.lam : ℂ) * Formalism.MainNotions.S.hsInner (amp Y q.l1) (amp Y q.l2) := by
  have key : ∀ r : fib Y q.1.1 × fib Y q.1.2,
      (if rowOf Y.TR (Y.cs u) (Y.cs u') r.1.1 = rowOf Y.TR (Y.cs u) (Y.cs u') r.2.1 then
        inner ℂ (vT Y u u' r.2.1) (vT Y u u' r.1.1) else 0) =
        (Formalism.MainNotions.S.wRow D (X.Fu u) q.1.1.lam : ℂ) * Formalism.MainNotions.S.hsInner (amp Y q.l1) (amp Y q.l2) *
          (((if row Y r.1.1 = row Y r.2.1 then Formalism.MainNotions.S.wRow D (X.Fu u') r.1.1.lam' else 0 : ℝ)) : ℂ) := by
    intro r
    by_cases hr : row Y r.1.1 = row Y r.2.1
    · have hlam : r.1.1.lam = q.1.1.lam := congrArg TermDef.Term.lam r.1.2
      have hc := hK u u' q.1.1 q.1.2 r (q.2.choose, q.2.choose_spec.choose) hr q.2.choose_spec.choose_spec
      rw [if_pos hr, if_pos hr, inner_vT _ _ hr, hc, hlam]
      simp only [RP.l1, RP.l2, Complex.ofReal_mul]
      ring
    · rw [if_neg hr, if_neg hr]
      simp
  unfold pvR
  rw [Finset.sum_congr rfl fun r _ => key r, ← Finset.mul_sum, ← Complex.ofReal_sum]
  have hn := hN u u' q
  rw [hn]
  simp

theorem pvR_form (hF : FinX Y) (hC : AmpCov Y) (hK : PairAmpConst Y) (hN : FibreCountEq hF) {u u' : D.what₂.Word}
    (q : RP Y u u') (g₁ : fib Y q.1.1) (g₂ : fib Y q.1.2) :
    ∃ (c : ℂ) (U : X.Vpi u' ≃ₗᵢ[ℂ] X.Vpi u'), ‖c‖ = 1 ∧
      pvR hF u u' q = (Formalism.MainNotions.S.wRow D (X.Fu u) q.1.1.lam : ℂ) * c *
        Formalism.MainNotions.S.hsInner ((amp Y g₁.1).comp (cl U)) (amp Y g₂.1) := by
  obtain ⟨c₁, U₁, hc₁, h₁⟩ := hC u u' q.1.1 g₁ q.2.choose
  obtain ⟨c₂, U₂, hc₂, h₂⟩ := hC u u' q.1.2 g₂ q.2.choose_spec.choose
  refine ⟨c₁ * (starRingEnd ℂ) c₂, U₂.symm.trans U₁, by simp [hc₁, hc₂], ?_⟩
  rw [pvR_eq hF hK hN q]
  show _ * Formalism.MainNotions.S.hsInner (amp Y q.2.choose.1) (amp Y q.2.choose_spec.choose.1) = _
  rw [h₁, h₂, hsInner_form]
  ring

end Val

end Formalism.L2.SG.Pf.KernelOfEmbedding
