import Formalism.HermitianCurvature.CompositeFormulaLevelZero

open scoped ComplexConjugate ContDiff
open Filter Topology

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd

theorem fsv_mul_fsv_neg (s t : ℂ) : fsv s t * fsv (-s) t = 1 := by
  rw [fsv, fsv, ← Complex.exp_add]
  convert Complex.exp_zero using 2
  simp only [map_neg]
  ring

theorem fsv_neg_mul_fsv (s t : ℂ) : fsv (-s) t * fsv s t = 1 := by
  rw [mul_comm]
  exact fsv_mul_fsv_neg s t

theorem hasFDerivAt_fsv {m : ℕ} (t : ℂ) (l : Fin m) (c : Fin m → ℂ) :
    ∃ D : (Fin m → ℂ) →L[ℝ] ℂ, HasFDerivAt (fun c' : Fin m → ℂ => fsv t (c' l)) D c ∧
      D (Pi.single l 1) = (t - conj t) * fsv t (c l) ∧
      D (Pi.single l Complex.I) = Complex.I * (t + conj t) * fsv t (c l) := by
  classical
  let L : (Fin m → ℂ) →L[ℝ] ℂ := t • (ContinuousLinearMap.proj l : (Fin m → ℂ) →L[ℝ] ℂ) -
    (conj t) • (Complex.conjCLE.toContinuousLinearMap.comp (ContinuousLinearMap.proj l : (Fin m → ℂ) →L[ℝ] ℂ))
  have hL : ∀ c' : Fin m → ℂ, L c' = t * c' l - conj t * conj (c' l) := by
    intro c'
    simp [L]
  refine ⟨fsv t (c l) • L, ?_, ?_, ?_⟩
  · have h2 := (L.hasFDerivAt (x := c)).cexp
    have he : (fun c' : Fin m → ℂ => fsv t (c' l)) = fun c' => Complex.exp (L c') := by
      funext c'
      rw [hL]
      rfl
    have hc : Complex.exp (L c) = fsv t (c l) := by
      rw [hL]
      rfl
    rw [he, ← hc]
    exact h2
  · simp only [ContinuousLinearMap.smul_apply, hL, Pi.single_eq_same, map_one, smul_eq_mul]
    ring
  · simp only [ContinuousLinearMap.smul_apply, hL, Pi.single_eq_same, Complex.conj_I, smul_eq_mul]
    ring

section Leibniz

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem wirt_fsv_smul (t : ℂ) (l : Fin m) (φ : (Fin m → ℂ) → E) (c : Fin m → ℂ)
    (hφ : DifferentiableAt ℝ φ c) :
    wirt l (fun c' => fsv t (c' l) • φ c') c = fsv t (c l) • wirt l φ c + (t * fsv t (c l)) • φ c ∧
    wirtBar l (fun c' => fsv t (c' l) • φ c') c =
      fsv t (c l) • wirtBar l φ c + (-(conj t) * fsv t (c l)) • φ c := by
  obtain ⟨D, hD, h1, hI⟩ := hasFDerivAt_fsv t l c
  have hP : HasFDerivAt (fun c' => fsv t (c' l) • φ c') (fsv t (c l) • fderiv ℝ φ c + D.smulRight (φ c)) c :=
    hD.smul hφ.hasFDerivAt
  unfold wirt wirtBar
  rw [hP.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, h1, hI, smul_add, smul_sub, smul_smul, ← mul_assoc, Complex.I_mul_I]
  constructor <;> module

theorem pOp_fsv_smul (t : ℂ) (l : Fin m) (φ : (Fin m → ℂ) → E) (c : Fin m → ℂ)
    (hd : c ∈ OmX m → DifferentiableAt ℝ φ c) (h0 : c ∉ OmX m → φ c = 0) :
    pOp l (fun c' => fsv t (c' l) • φ c') c =
      fsv t (c l) • pOp l φ c + t • fsv t (c l) • (c l • φ c) := by
  unfold pOp
  by_cases h : c ∈ OmX m
  · rw [if_pos h, if_pos h, (wirt_fsv_smul t l φ c (hd h)).1]
    module
  · rw [if_neg h, if_neg h, h0 h]
    simp

theorem pbOp_fsv_smul (t : ℂ) (l : Fin m) (φ : (Fin m → ℂ) → E) (c : Fin m → ℂ)
    (hd : c ∈ OmX m → DifferentiableAt ℝ φ c) (h0 : c ∉ OmX m → φ c = 0) :
    pbOp l (fun c' => fsv (-t) (c' l) • φ c') c =
      fsv (-t) (c l) • pbOp l φ c + conj t • fsv (-t) (c l) • (star (c l) • φ c) := by
  unfold pbOp
  by_cases h : c ∈ OmX m
  · rw [if_pos h, if_pos h, (wirt_fsv_smul (-t) l φ c (hd h)).2]
    simp only [map_neg, neg_neg, Complex.star_def]
    module
  · rw [if_neg h, if_neg h, h0 h]
    simp

end Leibniz

section Reg

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
  [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem radSp_regular (Φ : RadSp k r z z' π π') (g : Mx k r) (c : Fin r → ℂ) :
    (c ∈ OmX r → DifferentiableAt ℝ (fun c' => (Φ : Fn k r (Wq →L[ℂ] Wp)) c' g) c) ∧
      (c ∉ OmX r → (Φ : Fn k r (Wq →L[ℂ] Wp)) c g = 0) := by
  have hΦm : (Φ : Fn k r (Wq →L[ℂ] Wp)) ∈ RadSp k r z z' π π' := Φ.2
  obtain ⟨h0, hs, -⟩ := hΦm
  refine ⟨fun hc => ?_, fun hc => h0 (c, g) (fun hx => hc (by
    simp only [DomR, Set.mem_setOf_eq] at hx
    exact hx.1))⟩
  by_cases hg : g ∈ Glev k r (Fin.last r) ∧ 0 < GGl k r z z' g
  · obtain ⟨U, F, hU, hxU, hF, hΦ⟩ := hs (c, g) (by
      simp only [DomR, Set.mem_setOf_eq]
      exact ⟨hc, hg.1, hg.2⟩)
    have hcont : Continuous (fun c' : Fin r → ℂ => (c', g)) := by fun_prop
    have hev : ∀ᶠ c' in nhds c, (Φ : Fn k r (Wq →L[ℂ] Wp)) c' g = F (c', g) := by
      have hU' : ∀ᶠ c' in nhds c, (c', g) ∈ U := hcont.continuousAt.preimage_mem_nhds (hU.mem_nhds hxU)
      filter_upwards [hU'] with c' hc'
      exact hΦ (c', g) hc' hg.1
    have hFd : DifferentiableAt ℝ F (c, g) := (hF.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)
    have hpair : DifferentiableAt ℝ (fun c' : Fin r → ℂ => (c', g)) c := by fun_prop
    have hcomp : DifferentiableAt ℝ (fun c' => F (c', g)) c := hFd.comp c hpair
    exact hcomp.congr_of_eventuallyEq hev
  · have hz : (fun c' => (Φ : Fn k r (Wq →L[ℂ] Wp)) c' g) = fun _ => 0 := by
      funext c'
      refine h0 (c', g) (fun hx => hg ?_)
      simp only [DomR, Set.mem_setOf_eq] at hx
      exact ⟨hx.2.1, hx.2.2⟩
    rw [hz]
    exact differentiableAt_const 0

end Reg

section PairLemmas

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem pr_ext {a b : Pr V} (h1 : a.1 = b.1) (h2 : a.2.unop = b.2.unop) : a = b :=
  Prod.ext h1 (MulOpposite.unop_injective h2)

@[simp] theorem mkPair_fst' (X Xs : Module.End ℂ V) : (mkP X Xs : Pr V).1 = X := rfl
@[simp] theorem mkPair_snd' (X Xs : Module.End ℂ V) : (mkP X Xs : Pr V).2.unop = Xs := rfl
@[simp] theorem pr_mul_fst (a b : Pr V) : (a * b).1 = a.1 * b.1 := rfl
@[simp] theorem pr_mul_snd (a b : Pr V) : (a * b).2.unop = b.2.unop * a.2.unop := rfl
@[simp] theorem pr_add_fst (a b : Pr V) : (a + b).1 = a.1 + b.1 := rfl
@[simp] theorem pr_add_snd (a b : Pr V) : (a + b).2.unop = a.2.unop + b.2.unop := rfl
@[simp] theorem pr_one_fst : (1 : Pr V).1 = 1 := rfl
@[simp] theorem pr_one_snd : (1 : Pr V).2.unop = 1 := rfl
@[simp] theorem pr_alg_fst (w : ℂ) : (algebraMap ℂ (Pr V) w).1 = algebraMap ℂ (Module.End ℂ V) w := rfl
@[simp] theorem pr_alg_snd (w : ℂ) :
    (algebraMap ℂ (Pr V) w).2.unop = algebraMap ℂ (Module.End ℂ V) (conj w) := rfl

end PairLemmas

theorem waveSiteAll : WaveSiteAll := by
  intro Wp Wq _ _ _ _ P z z' π π' X L hL l s Wv Wv' hW hW'
  obtain ⟨hp, -, hc, hci, -⟩ := hL
  have hW1 : ∀ (Φ : RadSp P.k P.r z z' π π') c g, (Wv Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g =
      fsv s (c l) • (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g := hW
  have hW2 : ∀ (Φ : RadSp P.k P.r z z' π π') c g, (Wv' Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g =
      fsv (-s) (c l) • (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g := hW'
  have hop : ∀ i (Φ : RadSp P.k P.r z z' π π'),
      (X.op l i Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) = crd (opL l i) (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) :=
    fun i Φ => X.op_apply l i Φ
  have hWW' : Wv * Wv' = 1 := by
    apply LinearMap.ext; intro Φ; apply Subtype.ext; funext c g
    simp only [Module.End.mul_apply, Module.End.one_apply, hW1, hW2, smul_smul, fsv_mul_fsv_neg, one_smul]
  have hW'W : Wv' * Wv = 1 := by
    apply LinearMap.ext; intro Φ; apply Subtype.ext; funext c g
    simp only [Module.End.mul_apply, Module.End.one_apply, hW1, hW2, smul_smul, fsv_neg_mul_fsv, one_smul]

  have hcomm : ∀ (W : Module.End ℂ (RadSp P.k P.r z z' π π')) (u : ℂ → ℂ),
      (∀ (Φ : RadSp P.k P.r z z' π π') c g, (W Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g =
        u (c l) • (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g) →
      ∀ i : Fin 6, (i = 1 ∨ i = 2 ∨ i = 4 ∨ i = 5) → W * X.op l i = X.op l i * W := by
    intro W u hWu i hi
    apply LinearMap.ext; intro Φ; apply Subtype.ext; funext c g
    simp only [Module.End.mul_apply, hWu, hop, crd]
    rcases hi with rfl | rfl | rfl | rfl <;>
      simp only [opL, cOp, ciOp, cbOp, cbiOp] <;> exact smul_comm _ _ _
  have hsite : ∀ f : Pr (RadSp P.k P.r z z' π π'), (site L l).p = L.p l ∧ (site L l).c = L.c l ∧
      (site L l).ci = L.ci l := fun _ => ⟨rfl, rfl, rfl⟩
  obtain ⟨hsp, hsc, hsci⟩ := hsite 0
  rw [hsp, hsc, hsci, hp l, hc l, hci l]
  refine ⟨⟨pr_ext ?_ ?_, pr_ext ?_ ?_, rfl⟩, pr_ext ?_ ?_, pr_ext ?_ ?_, pr_ext ?_ ?_⟩
  · simpa using hWW'
  · simpa using hWW'
  · simpa using hW'W
  · simpa using hW'W
  · simpa using hcomm Wv _ hW1 1 (by decide)
  · simpa using (hcomm Wv' _ hW2 4 (by decide)).symm
  · simpa using hcomm Wv _ hW1 2 (by decide)
  · simpa using (hcomm Wv' _ hW2 5 (by decide)).symm
  · simp only [mkPair_fst', pr_mul_fst, pr_add_fst, pr_alg_fst]
    apply LinearMap.ext; intro Φ; apply Subtype.ext; funext c g
    obtain ⟨hd, h0⟩ := radSp_regular Φ g c
    simp only [Module.End.mul_apply, LinearMap.add_apply, Module.algebraMap_end_apply, Submodule.coe_add,
      Submodule.coe_smul, Pi.add_apply, Pi.smul_apply, hop, crd, hW1, opL]
    rw [pOp_fsv_smul s l _ c hd h0]
    simp only [cOp]
  · simp only [mkPair_snd', pr_mul_snd, pr_add_snd, pr_alg_snd]
    apply LinearMap.ext; intro Φ; apply Subtype.ext; funext c g
    obtain ⟨hd, h0⟩ := radSp_regular Φ g c
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.neg_apply, Module.algebraMap_end_apply,
      Submodule.coe_add, Submodule.coe_neg, Submodule.coe_smul, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, hop,
      crd, hW2, opL]
    rw [pbOp_fsv_smul s l _ c hd h0]
    simp only [cbOp]
    module

end Formalism.FourierDecayAlt.P5
