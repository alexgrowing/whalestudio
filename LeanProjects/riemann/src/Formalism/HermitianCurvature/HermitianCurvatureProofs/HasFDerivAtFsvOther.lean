import Formalism.HermitianCurvature.HermitianCurvatureProofs.FsvMulFsvNeg

open scoped ComplexConjugate ContDiff
open Filter Topology

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd

section SmulC

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def SmulC (T : (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E)) : Prop :=
  ∀ (α : ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E), T (α • f) = α • T f

theorem rdV_smulC (X : Matrix (Fin n) (Fin n) ℂ) : SmulC (E := E) (RdV X) := by
  intro α f
  funext g
  simp only [RdV, Pi.smul_apply]
  first
    | exact deriv_const_smul' α
    | (by_cases h : DifferentiableAt ℝ (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) 0
       · exact deriv_const_smul α h
       · by_cases hα : α = 0
         · subst hα; simp
         · rw [deriv_zero_of_not_differentiableAt h, smul_zero]
           apply deriv_zero_of_not_differentiableAt
           intro h'
           apply h
           have e : (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) =
               α⁻¹ • fun t : ℝ => α • f (g * NormedSpace.exp ((t : ℂ) • X)) := by
             funext t
             simp [smul_smul, inv_mul_cancel₀ hα]
           rw [e]
           exact h'.const_smul α⁻¹)

theorem eabH_smulC (H : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) : SmulC (E := E) (EabH H a b) := by
  intro α f
  funext g
  simp only [EabH, Pi.smul_apply]
  rw [rdV_smulC _ α f, rdV_smulC _ α f]
  simp only [Pi.smul_apply, smul_add]
  rw [smul_comm Complex.I α]

theorem top_smulC {Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E)}
    (hE : ∀ a b, SmulC (Eop a b)) (u : ℂ) (a b : Fin n) : SmulC (Top Eop u a b) := by
  intro α f
  funext g
  simp only [Formalism.QuantumDeterminants.Top, Pi.smul_apply]
  rw [hE a b α f, Pi.smul_apply, smul_add]
  split_ifs
  · rw [smul_comm u α]
  · rw [smul_zero]

theorem foldr_smulC (Ts : List ((Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E)))
    (h : ∀ T ∈ Ts, SmulC T) : SmulC (fun f => Ts.foldr (fun T h => T h) f) := by
  induction Ts with
  | nil => intro α f; rfl
  | cons T Ts ih =>
    intro α f
    have ih' := ih (fun T' hT' => h T' (by simp [hT']))
    have e := ih' α f
    simp only [List.foldr_cons] at e ⊢
    rw [e]
    exact h T (by simp) α _

theorem qminorOp_smulC {t : ℕ}
    {Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E)}
    (hE : ∀ a b, SmulC (Eop a b)) (a b : Fin t → Fin n) (u : ℂ) : SmulC (qminorOp Eop a b u) := by
  intro α f
  simp only [qminorOp, Finset.smul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hT : (List.ofFn fun k : Fin t => Formalism.QuantumDeterminants.Top Eop (u - ((k : ℕ) : ℂ)) (a (σ k)) (b k)).foldr (fun T h => T h) (α • f) =
      α • (List.ofFn fun k : Fin t => Formalism.QuantumDeterminants.Top Eop (u - ((k : ℕ) : ℂ)) (a (σ k)) (b k)).foldr (fun T h => T h) f :=
    foldr_smulC (List.ofFn fun k : Fin t => Formalism.QuantumDeterminants.Top Eop (u - ((k : ℕ) : ℂ)) (a (σ k)) (b k))
      (fun T hT => by
        simp only [List.mem_ofFn, Set.mem_range] at hT
        obtain ⟨k, rfl⟩ := hT
        exact top_smulC hE _ _ _) α f
  rw [hT, smul_comm]

end SmulC

section TL

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem eH_smulC (a b : Fin (2 * r + k + 1)) : SmulC (E := E) (EH k r a b) := by
  exact eabH_smulC _ a b

theorem chatL_smulC {t : ℕ} (pos : Fin t → Fin (2 * r + k + 1)) (u : ℂ) (a β : Mx k r → Fin t → ℂ) :
    SmulC (E := E) (chatL (EH k r) pos u a β) := by
  intro α f
  funext g
  simp only [chatL, Pi.smul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [qminorOp_smulC (fun a b => eH_smulC a b) _ _ u α f, Pi.smul_apply, smul_comm]

theorem capelli_entry_smul {t : ℕ} (pos : Fin t → Fin (2 * r + k + 1)) (u : ℂ) (a a' β β' : Mx k r → Fin t → ℂ) :
    SmulC (E := E) (chat2L (EH k r) pos u a a' β β') := by
  intro α f
  funext g
  simp only [chat2L, Pi.smul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ =>
    Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
  split_ifs
  · rw [qminorOp_smulC (fun a b => eH_smulC a b) _ _ u α f, Pi.smul_apply, smul_comm]
  · rw [smul_zero]

theorem tL_smulC (z z' : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)) (Y : ℂ) :
    ∀ p q : Fin 2, SmulC (E := E) (tL k r z z' i Y p q)
  | 0, 0 => fun α f => by
      simp only [tL, capL]
      exact qminorOp_smulC (eH_smulC (k := k) (r := r)) _ _ _ α f
  | 0, 1 => fun α f => by
      simp only [tL]
      rw [chatL_smulC _ _ _ _ α f, smul_neg]
  | 1, 0 => fun α f => by
      simp only [tL]
      rw [chatL_smulC _ _ _ _ α f, smul_neg]
  | 1, 1 => fun α f => by
      simp only [tL]
      rw [capelli_entry_smul _ _ _ _ _ _ α f, smul_neg]

end TL

section Other

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem hasFDerivAt_fsv_other (t : ℂ) (l : Fin m) (c : Fin m → ℂ) :
    ∃ D : (Fin m → ℂ) →L[ℝ] ℂ, HasFDerivAt (fun c' : Fin m → ℂ => fsv t (c' l)) D c ∧
      ∀ l' : Fin m, l' ≠ l → ∀ v : ℂ, D (Pi.single l' v) = 0 := by
  have hconj : Differentiable ℝ (fun z : ℂ => conj z) := Complex.conjCLE.differentiable
  have hlin : Differentiable ℝ (fun z : ℂ => t * z - conj t * conj z) := by
    first
      | fun_prop
      | (apply Differentiable.sub
         · exact (differentiable_id (𝕜 := ℝ) (E := ℂ)).const_mul t
         · exact hconj.const_mul (conj t))
  have hg : DifferentiableAt ℝ (fun z : ℂ => fsv t z) (c l) := by
    unfold fsv
    first
      | exact ((Complex.differentiable_exp (𝕜 := ℝ)).comp hlin) (c l)
      | exact (hlin (c l)).cexp
      | fun_prop
  refine ⟨(fderiv ℝ (fun z : ℂ => fsv t z) (c l)).comp (ContinuousLinearMap.proj l), ?_, ?_⟩
  · have h := hg.hasFDerivAt.comp c (hasFDerivAt_apply (𝕜 := ℝ) l c)
    exact h
  · intro l' hl' v
    simp [Pi.single_apply, Ne.symm hl']

theorem wirt_fsv_smul_other (t : ℂ) {l l' : Fin m} (hl : l' ≠ l) (φ : (Fin m → ℂ) → E) (c : Fin m → ℂ)
    (hφ : DifferentiableAt ℝ φ c) :
    wirt l' (fun c' => fsv t (c' l) • φ c') c = fsv t (c l) • wirt l' φ c ∧
    wirtBar l' (fun c' => fsv t (c' l) • φ c') c = fsv t (c l) • wirtBar l' φ c := by
  obtain ⟨D, hD, hD0⟩ := hasFDerivAt_fsv_other t l c
  have hf : fderiv ℝ (fun c' => fsv t (c' l) • φ c') c = fsv t (c l) • fderiv ℝ φ c + D.smulRight (φ c) :=
    (hD.smul hφ.hasFDerivAt).fderiv
  have e : ∀ v : ℂ, fderiv ℝ (fun c' => fsv t (c' l) • φ c') c (Pi.single l' v) =
      fsv t (c l) • fderiv ℝ φ c (Pi.single l' v) := by
    intro v
    rw [hf, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
      hD0 l' hl v, zero_smul, add_zero]
  constructor
  · unfold Formalism.QuantumDeterminants.wirt
    rw [e, e, smul_comm Complex.I (fsv t (c l)), ← smul_sub, smul_comm]
  · unfold Formalism.QuantumDeterminants.wirtBar
    rw [e, e, smul_comm Complex.I (fsv t (c l)), ← smul_add, smul_comm]

theorem opL_fsv_smul_other (t : ℂ) {l l' : Fin m} (hl : l' ≠ l) (i : Fin 6) (φ : (Fin m → ℂ) → E)
    (c : Fin m → ℂ) (hd : c ∈ OmX m → DifferentiableAt ℝ φ c) :
    opL l' i (fun c' => fsv t (c' l) • φ c') c = fsv t (c l) • opL l' i φ c := by
  match i with
  | 0 =>
    show Formalism.QuantumDeterminants.pOp l' _ c = _ • Formalism.QuantumDeterminants.pOp l' φ c
    simp only [Formalism.QuantumDeterminants.pOp]
    split_ifs with h
    · rw [(wirt_fsv_smul_other t hl φ c (hd h)).1, smul_comm]
    · rw [smul_zero]
  | 1 => exact smul_comm _ _ _
  | 2 => exact smul_comm _ _ _
  | 3 =>
    show Formalism.QuantumDeterminants.pbOp l' _ c = _ • Formalism.QuantumDeterminants.pbOp l' φ c
    simp only [Formalism.QuantumDeterminants.pbOp]
    split_ifs with h
    · rw [(wirt_fsv_smul_other t hl φ c (hd h)).2, smul_comm]
    · rw [smul_zero]
  | 4 => exact smul_comm _ _ _
  | 5 => exact smul_comm _ _ _

end Other

section Ops

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
  [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem mulOp_comm_op (X : ActualOps k r z z' π π') (W : Module.End ℂ (RadSp k r z z' π π')) (t : ℂ) (l : Fin r)
    (hW : ∀ (Φ : RadSp k r z z' π π') c g, (W Φ : Fn k r (Wq →L[ℂ] Wp)) c g =
      fsv t (c l) • (Φ : Fn k r (Wq →L[ℂ] Wp)) c g)
    {l' : Fin r} (hl : l' ≠ l) (i : Fin 6) : W * X.op l' i = X.op l' i * W := by
  apply LinearMap.ext; intro Φ; apply Subtype.ext; funext c g
  have hop : ∀ (Ψ : RadSp k r z z' π π'),
      (X.op l' i Ψ : Fn k r (Wq →L[ℂ] Wp)) = crd (opL l' i) (Ψ : Fn k r (Wq →L[ℂ] Wp)) :=
    fun Ψ => X.op_apply l' i Ψ
  simp only [Module.End.mul_apply, hW, hop, crd]
  exact (opL_fsv_smul_other t hl i _ c (radSp_regular Φ g c).1).symm

theorem comm_xt_of_fsv_smul_endomorphism (X : ActualOps k r z z' π π') (W : Module.End ℂ (RadSp k r z z' π π')) (t : ℂ) (l : Fin r)
    (hW : ∀ (Φ : RadSp k r z z' π π') c g, (W Φ : Fn k r (Wq →L[ℂ] Wp)) c g =
      fsv t (c l) • (Φ : Fn k r (Wq →L[ℂ] Wp)) c g)
    (Y : ℂ) (a b : Fin 2) : W * X.t Y a b = X.t Y a b * W := by
  apply LinearMap.ext; intro Φ; apply Subtype.ext; funext c g
  simp only [Module.End.mul_apply]
  rw [hW]
  by_cases hx : (c, g) ∈ DomR k r z z'
  · have h1 := X.t_apply Y a b Φ (c, g) hx
    have h2 := X.t_apply Y a b (W Φ) (c, g) hx
    simp only at h1 h2
    have hWc : (W Φ : Fn k r (Wq →L[ℂ] Wp)) c = fsv t (c l) • (Φ : Fn k r (Wq →L[ℂ] Wp)) c := by
      funext g'; rw [hW]; rfl
    rw [h1, h2, hWc, tL_smulC z z' _ Y a b]
    rfl
  · rw [(X.t Y a b Φ).2.1 (c, g) hx, (X.t Y a b (W Φ)).2.1 (c, g) hx, smul_zero]

end Ops

section Cen

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem star_mkP (A B : Module.End ℂ V) : star (mkP A B : Pr V) = mkP B A := rfl

theorem commute_mkP {A B C D : Module.End ℂ V} (h1 : A * C = C * A) (h2 : D * B = B * D) :
    Commute (mkP A B : Pr V) (mkP C D) := by
  show ((A * C, MulOpposite.op B * MulOpposite.op D) : Module.End ℂ V × (Module.End ℂ V)ᵐᵒᵖ) =
    (C * A, MulOpposite.op D * MulOpposite.op B)
  rw [h1, ← MulOpposite.op_mul, ← MulOpposite.op_mul, h2]

def cenW (Wv Wv' : Module.End ℂ V) : Subalgebra ℂ (Pr V) :=
  Subalgebra.centralizer ℂ ({mkP Wv Wv', mkP Wv' Wv} : Set (Pr V))

theorem mem_cenW_of {Wv Wv' C D : Module.End ℂ V} (h1 : Wv * C = C * Wv) (h2 : Wv' * C = C * Wv')
    (h3 : Wv * D = D * Wv) (h4 : Wv' * D = D * Wv') : mkP C D ∈ cenW Wv Wv' := by
  rw [cenW, Subalgebra.mem_centralizer_iff]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl
  · exact (commute_mkP h1 h4.symm).eq
  · exact (commute_mkP h2 h3.symm).eq

theorem star_mem_cenW {Wv Wv' : Module.End ℂ V} {x : Pr V} (hx : x ∈ cenW Wv Wv') : star x ∈ cenW Wv Wv' := by
  rw [cenW, Subalgebra.mem_centralizer_iff] at hx ⊢
  intro g hg
  have hg' : star g ∈ ({mkP Wv Wv', mkP Wv' Wv} : Set (Pr V)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg ⊢
    rcases hg with rfl | rfl
    · right; exact star_mkP _ _
    · left; exact star_mkP _ _
  have e := congrArg star (hx _ hg')
  simp only [star_mul, star_star] at e
  exact e.symm

theorem Ts_mem {T : Subalgebra ℂ (Pr V)} (σ : Site (Pr V)) (Y : ℂ) (hp : σ.p ∈ T) (hc : σ.c ∈ T)
    (hci : σ.ci ∈ T) (a b : Fin 2) : Ts σ Y a b ∈ T := by
  fin_cases a <;> fin_cases b <;>
    simp [Ts, Formalism.YangianSpanCharacter.T.Tm] <;>
    first
      | exact T.add_mem (T.algebraMap_mem Y) hp
      | exact hc
      | exact hci
      | exact T.neg_mem hc

end Cen

section Prod

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem tprod_mem (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (Tc : Subalgebra ℂ (Pr (RadSp k r z z' π π')))
    (l : ℕ) (hs : ∀ l' : Fin r, l < l'.val → L.p l' ∈ Tc ∧ L.c l' ∈ Tc ∧ L.ci l' ∈ Tc) (Y : ℂ) (i : ℕ)
    (hi : l < i) : ∀ a b, tprod L Y i a b ∈ Tc := by
  suffices H : ∀ n : ℕ, ∀ j : ℕ, r - j = n → l < j → ∀ a b, tprod L Y j a b ∈ Tc from H _ i rfl hi
  intro n
  induction n with
  | zero =>
    intro j hn hj a b
    rw [tprod, dif_neg (by omega), Matrix.one_apply]
    split_ifs
    · exact Tc.one_mem
    · exact Tc.zero_mem
  | succ n ih =>
    intro j hn hj a b
    rw [tprod, dif_pos (by omega), Matrix.mul_apply]
    refine Subalgebra.sum_mem _ fun c _ => Subalgebra.mul_mem _ (ih (j + 1) (by omega) (by omega) a c) ?_
    have hh := hs ⟨j, by omega⟩ hj
    exact Ts_mem _ Y hh.1 hh.2.1 hh.2.2 c b

end Prod

theorem waveCommQQAll : WaveCommQQAll := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 hD
  obtain ⟨-, -, hL, hQQ, -⟩ := hD
  obtain ⟨hp, -, hc, hci, -⟩ := hL
  intro l s Wv Wv' hW hW' Y a b
  have hW1 : ∀ (Φ : RadSp P.k P.r z z' π π') c g, (Wv Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g =
      fsv s (c l) • (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g := hW
  have hW2 : ∀ (Φ : RadSp P.k P.r z z' π π') c g, (Wv' Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g =
      fsv (-s) (c l) • (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g := hW'
  set T := cenW Wv Wv' with hT
  have hop : ∀ l' : Fin P.r, l' ≠ l → ∀ i, mkP (X.op l' i) (X.op l' i) ∈ T ∧ True := by
    intro l' hl' i
    exact ⟨mem_cenW_of (mulOp_comm_op X Wv s l hW1 hl' i) (mulOp_comm_op X Wv' (-s) l hW2 hl' i)
      (mulOp_comm_op X Wv s l hW1 hl' i) (mulOp_comm_op X Wv' (-s) l hW2 hl' i), trivial⟩
  have hcomm : ∀ l' : Fin P.r, l' ≠ l → ∀ i j, mkP (X.op l' i) (X.op l' j) ∈ T := by
    intro l' hl' i j
    exact mem_cenW_of (mulOp_comm_op X Wv s l hW1 hl' i) (mulOp_comm_op X Wv' (-s) l hW2 hl' i)
      (mulOp_comm_op X Wv s l hW1 hl' j) (mulOp_comm_op X Wv' (-s) l hW2 hl' j)
  have hneg : ∀ (A : Module.End ℂ (RadSp P.k P.r z z' π π')) (W : Module.End ℂ (RadSp P.k P.r z z' π π')),
      W * A = A * W → W * -A = -A * W := by
    intro A W h; rw [mul_neg, neg_mul, h]
  have hs : ∀ l' : Fin P.r, l.val < l'.val → L.p l' ∈ T ∧ L.c l' ∈ T ∧ L.ci l' ∈ T := by
    intro l' hl'
    have hne : l' ≠ l := fun h => by rw [h] at hl'; exact lt_irrefl _ hl'
    refine ⟨?_, ?_, ?_⟩
    · rw [hp l']
      exact mem_cenW_of (mulOp_comm_op X Wv s l hW1 hne 0) (mulOp_comm_op X Wv' (-s) l hW2 hne 0)
        (hneg _ _ (mulOp_comm_op X Wv s l hW1 hne 3)) (hneg _ _ (mulOp_comm_op X Wv' (-s) l hW2 hne 3))
    · rw [hc l']; exact hcomm l' hne 1 4
    · rw [hci l']; exact hcomm l' hne 2 5
  have hQ : ∀ a b, st.QQ Y a b ∈ T := by
    intro a b
    rw [hQQ Y, Matrix.smul_apply]
    refine T.smul_mem ?_ _
    simp only [ActualOps.QQ, Matrix.of_apply]
    exact mem_cenW_of (comm_xt_of_fsv_smul_endomorphism X Wv s l hW1 Y a b) (comm_xt_of_fsv_smul_endomorphism X Wv' (-s) l hW2 Y a b)
      (comm_xt_of_fsv_smul_endomorphism X Wv s l hW1 (star Y) b a) (comm_xt_of_fsv_smul_endomorphism X Wv' (-s) l hW2 (star Y) b a)
  have hA := tprod_mem L T l.val hs (star Y) (l.succ.val) (by simp)
  have hB := tprod_mem L T l.val hs Y (l.succ.val) (by simp)
  have hmem : QQi L st l.succ Y a b ∈ T := by
    simp only [QQi, Matrix.mul_apply, Matrix.conjTranspose_apply]
    refine T.sum_mem fun c _ => T.mul_mem (T.sum_mem fun d _ => T.mul_mem (star_mem_cenW (hA d a)) (hQ d c)) (hB c b)
  rw [hT, cenW, Subalgebra.mem_centralizer_iff] at hmem
  exact hmem _ (by simp)

end Formalism.FourierDecayAlt.P5
