import Formalism.HermitianCurvature.StatementTL
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactSupportFacts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BaseCutoffIsTruncation
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComposeDifferentialOperators
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBFVpic
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumPairAtStarMul

namespace Formalism.FourierDecayAlt.P.TLB

open MeasureTheory Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section ops

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem ckOn_csmul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {m : ℕ∞} {UU : Set (B.Mat k r)}
    {f : B.Mat k r → E} (c : ℂ) (h : B.CkOn m UU f) : B.CkOn m UU (fun x => c • f x) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hcd, heq⟩ := h g₀ hg₀
  exact ⟨U, fun x => c • f' x, hU, hgU, hcd.const_smul c, fun g hg hgv => by
    show c • f g = c • f' g
    rw [heq g hg hgv]⟩

theorem ddp_mono (D : B.RealPlaceData k r Wp Wq) {nf : ℕ} {fib : Fin nf → B.Mat k r → C6.EndH Wp Wq}
    {L : Finset (Fin (r + 2))} {o κ o' κ' : ℕ} {Θ : B.DiffOp k r Wp Wq} (h : C6.InDDPlus D fib L o κ Θ)
    (ho : o ≤ o') (hκ : κ ≤ κ') : C6.InDDPlus D fib L o' κ' Θ := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, fun T hT => ?_⟩
  obtain ⟨P, a, b, c, es, ⟨q, hq, hPq⟩, hab, hlen, hlie, hcoef⟩ := h3 T hT
  exact ⟨P, a, b, c, es, ⟨q, hq.trans hκ, hPq⟩, hab, hlen.trans ho, hlie, hcoef⟩

theorem ddp_left (D : B.RealPlaceData k r Wp Wq) {nf nf' : ℕ} {fib : Fin nf → B.Mat k r → C6.EndH Wp Wq}
    (fib' : Fin nf' → B.Mat k r → C6.EndH Wp Wq) {L : Finset (Fin (r + 2))} {o κ : ℕ} {Θ : B.DiffOp k r Wp Wq}
    (h : C6.InDDPlus D fib L o κ Θ) : C6.InDDPlus D (Fin.append fib fib') L o κ Θ := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, fun T hT => ?_⟩
  obtain ⟨P, a, b, c, es, hP, hab, hlen, hlie, hcoef⟩ := h3 T hT
  refine ⟨P, a, b, c, es.map (fun e => (Fin.castAdd nf' e.1, e.2)), hP, hab, ?_, ?_, ?_⟩
  · simpa [List.map_map, Function.comp_def] using hlen
  · intro e he X hX
    rw [List.mem_map] at he
    obtain ⟨e0, he0, rfl⟩ := he
    exact hlie e0 he0 X hX
  · intro g hg
    rw [hcoef g hg]
    simp only [C6.Epart, List.map_map, Function.comp_def, Fin.append_left]

theorem ddp_right (D : B.RealPlaceData k r Wp Wq) {nf nf' : ℕ} (fib : Fin nf → B.Mat k r → C6.EndH Wp Wq)
    {fib' : Fin nf' → B.Mat k r → C6.EndH Wp Wq} {L : Finset (Fin (r + 2))} {o κ : ℕ} {Θ : B.DiffOp k r Wp Wq}
    (h : C6.InDDPlus D fib' L o κ Θ) : C6.InDDPlus D (Fin.append fib fib') L o κ Θ := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, fun T hT => ?_⟩
  obtain ⟨P, a, b, c, es, hP, hab, hlen, hlie, hcoef⟩ := h3 T hT
  refine ⟨P, a, b, c, es.map (fun e => (Fin.natAdd nf e.1, e.2)), hP, hab, ?_, ?_, ?_⟩
  · simpa [List.map_map, Function.comp_def] using hlen
  · intro e he X hX
    rw [List.mem_map] at he
    obtain ⟨e0, he0, rfl⟩ := he
    exact hlie e0 he0 X hX
  · intro g hg
    rw [hcoef g hg]
    simp only [C6.Epart, List.map_map, Function.comp_def, Fin.append_right]

theorem opApply_append (Θ₁ Θ₂ : B.DiffOp k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r) :
    B.opApply (Θ₁ ++ Θ₂) F g = B.opApply Θ₁ F g + B.opApply Θ₂ F g := by
  unfold B.opApply
  rw [List.map_append, List.sum_append]

private theorem foldr_max_eq_max_foldr_max_zero (l : List ℕ) (b : ℕ) : l.foldr max b = max (l.foldr max 0) b := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldr_cons]
    rw [ih]
    exact (max_assoc _ _ _).symm

theorem opOrder_append (Θ₁ Θ₂ : B.DiffOp k r Wp Wq) :
    B.opOrder (Θ₁ ++ Θ₂) = max (B.opOrder Θ₁) (B.opOrder Θ₂) := by
  unfold B.opOrder
  rw [List.map_append, List.foldr_append, foldr_max_eq_max_foldr_max_zero]

theorem rho_add (D : B.RealPlaceData k r Wp Wq) (p : B.SS k r) (F₁ F₂ : B.Mat k r → (Wq →L[ℂ] Wp))
    (g : B.Mat k r) : B.rho D p (fun x => F₁ x + F₂ x) g = B.rho D p F₁ g + B.rho D p F₂ g := by
  simp only [B.rho, ContinuousLinearMap.comp_add, ContinuousLinearMap.add_comp]

theorem rho_smul (D : B.RealPlaceData k r Wp Wq) (p : B.SS k r) (c : ℂ) (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (g : B.Mat k r) : B.rho D p (fun x => c • F x) g = c • B.rho D p F g := by
  simp only [B.rho, ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp]

theorem ddp_append (D : B.RealPlaceData k r Wp Wq) {nf : ℕ} {fib : Fin nf → B.Mat k r → C6.EndH Wp Wq}
    {L : Finset (Fin (r + 2))} {o κ : ℕ} {Θ₁ Θ₂ : B.DiffOp k r Wp Wq}
    (h₁ : C6.InDDPlus D fib L o κ Θ₁) (h₂ : C6.InDDPlus D fib L o κ Θ₂) :
    C6.InDDPlus D fib L o κ (Θ₁ ++ Θ₂) := by
  obtain ⟨s1, c1, t1⟩ := h₁
  obtain ⟨s2, c2, t2⟩ := h₂
  refine ⟨?_, ?_, ?_⟩
  · intro T hT
    rcases List.mem_append.mp hT with h | h
    · exact s1 T h
    · exact s2 T h
  · intro p hp f hf g hg
    have hf1 : B.CkOn (B.opOrder Θ₁ : ℕ∞) (B.GV k r) f :=
      B5.ckOn_mono (by rw [opOrder_append]; exact_mod_cast le_max_left _ _) hf
    have hf2 : B.CkOn (B.opOrder Θ₂ : ℕ∞) (B.GV k r) f :=
      B5.ckOn_mono (by rw [opOrder_append]; exact_mod_cast le_max_right _ _) hf
    have hsum : B.opApply (Θ₁ ++ Θ₂) f = fun x => B.opApply Θ₁ f x + B.opApply Θ₂ f x :=
      funext (opApply_append Θ₁ Θ₂ f)
    rw [opApply_append, c1 p hp f hf1 g hg, c2 p hp f hf2 g hg, hsum, rho_add]
  · intro T hT
    rcases List.mem_append.mp hT with h | h
    · exact t1 T h
    · exact t2 T h

def smulT (c : ℂ) (T : B.DTerm k r Wp Wq) : B.DTerm k r Wp Wq where
  coef := fun x => c • T.coef x
  coefAdj := fun x => conj c • T.coefAdj x
  word := T.word
  word_lie := T.word_lie
  adj_id := fun x A B' => by
    show B.hsInner (c • T.coef x A) B' = B.hsInner A (conj c • T.coefAdj x B')
    rw [P5.HerA.hsInner_smul_left', P5.HerA.hsInner_smul_right', T.adj_id, Complex.conj_conj]

theorem opApply_smulT (c : ℂ) (Θ : B.DiffOp k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r) :
    B.opApply (Θ.map (smulT c)) F g = c • B.opApply Θ F g := by
  unfold B.opApply
  rw [List.smul_sum, List.map_map, List.map_map]
  rfl

theorem opOrder_smulT (c : ℂ) (Θ : B.DiffOp k r Wp Wq) : B.opOrder (Θ.map (smulT c)) = B.opOrder Θ := by
  unfold B.opOrder
  rw [List.map_map]
  rfl

theorem ddp_smul (D : B.RealPlaceData k r Wp Wq) {nf : ℕ} {fib : Fin nf → B.Mat k r → C6.EndH Wp Wq}
    {L : Finset (Fin (r + 2))} {o κ : ℕ} {Θ : B.DiffOp k r Wp Wq} (c : ℂ)
    (h : C6.InDDPlus D fib L o κ Θ) : C6.InDDPlus D fib L o κ (Θ.map (smulT c)) := by
  obtain ⟨s, cm, t⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro T hT
    rw [List.mem_map] at hT
    obtain ⟨T0, hT0, rfl⟩ := hT
    exact ⟨ckOn_csmul c (s T0 hT0).1, ckOn_csmul (conj c) (s T0 hT0).2⟩
  · intro p hp f hf g hg
    rw [opOrder_smulT] at hf
    have hmap : B.opApply (Θ.map (smulT c)) f = fun x => c • B.opApply Θ f x :=
      funext (opApply_smulT c Θ f)
    rw [opApply_smulT, cm p hp f hf g hg, hmap, rho_smul]
  · intro T hT
    rw [List.mem_map] at hT
    obtain ⟨T0, hT0, rfl⟩ := hT
    obtain ⟨P, a, b, e, es, ⟨q, hq, hPq⟩, hab, hlen, hlie, hcoef⟩ := t T0 hT0
    refine ⟨fun g => c * P g, a, b, e, es, ⟨MvPolynomial.C c * q, ?_, ?_⟩, hab, hlen, hlie, ?_⟩
    · calc (MvPolynomial.C c * q).totalDegree ≤ (MvPolynomial.C c).totalDegree + q.totalDegree :=
            MvPolynomial.totalDegree_mul _ _
        _ ≤ κ := by rw [MvPolynomial.totalDegree_C, zero_add]; exact hq
    · intro g
      simp only [map_mul, MvPolynomial.eval_C]
      rw [hPq g]
    · intro g hg
      show c • T0.coef g = _
      rw [hcoef g hg, smul_smul, mul_assoc]

theorem fib_append {D : B.RealPlaceData k r Wp Wq} {nf nf' : ℕ} {fib : Fin nf → B.Mat k r → C6.EndH Wp Wq}
    {fib' : Fin nf' → B.Mat k r → C6.EndH Wp Wq} (h : ∀ j, C6.FibBound D (fib j)) (h' : ∀ j, C6.FibBound D (fib' j)) :
    ∀ j, C6.FibBound D (Fin.append fib fib' j) := by
  intro j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · rw [Fin.append_left]; exact h i
  · rw [Fin.append_right]; exact h' i

theorem nice_mono {Bs : B.RealPlaceData k r Wp Wq} {ε ε' : ℝ} {F : B.Mat k r → (Wq →L[ℂ] Wp)} (h : JC.NiceCoef Bs ε F)
    (hε : ε' ≤ ε) : JC.NiceCoef Bs ε' F := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, h2, fun g hg hne => hε.trans (h3 g hg hne)⟩

end ops

section rad

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem wCell_om {Pa : M.Par} (Bs : B.RealPlaceData Pa.k Pa.r Wp Wq) {x : (Fin Pa.r → ℂ) × Q.Mx Pa.k Pa.r}
    (hx : x ∈ Q.DomR Pa.k Pa.r Bs.z Bs.z') :
    Q.wCell Pa.k Pa.r (Fin.last Pa.r) x.1 * x.2 ∈ JF.Om Pa.k Pa.r Bs.z Bs.z' := by
  refine ⟨?_, P5.Rad.wCell_mem_omPlus Bs.z_mem Bs.z'_mem hx.1 hx.2.1 hx.2.2⟩
  have h1 : Q.wCell Pa.k Pa.r (Fin.last Pa.r) x.1 ∈ Q.Glev Pa.k Pa.r 0 := by
    unfold Q.wCell
    exact Qx3.wlist_glev hx.1 _
  exact (Qx5.Glev_mul h1 (Qx4.glev0 hx.2.1.1)).1

theorem wCell_gv {Pa : M.Par} (Bs : B.RealPlaceData Pa.k Pa.r Wp Wq) {x : (Fin Pa.r → ℂ) × Q.Mx Pa.k Pa.r}
    (hx : x ∈ Q.DomR Pa.k Pa.r Bs.z Bs.z') :
    Q.wCell Pa.k Pa.r (Fin.last Pa.r) x.1 * x.2 ∈ B.GV Pa.k Pa.r := (wCell_om Bs hx).1

theorem cpt_op {k r : ℕ} {Bs : B.RealPlaceData k r Wp Wq} {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : KB.CptCoef Bs F)
    {Θ : B.DiffOp k r Wp Wq} (hΘ : B.SmoothCoef (C6.domL Bs ∅) Θ) : KB.CptCoef Bs (B.opApply Θ F) :=
  ((Formalism.FourierDecayAlt.P.compact_support_facts k r Wp Wq Bs F hF).2 Θ hΘ).1

theorem op_zero_off {k r : ℕ} {Bs : B.RealPlaceData k r Wp Wq} {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : KB.CptCoef Bs F)
    {Θ : B.DiffOp k r Wp Wq} (hΘ : B.SmoothCoef (C6.domL Bs ∅) Θ) :
    ∀ g ∈ B.GV k r, g ∉ C6.domL Bs ∅ → B.opApply Θ F g = 0 :=
  ((Formalism.FourierDecayAlt.P.compact_support_facts k r Wp Wq Bs F hF).2 Θ hΘ).2

theorem nice_of_cpt {k r : ℕ} {Bs : B.RealPlaceData k r Wp Wq} {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : KB.CptCoef Bs F) :
    ∃ ε, 0 < ε ∧ JC.NiceCoef Bs ε F :=
  (Formalism.FourierDecayAlt.P.compact_support_facts k r Wp Wq Bs F hF).1

theorem radIs_zero (Pa : M.Par) (Bs : B.RealPlaceData Pa.k Pa.r Wp Wq) :
    TL.RadIs Pa Bs [] (0 : Module.End ℂ (Q.RadSp Pa.k Pa.r Bs.z Bs.z' Bs.π Bs.π')) := by
  intro F hF Φ hΦ x hx
  have h0 : B.opApply ([] : B.DiffOp Pa.k Pa.r Wp Wq) F = fun _ => 0 := by
    funext g
    simp [B.opApply]
  rw [h0]
  simp [Q.resG, JCx2.bc_JF_zero]

theorem radIs_add (Pa : M.Par) (Bs : B.RealPlaceData Pa.k Pa.r Wp Wq) {Θ₁ Θ₂ : B.DiffOp Pa.k Pa.r Wp Wq}
    {T₁ T₂ : Module.End ℂ (Q.RadSp Pa.k Pa.r Bs.z Bs.z' Bs.π Bs.π')}
    (hs₁ : B.SmoothCoef (C6.domL Bs ∅) Θ₁) (hs₂ : B.SmoothCoef (C6.domL Bs ∅) Θ₂)
    (h₁ : TL.RadIs Pa Bs Θ₁ T₁) (h₂ : TL.RadIs Pa Bs Θ₂ T₂) : TL.RadIs Pa Bs (Θ₁ ++ Θ₂) (T₁ + T₂) := by
  intro F hF Φ hΦ x hx
  obtain ⟨ε₁, -, hn₁⟩ := nice_of_cpt (cpt_op hF hs₁)
  obtain ⟨ε₂, -, hn₂⟩ := nice_of_cpt (cpt_op hF hs₂)
  have e1 := h₁ F hF Φ hΦ x hx
  have e2 := h₂ F hF Φ hΦ x hx
  have hsum : B.opApply (Θ₁ ++ Θ₂) F = fun g => B.opApply Θ₁ F g + B.opApply Θ₂ F g :=
    funext (opApply_append Θ₁ Θ₂ F)
  rw [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply, Pi.add_apply, e1, e2, hsum]
  simp only [Q.resG]
  rw [JCx2.bc_JF_add (nice_mono hn₁ (min_le_left ε₁ ε₂)) (nice_mono hn₂ (min_le_right ε₁ ε₂))
    (wCell_om Bs hx), smul_add]

theorem radIs_smul (Pa : M.Par) (Bs : B.RealPlaceData Pa.k Pa.r Wp Wq) {Θ : B.DiffOp Pa.k Pa.r Wp Wq}
    {T : Module.End ℂ (Q.RadSp Pa.k Pa.r Bs.z Bs.z' Bs.π Bs.π')} (c : ℂ)
    (h : TL.RadIs Pa Bs Θ T) : TL.RadIs Pa Bs (Θ.map (smulT c)) (c • T) := by
  intro F hF Φ hΦ x hx
  have e := h F hF Φ hΦ x hx
  have hmap : B.opApply (Θ.map (smulT c)) F = fun g => c • B.opApply Θ F g :=
    funext (opApply_smulT c Θ F)
  rw [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply, Pi.smul_apply, e, hmap]
  simp only [Q.resG]
  rw [JCx2.bc_JF_smul, smul_comm]

theorem radIs_comp (Pa : M.Par) (Bs : B.RealPlaceData Pa.k Pa.r Wp Wq) {Θ Θ₁ Θ₂ : B.DiffOp Pa.k Pa.r Wp Wq} {o : ℕ}
    {T₁ T₂ : Module.End ℂ (Q.RadSp Pa.k Pa.r Bs.z Bs.z' Bs.π Bs.π')}
    (hs : B.SmoothCoef (C6.domL Bs ∅) Θ) (hs₁ : B.SmoothCoef (C6.domL Bs ∅) Θ₁)
    (hs₂ : B.SmoothCoef (C6.domL Bs ∅) Θ₂)
    (hΘ : ∀ F : B.Mat Pa.k Pa.r → (Wq →L[ℂ] Wp), B.CkOn (o : ℕ∞) (B.GV Pa.k Pa.r) F →
      ∀ g ∈ C6.domL Bs ∅, B.opApply Θ F g = B.opApply Θ₁ (B.opApply Θ₂ F) g)
    (h₁ : TL.RadIs Pa Bs Θ₁ T₁) (h₂ : TL.RadIs Pa Bs Θ₂ T₂) : TL.RadIs Pa Bs Θ (T₁ * T₂) := by
  intro F hF Φ hΦ x hx
  have hc2 := cpt_op hF hs₂
  have e := h₁ _ hc2 _ (h₂ F hF Φ hΦ) x hx
  have hEq : ∀ g ∈ B.GV Pa.k Pa.r, B.opApply Θ₁ (B.opApply Θ₂ F) g = B.opApply Θ F g := by
    intro g hg
    by_cases hd : g ∈ C6.domL Bs ∅
    · exact (hΘ F (B5.ckOn_mono le_top hF.1) g hd).symm
    · rw [op_zero_off hc2 hs₁ g hg hd, op_zero_off hF hs g hg hd]
  rw [Module.End.mul_apply, e]
  simp only [Q.resG]
  rw [JCx2.sq_jf_congr Bs hEq (wCell_gv Bs hx)]

end rad

end

end Formalism.FourierDecayAlt.P.TLB

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TL Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.TLB

theorem lift_closed_under_operations : TL.LiftClosed := by
  intro Wp Wq _ _ _ _ _ _ P Bs
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro o o' κ κ' a ho hκ ⟨nf, fib, Dop, hfib, hdd, hrad⟩
    exact ⟨nf, fib, Dop, hfib, ddp_mono Bs hdd ho hκ, hrad⟩
  · intro o κ
    refine ⟨0, Fin.elim0, [], fun j => j.elim0, ⟨?_, ?_, ?_⟩, ?_⟩
    · intro T hT
      simp at hT
    · intro p hp f hf g hg
      simp [B.opApply, B.rho]
    · intro T hT
      simp at hT
    · exact radIs_zero P Bs
  · rintro o κ a b ⟨nf, fib, Θ₁, hf₁, hd₁, hr₁⟩ ⟨nf', fib', Θ₂, hf₂, hd₂, hr₂⟩
    exact ⟨nf + nf', Fin.append fib fib', Θ₁ ++ Θ₂, fib_append hf₁ hf₂,
      ddp_append Bs (ddp_left Bs fib' hd₁) (ddp_right Bs fib hd₂), radIs_add P Bs hd₁.1 hd₂.1 hr₁ hr₂⟩
  · rintro o κ a z ⟨nf, fib, Θ, hf, hd, hr⟩
    exact ⟨nf, fib, Θ.map (smulT z), hf, ddp_smul Bs z hd, radIs_smul P Bs z hr⟩
  · rintro o₁ κ₁ o₂ κ₂ a b ⟨nf, fib, Θ₁, hf₁, hd₁, hr₁⟩ ⟨nf', fib', Θ₂, hf₂, hd₂, hr₂⟩
    obtain ⟨Θ, hd, hΘ⟩ := compose_differential_operators P.k P.r Wp Wq Bs (nf + nf') (Fin.append fib fib') ∅
      o₁ κ₁ o₂ κ₂ Θ₁ Θ₂ (fib_append hf₁ hf₂) (ddp_left Bs fib' hd₁) (ddp_right Bs fib hd₂)
    exact ⟨nf + nf', Fin.append fib fib', Θ, fib_append hf₁ hf₂, hd,
      radIs_comp P Bs hd.1 hd₁.1 hd₂.1 hΘ hr₁ hr₂⟩

end Formalism.FourierDecayAlt.P
