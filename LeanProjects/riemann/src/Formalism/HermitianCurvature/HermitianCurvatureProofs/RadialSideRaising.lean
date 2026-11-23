import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadAATopOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellConjTransposeMulApply
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WCellMemOmPlus
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAlgebraFacts

open MeasureTheory Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBN

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section cell

variable {k r : ℕ}

theorem herm_eI (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    herm (Hpk k r) v (bvec (eI k r a)) = v (esI k r a) := by
  unfold herm
  rw [dotProduct, Finset.sum_eq_single (eI k r a)]
  · simp only [bvec, Pi.star_apply, Pi.single_eq_same, star_one, one_mul, Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single (esI k r a)]
    · rw [Formalism.FourierDecayAlt.P.Qx3.hpk_row_e, if_pos rfl, one_mul]
    · intro b _ hb
      rw [Formalism.FourierDecayAlt.P.Qx3.hpk_row_e, if_neg hb, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro b _ hb
    simp [bvec, Pi.single_apply, hb]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem glev_row {g : B.Mat k r} (hg : g ∈ Q.Glev k r (Fin.last r)) (a : Fin r) (p : Fin (2 * r + k + 1)) :
    g (eI k r a) p = if p = eI k r a then 1 else 0 := by
  have hU : gᴴ * Hpk k r * g = Hpk k r := hg.1
  have hfix : g *ᵥ bvec (esI k r a) = bvec (esI k r a) := (hg.2 a (by simp)).2
  have hcol : ∀ i, g i (esI k r a) = if i = esI k r a then 1 else 0 := by
    intro i
    have := congrFun hfix i
    simpa [bvec, Matrix.mulVec_single_one, Pi.single_apply] using this
  have e1 := congrFun (congrFun hU (esI k r a)) p
  rw [Formalism.FourierDecayAlt.P.Qx3.hpk_row_es] at e1
  have hrow : ∀ b, (gᴴ * Hpk k r) (esI k r a) b = if b = eI k r a then 1 else 0 := by
    intro b
    rw [Matrix.mul_apply, Finset.sum_eq_single (esI k r a)]
    · rw [Matrix.conjTranspose_apply, hcol, if_pos rfl, star_one, one_mul, Formalism.FourierDecayAlt.P.Qx3.hpk_row_es]
    · intro i _ hi
      rw [Matrix.conjTranspose_apply, hcol, if_neg hi, star_zero, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [← e1, Matrix.mul_apply, Finset.sum_eq_single (eI k r a)]
  · rw [hrow, if_pos rfl, one_mul]
  · intro b _ hb
    rw [hrow, if_neg hb, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem xi_cell (c : Fin r → ℂ) {g : B.Mat k r} (hg : g ∈ Q.Glev k r (Fin.last r)) (a : Fin r)
    (p : Fin (2 * r + k + 1)) :
    herm (Hpk k r) ((Q.wCell k r (Fin.last r) c * g) *ᵥ bvec p) (bvec (eI k r a)) =
      if p = eI k r a then c a else 0 := by
  rw [herm_eI]
  simp only [bvec, Matrix.mulVec_single_one, Matrix.col_apply]
  rw [Formalism.FourierDecayAlt.P5.Rad.wCell_last_eq, Matrix.mul_apply, Finset.sum_eq_single (eI k r a)]
  · rw [glev_row hg]
    have : bigCell k r c 1 (esI k r a) (eI k r a) = c a := by
      unfold bigCell
      simp [eI, esI]
    rw [this]
    split_ifs <;> simp
  · intro q _ hq
    have : bigCell k r c 1 (esI k r a) q = 0 := by
      unfold bigCell
      have ha := a.isLt
      have hql := q.isLt
      split_ifs
      all_goals first | rfl | (exfalso; simp only [esI, eI, Fin.ext_iff, ne_eq] at *; omega)
    rw [this, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem mono_ge {n : ℕ} {C : Fin r → Fin n} (hC : StrictMono C) : ∀ l : Fin r, l.val ≤ (C l).val := by
  have key : ∀ m, ∀ l : Fin r, l.val = m → m ≤ (C l).val := by
    intro m
    induction m with
    | zero => intro l _; exact Nat.zero_le _
    | succ m ih =>
      intro l hl
      have hm : m < r := by have := l.isLt; omega
      have h1 := ih ⟨m, hm⟩ rfl
      have h2 : C ⟨m, hm⟩ < C l := hC (by rw [Fin.lt_def]; simp; omega)
      rw [Fin.lt_def] at h2
      omega
  exact fun l => key l.val l rfl

theorem mono_le {n : ℕ} {C : Fin r → Fin n} (hC : StrictMono C) (hb : ∀ l, (C l).val < r) :
    ∀ l : Fin r, (C l).val ≤ l.val := by
  have key : ∀ j, ∀ l : Fin r, l.val + j = r - 1 → (C l).val + j ≤ r - 1 := by
    intro j
    induction j with
    | zero => intro l _; have := hb l; omega
    | succ j ih =>
      intro l hl
      have hm : l.val + 1 < r := by omega
      have h1 := ih ⟨l.val + 1, hm⟩ (by simp; omega)
      have h2 : C l < C ⟨l.val + 1, hm⟩ := hC (by rw [Fin.lt_def]; simp)
      rw [Fin.lt_def] at h2
      omega
  intro l
  have := key (r - 1 - l.val) l (by have := l.isLt; omega)
  have := l.isLt
  omega

theorem eq_xR {C : Fin r → Fin (2 * r + k + 1)} (hC : StrictMono C) (hb : ∀ l, (C l).val < r) :
    C = C3.xR k r r le_rfl := by
  funext l
  apply Fin.ext
  have h1 := mono_ge hC l
  have h2 := mono_le hC hb l
  simp only [C3.xR, eI, Fin.val_castLE]
  omega

theorem xR_mono : StrictMono (C3.xR k r r le_rfl) := by
  intro a b h
  simp only [C3.xR, eI, Fin.lt_def, Fin.val_castLE] at h ⊢
  exact h

end cell

section radside

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Q.Mx k r → (Wp →L[ℂ] Wp)} {π' : Q.Mx k r → (Wq →L[ℂ] Wq)}

theorem pOp_loc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (l : Fin r) {f₁ f₂ : (Fin r → ℂ) → E}
    {c : Fin r → ℂ} (hc : c ∈ OmX r) (h : ∀ c' ∈ OmX r, f₁ c' = f₂ c') : pOp l f₁ c = pOp l f₂ c := by
  have he : f₁ =ᶠ[nhds c] f₂ := Filter.eventuallyEq_of_mem ((Formalism.FourierDecayAlt.P.Qx3.isOpen_OmX r).mem_nhds hc) h
  simp only [pOp, wirt, he.fderiv_eq]

theorem radSide_chain (X : Q.ActualOps k r z z' π π') (L : R.LevelData (Q.Pr (Q.RadSp k r z z' π π')) r)
    (hL : Q.IsActualLevel X L) (Y : ℂ) :
    ∀ n, n ≤ r → ∀ (Ψ : Q.RadSp k r z z' π π'), ∀ x ∈ Q.DomR k r z z',
      ((((Formalism.FourierDecayAlt.P.JCx2.rma_pref L Y n) 0 0).1 Ψ : Q.RadSp k r z z' π π') : Q.Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 =
          Q.crd (Q.vAB r Y n).1 (Ψ : Q.Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 ∧
        ((((Formalism.FourierDecayAlt.P.JCx2.rma_pref L Y n) 1 0).1 Ψ : Q.RadSp k r z z' π π') : Q.Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 =
          Q.crd (Q.vAB r Y n).2 (Ψ : Q.Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 := by
  intro n
  induction n with
  | zero =>
    intro _ Ψ x _
    refine ⟨rfl, ?_⟩
    simp [Formalism.FourierDecayAlt.P.JCx2.rma_pref, Q.vAB, Q.crd]
    rfl
  | succ n ih =>
    intro hn Ψ x hx
    have hnr : n < r := by omega
    obtain ⟨hp, -, hc, hci, -⟩ := hL
    have ihA : ∀ c' ∈ OmX r, ((((Formalism.FourierDecayAlt.P.JCx2.rma_pref L Y n) 0 0).1 Ψ : Q.RadSp k r z z' π π') :
        Q.Fn k r (Wq →L[ℂ] Wp)) c' x.2 = (Q.vAB r Y n).1 (fun c'' => (Ψ : Q.Fn k r (Wq →L[ℂ] Wp)) c'' x.2) c' :=
      fun c' hc' => (ih (by omega) Ψ (c', x.2) ⟨hc', hx.2.1, hx.2.2⟩).1
    have ihB : ∀ c' ∈ OmX r, ((((Formalism.FourierDecayAlt.P.JCx2.rma_pref L Y n) 1 0).1 Ψ : Q.RadSp k r z z' π π') :
        Q.Fn k r (Wq →L[ℂ] Wp)) c' x.2 = (Q.vAB r Y n).2 (fun c'' => (Ψ : Q.Fn k r (Wq →L[ℂ] Wp)) c'' x.2) c' :=
      fun c' hc' => (ih (by omega) Ψ (c', x.2) ⟨hc', hx.2.1, hx.2.2⟩).2
    have hA0 := ihA x.1 hx.1
    set product_zeroth_terms := ((Formalism.FourierDecayAlt.P.JCx2.rma_pref L Y n) 0 0).1 Ψ with hP00
    set product_first_zeroth_parts := ((Formalism.FourierDecayAlt.P.JCx2.rma_pref L Y n) 1 0).1 Ψ with hP10
    have eT : Formalism.FourierDecayAlt.P.JCx2.rma_pref L Y (n + 1) = Wd.Ts (P5.site L ⟨n, hnr⟩) Y * Formalism.FourierDecayAlt.P.JCx2.rma_pref L Y n := by
      rw [Formalism.FourierDecayAlt.P.JCx2.rma_pref, dif_pos hnr]
    have e0 : ((Formalism.FourierDecayAlt.P.JCx2.rma_pref L Y (n + 1)) 0 0).1 Ψ = Y • product_zeroth_terms + X.op ⟨n, hnr⟩ 0 product_zeroth_terms - X.op ⟨n, hnr⟩ 1 product_first_zeroth_parts := by
      rw [eT]
      change Formalism.FourierDecayAlt.P.JCx2.rma_fst _ ((Wd.Ts (P5.site L ⟨n, hnr⟩) Y * Formalism.FourierDecayAlt.P.JCx2.rma_pref L Y n) 0 0) Ψ = _
      rw [Matrix.mul_apply, Fin.sum_univ_two]
      simp only [Wd.Ts, YangianSpanCharacter.T.Tm, P5.site, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
      rw [hp, hc]
      simp only [map_add, map_mul, map_neg, AlgHom.commutes, LinearMap.add_apply, LinearMap.neg_apply,
        Module.End.mul_apply, Module.algebraMap_end_apply]
      rw [sub_eq_add_neg]
      rfl
    have e1 : ((Formalism.FourierDecayAlt.P.JCx2.rma_pref L Y (n + 1)) 1 0).1 Ψ = X.op ⟨n, hnr⟩ 2 product_zeroth_terms := by
      rw [eT]
      change Formalism.FourierDecayAlt.P.JCx2.rma_fst _ ((Wd.Ts (P5.site L ⟨n, hnr⟩) Y * Formalism.FourierDecayAlt.P.JCx2.rma_pref L Y n) 1 0) Ψ = _
      rw [Matrix.mul_apply, Fin.sum_univ_two]
      simp only [Wd.Ts, YangianSpanCharacter.T.Tm, P5.site, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
      rw [hci]
      simp only [map_add, map_mul, map_zero, zero_mul, add_zero, Module.End.mul_apply]
      rfl
    rw [e0, e1]
    simp only [Q.vAB, dif_pos hnr, Q.crd]
    simp only [Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
    rw [X.op_apply, X.op_apply, X.op_apply]
    simp only [Q.crd, Formalism.QuantumDeterminants.opL]
    refine ⟨?_, ?_⟩
    · rw [pOp_loc ⟨n, hnr⟩ hx.1 ihA]
      simp only [cOp]
      rw [hA0, ihB x.1 hx.1]
    · simp only [ciOp]
      rw [hA0]

end radside

end Formalism.FourierDecayAlt.P.PBN

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.PBN

theorem radial_side_raising : PBN.RadSideA := by
  intro k r z z' Wp Wq _ _ _ _ _ π π' X L y hL Ψ x hx
  have e : L.Ar y = (Formalism.FourierDecayAlt.P.JCx2.rma_pref L y r) 0 0 := by
    rw [R.LevelData.Ar, Formalism.FourierDecayAlt.P.TLB.rma_pref_take, ← Formalism.FourierDecayAlt.P.TLB.tprod_take_all]
  rw [e]
  exact (radSide_chain X L hL y r le_rfl Ψ x hx).1

end Formalism.FourierDecayAlt.P

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.PBN

theorem raising_cell : PBN.AACell := by
  intro k r E _ _ f u c g hg
  unfold C3.AAop
  rw [Finset.sum_eq_single (C3.xR k r r le_rfl)]
  · rw [if_pos xR_mono]
    congr 1
    have hM : (Matrix.of fun a l : Fin r => herm (Hpk k r) ((Q.wCell k r (Fin.last r) c * g) *ᵥ
        bvec (C3.xR k r r le_rfl l)) (bvec (eI k r (Fin.castLE le_rfl a)))) = Matrix.diagonal c := by
      ext a l
      rw [Matrix.of_apply, xi_cell c hg, Matrix.diagonal_apply]
      by_cases h : a = l
      · subst h; simp [C3.xR]
      · have h' : ¬(C3.xR k r r le_rfl l = eI k r (Fin.castLE le_rfl a)) := by
          intro e
          apply h
          have := congrArg Fin.val e
          simp [C3.xR, eI] at this
          exact Fin.ext this.symm
        simp only [h', h, if_false]
    rw [hM, Matrix.det_diagonal]
  · intro C _ hC
    split_ifs with hm
    · have hex : ∃ l0, r ≤ (C l0).val := by
        by_contra h
        push Not at h
        exact hC (eq_xR hm h)
      obtain ⟨l0, hl0⟩ := hex
      rw [Matrix.det_eq_zero_of_column_eq_zero l0, zero_smul]
      intro a
      rw [Matrix.of_apply, xi_cell c hg, if_neg]
      intro h
      rw [h] at hl0
      simp [eI] at hl0
      omega
    · rfl
  · intro h
    exact absurd (Finset.mem_univ _) h

end Formalism.FourierDecayAlt.P
