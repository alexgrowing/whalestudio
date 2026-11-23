import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ExDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ExistsLocalFirstOrderLifts
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SmoothPtWeightedPresentationOfPointDerivations
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.DerHom
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

noncomputable section SlopeTestRemainingChoices

section Abs

variable {O Q H : Type} [CommRing O] [CommRing Q] [Algebra O Q] [Module Oᵐᵒᵖ Q] [IsCentralScalar O Q] [Group H]

private def tw (Q : Type) [CommRing Q] [Algebra O Q] (A B : M4 O) (q : Q) : M4 (TrivSqZeroExt O Q) :=
  Matrix.of fun i j => TrivSqZeroExt.inl (A i j) + TrivSqZeroExt.inr (B i j • q)

private theorem tw_fst (A B : M4 O) (q : Q) (i j : Fin 4) : (tw Q A B q i j).fst = A i j := by simp [tw]

private theorem tw_snd (A B : M4 O) (q : Q) (i j : Fin 4) : (tw Q A B q i j).snd = B i j • q := by simp [tw]

private theorem tw_one (B : M4 O) : tw Q 1 B 0 = 1 := by
  ext i j
  · rw [tw_fst]; by_cases h : i = j <;> simp [Matrix.one_apply, h]
  · rw [tw_snd]; by_cases h : i = j <;> simp [Matrix.one_apply, h]

private theorem tw_mul (A B A' B' C : M4 O) (q q' : Q) (u : O) (h1 : B * A' = C) (h2 : A * B' = u • C) :
    tw Q (A * A') C (q + u • q') = tw Q A B q * tw Q A' B' q' := by
  ext i j
  · simp [tw_fst, Matrix.mul_apply, TrivSqZeroExt.fst_sum]
  · have e1 := congrFun (congrFun h1 i) j
    have e2 := congrFun (congrFun h2 i) j
    rw [Matrix.mul_apply] at e1 e2
    rw [Matrix.smul_apply, smul_eq_mul] at e2
    simp only [tw_fst, tw_snd, Matrix.mul_apply, TrivSqZeroExt.snd_sum, TrivSqZeroExt.snd_mul, op_smul_eq_smul, smul_smul,
      Finset.sum_add_distrib, ← Finset.sum_smul, smul_add]
    rw [e2, mul_comm u, add_comm, ← e1]
    simp only [mul_comm]

private theorem tw_adj (A B : M4 O) (q : Q) : adj (tw Q A B q) = tw Q (adj A) (adj B) q := by
  ext i j
  · simp only [adj_apply, TrivSqZeroExt.fst_smul, tw_fst]
  · simp only [adj_apply, TrivSqZeroExt.snd_smul, tw_snd, smul_assoc]

private theorem tw_gsp (A B : M4 O) (q : Q) (ν : O) (h1 : IsGSp ν A) (h2 : adj B * A = -(adj A * B)) :
    IsGSp (algebraMap O _ ν) (tw Q A B q) := by
  unfold IsGSp at *
  have h := tw_mul (adj A) (adj B) A B (adj B * A) q q (-1) rfl (by rw [h2]; simp)
  rw [tw_adj, ← h, h1]
  ext i j
  · rw [tw_fst]; by_cases h : i = j <;> simp [Matrix.one_apply, h, TrivSqZeroExt.algebraMap_eq_inl]
  · rw [tw_snd]; by_cases h : i = j <;> simp [Matrix.one_apply, h, TrivSqZeroExt.algebraMap_eq_inl]

private theorem dg_comm (d : Fin 4 → O) (u : O) (h2 : d 2 = u * d 0) (h3 : d 3 = u * d 1) :
    Matrix.diagonal d * Xm O = u • (Xm O * Matrix.diagonal d) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Xm, Matrix.single_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.add_mul, Matrix.mul_add, h2, h3]

private theorem adj_dg (d : Fin 4 → O) : adj (Matrix.diagonal d) = Matrix.diagonal fun i => d i.rev := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev, Matrix.diagonal_apply]

private theorem dg_gsp (d : Fin 4 → O) (ν : O) (h : ∀ i, d i * d i.rev = ν) : IsGSp ν (Matrix.diagonal d) := by
  unfold IsGSp
  rw [adj_dg, Matrix.diagonal_mul_diagonal, Matrix.smul_one_eq_diagonal]
  congr 1
  funext i
  rw [mul_comm, h]

private theorem dg_adj (d : Fin 4 → O) :
    adj (Xm O * Matrix.diagonal d) * Matrix.diagonal d = -(adj (Matrix.diagonal d) * (Xm O * Matrix.diagonal d)) := by
  rw [adj_dg]
  ext i j
  rw [Matrix.neg_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, adj_apply, Matrix.mul_diagonal, Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;> simp [Xm, Matrix.single_apply, sgn, Fin.rev]

private theorem Xm_sp : Xm O ∈ sp4 O := by
  show adj _ = -_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Xm, Fin.rev, Matrix.single_apply]

private theorem Xm_wt (i j : Fin 4) (h : wt i j ≠ -wPs) : Xm O i j = 0 := by
  fin_cases i <;> fin_cases j <;> first | exact absurd (by decide) h | simp [Xm, Matrix.single_apply]

private theorem ac_lc {Γ R : Type} [TopologicalSpace Γ] [CommRing R] (I : Ideal R) {f : Γ → R} (h : IsLocallyConstant f) :
    AdicCont I f := fun _ => h.comp _

private theorem ac_add {Γ R : Type} [TopologicalSpace Γ] [CommRing R] {I : Ideal R} {f g : Γ → R} (h : AdicCont I f)
    (h' : AdicCont I g) : AdicCont I fun x => f x + g x := fun N => by
  simp only [map_add]; exact (h N).add (h' N)

private theorem ac_mul {Γ R : Type} [TopologicalSpace Γ] [CommRing R] {I : Ideal R} {f g : Γ → R} (h : AdicCont I f)
    (h' : AdicCont I g) : AdicCont I fun x => f x * g x := fun N => by
  simp only [map_mul]; exact (h N).mul (h' N)

private theorem ac_map {Γ R : Type} [TopologicalSpace Γ] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R] {f : Γ → O}
    (h : AdicCont (maximalIdeal O) f) : AdicCont (maximalIdeal R) fun x => algebraMap O R (f x) := fun N => by
  have hle : maximalIdeal O ^ N ≤ (maximalIdeal R ^ N).comap (algebraMap O R) := by
    refine le_trans (Ideal.pow_right_mono (fun y hy => ?_) N) (Ideal.le_comap_pow _ N)
    exact fun hu => hy (IsLocalHom.map_nonunit y hu)
  exact (h N).comp (Ideal.quotientMap _ (algebraMap O R) hle)

private theorem ac_dg {Γ : Type} [TopologicalSpace Γ] {I : Ideal O} {d : Γ → Fin 4 → O} (h : ∀ i, AdicCont I fun g => d g i)
    (i j : Fin 4) : AdicCont I fun g => Matrix.diagonal (d g) i j := by
  by_cases e : i = j
  · subst e; simpa using h i
  · simp only [Matrix.diagonal_apply_ne _ e]; exact ac_lc _ (IsLocallyConstant.const _)

private theorem ac_tw {Γ : Type} [TopologicalSpace Γ] [IsLocalRing O] [IsCO O (TrivSqZeroExt O Q)] {A B : Γ → M4 O} {q : Γ → Q}
    (i j : Fin 4) (hA : AdicCont (maximalIdeal O) fun g => A g i j) (hB : AdicCont (maximalIdeal O) fun g => B g i j)
    (hq : IsLocallyConstant q) : AdicCont (maximalIdeal (TrivSqZeroExt O Q)) fun g => tw Q (A g) (B g) (q g) i j := by
  have := ac_add (ac_map (R := TrivSqZeroExt O Q) hA) (ac_mul (ac_map hB) (ac_lc _ (hq.comp TrivSqZeroExt.inr)))
  convert this using 2 with g
  ext <;> simp [tw_fst, tw_snd, TrivSqZeroExt.algebraMap_eq_inl]

private theorem res_fst [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [IsCO O (TrivSqZeroExt O Q)]
    (x : TrivSqZeroExt O Q) : res O _ x = residue O x.fst := by
  rw [← res_map (TrivSqZeroExt.fstHom O O Q) x]
  exact (res O O).commutes _

private def twRep (ps : Fin 4 → H →* Oˣ) (u : H → O) (h2 : ∀ g, (ps 2 g : O) = u g * ps 0 g)
    (h3 : ∀ g, (ps 3 g : O) = u g * ps 1 g) (z : H → Q) (hz : ∀ g h, z (g * h) = z g + u g • z h) (h1 : z 1 = 0) :
    H →* M4 (TrivSqZeroExt O Q) where
  toFun g := tw Q (diagRep ps g) (Xm O * diagRep ps g) (z g)
  map_one' := by rw [map_one, h1, tw_one]
  map_mul' g h := by
    rw [hz, map_mul]
    refine tw_mul _ _ _ _ _ _ _ _ (mul_assoc _ _ _) ?_
    have := dg_comm (fun i => (ps i g : O)) (u g) (h2 g) (h3 g)
    rw [← mul_assoc, ← mul_assoc, ← smul_mul_assoc]
    exact congrArg (· * diagRep ps h) this

end Abs

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c}

private theorem symplectic_integral_one {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R] :
    Sp1 O (1 : M4 R) := by
  refine ⟨?_, Matrix.map_one _ (map_zero _) (map_one _)⟩
  rw [← Matrix.diagonal_one]
  exact dg_gsp _ _ fun _ => mul_one _

private theorem fr_map {L : LocBase D} {R R' : Type} [CommRing R] [Algebra c.O R] [IsCO c.O R] [CommRing R'] [Algebra c.O R']
    [IsCO c.O R'] {i : L.B →ₐ[c.O] R} {r : Lift c.O D.rbar R} (h : IsFr L i r fun _ => 1) (f : R →ₐ[c.O] R') :
    IsFr L (f.comp i) (r.map f) fun _ => 1 := by
  refine ⟨Ex.mult_map D f r h.mult, Ex.unr_map D f r h.unr, fun _ => symplectic_integral_one, rfl, fun v g => ?_⟩
  have := h.loc v g
  rw [mul_one, one_mul] at this ⊢
  ext a b
  rw [Lift.map_hom, this]
  rfl

set_option maxHeartbeats 1000000 in
private theorem main (hD : D.Good) (L : LocBase D) (F : Fr D L) (Q : Type) [CommRing Q] [Algebra c.O Q] [Module c.Oᵐᵒᵖ Q]
    [IsCentralScalar c.O Q] [Module.Finite c.O Q] (z : G ℚ Ω → Q) (lc : IsLocallyConstant z)
    (coc : ∀ g h, z (g * h) = z g + ((D.Psi⁻¹ g : c.Oˣ) : c.O) • z h) (unr : D.UnrT z 0)
    (m : D.T → c.O) (hm : ∀ v : D.T, ∀ g ∈ D.Gp v, z g = algebraMap c.O Q (((D.Psi⁻¹ g : c.Oˣ) : c.O) * m v - m v)) :
    ∃ Db ∈ PtDer (F.W.origin F.org) Q, ∃ DB ∈ PtDer (L.W.origin L.org) c.O, HasWt L.W.part (-wPs) DB ∧
      (∀ x, Db (F.i x) = algebraMap c.O Q (DB x)) ∧ (∀ g i j, Db (F.r.hom g i j) = (Xm c.O * D.r0 g) i j • z g) ∧
      ∀ v i j, Db (F.α v i j) = 0 := by
  haveI : IsCO c.O (TrivSqZeroExt c.O Q) := co_sqz c.O c.O _ fun _ => rfl
  obtain ⟨-, -, f3, -, -, f6, -, -, -, -, f11, -⟩ := facts D hD
  have h1 : z 1 = 0 := by
    have := coc 1 1
    rw [mul_one, map_one, Units.val_one, one_smul] at this
    exact left_eq_add.1 this
  have h2 : ∀ g, (D.ps 2 g : c.O) = ((D.Psi⁻¹ g : c.Oˣ) : c.O) * D.ps 0 g := fun g => by
    rw [← Units.val_mul]
    congr 1
    show D.al g = (D.Psi g)⁻¹ * (D.al g * D.Psi g)
    rw [mul_comm, mul_inv_cancel_right]
  have h3 : ∀ g, (D.ps 3 g : c.O) = ((D.Psi⁻¹ g : c.Oˣ) : c.O) * D.ps 1 g := fun g => by
    rw [← Units.val_mul]
    congr 1
    show 1 = (D.Psi g)⁻¹ * D.Psi g
    rw [inv_mul_cancel]
  have c0 : ∀ i j, AdicCont (maximalIdeal c.O) fun g => D.r0 g i j := ac_dg (d := fun g i => (D.ps i g : c.O)) f11
  let r : Lift c.O D.rbar (TrivSqZeroExt c.O Q) :=
    { hom := twRep D.ps _ h2 h3 z coc h1
      cont := fun i j => ac_tw (A := fun g => D.r0 g) (B := fun g => Xm c.O * D.r0 g) i j (c0 i j) (by
        have e : ∀ g, (Xm c.O * D.r0 g) i j = Xm c.O i j * (D.ps j g : c.O) := fun g => Matrix.mul_diagonal _ _ _ _
        simp only [e]
        exact ac_mul (ac_lc _ (IsLocallyConstant.const _)) (f11 j)) lc
      red := fun g i j => (res_fst _).trans (congrArg (residue c.O) (tw_fst _ _ _ i j)) }
  have hr : ∀ g, r.hom g = tw Q (D.r0 g) (Xm c.O * D.r0 g) (z g) := fun _ => rfl
  obtain ⟨ρ, hρ, hρ'⟩ := UpperTheory.exists_local_first_order_lifts D hD (fun v => (-m v) • Xm c.O) fun v => (sp4 c.O).smul_mem _ Xm_sp
  obtain ⟨yB, hyB, -⟩ := L.univ _ ρ hρ
  have hc : ∀ (v : D.T) (g : G ℚ Ω), (-m v) • Xm c.O * D.r0 g - D.r0 g * (-m v) • Xm c.O =
      (((D.Psi⁻¹ g : c.Oˣ) : c.O) * m v - m v) • (Xm c.O * D.r0 g) := fun v g => by
    have : D.r0 g * Xm c.O = _ • (Xm c.O * D.r0 g) := dg_comm (fun i => (D.ps i g : c.O)) _ (h2 g) (h3 g)
    rw [smul_mul_assoc, mul_smul_comm, this, smul_smul, ← sub_smul]
    congr 1
    ring
  have hy : ∀ (v : D.T) (g : D.Gp v) i j, (yB ((L.ρ v).hom g i j)).fst = D.r0 g i j ∧ (yB ((L.ρ v).hom g i j)).snd =
      (((D.Psi⁻¹ g : c.Oˣ) : c.O) * m v - m v) * (Xm c.O * D.r0 g) i j := fun v g i j => by
    have e : yB ((L.ρ v).hom g i j) = (ρ v).hom g i j := by rw [← hyB v]; rfl
    rw [e, (hρ' v g i j).1, (hρ' v g i j).2, hc]
    exact ⟨rfl, rfl⟩
  obtain ⟨w1, w2⟩ := UpperTheory.smoothPt_weightedPresentation_of_pointDerivations D hD L yB (-wPs) fun v g i j => ⟨(hy v g i j).1, fun h => by
    have e : (Xm c.O * D.r0 g) i j = Xm c.O i j * (D.ps j g : c.O) := Matrix.mul_diagonal _ _ _ _
    rw [(hy v g i j).2, e, Xm_wt i j h, zero_mul, mul_zero]⟩
  let p : DualNumber c.O →ₐ[c.O] TrivSqZeroExt c.O Q := TrivSqZeroExt.map (Algebra.linearMap c.O Q)
  have p1 : ∀ x, (p x).fst = x.fst := fun x => TrivSqZeroExt.fst_map _ x
  have p2 : ∀ x, (p x).snd = algebraMap c.O Q x.snd := fun x => TrivSqZeroExt.snd_map _ x
  have hF : IsFr L (p.comp yB) r fun _ => 1 := by
    refine ⟨fun g => ?_, fun A hA g hg hg' => ?_, fun _ => symplectic_integral_one, rfl, fun v g => ?_⟩
    · rw [hr]
      refine tw_gsp _ _ _ _ (dg_gsp (fun i => (D.ps i g : c.O)) _ fun i => ?_) (dg_adj fun i => (D.ps i g : c.O))
      rw [← f6 i]; rfl
    · have e : D.r0 g = 1 := by
        show Matrix.diagonal (fun i => (D.ps i g : c.O)) = 1
        simp only [fun i => f3 i A hA g hg hg', Units.val_one, Matrix.diagonal_one]
      rw [hr, unr A hA g hg hg', e, tw_one]
    · rw [mul_one, one_mul, hr]
      refine Matrix.ext fun i j => TrivSqZeroExt.ext ?_ ?_
      · rw [tw_fst, Matrix.map_apply, AlgHom.comp_apply, p1, (hy v g i j).1]
      · rw [tw_snd, Matrix.map_apply, AlgHom.comp_apply, p2, (hy v g i j).2, hm v g g.2, map_mul, Algebra.smul_def, mul_comm]
  obtain ⟨y, ⟨y1, y2, y3⟩, -⟩ := F.univ _ _ _ _ hF
  have y2' : ∀ g i j, y (F.r.hom g i j) = tw Q (D.r0 g) (Xm c.O * D.r0 g) (z g) i j := fun g i j => by
    rw [← hr, ← y2]; rfl
  have y3' : ∀ v i j, y (F.α v i j) = (1 : M4 (TrivSqZeroExt c.O Q)) i j := fun v i j => congrFun (congrFun (y3 v) i) j
  let q : TrivSqZeroExt c.O Q →ₐ[c.O] c.O := TrivSqZeroExt.fstHom c.O c.O Q
  have hq : ∀ x, q x = x.fst := fun _ => rfl
  have hfst : q.comp y = F.W.origin F.org := by
    refine (F.univ _ _ _ _ (fr_map hF q)).unique ⟨by rw [AlgHom.comp_assoc, y1], by rw [← y2]; rfl, fun v => ?_⟩
      ⟨?_, Lift.ext (MonoidHom.ext fun g => Matrix.ext fun i j => ?_), F.at0α⟩
    · ext i j : 1
      rw [Matrix.map_apply, AlgHom.comp_apply, y3']
      by_cases h : i = j <;> simp [Matrix.one_apply, h]
    · rw [F.at0i]
      refine AlgHom.ext fun x => ?_
      rw [AlgHom.comp_apply, AlgHom.comp_apply, hq, p1, w1]
    · rw [Lift.map_hom, Lift.map_hom, F.at0r, hr, hq, tw_fst]
  obtain ⟨Db, hDb, e1⟩ := (der_hom c.O F.U c.O Q (F.W.origin F.org) fun x => (y x).snd).2
    ⟨y, fun x => ⟨by rw [← hfst]; rfl, rfl⟩⟩
  obtain ⟨DB, hDB, e2⟩ := (der_hom c.O L.B c.O c.O (L.W.origin L.org) fun x => (yB x).snd).2
    ⟨yB, fun x => ⟨w1 x, rfl⟩⟩
  refine ⟨Db, hDb, DB, hDB, fun i hi x hx => ?_, fun x => ?_, fun g i j => ?_, fun v i j => ?_⟩
  · rw [e2]; exact w2 i hi x hx
  · rw [e1, e2]
    show ((y.comp F.i) x).snd = _
    rw [y1, AlgHom.comp_apply, p2]
  · rw [e1]
    show (y _).snd = _
    rw [y2', tw_snd]
  · rw [e1]
    show (y _).snd = _
    rw [y3']
    by_cases h : i = j <;> simp [Matrix.one_apply, h]

end SlopeTestRemainingChoices

theorem UpperTheory.exists_quotientDerivation_of_shaCocycle :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (L : LocBase D) (F : Fr D L) (a : c.O) (z : G ℚ Ω → c.O ⧸ Ideal.span {a}), D.ShaCoc a z → ∃ Db ∈ QDer (F.W.origin F.org) a, ∃ DB ∈ PtDer (L.W.origin L.org) c.O, HasWt L.W.part (-wPs) DB ∧ (∀ x, Db (F.i x) = Ideal.Quotient.mk _ (DB x)) ∧ (∀ g i j, Db (F.r.hom g i j) = Ideal.Quotient.mk _ ((Xm c.O * D.r0 g) i j) * z g) ∧ ∀ v i j, Db (F.α v i j) = 0 := by
  intro Ω _ _ _ l _ c D hD L F a z hz
  have hm : ∀ v : D.T, ∃ m : c.O, ∀ g ∈ D.Gp v, z g = algebraMap c.O (c.O ⧸ Ideal.span {a}) (((D.Psi⁻¹ g : c.Oˣ) : c.O) * m - m) :=
    fun v => by
      obtain ⟨m, hm⟩ := hz.loc v v.2
      obtain ⟨m, rfl⟩ := Ideal.Quotient.mk_surjective m
      exact ⟨m, fun g hg => by rw [hm g hg, map_sub, map_mul]; rfl⟩
  choose m hm using hm
  obtain ⟨Db, h1, DB, h2, h3, h4, h5, h6⟩ := main hD L F (c.O ⧸ Ideal.span {a}) z hz.lc
    (fun g h => by rw [hz.coc, Algebra.smul_def]; rfl) hz.unr m hm
  exact ⟨Db, h1, DB, h2, h3, h4, fun g i j => by rw [h5, Algebra.smul_def]; rfl, h6⟩
