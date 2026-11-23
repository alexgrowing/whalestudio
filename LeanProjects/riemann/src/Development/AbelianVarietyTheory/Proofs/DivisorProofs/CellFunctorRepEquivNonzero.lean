import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
open GlobalTheory.PRep GlobalTheory.SmGL Matrix

noncomputable section

namespace GlobalTheory.CellDetSecond

open scoped TensorProduct

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private def valEquiv {β : Type} {n : β → ℕ} {t : ℕ} (a₀ : β) (ha₀ : n a₀ = t) (h0 : ∀ j, j ≠ a₀ → n j = 0) :
    (Σ j, Fin (n j)) ≃ Fin t where
  toFun p := ⟨p.2.val, by
    by_cases hp : p.1 = a₀
    · have h1 := p.2.2
      have h2 : n p.1 = t := hp ▸ ha₀
      omega
    · have h1 := p.2.2
      have h2 := h0 _ hp
      omega⟩
  invFun x := ⟨a₀, ⟨x.val, by have := x.2; omega⟩⟩
  left_inv p := by
    obtain ⟨a, s⟩ := p
    by_cases ha : a = a₀
    · subst ha
      rfl
    · have h1 := s.2
      have h2 := h0 _ ha
      omega
  right_inv x := rfl

private theorem mem_parab_of_single {R : Type} [CommRing R] {β : Type} [LinearOrder β] {n : β → ℕ} {t : ℕ}
    (e : (Σ j, Fin (n j)) ≃ Fin t) (a₀ : β) (h0 : ∀ j, j ≠ a₀ → n j = 0) (x : GL (Fin t) R) :
    x ∈ parab R e := by
  refine mem_parab_iff.2 fun a b i j hab => ?_
  by_cases ha : a = a₀
  · have hb : b ≠ a₀ := fun e => by rw [e, ha] at hab; exact lt_irrefl _ hab
    exact absurd j.2 (by have := j.2; have := h0 b hb; omega)
  · exact absurd i.2 (by have := i.2; have := h0 a ha; omega)

private theorem extTensor_detRep_apply {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    (χ ψ : kˣ →* ℂˣ) (x : GL n k × GL n' k) (v : ℂ ⊗[ℂ] ℂ) :
    extTensor (detRep n χ) (detRep n' ψ) x v =
      ((χ (Matrix.GeneralLinearGroup.det x.1) * ψ (Matrix.GeneralLinearGroup.det x.2) : ℂˣ) : ℂ) • v := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul u w =>
    rw [extTensor_tmul]
    simp only [detRep, ofChar_apply, detChar_apply, Units.val_mul]
    rw [← smul_eq_mul, ← smul_eq_mul (a := ((ψ _ : ℂˣ) : ℂ)), TensorProduct.smul_tmul_smul]
  | add u w hu hw => rw [map_add, hu, hw, smul_add]

private def equivOfBij {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (f : ρ.IntertwiningMap σ)
    (hf : Function.Bijective f) : ρ.Equiv σ :=
  Representation.Equiv.mk (LinearEquiv.ofBijective f.toLinearMap hf) f.isIntertwining'

private theorem card_two_false' (a b : Type) [Fintype a] [Fintype b] :
    Fintype.card (Two a b false) = Fintype.card a := rfl

private theorem card_two_true' (a b : Type) [Fintype a] [Fintype b] :
    Fintype.card (Two a b true) = Fintype.card b := rfl

private def sizeSecond (u v : ℕ) : SizeMatrix (Two (Fin (u + 1)) (Fin v)) (Two (Fin (u + v)) (Fin 1)) :=
  ⟨fun i j => cond i (cond j 0 v) (cond j 1 u), by
    refine ⟨fun i => ?_, fun j => ?_⟩
    · cases i <;> simp [Fintype.sum_bool, card_two_false', card_two_true'] <;> omega
    · cases j <;> simp [Fintype.sum_bool, card_two_false', card_two_true'] <;> omega⟩

private theorem eq_sizeSecond {u v : ℕ} (b : SizeMatrix (Two (Fin (u + 1)) (Fin v)) (Two (Fin (u + v)) (Fin 1)))
    (h : b.1 false true = 1) : b = sizeSecond u v := by
  have r0 := b.2.1 false
  have r1 := b.2.1 true
  have c1 := b.2.2 true
  simp only [Fintype.sum_bool, card_two_false', card_two_true', Fintype.card_fin] at r0 r1 c1
  refine Subtype.ext (funext fun i => funext fun j => ?_)
  cases i <;> cases j <;> simp [sizeSecond] <;> omega

private def colFalse (u v : ℕ) : (Σ i, Fin ((sizeSecond u v).1 i false)) ≃ Fin (u + v) :=
  (Equiv.sigmaCongrRight (β₂ := Two (Fin u) (Fin v)) fun i => match i with
    | false => Equiv.refl (Fin u)
    | true => Equiv.refl (Fin v)).trans (two (stdSum rfl))

private def colEq (u v : ℕ) : ∀ j, (Σ i, Fin ((sizeSecond u v).1 i j)) ≃ Two (Fin (u + v)) (Fin 1) j
  | false => colFalse u v
  | true => valEquiv (n := fun i => (sizeSecond u v).1 i true) false rfl
      (fun i hi => by cases i <;> simp_all [sizeSecond])

private def rowEq (u v : ℕ) : ∀ i, (Σ j, Fin ((sizeSecond u v).1 i j)) ≃ Two (Fin (u + 1)) (Fin v) i :=
  (sizeSecond u v).nonempty_rows.some

private theorem blk_colFalse (u v : ℕ) (x : Fin (u + v)) :
    blk (colFalse u v) x = blk (two (stdSum (rfl : u + v = u + v))) x := by
  simp only [blk, colFalse, Equiv.symm_trans_apply]
  rcases (two (stdSum (rfl : u + v = u + v))).symm x with ⟨a, y⟩
  rfl

private theorem mem_relParab_colEq {u v : ℕ} (x : Levi k (Two (Fin (u + v)) (Fin 1))) :
    x ∈ relParab k (colEq u v) ↔ x false ∈ parab k (two (stdSum (rfl : u + v = u + v))) := by
  constructor
  · intro h
    have h1 : x false ∈ parab k (colFalse u v) := h false trivial
    refine mem_parab.2 fun i j hij => mem_parab.1 h1 i j ?_
    rwa [blk_colFalse, blk_colFalse]
  · intro h j _
    cases j
    · refine mem_parab.2 fun i i' hij => mem_parab.1 h i i' ?_
      rwa [← blk_colFalse, ← blk_colFalse]
    · exact mem_parab_of_single _ false (fun i hi => by cases i <;> simp_all [sizeSecond]) _

private theorem relProj_colEq_ff {u v : ℕ} (p : relParab k (colEq u v)) :
    (relProj k (colEq u v) p false false : GL (Fin u) k) =
      leviProj k (two (stdSum (rfl : u + v = u + v))) ⟨p.1 false, (mem_relParab_colEq _).1 p.2⟩ false := by
  ext a b; rfl

private theorem relProj_colEq_ft {u v : ℕ} (p : relParab k (colEq u v)) :
    (relProj k (colEq u v) p false true : GL (Fin v) k) =
      leviProj k (two (stdSum (rfl : u + v = u + v))) ⟨p.1 false, (mem_relParab_colEq _).1 p.2⟩ true := by
  ext a b; rfl

private theorem det_relProj_tf {u v : ℕ} (p : relParab k (colEq u v)) :
    GeneralLinearGroup.det (relProj k (colEq u v) p true false : GL (Fin 1) k) =
      GeneralLinearGroup.det (p.1 true) := by
  have h := det_parab k (colEq u v true) ⟨p.1 true, p.2 true trivial⟩
  rw [h, Fintype.prod_bool]
  have h0 : GeneralLinearGroup.det (leviProj k (colEq u v true) ⟨p.1 true, p.2 true trivial⟩ true) = 1 := by
    haveI : IsEmpty (Fin ((sizeSecond u v).1 true true)) := ⟨fun x => Fin.elim0 x⟩
    ext
    simp [Matrix.det_isEmpty]
  rw [h0, one_mul]
  rfl

private abbrev rhoM (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ) :
    Representation ℂ (Levi k (Two (Fin (u + 1)) (Fin v))) (ℂ ⊗[ℂ] ℂ) :=
  (extTensor (detRep (Fin (u + 1)) χ₁) (detRep (Fin v) χ₂)).comp
    (leviTwo k (Fin (u + 1)) (Fin v)).symm.toMonoidHom

private theorem rhoM_apply (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ) (y : Levi k (Two (Fin (u + 1)) (Fin v)))
    (w : ℂ ⊗[ℂ] ℂ) :
    rhoM χ₁ χ₂ u v y w = ((χ₁ (GeneralLinearGroup.det (y false)) *
      χ₂ (GeneralLinearGroup.det (y true)) : ℂˣ) : ℂ) • w :=
  extTensor_detRep_apply χ₁ χ₂ _ w

private theorem twKer_rhoM (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ) :
    twKer (rhoM (k := k) χ₁ χ₂ u v) (relUnip k (rowEq u v)) 1 = ⊥ := by
  refine Submodule.span_eq_bot.2 ?_
  rintro _ ⟨n, w, rfl⟩
  have hd : ∀ i, GeneralLinearGroup.det ((n : Levi k (Two (Fin (u + 1)) (Fin v))) i) = 1 :=
    fun i => det_eq_one_of_mem_unipRad k (n.2 i trivial)
  simp only [MonoidHom.one_apply, Units.val_one, one_smul, sub_eq_zero]
  refine (rhoM_apply χ₁ χ₂ u v (n : Levi k (Two (Fin (u + 1)) (Fin v))) w).trans ?_
  simp [hd]

private abbrev sigmaC (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ) :=
  (twist ((relJac (rowEq u v) (rhoM (k := k) χ₁ χ₂ u v)).comp
        (swapBlocks k (fun i j => Fin ((sizeSecond u v).1 i j))))
      (relDeltaHalf k (fun j i => Fin ((sizeSecond u v).1 i j)))).comp (relProj k (colEq u v))

private theorem sigmaC_mk_scalar : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ) (p : relParab k (colEq u v)) (w : ℂ ⊗[ℂ] ℂ),
    sigmaC χ₁ χ₂ u v p (Submodule.Quotient.mk w) =
    (((χ₁ * absPow k ((u : ℂ) / 2)) (GeneralLinearGroup.det (p.1 true)) *
      deltaHalf k (Two (Fin u) (Fin v))
        (leviProj k (two (stdSum (rfl : u + v = u + v))) ⟨p.1 false, (mem_relParab_colEq _).1 p.2⟩) *
      ((χ₁ * absPow k (-(1 / 2))) (GeneralLinearGroup.det (leviProj k (two (stdSum (rfl : u + v = u + v)))
          ⟨p.1 false, (mem_relParab_colEq _).1 p.2⟩ false)) *
        χ₂ (GeneralLinearGroup.det (leviProj k (two (stdSum (rfl : u + v = u + v)))
          ⟨p.1 false, (mem_relParab_colEq _).1 p.2⟩ true))) : ℂˣ) : ℂ) • Submodule.Quotient.mk w := by
  intro k _ _ _ _ χ₁ χ₂ u v p w
  have hb : ¬ (true < false) := by decide
  have m1 : modExp (fun i => Fin ((sizeSecond u v).1 i true)) true = -1 := by simp [modExp, Finset.sum_filter, sizeSecond, hb] <;> exact (Fintype.card_congr' rfl).trans (Fintype.card_fin _)
  have m2 : modExp (fun i => Fin ((sizeSecond u v).1 i true)) false = 0 := by simp [modExp, Finset.sum_filter, sizeSecond, hb] <;> exact (Fintype.card_congr' rfl).trans (Fintype.card_fin _)
  have m3 : modExp (fun i => Fin ((sizeSecond u v).1 i false)) true = -(u : ℤ) := by simp [modExp, Finset.sum_filter, sizeSecond, hb] <;> exact (Fintype.card_congr' rfl).trans (Fintype.card_fin _)
  have m4 : modExp (fun i => Fin ((sizeSecond u v).1 i false)) false = v := by simp [modExp, Finset.sum_filter, sizeSecond, hb] <;> exact (Fintype.card_congr' rfl).trans (Fintype.card_fin _)
  have m5 : modExp (fun j => Fin ((sizeSecond u v).1 true j)) true = -(v : ℤ) := by simp [modExp, Finset.sum_filter, sizeSecond, hb] <;> exact (Fintype.card_congr' rfl).trans (Fintype.card_fin _)
  have m6 : modExp (fun j => Fin ((sizeSecond u v).1 true j)) false = 0 := by simp [modExp, Finset.sum_filter, sizeSecond, hb] <;> exact (Fintype.card_congr' rfl).trans (Fintype.card_fin _)
  have m7 : modExp (fun j => Fin ((sizeSecond u v).1 false j)) true = -(u : ℤ) := by simp [modExp, Finset.sum_filter, sizeSecond, hb] <;> exact (Fintype.card_congr' rfl).trans (Fintype.card_fin _)
  have m8 : modExp (fun j => Fin ((sizeSecond u v).1 false j)) false = 1 := by simp [modExp, Finset.sum_filter, sizeSecond, hb] <;> exact (Fintype.card_congr' rfl).trans (Fintype.card_fin _)
  have m9 : modExp (Two (Fin u) (Fin v)) false = v := by simp [modExp, Finset.sum_filter]
  have m10 : modExp (Two (Fin u) (Fin v)) true = -(u : ℤ) := by simp [modExp, Finset.sum_filter]
  have hs : ∀ i j, swapBlocks k (fun i j => Fin ((sizeSecond u v).1 i j)) (relProj k (colEq u v) p) i j =
      relProj k (colEq u v) p j i := fun _ _ => rfl
  have e0 : GeneralLinearGroup.det (relProj k (colEq u v) p true true) = 1 := by
    haveI : IsEmpty (Fin ((sizeSecond u v).1 true true)) := ⟨fun x => Fin.elim0 x⟩
    ext
    simp [Matrix.det_isEmpty]
  have d00 : GeneralLinearGroup.det (relProj k (colEq u v) p false false) =
      GeneralLinearGroup.det (leviProj k (two (stdSum (rfl : u + v = u + v)))
        ⟨p.1 false, (mem_relParab_colEq _).1 p.2⟩ false) := by
    first | exact congrArg GeneralLinearGroup.det (relProj_colEq_ff p) | (rw [relProj_colEq_ff] <;> rfl)
  have d01 : GeneralLinearGroup.det (relProj k (colEq u v) p false true) =
      GeneralLinearGroup.det (leviProj k (two (stdSum (rfl : u + v = u + v)))
        ⟨p.1 false, (mem_relParab_colEq _).1 p.2⟩ true) := by
    first | exact congrArg GeneralLinearGroup.det (relProj_colEq_ft p) | (rw [relProj_colEq_ft] <;> rfl)
  rw [MonoidHom.comp_apply, twist_apply, MonoidHom.comp_apply, relJac_mk, rhoM_apply, Submodule.Quotient.mk_smul,
    smul_smul, smul_smul]
  congr 1
  simp only [← Units.val_mul]
  congr 1
  rw [relDeltaHalf_apply, relDeltaHalf_apply, Fintype.prod_bool, Fintype.prod_bool]
  simp only [deltaHalf_apply, Fintype.prod_bool, relEmb_apply, det_leviEmb, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, hs,
    e0, d00, d01, det_relProj_tf, map_one, mul_one, one_mul, map_mul, MonoidHom.mul_apply, Int.cast_zero, zero_div,
    absPow_zero, MonoidHom.one_apply, Int.cast_one, Int.cast_neg, Int.cast_natCast]
  simp only [neg_div, absPow_neg, MonoidHom.inv_apply, mul_inv, inv_inv]
  have key : ∀ (x y z q d f e : ℂˣ), x * y * (z * q) * (f * e * d) = f * z * (x * y) * (e * q * d) := by
    intro x y z q d f e
    ac_rfl
  exact key _ _ _ _ _ _ _

private theorem inducing_mk (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ) (p : relParab k (colEq u v)) (w : ℂ ⊗[ℂ] ℂ) :
    sigmaC χ₁ χ₂ u v p (Submodule.Quotient.mk w) =
    (((χ₁ * absPow k ((u : ℂ) / 2)) (GeneralLinearGroup.det (p.1 true)) *
      deltaHalf k (Two (Fin u) (Fin v))
        (leviProj k (two (stdSum (rfl : u + v = u + v))) ⟨p.1 false, (mem_relParab_colEq _).1 p.2⟩) *
      ((χ₁ * absPow k (-(1 / 2))) (GeneralLinearGroup.det (leviProj k (two (stdSum (rfl : u + v = u + v)))
          ⟨p.1 false, (mem_relParab_colEq _).1 p.2⟩ false)) *
        χ₂ (GeneralLinearGroup.det (leviProj k (two (stdSum (rfl : u + v = u + v)))
          ⟨p.1 false, (mem_relParab_colEq _).1 p.2⟩ true))) : ℂˣ) : ℂ) • Submodule.Quotient.mk w :=
  sigmaC_mk_scalar χ₁ χ₂ u v p w

private abbrev rhoL (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ) :
    Representation ℂ (Levi k (Two (Fin u) (Fin v))) (ℂ ⊗[ℂ] ℂ) :=
  (extTensor (detRep (Fin u) (χ₁ * absPow k (-(1 / 2)))) (detRep (Fin v) χ₂)).comp
    (leviTwo k (Fin u) (Fin v)).symm.toMonoidHom

private def toFun (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ)
    (φ : IndSp (two (stdSum (rfl : u + v = u + v))) (rhoL (k := k) χ₁ χ₂ u v))
    (x : Levi k (Two (Fin (u + v)) (Fin 1))) :
    Jacquet (rhoM (k := k) χ₁ χ₂ u v) (relUnip k (rowEq u v)) :=
  (((χ₁ * absPow k ((u : ℂ) / 2)) (GeneralLinearGroup.det (x true)) : ℂˣ) : ℂ) •
    Submodule.Quotient.mk (φ.1.1 (x false))

private theorem toFun_law (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ)
    (φ : IndSp (two (stdSum (rfl : u + v = u + v))) (rhoL (k := k) χ₁ χ₂ u v))
    (p : relParab k (colEq u v)) (x : Levi k (Two (Fin (u + v)) (Fin 1))) :
    toFun χ₁ χ₂ u v φ ((p : Levi k (Two (Fin (u + v)) (Fin 1))) * x) =
      sigmaC χ₁ χ₂ u v p (toFun χ₁ χ₂ u v φ x) := by
  have hq := (mem_relParab_colEq (p : Levi k (Two (Fin (u + v)) (Fin 1)))).1 p.2
  have h1 := parInd_law (two (stdSum (rfl : u + v = u + v))) (rhoL χ₁ χ₂ u v) φ ⟨_, hq⟩ (x false)
  have h2 : rhoL χ₁ χ₂ u v (leviProj k (two (stdSum (rfl : u + v = u + v))) ⟨_, hq⟩) (φ.1.1 (x false)) =
      (((χ₁ * absPow k (-(1 / 2))) (GeneralLinearGroup.det (leviProj k (two (stdSum (rfl : u + v = u + v))) ⟨_, hq⟩ false)) *
        χ₂ (GeneralLinearGroup.det
          (leviProj k (two (stdSum (rfl : u + v = u + v))) ⟨_, hq⟩ true)) : ℂˣ) : ℂ) • φ.1.1 (x false) :=
    extTensor_detRep_apply (χ₁ * absPow k (-(1 / 2))) χ₂ _ _
  unfold toFun
  rw [map_smul, inducing_mk]
  show (((χ₁ * absPow k ((u : ℂ) / 2)) (GeneralLinearGroup.det (p.1 true * x true)) : ℂˣ) : ℂ) •
    Submodule.Quotient.mk (φ.1.1 (p.1 false * x false)) = _
  rw [h1, h2]
  rw [map_mul, map_mul, Submodule.Quotient.mk_smul, Submodule.Quotient.mk_smul, smul_smul, smul_smul,
    smul_smul]
  congr 1
  simp only [Units.val_mul]
  ring

private theorem toFun_smooth {χ₁ χ₂ : kˣ →* ℂˣ} (hχ₁ : IsSmoothChar χ₁) (u v : ℕ)
    (φ : IndSp (two (stdSum (rfl : u + v = u + v))) (rhoL (k := k) χ₁ χ₂ u v)) :
    (⟨toFun χ₁ χ₂ u v φ, fun p x => toFun_law χ₁ χ₂ u v φ p x⟩ :
      indSpace (relParab k (colEq u v)) (sigmaC χ₁ χ₂ u v)) ∈
        smoothPart (ind (relParab k (colEq u v)) (sigmaC χ₁ χ₂ u v)) := by
  have hc : IsSmoothChar (χ₁ * absPow k ((u : ℂ) / 2)) :=
    hχ₁.mul (isSmoothChar_of_isUnram (isUnram_absPow k _))
  have hd := (hc.detChar (n := Fin 1)).comp
    (Pi.evalMonoidHom (fun j => GL (Two (Fin (u + v)) (Fin 1) j) k) true) (continuous_apply true)
  have hφ : IsOpen {g : GL (Fin (u + v)) k | ind _ _ g φ.1 = φ.1} := φ.2
  refine mem_smoothPart_of_nhds (Filter.mem_of_superset
    (((hφ.preimage (continuous_apply false)).inter hd).mem_nhds ⟨by simp, by simp⟩) ?_)
  rintro y ⟨hy1, hy2⟩
  have hy2' : (χ₁ * absPow k ((u : ℂ) / 2)) (GeneralLinearGroup.det (y true)) = 1 := MonoidHom.mem_ker.1 hy2
  refine Subtype.ext (funext fun x => ?_)
  show toFun χ₁ χ₂ u v φ (x * y) = toFun χ₁ χ₂ u v φ x
  have h3 : φ.1.1 (x false * y false) = φ.1.1 (x false) :=
    congrArg (fun F => F.1 (x false)) (show ind _ _ (y false) φ.1 = φ.1 from hy1)
  unfold toFun
  rw [Pi.mul_apply, Pi.mul_apply, h3, map_mul, map_mul, hy2', mul_one]

private def toCell {χ₁ χ₂ : kˣ →* ℂˣ} (hχ₁ : IsSmoothChar χ₁) (u v : ℕ) :
    IndSp (two (stdSum (rfl : u + v = u + v))) (rhoL (k := k) χ₁ χ₂ u v) →ₗ[ℂ]
      smoothPart (ind (relParab k (colEq u v)) (sigmaC (k := k) χ₁ χ₂ u v)) where
  toFun φ := ⟨⟨toFun χ₁ χ₂ u v φ, fun p x => toFun_law χ₁ χ₂ u v φ p x⟩, toFun_smooth hχ₁ u v φ⟩
  map_add' φ ψ := Subtype.ext (Subtype.ext (funext fun x => by
    show toFun χ₁ χ₂ u v (φ + ψ) x = toFun χ₁ χ₂ u v φ x + toFun χ₁ χ₂ u v ψ x
    simp only [toFun]
    rw [← smul_add, ← Submodule.Quotient.mk_add]
    rfl))
  map_smul' c φ := Subtype.ext (Subtype.ext (funext fun x => by
    show toFun χ₁ χ₂ u v (c • φ) x = c • toFun χ₁ χ₂ u v φ x
    simp only [toFun]
    rw [smul_comm, ← Submodule.Quotient.mk_smul]
    rfl))

private theorem toCell_apply {χ₁ χ₂ : kˣ →* ℂˣ} (hχ₁ : IsSmoothChar χ₁) (u v : ℕ)
    (φ : IndSp (two (stdSum (rfl : u + v = u + v))) (rhoL (k := k) χ₁ χ₂ u v)) (x) :
    (toCell hχ₁ u v φ).1.1 x = toFun χ₁ χ₂ u v φ x := rfl

private theorem toCell_injective {χ₁ χ₂ : kˣ →* ℂˣ} (hχ₁ : IsSmoothChar χ₁) (u v : ℕ) :
    Function.Injective (toCell (k := k) (χ₂ := χ₂) hχ₁ u v) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro φ hφ
  refine Subtype.ext (Subtype.ext (funext fun x₁ => ?_))
  have h := congrArg (fun F => F.1.1 (leviTwo k (Fin (u + v)) (Fin 1) (x₁, 1))) hφ
  simp only [toCell_apply] at h
  have h' : (Submodule.Quotient.mk (φ.1.1 x₁) :
      Jacquet (rhoM (k := k) χ₁ χ₂ u v) (relUnip k (rowEq u v))) = 0 := by
    have e : toFun χ₁ χ₂ u v φ (leviTwo k (Fin (u + v)) (Fin 1) (x₁, 1)) =
        Submodule.Quotient.mk (φ.1.1 x₁) := by
      unfold toFun
      show ((((χ₁ * absPow k ((u : ℂ) / 2)) (GeneralLinearGroup.det (1 : GL (Fin 1) k)) : ℂˣ) : ℂ) • _) = _
      rw [map_one, map_one, Units.val_one, one_smul]
      rfl
    rw [← e]
    exact h
  rw [Submodule.Quotient.mk_eq_zero, twKer_rhoM, Submodule.mem_bot] at h'
  exact h'

private abbrev CellSp (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ) : Type :=
  smoothPart (ind (relParab k (colEq u v)) (sigmaC (k := k) χ₁ χ₂ u v))

private def incl (u v : ℕ) : GL (Fin (u + v)) k →* Levi k (Two (Fin (u + v)) (Fin 1)) :=
  (leviTwo k (Fin (u + v)) (Fin 1)).toMonoidHom.comp (MonoidHom.inl _ _)

private theorem incl_false (u v : ℕ) (x₁ : GL (Fin (u + v)) k) : incl u v x₁ false = x₁ := rfl

private theorem incl_true (u v : ℕ) (x₁ : GL (Fin (u + v)) k) : incl u v x₁ true = 1 := rfl

private def restr (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ) (Φ : CellSp (k := k) χ₁ χ₂ u v) (x₁ : GL (Fin (u + v)) k) :
    ℂ ⊗[ℂ] ℂ :=
  Submodule.quotEquivOfEqBot _ (twKer_rhoM (k := k) χ₁ χ₂ u v) (Φ.1.1 (incl u v x₁))

private theorem mk_restr (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ) (Φ : CellSp (k := k) χ₁ χ₂ u v) (x₁ : GL (Fin (u + v)) k) :
    (Submodule.Quotient.mk (restr χ₁ χ₂ u v Φ x₁) :
      Jacquet (rhoM (k := k) χ₁ χ₂ u v) (relUnip k (rowEq u v))) = Φ.1.1 (incl u v x₁) :=
  (Submodule.quotEquivOfEqBot _ (twKer_rhoM (k := k) χ₁ χ₂ u v)).symm_apply_apply _

private theorem restr_law (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ) (Φ : CellSp (k := k) χ₁ χ₂ u v)
    (q : parab k (two (stdSum (rfl : u + v = u + v)))) (x₁ : GL (Fin (u + v)) k) :
    restr χ₁ χ₂ u v Φ ((q : GL (Fin (u + v)) k) * x₁) =
      ((twist (rhoL (k := k) χ₁ χ₂ u v) (deltaHalf k (Two (Fin u) (Fin v)))).comp
        (leviProj k (two (stdSum (rfl : u + v = u + v))))) q (restr χ₁ χ₂ u v Φ x₁) := by
  have hmem : incl u v (q : GL (Fin (u + v)) k) ∈ relParab k (colEq u v) := (mem_relParab_colEq _).2 q.2
  have h1 : Φ.1.1 (incl u v (q : GL (Fin (u + v)) k) * incl u v x₁) =
      sigmaC χ₁ χ₂ u v ⟨_, hmem⟩ (Φ.1.1 (incl u v x₁)) := Φ.1.2 ⟨_, hmem⟩ (incl u v x₁)
  have h2 : rhoL χ₁ χ₂ u v (leviProj k (two (stdSum (rfl : u + v = u + v))) q) (restr χ₁ χ₂ u v Φ x₁) =
      (((χ₁ * absPow k (-(1 / 2))) (GeneralLinearGroup.det (leviProj k (two (stdSum (rfl : u + v = u + v))) q false)) *
        χ₂ (GeneralLinearGroup.det
          (leviProj k (two (stdSum (rfl : u + v = u + v))) q true)) : ℂˣ) : ℂ) • restr χ₁ χ₂ u v Φ x₁ :=
    extTensor_detRep_apply (χ₁ * absPow k (-(1 / 2))) χ₂ _ _
  rw [MonoidHom.comp_apply, twist_apply, h2, smul_smul]
  unfold restr
  rw [map_mul, h1, ← mk_restr χ₁ χ₂ u v Φ x₁, inducing_mk, map_smul]
  unfold restr
  rw [Submodule.quotEquivOfEqBot_apply_mk]
  congr 1
  simp only [Subtype.coe_mk, incl_true, incl_false, Subtype.coe_eta, map_one, one_mul, Units.val_mul]

private theorem restr_smooth (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ) (Φ : CellSp (k := k) χ₁ χ₂ u v) :
    (⟨restr χ₁ χ₂ u v Φ, fun q x₁ => restr_law χ₁ χ₂ u v Φ q x₁⟩ :
      indSpace (parab k (two (stdSum (rfl : u + v = u + v))))
        ((twist (rhoL (k := k) χ₁ χ₂ u v) (deltaHalf k (Two (Fin u) (Fin v)))).comp
          (leviProj k (two (stdSum (rfl : u + v = u + v)))))) ∈ smoothPart (ind _ _) := by
  have hΦ : IsOpen {y : Levi k (Two (Fin (u + v)) (Fin 1)) |
      ind (relParab k (colEq u v)) (sigmaC χ₁ χ₂ u v) y Φ.1 = Φ.1} := Φ.2
  have hcont : Continuous (incl (k := k) u v) :=
    (continuous_leviTwo k).comp (continuous_id.prodMk continuous_const)
  refine mem_smoothPart_of_nhds (Filter.mem_of_superset ((hΦ.preimage hcont).mem_nhds ?_) ?_)
  · show ind (relParab k (colEq u v)) (sigmaC χ₁ χ₂ u v) (incl u v 1) Φ.1 = Φ.1
    refine Subtype.ext (funext fun y => ?_)
    show Φ.1.1 (y * incl u v 1) = Φ.1.1 y
    rw [map_one, mul_one]
  · intro g₁ hg
    refine Subtype.ext (funext fun x₁ => ?_)
    show restr χ₁ χ₂ u v Φ (x₁ * g₁) = restr χ₁ χ₂ u v Φ x₁
    have h := congrArg (fun F => F.1 (incl u v x₁))
      (show ind (relParab k (colEq u v)) (sigmaC χ₁ χ₂ u v) (incl u v g₁) Φ.1 = Φ.1 from hg)
    have h' : Φ.1.1 (incl u v (x₁ * g₁)) = Φ.1.1 (incl u v x₁) :=
      (congrArg (fun y => Φ.1.1 y) (map_mul (incl (k := k) u v) x₁ g₁)).trans h
    unfold restr
    exact congrArg _ h'

private theorem toCell_surjective {χ₁ χ₂ : kˣ →* ℂˣ} (hχ₁ : IsSmoothChar χ₁) (u v : ℕ) :
    Function.Surjective (toCell (k := k) (χ₂ := χ₂) hχ₁ u v) := by
  intro Φ
  refine ⟨⟨⟨restr χ₁ χ₂ u v Φ, fun q x₁ => restr_law χ₁ χ₂ u v Φ q x₁⟩, restr_smooth χ₁ χ₂ u v Φ⟩,
    Subtype.ext (Subtype.ext (funext fun x => ?_))⟩
  show toFun χ₁ χ₂ u v _ x = Φ.1.1 x
  have hx : x = leviTwo k (Fin (u + v)) (Fin 1) (1, x true) * incl u v (x false) := by
    funext j
    cases j
    · exact (one_mul (x false)).symm
    · exact (mul_one (x true)).symm
  have hp : leviTwo k (Fin (u + v)) (Fin 1) (1, x true) ∈ relParab k (colEq u v) :=
    (mem_relParab_colEq _).2 (one_mem _)
  have h1 : Φ.1.1 (leviTwo k (Fin (u + v)) (Fin 1) (1, x true) * incl u v (x false)) =
      sigmaC χ₁ χ₂ u v ⟨_, hp⟩ (Φ.1.1 (incl u v (x false))) := Φ.1.2 ⟨_, hp⟩ _
  have hl : leviProj k (two (stdSum (rfl : u + v = u + v)))
      ⟨(leviTwo k (Fin (u + v)) (Fin 1) (1, x true)) false, (mem_relParab_colEq _).1 hp⟩ = 1 :=
    map_one (leviProj k (two (stdSum (rfl : u + v = u + v))))
  conv_rhs => rw [hx, h1, ← mk_restr χ₁ χ₂ u v Φ (x false), inducing_mk]
  unfold toFun
  rw [hl]
  simp only [map_one, Pi.one_apply, Units.val_one, mul_one]
  rfl

private def mapF {χ₁ χ₂ : kˣ →* ℂˣ} (hχ₁ : IsSmoothChar χ₁) (u v : ℕ) :
    (extTensor (prod₂ (detRep (Fin u) (χ₁ * absPow k (-(1 / 2)))) (detRep (Fin v) χ₂))
      (detRep (Fin 1) (χ₁ * absPow k ((u : ℂ) / 2)))).IntertwiningMap
    ((cellFunctor (rowEq u v) (colEq u v) (rhoM (k := k) χ₁ χ₂ u v)).comp
      (leviTwo k (Fin (u + v)) (Fin 1)).toMonoidHom) where
  toLinearMap := (toCell hχ₁ u v).comp (TensorProduct.rid ℂ _).toLinearMap
  isIntertwining' g := TensorProduct.ext' fun φ c => Subtype.ext (Subtype.ext (funext fun x => by
    show toFun χ₁ χ₂ u v (TensorProduct.rid ℂ _ (extTensor _ _ g (φ ⊗ₜ c))) x =
      toFun χ₁ χ₂ u v (TensorProduct.rid ℂ _ (φ ⊗ₜ c)) (x * leviTwo k (Fin (u + v)) (Fin 1) g)
    rw [extTensor_tmul, TensorProduct.rid_tmul, TensorProduct.rid_tmul]
    unfold toFun
    show (((χ₁ * absPow k ((u : ℂ) / 2)) (GeneralLinearGroup.det (x true)) : ℂˣ) : ℂ) •
        Submodule.Quotient.mk ((detRep (Fin 1) (χ₁ * absPow k ((u : ℂ) / 2)) g.2 c) • φ.1.1 (x false * g.1)) =
      (((χ₁ * absPow k ((u : ℂ) / 2)) (GeneralLinearGroup.det (x true * g.2)) : ℂˣ) : ℂ) •
        Submodule.Quotient.mk (c • φ.1.1 (x false * g.1))
    rw [detRep, ofChar_apply, detChar_apply, map_mul GeneralLinearGroup.det (x true) g.2,
      map_mul (χ₁ * absPow k ((u : ℂ) / 2)), Submodule.Quotient.mk_smul, Submodule.Quotient.mk_smul,
      smul_smul, smul_smul, Units.val_mul]
    congr 1
    ring))

private theorem mapF_bijective {χ₁ χ₂ : kˣ →* ℂˣ} (hχ₁ : IsSmoothChar χ₁) (u v : ℕ) :
    Function.Bijective (mapF (k := k) (χ₂ := χ₂) hχ₁ u v) :=
  ⟨(toCell_injective hχ₁ u v).comp (TensorProduct.rid ℂ _).injective,
    (toCell_surjective hχ₁ u v).comp (TensorProduct.rid ℂ _).surjective⟩

end GlobalTheory.CellDetSecond

end

theorem _root_.GlobalTheory.T.cell_functor_rep_equiv_nonzero : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ → ∀ (u v : ℕ)
    (b : SizeMatrix (Two (Fin (u + 1)) (Fin v)) (Two (Fin (u + v)) (Fin 1))), b.1 false true = 1 →
    ∃ (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Two (Fin (u + 1)) (Fin v) i)
      (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Two (Fin (u + v)) (Fin 1) j),
      Nonempty (Representation.Equiv ((cellFunctor f g ((extTensor (detRep (Fin (u + 1)) χ₁) (detRep (Fin v) χ₂)).comp
          (leviTwo k (Fin (u + 1)) (Fin v)).symm.toMonoidHom)).comp
            (leviTwo k (Fin (u + v)) (Fin 1)).toMonoidHom)
        (extTensor (prod₂ (detRep (Fin u) (χ₁ * absPow k (-(1 / 2)))) (detRep (Fin v) χ₂))
          (detRep (Fin 1) (χ₁ * absPow k ((u : ℂ) / 2))))) := by
  intro k _ _ _ _ χ₁ χ₂ h₁ _ u v b hb
  have e := GlobalTheory.CellDetSecond.eq_sizeSecond b hb
  subst e
  exact ⟨GlobalTheory.CellDetSecond.rowEq u v, GlobalTheory.CellDetSecond.colEq u v,
    ⟨(GlobalTheory.CellDetSecond.equivOfBij (GlobalTheory.CellDetSecond.mapF h₁ u v)
      (GlobalTheory.CellDetSecond.mapF_bijective h₁ u v)).symm⟩⟩
