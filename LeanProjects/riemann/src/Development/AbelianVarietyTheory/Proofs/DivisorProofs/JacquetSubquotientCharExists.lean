import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMidJacAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDetProdConstAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSignatureSum
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubquotientTwistFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentationSigmaEquivReindexStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThK.DetProd

noncomputable section

namespace GlobalTheory.ThK.MidJacCell

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThK.MidJac

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem surjective_of_ne_zero {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ G V} {ρ : Representation ℂ G W} (hρ : ρ.IsIrreducible) (F : σ.IntertwiningMap ρ)
    (hF : F ≠ 0) : Function.Surjective F := by
  let R : Subrepresentation ρ := ⟨LinearMap.range F.toLinearMap, by
    rintro g _ ⟨v, rfl⟩
    exact ⟨σ g v, F.isIntertwining _ _ g v⟩⟩
  rcases eq_bot_or_eq_top R with h | h
  · exfalso
    refine hF (Representation.IntertwiningMap.ext (LinearMap.ext fun v => ?_))
    have : F v ∈ R.toSubmodule := ⟨v, rfl⟩
    rw [h] at this
    exact this
  · intro w
    have : w ∈ R.toSubmodule := by rw [h]; trivial
    obtain ⟨v, hv⟩ := this
    exact ⟨v, hv⟩

theorem isDetProdConst_of_char {n : ℕ} (s : Fin 2 → ℕ) (e : (Σ i, Fin (s i)) ≃ Fin n)
    (ψ : Levi k (fun i => Fin (s i)) →* ℂˣ) (χ₁ χ₂ : kˣ →* ℂˣ)
    (hψ : ∀ z, ψ z = χ₁ (Matrix.GeneralLinearGroup.det (z 0)) * χ₂ (Matrix.GeneralLinearGroup.det (z 1)))
    {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V)
    (hπ : IsSubquotient π (parInd e (ofChar ψ))) : IsDetProdConst (s 0) (s 1) χ₁ χ₂ π := by
  obtain ⟨x, x', rfl⟩ : ∃ x x', s = ![x, x'] :=
    ⟨s 0, s 1, funext fun i => by fin_cases i <;> rfl⟩
  have : ψ = twoDet x x' χ₁ χ₂ := MonoidHom.ext fun z => by
    rw [hψ]
    rfl
  subst this
  exact ⟨e, hπ⟩

theorem isSubquotient_comp_of_equiv {G H V V' W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ G V}
    {ρ' : Representation ℂ G V'} (φ : ρ.Equiv ρ') (s : H →* G) {σ : Representation ℂ H W}
    (h : IsSubquotient σ ((twist ρ 1).comp s)) : IsSubquotient σ ((twist ρ' 1).comp s) := by
  simp only [twist_one] at h ⊢
  exact h.trans (.of_surjective (compMap φ.symm.toIntertwiningMap _)
    fun w => ⟨φ.symm.toLinearEquiv.symm w, φ.symm.toLinearEquiv.apply_symm_apply w⟩)

theorem isSubquotient_twist_one_comp {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ G V} (s : H →* G) {σ : Representation ℂ H W}
    (h : IsSubquotient σ (ρ.comp s)) : IsSubquotient σ ((twist ρ 1).comp s) := by
  simpa only [twist_one] using h

theorem isSubquotient_of_twist_one {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ H V} (s : H →* G) {σ : Representation ℂ H W}
    (h : IsSubquotient σ (twist ρ ((1 : G →* ℂˣ).comp s))) : IsSubquotient σ ρ := by
  simpa only [MonoidHom.one_comp, twist_one] using h

theorem modExp_row (b : Fin 3 → ℕ) : modExp (fun j : Fin 3 => Fin (b j)) 1 = (b 2 : ℤ) - b 0 := by
  simp [modExp, Finset.sum_filter, Fin.sum_univ_three]

theorem cellChar_mid (a a' : ℕ) (α β : kˣ →* ℂˣ) (b : Fin 2 → Fin 3 → ℕ)
    (f : ∀ i, (Σ j, Fin (b i j)) ≃ Fin (![a, a'] i)) (z : Levi k (fun i : Fin 2 => Fin (b i 1))) :
    (((twoDet a a' α β).comp (relEmb k f) * (relDeltaHalf k (fun i j => Fin (b i j)))⁻¹)
      (swapBlocks k (fun i j => Fin (b i j)) (Pi.mulSingle (1 : Fin 3) z)) : ℂˣ) =
      (α * absPow k (((b 0 0 : ℂ) - b 0 2) / 2)) (Matrix.GeneralLinearGroup.det (z 0)) *
      (β * absPow k (((b 1 0 : ℂ) - b 1 2) / 2)) (Matrix.GeneralLinearGroup.det (z 1)) := by
  have hw : ∀ i j, swapBlocks k (fun i j => Fin (b i j)) (Pi.mulSingle (1 : Fin 3) z) i j =
      (Pi.mulSingle (M := fun j => Levi k (fun i : Fin 2 => Fin (b i j))) (1 : Fin 3) z j) i := fun _ _ => rfl
  have h0 : ∀ i, swapBlocks k (fun i j => Fin (b i j)) (Pi.mulSingle (1 : Fin 3) z) i 0 = 1 := fun i => by
    rw [hw, Pi.mulSingle_eq_of_ne (by decide)]; rfl
  have h1 : ∀ i, swapBlocks k (fun i j => Fin (b i j)) (Pi.mulSingle (1 : Fin 3) z) i 1 = z i := fun i => by
    rw [hw, Pi.mulSingle_eq_same]
  have h2 : ∀ i, swapBlocks k (fun i j => Fin (b i j)) (Pi.mulSingle (1 : Fin 3) z) i 2 = 1 := fun i => by
    rw [hw, Pi.mulSingle_eq_of_ne (by decide)]; rfl
  have e : ∀ i : Fin 2, absPow k (((b i 0 : ℂ) - b i 2) / 2) =
      (absPow k (((modExp (fun j : Fin 3 => Fin (b i j)) 1 : ℤ) : ℂ) / 2))⁻¹ := fun i => by
    rw [← absPow_neg, modExp_row]
    congr 1
    push_cast
    ring
  rw [e 0, e 1]
  simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.inv_apply, relDeltaHalf_apply, twoDet,
    Pi.evalMonoidHom_apply, detChar_apply, relEmb_apply, det_leviEmb, deltaHalf_apply, Fin.prod_univ_two,
    Fin.prod_univ_three, h0, h1, h2, map_one, one_mul, mul_one]
  rw [mul_inv]
  exact mul_mul_mul_comm _ _ _ _

end GlobalTheory.ThK.MidJacCell

namespace GlobalTheory.ThK.MidJacCell

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThK.MidJac

set_option maxHeartbeats 1000000 in

theorem midJac_detInd : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.Published.GeometricLemmaFiltration →
    ∀ (a a' l n : ℕ) (h : l + n ≤ a + a') (α β : kˣ →* ℂˣ), GlobalTheory.SplitWeil.IsUnram α → GlobalTheory.SplitWeil.IsUnram β →
    ∀ ρ : GlobalTheory.CuspRep.SmIrr (GL (Fin n) k),
      GlobalTheory.SmGL.IsSubquotient ρ.ρ (GlobalTheory.ThK.MidJac.midJac l n (a + a') h (GlobalTheory.ThK.MidJac.detInd a a' α β)) →
      ∃ x x' j j' : ℕ, x + x' = n ∧ j + j' = l ∧ j + x ≤ a ∧ j' + x' ≤ a' ∧
        GlobalTheory.ThK.DetProd.IsDetProdConst x x'
          (α * GlobalTheory.SmGL.absPow k ((((1 : ℝ) - a) / 2 + j + ((x : ℝ) - 1) / 2 : ℝ) : ℂ))
          (β * GlobalTheory.SmGL.absPow k ((((1 : ℝ) - a') / 2 + j' + ((x' : ℝ) - 1) / 2 : ℝ) : ℂ)) ρ.ρ := by
  intro k _ _ _ _ hG a a' l n h α β hα hβ ρ hρ
  have hsm : IsSmooth (ofChar (twoDet a a' α β)) := by
    refine (isSmooth_ofChar_iff _).2 ?_
    exact ((isSmoothChar_of_isUnram hα).detChar.comp _ (continuous_apply 0)).mul
      ((isSmoothChar_of_isUnram hβ).detChar.comp _ (continuous_apply 1))
  obtain ⟨N, bb, hbb⟩ := hG k (Fin 2) (Fin 3) (Fin (a + a')) (fun i => Fin (![a, a'] i))
    (fun j => Fin (![l, n, a + a' - l - n] j)) (e2 a a') (e3 l n (a + a') h)
  obtain ⟨S, hmono, h0, htop, hS⟩ := hbb ℂ (ofChar (twoDet a a' α β)) hsm
  haveI := nontrivial_of_irreducible ρ.irred
  have hid : Representation.IntertwiningMap.id ρ.ρ ≠ 0 := by
    intro h0'
    obtain ⟨v, hv⟩ := exists_ne (0 : ρ.V)
    exact hv (congrArg (fun F : ρ.ρ.IntertwiningMap ρ.ρ => F v) h0')
  have hρ' : IsSubquotient ρ.ρ ((twist (jac (e3 l n (a + a') h) (detInd a a' α β)) 1).comp
      (midIncl l n (a + a' - l - n))) := isSubquotient_twist_one_comp _ hρ
  obtain ⟨t, V', _, _, Q', hQ', F', hF'⟩ := exists_step_subquotient_ne_zero_of_filtration _ 1
    (midIncl l n (a + a' - l - n)) N S hmono h0 htop ρ.ρ ρ.ρ hρ' _ hid
  obtain ⟨f⟩ := (bb t).nonempty_rows
  obtain ⟨g⟩ := (bb t).nonempty_cols
  obtain ⟨φ⟩ := hS t f g
  have hQ'' : IsSubquotient Q' ((twist (cellFunctor f g (ofChar (twoDet a a' α β))) 1).comp
      (midIncl l n (a + a' - l - n))) := isSubquotient_comp_of_equiv φ _ hQ'
  let ψ : (∀ j, Levi k (fun i : Fin 2 => Fin ((bb t).1 i j))) →* ℂˣ :=
    ((twoDet a a' α β).comp (relEmb k f) * (relDeltaHalf k (fun i j => Fin ((bb t).1 i j)))⁻¹).comp
      (swapBlocks k (fun i j => Fin ((bb t).1 i j)))
  have hτ : ∀ z w, ((relJac f (ofChar (twoDet a a' α β))).comp
      (swapBlocks k (fun i j => Fin ((bb t).1 i j)))) z w = (ψ z : ℂ) • w := by
    intro z w
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    show relJac f _ _ _ = _
    rw [relJac_mk, ofChar_apply, ← smul_eq_mul, Submodule.Quotient.mk_smul, smul_smul]
    congr 1
    rw [← Units.val_mul, mul_comm]
    rfl
  obtain ⟨V'', _, _, Q'', hQ''', F'', hF''⟩ := GlobalTheory.T.representation_sigma_equiv_reindex k g _ ψ hτ 1 1 Q' ρ.ρ hQ'' F' hF'
  have hfin := (IsSubquotient.of_surjective F'' (surjective_of_ne_zero ρ.irred F'' hF'')).trans hQ'''
  replace hfin := isSubquotient_of_twist_one _ hfin
  have hr0 := (bb t).2.1 0
  have hr1 := (bb t).2.1 1
  have hc0 := (bb t).2.2 0
  have hc1 := (bb t).2.2 1
  have hcard : ∀ (m : ℕ) (i : Fintype (Fin m)), @Fintype.card (Fin m) i = m := fun m i => by
    convert Fintype.card_fin m
  simp only [Fin.sum_univ_two, Fin.sum_univ_three, hcard] at hr0 hr1 hc0 hc1
  replace hr0 : (bb t).1 0 0 + (bb t).1 0 1 + (bb t).1 0 2 = a := hr0
  replace hr1 : (bb t).1 1 0 + (bb t).1 1 1 + (bb t).1 1 2 = a' := hr1
  replace hc0 : (bb t).1 0 0 + (bb t).1 1 0 = l := hc0
  replace hc1 : (bb t).1 0 1 + (bb t).1 1 1 = n := hc1
  refine ⟨(bb t).1 0 1, (bb t).1 1 1, (bb t).1 0 0, (bb t).1 1 0, hc1, hc0, by omega, by omega, ?_⟩
  refine isDetProdConst_of_char (fun i => (bb t).1 i 1) (g 1) _ _ _ (fun z => ?_) ρ.ρ hfin
  have haC : (a : ℂ) = (bb t).1 0 0 + (bb t).1 0 1 + (bb t).1 0 2 := by exact_mod_cast hr0.symm
  have haC' : (a' : ℂ) = (bb t).1 1 0 + (bb t).1 1 1 + (bb t).1 1 2 := by exact_mod_cast hr1.symm
  have e1 : α * absPow k ((((bb t).1 0 0 : ℂ) - (bb t).1 0 2) / 2) =
      α * absPow k ((((1 : ℝ) - a) / 2 + (bb t).1 0 0 + (((bb t).1 0 1 : ℝ) - 1) / 2 : ℝ) : ℂ) := by
    congr 2
    push_cast
    rw [haC]
    ring
  have e2 : β * absPow k ((((bb t).1 1 0 : ℂ) - (bb t).1 1 2) / 2) =
      β * absPow k ((((1 : ℝ) - a') / 2 + (bb t).1 1 0 + (((bb t).1 1 1 : ℝ) - 1) / 2 : ℝ) : ℂ) := by
    congr 2
    push_cast
    rw [haC']
    ring
  refine (cellChar_mid a a' α β (bb t).1 f z).trans ?_
  rw [e1, e2]

end GlobalTheory.ThK.MidJacCell
