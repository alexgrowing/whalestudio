import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.SplitDict
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwasawaBlockTriangular

open ValuativeRel Matrix Topology
open scoped TensorProduct

noncomputable section

namespace PositivityTheory.ThK.SplitLoc

open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.PRep

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {a a' : ℕ}

abbrev stdE (a a' : ℕ) : Fin a ⊕ Fin a' ≃ Fin (a + a') := stdSum (rfl : a + a' = a + a')

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem isBlockUpper_iff (b : GL (Fin (a + a')) k) : IsBlockUpper b ↔ b ∈ parab k (two (stdE a a')) :=
  (mem_parab_two k).symm

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem det_blkA (p : parab k (two (stdE a a'))) :
    ((GeneralLinearGroup.det (leviProj k (two (stdE a a')) p false) : kˣ) : k) = (blkA (p : GL (Fin (a + a')) k)).det := by
  rw [GeneralLinearGroup.val_det_apply]
  congr 1

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem det_blkD (p : parab k (two (stdE a a'))) :
    ((GeneralLinearGroup.det (leviProj k (two (stdE a a')) p true) : kˣ) : k) = (blkD (p : GL (Fin (a + a')) k)).det := by
  rw [GeneralLinearGroup.val_det_apply]
  congr 1

theorem law_parab {α β : kˣ →* ℂˣ} {F : GL (Fin (a + a')) k → ℂ} (hF : F ∈ indSp a a' α β)
    (p : parab k (two (stdE a a'))) (h : GL (Fin (a + a')) k) :
    F (p * h) = indFac a a' α β (GeneralLinearGroup.det (leviProj k (two (stdE a a')) p false))
      (GeneralLinearGroup.det (leviProj k (two (stdE a a')) p true)) * F h :=
  hF.2 _ h ((isBlockUpper_iff _).2 p.2) _ _ (det_blkA p) (det_blkD p)

theorem indFac_eventually {α β : kˣ →* ℂˣ} {F : GL (Fin (a + a')) k → ℂ} (hF : F ∈ indSp a a' α β)
    {h : GL (Fin (a + a')) k} (h0 : F h ≠ 0) :
    ∀ᶠ g in 𝓝 (1 : GL (Fin a) k × GL (Fin a') k),
      indFac a a' α β (GeneralLinearGroup.det g.1) (GeneralLinearGroup.det g.2) = 1 := by
  obtain ⟨U, hU, hUF⟩ := hF.1
  have hc : Continuous fun g : GL (Fin a) k × GL (Fin a') k => h⁻¹ * emb₂ k (stdE a a') g * h :=
    (continuous_const.mul ((continuous_leviEmb k (two (stdE a a'))).comp (continuous_leviTwo k))).mul continuous_const
  have hn : (fun g : GL (Fin a) k × GL (Fin a') k => h⁻¹ * emb₂ k (stdE a a') g * h) ⁻¹' (U : Set _) ∈ 𝓝 1 :=
    (hU.preimage hc).mem_nhds (by simp)
  filter_upwards [hn] with g hg
  have h1 := hUF _ hg h
  have h2 := law_parab hF ⟨_, leviEmb_mem_parab k (two (stdE a a')) (leviTwo k _ _ g)⟩ h
  rw [leviProj_leviEmb] at h2
  have h3 : h * (h⁻¹ * emb₂ k (stdE a a') g * h) = emb₂ k (stdE a a') g * h := by group
  rw [h3] at h1
  exact mul_right_cancel₀ h0 ((h2.symm.trans h1).trans (one_mul _).symm)

theorem smooth_of_eventually {n : ℕ} {χ : kˣ →* ℂˣ} (z : ℂ)
    (h : ∀ᶠ g in 𝓝 (1 : GL (Fin n) k), (χ (GeneralLinearGroup.det g) : ℂ) * apow (GeneralLinearGroup.det g) z = 1) :
    IsSmooth (detRep (Fin n) χ) := by
  refine (isSmooth_ofChar_iff _).2 (Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_)
  have hz : IsSmoothChar (detChar (Fin n) (absPow k z)) := (isSmoothChar_of_isUnram (isUnram_absPow k z)).detChar
  filter_upwards [h, IsOpen.mem_nhds hz (one_mem _)] with g h1 h2
  have h3 : apow (GeneralLinearGroup.det g) z = 1 := congrArg Units.val (MonoidHom.mem_ker.1 h2)
  rw [h3, mul_one] at h1
  exact Units.ext h1

theorem smooth_of_ne_zero {α β : kˣ →* ℂˣ} {F : GL (Fin (a + a')) k → ℂ} (hF : F ∈ indSp a a' α β)
    {h : GL (Fin (a + a')) k} (h0 : F h ≠ 0) : IsSmooth (detRep (Fin a) α) ∧ IsSmooth (detRep (Fin a') β) := by
  have he := indFac_eventually hF h0
  constructor
  · refine smooth_of_eventually ((a' : ℂ) / 2) ?_
    have hc : ContinuousAt (fun g : GL (Fin a) k => (g, (1 : GL (Fin a') k))) 1 := by fun_prop
    filter_upwards [hc.eventually he] with g hg
    simpa [indFac] using hg
  · refine smooth_of_eventually (-(a : ℂ) / 2) ?_
    have hc : ContinuousAt (fun g : GL (Fin a') k => ((1 : GL (Fin a) k), g)) 1 := by fun_prop
    filter_upwards [hc.eventually he] with g hg
    simpa [indFac] using hg

abbrev rhoD (a a' : ℕ) (α β : kˣ →* ℂˣ) : Representation ℂ (Levi k (Two (Fin a) (Fin a'))) (ℂ ⊗[ℂ] ℂ) :=
  (extTensor (detRep (Fin a) α) (detRep (Fin a') β)).comp (leviTwo k (Fin a) (Fin a')).symm.toMonoidHom

theorem twist_rhoD (α β : kˣ →* ℂˣ) (g : Levi k (Two (Fin a) (Fin a'))) (x : ℂ ⊗[ℂ] ℂ) :
    twist (rhoD a a' α β) (deltaHalf k (Two (Fin a) (Fin a'))) g x =
      indFac a a' α β (GeneralLinearGroup.det (g false)) (GeneralLinearGroup.det (g true)) • x := by
  obtain ⟨g, rfl⟩ := (leviTwo k (Fin a) (Fin a')).surjective g
  rw [twist_apply, deltaHalf_two]
  have h : ∀ x, rhoD a a' α β (leviTwo k (Fin a) (Fin a') g) x =
      ((α (GeneralLinearGroup.det g.1) : ℂ) * β (GeneralLinearGroup.det g.2)) • x := by
    intro x
    show extTensor _ _ ((leviTwo k (Fin a) (Fin a')).symm (leviTwo k (Fin a) (Fin a') g)) x = _
    rw [MulEquiv.symm_apply_apply]
    induction x with
    | zero => simp
    | add x y hx hy => rw [map_add, hx, hy, smul_add]
    | tmul v w =>
      rw [extTensor_tmul]
      simp only [detRep, ofChar_apply, detChar_apply, ← smul_eq_mul, TensorProduct.smul_tmul_smul]
  rw [h, smul_smul]
  congr 1
  simp only [Fintype.card_fin, Units.val_mul]
  show apow (GeneralLinearGroup.det g.1) ((a' : ℂ) / 2) * apow (GeneralLinearGroup.det g.2) (-(a : ℂ) / 2) * _ =
    indFac a a' α β (GeneralLinearGroup.det g.1) (GeneralLinearGroup.det g.2)
  unfold indFac
  ring

def toFn (a a' : ℕ) (α β : kˣ →* ℂˣ) : IndSp (two (stdE a a')) (rhoD a a' α β) →ₗ[ℂ] (GL (Fin (a + a')) k → ℂ) where
  toFun f := fun g => TensorProduct.lid ℂ ℂ (f.1.1 g)
  map_add' f f' := funext fun g => map_add (TensorProduct.lid ℂ ℂ) (f.1.1 g) (f'.1.1 g)
  map_smul' c f := funext fun g => map_smul (TensorProduct.lid ℂ ℂ) c (f.1.1 g)

theorem exists_toFn {α β : kˣ →* ℂˣ} {F : GL (Fin (a + a')) k → ℂ} (hF : F ∈ indSp a a' α β) :
    ∃ f, toFn a a' α β f = F := by
  obtain ⟨U, hU, hUF⟩ := hF.1
  refine ⟨⟨⟨fun g => (TensorProduct.lid ℂ ℂ).symm (F g), fun p g => ?_⟩,
    mem_smoothPart_of_nhds (Filter.mem_of_superset (hU.mem_nhds U.one_mem) fun u hu => ?_)⟩, funext fun g => ?_⟩
  · refine Eq.trans ?_ (twist_rhoD α β (leviProj k (two (stdE a a')) p) _).symm
    rw [← map_smul, smul_eq_mul]
    exact congrArg _ (law_parab hF p g)
  · exact Subtype.ext (funext fun x => congrArg (TensorProduct.lid ℂ ℂ).symm (hUF u hu x))
  · exact (TensorProduct.lid ℂ ℂ).apply_symm_apply _

theorem indIrred_of (hB : GlobalTheory.Published.BernsteinUnitaryProductIrreducible) : IndIrred := by
  intro k _ _ _ _ a a' α β hα hβ N hN hr
  by_cases h0 : N = ⊥
  · exact Or.inl h0
  refine Or.inr (le_antisymm hN ?_)
  obtain ⟨F, hFN, hF0⟩ := (Submodule.ne_bot_iff N).1 h0
  obtain ⟨h, hh⟩ := Function.ne_iff.1 hF0
  obtain ⟨s₁, s₂⟩ := smooth_of_ne_zero (hN hFN) hh
  have hI : (parInd (two (stdE a a')) (rhoD a a' α β)).IsIrreducible := hB k a a' ℂ ℂ _ _
    s₁ (isIrreducible_ofChar _) ((isUnitarisable_ofChar_iff _).2 fun _ => hα _)
    s₂ (isIrreducible_ofChar _) ((isUnitarisable_ofChar_iff _).2 fun _ => hβ _)
  let S : Subrepresentation (parInd (two (stdE a a')) (rhoD a a' α β)) :=
    ⟨N.comap (toFn a a' α β), fun g f hf => hr g _ hf⟩
  rcases hI.eq_bot_or_eq_top S with e | e
  · obtain ⟨f, rfl⟩ := exists_toFn (hN hFN)
    have hf : f ∈ S.toSubmodule := hFN
    rw [e] at hf
    have hf0 : f = 0 := hf
    exact absurd (by rw [hf0, map_zero]) hF0
  · intro G hG
    obtain ⟨f, rfl⟩ := exists_toFn hG
    have hf : f ∈ S.toSubmodule := by rw [e]; trivial
    exact hf

end PositivityTheory.ThK.SplitLoc

namespace PositivityTheory.ThK.SplitDict

open PositivityTheory.ThK.SplitLoc GlobalTheory.SplitWeil GlobalTheory.SmGL

theorem induced_vanish_of_vanish_on_integral : IndIwasawa := by
  intro k _ _ _ _ a a' α β F hF h0
  funext g
  obtain ⟨p, hp, c, hc, rfl⟩ := iwasawa_blockTriangular k _ (fun i => (blk (two (stdE a a')) i).toNat) g
  have hp' : p ∈ parab k (two (stdE a a')) := fun i j hij => hp (by
    revert hij
    dsimp only
    cases blk (two (stdE a a')) i <;> cases blk (two (stdE a a')) j <;> simp)
  exact (law_parab hF ⟨p, hp'⟩ c).trans (by rw [h0 c hc, mul_zero]; rfl)

end PositivityTheory.ThK.SplitDict
