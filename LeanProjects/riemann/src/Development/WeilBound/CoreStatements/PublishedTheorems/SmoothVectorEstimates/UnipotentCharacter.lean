import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerVanishingImpliesZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

namespace UnipotentCharacter

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def chi (ψ : AddChar (Ad E) ℂ) (w : Pl E) : AddChar (w.adicCompletion E) ℂ where
  toFun y := ψ (sFin E (sLoc E w y))
  map_zero_eq_one' := by simp only [map_zero, AddChar.map_zero_eq_one]
  map_add_eq_mul' x y := by simp only [map_add, AddChar.map_add_eq_mul]

theorem chi_apply (ψ : AddChar (Ad E) ℂ) (w : Pl E) (y : w.adicCompletion E) :
    chi ψ w y = ψ (sFin E (sLoc E w y)) := rfl

theorem chi_cont {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) (w : Pl E) : Continuous (chi ψ w) :=
  hψ.cont.comp ((continuous_const.prodMk continuous_id : Continuous fun x : Af E =>
    ((0, x) : InfiniteAdeleRing E × Af E)).comp (CuspSub.continuous_sLoc w))

theorem lastE_loc (w : Pl E) {k : ℕ} (y : UnipotentBlockColumnIndex a k k → w.adicCompletion E) :
    lastE k (fun t => sFin E (sLoc E w (y t))) = sFin E (sLoc E w (lastE k y)) := by
  unfold lastE
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  split_ifs <;> simp

theorem sum_of {X : Type} [AddCommMonoid X] [Module ℂ X] (P : X → Prop) (h0 : P 0)
    (hadd : ∀ x y, P x → P y → P (x + y)) (hsm : ∀ (c : ℂ) x, P x → P (c • x)) {ι : Type}
    (T : Finset ι) (c : ι → ℂ) (f : ι → X) (hf : ∀ t, P (f t)) : P (∑ t ∈ T, c t • f t) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using h0
  | insert t T ht ih => rw [Finset.sum_insert ht]; exact hadd _ _ (hsm _ _ (hf t)) ih

end UnipotentCharacter

open UnipotentCharacter in
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in
theorem whittaker_expansion_cuspidal : S2 → S9 → MirabolicColumnBlock → G0 → G5 → G5b → G7 := by
  intro hS2 hS9 hS10 hG0 hG5 hG5b E _ _ _ a ψ hψ S Y Y' hY hY' n m w hw hmw hSt
  obtain ⟨φ, hφY, φ', hφY', hsm, hsm', hlev, hlev', h1, hWh⟩ := hSt
  obtain ⟨-, -, i3, i4, i5, -, -, i8, -, i10, -⟩ := hG0 E a
  obtain ⟨g5a, g5r, -, g5c⟩ := hG5 E a ψ hψ
  obtain ⟨b1, b2, b3, b4, b5⟩ := hG5b E a S
  obtain ⟨s10dec, -, -, s10blk1, -⟩ := hS10 (w.adicCompletion E) a (m w + 1)
  have hpoly : PolyBd (repI E a) := ⟨1, 0, zero_le_one, fun g x => by
    rw [pow_zero, mul_one, one_mul]
    exact le_of_eq (norm_Rt (infGL E a g) x)⟩
  obtain ⟨s0, sadd, ssmul, -, -, -⟩ := hS2 (InfinitePlace E) a (XB E a) (repI E a) hpoly
  let U : Set (GL (Fin a) (w.adicCompletion E)) := {u | repW a w u φ = φ} ∩ {u | repW a w u φ' = φ'}
  have hU : U ∈ 𝓝 (1 : GL (Fin a) (w.adicCompletion E)) := Filter.inter_mem (hlev w hw) (hlev' w hw)
  have hne : ∃ x, chi ψ w x ≠ 1 := by
    obtain ⟨y, hy⟩ := hψ.loc w
    exact ⟨y, hy⟩
  obtain ⟨T, c, η, r, hη1, hr1, hrMir, -, -, hmain⟩ :=
    hS9 (w.adicCompletion E) a (m w) hmw (chi ψ w) (chi_cont hψ w) hne (XB E a) (repW a w) U hU
  have inS : ∀ u, InS S (fl a w u : GA E a) := fun u v hv => i5 w v u (fun e => hv (e ▸ hw))
  have stab : ∀ Z : Submodule ℂ (XB E a), YOK ψ S Z → ∀ u, ∀ x ∈ Z, repW a w u x ∈ Z :=
    fun Z hZ u x hx => hZ.stable _ (inS u) x hx
  have memZ : ∀ Z : Submodule ℂ (XB E a), YOK ψ S Z → ∀ x ∈ Z, ∑ t ∈ T, c t • repW a w t x ∈ Z :=
    fun Z hZ x hx => Z.sum_mem fun t _ => Z.smul_mem _ (stab Z hZ t x hx)
  have smZ : ∀ x : XB E a, SmV (repI E a) x → SmV (repI E a) (∑ t ∈ T, c t • repW a w t x) :=
    fun x hx => sum_of _ s0 sadd ssmul T c _ fun t => b1 _ x hx
  have levZ : ∀ x : XB E a, Lev S x → Lev S (∑ t ∈ T, c t • repW a w t x) :=
    fun x hx => sum_of _ b5 b4 b3 T c _ fun t => b2 _ x hx

  have key : ∀ Z : Submodule ℂ (XB E a), YOK ψ S Z → ∀ x ∈ Z, (∀ u ∈ U, repW a w u x = x) →
      ∀ g' : GA E a, cLoc w g' = 1 → ∀ h, GlobalTheory (m w + 1) h →
      Wh ψ (∑ t ∈ T, c t • repW a w t x) (g' * fl a w h) = η h * Wh ψ x (g' * fl a w (r h)) := by
    intro Z hZ x hx hxU g' hg' h hh
    obtain ⟨Λ, hΛ⟩ := g5a g'
    have hcond : ∀ z ∈ Z, ∀ y : UnipotentBlockColumnIndex a (m w + 1) (m w + 1) → w.adicCompletion E,
        (Λ : XB E a →ₗ[ℂ] ℂ) (repW a w (blkU y) z) = chi ψ w (lastE (m w + 1) y) * (Λ : XB E a →ₗ[ℂ] ℂ) z := by
      intro z hz y
      show Λ _ = _ * Λ _
      rw [hΛ _ (hZ.good _ (stab Z hZ _ z hz)),
        hΛ _ (hZ.good _ hz), repW_apply, g5r, i8 w g' hg', i10,
        (g5c z (hZ.good _ hz)).2.2 (m w + 1) (Nat.succ_pos _), lastE_loc, chi_apply]
    have := hmain x hxU Z (stab Z hZ) hx (Λ : XB E a →ₗ[ℂ] ℂ) hcond h hh
    change Λ _ = η h * Λ _ at this
    rw [hΛ _ (hZ.good _ (stab Z hZ _ _ (memZ Z hZ x hx))), hΛ _ (hZ.good _ (stab Z hZ _ _ hx)),
      repW_apply, repW_apply, g5r, g5r] at this
    exact this
  refine ⟨_, memZ Y hY φ hφY, _, memZ Y' hY' φ' hφY', smZ φ hsm, smZ φ' hsm', levZ φ hlev, levZ φ' hlev', ?_, ?_⟩
  · have := key Y hY φ hφY (fun u hu => hu.1) 1 (map_one _) 1 s10blk1
    rw [hr1] at this
    simp only [map_one, mul_one] at this
    rw [this]
    exact mul_ne_zero hη1 h1
  · intro g hg
    obtain ⟨hgI, hgL⟩ := hg
    have hgw : Mir (m w + 1) (cLoc w g) := by simpa using hgL w
    obtain ⟨y, h, hh, hdec⟩ := s10dec _ hgw
    set g' : GA E a := g * (fl a w (cLoc w g))⁻¹ with hg'def
    have hg' : cLoc w g' = 1 := by rw [hg'def, map_mul, map_inv, i4, mul_inv_cancel]
    have red : ∀ Z : Submodule ℂ (XB E a), YOK ψ S Z → ∀ x ∈ Z, (∀ u ∈ U, repW a w u x = x) →
        Wh ψ (∑ t ∈ T, c t • repW a w t x) g =
          ψ (lastE (m w + 1) fun t => sFin E (sLoc E w (y t))) * (η h * Wh ψ x (g' * fl a w (r h))) := by
      intro Z hZ x hx hxU
      have e : g = blkU (fun t => sFin E (sLoc E w (y t))) * (g' * fl a w h) := by
        rw [← i10, ← mul_assoc, ← i8 w g' hg', mul_assoc, ← map_mul, ← hdec, hg'def, inv_mul_cancel_right]
      rw [e, (g5c _ (hZ.good _ (memZ Z hZ x hx))).2.2 (m w + 1) (Nat.succ_pos _), key Z hZ x hx hxU g' hg' h hh]
    rw [red Y hY φ hφY (fun u hu => hu.1), red Y' hY' φ' hφY' (fun u hu => hu.2)]
    by_cases hη : η h = 0
    · rw [hη]; simp
    congr 2
    refine hWh _ ⟨?_, fun v => ?_⟩
    · rw [map_mul, hg'def, map_mul, map_inv, i3, i3, inv_one, mul_one, mul_one]
      exact hgI
    · rcases eq_or_ne v w with rfl | hv
      · rw [map_mul, hg', i4, one_mul]
        exact hrMir h hh hη
      · rw [map_mul, hg'def, map_mul, map_inv, i5 w v _ hv, i5 w v _ hv, inv_one, mul_one, mul_one]
        simpa [hv] using hgL v

end PositivityTheory.jumpWindows

end
