import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo

noncomputable section

open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel Matrix

namespace GlobalTheory.SmGL.EmptyBlocks

section General

variable {F G H V W : Type} [Field F] [Group G] [Group H] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]

theorem jhMult_comp_surjective (φ : H →* G) (hφ : Function.Surjective φ) (σ : Representation F G W)
    (ρ : Representation F G V) :
    jhMult (σ.comp φ : Representation F H W) (ρ.comp φ : Representation F H V) = jhMult σ ρ := by
  have : ∀ r, OccursTimes (σ.comp φ : Representation F H W) (ρ.comp φ : Representation F H V) r ↔
      OccursTimes σ ρ r := fun r => by
    constructor
    · rintro ⟨S, T, h1, h2, h3⟩
      let up : Subrepresentation (ρ.comp φ : Representation F H V) → Subrepresentation ρ := fun S =>
        ⟨S.toSubmodule, fun g v hv => by
          obtain ⟨h, rfl⟩ := hφ g
          exact S.apply_mem_toSubmodule h hv⟩
      refine ⟨fun i => up (S i), fun i => up (T i), h1, h2, fun i => (h3 i).map fun ψ =>
        .mk ψ.toLinearEquiv fun g => ?_⟩
      obtain ⟨h, rfl⟩ := hφ g
      exact ψ.isIntertwining' h
    · rintro ⟨S, T, h1, h2, h3⟩
      let down : Subrepresentation ρ → Subrepresentation (ρ.comp φ : Representation F H V) := fun S =>
        ⟨S.toSubmodule, fun h v hv => S.apply_mem_toSubmodule (φ h) hv⟩
      exact ⟨fun i => down (S i), fun i => down (T i), h1, h2, fun i => (h3 i).map fun ψ =>
        .mk ψ.toLinearEquiv fun h => ψ.isIntertwining' (φ h)⟩
  simp only [jhMult, this]

end General

section Blocks

variable (R : Type) [CommRing R] {β n : Type} [Fintype β] [LinearOrder β] [Fintype n] [DecidableEq n]
  {c : β → Type} [∀ j, Fintype (c j)] [∀ j, DecidableEq (c j)] (f : (Σ j, c j) ≃ n)

def torusToLevi : (n → Rˣ) →* Levi R c :=
  (leviProj R f).comp ((diagT R n).codRestrict (parab R f) fun t => mem_parab.2 fun i j h => by
    rw [val_diagT, diagonal_apply_ne]
    rintro rfl
    exact lt_irrefl _ h)

theorem val_torusToLevi (t : n → Rˣ) (j : β) :
    (torusToLevi R f t j : Matrix (c j) (c j) R) = diagonal fun x => (t (f ⟨j, x⟩) : R) := by
  ext x y
  show (diagT R n t : Matrix n n R) (f ⟨j, x⟩) (f ⟨j, y⟩) = _
  rw [val_diagT]
  simp [diagonal_apply]

theorem leviEmb_torusToLevi (t : n → Rˣ) : leviEmb R f (torusToLevi R f t) = diagT R n t := by
  ext i j
  obtain ⟨⟨a, i⟩, rfl⟩ := f.surjective i
  obtain ⟨⟨b, j⟩, rfl⟩ := f.surjective j
  by_cases h : a = b
  · subst h
    rw [leviEmb_apply_same]
    rfl
  · rw [leviEmb_apply_ne R f _ h, val_diagT, diagonal_apply_ne]
    intro h'
    exact h (congrArg Sigma.fst (f.injective h'))

theorem det_torusToLevi (t : n → Rˣ) (j : β) :
    GeneralLinearGroup.det (torusToLevi R f t j) = ∏ x, t (f ⟨j, x⟩) := by
  ext
  simp [val_torusToLevi]

theorem prod_det_torusToLevi (χ : β → Rˣ →* ℂˣ) (t : n → Rˣ) :
    ∏ j, χ j (GeneralLinearGroup.det (torusToLevi R f t j)) = ∏ i, χ (blk f i) (t i) := by
  rw [← f.prod_comp, Fintype.prod_sigma]
  simp [det_torusToLevi]

theorem torusToLevi_surjective (hf : Function.Injective (blk f)) :
    Function.Surjective (torusToLevi R f) := by
  intro g
  refine ⟨fun i => GeneralLinearGroup.det (g (blk f i)), funext fun j => ?_⟩
  ext x y
  have hs : ∀ u v : c j, u = v := fun u v => by
    have : f ⟨j, u⟩ = f ⟨j, v⟩ := hf (by simp)
    simpa using this
  obtain rfl := hs x y
  haveI : Unique (c j) := ⟨⟨x⟩, fun u => hs _ _⟩
  rw [val_torusToLevi, diagonal_apply_eq, blk_apply, GeneralLinearGroup.val_det_apply,
    det_unique, hs default x]

omit [LinearOrder β] [DecidableEq n] [∀ j, DecidableEq (c j)] in

theorem sum_card_blocks (P : β → Prop) [DecidablePred P] :
    ∑ b with P b, (Fintype.card (c b) : ℤ) = ∑ i with P (blk f i), (1 : ℤ) := by
  rw [Finset.sum_filter, Finset.sum_filter, ← f.sum_comp, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [blk_apply]
  split_ifs <;> simp

variable [LinearOrder n]

omit [DecidableEq n] [∀ j, DecidableEq (c j)] in

theorem modExp_blk (hf : StrictMono (blk f)) (i : n) :
    modExp c (blk f i) = modExp (fun _ : n => Unit) i := by
  unfold modExp
  rw [sum_card_blocks f, sum_card_blocks f]
  simp [hf.lt_iff_lt]

theorem unipRad_eq (hf : StrictMono (blk f)) : unipRad R f = unipB R n := by
  ext g
  rw [mem_unipRad, mem_unipB, mem_parab]
  simp only [hf.lt_iff_lt]
  refine and_congr Iff.rfl ⟨fun h i => ?_, fun h a x y => ?_⟩
  · obtain ⟨⟨a, x⟩, rfl⟩ := f.surjective i
    simpa using h a x x
  · have : f ⟨a, x⟩ = f ⟨a, y⟩ := hf.injective (by simp)
    obtain rfl : x = y := by simpa using this
    simpa using h _

end Blocks

theorem jhMult_jac_eq_jacB (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (β n : Type) [Fintype β] [LinearOrder β] [Fintype n]
    [DecidableEq n] [LinearOrder n] (c : β → Type) [∀ j, Fintype (c j)] [∀ j, DecidableEq (c j)]
    (f : (Σ j, c j) ≃ n) (hf : StrictMono (blk f)) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL n k) V) (χ : β → kˣ →* ℂˣ) :
    jhMult (ofChar (leviChar c χ)) (jac f π) =
      jhMult (ofChar (torusChar fun i => χ (blk f i))) (jacB π) := by
  have h1 : ((ofChar (leviChar c χ)).comp (torusToLevi k f) : Representation ℂ (n → kˣ) ℂ) =
      ofChar (torusChar fun i => χ (blk f i)) := by
    refine MonoidHom.ext fun t => LinearMap.ext fun y => ?_
    show ofChar _ _ y = _
    rw [ofChar_apply, ofChar_apply, leviChar_apply, torusChar_apply, prod_det_torusToLevi]
  have h2 : ∀ t, deltaHalf k c (torusToLevi k f t) =
      deltaHalf k (fun _ : n => Unit) (leviTorus k n t) := fun t => by
    have hd : ∀ i, GeneralLinearGroup.det (leviTorus k n t i) = t i :=
      congrFun ((leviTorus k n).left_inv t)
    rw [deltaHalf_apply, deltaHalf_apply,
      prod_det_torusToLevi k f fun a => absPow k ((modExp c a : ℂ) / 2)]
    simp only [hd, modExp_blk f hf]
  have h3 : twKer π (unipRad k f) 1 = twKer π (unipB k n) 1 := by rw [unipRad_eq k f hf]
  rw [← jhMult_comp_surjective (torusToLevi k f) (torusToLevi_surjective k f hf.injective), h1]
  refine jhMult_congr_right _ (.mk (Submodule.quotEquivOfEq _ _ h3) fun t => ?_)
  refine Submodule.linearMap_qext _ (LinearMap.ext fun v => ?_)
  show Submodule.quotEquivOfEq _ _ h3 (jac f π (torusToLevi k f t) (Submodule.Quotient.mk v)) =
    jac (points n) π (leviTorus k n t) (Submodule.Quotient.mk v)
  rw [jac_mk, jac_mk, map_smul, h2, leviEmb_torusToLevi]
  rfl

end GlobalTheory.SmGL.EmptyBlocks
