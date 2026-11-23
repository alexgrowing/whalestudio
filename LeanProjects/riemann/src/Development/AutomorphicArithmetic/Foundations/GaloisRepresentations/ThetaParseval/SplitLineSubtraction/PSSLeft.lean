import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.SubtractOf
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigencharacterOfSummandCharZero
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

section
open scoped Matrix

variable {Γ k : Type} [Group Γ] [Field k]

private def inc (a b : ℕ) : (Fin a → k) →ₗ[k] (Fin (a + b) → k) where
  toFun x := Sum.elim x 0 ∘ finSumFinEquiv.symm
  map_add' x y := by
    funext i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
    cases j <;> simp
  map_smul' c x := by
    funext i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
    cases j <;> simp

private theorem inc_inl {a b : ℕ} (x : Fin a → k) (i : Fin a) :
    inc a b x (finSumFinEquiv (Sum.inl i)) = x i := by
  simp [inc]

private theorem inc_inr {a b : ℕ} (x : Fin a → k) (j : Fin b) :
    inc a b x (finSumFinEquiv (Sum.inr j)) = 0 := by
  simp [inc]

private theorem inc_injective {a b : ℕ} : Function.Injective (inc (k := k) a b) := by
  intro x y h
  funext i
  rw [← inc_inl (b := b) x i, ← inc_inl (b := b) y i, h]

private theorem sum_mulVec_inc {a b : ℕ} (r : Γ →* GL (Fin a) k) (s : Γ →* GL (Fin b) k) (g : Γ)
    (x : Fin a → k) :
    (sumRep r s g : Matrix (Fin (a + b)) (Fin (a + b)) k) *ᵥ inc a b x =
      inc a b ((r g : Matrix (Fin a) (Fin a) k) *ᵥ x) := by
  funext i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
  rcases j with j | j
  · rw [GlobalTheory.EigTwist.sumRep_mulVec_inl, inc_inl]
    congr 1
    funext i
    exact inc_inl x i
  · rw [GlobalTheory.EigTwist.sumRep_mulVec_inr, inc_inr]
    have : (inc a b x ∘ finSumFinEquiv ∘ Sum.inr : Fin b → k) = 0 := by
      funext i
      exact inc_inr x i
    rw [this, Matrix.mulVec_zero]
    rfl

private theorem ss_left {a b : ℕ} (r : Γ →* GL (Fin a) k) (s : Γ →* GL (Fin b) k)
    (h : IsSSRep (sumRep r s)) : IsSSRep r := by
  intro W hW
  obtain ⟨C, hC, hc⟩ := h (W.map (inc a b)) (by
    rintro g _ ⟨x, hx, rfl⟩
    exact ⟨_, hW g x hx, (sum_mulVec_inc r s g x).symm⟩)
  refine ⟨C.comap (inc a b), fun g v hv => ?_, ?_, ?_⟩
  · show inc a b _ ∈ C
    rw [← sum_mulVec_inc r s g v]
    exact hC g _ hv
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    have h0 : inc a b x ∈ W.map (inc a b) ⊓ C := ⟨⟨x, hx, rfl⟩, hx'⟩
    rw [hc.disjoint.eq_bot, Submodule.mem_bot] at h0
    exact inc_injective (h0.trans (map_zero _).symm)
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have hx : inc a b x ∈ W.map (inc a b) ⊔ C := by
      rw [hc.codisjoint.eq_top]
      exact Submodule.mem_top
    obtain ⟨_, ⟨w, hw, rfl⟩, z, hz, hzx⟩ := Submodule.mem_sup.1 hx
    have hz' : z = inc a b (x - w) := by
      rw [map_sub, ← hzx]
      abel
    refine Submodule.mem_sup.2 ⟨w, hw, x - w, ?_, by abel⟩
    show inc a b (x - w) ∈ C
    rwa [← hz']

private theorem ss_of_iso {n : ℕ} (r r' : Γ →* GL (Fin n) k) (h : RepIso r r') (hr : IsSSRep r) :
    IsSSRep r' := by
  obtain ⟨g, hg⟩ := h
  let e : (Fin n → k) ≃ₗ[k] (Fin n → k) := Matrix.toLin'OfInv
    (M := ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) (M' := (g : Matrix (Fin n) (Fin n) k))
    (Units.inv_mul g) (Units.mul_inv g)
  have he : ∀ v, e v = (g : Matrix (Fin n) (Fin n) k) *ᵥ v := fun v => rfl
  have key : ∀ s v, e ((r s : Matrix (Fin n) (Fin n) k) *ᵥ v) = (r' s : Matrix (Fin n) (Fin n) k) *ᵥ e v := by
    intro s v
    rw [he, he, hg, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul,
      inv_mul_cancel_right]
  intro W hW
  obtain ⟨C, hC, hc⟩ := hr (W.comap (e : (Fin n → k) →ₗ[k] (Fin n → k))) (by
    intro s v hv
    show e _ ∈ W
    rw [key]
    exact hW s _ hv)
  refine ⟨C.map (e : (Fin n → k) →ₗ[k] (Fin n → k)), ?_, ?_⟩
  · rintro s _ ⟨u, hu, rfl⟩
    exact ⟨_, hC s u hu, key s u⟩
  · have h2 : IsCompl ((W.comap (e : (Fin n → k) →ₗ[k] (Fin n → k))).map (e : (Fin n → k) →ₗ[k] (Fin n → k)))
        (C.map (e : (Fin n → k) →ₗ[k] (Fin n → k))) := (Submodule.orderIsoMapComap e).isCompl hc
    rwa [Submodule.map_comap_eq_of_surjective e.surjective] at h2

private theorem ss_tw {n : ℕ} (r : Γ →* GL (Fin n) k) (c : Γ →* kˣ) (hr : IsSSRep r) :
    IsSSRep (tw r c) := by
  intro W hW
  have hW' : IsInv r W := by
    intro g v hv
    have h1 := W.smul_mem ((c g)⁻¹ : kˣ).val (hW g v hv)
    rw [UpperTheory.V.Af.tw_val, Matrix.smul_mulVec, smul_smul, Units.val_inv_eq_inv_val,
      inv_mul_cancel₀ (c g).ne_zero, one_smul] at h1
    exact h1
  obtain ⟨C, hC, hc⟩ := hr W hW'
  refine ⟨C, fun g v hv => ?_, hc⟩
  rw [UpperTheory.V.Af.tw_val, Matrix.smul_mulVec]
  exact C.smul_mem _ (hC g v hv)

end

theorem UpperTheory.Gal.TP.Sub.sSLeft_holds :
    SSLeft := by
  intro Γ k _ _ a b
  exact ⟨fun r s h => ss_left r s h, fun r r' h hr => ss_of_iso r r' h hr, fun r c h => ss_tw r c h⟩
