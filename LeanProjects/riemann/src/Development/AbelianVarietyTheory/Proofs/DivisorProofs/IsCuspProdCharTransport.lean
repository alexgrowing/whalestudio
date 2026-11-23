import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CuspidalProductMultiplicity

noncomputable section

namespace GlobalTheory.FinGL.Transport

open Formalism.L2.DIV

theorem isIrreducible_comp {G G' V : Type} [Group G] [Group G'] [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ G V) (f : G' →* G) (hf : Function.Surjective f) (h : σ.IsIrreducible) :
    Representation.IsIrreducible (σ.comp f : Representation ℂ G' V) := by
  let Φ : Subrepresentation (σ.comp f : Representation ℂ G' V) ≃o Subrepresentation σ :=
    { toFun := fun U => ⟨U.toSubmodule, fun g v hv => by
        obtain ⟨g', rfl⟩ := hf g
        exact U.apply_mem_toSubmodule g' hv⟩
      invFun := fun U => ⟨U.toSubmodule, fun g v hv => U.apply_mem_toSubmodule (f g) hv⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  exact Φ.isSimpleOrder

theorem character_coind {G G' P P' V : Type} [Group G] [Group G'] [Group P] [Group P'] [AddCommGroup V] [Module ℂ V]
    (i : P →* G) (i' : P' →* G') (σ : Representation ℂ P V) (F : G' ≃* G) (f : P' →* P) (hf : Function.Surjective f)
    (hc : ∀ p, F (i' p) = i (f p)) (x : G') :
    (Representation.coind i' (σ.comp f : Representation ℂ P' V)).character x =
      (Representation.coind i σ).character (F x) := by
  let L : Representation.coindV i σ ≃ₗ[ℂ] Representation.coindV i' (σ.comp f : Representation ℂ P' V) :=
    { toFun := fun φ => ⟨fun y => φ.1 (F y), fun p y => by
        show φ.1 (F (i' p * y)) = σ (f p) (φ.1 (F y))
        rw [map_mul, hc]
        exact φ.2 _ _⟩
      invFun := fun φ => ⟨fun y => φ.1 (F.symm y), fun p y => by
        obtain ⟨p', rfl⟩ := hf p
        show φ.1 (F.symm (i (f p') * y)) = σ (f p') (φ.1 (F.symm y))
        rw [map_mul, ← hc, MulEquiv.symm_apply_apply]
        exact φ.2 _ _⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun φ => Subtype.ext (funext fun y => congrArg φ.1 (F.apply_symm_apply y))
      right_inv := fun φ => Subtype.ext (funext fun y => congrArg φ.1 (F.symm_apply_apply y)) }
  unfold Representation.character
  rw [← LinearMap.trace_conj' _ L]
  congr 1
  refine LinearMap.ext fun φ => Subtype.ext (funext fun y => ?_)
  show φ.1 (y * x) = φ.1 (F.symm (F y * F x))
  rw [← map_mul, MulEquiv.symm_apply_apply]

variable {κ κ' : Type} [Field κ] [Field κ'] {r : ℕ}

def glEquiv (e : κ' ≃+* κ) (r : ℕ) : GL (Fin r) κ' ≃* GL (Fin r) κ :=
  { Matrix.GeneralLinearGroup.map (e : κ' →+* κ) with
    invFun := Matrix.GeneralLinearGroup.map (e.symm : κ →+* κ')
    left_inv := fun g => by
      ext i j
      simp [Matrix.GeneralLinearGroup.map_apply]
    right_inv := fun g => by
      ext i j
      simp [Matrix.GeneralLinearGroup.map_apply] }

def triMap (e : κ' →+* κ) (b : Fin r → ℕ) : blockTri (κ := κ') b →* blockTri (κ := κ) b :=
  ((Matrix.GeneralLinearGroup.map e).comp (blockTri (κ := κ') b).subtype).codRestrict _ fun p i j hij => by
    have h : (p.1 : Matrix (Fin r) (Fin r) κ') i j = 0 := p.2 hij
    show e ((p.1 : Matrix (Fin r) (Fin r) κ') i j) = 0
    rw [h, map_zero]

theorem triMap_apply (e : κ' →+* κ) (b : Fin r → ℕ) (p : blockTri (κ := κ') b) (i j : Fin r) :
    ((triMap e b p : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) i j =
      e (((p : GL (Fin r) κ') : Matrix (Fin r) (Fin r) κ') i j) := rfl

theorem triMap_surjective (e : κ' ≃+* κ) (b : Fin r → ℕ) : Function.Surjective (triMap (e : κ' →+* κ) b) := fun p =>
  ⟨triMap (e.symm : κ →+* κ') b p, by
    ext i j
    simp [triMap_apply]⟩

theorem triMap_eq_one_iff (e : κ' →+* κ) (b : Fin r → ℕ) (p : blockTri (κ := κ') b) (i j : Fin r) :
    ((triMap e b p : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) i j = (1 : Matrix (Fin r) (Fin r) κ) i j ↔
      ((p : GL (Fin r) κ') : Matrix (Fin r) (Fin r) κ') i j = (1 : Matrix (Fin r) (Fin r) κ') i j := by
  have h1 : (1 : Matrix (Fin r) (Fin r) κ) i j = e ((1 : Matrix (Fin r) (Fin r) κ') i j) := by
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  rw [triMap_apply, h1, e.injective.eq_iff]

theorem isCuspDatum_comp {V : Type} [AddCommGroup V] [Module ℂ V] (e : κ' ≃+* κ) (b : Fin r → ℕ)
    (σ : Representation ℂ (blockTri (κ := κ) b) V) (h : IsCuspDatum b σ) :
    IsCuspDatum b (σ.comp (triMap (e : κ' →+* κ) b) : Representation ℂ (blockTri (κ := κ') b) V) where
  mono := h.mono
  irr := isIrreducible_comp σ _ (triMap_surjective e b) h.irr
  infl := fun p hp => h.infl _ fun i j hij => (triMap_eq_one_iff _ b p i j).2 (hp i j hij)
  cusp := fun S hS y hy => h.cusp S hS y fun u hu => by
    obtain ⟨u', rfl⟩ := triMap_surjective e b u
    exact hy u' fun i j hij => hu i j fun h' => hij ((triMap_eq_one_iff _ b u' i j).1 h')

theorem isCuspProdChar_transport : ∀ (κ κ' : Type) [Field κ] [Field κ'] (e : κ ≃+* κ') (r : ℕ) (θ : GL (Fin r) κ → ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsCuspProdChar θ → GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsCuspProdChar
      (fun x : GL (Fin r) κ' => θ (Matrix.GeneralLinearGroup.map (e.symm : κ' →+* κ) x)) := by
  rintro κ κ' _ _ e r θ ⟨d, b, σ, hσ, hθ⟩
  refine ⟨d, b, σ.comp (triMap (e.symm : κ' →+* κ) b), isCuspDatum_comp e.symm b σ hσ, fun x => ?_⟩
  show θ _ = _
  rw [hθ]
  exact (character_coind _ _ σ (glEquiv e.symm r) _ (triMap_surjective e.symm b) (fun _ => rfl) x).symm

end GlobalTheory.FinGL.Transport
