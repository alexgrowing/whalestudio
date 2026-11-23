import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DisjointSpanPerpLat

noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal

namespace GlobalTheory.UnitVectorStabEq

section General

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem hform_eq (s : A →+* A) (J : Matrix n n A) (y z : n → A) :
    Formalism.UG.hform s J y z = (s ∘ y) ⬝ᵥ (J *ᵥ z) := by
  simp only [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, Function.comp, mul_assoc]

theorem hform_mulVec (s : A →+* A) (J g : Matrix n n A) (y z : n → A) :
    Formalism.UG.hform s J (g *ᵥ y) (g *ᵥ z) = Formalism.UG.hform s (Formalism.UG.cT s g * J * g) y z := by
  have h : s ∘ (g *ᵥ y) = (g.map s) *ᵥ (s ∘ y) := by
    funext i
    exact RingHom.map_mulVec s g y i
  rw [hform_eq, hform_eq, h, Formalism.UG.cT, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec (s ∘ y), Matrix.vecMul_transpose]

theorem hform_sub_smul (s : A →+* A) (J : Matrix n n A) (x y : n → A) (a : A) :
    Formalism.UG.hform s J x (y - a • x) = Formalism.UG.hform s J x y - a * Formalism.UG.hform s J x x := by
  simp only [hform_eq, Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub, dotProduct_smul,
    smul_eq_mul]

end General

section Place

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (v : HeightOneSpectrum (𝓞 F))

theorem mem_stabVec (x : Fin M → Ev F E v) (g : HA (Fv F v) σ J) :
    g ∈ stabVec σ J v x ↔ act σ J v g x = x := by
  unfold stabVec
  rw [MulAction.mem_stabilizer_iff]
  exact ⟨fun h => congrFun h 0, fun h => funext fun _ => h⟩

theorem mem_stabLat (L : Submodule (OEv F E v) (Fin M → Ev F E v)) (g : HA (Fv F v) σ J) :
    g ∈ stabLat σ J v L ↔ ∀ y, y ∈ L ↔ act σ J v g y ∈ L := Iff.rfl

theorem mem_perpLat (L : Submodule (OEv F E v) (Fin M → Ev F E v)) (x y : Fin M → Ev F E v) :
    y ∈ perpLat σ J v L x ↔ hR (Fv F v) σ J x y = 0 ∧ y ∈ L := Iff.rfl

theorem hR_act (g : HA (Fv F v) σ J) (y z : Fin M → Ev F E v) :
    hR (Fv F v) σ J (act σ J v g y) (act σ J v g z) = hR (Fv F v) σ J y z := by
  unfold hR act
  rw [hform_mulVec]
  congr 1
  exact (show HR (Fv F v) σ J from g).2

theorem act_sub_smul (g : HA (Fv F v) σ J) (x y : Fin M → Ev F E v) (a : Ev F E v) :
    act σ J v g (y - a • x) = act σ J v g y - a • act σ J v g x := by
  unfold act
  rw [Matrix.mulVec_sub, Matrix.mulVec_smul]

theorem mem_iff (L : Submodule (OEv F E v) (Fin M → Ev F E v)) (hL : IsSDLat σ J v L)
    (x : Fin M → Ev F E v) (hx : x ∈ L) (b : Ev F E v) (hb : b ∈ OEv F E v)
    (hb1 : hR (Fv F v) σ J x x * b = 1) (y : Fin M → Ev F E v) :
    y ∈ L ↔ (b * hR (Fv F v) σ J x y ∈ OEv F E v ∧
      y - (b * hR (Fv F v) σ J x y) • x ∈ perpLat σ J v L x) := by
  have hs : ∀ a ∈ OEv F E v, a • x ∈ L := fun a ha => L.smul_mem (⟨a, ha⟩ : OEv F E v) hx
  constructor
  · intro hy
    have ha : b * hR (Fv F v) σ J x y ∈ OEv F E v := mul_mem hb (((hL.2.2 y).1 hy).2 x hx)
    refine ⟨ha, (mem_perpLat σ J v L x _).2 ⟨?_, L.sub_mem hy (hs _ ha)⟩⟩
    have h : hR (Fv F v) σ J x (y - (b * hR (Fv F v) σ J x y) • x) =
        hR (Fv F v) σ J x y - (b * hR (Fv F v) σ J x y) * hR (Fv F v) σ J x x :=
      hform_sub_smul _ _ _ _ _
    rw [h]
    linear_combination (- hR (Fv F v) σ J x y) * hb1
  · rintro ⟨ha, hy⟩
    have := L.add_mem ((mem_perpLat σ J v L x _).1 hy).2 (hs _ ha)
    rwa [sub_add_cancel] at this

end Place

theorem stabLat_inf_stabVec : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)) (L : Submodule (OEv F E v) (Fin M → Ev F E v)), IsSDLat σ J v L → ∀ x ∈ L, (∃ b ∈ OEv F E v, hR (Fv F v) σ J x x * b = 1) → stabLat σ J v L ⊓ stabVec σ J v x = stabLat σ J v (perpLat σ J v L x) ⊓ stabVec σ J v x := by
  intro F E _ _ _ _ _ σ _ M J _ v L hL x hx ⟨b, hb, hb1⟩
  ext g
  rw [Subgroup.mem_inf, Subgroup.mem_inf]
  refine and_congr_left fun hg => ?_
  rw [mem_stabVec] at hg
  have hh : ∀ y, hR (Fv F v) σ J x (act σ J v g y) = hR (Fv F v) σ J x y := by
    intro y
    rw [← hR_act σ J v g x y, hg]
  rw [mem_stabLat, mem_stabLat]
  constructor
  · intro h y
    rw [mem_perpLat, mem_perpLat, hh, h y]
  · intro h y
    rw [mem_iff σ J v L hL x hx b hb hb1 y, mem_iff σ J v L hL x hx b hb hb1 (act σ J v g y), hh,
      h (y - _), act_sub_smul, hg]

end GlobalTheory.UnitVectorStabEq
