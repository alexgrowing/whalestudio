import Formalism.LocalToGlobal.GlobalTheory.BlockActions.MulLatMulLat

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.L2.Forms NumberField Formalism.UG Matrix
open scoped TensorProduct
open IsDedekindDomain

variable {D : D7}

section IsExtAlg

variable {z0 : Fin (D.R.N D.R.m) → D.host.E} {R : Type} [CommRing R] {φ : D.host.E →+* R}

theorem isExt_mul {a b : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) R} {A B : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) R}
    (ha : IsExt D z0 φ a A) (hb : IsExt D z0 φ b B) : IsExt D z0 φ (a * b) (A * B) := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  refine ⟨?_, ?_⟩
  · rw [Matrix.mul_assoc, hb1, ← Matrix.mul_assoc, ha1, Matrix.mul_assoc]
  · rw [← mulVec_mulVec, hb2, ha2]

theorem isExt_inv {a a' : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) R} {A A' : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) R}
    (ha : IsExt D z0 φ a A) (hA : A' * A = 1) (ha' : a * a' = 1) : IsExt D z0 φ a' A' := by
  obtain ⟨ha1, ha2⟩ := ha
  refine ⟨?_, ?_⟩
  · calc A' * (iXm D).map φ = A' * ((iXm D).map φ * (a * a')) := by rw [ha', Matrix.mul_one]
      _ = (A' * A) * (iXm D).map φ * a' := by rw [← Matrix.mul_assoc ((iXm D).map φ), ← ha1]; simp only [Matrix.mul_assoc]
      _ = (iXm D).map φ * a' := by rw [hA, Matrix.one_mul]
  · conv_lhs => rw [← ha2]
    rw [mulVec_mulVec, hA, one_mulVec]

theorem isExt_map {a : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E} {A : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E}
    (ha : IsExt D z0 (RingHom.id D.host.E) a A) : IsExt D z0 φ (a.map φ) (A.map φ) := by
  obtain ⟨ha1, ha2⟩ := ha
  have hm : (iXm D).map (RingHom.id D.host.E) = iXm D := by ext i j; rfl
  rw [hm] at ha1
  refine ⟨?_, ?_⟩
  · rw [← Matrix.map_mul, ha1, Matrix.map_mul]
  · have hz : (fun i => (RingHom.id D.host.E) (z0 i)) = z0 := rfl
    rw [hz] at ha2
    funext i
    have := congrArg (fun w => φ (w i)) ha2
    rw [← this, RingHom.map_mulVec]; rfl

end IsExtAlg

variable {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

set_option maxHeartbeats 2000000 in

theorem til_eq_level (Tf : FormsTiedSym D u Ch chOf) (hC : CrdFacts D)
    (hSD : ∀ c, dualSet (sigD D : D.host.E →+* D.host.E) (gramP D) (Tf.clsP.lat c) = (Tf.clsP.lat c : Set (Fin (D.R.N D.R.m - 1) → D.host.E)))
    (hdeg : Module.finrank ℚ D.host.E < (D.mem u).A.T - 1) (v : (D.mem u).A.vT)
    (c c' : (D.fm u).clsP) (h : (D.fm u).til c = (D.fm u).til c') :
    ∃ (δ : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
      (k : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))
      (G : GL (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)),
      IsExt D Tf.til.z0 (RingHom.id D.host.E) δ ((Tf.til.ga c').1.1 * ((Tf.til.ga c)⁻¹).1.1) ∧
      (∀ x y, hform (sigD D : D.host.E →+* D.host.E) (gramP D) (δ *ᵥ x) (δ *ᵥ y) =
        hform (sigD D : D.host.E →+* D.host.E) (gramP D) x y) ∧
      IsExt D Tf.til.z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) k G.1 ∧
      G ∈ (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.U ∧
      (Tf.clsP.y c').1.1 * k = δ.map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) * (Tf.clsP.y c).1.1 := by
  set incl : D.host.E →+* D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F :=
    inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) with hincl
  obtain ⟨δ, hδE, hδi⟩ := til_eq_ext Tf hC hSD hdeg v c c' h
  have hdet : ∀ d : (D.fm u).clsP, IsUnit ((Tf.clsP.y d).1.1).det := fun d =>
    (Matrix.isUnit_iff_isUnit_det _).mp (Tf.clsP.y d).1.isUnit
  have ext_of : ∀ d : (D.fm u).clsP, ∃ Gd : GL (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F),
      IsExt D Tf.til.z0 incl (Tf.clsP.y d).1.1 Gd.1 := by
    intro d
    obtain ⟨g, hg, hu⟩ := til_ext Tf incl (Tf.clsP.y d).1.1
    exact ⟨((Matrix.isUnit_iff_isUnit_det g).mpr (hu (hdet d))).unit, hg⟩
  obtain ⟨Gc, hGc⟩ := ext_of c
  obtain ⟨Gc', hGc'⟩ := ext_of c'
  have e1 := Tf.tilAd.til_ad c Gc hGc
  have e2 := Tf.tilAd.til_ad c' Gc' hGc'
  rw [← h] at e2
  have hGc1 : Gc = bc incl (Tf.til.ga c).1 * ((Tf.cls D.R.m le_rfl (Or.inr rfl)).y ((D.fm u).til c)).1 *
      ((Tf.tilAd.ka c).1)⁻¹ := eq_mul_inv_of_mul_eq e1.symm
  have hGc2 : Gc' = bc incl (Tf.til.ga c').1 * ((Tf.cls D.R.m le_rfl (Or.inr rfl)).y ((D.fm u).til c)).1 *
      ((Tf.tilAd.ka c').1)⁻¹ := eq_mul_inv_of_mul_eq e2.symm
  set Γ := bc incl (Tf.til.ga c').1 * (bc incl (Tf.til.ga c).1)⁻¹ with hΓ
  refine ⟨δ, ((Tf.clsP.y c').1.1)⁻¹ * δ.map incl * (Tf.clsP.y c).1.1, Gc'⁻¹ * Γ * Gc, hδE, hδi, ?_, ?_, ?_⟩
  · have hinv : IsExt D Tf.til.z0 incl ((Tf.clsP.y c').1.1)⁻¹ (Gc'⁻¹).1 :=
      isExt_inv hGc' (Units.inv_mul Gc') (Matrix.mul_nonsing_inv _ (hdet c'))
    have hΓ1 : (Γ.1 : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) =
        ((Tf.til.ga c').1.1 * ((Tf.til.ga c)⁻¹).1.1).map incl := by
      rw [hΓ, Units.val_mul, Matrix.map_mul]
      congr 1
    have hG : IsExt D Tf.til.z0 incl (δ.map incl) Γ.1 := by rw [hΓ1]; exact isExt_map hδE
    rw [Units.val_mul, Units.val_mul]
    exact isExt_mul (isExt_mul hinv hG) hGc
  · have : Gc'⁻¹ * Γ * Gc = (Tf.tilAd.ka c').1 * ((Tf.tilAd.ka c).1)⁻¹ := by
      rw [hGc1, hGc2, hΓ]; group
    rw [this]
    exact Subgroup.mul_mem _ (Tf.tilAd.ka c').2 (Subgroup.inv_mem _ (Tf.tilAd.ka c).2)
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hdet c'), Matrix.one_mul]

end Formalism.L2.GlobalTheoryTheory.Br
