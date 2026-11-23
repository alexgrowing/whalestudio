import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ToLocEqMapToMatrix

open NumberField IsDedekindDomain Matrix Formalism.L2.Col GlobalTheory.SymBridge

noncomputable section
namespace GlobalTheory.VolBridge

variable {E k : Type} [Field E] [Field k] (ι : E →+* k) {A : Type} [Fintype A] [DecidableEq A] {N : ℕ} (e : A ≃ Fin N)

def locHom : (Sp E N ≃ₗ[E] Sp E N) →* GL A k where
  toFun x := ⟨toLoc ι e e x.toLinearMap, toLoc ι e e (x⁻¹ : Sp E N ≃ₗ[E] Sp E N).toLinearMap,
    by
      rw [← toLoc_comp_square]
      have h : x.toLinearMap ∘ₗ (x⁻¹ : Sp E N ≃ₗ[E] Sp E N).toLinearMap = LinearMap.id := by
        ext v i; simp [LinearEquiv.coe_inv]
      rw [h, toLoc_id_square],
    by
      rw [← toLoc_comp_square]
      have h : (x⁻¹ : Sp E N ≃ₗ[E] Sp E N).toLinearMap ∘ₗ x.toLinearMap = LinearMap.id := by
        ext v i; simp [LinearEquiv.coe_inv]
      rw [h, toLoc_id_square]⟩
  map_one' := by
    ext1
    show toLoc ι e e (LinearEquiv.refl E (Sp E N)).toLinearMap = 1
    exact toLoc_id_square ι e
  map_mul' x y := by
    ext1
    show toLoc ι e e (x * y).toLinearMap = toLoc ι e e x.toLinearMap * toLoc ι e e y.toLinearMap
    rw [← toLoc_comp_square]
    rfl

theorem locHom_val (x : Sp E N ≃ₗ[E] Sp E N) : (locHom ι e x).val = toLoc ι e e x.toLinearMap := rfl

section Num
variable {A : Type} {N c c' : ℕ} (e : A ⊕ Fin c ≃ Fin (N + c')) (hcc : c' = c)
  (he : ∀ i : Fin c, (e (Sum.inr i)).val = N + i.val)

include hcc he in
theorem eX_lt (a : A) : (e (Sum.inl a)).val < N := by
  by_contra h
  push Not at h
  have hc : (e (Sum.inl a)).val - N < c := by have := (e (Sum.inl a)).isLt; omega
  have h2 : e (Sum.inr ⟨_, hc⟩) = e (Sum.inl a) := Fin.ext (by rw [he]; simp; omega)
  exact absurd (e.injective h2) (by simp)

def eX : A ≃ Fin N :=
  Equiv.ofBijective (fun a => ⟨(e (Sum.inl a)).val, eX_lt e hcc he a⟩) (by
    constructor
    · intro a b hab
      have : e (Sum.inl a) = e (Sum.inl b) := Fin.ext (by simpa using congrArg Fin.val hab)
      simpa using e.injective this
    · intro m
      rcases hm : e.symm (Fin.castAdd c' m) with a | i
      · refine ⟨a, Fin.ext ?_⟩
        have := congrArg (fun z => (e z).val) hm
        simp at this
        simp [← this]
      · exfalso
        have := congrArg (fun z => (e z).val) hm
        simp [he] at this
        have := m.isLt
        omega)

theorem eX_val (a : A) : ((eX e hcc he a : Fin N) : ℕ) = (e (Sum.inl a)).val := rfl

end Num

section Ext
variable {E : Type} [Field E] {N c : ℕ}

def extX (c : ℕ) (y : Sp E N ≃ₗ[E] Sp E N) : Sp E (N + c) ≃ₗ[E] Sp E (N + c) :=
  (LinearEquiv.funCongrLeft E E finSumFinEquiv) ≪≫ₗ (LinearEquiv.sumArrowLequivProdArrow (Fin N) (Fin c) E E) ≪≫ₗ
    (y.prodCongr (LinearEquiv.refl E (Fin c → E))) ≪≫ₗ (LinearEquiv.sumArrowLequivProdArrow (Fin N) (Fin c) E E).symm ≪≫ₗ
    (LinearEquiv.funCongrLeft E E finSumFinEquiv).symm

theorem extX_castAdd (y : Sp E N ≃ₗ[E] Sp E N) (v : Sp E (N + c)) (i : Fin N) :
    extX c y v (Fin.castAdd c i) = y (fun i => v (Fin.castAdd c i)) i := by
  simp [extX, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft, LinearEquiv.sumArrowLequivProdArrow, LinearEquiv.funCongrLeft, Equiv.sumArrowEquivProdArrow]
  rfl

theorem extX_natAdd (y : Sp E N ≃ₗ[E] Sp E N) (v : Sp E (N + c)) (i : Fin c) :
    extX c y v (Fin.natAdd N i) = v (Fin.natAdd N i) := by
  simp [extX, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft, LinearEquiv.sumArrowLequivProdArrow, LinearEquiv.funCongrLeft, Equiv.sumArrowEquivProdArrow]

end Ext

end GlobalTheory.VolBridge
