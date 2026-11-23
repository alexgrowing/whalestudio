import Mathlib
import Development.AbelianVarietyTheory.Statements.HaarFundamentalDomain.HypothesesHold
import Development.AbelianVarietyTheory.BlockTheory.ClassSums.ReadingWithSpecialisation
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ValuesAlgIffValuesUnitOfNe

open AlgebraicGeometry CategoryTheory NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.ClsVal GlobalTheory.IndefiniteRowSideFullHecke.ReadingWithSpecialisation
open scoped Classical

namespace GlobalTheory.ClsVal.Cmp

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g q0 n : ℕ} {H : Host E} {Dw : Datum H}
  {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}

def ren (π : Equiv.Perm (Fin g)) : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ) :=
  (LinearEquiv.funCongrLeft ℂ ℂ π).toContinuousLinearEquiv

theorem ren_apply (π : Equiv.Perm (Fin g)) (z : Fin g → ℂ) : ren π z = z ∘ π := rfl

theorem ren_single (π : Equiv.Perm (Fin g)) (j : Fin g) : ren π (Pi.single j 1) = Pi.single (π.symm j) 1 := by
  funext i
  rw [ren_apply, Function.comp_apply]
  by_cases h : i = π.symm j
  · subst h
    simp
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne]
    intro h'
    exact h (by rw [← h']; simp)

section Rename₂

variable (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (π : Equiv.Perm (Fin g))
  (x : Frame X.Ψ r)

theorem pv_ren (v : Fin r → E) : pv X (π.trans idx) x v = ren π (pv X idx x v) := rfl

private theorem perMat_trans_idx_eq_submatrix (s : Fin g → Fin g ⊕ Fin g) :
    perMat X bas (π.trans idx) s x = (perMat X bas idx s x).submatrix π (Equiv.refl _) := by
  ext i k
  simp [perMat_apply]

theorem hMat_ren : hMat X bas (π.trans idx) x = (hMat X bas idx x).submatrix (Equiv.refl _) π := by
  simp only [hMat]
  rw [perMat_trans_idx_eq_submatrix, Matrix.inv_submatrix_equiv]

theorem hMat_mulVec_ren (z : Fin g → ℂ) : hMat X bas (π.trans idx) x *ᵥ ren π z = hMat X bas idx x *ᵥ z := by
  rw [hMat_ren, ren_apply, Matrix.submatrix_mulVec_equiv]
  ext i
  simp [Function.comp_def]

theorem tauMat_ren : tauMat X bas (π.trans idx) x = tauMat X bas idx x := by
  simp only [tauMat]
  rw [hMat_ren, perMat_trans_idx_eq_submatrix, Matrix.submatrix_mul_equiv]
  simp

theorem imInv_ren : imInv X bas (π.trans idx) x = imInv X bas idx x := by
  simp only [imInv, tauMat_ren]

theorem hx_ren (z w : Fin g → ℂ) : hx X bas (π.trans idx) x (ren π z) (ren π w) = hx X bas idx x z w := by
  simp only [hx, hMat_mulVec_ren, imInv_ren]

def sg (π : Equiv.Perm (Fin g)) (n : ℕ) : ℂ := (((Equiv.Perm.sign π : ℤˣ) : ℤ) : ℂ) ^ (n / 2)

theorem letterDir_ren (hr : X.p0 + q0 = r) (ℓ : Harm.Var X.Ψ q0 X.p0 (Fin n)) :
    letterDir X hr (π.trans idx) ℓ = fun k => ren π (letterDir X hr idx ℓ k) := by
  funext k
  simp only [letterDir]
  by_cases h : k = ℓ.2.2
  · subst h
    simp only [Pi.single_eq_same, ren_single, Equiv.symm_trans_apply]
  · simp only [Pi.single_eq_of_ne h, map_zero]

variable {X bas idx x}

def anFibRen [Algebra c.F ℂ] {e : Fin g ≃ Lt1 Dw} {L : Lt E r} {y : FrPt Xo c ℂ}
    (A : AnFib X bas (π.trans idx) (π.trans e) x L y) : AnFib X bas idx e x L y where
  ex z := A.ex (ren π z)
  ex_add z w := by rw [map_add, A.ex_add]
  ex_onto := A.ex_onto.comp (ren π).surjective
  ex_ker z := by simp only [A.ex_ker, pv_ren, (ren π).injective.eq_iff]
  ex_lin a z := A.ex_lin a (ren π z)
  hol U f := ⟨(A.hol U f).1.preimage (ren π).continuous,
    (A.hol U f).2.comp (ren π).differentiable.differentiableOn fun _ h => h⟩
  der ℓ := by
    refine ⟨by simpa only [map_zero] using (A.der ℓ).1, fun U h f => ((A.der ℓ).2 U h f).trans ?_⟩
    have := (ren π).comp_right_fderiv (f := fun z => valAt' (A.ex z).left U f) (x := 0)
    rw [map_zero] at this
    change _ = fderiv ℂ ((fun z => valAt' (A.ex z).left U f) ∘ ren π) 0 _
    rw [this, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, ren_single]
    rfl
  fr j z := A.fr j (ren π z)
  fr_hol j := (A.fr_hol j).comp (ren π).differentiable.differentiableOn fun _ h => h
  fr_ne j z := A.fr_ne j _
  fr_g j j' z := A.fr_g j j' _
  fr_0 j := by rw [map_zero]; exact A.fr_0 j
  χ := A.χ
  χ_norm := A.χ_norm
  fr_per v hv j z h := by
    rw [A.fr_per v hv j _ h, pv_ren, hx_ren, hx_ren, map_add]

end Rename₂

def reindex₃ {σ : c.F →+* ℂ} {X : Data E r} {a : (E →+* ℂ) × ℕ → ℕ} (D : Dic Dw c σ X g q0 n a)
    (π : Equiv.Perm (Fin g)) : Dic Dw c σ X g q0 n a :=
  { D with
    idx := π.trans D.idx
    e := π.trans D.e
    per_eq := fun x v j => D.per_eq x v (π j)
    ty_eq := fun j => D.ty_eq (π j)
    dir_eq := fun ℓ => by
      rw [letterDir_ren, D.dir_eq]
      funext k
      by_cases h : k = ℓ.2.2
      · subst h
        simp only [Pi.single_eq_same, ren_single]
        rfl
      · simp only [Pi.single_eq_of_ne h, map_zero] }

def ClassSumValuesUnit : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r),
    Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → 1 ≤ r → l.A = 1 →
    ∀ (W : UW U) (k : U.Comp) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n →
    ∀ (g q0 : ℕ) (D : Dic Dw c σ (U.X k) g q0 n a) (v : TF n g),
      IsVac (U.X k) D.bas (H.w0 : E) (tens (stdLat E n) (U.X k).Λ) v →
      ∃ κ : ℂ, κ ≠ 0 ∧ IsModulus (U.X k) D.bas D.idx (H.w0 : E) v ‖κ‖ ∧ ReadsUnit U W k D v κ

end

end GlobalTheory.ClsVal.Cmp
