import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RCocompactPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.UnipRat
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant

noncomputable section

open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp
open Formalism.L2.SG.Pf.UnipB Formalism.L2.SG.Pf.Unip

namespace Formalism.L2.SG.TermOp.Vanish

def MemIsomOf : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (g : GL (Fin X.B.I.n) X.B.I.E), g ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J →
    ∃ n : (VS D).V ≃ₗ[D.host.E] (VS D).V, n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧
      ∀ y, X.crd (n y) = (g : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ X.crd y

def MemFlagOf : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (Z : Matrix (Kap X) (Kap X) X.B.I.E)
    (n : (VS D).V ≃ₗ[D.host.E] (VS D).V), InPat (lvk X) 1 Z → (∀ y, X.crd (n y) = gE X Z *ᵥ X.crd y) →
    (∀ j, ∀ x ∈ Xflag (lf D (X.Fu u)) (j + 1), n x - x ∈ Xflag (lf D (X.Fu u)) j) ∧
      ∀ x ∈ orth (VS D) (Xsp (lf D (X.Fu u))), n x - x ∈ Xsp (lf D (X.Fu u))

def MemLatOf : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Λ : Submodule (𝓞 D.host.E) (VS D).V), Submodule.IsLattice D.host.E Λ →
    ∃ d : ℕ, 1 ≤ d ∧ ∀ (Z : Matrix (Kap X) (Kap X) X.B.I.E) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V),
      InPat (lvk X) 1 Z → (∃ A : Matrix (Kap X) (Kap X) (𝓞 X.B.I.E), Z = (d : X.B.I.E) • A.map (fun a => (a : X.B.I.E))) →
      (∀ y, X.crd (n y) = gE X Z *ᵥ X.crd y) → Formalism.HermitianLatticesTheory.gmap n Λ = Λ

def MemConjOf : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (M : GL (Fin X.B.I.n) X.B.I.E), M ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J →
    (∀ Z : Matrix (Kap X) (Kap X) X.B.I.E, (↑M⁻¹ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) * gE X Z *
      (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) =
        gE X (Gr X (↑M⁻¹ : Matrix _ _ _) * Z * Gr X (M : Matrix _ _ _))) ∧
    (∀ Z : Matrix (Kap X) (Kap X) X.B.I.E, Zᴴ * JB X = -(JB X * Z) →
      (Gr X (↑M⁻¹ : Matrix _ _ _) * Z * Gr X (M : Matrix _ _ _))ᴴ * JB X =
        -(JB X * (Gr X (↑M⁻¹ : Matrix _ _ _) * Z * Gr X (M : Matrix _ _ _)))) ∧
    ∃ c : ℕ, 1 ≤ c ∧ ∀ (d : ℕ) (A : Matrix (Kap X) (Kap X) (𝓞 X.B.I.E)),
      ∃ A' : Matrix (Kap X) (Kap X) (𝓞 X.B.I.E),
        Gr X (↑M⁻¹ : Matrix _ _ _) * (((c * d : ℕ) : X.B.I.E) • A.map (fun a => (a : X.B.I.E))) *
          Gr X (M : Matrix _ _ _) = (d : X.B.I.E) • A'.map (fun a => (a : X.B.I.E))

def MemPtOf : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Z : Matrix (Kap X) (Kap X) X.B.I.E) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V),
    n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → (∀ y, X.crd (n y) = gE X Z *ᵥ X.crd y) →
    ∃ x : X.B.I.GA, RatLink X x n ∧ ∀ v, Mv X v x.1 = (cay (2 * D.R.rS + 2) Z).map (X.B.I.φ v)

theorem ratMem_of (h1 : MemIsomOf) (h2 : MemFlagOf) (h3 : MemLatOf) (h4 : MemConjOf) (h5 : MemPtOf) : RatMem := by
  intro D X Y u u' t M hM hlin
  obtain ⟨d1, hd1, H1⟩ := h3 D X t.lam ((Y.rowsOK u).1 t.lam t.mem).1.1
  obtain ⟨d2, hd2, H2⟩ := h3 D X t.lam' ((Y.rowsOK u').1 t.lam' t.mem').1.1
  obtain ⟨hc1, hsk, c, hc, hdiv⟩ := h4 D X M hM
  have crd_inj : ∀ a b : (VS D).V, X.crd a = X.crd b → a = b := fun a b h => by
    rw [← Formalism.L2.SG.Pf.Level.toV_crd X a, h, Formalism.L2.SG.Pf.Level.toV_crd]
  refine ⟨c * d2 * d1, Nat.one_le_iff_ne_zero.2 (by positivity), fun Z hZ hZ' hZs hA => ?_⟩
  obtain ⟨A, hA⟩ := hA
  obtain ⟨n, hni, hn⟩ := h1 D X (gGL X le_rfl hZ) (gGL_mem X le_rfl hZ hZs)
  have hn' : ∀ y, X.crd (n y) = gE X Z *ᵥ X.crd y := hn
  have hZs' := hsk Z hZs
  obtain ⟨m, hmi, hm⟩ := h1 D X (gGL X le_rfl hZ') (gGL_mem X le_rfl hZ' hZs')
  have hm' : ∀ y, X.crd (m y) =
      gE X (Gr X (↑M⁻¹ : Matrix _ _ _) * Z * Gr X (M : Matrix _ _ _)) *ᵥ X.crd y := hm
  have hinv : ∀ y, X.crd (t.lin⁻¹ y) = (↑M⁻¹ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ X.crd y := by
    intro y
    have e := hlin (t.lin⁻¹ y)
    have : t.lin (t.lin⁻¹ y) = y := by
      show (t.lin * t.lin⁻¹) y = y
      rw [mul_inv_cancel]; rfl
    rw [this] at e
    rw [e, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hconj : t.lin⁻¹ * n * t.lin = m := by
    apply LinearEquiv.ext
    intro y
    apply crd_inj
    show X.crd (t.lin⁻¹ (n (t.lin y))) = _
    rw [hinv, hn', hlin, hm', Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hc1]
  have e1 : Z = (d1 : X.B.I.E) • ((((c * d2 : ℕ) : 𝓞 X.B.I.E)) • A).map (fun a => (a : X.B.I.E)) := by
    rw [hA]
    ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    push_cast
    ring
  have e2 : Z = ((c * d2 : ℕ) : X.B.I.E) • ((((d1 : ℕ) : 𝓞 X.B.I.E)) • A).map (fun a => (a : X.B.I.E)) := by
    rw [hA]
    ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    push_cast
    ring
  obtain ⟨A', hA'⟩ := hdiv d2 ((((d1 : ℕ) : 𝓞 X.B.I.E)) • A)
  have hnN : n ∈ NLam t.lam (lf D (X.Fu u)) :=
    ⟨⟨hni, H1 Z n hZ ⟨_, e1⟩ hn'⟩, h2 D X u Z n hZ hn'⟩
  have hmN : t.lin⁻¹ * n * t.lin ∈ NLam t.lam' (lf D (X.Fu u')) := by
    rw [hconj]
    refine ⟨⟨hmi, H2 _ m hZ' ⟨A', ?_⟩ hm'⟩, h2 D X u' _ m hZ' hm'⟩
    rw [← hA', ← e2]
  obtain ⟨x, hx, hMv⟩ := h5 D X Z n hni hn'
  exact ⟨x.1, ⟨x, n, hx, rfl, hnN, hmN⟩, hMv⟩

end Formalism.L2.SG.TermOp.Vanish
