import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Formalism.LocalToGlobal.ProjectiveLattices.JFDFree
import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.GoodUniformizationCusps

open NumberField Formalism.L2.Pj Formalism.L2.PjFree ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

def IsGoodUnif (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) : Prop :=
  ∀ σ : c.F →+* ℂ, GoodEmb c σ → IsUnf (U σ)

def Cusp (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (_hn : Even n) :
    Submodule c.F (Rul Xo c) where
  carrier := {f | f ∈ sec Xo c a n ∧
    ∀ σ : c.F →+* ℂ, GoodEmb c σ → ∀ k : (U σ).Comp, rdU (U σ) f k ∈ ((U σ).X k).SS (laU (U σ) a n k)}
  zero_mem' := ⟨Submodule.zero_mem _, fun σ _ k => by
    rw [map_zero]
    exact (siegelSpaceAlgebra_holds r ((U σ).X k) (laU (U σ) a n k) (laU (U σ) a n k) 0).1.1⟩
  add_mem' := fun {f g} hf hg => ⟨Submodule.add_mem _ hf.1 hg.1, fun σ hσ k => by
    rw [map_add]
    exact (siegelSpaceAlgebra_holds r ((U σ).X k) (laU (U σ) a n k) (laU (U σ) a n k) 0).1.2.1 _ (hf.2 σ hσ k) _ (hg.2 σ hσ k)⟩
  smul_mem' := fun b f hf => ⟨Submodule.smul_mem _ b hf.1, fun σ hσ k => by
    rw [map_smulₛₗ]
    exact (siegelSpaceAlgebra_holds r ((U σ).X k) (laU (U σ) a n k) (laU (U σ) a n k) 0).1.2.2 _ _ (hf.2 σ hσ k)⟩

theorem mem_cusp (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hn : Even n)
    (f : Rul Xo c) : f ∈ Cusp U a n hn ↔ f ∈ sec Xo c a n ∧
      ∀ σ : c.F →+* ℂ, GoodEmb c σ → IsHolCusp (U σ).X (laU (U σ) a n) (rdU (U σ) f) := Iff.rfl

theorem cusp_le_sec (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hn : Even n) :
    Cusp U a n hn ≤ sec Xo c a n := fun _ hf => hf.1

variable (Xo c) in

def formMul (a a' : (E →+* ℂ) × ℕ → ℕ) (n n' : ℕ) (f : sec Xo c a n) (g : sec Xo c a' n') :
    sec Xo c (a + a') (n + n') :=
  ⟨(f : Rul Xo c) * (g : Rul Xo c), sec_mul Xo c a a' n n' f.2 g.2⟩

def CuspMulClosed (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) : Prop :=
  ∀ (a a' : (E →+* ℂ) × ℕ → ℕ) (n n' : ℕ) (h : Dom a n) (h' : Dom a' n'),
    ∀ f ∈ Cusp U a n h.2, ∀ g ∈ Cusp U a' n' h'.2, f * g ∈ Cusp U (a + a') (n + n') (h.2.add h'.2)

def CuspFinite (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hn : Even n), FiniteDimensional c.F (Cusp U a n hn)

variable (Xo c r) in

def CuspMulClaim : Prop :=
  ∀ U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r, IsGoodUnif U → CuspMulClosed U

variable (Xo c r) in

def CuspFiniteClaim : Prop :=
  ∀ U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r, IsGoodUnif U → CuspFinite U

theorem laU_add {σ : c.F →+* ℂ} (V : Unf Xo c σ r) (a a' : (E →+* ℂ) × ℕ → ℕ) {n n' : ℕ} (hn : Even n)
    (hn' : Even n') (k : V.Comp) : laU V (a + a') (n + n') k = laU V a n k + laU V a' n' k := by
  obtain ⟨m, rfl⟩ := hn
  obtain ⟨m', rfl⟩ := hn'
  funext τ j
  have e : (m + m + (m' + m')) / 2 = (m + m) / 2 + (m' + m') / 2 := by omega
  simp only [laU, Pi.add_apply, e]
  split_ifs <;> push_cast <;> ring

theorem rdU_mul {σ : c.F →+* ℂ} (V : Unf Xo c σ r) (f g : Rul Xo c) (k : V.Comp) :
    rdU V (f * g) k = rdU V f k * rdU V g k := by
  funext x
  simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, Pi.mul_apply]
  split_ifs with h
  · exact evalAt_mul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f g (V.un k ⟨x, h⟩)
  · simp

theorem cuspMulClosed (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) : CuspMulClosed U := by
  intro a a' n n' h h' f hf g hg
  refine ⟨sec_mul Xo c a a' n n' hf.1 hg.1, fun σ hσ k => ?_⟩
  rw [laU_add (U σ) a a' h.2 h'.2, rdU_mul]
  exact (siegelSpaceAlgebra_holds r ((U σ).X k) _ _ 0).2.1 _ (hf.2 σ hσ k) _ (hg.2 σ hσ k).1

def cuspMul (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) {a a' : (E →+* ℂ) × ℕ → ℕ} {n n' : ℕ} (h : Dom a n)
    (h' : Dom a' n') (f : Cusp U a n h.2) (g : Cusp U a' n' h'.2) : Cusp U (a + a') (n + n') (h.2.add h'.2) :=
  ⟨(f : Rul Xo c) * (g : Rul Xo c), cuspMulClosed U a a' n n' h h' f.1 f.2 g.1 g.2⟩

end GlobalTheory.IndefiniteRowSideFullHecke.GoodUniformizationCusps
