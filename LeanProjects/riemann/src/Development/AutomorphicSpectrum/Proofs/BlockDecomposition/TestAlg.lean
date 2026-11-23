import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace GlobalTheory.CompanionTheory.EisM

section Abstract

variable {X H : Type}

def TestAlg [TopologicalSpace X] (A : Submodule ℂ (X → ℂ)) : Prop :=
  (∀ f ∈ A, Continuous f ∧ HasCompactSupport f) ∧ (∀ f ∈ A, ∀ g ∈ A, f * g ∈ A) ∧ (∀ f ∈ A, star f ∈ A) ∧
    (∀ x y, x ≠ y → ∃ f ∈ A, f x ≠ f y) ∧
    ∀ C, IsCompact C → ∃ f ∈ A, (∀ x, 0 ≤ (f x).re ∧ (f x).im = 0) ∧ ∀ x ∈ C, f x = 1

def InJ [MeasurableSpace X] [MeasurableSpace H] (lam : Measure H) (Q : Measure X) (p : H → X → ℂ) (ξ : X → ℂ) : Prop :=
  Integrable ξ Q ∧ Integrable (fun x => ∫ z, ξ z * p x z ∂Q) lam

def LJ [MeasurableSpace X] [MeasurableSpace H] (lam : Measure H) (Q : Measure X) (p : H → X → ℂ) (ξ : X → ℂ) : ℂ :=
  ∫ x, ∫ z, ξ z * p x z ∂Q ∂lam

end Abstract

variable {D : D7} {N r t n : ℕ}

abbrev XS (e : AE D) (N r t : ℕ) : Type := {z : Mx D N r × Mx D N t // e • z.1 = z.1 ∧ e • z.2 = z.2}

def testA (θ : InfFam D) (S : Finset (Pl D)) (e : AE D) (hn : r + t = n) : Submodule ℂ (XS e N r t → ℂ) where
  carrier := {f | ∃ Φ ∈ schwartzA θ N n, Good S e Φ ∧ HasCompactSupport Φ ∧ ∀ z : XS e N r t, f z = Φ (jn hn z.1.1 z.1.2)}
  add_mem' := by
    rintro f f' ⟨Φ, h₁, h₂, h₃, h₄⟩ ⟨Φ', h₁', h₂', h₃', h₄'⟩
    refine ⟨Φ + Φ', Submodule.add_mem _ h₁ h₁', fun x => ?_, h₃.add h₃', fun z => ?_⟩
    · have a := h₂ x
      have b := h₂' x
      by_cases h : IntOff S x
      · simp only [Pi.add_apply, if_pos h] at a b ⊢
        rw [a, b]
      · simp only [Pi.add_apply, if_neg h] at a b ⊢
        rw [a, b, add_zero]
    · simp only [Pi.add_apply, h₄, h₄']
  zero_mem' := by
    refine ⟨0, Submodule.zero_mem _, fun x => ?_, HasCompactSupport.zero, fun z => rfl⟩
    simp
  smul_mem' := by
    rintro c f ⟨Φ, h₁, h₂, h₃, h₄⟩
    refine ⟨c • Φ, Submodule.smul_mem _ c h₁, fun x => ?_, h₃.smul_left, fun z => ?_⟩
    · have a := h₂ x
      by_cases h : IntOff S x
      · simp only [Pi.smul_apply, if_pos h] at a ⊢
        rw [a]
      · simp only [Pi.smul_apply, if_neg h] at a ⊢
        rw [a, smul_zero]
    · simp only [Pi.smul_apply, h₄]

def toXS {e : AE D} (he : e * e = e) (z : Mx D N r × Mx D N t) : XS e N r t :=
  ⟨(e • z.1, e • z.2), by simp only [smul_smul, he, and_self]⟩

def PS {e : AE D} (he : e * e = e) (S : Finset (Pl D)) (P : Measure (Mx D N r × Mx D N t)) : Measure (XS e N r t) :=
  (P.restrict {z | IntOff S z.1 ∧ IntOff S z.2}).map (toXS he)

def pk (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) (b₀ : HermE D r) {e : AE D} (x : hermS D t e) (z : XS e V.rank r t) : ℂ :=
  pch ψ x.1.1 (qv V b₀ z.1)

def xi (V : HSp D) (b₀ : HermE D r) (hn : r + t = n) {e : AE D} (Φ : Mx D V.rank n → ℂ) (η : Mx D r t → ℂ)
    (z : XS e V.rank r t) : ℂ :=
  Φ (jn hn z.1.1 z.1.2) * conj (η (yv V b₀ z.1))

def phiU (V : HSp D) (r t : ℕ) (h : GA D V) : (Mx D V.rank r × Mx D V.rank t) ≃ₜ (Mx D V.rank r × Mx D V.rank t) where
  toFun z := (mm (mt V h) z.1, mm (mt V h) z.2)
  invFun z := (mm (mt V h⁻¹) z.1, mm (mt V h⁻¹) z.2)
  left_inv z := by
    have e₁ : mt V h⁻¹ * mt V h = 1 := by
      simp only [Formalism.L2.Theta.mt]
      rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
    refine Prod.ext ?_ ?_
    · change (mt V h⁻¹ * (mt V h * z.1 : Matrix _ _ _) : Matrix _ _ _) = z.1
      rw [← Matrix.mul_assoc, e₁, Matrix.one_mul]
    · change (mt V h⁻¹ * (mt V h * z.2 : Matrix _ _ _) : Matrix _ _ _) = z.2
      rw [← Matrix.mul_assoc, e₁, Matrix.one_mul]
  right_inv z := by
    have e₁ : mt V h * mt V h⁻¹ = 1 := by
      simp only [Formalism.L2.Theta.mt]
      rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
    refine Prod.ext ?_ ?_
    · change (mt V h * (mt V h⁻¹ * z.1 : Matrix _ _ _) : Matrix _ _ _) = z.1
      rw [← Matrix.mul_assoc, e₁, Matrix.one_mul]
    · change (mt V h * (mt V h⁻¹ * z.2 : Matrix _ _ _) : Matrix _ _ _) = z.2
      rw [← Matrix.mul_assoc, e₁, Matrix.one_mul]
  continuous_toFun := (continuous_const.matrix_mul continuous_fst).prodMk (continuous_const.matrix_mul continuous_snd)
  continuous_invFun := (continuous_const.matrix_mul continuous_fst).prodMk (continuous_const.matrix_mul continuous_snd)

def phiS (N : ℕ) (y : Mx D r t) : (Mx D N r × Mx D N t) ≃ₜ (Mx D N r × Mx D N t) where
  toFun z := (z.1, z.2 + mm z.1 y)
  invFun z := (z.1, z.2 + mm z.1 (-y))
  left_inv z := by simp [Matrix.mul_neg]
  right_inv z := by simp [Matrix.mul_neg]
  continuous_toFun := continuous_fst.prodMk (continuous_snd.add (continuous_fst.matrix_mul continuous_const))
  continuous_invFun := continuous_fst.prodMk (continuous_snd.add (continuous_fst.matrix_mul continuous_const))

def phiG (N r : ℕ) (g : GL (Fin t) (AE D)) : (Mx D N r × Mx D N t) ≃ₜ (Mx D N r × Mx D N t) where
  toFun z := (z.1, mm z.2 g.1)
  invFun z := (z.1, mm z.2 (g⁻¹).1)
  left_inv z := by
    have e₁ : g.1 * (g⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    refine Prod.ext rfl ?_
    change ((z.2 * g.1 : Matrix _ _ _) * (g⁻¹).1 : Matrix _ _ _) = z.2
    rw [Matrix.mul_assoc, e₁, Matrix.mul_one]
  right_inv z := by
    have e₁ : (g⁻¹).1 * g.1 = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    refine Prod.ext rfl ?_
    change ((z.2 * (g⁻¹).1 : Matrix _ _ _) * g.1 : Matrix _ _ _) = z.2
    rw [Matrix.mul_assoc, e₁, Matrix.mul_one]
  continuous_toFun := continuous_fst.prodMk (continuous_snd.matrix_mul continuous_const)
  continuous_invFun := continuous_fst.prodMk (continuous_snd.matrix_mul continuous_const)

def tauG {e : AE D} (g : GL (Fin t) (AE D)) (x : hermS D t e) : hermS D t e :=
  ⟨⟨mm (mm (g⁻¹).1 x.1.1) (adj (g⁻¹).1), by
      have hx : adj x.1.1 = x.1.1 := x.1.2
      change adj (mm (mm (g⁻¹).1 x.1.1) (adj (g⁻¹).1)) = _
      simp only [mm, adj_mul, adj_adj, hx]
      rw [Matrix.mul_assoc]⟩, by
      have hx : e • x.1.1 = x.1.1 := x.2
      change e • (mm (mm (g⁻¹).1 x.1.1) (adj (g⁻¹).1)) = _
      simp only [mm]
      rw [← Matrix.smul_mul, ← Matrix.mul_smul, hx]⟩

end GlobalTheory.CompanionTheory.EisM

namespace GlobalTheory.CompanionTheory.EisM
variable {D : D7} {N r t n : ℕ}

def liftU {e : AE D} (V : HSp D) (r t : ℕ) (h : GA D V) : XS e V.rank r t ≃ₜ XS e V.rank r t :=
  (phiU V r t h).subtype (fun z => by
    have a : ∀ {k : ℕ} (x : Mx D V.rank k), e • mm (mt V h) x = mm (mt V h) (e • x) := fun x => (Matrix.mul_smul _ _ _).symm
    have b : ∀ {k : ℕ} (x : Mx D V.rank k), e • mm (mt V h) x = mm (mt V h) x → e • x = x := fun {k} x hx => by
      have i := congrArg (fun y => mm (mt V h⁻¹) y) hx
      have l : ∀ y : Mx D V.rank k, mm (mt V h⁻¹) (mm (mt V h) y) = y := fun y =>
        congrArg Prod.fst ((phiU V k k h).left_inv (y, y))
      simpa only [a, l] using i
    refine ⟨fun hz => ⟨?_, ?_⟩, fun hz => ⟨b _ hz.1, b _ hz.2⟩⟩
    · change e • mm (mt V h) z.1 = mm (mt V h) z.1
      rw [a, hz.1]
    · change e • mm (mt V h) z.2 = mm (mt V h) z.2
      rw [a, hz.2])

def liftS {e : AE D} (N : ℕ) (y : Mx D r t) : XS e N r t ≃ₜ XS e N r t :=
  (phiS N y).subtype (fun z => by
    have a : ∀ x : Mx D N r, e • x = x → e • mm x y = mm x y := fun x hx => by
      simp only [mm]
      rw [← Matrix.smul_mul, hx]
    refine ⟨fun hz => ⟨hz.1, ?_⟩, fun hz => ⟨hz.1, ?_⟩⟩
    · change e • (z.2 + mm z.1 y) = z.2 + mm z.1 y
      rw [smul_add, hz.2, a _ hz.1]
    · have h₂ : e • (z.2 + mm z.1 y) = z.2 + mm z.1 y := hz.2
      have h₁ : e • z.1 = z.1 := hz.1
      rw [smul_add, a _ h₁] at h₂
      exact add_right_cancel h₂)

def liftG {e : AE D} (N r : ℕ) (g : GL (Fin t) (AE D)) : XS e N r t ≃ₜ XS e N r t :=
  (phiG N r g).subtype (fun z => by
    have a : ∀ x : Mx D N t, e • mm x g.1 = mm (e • x) g.1 := fun x => (Matrix.smul_mul _ _ _).symm
    refine ⟨fun hz => ⟨hz.1, ?_⟩, fun hz => ⟨hz.1, ?_⟩⟩
    · change e • mm z.2 g.1 = mm z.2 g.1
      rw [a, hz.2]
    · have h₂ : e • mm z.2 g.1 = mm z.2 g.1 := hz.2
      have i := congrArg (fun y => mm y (g⁻¹).1) h₂
      have l : ∀ y : Mx D N t, mm (mm y g.1) (g⁻¹).1 = y := fun y =>
        congrArg Prod.snd ((phiG N r g).left_inv ((0 : Mx D N r), y))
      simpa only [a, l] using i)

end GlobalTheory.CompanionTheory.EisM
