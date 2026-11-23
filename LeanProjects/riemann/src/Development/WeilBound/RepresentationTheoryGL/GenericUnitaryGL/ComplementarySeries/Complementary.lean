import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SegmentDerivatives.DerivJac
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.RightWhit
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspLinesIrr

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil

namespace PositivityTheory.RgGu.NR

section N

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def DerEquiv : Prop :=
  ∀ (ψ : AddChar k Circle) (n j : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin (n + j + 1)) k) V),
    Nonempty ((GlobalTheory.BZMir.deriv k ψ j π).Equiv (GlobalTheory.BZMir.derRep k ψ (show n + (j + 1) = n + j + 1 from rfl) π))

def DerFin : Prop :=
  ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n j : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin (n + j + 1)) k) V), IsSmooth π → π.IsIrreducible →
    HasFiniteLength (GlobalTheory.BZMir.deriv k ψ j π)

end N

section Forms

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def HasSesq (π : Representation ℂ G V) : Prop :=
  ∃ B : V →ₗ[ℂ] V →ₛₗ[starRingEnd ℂ] ℂ, B ≠ 0 ∧ ∀ g v w, B (π g v) (π g w) = B v w

def ConjEquiv (π : Representation ℂ G V) (σ : Representation ℂ G W) : Prop :=
  ∃ φ : V →ₛₗ[starRingEnd ℂ] W, Function.Bijective φ ∧ ∀ g v, φ (π g v) = σ g (φ v)

structure IsFamily (K₀ : Subgroup G) (F : ℝ → Representation ℂ G V) : Prop where
  const : ∀ s, ∀ x ∈ K₀, F s x = F 0 x
  expo : ∀ (g : G) (v : V), ∃ (m : ℕ) (r : Fin m → ℝ) (u : Fin m → V),
    ∀ s, F s g v = ∑ i, ((Real.exp (r i * s) : ℝ) : ℂ) • u i

end Forms

def Signature : Prop :=
  ∀ (I W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ι : I → I) (T : ℝ → I → Module.End ℂ W),
    (∀ (i : I) (w : W) (l : Module.Dual ℂ W), Continuous fun s => l (T s i w)) →
    (∀ s, 0 ≤ s → ∀ U : Submodule ℂ W, (∀ i, ∀ w ∈ U, T s i w ∈ U) → U = ⊥ ∨ U = ⊤) →
    (∀ s, 0 ≤ s → ∃ B : W →ₗ[ℂ] W →ₛₗ[starRingEnd ℂ] ℂ, B ≠ 0 ∧ (∀ v w, B w v = starRingEnd ℂ (B v w)) ∧
      ∀ i v w, B (T s i v) w = B v (T s (ι i) w)) →
    (∃ B : W →ₗ[ℂ] W →ₛₗ[starRingEnd ℂ] ℂ, (∀ v w, B w v = starRingEnd ℂ (B v w)) ∧ (∀ v, v ≠ 0 → 0 < (B v v).re) ∧
      ∀ i v w, B (T 0 i v) w = B v (T 0 (ι i) w)) →
    Function.Surjective ι →
    ∀ s, 0 ≤ s → ∀ B : W →ₗ[ℂ] W →ₛₗ[starRingEnd ℂ] ℂ, B ≠ 0 → (∀ v w, B w v = starRingEnd ℂ (B v w)) →
      (∀ i v w, B (T s i v) w = B v (T s (ι i) w)) →
      (∀ v, v ≠ 0 → 0 < (B v v).re) ∨ ∀ v, v ≠ 0 → (B v v).re < 0

def Complementary : Prop :=
  ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (K₀ : Subgroup G), IsOpen (K₀ : Set G) → IsCompact (K₀ : Set G) → ∀ F : ℝ → Representation ℂ G V, IsFamily K₀ F →
    (∀ s, 0 ≤ s → IsAdmissible (F s) ∧ IsSmooth (F s) ∧ (F s).IsIrreducible ∧ HasSesq (F s)) →
    IsUnitarisable (F 0) → ∀ s, 0 ≤ s → IsUnitarisable (F s)

section R

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def chi (d : ℕ) (s : ℝ) : Levi k (fun _ : Fin 2 => Fin d) →* ℂˣ :=
  ((detChar (Fin d) (absPow k (-(s : ℂ)))).comp (Pi.evalMonoidHom (fun _ : Fin 2 => GL (Fin d) k) 0)) *
    ((detChar (Fin d) (absPow k (s : ℂ))).comp (Pi.evalMonoidHom (fun _ : Fin 2 => GL (Fin d) k) 1))

theorem sum_two (d : ℕ) : ∑ _a : Fin 2, d = d + d := by simp [two_mul]

def blk2 (d : ℕ) : (Σ _ : Fin 2, Fin d) ≃ Fin (d + d) := stdBlocks (fun _ : Fin 2 => d) (sum_two d)

def Compact : Prop :=
  ∀ (d : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Levi k fun _ : Fin 2 => Fin d) W),
    ∃ (K₀ : Subgroup (GL (Fin (d + d)) k)) (F : ℝ → Representation ℂ (GL (Fin (d + d)) k) (IndSp (blk2 d) τ)),
      IsOpen (K₀ : Set (GL (Fin (d + d)) k)) ∧ IsCompact (K₀ : Set (GL (Fin (d + d)) k)) ∧ IsFamily K₀ F ∧
        ∀ s, Nonempty ((F s).Equiv (parInd (blk2 d) (twist τ (chi k d s))))

def Bound : Prop :=
  ∀ (d : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] [Nontrivial W]
    (τ : Representation ℂ (Levi k fun _ : Fin 2 => Fin d) W), IsSmooth τ →
    IsAdmissible (parInd (blk2 d) τ) → IsUnitarisable (parInd (blk2 d) τ) → ∀ (t : kˣ) (c : ℂ), nabs k t ≤ 1 →
      (∀ w, τ ![Matrix.GeneralLinearGroup.scalar (Fin d) t, 1] w = c • w) →
        ‖c‖ * nabs k t ^ (((d * d : ℕ) : ℝ) / 2) ≤ 1

def ConjProd : Prop :=
  ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (X Y : Fin h → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)] (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a))
    (σ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (Y a)), (∀ a, ConjEquiv (π a) (σ a)) →
      ConjEquiv (multiProd (stdBlocks d hd) π) (multiProd (stdBlocks d hd) σ)

def ConjDual : Prop :=
  ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) k) V), IsSmooth ρ →
    ρ.IsIrreducible → IsUnitarisable ρ → ∀ s : ℝ,
      ConjEquiv (twist ρ (detChar (Fin n) (absPow k (s : ℂ)))) (twist (contra ρ) (detChar (Fin n) (absPow k (s : ℂ))))

def Herm : Prop :=
  ∀ (x : IrrGL k), IsUnitarisable x.rep → ∀ (s : ℝ) (N : ℕ) (hd : ∑ a, (![x.nu (-(s : ℂ)), x.nu (s : ℂ)] a).1 = N),
    (prodIrr ![x.nu (-(s : ℂ)), x.nu (s : ℂ)] hd).IsIrreducible → HasSesq (prodIrr ![x.nu (-(s : ℂ)), x.nu (s : ℂ)] hd)

def ProdModel : Prop :=
  ∀ (x : IrrGL k) (s : ℝ) (hd : ∑ a, (![x.nu (-(s : ℂ)), x.nu (s : ℂ)] a).1 = x.1 + x.1),
    Nonempty ((prodIrr ![x.nu (-(s : ℂ)), x.nu (s : ℂ)] hd).Equiv
      (parInd (blk2 x.1) (twist (piTensor fun _ : Fin 2 => x.rep) (chi k x.1 s))))

def CuspUnit : Prop := ∀ y : IrrGL k, y.IsCusp → ∃ (ρ : IrrGL k) (z : ℝ), ρ.IsCusp ∧ IsUnitarisable ρ.rep ∧ y = ρ.nu z

def SomeRed : Prop :=
  ∀ (x : IrrGL k), x.IsCusp → IsUnitarisable x.rep →
    ∃ s : ℝ, 0 ≤ s ∧ ∀ (N : ℕ) (hd : ∑ a, (![x.nu (-(s : ℂ)), x.nu (s : ℂ)] a).1 = N),
      ¬ (prodIrr ![x.nu (-(s : ℂ)), x.nu (s : ℂ)] hd).IsIrreducible

def RedCl : Prop :=
  ∀ (y : IrrGL k), y.IsCusp → ∀ (N : ℕ) (hd : ∑ a, (![y, y.nu 1] a).1 = N), ¬ (prodIrr ![y, y.nu 1] hd).IsIrreducible

end R

end PositivityTheory.RgGu.NR

end
