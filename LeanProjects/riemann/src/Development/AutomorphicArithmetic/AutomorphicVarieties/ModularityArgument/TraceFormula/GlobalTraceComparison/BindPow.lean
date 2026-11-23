import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.IsTransl
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HeckeLocalBlock
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8 (K2)
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison

inductive Ex (ι : Type) : Type
  | one : Ex ι
  | gen : ι → Ex ι
  | smul : ℂ → Ex ι → Ex ι
  | add : Ex ι → Ex ι → Ex ι
  | mul : Ex ι → Ex ι → Ex ι

namespace Ex

variable {ι κ : Type}

def ev (x : ι → ℂ) : Ex ι → ℂ
  | one => 1
  | gen i => x i
  | smul c a => c * a.ev x
  | add a b => a.ev x + b.ev x
  | mul a b => a.ev x * b.ev x

def pow (e : Ex ι) : ℕ → Ex ι
  | 0 => one
  | k + 1 => mul (e.pow k) e

def bind (τ : ι → Ex κ) : Ex ι → Ex κ
  | one => one
  | gen i => τ i
  | smul c a => smul c (a.bind τ)
  | add a b => add (a.bind τ) (b.bind τ)
  | mul a b => mul (a.bind τ) (b.bind τ)

theorem ev_pow (x : ι → ℂ) (e : Ex ι) (k : ℕ) : (e.pow k).ev x = e.ev x ^ k := by
  induction k with
  | zero => simp [pow, ev]
  | succ k ih => simp [pow, ev, ih, pow_succ]

theorem bind_pow (τ : ι → Ex κ) (e : Ex ι) (k : ℕ) : (e.pow k).bind τ = (e.bind τ).pow k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [pow, bind, ih]

def fn {G : Type} [Group G] (K : Subgroup G) (g : ι → G → ℂ) : Ex ι → G → ℂ
  | one => (K : Set G).indicator 1
  | gen i => g i
  | smul c a => fun y => c * a.fn K g y
  | add a b => fun y => a.fn K g y + b.fn K g y
  | mul a b => fun y => hint K fun z => a.fn K g z * b.fn K g (z⁻¹ * y)

end Ex

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n a b : ℕ}

def unif (w : Pl E) : w.adicCompletion E := Classical.epsilon (IsUnifV E w)

def fn1 (n : ℕ) (w : Pl E) (e : Ex (Fin (n + 1))) : GLw n w → ℂ :=
  e.fn (KGL w n) fun j : Fin (n + 1) => Tj ℂ n (Ov E w) (unif w) j

def ev1 (n : ℕ) (w : Pl E) (e : Ex (Fin (n + 1))) (B : Multiset ℂˣ) : ℂ := e.ev fun j : Fin (n + 1) => satEig (qV E w) n B j

def fn2 (a b : ℕ) (w : Pl E) (e : Ex (Fin (a + 1) × Fin (b + 1))) : GLw a w × GLw b w → ℂ :=
  e.fn (K2 a b w) fun p y => Tj ℂ a (Ov E w) (unif w) p.1 y.1 * Tj ℂ b (Ov E w) (unif w) p.2 y.2

def ev2 (a b : ℕ) (w : Pl E) (e : Ex (Fin (a + 1) × Fin (b + 1))) (B₁ B₂ : Multiset ℂˣ) : ℂ :=
  e.ev fun p => satEig (qV E w) a B₁ p.1 * satEig (qV E w) b B₂ p.2

def inv (B : Multiset ℂˣ) : Multiset ℂˣ := B.map (·⁻¹)

structure CD (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) where
  c : ℕ
  N : Fin c → ℕ
  P : ∀ i, CG E (N i)
  pos : ∀ i, 1 ≤ N i
  sum : ∑ i, N i = n

def CD.nil (E : Type) [Field E] [NumberField E] [IsCMField E] : CD E 0 := ⟨0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, rfl⟩

def CD.Sat (D : CD E n) (w : Pl E) (B : Multiset ℂˣ) : Prop :=
  ∃ b : Fin D.c → Multiset ℂˣ, (∀ i, (D.P i).HasSat w (b i)) ∧ ∑ i, b i = B

def CD.Has {m : ℕ} (D : CD E n) (π : CuspSub E m) : Prop := ∃ i, (⟨D.N i, D.P i⟩ : Σ k, CG E k) = ⟨m, CG.mk π⟩

def Off (Z : Finset (Pl E)) (w : Pl E) : Prop := w ∉ Z ∧ cPl w ∉ Z

def SplitIn (S : Set (Pl E)) (Z : Finset (Pl E)) : Prop := ∀ w ∈ Z, w ∈ S ∧ IsSplitAt w

def Lc {G : Type} [Group G] [TopologicalSpace G] (K : Subgroup G) (f : G → ℂ) : Prop :=
  ∃ K' : Subgroup G, IsOpen (K' : Set G) ∧ K' ≤ K ∧ IsHecke K' f

def trc {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G) (f : G → ℂ) : ℂ :=
  twTr ρ K (K ⊓ rStab f ⊓ rStab fun y => f y⁻¹) f LinearMap.id

def fam (Z T : Finset (Pl E)) (φ : ∀ w : Pl E, GLw a w × GLw b w → ℂ) (e₁ e₂ : Pl E → Ex (Fin (a + 1) × Fin (b + 1)))
    (k : ℕ) (w : Pl E) : GLw a w × GLw b w → ℂ :=
  if w ∈ Z then φ w else if w ∈ T then fn2 a b w (((e₁ w).pow k).mul ((e₂ w).pow k)) else (K2 a b w : Set _).indicator 1

def val (T : Finset (Pl E)) (e₁ e₂ : Pl E → Ex (Fin (a + 1) × Fin (b + 1))) (B₁ B₂ : Pl E → Multiset ℂˣ) : ℂ :=
  ∏ w ∈ T, ev2 a b w (e₁ w) (B₁ w) (B₂ w) * ev2 a b w (e₂ w) (inv (B₁ (cPl w))) (inv (B₂ (cPl w)))

def Small (ρ : ℝ) (x : ℕ → ℂ) : Prop := ∃ (C : ℝ) (N : ℕ), ∀ k, ‖x k‖ ≤ C * (1 + k) ^ N * ρ ^ k

end UpperTheory.V.Z.Tf.GlobalTraceComparison
