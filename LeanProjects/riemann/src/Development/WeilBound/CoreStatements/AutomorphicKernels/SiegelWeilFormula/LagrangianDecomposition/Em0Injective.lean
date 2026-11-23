import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LowerRankDatum

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def i0 {N n : ℕ} (h : n + 1 = N) : Fin N := ⟨n, by omega⟩

def em0 {N n : ℕ} (h : n + 1 = N) : Fin n → Fin N := fun i => ⟨i, by omega⟩

theorem em0_injective {N n : ℕ} (h : n + 1 = N) : Function.Injective (em0 h) := fun a b e => by
  simp only [em0, Fin.mk.injEq] at e
  exact Fin.ext e

theorem ne_last_iff_mem_range {N n : ℕ} (h : n + 1 = N) (i : Fin N) : i ≠ i0 h ↔ i ∈ Set.range (em0 h) := by
  constructor
  · intro hi
    refine ⟨⟨i.1, ?_⟩, Fin.ext rfl⟩
    have : i.1 ≠ n := fun e => hi (Fin.ext e)
    omega
  · rintro ⟨k, rfl⟩ e
    have := congrArg Fin.val e
    simp [em0, i0] at this
    omega

def jeps (n : ℕ) (ε : ℤˣ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E := Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0

def Tof {m n : ℕ} {A : Spc F E m} {Y : Spc F E n} (ψ : AddChar (AF F) ℂ) {κ : Type} [Fintype κ]
    (dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F A.J) (dbl (incM F Y.J))) κ) (l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ)
    (b : GL (Fin n ⊕ Fin n) E) (Φ : (κ → AF F) → ℂ) (X : Mx F E m n) : ℂ :=
  l (dd.rho ψ (X * (incM F b.1.toCols₂)ᵀ) Φ)

theorem T_eq (d : SD σ) (Φ : d.Fn) (X : Mx F E d.m d.n) : d.T Φ X = Tof d.B.ψ d.dd d.l d.b Φ X := rfl

def SignOK (d : SD σ) {n : ℕ} (Y : Spc F E n) : Prop :=
  d.A.IsHerm σ d.B d.r d.s ∧ (∀ i j, σ (Y.J j i) = -Y.J i j) ∨ d.A.IsSkew σ d.B d.r d.s ∧ ∀ i j, σ (Y.J j i) = Y.J i j

def IsJ (d : SD σ) {n : ℕ} (h : n + 1 = d.n) {Y : Spc F E n} (b : GL (Fin n ⊕ Fin n) E) (j : G2 σ Y →* d.G) : Prop :=
  Continuous j ∧
  (∀ g, (inFrame d.b (j g)).submatrix (Sum.map (em0 h) (em0 h)) (Sum.map (em0 h) (em0 h)) = inFrame b g) ∧
  ∀ g, ∀ u ∈ ({Sum.inl (i0 h), Sum.inr (i0 h)} : Set (Fin d.n ⊕ Fin d.n)), ∀ v,
    inFrame d.b (j g) u v = (1 : Matrix _ _ (AE F E)) u v ∧ inFrame d.b (j g) v u = (1 : Matrix _ _ (AE F E)) v u

def Res (d : SD σ) {n : ℕ} (h : n + 1 = d.n) {Y : Spc F E n} (b : GL (Fin n ⊕ Fin n) E) (j : G2 σ Y →* d.G) {κ : Type}
    [Fintype κ] (dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F d.A.J) (dbl (incM F Y.J))) κ)
    (om : G2 σ Y →* Module.End ℂ ((κ → AF F) → ℂ)) (l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) : Prop :=
  ∀ Φ ∈ d.sch, ∀ Φ' ∈ schA F κ,
    (∀ X : Mx F E d.m d.n, (∀ a, X a (i0 h) = 0) → Tof d.B.ψ dd l b Φ' (X.submatrix id (em0 h)) = d.T Φ X) →
    ∀ g (X : Mx F E d.m d.n), (∀ a, X a (i0 h) = 0) → Tof d.B.ψ dd l b (om g Φ') (X.submatrix id (em0 h)) = d.T (d.om (j g) Φ) X

def IsGenF {n : ℕ} {Y : Spc F E n} (b : GL (Fin n ⊕ Fin n) E) (x : G2 σ Y) : Prop :=
  (∃ β, inFrame b x = Matrix.fromBlocks 1 β 0 1) ∨
  (∃ t u : GL (Fin n) (AE F E), inFrame b x = Matrix.fromBlocks t.1 0 0 u.1) ∨
  (∃ γ, inFrame b x = Matrix.fromBlocks 1 0 γ 1)

end PositivityTheory.SiegelWeilFormula.Ald

end
