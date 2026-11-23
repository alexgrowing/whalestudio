import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FiniteNonunitMatrix

open Matrix

namespace GlobalTheory.CompanionTheory.Ar.RT.CellSplit

open GlobalTheory.WeilM

section Lift

variable {S E₁ E₂ : Type} [CommRing S] [CommRing E₁] [CommRing E₂] (s : S ≃+* E₁ × E₂)

def pr₁ : S →+* E₁ := (RingHom.fst E₁ E₂).comp (s : S →+* E₁ × E₂)

def pr₂ : S →+* E₂ := (RingHom.snd E₁ E₂).comp (s : S →+* E₁ × E₂)

theorem pr₁_apply (x : S) : pr₁ s x = (s x).1 := rfl

theorem pr₂_apply (x : S) : pr₂ s x = (s x).2 := rfl

theorem mat_ext {m n : Type} {A B : Matrix m n S} (h1 : A.map (pr₁ s) = B.map (pr₁ s))
    (h2 : A.map (pr₂ s) = B.map (pr₂ s)) : A = B := by
  ext i j
  have e1 : (A.map (pr₁ s)) i j = (B.map (pr₁ s)) i j := by rw [h1]
  have e2 : (A.map (pr₂ s)) i j = (B.map (pr₂ s)) i j := by rw [h2]
  simp only [Matrix.map_apply, pr₁_apply, pr₂_apply] at e1 e2
  exact s.injective (Prod.ext e1 e2)

variable {n : Type} [DecidableEq n]

def lift (x : Matrix n n E₁) : Matrix n n S :=
  Matrix.of fun i j => s.symm (x i j, (1 : Matrix n n E₂) i j)

theorem lift_map₁ (x : Matrix n n E₁) : (lift s x).map (pr₁ s) = x := by
  ext i j
  simp only [lift, Matrix.map_apply, Matrix.of_apply, pr₁_apply, RingEquiv.apply_symm_apply]

theorem lift_map₂ (x : Matrix n n E₁) : (lift s x).map (pr₂ s) = 1 := by
  ext i j
  simp only [lift, Matrix.map_apply, Matrix.of_apply, pr₂_apply, RingEquiv.apply_symm_apply]

theorem map_one' {T : Type} [CommRing T] (f : S →+* T) : (1 : Matrix n n S).map f = 1 := by
  exact Matrix.map_one f (map_zero f) (map_one f)

theorem lift_one : lift s (1 : Matrix n n E₁) = 1 := by
  apply mat_ext s
  · rw [lift_map₁, map_one']
  · rw [lift_map₂, map_one']

theorem lift_mul [Fintype n] (x y : Matrix n n E₁) : lift s (x * y) = lift s x * lift s y := by
  apply mat_ext s
  · rw [Matrix.map_mul, lift_map₁, lift_map₁, lift_map₁]
  · rw [Matrix.map_mul, lift_map₂, lift_map₂, lift_map₂, Matrix.one_mul]

variable [Fintype n]

def liftHom : Matrix n n E₁ →* Matrix n n S where
  toFun := lift s
  map_one' := lift_one s
  map_mul' := lift_mul s

def glLift : GL n E₁ →* GL n S := Units.map (liftHom s)

theorem glLift_coe (x : GL n E₁) : ((glLift s x : GL n S) : Matrix n n S) = lift s (x : Matrix n n E₁) := rfl

def glPr : GL n S →* GL n E₁ := Units.map (RingHom.mapMatrix (pr₁ s) : Matrix n n S →+* Matrix n n E₁).toMonoidHom

theorem glPr_coe (x : GL n S) : ((glPr s x : GL n E₁) : Matrix n n E₁) = (x : Matrix n n S).map (pr₁ s) := rfl

end Lift

theorem dbl_map {S T β : Type} [CommRing S] [CommRing T] (f : S →+* T) (J : Matrix β β S) :
    (dbl J).map f = dbl (J.map f) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [dbl]

theorem diagCols_map {S T β : Type} [CommRing S] [CommRing T] [DecidableEq β] (f : S →+* T) :
    (diagCols β : Matrix (β ⊕ β) β S).map f = diagCols β := by
  ext i j
  rcases i with i | i
  · by_cases h : i = j
    · subst h
      simp [diagCols]
    · simp [diagCols, Matrix.one_apply_ne h]
  · by_cases h : i = j
    · subst h
      simp [diagCols]
    · simp [diagCols, Matrix.one_apply_ne h]

theorem lift_diag {S E₁ E₂ β : Type} [CommRing S] [CommRing E₁] [CommRing E₂] (s : S ≃+* E₁ × E₂) [Fintype β]
    [DecidableEq β] (A : Matrix (β ⊕ β) (β ⊕ β) E₁) (B : Matrix β β E₁)
    (h : A * (diagCols β : Matrix (β ⊕ β) β E₁) = (diagCols β : Matrix (β ⊕ β) β E₁) * B) :
    lift s A * (diagCols β : Matrix (β ⊕ β) β S) = (diagCols β : Matrix (β ⊕ β) β S) * lift s B := by
  apply mat_ext s
  · rw [Matrix.map_mul, Matrix.map_mul, lift_map₁, lift_map₁, diagCols_map, h]
  · rw [Matrix.map_mul, Matrix.map_mul, lift_map₂, lift_map₂, diagCols_map, Matrix.one_mul, Matrix.mul_one]

section Unitary

variable {k R S E₁ E₂ : Type} [CommRing k] [CommRing R] [CommRing S] [Algebra R S] [CommRing E₁] [Algebra k E₁] [CommRing E₂]
  (c : S →ₐ[R] S) (c₁ : E₁ →ₐ[k] E₁) (c₂ : E₂ →+* E₂) (s : S ≃+* E₁ × E₂)
  (hc1 : ∀ x, (s (c x)).1 = c₁ (s x).1) (hc2 : ∀ x, (s (c x)).2 = c₂ (s x).2)

include hc1 in
theorem map_c₁ {m n : Type} (A : Matrix m n S) : (A.map c).map (pr₁ s) = (A.map (pr₁ s)).map c₁ := by
  ext i j
  simp only [Matrix.map_apply, pr₁_apply, hc1]

include hc2 in
theorem map_c₂ {m n : Type} (A : Matrix m n S) : (A.map c).map (pr₂ s) = (A.map (pr₂ s)).map c₂ := by
  ext i j
  simp only [Matrix.map_apply, pr₂_apply, hc2]

variable {β : Type} [Fintype β] [DecidableEq β] (J : Matrix β β S)

include hc1 hc2 in
theorem lift_mem (x : UG c₁ (dbl (J.map (pr₁ s)))) :
    glLift s (x : GL (β ⊕ β) E₁) ∈ UG c (dbl J) := by
  have hx : ((x : GL (β ⊕ β) E₁) : Matrix (β ⊕ β) (β ⊕ β) E₁)ᵀ * dbl (J.map (pr₁ s)) *
      ((x : GL (β ⊕ β) E₁) : Matrix (β ⊕ β) (β ⊕ β) E₁).map c₁ = dbl (J.map (pr₁ s)) := x.2
  show ((glLift s (x : GL (β ⊕ β) E₁) : GL (β ⊕ β) S) : Matrix (β ⊕ β) (β ⊕ β) S)ᵀ * dbl J *
      ((glLift s (x : GL (β ⊕ β) E₁) : GL (β ⊕ β) S) : Matrix (β ⊕ β) (β ⊕ β) S).map c = dbl J
  rw [glLift_coe]
  apply mat_ext s
  · rw [Matrix.map_mul, Matrix.map_mul, map_c₁ c c₁ s hc1, Matrix.transpose_map, lift_map₁, dbl_map, hx]
  · rw [Matrix.map_mul, Matrix.map_mul, map_c₂ c c₂ s hc2, Matrix.transpose_map, lift_map₂, map_one',
      Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

def uLift : UG c₁ (dbl (J.map (pr₁ s))) →* UG c (dbl J) :=
  MonoidHom.codRestrict ((glLift s).comp (UG c₁ (dbl (J.map (pr₁ s)))).subtype) (UG c (dbl J))
    (lift_mem c c₁ c₂ s hc1 hc2 J)

theorem uLift_coe (x : UG c₁ (dbl (J.map (pr₁ s)))) :
    (((uLift c c₁ c₂ s hc1 hc2 J x : UG c (dbl J)) : GL (β ⊕ β) S) : Matrix (β ⊕ β) (β ⊕ β) S) =
      lift s ((x : GL (β ⊕ β) E₁) : Matrix (β ⊕ β) (β ⊕ β) E₁) := rfl

include hc1 in
theorem pr_mem (g : UG c (dbl J)) : glPr s (g : GL (β ⊕ β) S) ∈ UG c₁ (dbl (J.map (pr₁ s))) := by
  have hg : ((g : GL (β ⊕ β) S) : Matrix (β ⊕ β) (β ⊕ β) S)ᵀ * dbl J *
      ((g : GL (β ⊕ β) S) : Matrix (β ⊕ β) (β ⊕ β) S).map c = dbl J := g.2
  show ((glPr s (g : GL (β ⊕ β) S) : GL (β ⊕ β) E₁) : Matrix (β ⊕ β) (β ⊕ β) E₁)ᵀ * dbl (J.map (pr₁ s)) *
      ((glPr s (g : GL (β ⊕ β) S) : GL (β ⊕ β) E₁) : Matrix (β ⊕ β) (β ⊕ β) E₁).map c₁ = dbl (J.map (pr₁ s))
  rw [glPr_coe]
  have h1 := congrArg (fun M => M.map (pr₁ s)) hg
  simp only [Matrix.map_mul, map_c₁ c c₁ s hc1, Matrix.transpose_map, dbl_map] at h1
  exact h1

end Unitary

theorem isUnit_det_dbl {E β : Type} [CommRing E] [Fintype β] [DecidableEq β] (J : Matrix β β E) (h : IsUnit J.det) :
    IsUnit (dbl J).det := by
  rw [show dbl J = Matrix.fromBlocks J 0 0 (-J) from rfl, Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg]
  exact h.mul ((isUnit_one.neg.pow _).mul h)

private theorem snd_lift_sub_one_apply_eq_zero {S E₁ E₂ n : Type} [CommRing S] [CommRing E₁] [CommRing E₂] [DecidableEq n]
    (s : S ≃+* E₁ × E₂) (X : Matrix n n E₁) (i j : n) : (s ((lift s X - 1) i j)).2 = 0 := by
  by_cases h : i = j
  · subst h
    simp [lift]
  · simp [lift, Matrix.one_apply_ne h]

theorem char_trivial_first : ∀ (k : Type) [Field k] [CharZero k] (R S E₁ E₂ : Type) [CommRing R] [CommRing S] [Algebra R S] [CommRing E₁] [IsArtinianRing E₁] [Algebra k E₁] [CommRing E₂] (c : S →ₐ[R] S) (c₁ : E₁ →ₐ[k] E₁) (c₂ : E₂ →+* E₂) (ξ₁ : E₁) (s : S ≃+* E₁ × E₂), IsUnit ξ₁ → c₁ ξ₁ = -ξ₁ → (∀ x, c₁ (c₁ x) = x) → (∀ x, (s (c x)).1 = c₁ (s x).1) → (∀ x, (s (c x)).2 = c₂ (s x).2) → ∀ (β : Type) [Fintype β] [DecidableEq β] (J : Matrix β β S), IsUnit J.det → ∀ lam : GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J) →* ℂˣ, (∀ (p : GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J)) (t : GL β S), (∀ i j, (s ((((p : GL (β ⊕ β) S) : Matrix (β ⊕ β) (β ⊕ β) S) - 1) i j)).2 = 0) → (∀ i j, (s (((t : Matrix β β S) - 1) i j)).2 = 0) → ((p : GL (β ⊕ β) S) : Matrix (β ⊕ β) (β ⊕ β) S) * GlobalTheory.WeilM.diagCols β = GlobalTheory.WeilM.diagCols β * (t : Matrix β β S) → lam p = 1) → ∀ g : GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J), (∀ i j, (s ((((g : GL (β ⊕ β) S) : Matrix (β ⊕ β) (β ⊕ β) S) - 1) i j)).2 = 0) → lam g = 1 := by
  intro k _ _ R S E₁ E₂ _ _ _ _ _ _ _ c c₁ c₂ ξ₁ s hξ hcξ hinv hc1 hc2 β _ _ J hdet lam hlam g hg
  haveI : Invertible (2 : k) := invertibleOfNonzero two_ne_zero
  have hdet₁ : IsUnit (J.map (pr₁ s)).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hdet.map (pr₁ s)
  have hP : ∀ (p : UG c₁ (dbl (J.map (pr₁ s)))) (t : GL β E₁),
      ((p : GL (β ⊕ β) E₁) : Matrix (β ⊕ β) (β ⊕ β) E₁) * diagCols β = diagCols β * (t : Matrix β β E₁) →
        (lam.comp (uLift c c₁ c₂ s hc1 hc2 J)) p = 1 := by
    intro p t hpt
    show lam (uLift c c₁ c₂ s hc1 hc2 J p) = 1
    refine hlam (uLift c c₁ c₂ s hc1 hc2 J p) (glLift s t) ?_ ?_ ?_
    · intro i j
      rw [uLift_coe]
      exact snd_lift_sub_one_apply_eq_zero s _ i j
    · intro i j
      rw [glLift_coe]
      exact snd_lift_sub_one_apply_eq_zero s _ i j
    · rw [uLift_coe, glLift_coe]
      exact lift_diag s _ _ hpt
  have hlam1 := GlobalTheory.CompanionTheory.Ar.RT.Siegel.char_trivial_artinian k E₁ c₁ ξ₁ (β ⊕ β) β (dbl (J.map (pr₁ s)))
    (diagCols β) hξ hcξ hinv (isUnit_det_dbl _ hdet₁) (GlobalTheory.WeilM.isLagr_diagCols c₁ (J.map (pr₁ s)))
    (lam.comp (uLift c c₁ c₂ s hc1 hc2 J)) hP
  have hG2 : ((g : GL (β ⊕ β) S) : Matrix (β ⊕ β) (β ⊕ β) S).map (pr₂ s) = 1 := by
    ext i j
    have hij := hg i j
    rw [Matrix.map_apply, pr₂_apply]
    rw [Matrix.sub_apply, map_sub, Prod.snd_sub, sub_eq_zero] at hij
    rw [hij]
    by_cases h : i = j
    · subst h
      simp
    · simp [Matrix.one_apply_ne h]
  have hg1 : uLift c c₁ c₂ s hc1 hc2 J ⟨glPr s (g : GL (β ⊕ β) S), pr_mem c c₁ s hc1 J g⟩ = g := by
    apply Subtype.ext
    apply Units.ext
    rw [uLift_coe]
    show lift s ((glPr s (g : GL (β ⊕ β) S) : GL (β ⊕ β) E₁) : Matrix (β ⊕ β) (β ⊕ β) E₁) = _
    rw [glPr_coe]
    apply mat_ext s
    · rw [lift_map₁]
    · rw [lift_map₂, hG2]
  rw [← hg1]
  exact DFunLike.congr_fun hlam1 _

end GlobalTheory.CompanionTheory.Ar.RT.CellSplit
