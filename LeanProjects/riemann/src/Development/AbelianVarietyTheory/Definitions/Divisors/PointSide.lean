import Development.AbelianVarietyTheory.Definitions.Divisors.MaxWeightGL1EqOne

noncomputable section

open scoped Classical

namespace GlobalTheory.LKCount

section Vol

variable {G : Type} [Group G]

def vol (C H : Subgroup G) : ℚ := ((C.relIndex H : ℕ) : ℚ) / ((H.relIndex C : ℕ) : ℚ)

def orbC (θ : G →* G) (K C : Subgroup G) (δ : G) (f : G → ℂ) : ℂ :=
  ∑ᶠ q : DoubleCoset.Quotient (GlobalTheory.BCT.twCent θ δ : Set G) (K : Set G),
    ((vol C (GlobalTheory.BCT.twCent θ δ ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom) : ℚ) : ℂ)⁻¹ *
      f ((Quotient.out q)⁻¹ * δ * θ (Quotient.out q))

def orbK (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) : ℂ :=
  orbC θ K (GlobalTheory.BCT.twCent θ δ ⊓ K) δ f

def massC (Γ' T C : Subgroup G) : ℚ :=
  ∑ᶠ q : DoubleCoset.Quotient ((Γ'.subgroupOf T : Subgroup T) : Set T) ((C.subgroupOf T : Subgroup T) : Set T),
    ((Nat.card ((Γ'.subgroupOf T) ⊓ (C.subgroupOf T).map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup T) : ℕ) : ℚ)⁻¹

end Vol

section Count

variable {Γ G₁ G₂ : Type} [Group Γ] [Group G₁] [Group G₂]

def stab (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (x : G₁ × G₂) : Subgroup Γ :=
  (K₁.map (MulAut.conj x.1).toMonoidHom).comap ι₁ ⊓ (K₂.map (MulAut.conj x.2).toMonoidHom).comap ι₂

def pointSum (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (γ : G₁) (δ : G₂)
    (f₁ : G₁ → ℂ) (φ : G₂ → ℂ) : ℂ :=
  ∑ᶠ q : DoubleCoset.Quotient ((ι₁.prod ι₂).range : Set (G₁ × G₂)) ((K₁.prod K₂ : Subgroup (G₁ × G₂)) : Set (G₁ × G₂)),
    ((Nat.card (stab ι₁ ι₂ K₁ K₂ (Quotient.out q)) : ℕ) : ℂ)⁻¹ *
      (f₁ ((Quotient.out q).1⁻¹ * γ * (Quotient.out q).1) * φ ((Quotient.out q).2⁻¹ * δ * θ (Quotient.out q).2))

def pointSide (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (γ : G₁) (δ : G₂)
    (f₁ : G₁ → ℂ) (φ : G₂ → ℂ) : ℂ :=
  ((massC (ι₁.prod ι₂).range (GlobalTheory.BCT.twCent ((MonoidHom.id G₁).prodMap θ) (γ, δ))
      (GlobalTheory.BCT.twCent ((MonoidHom.id G₁).prodMap θ) (γ, δ) ⊓ K₁.prod K₂) : ℚ) : ℂ) *
    (orbK (MonoidHom.id G₁) K₁ γ f₁ * orbK θ K₂ δ φ)

def term (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (δ : G₂) (f₁ : G₁ → ℂ) (φ : G₂ → ℂ) (x : G₁ × G₂) (γ : Γ) : ℂ :=
  f₁ (x.1⁻¹ * ι₁ γ * x.1) * φ (x.2⁻¹ * (ι₂ γ * δ) * θ x.2)

def classSum (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (δ : G₂)
    (f₁ : G₁ → ℂ) (φ : G₂ → ℂ) : ℂ :=
  ∑ᶠ q : DoubleCoset.Quotient ((ι₁.prod ι₂).range : Set (G₁ × G₂)) ((K₁.prod K₂ : Subgroup (G₁ × G₂)) : Set (G₁ × G₂)),
    ((Nat.card (stab ι₁ ι₂ K₁ K₂ (Quotient.out q)) : ℕ) : ℂ)⁻¹ *
      ∑ᶠ γ : Γ, term ι₁ ι₂ θ δ f₁ φ (Quotient.out q) γ

def centSum (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (δ : G₂)
    (f₁ : G₁ → ℂ) (φ : G₂ → ℂ) (γ : Γ) : ℂ :=
  ∑ᶠ q : DoubleCoset.Quotient (((Subgroup.centralizer {γ}).map (ι₁.prod ι₂) : Subgroup (G₁ × G₂)) : Set (G₁ × G₂))
      ((K₁.prod K₂ : Subgroup (G₁ × G₂)) : Set (G₁ × G₂)),
    ((Nat.card (stab ι₁ ι₂ K₁ K₂ (Quotient.out q) ⊓ Subgroup.centralizer {γ} : Subgroup Γ) : ℕ) : ℂ)⁻¹ *
      term ι₁ ι₂ θ δ f₁ φ (Quotient.out q) γ

def cent (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (δ : G₂) (γ : Γ) : Subgroup (G₁ × G₂) :=
  GlobalTheory.BCT.twCent ((MonoidHom.id G₁).prodMap θ) (ι₁ γ, ι₂ γ * δ)

def classSide (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (δ : G₂)
    (f₁ : G₁ → ℂ) (φ : G₂ → ℂ) : ℂ :=
  ∑ᶠ c : ConjClasses Γ,
    ((massC ((Subgroup.centralizer {Quotient.out c}).map (ι₁.prod ι₂)) (cent ι₁ ι₂ θ δ (Quotient.out c))
        (cent ι₁ ι₂ θ δ (Quotient.out c) ⊓ K₁.prod K₂) : ℚ) : ℂ) *
      (orbK (MonoidHom.id G₁) K₁ (ι₁ (Quotient.out c)) f₁ * orbK θ K₂ (ι₂ (Quotient.out c) * δ) φ)

end Count

section Examples

example {Γ G₁ G₂ : Type} [Group Γ] [Group G₁] [Group G₂] (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (θ : G₂ →* G₂)
    (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (γ : G₁) (δ : G₂) (φ : G₂ → ℂ) :
    pointSum ι₁ ι₂ θ K₁ K₂ γ δ (fun _ => 0) φ = 0 := by
  simp [pointSum]

example {G : Type} [Group G] (C : Subgroup G) : vol C C = 1 := by
  simp [vol, Subgroup.relIndex_self]

example : pointSum (MonoidHom.id Unit) (MonoidHom.id Unit) (MonoidHom.id Unit) ⊤ ⊤ () () (fun _ => 1) (fun _ => 1) = 1 := by
  unfold pointSum
  let U : Unique (DoubleCoset.Quotient (((MonoidHom.id Unit).prod (MonoidHom.id Unit)).range : Set (Unit × Unit))
      (((⊤ : Subgroup Unit).prod (⊤ : Subgroup Unit) : Subgroup (Unit × Unit)) : Set (Unit × Unit))) :=
    { default := DoubleCoset.mk _ _ 1
      uniq := fun q => by
        rw [← DoubleCoset.out_eq' _ _ q]
        exact congrArg _ (Subsingleton.elim _ _) }
  rw [finsum_unique]
  have h : Nat.card (stab (MonoidHom.id Unit) (MonoidHom.id Unit) ⊤ ⊤ (Quotient.out (default : DoubleCoset.Quotient
      (((MonoidHom.id Unit).prod (MonoidHom.id Unit)).range : Set (Unit × Unit))
      (((⊤ : Subgroup Unit).prod (⊤ : Subgroup Unit) : Subgroup (Unit × Unit)) : Set (Unit × Unit))))) = 1 :=
    Nat.card_eq_one_iff_exists.2 ⟨1, fun x => Subsingleton.elim _ _⟩
  rw [h]
  simp

example : pointSide (MonoidHom.id Unit) (MonoidHom.id Unit) (MonoidHom.id Unit) ⊤ ⊤ () () (fun _ => 1) (fun _ => 1) = 1 := by
  have hv : ∀ C H : Subgroup Unit, vol C H = 1 := fun C H => by
    have : H = C := Subsingleton.elim _ _
    subst this; simp [vol, Subgroup.relIndex_self]
  have ho : ∀ (K : Subgroup Unit) (δ : Unit), orbK (MonoidHom.id Unit) K δ (fun _ => 1) = 1 := fun K δ => by
    unfold orbK orbC
    let U : Unique (DoubleCoset.Quotient (GlobalTheory.BCT.twCent (MonoidHom.id Unit) δ : Set Unit) (K : Set Unit)) :=
      { default := DoubleCoset.mk _ _ 1
        uniq := fun q => by
          rw [← DoubleCoset.out_eq' _ _ q] }
    rw [finsum_unique, hv]
    simp
  unfold pointSide
  rw [ho]
  unfold massC
  generalize hT : GlobalTheory.BCT.twCent ((MonoidHom.id Unit).prodMap (MonoidHom.id Unit)) ((), ()) = T
  let U : Unique (DoubleCoset.Quotient
      ((((MonoidHom.id Unit).prod (MonoidHom.id Unit)).range.subgroupOf T : Subgroup T) : Set T)
      (((T ⊓ (⊤ : Subgroup Unit).prod ⊤).subgroupOf T : Subgroup T) : Set T)) :=
    { default := DoubleCoset.mk _ _ 1
      uniq := fun q => by
        rw [← DoubleCoset.out_eq' _ _ q]
        exact congrArg _ (Subsingleton.elim _ _) }
  rw [finsum_unique]
  rw [Nat.card_eq_one_iff_exists.2 ⟨1, fun x => Subsingleton.elim _ _⟩]
  simp

end Examples

end GlobalTheory.LKCount
