import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AltPullApply

noncomputable section

namespace GlobalTheory.KS

open CategoryTheory

variable {Γ : Type} [Group Γ] {L : Type} [AddCommGroup L]

def autOf (σ : Representation ℤ Γ L) : Γ →* MulAut (Multiplicative L) where
  toFun γ :=
    { toFun := fun x => Multiplicative.ofAdd (σ γ x.toAdd)
      invFun := fun x => Multiplicative.ofAdd (σ γ⁻¹ x.toAdd)
      left_inv := fun x => by simp [← Module.End.mul_apply, ← map_mul]
      right_inv := fun x => by simp [← Module.End.mul_apply, ← map_mul]
      map_mul' := fun x y => by simp }
  map_one' := by ext x; simp
  map_mul' γ δ := by ext x; simp

abbrev SD (σ : Representation ℤ Γ L) : Type := Multiplicative L ⋊[autOf σ] Γ

variable {Γ' : Type} [Group Γ'] {L' : Type} [AddCommGroup L']

def sdMap {σ' : Representation ℤ Γ' L'} {σ : Representation ℤ Γ L} (α : Γ' →* Γ) (u : L' →ₗ[ℤ] L)
    (h : ∀ γ x, u (σ' γ x) = σ (α γ) (u x)) : SD σ' →* SD σ :=
  SemidirectProduct.map (AddMonoidHom.toMultiplicative u.toAddMonoidHom) α fun γ => by
    ext x
    simp [autOf, h]

variable (E : Type) [Field E]

abbrev altRepZ (σ : Representation ℤ Γ L) (q : ℕ) : Representation E Γ (Alt ℤ L E q) := altRep E σ q

def altHom {σ' : Representation ℤ Γ' L'} {σ : Representation ℤ Γ L} (α : Γ' →* Γ) (u : L' →ₗ[ℤ] L)
    (h : ∀ γ x, u (σ' γ x) = σ (α γ) (u x)) (q : ℕ) :
    Rep.res α (Rep.of (altRepZ E σ q)) ⟶ Rep.of (altRepZ E σ' q) :=
  Rep.ofHom
    { toLinearMap := altPull E u q
      isIntertwining' := fun γ => by
        ext f x
        change f (fun i => σ (α γ)⁻¹ (u (x i))) = f (fun i => u (σ' γ⁻¹ (x i)))
        simp only [h, map_inv] }

abbrev HAlt (σ : Representation ℤ Γ L) (q p : ℕ) : Type := groupCohomology (Rep.of (altRepZ E σ q)) p

abbrev HTriv (G : Type) [Group G] (n : ℕ) : Type := groupCohomology (Rep.trivial E G E) n

abbrev SH (X : Type) [TopologicalSpace X] (n : ℕ) : Type :=
  Module.Dual E (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} E) n).obj (ModuleCat.of E E)).obj (TopCat.of X))

def shMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (n : ℕ) : SH E Y n →ₗ[E] SH E X n :=
  Module.Dual.transpose (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} E) n).obj (ModuleCat.of E E)).map
    (TopCat.ofHom f)).hom

structure Asph (Y : Type) [TopologicalSpace Y] where
  n : ℕ
  G : Fin n → Type
  [grp : ∀ i, Group (G i)]
  X : Fin n → Type
  [top : ∀ i, TopologicalSpace (X i)]
  [act : ∀ i, MulAction (G i) (X i)]
  contr : ∀ i, ContractibleSpace (X i)
  π : ∀ i, C(X i, Y)
  isOpen : ∀ i, IsOpen (Set.range (π i))
  cov : ∀ i, IsQuotientCoveringMap (Set.rangeFactorization (π i)) (G i)
  disj : Pairwise fun i j => Disjoint (Set.range (π i)) (Set.range (π j))
  cover : ∀ y, ∃ i, y ∈ Set.range (π i)

attribute [instance] Asph.grp Asph.top Asph.act

structure Asph.Lift {Y Y' : Type} [TopologicalSpace Y] [TopologicalSpace Y'] (K' : Asph Y') (K : Asph Y) (f : C(Y', Y)) where
  κ : Fin K'.n → Fin K.n
  α : ∀ i, K'.G i →* K.G (κ i)
  lift : ∀ i, C(K'.X i, K.X (κ i))
  equiv : ∀ i (g : K'.G i) x, lift i (g • x) = α i g • lift i x
  comm : ∀ i x, K.π (κ i) (lift i x) = f (K'.π i x)

def Asph.point : Asph Unit where
  n := 1
  G _ := Unit
  X _ := Unit
  contr _ := inferInstance
  π _ := ContinuousMap.const _ ()
  isOpen _ := isOpen_discrete _
  cov _ :=
    { toIsQuotientMap := by
        refine ⟨⟨Subsingleton.elim _ _⟩, fun y => ⟨(), Subtype.ext (Subsingleton.elim _ _)⟩⟩
      toContinuousConstSMul := ⟨fun _ => continuous_id⟩
      apply_eq_iff_mem_orbit := by
        intro a b
        simp [Subsingleton.elim a b, MulAction.mem_orbit_self]
      disjoint := fun _ => ⟨Set.univ, Filter.univ_mem, fun g _ => Subsingleton.elim _ _⟩ }
  disj i j h := absurd (Subsingleton.elim i j) h
  cover _ := ⟨0, (), rfl⟩

def circleAsph : Asph (AddCircle (1 : ℝ)) where
  n := 1
  G _ := Multiplicative (AddSubgroup.zmultiples (1 : ℝ))
  X _ := ℝ
  contr _ := inferInstance
  π _ := ⟨((↑) : ℝ → AddCircle (1 : ℝ)), continuous_quotient_mk'⟩
  isOpen _ := by
    show IsOpen (Set.range ((↑) : ℝ → AddCircle (1 : ℝ)))
    rw [Set.range_eq_univ.mpr (QuotientAddGroup.mk_surjective)]
    exact isOpen_univ
  cov _ := by
    have h := (AddCircle.isAddQuotientCoveringMap_coe (1 : ℝ)).toMultiplicative
    have hs : Set.range ((↑) : ℝ → AddCircle (1 : ℝ)) = Set.univ :=
      Set.range_eq_univ.mpr QuotientAddGroup.mk_surjective
    let φ : AddCircle (1 : ℝ) ≃ₜ Set.range ((↑) : ℝ → AddCircle (1 : ℝ)) :=
      (Homeomorph.Set.univ _).symm.trans (Homeomorph.setCongr hs.symm)
    have := h.homeomorph_comp φ
    show IsQuotientCoveringMap (Set.rangeFactorization ((↑) : ℝ → AddCircle (1 : ℝ))) _
    convert this using 1
    funext x
    rfl
  disj i j h := absurd (Subsingleton.elim i j) h
  cover y := ⟨0, QuotientAddGroup.mk_surjective y⟩

def Asph.liftId {Y : Type} [TopologicalSpace Y] (K : Asph Y) : Asph.Lift K K (ContinuousMap.id Y) where
  κ := id
  α _ := MonoidHom.id _
  lift _ := ContinuousMap.id _
  equiv _ _ _ := rfl
  comm _ _ := rfl

theorem circleAsph_G_nontrivial : Nontrivial (Multiplicative (AddSubgroup.zmultiples (1 : ℝ))) := by
  refine ⟨⟨1, Multiplicative.ofAdd ⟨1, AddSubgroup.mem_zmultiples 1⟩, ?_⟩⟩
  intro h
  have := congrArg (fun g => ((Multiplicative.toAdd g : AddSubgroup.zmultiples (1 : ℝ)) : ℝ)) h
  norm_num at this

example : Asph.Lift circleAsph circleAsph (ContinuousMap.id _) := circleAsph.liftId
example : circleAsph.n = 1 := rfl

example (σ : Representation ℤ Γ L) (a b : SD σ) :
    (a * b).left = Multiplicative.ofAdd ((a.left).toAdd + σ a.right (b.left).toAdd) := rfl

end GlobalTheory.KS
