import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.BaseRepGL3NormalisedOfPsiEqOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective

noncomputable section

namespace UpperTheory.V.U3

open Matrix IsLocalRing UpperTheory.V.Alg

section Emb

variable {m : ℕ} {R : Type*} [CommRing R]

def emb : GG m R →* Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) R where
  toFun x := if x.right = 1 then Matrix.fromBlocks x.mat 0 0 (theta x.left : GL (Fin m) R)
    else Matrix.fromBlocks 0 x.mat (theta x.left : GL (Fin m) R) 0
  map_one' := by
    have h : theta (1 : GL (Fin m) R) = 1 := map_one (thetaAut m R)
    simp [GG.mat, h]
  map_mul' x y := by
    have h : ((-1 : ℤˣ) = 1) = False := by decide
    obtain ⟨a, s⟩ := x
    obtain ⟨b, t⟩ := y
    rcases Int.units_eq_one_or s with rfl | rfl <;> rcases Int.units_eq_one_or t with rfl | rfl <;>
      simp [GG.mat, h, theta_mul, theta_theta, Matrix.fromBlocks_multiply]

def wt6 : Fin 3 ⊕ Fin 3 → ℤ := Sum.elim wt1 wt1

end Emb

section Lift

variable (O : Type) [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ]

def barChar (Ψ : Γ →* Oˣ) : Γ →* (ResidueField O)ˣ := (Units.map (residue O).toMonoidHom).comp Ψ

variable (η : Γ →* ℤˣ) (Ψ : Γ →* Oˣ)

def rbar : Γ →* GG 3 (ResidueField O) := r0 η (barChar O Ψ)

@[ext] structure GLift (R : Type) [CommRing R] [Algebra O R] [IsCO O R] where
  hom : Γ →* GG 3 R
  cont : ∀ a b, AdicCont (maximalIdeal R) fun g => (hom g).mat a b
  red : ∀ g, GG.map (res O R : R →+* ResidueField O) (hom g) = rbar O η Ψ g

variable {O η Ψ} {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing R'] [Algebra O R'] [IsCO O R']

theorem GLift.hasMult (r : GLift O η Ψ R) : HasMult η r.hom := fun g => congrArg SemidirectProduct.right (r.red g)

theorem GG.map_map {m : ℕ} {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (f' : B →+* C)
    (x : GG m A) : GG.map f' (GG.map f x) = GG.map (f'.comp f) x := rfl

def GLift.map (f : R →ₐ[O] R') (r : GLift O η Ψ R) : GLift O η Ψ R' where
  hom := (GG.map (f : R →+* R')).comp r.hom
  cont a b N := by
    have hle : maximalIdeal R ^ N ≤ (maximalIdeal R' ^ N).comap (f : R →+* R') := by
      refine le_trans (Ideal.pow_right_mono (fun y hy => ?_) N) (Ideal.le_comap_pow _ N)
      show f y ∈ maximalIdeal R'
      rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
      exact hy
    exact (r.cont a b N).comp (Ideal.quotientMap _ (f : R →+* R') hle)
  red g := by
    have e : (res O R' : R' →+* ResidueField O).comp (f : R →+* R') = (res O R : R →+* ResidueField O) :=
      RingHom.ext fun x => res_map f x
    rw [MonoidHom.comp_apply, GG.map_map, e, r.red]

def GLift.comap {H : Type} [Group H] [TopologicalSpace H] (φ : H →* Γ) (hφ : Continuous φ) (r : GLift O η Ψ R) :
    GLift O (η.comp φ) (Ψ.comp φ) R where
  hom := r.hom.comp φ
  cont a b N := (r.cont a b N).comp_continuous hφ
  red g := r.red (φ g)

variable (O η Ψ) in

def GCond : Type 1 := ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R], GLift O η Ψ R → Prop

variable (O η Ψ) in

def GCond.noCondition : GCond O η Ψ := fun _ _ _ _ _ => True

def GRepresents (P : GCond O η Ψ) (r : GLift O η Ψ R) : Prop :=
  ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'],
    (∀ f : R →ₐ[O] R', P R' (r.map f)) ∧ ∀ r' : GLift O η Ψ R', P R' r' → ∃! f : R →ₐ[O] R', r.map f = r'

structure Univ (P : GCond O η Ψ) : Type 1 where
  R : Type
  [cr : CommRing R]
  [al : Algebra O R]
  [co : IsCO O R]
  r : GLift O η Ψ R
  rep : GRepresents P r

attribute [instance] Univ.cr Univ.al Univ.co

def OnI (U : Univ (GCond.noCondition O η Ψ)) (I : Ideal U.R) : GCond O η Ψ :=
  fun R _ _ _ r => ∃ f : U.R →ₐ[O] R, U.r.map f = r ∧ I ≤ RingHom.ker f

def Kills (N : Set Γ) : GCond O η Ψ := fun _ _ _ _ r => ∀ g ∈ N, r.hom g = 1

def BoxCond (N : Set Γ) {H : Type} [Group H] [TopologicalSpace H] (ι : H →* Γ) (hι : Continuous ι)
    (U : Univ (GCond.noCondition O (η.comp ι) (Ψ.comp ι))) (I : Ideal U.R) : GCond O η Ψ :=
  fun R _ _ _ r => Kills N R r ∧ OnI U I R (r.comap ι hι)

def NormCond (c g₁ : Γ) (P : GCond O η Ψ) : GCond O η Ψ :=
  fun R _ _ _ r => Normalised c g₁ r.hom ∧ P R r

end Lift

section Points

variable (O : Type) [CommRing O] {Γ R : Type} [Group Γ] [CommRing R] [Algebra O R]

def entAlg (r : Γ →* GG 3 R) : Subalgebra O R := Algebra.adjoin O {x | ∃ g a b, x = (r g).mat a b}

def entMon (r : Γ →* GG 3 R) (j : ℤ) : Set R :=
  {x | ∃ L : List (Γ × Fin 3 × Fin 3), (L.map fun s => wt s.2.1 s.2.2).sum = j ∧
    x = (L.map fun s => (r s.1).mat s.2.1 s.2.2).prod}

def weightZeroSubalgebra (r : Γ →* GG 3 R) : Subalgebra O R := Algebra.adjoin O (entMon r 0)

variable {O} {κ : Type} [CommRing κ] [Algebra O κ]

def push (f : R →ₐ[O] κ) (r : Γ →* GG 3 R) : Γ →* GG 3 κ := (GG.map (f : R →+* κ)).comp r

def IsPush {A : Subalgebra O R} (ξ : A →ₐ[O] κ) (r : Γ →* GG 3 R) (r' : Γ →* GG 3 κ) : Prop :=
  ∀ g, (r' g).right = (r g).right ∧ ∀ a b, ∃ h : (r g).mat a b ∈ A, (r' g).mat a b = ξ ⟨_, h⟩

def tanCoc (F : R →ₐ[O] DualNumber κ) (r : Γ →* GG 3 R) (g : Γ) : Matrix (Fin 3) (Fin 3) κ :=
  ((r g).mat.map fun x => (F x).snd) *
    (((r g).left⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R).map fun x => (F x).fst

def dualFst (F : R →ₐ[O] DualNumber κ) : R →ₐ[O] κ := (TrivSqZeroExt.fstHom O κ κ).comp F

def Rigid (r : Γ →* GG 3 R) (f : R →ₐ[O] κ) : Prop :=
  ∀ F : R →ₐ[O] DualNumber κ, dualFst F = f → ∃ X, tanCoc F r = cob (push f r) X

def RigidWt (j : ℤ) (r : Γ →* GG 3 R) (f : R →ₐ[O] κ) : Prop :=
  ∀ F : R →ₐ[O] DualNumber κ, dualFst F = f → (∀ g, tanCoc F r g ∈ gw κ j) → ∃ X, tanCoc F r = cob (push f r) X

def IsLocPt [IsLocalRing R] {κ : Type} [NormedField κ] [Algebra O κ] (f : R →ₐ[O] κ) : Prop :=
  ∀ x ∈ maximalIdeal R, ‖f x‖ < 1

end Points

section Base

variable (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O]
  {Γ : Type} [Group Γ] [TopologicalSpace Γ] (η : Γ →* ℤˣ) (Ψ : Γ →* Oˣ)

def baseLift (hΨ : ∀ j : ℤ, AdicCont (maximalIdeal O) fun g => ((Ψ g ^ j : Oˣ) : O)) : GLift O η Ψ O where
  hom := r0 η Ψ
  cont a b := by
    by_cases h : a = b
    · subst h
      simpa [GG.mat, tor_val] using hΨ (wt1 a)
    · intro N
      simp only [GG.mat, unitaryThreeReflection_left, tor_val, Matrix.diagonal_apply_ne _ h]
      exact IsLocallyConstant.const _
  red g := by
    have e : ∀ x : O, res O O x = residue O x := fun x => (res O O).commutes x
    refine SemidirectProduct.ext (Units.ext ?_) rfl
    show (tor O (Ψ g) : Matrix (Fin 3) (Fin 3) O).map (res O O) = tor _ (barChar O Ψ g)
    rw [tor_val, tor_val, Matrix.diagonal_map (map_zero _)]
    congr 1
    funext i
    rw [e]
    exact congrArg Units.val (map_zpow (Units.map (residue O).toMonoidHom) (Ψ g) (wt1 i))

end Base

end UpperTheory.V.U3
