import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.StabDirectedSystem

noncomputable section

open NumberField IsDedekindDomain UpperTheory.V.KL
open scoped Kronecker

namespace UpperTheory.V.ZK

section Chains

variable (A : Type) [CommRing A] {G H : Type} [Group G] [Group H]

abbrev Ch (A : Type) [CommRing A] (G : Type) (m : ℕ) : Type := (Fin m → G) →₀ A

def bd (G : Type) [Group G] (m : ℕ) : Ch A G (m + 1) →ₗ[A] Ch A G m :=
  Finsupp.linearCombination A fun g =>
    Finsupp.single (fun i => g i.succ) 1 +
      ∑ j : Fin (m + 1), ((-1 : A) ^ ((j : ℕ) + 1)) • Finsupp.single (Fin.contractNth j (· * ·) g) 1

def cm (f : G →* H) (m : ℕ) : Ch A G m →ₗ[A] Ch A H m := Finsupp.lmapDomain A A fun g i => f (g i)

def prism (k : G) (m : ℕ) : Ch A G m →ₗ[A] Ch A G (m + 1) :=
  Finsupp.linearCombination A fun g =>
    ∑ i : Fin (m + 1), ((-1 : A) ^ (i : ℕ)) •
      Finsupp.single (Fin.insertNth (α := fun _ => G) i k fun j => if (j : ℕ) < i then g j else k⁻¹ * g j * k) 1

variable {A}

def Cyc {m : ℕ} (z : Ch A G (m + 1)) : Prop := bd A G m z = 0

def Bd {m : ℕ} (z : Ch A G m) : Prop := z ∈ LinearMap.range (bd A G m)

end Chains

abbrev Cq (q : ℕ) : Type := Multiplicative (ZMod q)

def zc (q : ℕ) [NeZero q] (e : ℕ) : Ch (ZMod q) (Cq q) (2 * e + 1 + 1) :=
  ∑ j : Fin (e + 1) → ZMod q, Finsupp.single
    (fun i => if (i : ℕ) % 2 = 0 then Multiplicative.ofAdd (j ⟨i / 2, by omega⟩) else Multiplicative.ofAdd 1) 1

def dt (q t : ℕ) : Cq q →* Cq q × Cq q := (MonoidHom.id _).prod (powMonoidHom t)

def psi (R : Type) [CommRing R] (d n : ℕ) : GL (Fin n) R →* GL (Fin (d * n)) R :=
  Units.map
    { toFun := fun A => Matrix.reindex finProdFinEquiv finProdFinEquiv ((1 : Matrix (Fin d) (Fin d) R) ⊗ₖ A)
      map_one' := by simp
      map_mul' := fun A B => by
        simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, ← Matrix.mul_kronecker_mul, Matrix.mul_one] }

def lev (l n : ℕ) : ℕ → ℕ
  | 0 => n
  | t + 1 => l * lev l n t

def zSeq (R : Type) [CommRing R] {l : ℕ} (hl : 0 < l) {n m : ℕ} (x : grpH (GL (Fin n) R) m) :
    ∀ t : ℕ, grpH (GL (Fin (lev l n t)) R) m
  | 0 => x
  | t + 1 => (grpHMap (psi R l (lev l n t)) m).hom (zSeq R hl x t) -
      l ^ (t + 2) • (grpHMap (stab R (lev l n t) (l * lev l n t) (Nat.le_mul_of_pos_left _ hl)) m).hom (zSeq R hl x t)

section Lin

variable {k : Type} [Field k]

def red {R : Type} [CommRing R] (r : R →+* k) (n : ℕ) : GL (Fin n) R →* ((Fin n → k) ≃ₗ[k] (Fin n → k)) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv k (Fin n → k)).toMonoidHom.comp
    ((Matrix.GeneralLinearGroup.toLin (n := Fin n) (R := k)).toMonoidHom.comp (Matrix.GeneralLinearGroup.map r))

def scal (V : Type) [AddCommGroup V] [Module k V] : kˣ →* (V ≃ₗ[k] V) := DistribMulAction.toModuleAut k V

def chi (q : ℕ) [NeZero q] {M : Type} [CommGroup M] (ζ : M) (hζ : ζ ^ q = 1) (x : ℕ) : Cq q →* M where
  toFun c := ζ ^ (x * (Multiplicative.toAdd c).val)
  map_one' := by simp
  map_mul' a b := by
    rw [← pow_add, ← mul_add, toAdd_mul, ZMod.val_add, mul_comm x, mul_comm x, pow_mul, pow_mul, ← pow_eq_pow_mod _ hζ]

def cj {V W : Type} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W] (φ : V ≃ₗ[k] W) :
    (V ≃ₗ[k] V) →* (W ≃ₗ[k] W) where
  toFun g := (φ.symm.trans g).trans φ
  map_one' := by ext; simp
  map_mul' a b := by ext; simp

def sumRep {G V W : Type} [Group G] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (ρ : G →* (V ≃ₗ[k] V)) (σ : G →* (W ≃ₗ[k] W)) : G →* ((V × W) ≃ₗ[k] (V × W)) where
  toFun g := (ρ g).prodCongr (σ g)
  map_one' := by ext <;> simp
  map_mul' a b := by ext <;> simp

abbrev Fam (k : Type) [Field k] (A : Type) [CommRing A] (m : ℕ) : Type 1 :=
  ∀ (V : Type) [AddCommGroup V] [Module k V] [Finite V], Ch A (V ≃ₗ[k] V) m →ₗ[A] A

structure IsAdd {A : Type} [CommRing A] {m : ℕ} (θ : Fam k A (m + 1)) : Prop where
  bdry : ∀ (V : Type) [AddCommGroup V] [Module k V] [Finite V] (z : Ch A (V ≃ₗ[k] V) (m + 1)), Bd z → θ V z = 0
  iso : ∀ (V W : Type) [AddCommGroup V] [Module k V] [Finite V] [AddCommGroup W] [Module k W] [Finite W]
    (φ : V ≃ₗ[k] W) (z : Ch A (V ≃ₗ[k] V) (m + 1)), Cyc z → θ W (cm A (cj φ) (m + 1) z) = θ V z
  add : ∀ (G V W : Type) [Group G] [AddCommGroup V] [Module k V] [Finite V] [AddCommGroup W] [Module k W] [Finite W]
    (ρ : G →* (V ≃ₗ[k] V)) (σ : G →* (W ≃ₗ[k] W)) (z : Ch A G (m + 1)), Cyc z →
      θ (V × W) (cm A (sumRep ρ σ) (m + 1) z) = θ V (cm A ρ (m + 1) z) + θ W (cm A σ (m + 1) z)

def HasVal (q : ℕ) [NeZero q] (e : ℕ) (ζ : kˣ) (hζ : ζ ^ q = 1) (v : kˣ →* Cq q)
    (θ : Fam k (ZMod q) (2 * e + 1 + 1 + 1)) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module k V] [Finite V] (x : ℕ) (g : V ≃ₗ[k] V),
    θ V (prism (ZMod q) g _ (cm (ZMod q) ((scal V).comp (chi q ζ hζ x)) _ (zc q e))) =
      (x : ZMod q) ^ (e + 1) * Multiplicative.toAdd (v (LinearEquiv.det g))

end Lin

section Arith

variable {L F : Type} [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F]

def ordP (P : HeightOneSpectrum (𝓞 F)) (α : Fˣ) : ℤ := -WithZero.log (P.valuation F (α : F))

def actP (σ : F ≃ₐ[L] F) (P : HeightOneSpectrum (𝓞 F)) : HeightOneSpectrum (𝓞 F) :=
  HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv σ.toRingEquiv) P

def actU (σ : F ≃ₐ[L] F) : Fˣ →* Fˣ := Units.map (σ : F →* F)

structure Lay (l c ν : ℕ) (ζ : (𝓞 F)ˣ) (γ : F ≃ₐ[L] F) : Prop where
  gal : IsGalois L F
  prim : IsPrimitiveRoot ζ (l ^ ν)
  gen : ∀ σ : F ≃ₐ[L] F, σ ∈ Subgroup.zpowers γ
  act : γ ((ζ : 𝓞 F) : F) = ((ζ : 𝓞 F) : F) ^ (1 + l ^ c)
  ord : orderOf γ = l ^ (ν - c)
  c_pos : 1 ≤ c
  c_two : l = 2 → 2 ≤ c
  c_le : c ≤ ν

def DivDel (γ : F ≃ₐ[L] F) (a : ℕ) (α : Fˣ) (𝔡 : HeightOneSpectrum (𝓞 F) →₀ ℤ) : Prop :=
  ∀ P, ordP P α = 𝔡 (actP γ P) - (a : ℤ) * 𝔡 P

def nrm (γ : F ≃ₐ[L] F) (a : ℕ) (α : Fˣ) : Fˣ := ∏ j ∈ Finset.range (orderOf γ), actU (γ ^ j) α ^ a ^ j

def Res {k : Type} [Field k] (r : 𝓞 F →+* k) (α : Fˣ) (u : kˣ) : Prop :=
  ∃ a b : 𝓞 F, r b ≠ 0 ∧ (α : F) * b = a ∧ r a = u * r b

def EqHom (γ : F ≃ₐ[L] F) (a q : ℕ) : Set (HeightOneSpectrum (𝓞 F) → ZMod q) :=
  {φ | (∀ α : Fˣ, ∑ᶠ P, (ordP P α : ZMod q) * φ P = 0) ∧ ∀ P, φ (actP γ⁻¹ P) = (a : ZMod q) * φ P}

def pe (κ M e : ℕ) : ℤ := ∏ j ∈ (Finset.range M).erase e, ((κ : ℤ) ^ e - (κ : ℤ) ^ j)

end Arith

end UpperTheory.V.ZK

end
