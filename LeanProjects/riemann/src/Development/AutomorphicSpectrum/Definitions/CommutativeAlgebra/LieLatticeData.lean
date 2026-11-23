import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.FlagMinor

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num

structure LieLatticeData (Ω F : Type) [Field Ω] (n : ℕ) (Sg : Type) (r s : Sg → ℕ) where

  M : AddSubgroup ((Fin n → F) → Ω)

  lie : ∀ τ, AddSubgroup (Fin (r τ) → Ω)

  W : ∀ τ, AddSubgroup (Fin (r τ) → Ω)

  om : ∀ τ, AddSubgroup (Fin (s τ) → Ω)

  omHT : ∀ τ, AddSubgroup (Fin (s τ) → Ω)

  Gam : ∀ τ, AddSubgroup ((Fin (r τ) → Ω) × (Fin n → Ω))

  Del : ∀ τ, AddSubgroup ((Fin n → Ω) × (Fin (s τ) → Ω))

  Th : ∀ τ, AddSubgroup (((Fin n → F) → Ω) × (Fin (r τ) → Ω))

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

def stdLat (R : Subalgebra o Ω) (ι : Type) : AddSubgroup (ι → Ω) :=
  AddSubgroup.pi Set.univ fun _ => R.toSubring.toAddSubgroup

def divLat {V : Type} [AddCommGroup V] [Module Ω V] (c : Ω) (L : AddSubgroup V) : AddSubgroup V :=
  L.comap (DistribMulAction.toAddMonoidHom V c)

def mulLat {V : Type} [AddCommGroup V] [Module Ω V] (c : Ω) (L : AddSubgroup V) : AddSubgroup V :=
  L.map (DistribMulAction.toAddMonoidHom V c)

def dotDual (R : Subalgebra o Ω) {m : ℕ} (L : AddSubgroup (Fin m → Ω)) : AddSubgroup (Fin m → Ω) :=
  ⨅ l ∈ L, R.toSubring.toAddSubgroup.comap
    (AddMonoidHom.mk' (fun v : Fin m → Ω => l ⬝ᵥ v) fun a b => dotProduct_add l a b)

def Summand {V : Type} [AddCommGroup V] [Module Ω V] (L : AddSubgroup V) (U : Submodule Ω V) : Prop :=
  ∃ ρ : V →ₗ[Ω] V, (∀ v, ρ v ∈ U) ∧ (∀ u ∈ U, ρ u = u) ∧ ∀ v ∈ L, ρ v ∈ L

def powSpan (R : Subalgebra o Ω) (p : ℕ) (X : AddSubgroup Ω) : AddSubgroup Ω :=
  spanOver R ((fun c => c ^ p) '' (X : Set Ω))

variable {F : Type} [Zero F] {n : ℕ}

def linMap (n : ℕ) (χ : F → Ω) : (Fin n → Ω) →ₗ[Ω] ((Fin n → F) → Ω) :=
  Fintype.linearCombination Ω fun (i : Fin n) (x : Fin n → F) => χ (x i)

def vanSub (Ω F : Type) [Field Ω] [Zero F] (n i : ℕ) : Submodule Ω ((Fin n → F) → Ω) :=
  Submodule.pi {x | ∀ j : Fin n, i ≤ (j : ℕ) → x j = 0} fun _ => ⊥

def charSub (χ : F → Ω) (i : Fin n) : Submodule Ω ((Fin n → F) → Ω) :=
  vanSub Ω F n ((i : ℕ) + 1) ⊔ Submodule.span Ω {fun x => χ (x i)}

def annSub (Ω : Type) [Field Ω] (n i : ℕ) : Submodule Ω (Fin n → Ω) :=
  Submodule.pi {j | (j : ℕ) < i} fun _ => ⊥

def bcMap (Ω C : Type) [Field Ω] [Field C] [Algebra Ω C] (ι : Type) : (ι → Ω) →ₗ[Ω] (ι → C) :=
  (Algebra.linearMap Ω C).compLeft ι

namespace LieLatticeData

variable {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ)

def bc {C : Type} [Field C] [Algebra o C] [Algebra Ω C] (RC : Subalgebra o C) : LieLatticeData C F n Sg r s where
  M := spanOver RC (bcMap Ω C _ '' D.M)
  lie τ := spanOver RC (bcMap Ω C _ '' D.lie τ)
  W τ := spanOver RC (bcMap Ω C _ '' D.W τ)
  om τ := spanOver RC (bcMap Ω C _ '' D.om τ)
  omHT τ := spanOver RC (bcMap Ω C _ '' D.omHT τ)
  Gam τ := spanOver RC (Prod.map (bcMap Ω C _) (bcMap Ω C _) '' D.Gam τ)
  Del τ := spanOver RC (Prod.map (bcMap Ω C _) (bcMap Ω C _) '' D.Del τ)
  Th τ := spanOver RC (Prod.map (bcMap Ω C _) (bcMap Ω C _) '' D.Th τ)

def l1 : AddSubgroup ((Fin n → F) → Ω) := D.M ⊔ mulLat (p : Ω) (stdLat R _)

def af (χ : F → Ω) : AddSubgroup (Fin n → Ω) := (D.l1 R p).comap (linMap n χ).toAddMonoidHom

def hh (χ : F → Ω) : AddSubgroup (Fin n → Ω) := dotDual R (D.af R p χ)

def dId (χ : F → Ω) (i : Fin n) : AddSubgroup Ω :=
  (D.af R p χ ⊓ (annSub Ω n i).toAddSubgroup).map (Pi.evalAddMonoidHom (fun _ => Ω) i)

def xId (χ : F → Ω) (i : Fin n) : AddSubgroup Ω :=
  (D.M ⊔ (vanSub Ω F n ((i : ℕ) + 1)).toAddSubgroup).comap
    (LinearMap.toSpanSingleton Ω ((Fin n → F) → Ω) fun x => χ (x i)).toAddMonoidHom

def kk (τ : Sg) (i : ℕ) : AddSubgroup (Fin (r τ) → Ω) :=
  (D.Th τ ⊓ (vanSub Ω F n i).toAddSubgroup.prod ⊤).map (AddMonoidHom.snd _ _)

def stepGraph (τ : Sg) (χ : F → Ω) (i : Fin n) : AddSubgroup (Ω × (Fin (r τ) → Ω)) :=
  (D.Th τ ⊔ (vanSub Ω F n ((i : ℕ) + 1)).toAddSubgroup.prod ⊥).comap
    ((LinearMap.toSpanSingleton Ω ((Fin n → F) → Ω) fun x => χ (x i)).toAddMonoidHom.prodMap
      (AddMonoidHom.id _))

def imH (τ : Sg) (χ : F → Ω) : AddSubgroup (Fin (s τ) → Ω) :=
  (D.Del τ ⊓ (D.hh R p χ).prod ⊤).map (AddMonoidHom.snd _ _)

def kerH (τ : Sg) (χ : F → Ω) : AddSubgroup (Fin (r τ) → Ω) :=
  (D.Gam τ ⊓ (⊤ : AddSubgroup _).prod (D.hh R p χ)).map (AddMonoidHom.fst _ _)

variable [Fintype F] (w : Ω) (χ : Sg → F → Ω) (φ : Equiv.Perm Sg)

structure Base : Prop where
  freeM : LocFree R (Fintype.card F ^ n) D.M
  M_le : D.M ≤ stdLat R _
  le_M : ∃ m : ℕ, mulLat ((p : Ω) ^ m) (stdLat R _) ≤ D.M
  one_mem : (1 : (Fin n → F) → Ω) ∈ D.M
  free : ∀ τ, LocFree R (r τ) (D.lie τ) ∧ LocFree R (r τ) (D.W τ) ∧ LocFree R (s τ) (D.om τ) ∧
    LocFree R (s τ) (D.omHT τ)
  incl : ∀ τ, D.lie τ ≤ D.W τ ∧ D.W τ ≤ divLat w (D.lie τ) ∧ D.omHT τ ≤ D.om τ ∧
    D.om τ ≤ divLat w (D.omHT τ)
  stable : ∀ τ, ∀ a ∈ R, (∀ v ∈ D.Gam τ, a • v ∈ D.Gam τ) ∧ (∀ v ∈ D.Del τ, a • v ∈ D.Del τ) ∧
    ∀ v ∈ D.Th τ, a • v ∈ D.Th τ
  gam : ∀ τ, (∀ a, (∃ b, (a, b) ∈ D.Gam τ) ↔ w • a ∈ D.W τ) ∧ (∀ b, (0, b) ∈ D.Gam τ ↔ b ∈ stdLat R _) ∧
    ∀ a, (a, 0) ∈ D.Gam τ ↔ a ∈ D.W τ
  del : ∀ τ, (∀ b, (∃ c, (b, c) ∈ D.Del τ) ↔ w • b ∈ stdLat R _) ∧
    (∀ c, (∃ b, (b, c) ∈ D.Del τ) ↔ w • c ∈ D.omHT τ) ∧ (∀ c, (0, c) ∈ D.Del τ ↔ c ∈ D.omHT τ) ∧
    ∀ b, (b, 0) ∈ D.Del τ ↔ ∃ a, (a, b) ∈ D.Gam τ
  th : ∀ τ, (∀ g, (∃ m, (g, m) ∈ D.Th τ) ↔ g ∈ D.M ∧ g 0 = 0) ∧
    (∀ m, (∃ g, (g, m) ∈ D.Th τ) ↔ m ∈ dotDual R (D.lie τ)) ∧
    ∀ m, (0, m) ∈ D.Th τ ↔ m ∈ mulLat (p : Ω) (dotDual R (D.lie τ))

structure Good₁ : Prop where
  l1 : LocFree R (Fintype.card F ^ n) (D.l1 R p)
  lin : ∀ τ, Summand (D.l1 R p) (LinearMap.range (linMap n (χ τ)))
  van : ∀ i, Summand D.M (vanSub Ω F n i)
  char : ∀ τ i, Summand D.M (charSub (χ τ) i)

structure Good₂ : Prop where
  ann : ∀ τ i, Summand (D.af R p (χ τ)) (annSub Ω n i)
  kk : ∀ τ i, LocFree R (r τ) (D.kk τ i)
  step : ∀ τ i, LocFree R (r τ) ((D.stepGraph τ (χ τ) i).map (AddMonoidHom.snd _ _))
  im : ∀ τ, LocFree R (s τ) (D.imH R p τ (χ τ))

structure Facts : Prop where
  le_af : ∀ τ, mulLat w (stdLat R _) ≤ D.af R p (χ τ)
  im : ∀ τ, D.imH R p τ (χ τ) = D.om τ
  ker : ∀ τ, D.kerH R p τ (χ τ) = divLat w (D.lie τ)
  dx : ∀ τ i, D.dId R p (χ τ) i = D.xId (χ τ) i
  onto : ∀ τ (i : Fin n), (D.stepGraph τ (χ τ) i).map (AddMonoidHom.snd _ _) = D.kk τ i
  inj : ∀ τ i, (D.stepGraph (φ τ) (χ (φ τ)) i).comap (AddMonoidHom.inl _ _) =
    powSpan R p (D.xId (χ τ) i)

end LieLatticeData

def IsTestPt (p : ℕ) (R : Subalgebra o Ω) {C : Type} [Field C] [Algebra o C] [Algebra Ω C]
    (RC : Subalgebra o C) : Prop :=
  IsAlgClosed C ∧ (∃ v : Valuation C NNReal, (∀ c, c ∈ RC ↔ v c ≤ 1) ∧ v (p : C) < 1) ∧
    IsAdicComplete (Ideal.span {(p : RC)}) RC ∧ ∀ a ∈ R, algebraMap Ω C a ∈ RC

def LieLatticeData.TestFacts {Sg : Type} {r s : Sg → ℕ} [Fintype F] (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω)
    (p : ℕ) (w : Ω) (χ : Sg → F → Ω) (φ : Equiv.Perm Sg) : Prop :=
  ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C),
    IsTestPt p R RC →
      (D.bc RC).Facts RC p (algebraMap Ω C w) (fun τ a => algebraMap Ω C (χ τ a)) φ

def CharData [One F] {Sg : Type} (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω) : Prop :=
  (p : Ω) ≠ 0 ∧ w ∈ R ∧ (∃ c ∈ R, (p : Ω) = c * w) ∧ (0 : F) ≠ 1 ∧
    ∀ τ, χ τ 0 = 0 ∧ χ τ 1 = 1 ∧ ∀ a, χ τ a ∈ R

end GlobalTheory.CompanionTheory.Ar.Num
