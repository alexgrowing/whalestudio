import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective

noncomputable section

open Polynomial TensorProduct UpperTheory.V.Alg

namespace UpperTheory.V.J

section Mu

variable {O Λ B K : Type} [CommRing O] [CommRing Λ] [CommRing B] [Field K] [Algebra O Λ] [Algebra O B] [Algebra O K]
  (lam : Λ →ₐ[O] B) (M : Type) [AddCommGroup M] [Module B M] [Module Λ M] (hs : ∀ (a : Λ) (m : M), a • m = lam a • m)

def actL (a : B) : Module.End Λ M where
  toFun m := a • m
  map_add' := smul_add a
  map_smul' c m := by simp only [RingHom.id_apply, hs, smul_smul, mul_comm]

def mu (x : B →ₐ[O] K) : ℕ :=
  letI : Algebra Λ K := (x.comp lam).toRingHom.toAlgebra
  Module.finrank K ↥(⨅ a : B, Module.End.maxGenEigenspace ((actL lam M hs a).baseChange K) (x a))

end Mu

structure Dat {O Λ B : Type} [CommRing O] [CommRing Λ] [CommRing B] [Algebra O Λ] [Algebra O B] (lam : Λ →ₐ[O] B)
    (J : Ideal B) (M : Type) [AddCommGroup M] [Module B M] [Module Λ M] : Prop where
  hs : ∀ (a : Λ) (m : M), a • m = lam a • m
  free : Module.Free Λ M
  fin : Module.Finite Λ M
  rad : J.IsRadical
  supp : ∀ p : Ideal B, p.IsPrime → (Module.annihilator B M ≤ p ↔ J ≤ p)
  tf : ∀ c : Λ, c ≠ 0 → ∀ a : B, lam c * a ∈ J → a ∈ J

def Prim {O Λ B : Type} [CommRing O] [CommRing Λ] [CommRing B] [Algebra O Λ] [Algebra O B] (lam : Λ →ₐ[O] B) (J : Ideal B)
    (t : B) : Prop := ∀ a : B, ∃ c : Λ, c ≠ 0 ∧ ∃ P : Λ[X], lam c * a - P.eval₂ (lam : Λ →+* B) t ∈ J

def Sep {O Λ B K : Type} [CommRing O] [CommRing Λ] [CommRing B] [Field K] [Algebra O Λ] [Algebra O B] [Algebra O K]
    (lam : Λ →ₐ[O] B) (J : Ideal B) (x : B →ₐ[O] K) (t : B) : Prop :=
  ∀ x' : B →ₐ[O] K, J ≤ RingHom.ker x' → x'.comp lam = x.comp lam → x' t = x t → x' = x

structure Fact' {Λ : Type} [CommRing Λ] [IsDomain Λ] (χ : Λ[X]) {s : ℕ} (g : Fin s → Λ[X]) (m : Fin s → ℕ) : Prop where
  monic : ∀ i, (g i).Monic
  irr : ∀ i, Irreducible ((g i).map (algebraMap Λ (FractionRing Λ)))
  inj : Function.Injective g
  pos : ∀ i, 1 ≤ m i
  prod : χ = ∏ i, g i ^ m i

def cmp {O Λ B : Type} [CommRing O] [CommRing Λ] [CommRing B] [Algebra O Λ] [Algebra O B] (lam : Λ →ₐ[O] B) (J : Ideal B)
    (t : B) {s : ℕ} (g : Fin s → Λ[X]) (i : Fin s) : Ideal B :=
  J.colon {(∏ j ∈ Finset.univ.erase i, g j).eval₂ (lam : Λ →+* B) t}

def PrimEx : Prop :=
  ∀ (O Λ B K : Type) [CommRing O] [CommRing Λ] [IsDomain Λ] [IsNoetherianRing Λ] [CharZero Λ] [CommRing B] [Field K] [CharZero K]
    [Algebra O Λ] [Algebra O B] [Algebra O K] (lam : Λ →ₐ[O] B) (J : Ideal B) (M : Type) [AddCommGroup M] [Module B M] [Module Λ M],
    Dat lam J M → ∀ x : B →ₐ[O] K, J ≤ RingHom.ker x → ∃ t, Prim lam J t ∧ Sep lam J x t

def MuLe : Prop :=
  ∀ (O Λ B K : Type) [CommRing O] [CommRing Λ] [Nontrivial Λ] [CommRing B] [Field K] [Algebra O Λ] [Algebra O B] [Algebra O K]
    (lam : Λ →ₐ[O] B) (M : Type) [AddCommGroup M] [Module B M] [Module Λ M] [Module.Free Λ M] [Module.Finite Λ M]
    (hs : ∀ (a : Λ) (m : M), a • m = lam a • m) (y : B →ₐ[O] K) (t : B),
    mu lam M hs y ≤ rootMultiplicity (y t) ((actL lam M hs t).charpoly.map (y.comp lam : Λ →+* K))

def MuGe : Prop :=
  ∀ (O Λ B K : Type) [CommRing O] [CommRing Λ] [Nontrivial Λ] [CommRing B] [Field K] [IsAlgClosed K] [Algebra O Λ] [Algebra O B]
    [Algebra O K] (lam : Λ →ₐ[O] B) (J : Ideal B) (M : Type) [AddCommGroup M] [Module B M] [Module Λ M] [Module.Free Λ M]
    [Module.Finite Λ M] (h : Dat lam J M) (x : B →ₐ[O] K) (t : B), Sep lam J x t →
    rootMultiplicity (x t) ((actL lam M h.hs t).charpoly.map (x.comp lam : Λ →+* K)) ≤ mu lam M h.hs x

def FactEx : Prop :=
  ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsIntegrallyClosed Λ] (χ : Λ[X]), χ.Monic →
    ∃ (s : ℕ) (g : Fin s → Λ[X]) (m : Fin s → ℕ), Fact' χ g m

def MinPol : Prop :=
  ∀ (O Λ B : Type) [CommRing O] [CommRing Λ] [IsDomain Λ] [CommRing B] [Algebra O Λ] [Algebra O B] (lam : Λ →ₐ[O] B)
    (J : Ideal B) (M : Type) [AddCommGroup M] [Module B M] [Module Λ M] [Module.Free Λ M] [Module.Finite Λ M] (h : Dat lam J M)
    (t : B) (s : ℕ) (g : Fin s → Λ[X]) (m : Fin s → ℕ), Fact' (actL lam M h.hs t).charpoly g m →
    (∏ i, g i).eval₂ (lam : Λ →+* B) t ∈ J ∧ ∀ q : Λ[X], q.eval₂ (lam : Λ →+* B) t ∈ J → ∀ i, g i ∣ q

def IntMod : Prop :=
  ∀ (O Λ B : Type) [CommRing O] [CommRing Λ] [Nontrivial Λ] [CommRing B] [Algebra O Λ] [Algebra O B] (lam : Λ →ₐ[O] B)
    (J : Ideal B) (M : Type) [AddCommGroup M] [Module B M] [Module Λ M], Dat lam J M →
    ∀ a : B, ∃ q : Λ[X], q.Monic ∧ q.eval₂ (lam : Λ →+* B) a ∈ J

structure Cmp {O Λ B : Type} [CommRing O] [CommRing Λ] [IsDomain Λ] [CommRing B] [Algebra O Λ] [Algebra O B]
    (lam : Λ →ₐ[O] B) (J : Ideal B) (t : B) {s : ℕ} (g : Fin s → Λ[X]) : Prop where
  tf : ∀ c : Λ, c ≠ 0 → ∀ a : B, lam c * a ∈ J → a ∈ J
  int : ∀ a : B, ∃ q : Λ[X], q.Monic ∧ q.eval₂ (lam : Λ →+* B) a ∈ J
  prim : Prim lam J t
  monic : ∀ i, (g i).Monic
  irr : ∀ i, Irreducible ((g i).map (algebraMap Λ (FractionRing Λ)))
  inj : Function.Injective g
  kill : (∏ i, g i).eval₂ (lam : Λ →+* B) t ∈ J
  min : ∀ q : Λ[X], q.eval₂ (lam : Λ →+* B) t ∈ J → ∀ i, g i ∣ q

def CmpPrime : Prop :=
  ∀ (O Λ B : Type) [CommRing O] [CommRing Λ] [IsDomain Λ] [CommRing B] [Algebra O Λ] [Algebra O B] (lam : Λ →ₐ[O] B)
    (J : Ideal B) (t : B) (s : ℕ) (g : Fin s → Λ[X]), Cmp lam J t g → ∀ i, (cmp lam J t g i).IsPrime ∧
    (∀ q : Λ[X], q.eval₂ (lam : Λ →+* B) t ∈ cmp lam J t g i ↔ g i ∣ q) ∧
    ∀ c : Λ, c ≠ 0 → lam c ∉ cmp lam J t g i

def LyOver : Prop :=
  ∀ (O Λ B K : Type) [CommRing O] [CommRing Λ] [IsDomain Λ] [CommRing B] [Field K] [IsAlgClosed K] [Algebra O Λ] [Algebra O B]
    [Algebra O K] (lam : Λ →ₐ[O] B) (J : Ideal B) (t : B) (s : ℕ) (g : Fin s → Λ[X]), Cmp lam J t g →
    ∀ (p : Λ →ₐ[O] K) (z : K) (i : Fin s), (g i).eval₂ (p : Λ →+* K) z = 0 →
      ∃ x' : B →ₐ[O] K, cmp lam J t g i ≤ RingHom.ker x' ∧ x'.comp lam = p ∧ x' t = z

def Cond : Prop :=
  ∀ (O Λ B : Type) [CommRing O] [CommRing Λ] [IsDomain Λ] [IsIntegrallyClosed Λ] [CharZero Λ] [CommRing B] [Algebra O Λ]
    [Algebra O B] (lam : Λ →ₐ[O] B) (J : Ideal B) (t : B) (s : ℕ) (g : Fin s → Λ[X]), Cmp lam J t g → ∀ i (a : B),
    ∃ P : Λ[X], (derivative (g i)).eval₂ (lam : Λ →+* B) t * a - P.eval₂ (lam : Λ →+* B) t ∈ cmp lam J t g i

def DerZero : Prop :=
  ∀ (O Λ B K : Type) [CommRing O] [CommRing Λ] [IsDomain Λ] [IsIntegrallyClosed Λ] [CharZero Λ] [CommRing B] [Field K]
    [Algebra O Λ] [Algebra O B] [Algebra O K] (lam : Λ →ₐ[O] B) (J : Ideal B) (t : B) (s : ℕ) (g : Fin s → Λ[X]),
    Cmp lam J t g → ∀ (x : B →ₐ[O] K) (i : Fin s), cmp lam J t g i ≤ RingHom.ker x →
    rootMultiplicity (x t) ((∏ j, g j).map (x.comp lam : Λ →+* K)) = 1 →
    ∀ δ ∈ PtDer x K, (∀ a ∈ J, δ a = 0) → (∀ c, δ (lam c) = 0) → δ = 0

def UnrAlg : Prop :=
  ∀ (O Λ B K : Type) [CommRing O] [CommRing Λ] [IsDomain Λ] [IsNoetherianRing Λ] [IsIntegrallyClosed Λ] [CharZero Λ] [CommRing B]
    [Field K] [CharZero K] [IsAlgClosed K] [Algebra O Λ] [Algebra O B] [Algebra O K] (lam : Λ →ₐ[O] B) (J : Ideal B) (M : Type)
    [AddCommGroup M] [Module B M] [Module Λ M] (h : Dat lam J M) (x : B →ₐ[O] K), J ≤ RingHom.ker x →
    ∀ (𝒢 : Set (B →ₐ[O] K)) (b₀ : B), x b₀ ≠ 0 → (∀ a : B, (∀ y ∈ 𝒢, y a = 0) → a ∈ J) →
    (∀ y ∈ 𝒢, J ≤ RingHom.ker y ∧ (y b₀ ≠ 0 → mu lam M h.hs x ≤ mu lam M h.hs y)) →
    ∀ δ ∈ PtDer x K, (∀ a ∈ J, δ a = 0) → (∀ c, δ (lam c) = 0) → δ = 0

end UpperTheory.V.J

end
