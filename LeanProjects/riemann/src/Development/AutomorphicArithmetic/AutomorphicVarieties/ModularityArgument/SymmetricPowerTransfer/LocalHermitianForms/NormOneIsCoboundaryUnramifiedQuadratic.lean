import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LcountNorm

noncomputable section

namespace UpperTheory.V.Z.Sym.Loc

open QuadraticAlgebra

section

variable (O : Type) [CommRing O] {K : Type} [Field K] [Algebra O K] {Δ : K} (τ : K)

def eps (lam : Lsq K Δ) : ℂ := hs (τ ^ 2 - 4) (2 + τ + QuadraticAlgebra.trace lam) * hs Δ (2 + τ + QuadraticAlgebra.trace lam)

structure IsLat (S : Set (Etau K τ)) : Prop where
  fg : ∃ s : Finset (Etau K τ), S = Submodule.span O (s : Set (Etau K τ))
  span : Submodule.span K S = ⊤

structure IsFixP (t : K) (S : Set (Etau K τ)) : Prop where
  fg : ∃ s : Finset (Etau K τ), S = Submodule.span O (s : Set (Etau K τ))
  dual : ∀ y, y ∈ S ↔ ∀ x ∈ S, t * (x * star y).im ∈ (algebraMap O K).range
  stab : ∀ x ∈ S, ω * x ∈ S

@[reducible] def quoAct : MulAction (Etau K τ)ˣ (Set (Etau K τ)) where
  smul z S := (quo z * ·) '' S
  one_smul S := by
    change (quo 1 * ·) '' S = S
    simp [quo]
  mul_smul a b S := by
    have e : quo (a * b) = quo a * quo b := by
      simp only [quo, _root_.mul_inv_rev, Units.val_mul, star_mul]; ring
    change (quo (a * b) * ·) '' S = (quo a * ·) '' ((quo b * ·) '' S)
    rw [← Set.image_comp]
    congr 1
    funext x
    simp [e, mul_assoc]

open Classical in

def pcount (t : K) : ℂ :=
  letI := quoAct τ
  wcount (Cint O τ) fun S : Set (Etau K τ) => if IsFixP O τ t S then 1 else 0

def cls (S : Set (Etau K τ)) : Set (Set (Etau K τ)) := {S' | ∃ s : Kˣ, S' = ((s : K) • ·) '' S}

@[reducible] def mulAct : MulAction (Etau K τ)ˣ (Set (Set (Etau K τ))) where
  smul z X := (fun S => ((z : Etau K τ) * ·) '' S) '' X
  one_smul X := by
    change (fun S => (((1 : (Etau K τ)ˣ) : Etau K τ) * ·) '' S) '' X = X
    simp
  mul_smul a b X := by
    change (fun S => (((a * b : (Etau K τ)ˣ) : Etau K τ) * ·) '' S) '' X =
      (fun S => ((a : Etau K τ) * ·) '' S) '' ((fun S => ((b : Etau K τ) * ·) '' S) '' X)
    simp [← Set.image_comp, Function.comp_def, mul_assoc]

open Classical in

def vcount (x : Etau K τ) : ℂ :=
  letI := mulAct τ
  wcount (Cint O τ) fun X : Set (Set (Etau K τ)) => if ∃ S, IsLat O τ S ∧ (∀ y ∈ S, x * y ∈ S) ∧ X = cls τ S then 1 else 0

end

def DatIso : Prop :=
  ∀ (O K : Type) [CommRing O] [Field K] [Algebra O K] (Δ τ c : K) (d m : EL Δ τ) (y : (EL Δ τ)ˣ),
    lcount O c d m = lcount O c (d * sigL (y : EL Δ τ) * ((y⁻¹ : (EL Δ τ)ˣ) : EL Δ τ)) (m * (y : EL Δ τ) * star (sigL (y : EL Δ τ))) ∧
      (IsDat c d m → IsDat c (d * sigL (y : EL Δ τ) * ((y⁻¹ : (EL Δ τ)ˣ) : EL Δ τ)) (m * (y : EL Δ τ) * star (sigL (y : EL Δ τ))))

def H90 : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    τ ^ 2 - 4 ≠ 0 → ∀ β : EL Δ τ, β * sigL β = 1 → ∃ y : (EL Δ τ)ˣ, sigL (y : EL Δ τ) = β * y

def NormOneIsCoboundaryUnramifiedQuadratic : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ : K), IsLoc O Δ →
    ∀ β : Lsq K Δ, QuadraticAlgebra.norm β = 1 → ∃ y : (Lsq K Δ)ˣ, star (y : Lsq K Δ) = β * y

def DatForm : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    ∀ (c : K) (lam : Lsq K Δ), QuadraticAlgebra.norm lam = 2 + τ → ∀ z : (Etau K τ)ˣ, (z : Etau K τ) = 1 + ω → ∀ m : EL Δ τ, IsDat c (dLam lam z) m → ∃ t : Kˣ, m = (t : K) • (1 : EL Δ τ)

def SignLaw : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    τ ^ 2 - 4 ≠ 0 → ∀ (lam : Lsq K Δ) (y : (Lsq K Δ)ˣ), QuadraticAlgebra.norm lam = 2 + τ →
    2 + τ + QuadraticAlgebra.trace lam ≠ 0 → 2 + τ + QuadraticAlgebra.trace (lam * star (y : Lsq K Δ) * ((y⁻¹ : (Lsq K Δ)ˣ) : Lsq K Δ)) ≠ 0 →
    eps τ (lam * star (y : Lsq K Δ) * ((y⁻¹ : (Lsq K Δ)ˣ) : Lsq K Δ)) = hs (τ ^ 2 - 4) (QuadraticAlgebra.norm (y : Lsq K Δ)) * eps τ lam

def SumShift : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    τ ^ 2 - 4 ≠ 0 → ∀ f : Kˣ → ℂ, (∀ t ∈ NE τ, ∀ x, f (t * x) = f x) → ∀ g : Kˣ,
    (∑ᶠ t : Kˣ ⧸ NE τ, f (t.out * g)) = ∑ᶠ t : Kˣ ⧸ NE τ, f t.out ∧
    (∑ᶠ t : Kˣ ⧸ NE τ, hs (τ ^ 2 - 4) ((t.out : Kˣ) : K) * f (t.out * g)) =
      hs (τ ^ 2 - 4) (g : K) * ∑ᶠ t : Kˣ ⧸ NE τ, hs (τ ^ 2 - 4) ((t.out : Kˣ) : K) * f t.out ∧
    ∀ (e : ℂ) (x : ℂ), (∀ t : Kˣ, f t = if hs (τ ^ 2 - 4) (t : K) = e then x else 0) → (∃ t : Kˣ, hs (τ ^ 2 - 4) (t : K) = e) →
      (∑ᶠ t : Kˣ ⧸ NE τ, f t.out) = x ∧ (∑ᶠ t : Kˣ ⧸ NE τ, hs (τ ^ 2 - 4) ((t.out : Kˣ) : K) * f t.out) = e * x

def SqrtO : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ : K), IsLoc O Δ →
    ∀ x r₀ : O, IsUnit r₀ → x - r₀ ^ 2 ∈ IsLocalRing.maximalIdeal O → ∃ r : O, r ^ 2 = x ∧ r - r₀ ∈ IsLocalRing.maximalIdeal O

def NormEx : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ : K), IsLoc O Δ →
    ∀ u : Oˣ, ∃ ν : Lsq K Δ, IsInt O ν ∧ QuadraticAlgebra.norm ν = algebraMap O K u

def RootEx : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    ∀ (τ₀ : O) (e : ℤˣ), algebraMap O K τ₀ = τ → τ₀ - 2 * ((e : ℤ) : O) ∈ IsLocalRing.maximalIdeal O →
    ∃ x y : O, IsUnit y ∧ ((⟨algebraMap O K x, algebraMap O K y⟩ : Etau K τ) ^ 2 = ((e : ℤ) : Etau K τ) * ω) ∧
      QuadraticAlgebra.norm (⟨algebraMap O K x, algebraMap O K y⟩ : Etau K τ) = 1

def CaseG : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    (∃ u : Oˣ, algebraMap O K u = τ ^ 2 - 4) → ∀ c : K, EvenVal O c → ∀ lam : Lsq K Δ, IsInt O lam → QuadraticAlgebra.norm lam = 2 + τ →
    ∀ z : (Etau K τ)ˣ, (z : Etau K τ) = 1 + ω → ∀ t : Kˣ, lcount O c (dLam lam z) ((t : K) • (1 : EL Δ τ)) = if hs (τ ^ 2 - 4) (t : K) = 1 then 1 else 0

def CaseP : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    τ ^ 2 - 4 ≠ 0 → ∀ r : O, r - 2 ∈ IsLocalRing.maximalIdeal O → algebraMap O K r ^ 2 = 2 + τ → ∀ c : K, EvenVal O (c * (2 - τ)) →
    ∀ (j : Etau K τ →ₐ[K] Matrix (Fin 2) (Fin 2) K) (χ : Kˣ →* ℂˣ), (j ω).trace = τ → Unr O χ → ∀ a : (Etau K τ)ˣ, (a : Etau K τ) = ω → ∀ z : (Etau K τ)ˣ, (z : Etau K τ) = 1 + ω → ∀ t : Kˣ,
    lcount O c (dLam (algebraMap K (Lsq K Δ) (algebraMap O K r)) z) ((t : K) • (1 : EL Δ τ)) =
      if hs (τ ^ 2 - 4) (t : K) = hs (τ ^ 2 - 4) (-2 * c) then gOrb O j χ a else 0

def CaseM : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    τ ^ 2 - 4 ≠ 0 → ∀ τ₀ : O, algebraMap O K τ₀ = τ → τ₀ + 2 ∈ IsLocalRing.maximalIdeal O → ∀ c : K, EvenVal O c →
    ∀ u : Etau K τ, u ^ 2 = -ω → QuadraticAlgebra.norm u = 1 → ∀ ν : Lsq K Δ, IsInt O ν → QuadraticAlgebra.norm ν = -1 →
    ∀ (s : K) (ε : Oˣ), Δ * s ^ 2 = algebraMap O K ε → ∀ t : Kˣ,
    lcount O c (ν • ofE Δ u) (((t : K) • s • (ω : Lsq K Δ)) • ofE Δ (ω - star ω : Etau K τ)) = pcount O τ ((t : K) * (τ ^ 2 - 4))

def DatFormM : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    ∀ (c : K) (u : Etau K τ), u ^ 2 = -ω → QuadraticAlgebra.norm u = 1 → ∀ ν : Lsq K Δ, QuadraticAlgebra.norm ν = -1 → ∀ s : K, s ≠ 0 →
    (ν • ofE Δ u) * sigL (ν • ofE Δ u) = ofE Δ (ω : Etau K τ) ∧ ∀ m : EL Δ τ, IsDat c (ν • ofE Δ u) m →
      ∃ t : Kˣ, m = ((t : K) • s • (ω : Lsq K Δ)) • ofE Δ (ω - star ω : Etau K τ)

def PNorm : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    ∀ t ∈ NE τ, ∀ x : K, pcount O τ ((t : K) * x) = pcount O τ x

def PStable : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    τ ^ 2 - 4 ≠ 0 → ∀ (j : Etau K τ →ₐ[K] Matrix (Fin 2) (Fin 2) K) (χ : Kˣ →* ℂˣ), (j ω).trace = τ → Unr O χ → ∀ a : (Etau K τ)ˣ, (a : Etau K τ) = ω → (∑ᶠ t : Kˣ ⧸ NE τ, pcount O τ ((t.out : Kˣ) : K)) = gOrb O j χ a

def PKappa : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    τ ^ 2 - 4 ≠ 0 → τ ∈ (algebraMap O K).range →
    (∀ (s : O) (ε : Oˣ), τ ^ 2 - 4 = algebraMap O K (ε * s ^ 2) →
      (∑ᶠ t : Kˣ ⧸ NE τ, hs (τ ^ 2 - 4) ((t.out : Kˣ) : K) * pcount O τ ((t.out : Kˣ) : K)) = (Nat.card (O ⧸ Ideal.span {s}) : ℂ))

def GConj : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    τ ^ 2 - 4 ≠ 0 → ∀ (j j' : Etau K τ →ₐ[K] Matrix (Fin 2) (Fin 2) K), (j ω).trace = τ → (j' ω).trace = τ → (∃ g : GL (Fin 2) K, ∀ z, jU j' z = g⁻¹ * jU j z * g) ∧
    ∀ χ : Kˣ →* ℂˣ, Unr O χ → ∀ z, gOrb O j χ z = gOrb O j' χ z

def GLat : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    τ ^ 2 - 4 ≠ 0 → ∀ (j : Etau K τ →ₐ[K] Matrix (Fin 2) (Fin 2) K) (χ : Kˣ →* ℂˣ), (j ω).trace = τ → Unr O χ → ∀ (z : (Etau K τ)ˣ) (s : Kˣ) (ε : Oˣ), QuadraticAlgebra.norm (z : Etau K τ) = algebraMap O K ε * (s : K) ^ 2 →
    gOrb O j χ z = (((χ s)⁻¹ : ℂˣ) : ℂ) * vcount O τ (((s⁻¹ : Kˣ) : K) • (z : Etau K τ))

def GOdd : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    ∀ (j : Etau K τ →ₐ[K] Matrix (Fin 2) (Fin 2) K) (χ : Kˣ →* ℂˣ) (z : (Etau K τ)ˣ), τ ^ 2 - 4 ≠ 0 → (j ω).trace = τ →
    ¬ EvenVal O (QuadraticAlgebra.norm (z : Etau K τ)) → gOrb O j χ z = 0

def VMax : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    τ ^ 2 - 4 ≠ 0 → ∀ x : Etau K τ, QuadraticAlgebra.trace x ∈ (algebraMap O K).range → QuadraticAlgebra.norm x ∈ (algebraMap O K).range →
    (∃ u : Oˣ, algebraMap O K u = x.im ^ 2 * (τ ^ 2 - 4)) → vcount O τ x = 1

def GVals : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    τ ^ 2 - 4 ≠ 0 → τ ∈ (algebraMap O K).range → ∀ (j : Etau K τ →ₐ[K] Matrix (Fin 2) (Fin 2) K) (χ : Kˣ →* ℂˣ), (j ω).trace = τ → Unr O χ → ∀ a : (Etau K τ)ˣ, (a : Etau K τ) = ω → ∀ z : (Etau K τ)ˣ, (z : Etau K τ) = 1 + ω →
    ((∃ u : Oˣ, algebraMap O K u = 2 + τ) → gOrb O j χ z = gOrb O j χ a) ∧
    ((∃ u : Oˣ, algebraMap O K u = τ ^ 2 - 4) → gOrb O j χ a = 1) ∧
    ((∃ u : Oˣ, algebraMap O K u = 2 - τ) → ∀ (s : Kˣ) (ε : Oˣ), 2 + τ = algebraMap O K ε * (s : K) ^ 2 → gOrb O j χ z = (((χ s)⁻¹ : ℂˣ) : ℂ))

def SplitM : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    ∀ (c : K) (d m : EL Δ τ), IsDat c d m → τ ∈ (algebraMap O K).range → (∃ u : Oˣ, algebraMap O K u = 2 - τ) →
    ∀ ε : Oˣ, lcount O c d (algebraMap O K ε • m) = lcount O c d m

def RamUnit : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ : K), IsLoc O Δ →
    ∀ D : K, D ≠ 0 → ¬ EvenVal O D → ∃ ε : Oˣ, hs D (algebraMap O K ε) = -1

def KapRam : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    ∀ (c : K) (d m : EL Δ τ), IsDat c d m → τ ∈ (algebraMap O K).range → ¬ EvenVal O (2 + τ) → (∃ u : Oˣ, algebraMap O K u = 2 - τ) ∧ kapSum O c d m = 0

def KapMove : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    τ ^ 2 - 4 ≠ 0 → ∀ c : K, c ≠ 0 → ∀ z : (Etau K τ)ˣ, (z : Etau K τ) = 1 + ω → ∀ lam lam' : Lsq K Δ,
    QuadraticAlgebra.norm lam = 2 + τ → QuadraticAlgebra.norm lam' = 2 + τ →
    2 + τ + QuadraticAlgebra.trace lam ≠ 0 → 2 + τ + QuadraticAlgebra.trace lam' ≠ 0 →
    eps τ lam * kapSum O c (dLam lam z) 1 = eps τ lam' * kapSum O c (dLam lam' z) 1

def KapM : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
    τ ^ 2 - 4 ≠ 0 → (∃ u : Oˣ, algebraMap O K u = 2 - τ) → ∀ (s : O) (ε : Oˣ), s ∈ IsLocalRing.maximalIdeal O → 2 + τ = algebraMap O K (ε * s ^ 2) →
    ∀ c : K, EvenVal O c → ∀ z : (Etau K τ)ˣ, (z : Etau K τ) = 1 + ω → ∀ lam : Lsq K Δ, QuadraticAlgebra.norm lam = 2 + τ →
    2 + τ + QuadraticAlgebra.trace lam ≠ 0 →
    kapSum O c (dLam lam z) 1 = eps τ lam * hs Δ (algebraMap O K s) * (Nat.card (O ⧸ Ideal.span {s}) : ℂ)

end UpperTheory.V.Z.Sym.Loc
