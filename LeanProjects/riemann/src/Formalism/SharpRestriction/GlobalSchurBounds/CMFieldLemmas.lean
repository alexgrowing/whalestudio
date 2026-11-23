import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataParams₂
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FiltrationBoundaryCriterion

noncomputable section

namespace Formalism.MainNotions.UnusedSlot33

open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory Ideal
open scoped Pointwise

def rdVal (D : D7) : ℝ :=
  (2 : ℝ) ^ ((D.R.e : ℝ) + 1 - (2 : ℝ) ^ (-(D.R.e : ℝ))) * Real.sqrt ((D.host.q : ℝ) * D.host.d)

def Conclusion1 (D : D7) : Prop :=
  IsCMField D.host.E ∧ Module.finrank ℚ D.host.E = 2 * D.R.f ∧
  (∀ p : ℕ, p.Prime →
    (1 < (span {(p : ℤ)}).ramificationIdxIn (𝓞 D.host.E) ↔ p ∣ D.host.condN)) ∧
  (∀ x : D.host.E, (∃ m : ℕ, 0 < m ∧ x ^ m = 1) → Algebra.norm D.host.K x = 1) ∧
  (∀ 𝔭 : Ideal (𝓞 D.host.F), 𝔭.IsPrime → 𝔭 ≠ ⊥ → 𝔭.ramificationIdxIn (𝓞 D.host.E) = 1) ∧
  (∀ p : ℕ, p.Prime → p ∣ D.host.condN →
    ∀ 𝔭 : Ideal (𝓞 D.host.F), 𝔭.IsPrime → 𝔭.LiesOver (span {(p : ℤ)}) →
      (primesOver 𝔭 (𝓞 D.host.E)).ncard = 2) ∧
  rdF D = D.host.rdE

open Classical in

def Conclusion2 (D : D7) : Prop :=
  (∀ φ : D.host.E →+* ℂ, φ ∈ PhiEmb D ↔ (starRingEnd ℂ).comp φ ∉ PhiEmb D) ∧
  (∀ φ ∈ PhiEmb D, ∀ x : D.host.E, x ∈ D.host.K → φ x = D.host.φ₀ x) ∧
  (∀ τ ∈ D.R.Psi, Set.BijOn (rho D τ) {g | g ∉ D.R.Psi} (D.R.Psi : Set (D.R.GG))) ∧
  (∀ h t : HH D,
    rho D (D.R.tau1 t) (gOf D c0 h) = D.R.tau1 (t + h) ∧
    rho D (D.R.tau2 t) (gOf D c0 h) = D.R.tau2 (t + h) ∧
    rho D (D.R.tau1 t) (gOf D sgc0 h) = D.R.tau2 (t + h) ∧
    rho D (D.R.tau2 t) (gOf D sgc0 h) = D.R.tau1 (t + h)) ∧
  (∀ χ : D.R.GG →* ℂˣ,
    (∑ g ∈ Finset.univ.filter (fun g : D.R.GG => g ∉ D.R.Psi),
        starRingEnd ℂ ((χ g : ℂˣ) : ℂ)) =
      if χ = 1 then (D.R.f : ℂ) else if χ = D.R.chC then -(D.R.f : ℂ) else 0) ∧
  (∀ g : D.R.GG, 2 * (if g.1 = sgc0 then (1 : ℚ) else 0) =
    (1 - ((D.R.chD g : ℤˣ) : ℚ)) * (1 + ((D.R.chQ g : ℤˣ) : ℚ)) / 2)

def Inert (D : D7) (𝔭 : Ideal (𝓞 D.host.F)) : Prop :=
  (primesOver 𝔭 (𝓞 D.host.E)).ncard = 1 ∧ 𝔭.inertiaDegIn (𝓞 D.host.E) = 2

def PointsLemma (D : D7) : Prop :=
  ∀ φ₀ : G0, (φ₀ = c0 ∨ φ₀ = sgc0) → ∀ h : HH D,
    (∀ τ ∈ D.R.Psi, ∀ i : ℕ,
      (Even i → (gOf D φ₀ h) ^ i * τ ∈ D.R.Psi) ∧
      (Odd i → ∃ τ' ∈ D.R.Psi, (gOf D φ₀ h) ^ i * τ = D.R.cc * τ')) ∧
    (∀ (t : HH D) (i : ℕ), hco D (Formalism.HC.Frame.placeOf ((gOf D φ₀ h) ^ i * D.R.tau1 t)) = t + i • h) ∧
    (φ₀ = c0 → ∀ (t : HH D) (i : ℕ), (Formalism.HC.Frame.placeOf ((gOf D φ₀ h) ^ i * D.R.tau1 t)).1 = 1) ∧
    (φ₀ = sgc0 → ∀ (t : HH D) (i : ℕ), (Formalism.HC.Frame.placeOf ((gOf D φ₀ h) ^ i * D.R.tau1 t)).1 =
      if Even i then 1 else (D.R.sg).1) ∧
    (D.R.cc ∈ Subgroup.zpowers (gOf D φ₀ h) ↔ φ₀ = c0 ∧ Odd (addOrderOf h)) ∧
    (∀ p : ℕ, p.Prime → (span {(p : ℤ)}).ramificationIdxIn (𝓞 D.host.E) = 1 →
      frob D p = gOf D φ₀ h →
      ∀ 𝔭 : Ideal (𝓞 D.host.F), 𝔭.IsPrime → 𝔭.LiesOver (span {(p : ℤ)}) →
        (Inert D 𝔭 ↔ φ₀ = c0 ∧ Odd (addOrderOf h))) ∧
    (φ₀ = c0 → ∀ τ ∈ D.R.Psi,
      (Set.range fun i : ℕ => Formalism.HC.Frame.placeOf ((gOf D φ₀ h) ^ i * τ)).ncard = addOrderOf h ∧
        (D.R.h h ≠ 0 → Even (addOrderOf h)))

open Classical in

def Conclusion4 (D : D7) (C : ℝ) : Prop :=
  (∀ l : ℕ, l.Prime → l ≠ 2 → ∀ j : ℕ, j ≤ D.R.e →
    ((2 ^ j : ℕ) • hOf D.R.e l = 0 ↔
      ((l : ZMod (4 * 2 ^ D.R.e / 2 ^ j)) = 1 ∨ (l : ZMod (4 * 2 ^ D.R.e / 2 ^ j)) = -1))) ∧
  (∀ J : ℝ, 1 ≤ J → ∀ l : ℕ, l.Prime → l ≠ 2 → (ordH (hOf D.R.e l) : ℝ) ≤ J →
    4 * ((2 ^ D.R.e : ℕ) : ℝ) / J - 1 ≤ l) ∧
  (∀ J : ℝ, 1 ≤ J → ∀ S : Finset ℕ,
    (∀ l ∈ S, l.Prime ∧ l ≠ 2 ∧ (ordH (hOf D.R.e l) : ℝ) ≤ J) →
    ∑ l ∈ S, Real.log l / (l : ℝ) ^ 2 ≤
      C * J ^ 2 * Real.log ((2 ^ D.R.e : ℕ) : ℝ) / ((2 ^ D.R.e : ℕ) : ℝ) ^ 2) ∧
  (∀ J : ℝ, 1 ≤ J → ∀ Y : ℝ,
    ∑ l ∈ (Finset.range (⌊Y⌋₊ + 1)).filter
        (fun l => l.Prime ∧ l ≠ 2 ∧ (ordH (hOf D.R.e l) : ℝ) ≤ J),
      Real.log l / (l : ℝ) ≤
      C * J * Real.log (((2 ^ D.R.e : ℕ) : ℝ) * Y) ^ 2 / ((2 ^ D.R.e : ℕ) : ℝ))

def NoThreeTermRelation (T : Finset ℕ) (L : ℕ) : Prop :=
  ∀ s₁ ∈ T, ∀ s₂ ∈ T, ∀ s₃ ∈ T, s₁ ≠ s₂ → s₁ ≠ s₃ → s₂ ≠ s₃ →
    ∀ i j : ℤ, 0 < |i| → |i| ≤ L → 0 < |j| → |j| ≤ L → i ≠ j →
      j * ((s₂ : ℤ) - s₁) ≠ i * ((s₃ : ℤ) - s₁)

def transl {φ : Formalism.HC.Frame} (T : Finset ℕ) (u₀ : φ.A) : Set φ.A := {x | ∃ s ∈ T, x = φ.dig s + u₀}

def coset {G : Type} [AddCommGroup G] (t h : G) : Set G := {x | ∃ i : ℤ, x = t + i • h}

open Classical in

def Conclusion5 (D : D7) (C : ℝ) : Prop :=
  ∀ Lw : ℕ, 2 ≤ Lw → ∃ T₂ : Finset ℕ,
    (∀ s ∈ T₂, (s : ℝ) < (D.R.n0 : ℝ) / (4 * Lw)) ∧
    (D.R.n0 : ℝ) * Real.exp (-C * Real.sqrt (Real.log D.R.n0 * Real.log Lw)) / Lw ≤ T₂.card ∧
    NoThreeTermRelation T₂ Lw ∧
    ∀ u₀ t h : HH D,
      (4 * Lw < addOrderOf h → ∀ i₀ : ℤ,
        ((Finset.Ico i₀ (i₀ + Lw)).filter (fun i : ℤ => t + i • h ∈ transl T₂ u₀)).card ≤ 2) ∧
      (addOrderOf h ≤ 4 * Lw → (coset t h ∩ transl T₂ u₀).ncard ≤ 1)

def TorusPairsWithVariant (D : D7) : Prop :=
  3 ≤ D.host.Lw → ∀ φ : D.R.GG, φ ∉ D.R.Psi → φ ≠ D.R.cc → ∀ τ ∈ D.R.Psi, ∀ i : ℕ,
    ¬ (Formalism.HC.Frame.placeOf (φ ^ i * τ) ∈ thick D ∧ Formalism.HC.Frame.placeOf (φ ^ (i + 1) * τ) ∈ thick D ∧
      Formalism.HC.Frame.placeOf (φ ^ (i + 2) * τ) ∈ thick D)

def bern {α : Type*} [Fintype α] (δ : ℝ) (T : Finset α) : ℝ :=
  δ ^ T.card * (1 - δ) ^ (Fintype.card α - T.card)

open Classical in

def Conclusion6 (D : D7) (sc : Scale) : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ 1 → 16 ≤ δ * D.R.n →
  ∀ β : ℝ, ∀ BAD : HH D → HH D → Finset (HH D) → Prop,
    (∀ (h t : HH D) (T T' : Finset (HH D)), (∀ x ∈ coset t h, (x ∈ T ↔ x ∈ T')) →
      (BAD h t T ↔ BAD h t T')) →
    (∀ h : HH D, sc.x ^ (sc.eps / 4) ≤ (addOrderOf h : ℝ) → ∀ t : HH D,
      (∑ T : Finset (HH D), if t ∈ T ∧ BAD h t T then bern δ T else 0) ≤ β * δ) →
    ∀ (P : Finset ℕ) (hp : ℕ → HH D) (ω : ℕ → ℝ),
      (∀ p ∈ P, sc.x ^ (sc.eps / 4) ≤ (addOrderOf (hp p) : ℝ)) → (∀ p ∈ P, 0 ≤ ω p) →
      ∃ T : Finset (HH D), δ * D.R.n / 2 ≤ T.card ∧ (T.card : ℝ) ≤ 2 * δ * D.R.n ∧
        ∑ p ∈ P, ω p * ((T.filter (fun t => BAD (hp p) t T)).card : ℝ) ≤
          4 * β * δ * D.R.n * ∑ p ∈ P, ω p

section UnitaryGroups

open Matrix

variable {A : Type} [CommRing A] {ι : Type} [Fintype ι] [DecidableEq ι]

def cT (σ : A →+* A) {m p : Type} (M : Matrix m p A) : Matrix p m A := (M.map σ)ᵀ

def IsHerm (σ : A →+* A) (J : Matrix ι ι A) : Prop := cT σ J = J

def hform (σ : A →+* A) (J : Matrix ι ι A) (x y : ι → A) : A :=
  ∑ i, ∑ j, σ (x i) * J i j * y j

theorem cT_mul (σ : A →+* A) {m p q : Type} [Fintype p] (M : Matrix m p A) (N : Matrix p q A) :
    cT σ (M * N) = cT σ N * cT σ M := by
  simp [cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_one (σ : A →+* A) : cT σ (1 : Matrix ι ι A) = 1 := by
  simp [cT, Matrix.map_one σ (map_zero σ) (map_one σ)]

def UJ (σ : A →+* A) (J : Matrix ι ι A) : Subgroup (GL ι A) where
  carrier := {g | cT σ (g : Matrix ι ι A) * J * (g : Matrix ι ι A) = J}
  one_mem' := by simp [cT_one]
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Units.val_mul] at *
    calc cT σ ((a : Matrix ι ι A) * (b : Matrix ι ι A)) * J * ((a : Matrix ι ι A) * (b : Matrix ι ι A))
        = cT σ (b : Matrix ι ι A) * (cT σ (a : Matrix ι ι A) * J * (a : Matrix ι ι A)) *
            (b : Matrix ι ι A) := by
          rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = J := by rw [ha, hb]
  inv_mem' := by
    intro g hg
    simp only [Set.mem_ofPred_eq] at *
    calc cT σ ((g⁻¹ : GL ι A) : Matrix ι ι A) * J * ((g⁻¹ : GL ι A) : Matrix ι ι A)
        = cT σ ((g⁻¹ : GL ι A) : Matrix ι ι A) * (cT σ (g : Matrix ι ι A) * J * (g : Matrix ι ι A))
            * ((g⁻¹ : GL ι A) : Matrix ι ι A) := by rw [hg]
      _ = cT σ ((g : Matrix ι ι A) * ((g⁻¹ : GL ι A) : Matrix ι ι A)) * J
            * ((g : Matrix ι ι A) * ((g⁻¹ : GL ι A) : Matrix ι ι A)) := by
          rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = J := by rw [Units.mul_inv, cT_one, Matrix.one_mul, Matrix.mul_one]

def bc {B : Type} [CommRing B] (φ : A →+* B) : GL ι A →* GL ι B :=
  Units.map (RingHom.mapMatrix φ).toMonoidHom

end UnitaryGroups

section Points

open TensorProduct

variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {ι : Type} [Fintype ι] [DecidableEq ι]

def sigR (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] : E ⊗[F] R →+* E ⊗[F] R :=
  (Algebra.TensorProduct.map σ (AlgHom.id F R)).toRingHom

def inclE (R : Type) [CommRing R] [Algebra F R] : E →+* E ⊗[F] R :=
  Algebra.TensorProduct.includeLeftRingHom

def UPts (σ : E →ₐ[F] E) (J : Matrix ι ι E) (R : Type) [CommRing R] [Algebra F R] :
    Subgroup (GL ι (E ⊗[F] R)) := UJ (sigR σ R) (J.map (inclE (F := F) R))

def ratPts (σ : E →ₐ[F] E) (J : Matrix ι ι E) (R : Type) [CommRing R] [Algebra F R] :
    Subgroup (GL ι (E ⊗[F] R)) := (UJ (σ : E →+* E) J).map (bc (inclE (F := F) R))

def IsDef (σ : E →ₐ[F] E) (J : Matrix ι ι E) : Prop :=
  ∀ ι' : F →+* ℝ,
    (∀ x : ι → E, x ≠ 0 → ∃ a : F, algebraMap F E a = hform (σ : E →+* E) J x x ∧ 0 < ι' a) ∨
    (∀ x : ι → E, x ≠ 0 → ∃ a : F, algebraMap F E a = hform (σ : E →+* E) J x x ∧ ι' a < 0)

@[reducible] def tensTop (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] :
    TopologicalSpace (E ⊗[F] R) :=
  letI : Algebra R (E ⊗[F] R) := Algebra.TensorProduct.rightAlgebra
  moduleTopology R (E ⊗[F] R)

def evalV (F : Type) [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    IsDedekindDomain.FiniteAdeleRing (𝓞 F) F →ₐ[F] v.adicCompletion F where
  toFun a := a v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

def prV [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    E ⊗[F] IsDedekindDomain.FiniteAdeleRing (𝓞 F) F →+* E ⊗[F] v.adicCompletion F :=
  (Algebra.TensorProduct.map (AlgHom.id F E) (evalV F v)).toRingHom

end Points

def IsProG {G : Type} [Group G] [TopologicalSpace G] (g : ℕ) (Uw : Subgroup G) : Prop :=
  IsCompact (Uw : Set G) ∧ ∀ N : Subgroup Uw, IsOpen (N : Set Uw) → N.Normal → ∃ m : ℕ, N.index = g ^ m

open IsDedekindDomain TensorProduct in

def division_rows_rational_lattice (D : D7) : Prop :=
  ∀ σ : D.host.E →ₐ[D.host.F] D.host.E, (∀ x, σ x = D.host.conj x) →
  ∀ J : Matrix (Fin D.R.k) (Fin D.R.k) D.host.E, IsHerm (σ : D.host.E →+* D.host.E) J → IsDef σ J →
  ∀ g : ℕ, g.Prime → 2 * D.R.f * D.R.k < g - 1 →
  ∀ v : HeightOneSpectrum (𝓞 D.host.F), ((g : 𝓞 D.host.F) ∈ v.asIdeal) →
  letI := tensTop (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
  letI := tensTop (F := D.host.F) (E := D.host.E) (v.adicCompletion D.host.F)
  ∀ U : Subgroup (GL (Fin D.R.k) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)),
    U ≤ UPts σ J (FiniteAdeleRing (𝓞 D.host.F) D.host.F) →
    IsCompact (U : Set (GL (Fin D.R.k) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))) →
    IsOpen {x : UPts σ J (FiniteAdeleRing (𝓞 D.host.F) D.host.F) | (x : GL _ _) ∈ U} →
  ∀ Uw : Subgroup (GL (Fin D.R.k) (D.host.E ⊗[D.host.F] v.adicCompletion D.host.F)),
    IsProG g Uw → (∀ u ∈ U, bc (prV v) u ∈ Uw) →
  ∀ y ∈ UPts σ J (FiniteAdeleRing (𝓞 D.host.F) D.host.F),
    ratPts σ J (FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊓ U.map (MulAut.conj y).toMonoidHom = ⊥

def Conclusion8 (D : D7) : Prop :=
  ∃ aa aab : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E,
    (∀ x : D.host.E, x ∈ aab ↔ D.host.conj x ∈ aa) ∧
    ((differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) : Ideal (𝓞 D.host.E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)⁻¹ = aa * aab ∧
    (∀ cc : Ideal (𝓞 D.host.K), cc ≠ ⊥ →
      (∀ x : D.host.E,
        (∀ y ∈ ((Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc : Ideal (𝓞 D.host.E)) :
            FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) * aa,
          x * y ∈ ((Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc : Ideal (𝓞 D.host.E)) :
            FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) * aa) ↔ IsIntegral ℤ x) ∧
      ∃ ξ : D.host.E, ξ ∈ D.host.K ∧ D.host.conj ξ = -ξ ∧ (∀ φ ∈ PhiEmb D, 0 < (φ ξ).im) ∧
        ∀ y : D.host.E,
          y ∈ ((Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc : Ideal (𝓞 D.host.E)) :
            FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) * aa ↔
          ∀ x ∈ ((Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc : Ideal (𝓞 D.host.E)) :
            FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) * aa,
            Algebra.trace ℚ D.host.E (ξ * D.host.conj x * y) ∈ (algebraMap ℤ ℚ).range) ∧
    (∀ p : ℕ, p.Prime → (primesOver (span {(p : ℤ)}) (𝓞 D.host.K)).ncard = 2 →
      ∀ P : Ideal (𝓞 D.host.E), P.IsPrime → P.LiesOver (span {(p : ℤ)}) →
        ∀ σ τ : D.host.E ≃ₐ[ℚ] D.host.E, τ ∈ MulAction.stabilizer (D.host.E ≃ₐ[ℚ] D.host.E) P →
          (D.host.galE (σ * τ) ∈ D.R.Psi ↔
            D.host.galE σ ∈ D.R.Psi))

def Conclusion₂ (D : D7) (C₄ C₅ : ℝ) (sc : Scale) : Prop :=
  Conclusion1 D ∧ Conclusion2 D ∧ PointsLemma D ∧ Conclusion4 D C₄ ∧ Conclusion5 D C₅ ∧ TorusPairsWithVariant D ∧ Conclusion6 D sc ∧ division_rows_rational_lattice D ∧ Conclusion8 D

def Stmt (D : D7) (C₄ C₅ : ℝ) (sc : Scale) : Prop := Conclusion₂ D C₄ C₅ sc

def ConclusionOnFamily {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (C₄ C₅ : ℝ) : Prop :=
  ∀ x : ℝ, Fm.x1 < x → ∀ i : Fm.Ix x, Conclusion₂ (Fm.D x i) C₄ C₅ (Fm.L x i).sc

def KudlaFamilyStatement {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (C₄ C₅ : ℝ) : Prop := ConclusionOnFamily Fm C₄ C₅

end Formalism.MainNotions.UnusedSlot33

end
