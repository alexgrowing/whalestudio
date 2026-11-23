import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.GrowthBounds.ObjPol

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.CovariantDegrees

open Formalism.MainNotions.G

def alt (n : ℕ) (al : Fin n → ℕ) : MvPolynomial (Fin n) ℤ := (Matrix.of fun i j : Fin n => X i ^ al j).det

def rhoN (n : ℕ) : Fin n → ℕ := fun j => n - 1 - j

def Interlace {n : ℕ} (lam mu : Fin n → ℕ) : Prop :=
  (∀ j, lam j ≤ mu j) ∧ ∀ i j : Fin n, i.val + 1 = j.val → mu j ≤ lam i

open Classical in

def adm1 (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℕ), Antitone lam → ∀ b : ℕ,
    alt n (lam + rhoN n) * hsymm (Fin n) ℤ b =
      ∑ mu ∈ (Fintype.piFinset fun _ : Fin n => Finset.range (∑ j, lam j + b + 1)).filter
          (fun mu => Interlace lam mu ∧ ∑ j, mu j = ∑ j, lam j + b),
        alt n (mu + rhoN n)

def adm2 (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] (n : ℕ)
    (E : GLOps n K V), IsGLRep E → ∀ W : Submodule K V, (∀ a b, ∀ x ∈ W, E a b x ∈ W) →
      ∃ W' : Submodule K V, IsCompl W W' ∧ ∀ a b, ∀ x ∈ W', E a b x ∈ W'

def adm3 (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ p : ℕ, p.Prime → ∀ m k b : ℕ, k ≤ m → Nat.log p m < b →
    padicValNat p (m.choose k) = #{i ∈ Finset.Ico 1 b | p ^ i ≤ k % p ^ i + (m - k) % p ^ i}

def ArchimedeanSignatureMatching (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (A : Type) [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A] (σ : Type) (w : A), Irreducible w →
    ∀ F G : MvPolynomial σ A, C w ∣ F * G → C w ∣ F ∨ C w ∣ G

def adm5 (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] (n : ℕ)
    (E : GLOps n K V), IsGLRep E → ∀ mu : Fin n → ℤ,
      (∀ a b : Fin n, a < b → 1 ≤ mu a - mu b + ((b : ℤ) - (a : ℤ))) →
      ∀ ord, NormalOrder n ord → ∀ T : ℕ, Module.finrank K V ≤ T →
        (∀ x ∈ weightSp E mu, pp E mu ord T x ∈ weightSp E mu) ∧
        (∀ x ∈ weightSp E mu, x ∈ nMinus E → pp E mu ord T x = 0) ∧
        (∀ x ∈ weightSp E mu, (∀ a b : Fin n, a < b → E a b x = 0) → pp E mu ord T x = x)

def admitted (D : Formalism.BasicNotions.D7) : Prop := adm1 D ∧ adm2 D ∧ adm3 D ∧ ArchimedeanSignatureMatching D ∧ adm5 D

def InvariantProjectionField (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (p n' : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (_S : UniformizedDVR p O),
    AdmissibleDVR p n' O →
    ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]
      [FiniteDimensional (KK O) V] (E : GLOps n (KK O) V), IsGLRep E →
      ∀ M : Submodule O V, UZLattice E M → MQ (K := KK O) M = ⊤ →
      ∀ Inv : Module.End (KK O) V, IsInvProj E Inv →
        (∀ π : Module.End (KK O) V, IsWtProj E 0 π → ∀ ord, NormalOrder n ord →
          ∀ T : ℕ, Module.finrank (KK O) V ≤ T → Inv = pp E 0 ord T * π) ∧
        ∀ x ∈ M, ((p : O) ^ (N0 n * deF p n (ellOf E (MQ M)))) • Inv x ∈ M

def NablaDeltaComparisonField (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (p n' : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (_S : UniformizedDVR p O),
    AdmissibleDVR p n' O →
    ∀ (n : ℕ) [NeZero n] (lam : Fin n → ℤ) (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V]
      [IsScalarTower O (KK O) V] (E : GLOps n (KK O) V) (v : V), IsIrrHW E lam v →
      (∀ x ∈ Nabla (O := O) E lam v, ((p : O) ^ (N0 n * deF p n (ellWt lam))) • x ∈ Delta (O := O) E v) ∧
      ∀ M : Submodule O V, UZLattice E M → MQ (K := KK O) M = ⊤ →
        (∀ x, (x ∈ M ∧ x ∈ weightSp E lam) ↔ ∃ c : O, x = c • v) →
        Delta (O := O) E v ≤ M ∧ (M : Set V) ⊆ Nabla (O := O) E lam v

def IsotypicProjectorTheoremField (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (p n' : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (_S : UniformizedDVR p O),
    AdmissibleDVR p n' O →
    ∀ (n : ℕ) [NeZero n] (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V]
      [IsScalarTower O (KK O) V] [FiniteDimensional (KK O) V] (E : GLOps n (KK O) V), IsGLRep E →
      ∀ M : Submodule O V, UZLattice E M → MQ (K := KK O) M = ⊤ →
      ∀ Sw : Finset (Fin n → ℤ), (∀ lam ∈ Sw, Dominant lam) →
      ∀ e : (Fin n → ℤ) → Module.End (KK O) V, (∀ lam ∈ Sw, IsIsoProj E lam (e lam)) →
        ∀ x ∈ M, ((p : O) ^ (Sw.sup fun lam => N0 n * deF p n (ellOf E (MQ M) + ellWt lam))) •
          (∑ lam ∈ Sw, e lam x) ∈ M

def TranslateCorollaryField (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (p n' : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (_S : UniformizedDVR p O),
    AdmissibleDVR p n' O →
    ∀ (n : ℕ) [NeZero n] (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V]
      [IsScalarTower O (KK O) V] [FiniteDimensional (KK O) V] (E : GLOps n (KK O) V), IsGLRep E →
      ∀ M : Submodule O V, UZLattice E M → MQ (K := KK O) M = ⊤ →
      ∀ lam : Fin n → ℤ, Dominant lam →
      ∀ e : Module.End (KK O) V, IsIsoProj E lam e → ∀ π : Module.End (KK O) V, IsWtProj E lam π →
      ∀ (c : ℤ) (Y : V), Y ∈ M → e Y = Y →
        (∀ u ∈ UZmon E, ∀ f : V →ₗ[KK O] KK O, (∀ x ∈ M, ∃ o : O, f x = algebraMap O (KK O) o) →
          ∃ o : O, f (π (u Y)) = (p : KK O) ^ c * algebraMap O (KK O) o) →
        ∃ m ∈ M, Y = ((p : KK O) ^ (c - ((N0 n * deF p n (ellWt lam) : ℕ) : ℤ))) • m

def FilteredProjectorCorollaryField (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (p n' : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (_S : UniformizedDVR p O),
    AdmissibleDVR p n' O →
    ∀ (n : ℕ) (ι : Type) [Fintype ι] (LL : Letters ι) (N : ℕ) (Ss : Fin N → Set ι), Monotone Ss →
      (∀ i, PolUZStable LL (Ss i) (IntPol O (ι × Fin n)) ∧
        ∀ u ∈ polUZgens (KK O) LL (Ss i), ∀ F : MvPolynomial (ι × Fin n) (KK O),
          InBB (O := O) p F → InBB (O := O) p (u F)) ∧
      ∀ ee : Fin N → (Fin n → ℤ) → Module.End (KK O) (MvPolynomial (ι × Fin n) (KK O)),
        (∀ i lam, IsIsoProj (glOps (KK O) n LL (Ss i)) lam (ee i lam)) →
        (∀ i j, i ≤ j → ∀ lam a b,
          ee i lam * glOps (KK O) n LL (Ss j) a b = glOps (KK O) n LL (Ss j) a b * ee i lam) ∧
        (∀ i lam (S' : Set ι), Disjoint (Ss i) S' → ∀ a b,
          ee i lam * glOps (KK O) n LL S' a b = glOps (KK O) n LL S' a b * ee i lam) ∧
        (∀ i j lam mu, ee i lam * ee j mu = ee j mu * ee i lam) ∧
        (∀ i lam (F G : MvPolynomial (ι × Fin n) (KK O)), fock (ee i lam F) G = fock F (ee i lam G)) ∧
        ∀ (T : Finset (Fin N → Fin n → ℤ)) (d : ι → ℕ) (F : MvPolynomial (ι × Fin n) (KK O)),
          F ∈ Pol (KK O) n d →
          ((F ∈ IntPol O (ι × Fin n) →
              ((p : KK O) ^ (∑ i, N0 n * Nat.log p (2 * degIn d (Ss i) + n - 1))) •
                (∑ t ∈ T, (List.ofFn fun i => ee i (t i)).prod) F ∈ IntPol O (ι × Fin n)) ∧
           (InBB (O := O) p F →
              InBB (O := O) p (((p : KK O) ^ (∑ i, N0 n * Nat.log p (2 * degIn d (Ss i) + n - 1))) •
                (∑ t ∈ T, (List.ofFn fun i => ee i (t i)).prod) F)))

def ProjectionTheorems (D : Formalism.BasicNotions.D7) : Prop := InvariantProjectionField D ∧ NablaDeltaComparisonField D ∧ IsotypicProjectorTheoremField D ∧ TranslateCorollaryField D ∧ FilteredProjectorCorollaryField D

def ValuationsAdditive (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (R : Type) [Field R] (ι : Type) [Fintype ι] (LL : Letters ι) (n : ℕ) [NeZero n] (S : Set ι),
    (∀ F G : MvPolynomial (ι × Fin n) R, valS LL S (F * G) = valS LL S F + valS LL S G) ∧
    (∀ F G : MvPolynomial (ι × Fin n) R, min (valS LL S F) (valS LL S G) ≤ valS LL S (F + G)) ∧
    (∀ F G : MvPolynomial (ι × Fin n) R, lam1S LL S (F * G) = lam1S LL S F + lam1S LL S G) ∧
    (∀ F G : MvPolynomial (ι × Fin n) R, lam1S LL S (F + G) ≤ max (lam1S LL S F) (lam1S LL S G)) ∧
    (∀ (G : MvPolynomial (ι × Fin n) R) (th : ℤ), ((th : WithTop ℤ) ≤ valS LL S G ↔
      ∀ mu ∈ polWts LL S (polGenSub R LL S G), th ≤ mu (lastIdx n))) ∧
    (∀ (G : MvPolynomial (ι × Fin n) R) (M : ℤ), (lam1S LL S G ≤ (M : WithBot ℤ) ↔
      ∀ mu ∈ polWts LL S (polGenSub R LL S G), mu 0 ≤ M))

def ShaLengthVersionTwo (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (R : Type) [Field R] [CharZero R] (ι : Type) [Fintype ι] (LL : Letters ι) (n : ℕ) [NeZero n] (S : Set ι)
    (e : (Fin n → ℤ) → Module.End R (MvPolynomial (ι × Fin n) R)),
    (∀ mu, IsIsoProj (glOps R n LL S) mu (e mu)) →
    (∀ (G : MvPolynomial (ι × Fin n) R) (th : ℤ),
      (th : WithTop ℤ) ≤ valS LL S G ↔ ∀ mu, e mu G ≠ 0 → th ≤ mu (lastIdx n)) ∧
    (∀ (G : MvPolynomial (ι × Fin n) R) (M : ℤ),
      lam1S LL S G ≤ (M : WithBot ℤ) ↔ ∀ mu, e mu G ≠ 0 → mu 0 ≤ M)

def ValuationLemmaField (D : Formalism.BasicNotions.D7) : Prop := ValuationsAdditive D ∧ ShaLengthVersionTwo D

def detA {R : Type} [CommRing R] {ι : Type} {r : ℕ} (A : Fin r → ι) : MvPolynomial (ι × Fin r) R :=
  (Matrix.of fun i j : Fin r => (X (A i, j) : MvPolynomial (ι × Fin r) R)).det

open Classical in

def degOther {ι : Type} [Fintype ι] {r : ℕ} (LL : Letters ι) (S : Set ι) (A : Fin r → ι) (d : ι → ℕ) : ℕ :=
  ∑ l, if l ∈ S ∧ LL.vec l = true ∧ l ∉ Set.range A then d l else 0

def ConclusionE (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (R : Type) [Field R] (ι : Type) [Fintype ι] (LL : Letters ι) (r : ℕ) [NeZero r] (S : Set ι)
    (A : Fin r → ι), Function.Injective A → (∀ l, A l ∈ S ∧ LL.vec (A l) = true) →
    (∀ (d : ι → ℕ) (G : MvPolynomial (ι × Fin r) R), G ∈ Pol R r d →
      ∀ th : ℤ, (th : WithTop ℤ) ≤ valS LL S G → (degOther LL S A d : ℤ) < th →
        (detA (R := R) A) ^ (th - degOther LL S A d).toNat ∣ G) ∧
    (∀ (G H : MvPolynomial (ι × Fin r) R) (m : ℕ), G = (detA (R := R) A) ^ m * H →
        ∀ S' : Set ι, valS LL S' G ≤ valS LL S' H + ((m : ℤ) : WithTop ℤ))

structure UnitFn where
  t : ℕ
  rho : ℕ
  isC : Bool
  inv : Bool

def unitFn (p : ℕ) (u : UnitFn) (m : ℕ) : ℚ :=
  let b := if u.isC then cUnit (p ^ (u.t + 1)) m else dUnit (p ^ (u.t + 1)) m u.rho
  if u.inv then b⁻¹ else b

def PadicGe (p : ℕ) (x : ℚ) (r : ℝ) : Prop := x = 0 ∨ r ≤ (padicValRat p x : ℝ)

def UnitFunctionExpansion (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ p : ℕ, p.Prime → 5 ≤ p →
    (∀ u : UnitFn, u.rho < p ^ (u.t + 1) →
      (∃ a : ℕ → ℚ, (∀ m : ℕ, unitFn p u m = ∑ j ∈ Finset.range (m + 1), a j * (m.choose j : ℚ)) ∧
        ∀ j : ℕ, PadicGe p (a j) ((j : ℝ) / 4)) ∧
      ∀ c : ℕ, ∃ q : ℕ → ℚ, (∀ j, PadicGe p (q j) 0) ∧
        ∀ m : ℕ, PadicGe p (unitFn p u m - ∑ j ∈ Finset.range (4 * c + 1), q j * (m.choose j : ℚ)) c) ∧
    ∀ (N m : ℕ) (us : Fin m → UnitFn) (var : Fin m → Fin N), (∀ i, (us i).rho < p ^ ((us i).t + 1)) →
      ∀ c : ℕ, ∃ (T : Finset (Fin N → ℕ)) (q : (Fin N → ℕ) → ℚ),
        (∀ j ∈ T, ∑ k, j k ≤ 4 * c ∧ PadicGe p (q j) 0) ∧
        ∀ x : Fin N → ℕ, PadicGe p ((∏ i, unitFn p (us i) (x (var i))) -
          ∑ j ∈ T, q j * ∏ k, ((x k).choose (j k) : ℚ)) c

def FactorialUnitDecomposition (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ p : ℕ, p.Prime → 5 ≤ p →
    (∀ t rho e' : ℕ, rho < p ^ (t + 1) →
      (((rho + p ^ (t + 1) * e').factorial : ℕ) : ℚ) =
        (rho.factorial : ℚ) * (e'.factorial : ℚ) * ((p ^ (t + 1)).factorial : ℚ) ^ e' *
          cUnit (p ^ (t + 1)) e' * dUnit (p ^ (t + 1)) e' rho) ∧
    ∀ (σ : Type) [Fintype σ] (t rho : σ → ℕ), (∀ k, rho k < p ^ (t k + 1)) →
      (∀ e' : σ → ℕ, (∏ k, cUnit (p ^ (t k + 1)) (e' k) * dUnit (p ^ (t k + 1)) (e' k) (rho k)) ≠ 0 ∧
        padicValRat p (∏ k, cUnit (p ^ (t k + 1)) (e' k) * dUnit (p ^ (t k + 1)) (e' k) (rho k)) = 0) ∧
      (∀ (inv : Bool) (c : ℕ), ∃ Q : MvPolynomial σ ℚ, Q.totalDegree ≤ 4 * c ∧ ∀ e' : σ → ℕ,
        PadicGe p
          ((if inv then (∏ k, cUnit (p ^ (t k + 1)) (e' k) * dUnit (p ^ (t k + 1)) (e' k) (rho k))⁻¹
            else (∏ k, cUnit (p ^ (t k + 1)) (e' k) * dUnit (p ^ (t k + 1)) (e' k) (rho k))) -
          MvPolynomial.eval (fun k => (e' k : ℚ)) Q) c) ∧
      (∀ (inv : Bool) (c : ℕ), ∃ (T : Finset (σ → ℕ)) (q : (σ → ℕ) → ℚ),
        (∀ j ∈ T, ∑ k, j k ≤ 4 * c ∧ PadicGe p (q j) 0) ∧
        ∀ e' : σ → ℕ, PadicGe p
          ((if inv then
              ((∏ k, (((rho k + p ^ (t k + 1) * e' k).factorial : ℕ) : ℚ)) /
                (∏ k, ((rho k).factorial : ℚ) * ((e' k).factorial : ℚ) *
                  ((p ^ (t k + 1)).factorial : ℚ) ^ (e' k)))⁻¹
            else
              ((∏ k, (((rho k + p ^ (t k + 1) * e' k).factorial : ℕ) : ℚ)) /
                (∏ k, ((rho k).factorial : ℚ) * ((e' k).factorial : ℚ) *
                  ((p ^ (t k + 1)).factorial : ℚ) ^ (e' k)))) -
           ∑ j ∈ T, q j * ∏ k, ((e' k).choose (j k) : ℚ)) c)

def DegreeTruncationLemma (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (R : Type) [Field R] (ι : Type) [Fintype ι] (LL : Letters ι) (n : ℕ) [NeZero n] (S : Set ι) (c : ℕ)
    (T : Finset (ι × Fin n →₀ ℕ)), (∀ m ∈ T, (m.sum fun _ k => k) ≤ 4 * c) →
    ∀ (q : (ι × Fin n →₀ ℕ) → R) (F : MvPolynomial (ι × Fin n) R),
      valS LL S F ≤ valS LL S (∑ m ∈ T, q m • (monomial m 1 * divDer m F)) + (((4 * c : ℕ) : ℤ) : WithTop ℤ) ∧
      lam1S LL S (∑ m ∈ T, q m • (monomial m 1 * divDer m F)) ≤ lam1S LL S F + (((4 * c : ℕ) : ℤ) : WithBot ℤ)

def UnitProductSecondLemma (D : Formalism.BasicNotions.D7) : Prop := FactorialUnitDecomposition D ∧ DegreeTruncationLemma D

def UnitProductLemmas (D : Formalism.BasicNotions.D7) : Prop := UnitFunctionExpansion D ∧ UnitProductSecondLemma D

open Classical in

def vecDeg {ι : Type} {n : ℕ} (LL : Letters ι) (S : Set ι) (al : ι × Fin n →₀ ℕ) : ℕ :=
  ∑ v ∈ al.support, if v.1 ∈ S ∧ LL.vec v.1 = true then al v else 0

open Classical in

def covDeg {ι : Type} {n : ℕ} (LL : Letters ι) (S : Set ι) (al : ι × Fin n →₀ ℕ) : ℕ :=
  ∑ v ∈ al.support, if v.1 ∈ S ∧ LL.vec v.1 = false then al v else 0

def DerivativeValuationBound (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (R : Type) [Field R] (ι : Type) [Fintype ι] (LL : Letters ι) (n : ℕ) [NeZero n] (S : Set ι)
    (F : MvPolynomial (ι × Fin n) R) (al be : ι × Fin n →₀ ℕ),
    valS LL S F ≤ valS LL S (monomial al 1 * divDer be F) + (((al.sum fun _ k => k) + (be.sum fun _ k => k) : ℕ) : ℤ) ∧
    lam1S LL S (monomial al 1 * divDer be F) ≤ lam1S LL S F + (((al.sum fun _ k => k) + (be.sum fun _ k => k) : ℕ) : ℤ) ∧
    valS LL S F ≤ valS LL S (monomial al 1 * divDer be F) + ((covDeg LL S al + vecDeg LL S be : ℕ) : ℤ) ∧
    lam1S LL S (monomial al 1 * divDer be F) ≤ lam1S LL S F + ((vecDeg LL S al + covDeg LL S be : ℕ) : ℤ)

def DerivativeDigitExpansion (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ (t : ℕ) (σ : Type) [Fintype σ] (rho M : σ → ℕ), (∀ k, rho k < p ^ t) →
    ∀ c : ℕ, ∃ (T : Finset (σ → ℕ)) (γ : (σ → ℕ) → ℤ),
      (∀ l ∈ T, ((∑ k, l k : ℕ) : ℝ) ≤ ((∑ k, M k : ℕ) : ℝ) / ((p ^ t : ℕ) : ℝ) + c) ∧
      (∀ l ∈ T, ∀ k, M k ≤ rho k + p ^ t * l k) ∧
      ∀ e' : σ → ℕ, (p : ℤ) ^ c ∣
        ((∏ k, (((rho k + p ^ t * e' k).choose (M k) : ℕ) : ℤ)) - ∑ l ∈ T, γ l * ∏ k, (((e' k).choose (l k) : ℕ) : ℤ))

open Classical in

def TrueDerivativeDigitClass (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (R : Type) [CommRing R] (σ : Type) (P : σ → ℕ), (∀ k, 1 ≤ P k) → ∀ (rho : σ → ℕ) (k : σ)
    (F : MvPolynomial σ R), F ∈ DigitClassL R P rho →
      pderiv k F ∈ DigitClassL R P (Function.update rho k (if 1 ≤ rho k then rho k - 1 else P k - 1))

def DerivativeLemma (D : Formalism.BasicNotions.D7) : Prop := DerivativeValuationBound D ∧ DerivativeDigitExpansion D ∧ TrueDerivativeDigitClass D

def DerivativeLemmaField (D : Formalism.BasicNotions.D7) : Prop := DerivativeLemma D

def Conclusion1 (D : Formalism.BasicNotions.D7) : Prop := ProjectionTheorems D ∧ ValuationLemmaField D ∧ ConclusionE D ∧ UnitProductLemmas D ∧ DerivativeLemmaField D

def IntegralityFromMetric (D : Formalism.BasicNotions.D7) : Prop := admitted D → Conclusion1 D

def AdmF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ (x : ℝ) (i : Fm.Ix x), admitted (Fm.D x i)

def Conclusion1Family {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∃ x0 : ℝ, ∀ x : ℝ, x0 ≤ x → ∀ i : Fm.Ix x, Conclusion1 (Fm.D x i)

def FamilyGlobalDerivation {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := AdmF Fm → Conclusion1Family Fm

end Formalism.MainNotions.CovariantDegrees
