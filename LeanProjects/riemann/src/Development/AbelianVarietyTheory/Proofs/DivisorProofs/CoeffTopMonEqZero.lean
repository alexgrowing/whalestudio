import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsThetaMeanSquareNorm
import Development.AbelianVarietyTheory.Definitions.Divisors.SecJets4
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory

namespace GlobalTheory.SecJet

section Alg

variable (R : Type) [CommRing R]

def sqIdeal (k : ℕ) : Ideal (MvPolynomial (Fin k) R) :=
  Ideal.span (Set.range fun a : Fin k => (MvPolynomial.X a : MvPolynomial (Fin k) R) ^ 2)

abbrev EpsAlg (k : ℕ) : Type := MvPolynomial (Fin k) R ⧸ sqIdeal R k

def topMon (k : ℕ) : Fin k →₀ ℕ := ∑ a, Finsupp.single a 1

theorem coeff_topMon_eq_zero {k : ℕ} {p : MvPolynomial (Fin k) R} (hp : p ∈ sqIdeal R k) :
    MvPolynomial.coeff (topMon k) p = 0 := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 hp
  rw [MvPolynomial.coeff_sum]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_mul_monomial', if_neg]
  intro h
  have := h a
  simp [topMon, Finsupp.finsetSum_apply, Finsupp.single_apply] at this

def topCoeff (k : ℕ) : EpsAlg R k →ₗ[R] R :=
  (Submodule.liftQ ((sqIdeal R k).restrictScalars R) (MvPolynomial.lcoeff R (topMon k))
    (fun _ hp => LinearMap.mem_ker.2 (coeff_topMon_eq_zero R hp))) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv R (sqIdeal R k)).symm.toLinearMap

def eps {k : ℕ} (a : Fin k) : EpsAlg R k := Ideal.Quotient.mk _ (MvPolynomial.X a)

theorem eps_mul_self {k : ℕ} (a : Fin k) : eps R a * eps R a = 0 := by
  rw [eps, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, ← sq]
  exact Ideal.subset_span ⟨a, rfl⟩

def epsIncl {k : ℕ} (a : Fin k) : DualNumber R →ₐ[R] EpsAlg R k :=
  DualNumber.lift ⟨(Algebra.ofId R (EpsAlg R k), eps R a), eps_mul_self R a,
    fun _ => Commute.all _ _⟩

end Alg

end GlobalTheory.SecJet

namespace GlobalTheory.SecJet

section Geo

variable (R : Type) [CommRing R]

abbrev epsT (k : ℕ) : Over (Sp R) := Over.mk (spMap (algebraMap R (EpsAlg R k)))

theorem spMap_comp_eq {A B : Type} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) :
    spMap (f : A →+* B) ≫ spMap (algebraMap R A) = spMap (algebraMap R B) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact f.comp_algebraMap

def epsIn {k : ℕ} (a : Fin k) : epsT R k ⟶ epsR R :=
  Over.homMk (spMap ((epsIncl R a : DualNumber R →ₐ[R] EpsAlg R k) : DualNumber R →+* EpsAlg R k))
    (spMap_comp_eq R (epsIncl R a))

def epsScaleA (c : R) : DualNumber R →ₐ[R] DualNumber R :=
  { epsScaleR c with commutes' := fun r => by simp [epsScaleR] }

def epsScale (c : R) : epsR R ⟶ epsR R :=
  Over.homMk (spMap (epsScaleR c)) (spMap_comp_eq R (epsScaleA R c))

variable {R}

def epsPt {G : Over (Sp R)} [GrpObj G] (y : epsR R ⟶ G) (k : ℕ) : epsT R k ⟶ G :=
  (List.ofFn fun a : Fin k => epsIn R a ≫ y).prod

def jetVal {G : Over (Sp R)} [GrpObj G] (y : epsR R ⟶ G) (k : ℕ) (U : G.left.Opens) (f : Γ(G.left, U)) : R :=
  topCoeff R k (valR (epsPt y k).left U f)

def tanComb {G : Over (Sp R)} [GrpObj G] {m : ℕ} (c : Fin m → R) (v : Fin m → (epsR R ⟶ G)) : epsR R ⟶ G :=
  (List.ofFn fun i => epsScale R (c i) ≫ v i).prod

theorem isLieComb_tanComb {G : Over (Sp R)} [GrpObj G] {m : ℕ} (c : Fin m → R) (v : Fin m → (epsR R ⟶ G)) :
    IsLieComb c v (tanComb c v) :=
  ⟨_, fun _ => rfl, rfl⟩

end Geo

def jetFun {K : Type} [Field K] {G : Over (Sp K)} [GrpObj G] (y : epsR K ⟶ G) {L : LB G.left} (i₀ : L.ι) (c₀ : K)
    {r : ℕ} (b : Fin r → L.Sec) (i : ℕ) : (Fin r → K) →ₗ[K] K :=
  ∑ a, (c₀⁻¹ * jetVal y i (L.U i₀) ((b a).f i₀)) • LinearMap.proj a

theorem jetFun_apply {K : Type} [Field K] {G : Over (Sp K)} [GrpObj G] (y : epsR K ⟶ G) {L : LB G.left} (i₀ : L.ι)
    (c₀ : K) {r : ℕ} (b : Fin r → L.Sec) (i : ℕ) (c : Fin r → K) :
    jetFun y i₀ c₀ b i c = ∑ a, c₀⁻¹ * jetVal y i (L.U i₀) ((b a).f i₀) * c a := by
  simp [jetFun]

def filt {K V : Type} [Field K] [AddCommGroup V] [Module K V] (j : ℕ → V →ₗ[K] K) (i : ℕ) : Submodule K V :=
  Nat.rec ⊤ (fun k F => F ⊓ LinearMap.ker (j k)) i

theorem filt_succ {K V : Type} [Field K] [AddCommGroup V] [Module K V] (j : ℕ → V →ₗ[K] K) (i : ℕ) :
    filt j (i + 1) = filt j i ⊓ LinearMap.ker (j i) := rfl

open Classical in

def rigVal {K : Type} [Field K] [NumberField K] {P : Out.PolAV (Sp K)} {AA : Over (Sp (𝓞 K))} [GrpObj AA]
    {φ : P.A.left ⟶ AA.left} {MM : RigLB AA} {N : ℕ} (w : LB.Iso (MM.L.pull φ) (lbPow P.L N))
    (i₀ : (lbPow P.L N).ι) : K :=
  if h : ∃ p : PUnit → MM.L.ι,
      ⊤ ≤ (spMap (algebraMap (𝓞 K) K)) ⁻¹ᵁ (show (Sp (𝓞 K)).Opens from (MM.L.pull (eSec AA)).U p) then
    valR (X := P.A.left) (eSec P.A) _ (w.s (i₀, h.choose)).val *
      valR (X := Sp (𝓞 K)) (spMap (algebraMap (𝓞 K) K)) _ (MM.rig.s h.choose).val
  else 0

end GlobalTheory.SecJet
