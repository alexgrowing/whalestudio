import Formalism.LocalToGlobal.LatticeGeometry.GeometryDefinitions.ClsSum
import Formalism.GradedWeylDivisibility.FinalD
import Formalism.RealPlaceAnalysis.FockPairGl
import Formalism.LocalRingCardinality.DataCoeff

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions MvPolynomial

namespace Formalism.L2.Geo.Def

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable instance ssFin (n : ℕ) (ν : Fin n → ℕ) : Fintype (Formalism.GradedWeylDivisibility.ssIdx n n ν) :=
  (Formalism.GradedWeylDivisibility.sSIdxFinite n n ν).fintype

def ssb (K : Type) [Field K] (n : ℕ) (ν : Fin n → ℕ) : Formalism.GradedWeylDivisibility.ssIdx n n ν → MvPolynomial (Fin n × Fin n) K :=
  (Formalism.GradedWeylDivisibility.sSBasis K n n ν).choose

def tenP {ι K : Type} [Fintype ι] [CommRing K] {n : ℕ} (f : ι → MvPolynomial (Fin n × Fin n) K) :
    MvPolynomial (ι × Fin n × Fin n) K :=
  ∏ τ, rename (Prod.mk τ) (f τ)

def nfD {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (p q : MvPolynomial (ι × Fin n × Fin n) ℂ) : ℂ :=
  Formalism.REAL.fockF p q / ∏ τ, Formalism.REAL.fockF (extremal ℂ n (lam τ)) (extremal ℂ n (lam τ))

variable (D : D7)

abbrev VarT : Type := D.what₂.Tau × Fin (nW D) × Fin (nW D)

def intLat (κ : D.what₂.Tau → DomWeight (nW D)) : Submodule (𝓞 D.what₂.LL) (MvPolynomial (VarT D) D.what₂.LL) :=
  Submodule.map (mapAlgHom (Algebra.ofId (𝓞 D.what₂.LL) D.what₂.LL)).toLinearMap
    (Formalism.GradedWeylDivisibility.tensorLat (𝓞 D.what₂.LL) (𝓞 D.what₂.LL) (fun τ => Formalism.GradedWeylDivisibility.dualWeyl (𝓞 D.what₂.LL) (nW D) (nW D) (κ τ).natW))

def twistB (B : D.what₂.Tau → GL (Fin (nW D)) D.what₂.LL) (e : D.what₂.Tau → ℤ) : D.what₂.LL :=
  ((∏ τ, (Matrix.GeneralLinearGroup.det (B τ)) ^ (e τ) : D.what₂.LLˣ) : D.what₂.LL)

def twAct (B : D.what₂.Tau → GL (Fin (nW D)) D.what₂.LL) (e : D.what₂.Tau → ℤ) :
    MvPolynomial (VarT D) D.what₂.LL →ₗ[𝓞 D.what₂.LL] MvPolynomial (VarT D) D.what₂.LL :=
  (twistB D B e • (Formalism.GradedWeylDivisibility.blockAct D.what₂.LL (fun τ => (B τ : Matrix (Fin (nW D)) (Fin (nW D)) D.what₂.LL))).toLinearMap).restrictScalars
    (𝓞 D.what₂.LL)

def LocEq (w : HeightOneSpectrum (𝓞 D.what₂.LL)) (A B : Submodule (𝓞 D.what₂.LL) (Fin (nW D) → D.what₂.LL)) : Prop :=
  Formalism.HermitianLatticesTheory.locS (@Ideal.primeCompl _ _ w.asIdeal w.isPrime) A = Formalism.HermitianLatticesTheory.locS (@Ideal.primeCompl _ _ w.asIdeal w.isPrime) B

def colSpan (B : GL (Fin (nW D)) D.what₂.LL) : Submodule (𝓞 D.what₂.LL) (Fin (nW D) → D.what₂.LL) :=
  Submodule.span (𝓞 D.what₂.LL) (Set.range fun t a => (B : Matrix (Fin (nW D)) (Fin (nW D)) D.what₂.LL) a t)

def FibLat (ell : D.what₂.Tau → HLat D.what₂.LL) (κ : D.what₂.Tau → DomWeight (nW D)) (c : XDef D) :
    Submodule (𝓞 D.what₂.LL) (MvPolynomial (VarT D) D.what₂.LL) :=
  ⨅ (w : HeightOneSpectrum (𝓞 D.what₂.LL)) (B : D.what₂.Tau → GL (Fin (nW D)) D.what₂.LL)
    (_ : ∀ τ, LocEq D w (TxLat D ell c τ) (colSpan D (B τ))),
    Submodule.comap (twAct D B (fun τ => (κ τ).detShift))
      (Formalism.HermitianLatticesTheory.locS (@Ideal.primeCompl _ _ w.asIdeal w.isPrime) (intLat D κ))

abbrev NNIdx (R : Finset (XDef D)) (κ : D.what₂.Tau → DomWeight (nW D)) : Type :=
  {c // c ∈ R} × (∀ τ, Formalism.GradedWeylDivisibility.ssIdx (nW D) (nW D) (κ τ).natW)

section NN

variable (ell : D.what₂.Tau → HLat D.what₂.LL) (κ : D.what₂.Tau → DomWeight (nW D)) (R : Finset (XDef D))

def bPoly (i : NNIdx D R κ) : MvPolynomial (VarT D) D.what₂.LL :=
  tenP (fun τ => ssb D.what₂.LL (nW D) (κ τ).natW (i.2 τ))

open Classical in

def polyAt (c : {c // c ∈ R}) : (NNIdx D R κ → D.what₂.LL) →ₗ[D.what₂.LL] MvPolynomial (VarT D) D.what₂.LL where
  toFun x := ∑ i : NNIdx D R κ, if i.1 = c then x i • bPoly D κ R i else 0
  map_add' x y := by simp only [Pi.add_apply, add_smul]; rw [← Finset.sum_add_distrib]; congr 1; funext i; split_ifs <;> simp
  map_smul' a x := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum]; congr 1; funext i; split_ifs <;> simp [mul_smul]

def NNLat : Submodule (𝓞 D.what₂.LL) (NNIdx D R κ → D.what₂.LL) :=
  ⨅ c : {c // c ∈ R}, Submodule.comap ((polyAt D κ R c).restrictScalars (𝓞 D.what₂.LL)) (FibLat D ell κ c.1)

def atFrame (v : InfinitePlace D.what₂.LL) (c : XDef D) (F : MvPolynomial (VarT D) D.what₂.LL) :
    MvPolynomial (VarT D) ℂ :=
  Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => (Tx D ell c τ).X v) (MvPolynomial.map v.embedding F)

def twAbs (v : InfinitePlace D.what₂.LL) (c : XDef D) : ℝ :=
  ∏ τ, ‖((Tx D ell c τ).X v).det‖ ^ (2 * (κ τ).detShift)

open Classical in

def gramNN (v : InfinitePlace D.what₂.LL) : Matrix (NNIdx D R κ) (NNIdx D R κ) ℂ := fun i i' =>
  if i.1 = i'.1 then
    (twAbs D ell κ v i.1.1 : ℂ) * nfD κ (atFrame D ell v i.1.1 (bPoly D κ R i')) (atFrame D ell v i.1.1 (bPoly D κ R i))
  else 0

open Classical in

def NNc : HLat D.what₂.LL where
  V := NNIdx D R κ → D.what₂.LL
  ι := NNIdx D R κ
  decι := Classical.decEq _
  b := Pi.basisFun D.what₂.LL (NNIdx D R κ)
  X := fun v => frameOf (gramNN D ell κ R v)
  L := NNLat D ell κ R

end NN

section Std

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def intStd (n : ℕ) (ν : Fin n → ℕ) : Submodule (𝓞 K) (MvPolynomial (Fin n × Fin n) K) :=
  Submodule.map (mapAlgHom (Algebra.ofId (𝓞 K) K)).toLinearMap (Formalism.GradedWeylDivisibility.dualWeyl (𝓞 K) n n ν)

def polyStd (n : ℕ) (ν : Fin n → ℕ) : (Formalism.GradedWeylDivisibility.ssIdx n n ν → K) →ₗ[K] MvPolynomial (Fin n × Fin n) K where
  toFun x := ∑ i, x i • ssb K n ν i
  map_add' x y := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a x := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, mul_smul]

def nabStd (n : ℕ) (lam : DomWeight n) : HLat K where
  V := Formalism.GradedWeylDivisibility.ssIdx n n lam.natW → K
  ι := Formalism.GradedWeylDivisibility.ssIdx n n lam.natW
  decι := Classical.decEq _
  b := Pi.basisFun K _
  X := fun v => frameOf (fun i i' =>
    nfD (fun _ : Unit => lam) (rename (Prod.mk ()) (MvPolynomial.map v.embedding (ssb K n lam.natW i')))
      (rename (Prod.mk ()) (MvPolynomial.map v.embedding (ssb K n lam.natW i))))
  L := Submodule.comap ((polyStd n lam.natW).restrictScalars (𝓞 K)) (intStd n lam.natW)

def mu0 (n : ℕ) (lam : DomWeight n) : ℝ := (nabStd (K := K) n lam).mu

end Std

end Formalism.L2.Geo.Def
