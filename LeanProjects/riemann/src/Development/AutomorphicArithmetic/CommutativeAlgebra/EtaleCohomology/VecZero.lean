import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.TestFacts
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.IsFirstChernClassOfLineBundle
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.EtSide

set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison TensorProduct

namespace UpperTheory.Ru.crystallineComparison

open UpperTheory.Gal.crystallineComparison

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

variable (l) in

def tA : Acris l := ACris.periodT (untilt_epsilon (p := l))

variable (l) in

def phiA : Acris l →+* Acris l := ACris.phi ℂ_[l] l

def galA (g : K.fixingSubgroup) : Acris l →+* Acris l := ACris.galCris (IntermediateField.fixingSubgroupEquiv K g)

variable (l) in

def zA : ℤ_[l] →+* Acris l := (algebraMap (Ainf l) (Acris l)).comp (IsPerfectoidField.padicIntToWitt l)

structure PBg (l : ℕ) [Fact l.Prime] {A Γ : Type} [CommRing A] (t : A) (φA : A →+* A) (σA : Γ → (A →+* A)) (z : ℤ_[l] →+* A) : Type 1 where
  C : Type
  [ring : CommRing C]
  [alg : Algebra ℚ_[l] C]
  c : A →+* C
  φ : C →ₐ[ℚ_[l]] C
  σ : Γ → (C →ₐ[ℚ_[l]] C)
  t_unit : IsUnit (c t)
  loc : ∀ x : C, ∃ (r : ℕ) (a : A), c t ^ r * x = c a
  ker : ∀ a : A, c a = 0 → ∃ r : ℕ, t ^ r * a = 0
  φ_c : ∀ a, φ (c a) = c (φA a)
  σ_c : ∀ g a, σ g (c a) = c (σA g a)
  z_c : ∀ x : ℤ_[l], algebraMap ℚ_[l] C x = c (z x)

attribute [instance] PBg.ring PBg.alg

variable (l K) in

abbrev PB : Type 1 := PBg l (tA l) (phiA l) (galA (K := K)) (zA l)

variable (B : PB l K)

def IsInv (M : Model l K) (j : ℕ) (x : M.V j ⊗[ℚ_[l]] B.C) : Prop :=
  ∀ g : K.fixingSubgroup, TensorProduct.map (M.act j g) (B.σ g).toLinearMap x = x

def vec (M : Model l K) (j r : ℕ) {ι : Type} [Fintype ι] (v : ι → M.T j) (c : ι → Acris l) : M.V j ⊗[ℚ_[l]] B.C :=
  ∑ k, M.toV j (v k) ⊗ₜ (B.c (c k) * Ring.inverse (B.c (tA l)) ^ r)

def evE (e : E.EtFam l K) (M : Model l K) (j n : ℕ) {ι : Type} [Fintype ι] (v : ι → M.T j) (c : ι → Acris l) : M.MH n j :=
  ∑ k, c k • e M n j ((v k).lev n)

def InjE (e : E.EtFam l K) (M : Model l K) (j : ℕ) : Prop :=
  ∀ (ι : Type) [Fintype ι] (v : ι → M.T j) (c : ι → Acris l) (u : ℕ), (∀ n, tA l ^ u • evE e M j n v c = 0) → vec B M j 0 v c = 0

def AbsInv (e : E.EtFam l K) (M : Model l K) (j f : ℕ) (ϖ : OK l K) : Prop :=
  ∃ (m N : ℕ) (g : OK l K →+* Qo l) (F : PQ M.p g ⟶ PQ M.p g) (ρ : M.P ⟶ PQ M.p g), g ϖ = 0 ∧ (∀ x, g x ^ l ^ f = g x) ∧ IsFr f F ∧ IsRd m ρ ∧
    ∀ (ι : Type) [Fintype ι] (v : ι → M.T j) (c : ι → Acris l) (r : ℕ), IsInv B M j (vec B M j r v c) →
      ∃ (a u : ℕ) (x : ∀ n, MH (PQ M.p g) n j), ∀ n, (phiH _ n j)^[f] (x n) = pullH F n j (x n) ∧
        ((l : Acris l) ^ a * tA l ^ u) • evE e M j n v (fun k => (phiA l)^[f * N] (c k)) = tA l ^ (u + r) • pullH ρ n j (x n)

def IsHk (M : Model l K) (T : Corr l M.X) (hr : T.r ≫ M.p = T.p ≫ M.p) (j : ℕ) (A : M.V j →ₗ[ℚ_[l]] M.V j) : Prop :=
  ∀ (W : Model l K) (w : W.X ⟶ M.X) (hw : w ≫ M.p = W.p) (z : Fin T.d → (W.X ⟶ T.Z)) (hz : ∀ i, z i ≫ T.p = w),
    (∀ (X : Scheme.{0}) (y : X ⟶ W.X), IsUnit (l : Γ(X, ⊤)) → SplitOn T.p (y ≫ w) fun i => y ≫ z i) →
    ∀ v, Model.pullV w hw j (A v) =
      ∑ i, Model.pullV (z i ≫ T.r) (by rw [Category.assoc, hr, ← Category.assoc, hz, hw]) j v

def SiteAnn : Prop := ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] (Y : Scheme.{0}) (q : Y ⟶ Spec (CommRingCat.of O)) (g : O →+* Qo l)
  (Q P : PAlg l ⥤ Type) (ρ : P ⟶ PQ q g) (F : PQ q g ⟶ PQ q g) (f : ℕ) (I : Type) [Fintype I] (a : I → ℤ) (t : I → (Q ⟶ P)) (k : I → ℕ),
  (TZero a fun i => t i ≫ ρ ≫ itE F (k i)) → ∀ (n j : ℕ) (x : MH (PQ q g) n j), (phiH _ n j)^[f] x = pullH F n j x →
  ∑ i, a i • pullH (t i) n j ((phiH P n j)^[f * k i] (pullH ρ n j x)) = 0

def VecZero : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (B : PB l K) (e : E.EtFam l K), e.Good →
  ∀ (M : Model l K) (j : ℕ) (ι : Type) [Fintype ι] (v : ι → M.T j) (c : ι → Acris l) (r : ℕ), vec B M j r v c = 0 →
  ∃ a u : ℕ, ∀ n, ((l : Acris l) ^ a * tA l ^ u) • evE e M j n v c = 0

def Top : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [IsDomain (OK l K)] [IsDiscreteValuationRing (OK l K)]
  (ϖ : OK l K), Irreducible ϖ → ∀ (e : E.EtFam l K), e.Good → ∀ (M : Model l K), Smooth M.p → QuasiCompact M.p → AffFin M.X →
  ∀ (f n j : ℕ), 0 < f → ∀ (T : Fin (n + 1) → Corr l M.X) (hr : ∀ i, (T i).r ≫ M.p = (T i).p ≫ M.p), PtId l (l ^ f) n (fn M.p ϖ) T →
  ∀ A : Fin (n + 1) → (M.V j →ₗ[ℚ_[l]] M.V j), (∀ i, IsHk M (T i) (hr i) j (A i)) → ∀ B : PB l K, InjE B e M j → AbsInv B e M j f ϖ →
  ∃ N : ℕ, ∀ x, IsInv B M j x →
    ∑ i : Fin (n + 1), ((-1) ^ (i : ℕ) * ((l ^ f : ℕ) : ℤ) ^ ((i : ℕ).choose 2)) • TensorProduct.map (A i) (B.φ.toLinearMap ^ (f * (n - i + N))) x = 0

end UpperTheory.Ru.crystallineComparison
