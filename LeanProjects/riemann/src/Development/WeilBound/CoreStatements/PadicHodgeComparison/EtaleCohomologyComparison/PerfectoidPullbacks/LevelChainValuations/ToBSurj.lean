import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.DatPull
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

structure Lev (R : Per l K) (m : ℕ) where
  B : Type
  [bring : CommRing B]
  [balg : Algebra K B]
  toB : R.P →+* B
  IB : Ideal B
  γB : DividedPowers IB
  A : Type
  [aring : CommRing A]
  [aalg : Algebra (OK l K) A]
  I : Ideal A
  γ : DividedPowers I
  ι : A →+* B
  lam : R.A →+* A
  σA : K.fixingSubgroup → A →+* A
  σB : K.fixingSubgroup → B →+* B

attribute [instance] Lev.bring Lev.balg Lev.aring Lev.aalg

structure LevSys (R : Per l K) where
  L : ∀ m, Lev R (m + 1)
  dA : ∀ m, (L (m + 1)).A →+* (L m).A
  dB : ∀ m, (L (m + 1)).B →+* (L m).B

variable {R : Per l K}

structure Lev.Good {m : ℕ} (L : Lev R m) : Prop where
  pos : 1 ≤ m
  lat : ∀ s, m ≤ s → LatBase L.γ l s
  toB_surj : Function.Surjective L.toB
  toB_ker : ∀ x : R.P, L.toB x = 0 ↔ ∃ y : R.P, (x : R.B) = R.tB ^ m * y
  toB_K : ∀ (k : K) (y : R.P), (y : R.B) = R.o k → L.toB y = algebraMap K L.B k
  ι_inj : Function.Injective L.ι
  ι_dp : IsDPMorphism L.γ L.γB L.ι
  ι_I : L.I = L.IB.comap L.ι
  IB_eq : L.IB = L.I.map L.ι
  ι_O : ∀ a : OK l K, L.ι (algebraMap (OK l K) L.A a) = algebraMap K L.B (a : K)
  ι_lam : ∀ (c : R.A) (y : R.P), (y : R.B) = R.i c → L.ι (L.lam c) = L.toB y
  σB_toB : ∀ (g : K.fixingSubgroup) (x y : R.P), R.σ g x = y → L.σB g (L.toB x) = L.toB y
  σ_ι : ∀ g a, L.ι (L.σA g a) = L.σB g (L.ι a)
  σ_lam : ∀ g c, L.σA g (L.lam c) = L.lam (R.σA g c)
  σ_O : ∀ g (a : OK l K), L.σA g (algebraMap (OK l K) L.A a) = algebraMap (OK l K) L.A a
  σ_dp : ∀ g, IsDPMorphism L.γ L.γ (L.σA g)
  σB_dp : ∀ g, IsDPMorphism L.γB L.γB (L.σB g)
  σB_K : ∀ g (k : K), L.σB g (algebraMap K L.B k) = algebraMap K L.B k
  pdP_B : ∀ (r : ℕ) (t : R.P), (t : R.B) = R.tB → pdP L.γB r = Ideal.span {L.toB t ^ r}

structure LevSys.Good (S : LevSys R) : Prop where
  lev : ∀ m, (S.L m).Good
  dB_toB : ∀ m x, S.dB m ((S.L (m + 1)).toB x) = (S.L m).toB x
  dι : ∀ m a, S.dB m ((S.L (m + 1)).ι a) = (S.L m).ι (S.dA m a)
  dlam : ∀ m c, S.dA m ((S.L (m + 1)).lam c) = (S.L m).lam c
  dO : ∀ m (a : OK l K), S.dA m (algebraMap (OK l K) _ a) = algebraMap (OK l K) _ a
  dK : ∀ m (k : K), S.dB m (algebraMap K _ k) = algebraMap K _ k
  ddp : ∀ m, IsDPMorphism (S.L (m + 1)).γ (S.L m).γ (S.dA m)
  ddpB : ∀ m, IsDPMorphism (S.L (m + 1)).γB (S.L m).γB (S.dB m)
  dσ : ∀ m g a, S.dA m ((S.L (m + 1)).σA g a) = (S.L m).σA g (S.dA m a)
  dσB : ∀ m g b, S.dB m ((S.L (m + 1)).σB g b) = (S.L m).σB g (S.dB m b)
  cpl : ∀ y : ∀ m, (S.L m).B, (∀ m, S.dB m (y (m + 1)) = y m) → ∃! x : R.P, ∀ m, (S.L m).toB x = y m

end CrystallineSemistableComparison.Pb.Kap
