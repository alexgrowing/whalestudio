import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchedSupportCompletions
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.UltraDefs
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsWeaklyRegularIffIsQuasiRegularSeqOfIsLocalRing

noncomputable section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools
open scoped TensorProduct

namespace UpperTheory.V.Pa.Core

structure IsYCpl {R σ : Type} [CommRing R] (y : σ → R) (f : R) (BB : Type) [CommRing BB] [Algebra R BB] : Prop where
  noeth : IsNoetherianRing BB
  unit : IsUnit (algebraMap R BB f)
  dense : ∀ (n : ℕ) (x : BB), ∃ (k : ℕ) (r : R),
    algebraMap R BB f ^ k * x - algebraMap R BB r ∈ (Ideal.span (Set.range y) ^ n).map (algebraMap R BB)
  strict : ∀ (n : ℕ) (r : R), algebraMap R BB r ∈ (Ideal.span (Set.range y) ^ n).map (algebraMap R BB) →
    ∃ k : ℕ, f ^ k * r ∈ Ideal.span (Set.range y) ^ n

structure PMod {R σ : Type} [CommRing R] [Fintype σ] (y : σ → R) (f : R) (ii : Ideal R)
    (X : Type) [AddCommGroup X] [Module R X] : Type 1 where
  BB : Type
  [ring : CommRing BB]
  [alg : Algebra R BB]
  cpl : IsYCpl y f BB
  MM : Type
  [add : AddCommGroup MM]
  [mod : Module BB MM]
  fin : Module.Finite BB MM
  qr : GlobalTheory.IsQuasiRegularSeq MM fun a => algebraMap R BB (y a)
  fib : (MM ⧸ (Ideal.span (Set.range fun a => algebraMap R BB (y a)) • ⊤ : Submodule BB MM)) ≃ₗ[BB] BB ⊗[R] X
  nil : ii ≤ (Module.annihilator BB MM).radical.comap (algebraMap R BB)

attribute [instance] PMod.ring PMod.alg PMod.add PMod.mod

variable {l : ℕ} [Fact l.Prime] {L : Loc} {G0 : Glob l L} {T : TWGrp G0} (Λ : Lim T)

abbrev Ph0 : Subgroup Λ.Ph := (Λ.G.η.comp Λ.πo).ker

def πo0 : Ph0 Λ →* Λ.G.G₀ := (Λ.πo.comp (Ph0 Λ).subtype).codRestrict _ fun g => g.2

def πN0 (N : ℕ) : Ph0 Λ →* (T.GN N).G₀ :=
  ((Λ.π N).comp (Ph0 Λ).subtype).codRestrict _ fun g => by
    have h1 := T.H_η _ (Λ.modH N g)
    have h2 : Λ.G.η (Λ.πo g) = 1 := g.2
    rw [map_mul, map_inv, (T.h N).η, Λ.h.η, h2, inv_one, mul_one] at h1
    exact h1

variable {n : ℕ} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {r : Resid G0.frame O n}
  {B : Type} [CommRing B] [Algebra O B] [IsCO O B] {u : Pair r B} {J : Ideal B} {D : ℕ} (A : TWAut u J Unit D T)

structure Tup (R : Type) [CommRing R] [Algebra O R] [IsCO O R] : Type 1 where
  D : GDet n R (Ph0 Λ)
  cont : D.IsCont (maximalIdeal R)
  red : D.map (res O R : R →+* ResidueField O) = r.Dbar.comap (Λ.h.p₀.comp (πo0 Λ))
  ψ : ∀ v, Fin n → L.Gv v →* Rˣ
  psi : ∀ v i, r.IsPsi v i (ψ v i)
  s : R
  s_mem : s ∈ maximalIdeal R
  U : Fin T.q → Fin n → R
  U_mem : ∀ j i, U j i - algebraMap O R (A.ut j i) ∈ maximalIdeal R
  y : Fin T.q → Fin n → R
  y_mem : ∀ j i, y j i ∈ maximalIdeal R

variable {Λ A} in

def Tup.Maps {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing R'] (t : Tup Λ A R) (f : R →+* R')
    (D' : GDet n R' (Ph0 Λ)) (ψ' : ∀ v, Fin n → L.Gv v →* R'ˣ) (s' : R') (U' y' : Fin T.q → Fin n → R') : Prop :=
  t.D.map f = D' ∧ (∀ v i, pushCh f (t.ψ v i) = ψ' v i) ∧ f t.s = s' ∧ (∀ j i, f (t.U j i) = U' j i) ∧
    ∀ j i, f (t.y j i) = y' j i

structure RRObj : Type 1 where
  R : Type
  [ring : CommRing R]
  [alg : Algebra O R]
  [co : IsCO O R]
  t : Tup Λ A R
  univ : ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (t' : Tup Λ A R'),
    ∃! f : R →ₐ[O] R', t.Maps f.toRingHom t'.D t'.ψ t'.s t'.U t'.y

attribute [instance] RRObj.ring RRObj.alg RRObj.co

variable {Λ A} (W : RRObj Λ A)

abbrev Spo (A : TWAut u J Unit D T) : Type := SpAt u T.sg A.ut

structure RMaps where
  s : Sinf O Unit D T.q n →ₐ[O] W.R
  s_X_unit : s (MvPowerSeries.C (MvPowerSeries.X (.inl ()))) = W.t.s
  s_w : ∀ k, s (MvPowerSeries.C (MvPowerSeries.X (.inr k))) =
    algebraMap O W.R (A.b.wt.c k) * (W.t.ψ (A.b.wt.v k) (A.b.wt.i k) (A.b.wt.γ k) : W.R) - 1
  s_y : ∀ j i, s (MvPowerSeries.X (j, i)) = W.t.y j i
  ρ : ∀ N, W.R →ₐ[O] (A.A N).R
  ρ_maps : ∀ N, W.t.Maps (ρ N).toRingHom ((A.A N).p.D.comap (πN0 Λ N)) (A.A N).p.ψ
    ((A.A N).s (MvPowerSeries.C (MvPowerSeries.X (.inl ())))) (A.A N).U fun j i => (A.A N).s (MvPowerSeries.X (j, i))
  specializationMap_comp_universalSection : ∀ N z, ρ N (s z) = (A.A N).s z
  π : W.R →ₐ[O] Spo A
  π_maps : W.t.Maps π.toRingHom ((u.D.comap (Λ.h.p₀.comp (πo0 Λ))).map (algebraMap B (Spo A)))
    (fun v i => pushCh (algebraMap B (Spo A)) (u.ψ v i)) (algebraMap B (Spo A) (A.b.lam (MvPowerSeries.X (.inl ()))))
    (fun j i => Sp.u _ _ j i) fun _ _ => 0
  π_s : ∀ z, π (s z) = algebraMap B (Spo A) (A.b.lam (MvPowerSeries.constantCoeff z))

inductive Rel : W.R → Prop
  | ker (h k : Ph0 Λ) : πo0 Λ k = 1 → Rel (W.t.D.tr (MonoidAlgebra.single h 1 * (MonoidAlgebra.single k 1 - 1)))
  | pol (i : ℕ) (g g' : Ph0 Λ) : (g' : Λ.Ph) = Λ.ct * g * Λ.ct⁻¹ →
      Rel (W.t.D.lam i (MonoidAlgebra.single g'⁻¹ ((Λ.G.frame.eps O W.R (πo0 Λ g) ^ (1 - (n : ℤ)) : W.Rˣ) : W.R)) -
        W.t.D.lam i (MonoidAlgebra.single g 1))
  | ord (v : L.Vl) (g : Fin n → L.Gv v) (ga : Fin n → Ph0 Λ) (h : Ph0 Λ) : (∀ i, πo0 Λ (ga i) = Λ.G.φ v (g i)) →
      Rel (W.t.D.tr (MonoidAlgebra.single h 1 * (List.ofFn fun i => MonoidAlgebra.single (ga i) (1 : W.R) -
        MonoidAlgebra.single 1 ((W.t.ψ v i (g i) : W.Rˣ) : W.R)).prod))
  | ine (w : L.St) (g : L.Gu w) (ga h : Ph0 Λ) : g ∈ L.Ju w → πo0 Λ ga = Λ.G.φu w g →
      Rel (W.t.D.tr (MonoidAlgebra.single h 1 * (MonoidAlgebra.single ga 1 - 1)))
  | q1 (j : Fin T.q) (ph h : Ph0 Λ) : πo0 Λ ph = Λ.ph j →
      Rel (W.t.D.tr (MonoidAlgebra.single h 1 * q1El ph (W.t.U j)))
  | q2 (j : Fin T.q) (i : Fin n) (ph ta h : Ph0 Λ) : πo0 Λ ph = Λ.ph j → πo0 Λ ta = Λ.ta j →
      Rel (W.t.D.tr (MonoidAlgebra.single h 1 * q2El ph ta (W.t.U j) i (W.t.y j i)))

def ii : Ideal W.R := Ideal.span {a | Rel W a}

def fo : W.R := fEl (fun _ => 1) W.t.U

variable {W} (m : RMaps W)

def MN (_m : RMaps W) (N : ℕ) : Type := (A.A N).M

instance (N : ℕ) : AddCommGroup (MN m N) := inferInstanceAs (AddCommGroup (A.A N).M)
instance (N : ℕ) : Module (A.A N).R (MN m N) := inferInstanceAs (Module (A.A N).R (A.A N).M)
instance (N : ℕ) : Module W.R (MN m N) := Module.compHom (MN m N) (m.ρ N).toRingHom

theorem MN.smul_def (N : ℕ) (a : W.R) (x : MN m N) : a • x = m.ρ N a • x := rfl

def X0 (_m : RMaps W) : Type := Spo A ⊗[B] A.b.M

instance : AddCommGroup (X0 m) := inferInstanceAs (AddCommGroup (Spo A ⊗[B] A.b.M))
instance : Module (Spo A) (X0 m) := inferInstanceAs (Module (Spo A) (Spo A ⊗[B] A.b.M))
instance : Module W.R (X0 m) := Module.compHom (X0 m) m.π.toRingHom
instance : Module (abelian₂ O Unit D) (X0 m) := Module.compHom (X0 m) ((algebraMap B (Spo A)).comp A.b.lam.toRingHom)

theorem X0.smul_def (a : W.R) (x : X0 m) : a • x = m.π a • x := rfl
theorem X0.lam_smul_def (a : abelian₂ O Unit D) (x : X0 m) : a • x = algebraMap B (Spo A) (A.b.lam a) • x := rfl

def IsApproximateAnnihilatorAtLevels (a : W.R) : Prop :=
  ∀ j : ℕ, ∀ᶠ N in Λ.U, ∃ b : W.R, (fo W * a) ^ (A.ex + 1) - b ∈ maximalIdeal W.R ^ j ∧ ∀ x : MN m N, b • x = 0

structure OoPair (W : RRObj Λ A) [IsCO O (W.R ⧸ ii W)] : Type 1 where
  r' : Resid Λ.G.frame O n
  compat : Glob.Compat Λ.h r' r
  p : Pair r' (W.R ⧸ ii W)
  D_eq : p.D.comap (πo0 Λ) = W.t.D.map (Ideal.Quotient.mk (ii W))
  ψ_eq : ∀ v i, p.ψ v i = pushCh (Ideal.Quotient.mk (ii W)) (W.t.ψ v i)

def ooKer {W : RRObj Λ A} [IsCO O (W.R ⧸ ii W)] (o : OoPair W) : Set (MonoidAlgebra (W.R ⧸ ii W) Λ.G.G₀) :=
  {z | z ∈ o.p.D.chBar (pairGens o.p ∪ qGens (O := O) (F := Λ.G.frame) Λ.ph Λ.ta
    (fun j i => Ideal.Quotient.mk (ii W) (W.t.U j i)) fun j i => Ideal.Quotient.mk (ii W) (W.t.y j i))}

def Sees {R G : Type} [CommRing R] [Group G] (D : GDet n R G) (V : Subgroup G) [V.Normal] (I : Ideal R) : Prop :=
  ∀ (i : ℕ) (x y : MonoidAlgebra R G), MonoidAlgebra.mapDomainRingHom R (QuotientGroup.mk' V) x =
    MonoidAlgebra.mapDomainRingHom R (QuotientGroup.mk' V) y → D.lam i x - D.lam i y ∈ I

end UpperTheory.V.Pa.Core
