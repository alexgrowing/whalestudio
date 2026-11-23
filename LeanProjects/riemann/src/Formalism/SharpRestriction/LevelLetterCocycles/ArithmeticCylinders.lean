import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut

noncomputable section

namespace Formalism.MainNotions.ArithmeticCylinders

open Formalism.BasicNotions Formalism.MainNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Filter Topology
open scoped ComplexOrder

def Conclusion2 (D : D7) (C c o : ℝ) : Prop :=
  D.what₂.delp ≤ C * ((∑ i : Fin 2, (D.R.f : ℝ) * (D.R.r : ℝ) ^ 5 * Real.log (D.host.g i) *
        (D.host.g i : ℝ) ^ (-(1 / 2 : ℝ))) +
      (D.R.f : ℝ) * D.R.m / ((min D.host.q D.host.d : ℕ) : ℝ) +
      (D.R.r : ℝ) * (7 / 8 + o) ^ D.R.f +
      Real.exp (-(c * D.R.f / Real.log D.R.r)))

def ExpDeficitBound (D : D7) (x eps : ℝ) : Prop :=
  D.what₂.delp ≤ Real.exp (-(x ^ (eps / 7)))

def br2 (D : D7) (c o : ℝ) : ℝ :=
  (∑ i : Fin 2, (D.R.f : ℝ) * (D.R.r : ℝ) ^ 5 * Real.log (D.host.g i) *
      (D.host.g i : ℝ) ^ (-(1 / 2 : ℝ))) +
    (D.R.f : ℝ) * D.R.m / ((min D.host.q D.host.d : ℕ) : ℝ) +
    (D.R.r : ℝ) * (7 / 8 + o) ^ D.R.f +
    Real.exp (-(c * D.R.f / Real.log D.R.r))

def eigSp {O K V X : Type} [CommRing O] [Field K] [Algebra O K] [AddCommGroup V] [Module K V]
    [Module O V] [IsScalarTower O K V] (T : Subalgebra O (X → O)) (act : T →ₐ[O] (V →ₗ[K] V)) (π : X) : Submodule K V where
  carrier := {v | ∀ t : T, act t v = algebraMap O K ((t : X → O) π) • v}
  add_mem' := fun {a b} ha hb t => by
    rw [map_add, ha t, hb t, smul_add]
  zero_mem' := fun t => by
    rw [map_zero, smul_zero]
  smul_mem' := fun c v hv t => by
    rw [map_smul, hv t, smul_comm]

def Conclusion5 (_D : D7) : Prop :=
  ∀ (O K V X : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    [FiniteDimensional K V] [Fintype X] [DecidableEq X]
    (T : Subalgebra O (X → O)) (act : T →ₐ[O] (V →ₗ[K] V)) (M : Submodule O V)
    (Z Zg : Finset X) (prZ e₀ : V →ₗ[K] V) (nG : ℕ),
    IsLocalRing T →
    (∀ x y : X, x ≠ y → ∃ t : T, (t : X → O) x ≠ (t : X → O) y) →
    M.FG → Submodule.span K (M : Set V) = ⊤ →
    (∀ t : T, ∀ m ∈ M, act t m ∈ M) →
    (⨆ π, eigSp T act π) = ⊤ →
    (∀ π ∈ Z, ∀ v ∈ eigSp T act π, prZ v = v) →
    (∀ π, π ∉ Z → ∀ v ∈ eigSp T act π, prZ v = 0) →
    Zg ⊆ Z →
    e₀ ∘ₗ e₀ = e₀ → (∀ t : T, e₀ ∘ₗ act t = act t ∘ₗ e₀) →
    (nG : O) ≠ 0 → (∀ m ∈ M, (nG : O) • e₀ m ∈ M) →
    (∀ π ∈ Zg, ∀ v ∈ eigSp T act π, e₀ v = v) →
    (∀ π ∈ Z, π ∉ Zg → ∀ v ∈ eigSp T act π, e₀ v = 0) →
    let MZ : Submodule O V := M.map (prZ.restrictScalars O)
    let VZ : Submodule K V := ⨆ π ∈ Z, eigSp T act π
    let MatZ : Submodule O V := M ⊓ VZ.restrictScalars O
    let VZg : Submodule K V := ⨆ π ∈ Zg, eigSp T act π
    let MatZg : Submodule O V := M ⊓ VZg.restrictScalars O
    let L : Submodule O V := MZ.map (e₀.restrictScalars O)
    let ccAt : X → Ideal O := fun π =>
      Ideal.span {a | ∃ t : T, (∀ y ∈ MZ, act t y ∈ MatZ) ∧ a = (t : X → O) π}
    Module.length O (↥L ⧸ MatZg.comap L.subtype) ≤
      ∑ π ∈ Zg, (Module.finrank K (eigSp T act π) : ℕ∞) *
        (Module.length O (O ⧸ ccAt π) + Module.length O (O ⧸ Ideal.span {(nG : O)}))

def Conclusion6 (_D : D7) : Prop :=
  ∀ (n : ℕ) (Q Pi : Matrix (Fin n) (Fin n) ℂ) (δ Dstar η s : ℝ),
    Q.PosSemidef → Pi.IsHermitian → Pi * Pi = Pi → 0 ≤ δ → 2 * δ < 1 → 0 < Dstar →
    (Pi.rank : ℝ) ≤ δ * Dstar → (n : ℝ) ≤ (1 + s) * Dstar → η ≤ 1 →
    (Q * Q).trace.re ≤ (1 + η) * (Q.trace.re) ^ 2 / Dstar →
    let Q₀ := (1 - Pi) * Q * (1 - Pi)
    ((Q₀ * Q₀).trace.re ≤ (1 + η) * (1 + s) / (1 - Real.sqrt (2 * δ)) ^ 2 *
        (Q₀.trace.re) ^ 2 / ((1 - Pi).rank : ℝ)) ∧
      (1 - Real.sqrt (2 * δ)) * Q.trace.re ≤ Q₀.trace.re ∧
      (Q₀ * Q₀).trace.re ≤ (Q * Q).trace.re ∧
      ∀ (m : ℕ) (B : Matrix (Fin n) (Fin m) ℂ) (Kk : Matrix (Fin m) (Fin m) ℂ) (c : ℝ), 0 ≤ c →
        (Kk - (c : ℂ) • (B.conjTranspose * B)).PosSemidef →
        (Kk - (c : ℂ) • (B.conjTranspose * (1 - Pi) * B)).PosSemidef

variable (D : D7)

def admissiblePrimesDyadic (Y : ℝ) : ℕ :=
  Nat.card {p : ℕ // D.ntypes.admissible p ∧ Y ≤ p ∧ (p : ℝ) ≤ 2 * Y}

def MrayRay (a : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime →
    (∃ π : 𝓞 D.host.E, (π : D.host.E) ∈ D.host.K ∧
      (π : D.host.E) * D.host.conj (π : D.host.E) = (p : D.host.E) ∧
      (π - 1) ∈ Ideal.span {((D.ntypes.cond ^ a : ℕ) : 𝓞 D.host.E)}) →
    (placesOver D.ntypes.Mray p).ncard = Module.finrank ℚ D.ntypes.Mray

def admissiblePrimesLE (X : ℝ) : ℕ :=
  Nat.card {p : ℕ // D.ntypes.admissible p ∧ (p : ℝ) ≤ X}

def adm2 (c₀ c₂ : ℝ) : Prop :=
  MrayRay D 1 → c₂ ≤ (D.host.d : ℝ) →
  ∀ X : ℝ, (D.ntypes.cond : ℝ) ^ 1737 ≤ X →
    c₀ / 2 * ((4 * (D.ntypes.cond : ℝ) ^ 3) ^ 5)⁻¹ * X / ((D.ntypes.cond : ℝ) ^ 3 * Real.log X) ≤
      (admissiblePrimesLE D X : ℝ)

def Conclusion1 (c₁ : ℝ) : Prop :=
  ∀ X : ℝ, 0 < X → c₁ ≤ (D.ntypes.cond : ℝ) → c₁ ≤ (D.host.d : ℝ) → 21 ≤ D.R.r →
    (D.R.r : ℝ) ^ 4 * (D.ntypes.cond : ℝ) ^ 500 ≤ (X * (D.ntypes.cond : ℝ) ^ (-(20 : ℝ))) ^ (1 / 4 : ℝ) →
    Real.log X ≤ (D.ntypes.cond : ℝ) →
    ∃ Y : ℝ, X * (D.ntypes.cond : ℝ) ^ (-(20 : ℝ)) ≤ Y ∧ Y ≤ X / 2 ∧
      (∃ g₁ g₂ : ℕ, D.ntypes.admissible g₁ ∧ D.ntypes.admissible g₂ ∧
        Y ≤ g₁ ∧ (g₁ : ℝ) ≤ 2 * Y ∧ Y ≤ g₂ ∧ (g₂ : ℝ) ≤ 2 * Y ∧
        g₁ ≠ g₂ ∧ Disjoint (Formalism.CyclotomicNorms.BB D.R.r g₁) (Formalism.CyclotomicNorms.BB D.R.r g₂)) ∧
      Y * (D.ntypes.cond : ℝ) ^ (-(20 : ℝ)) ≤ (admissiblePrimesDyadic D Y : ℝ)

def TwoPrimes (k b C : ℝ) : Prop :=
  ∃ Y : ℝ, (k * b) ^ 8 ≤ Y ∧ (D.R.r : ℝ) ^ 4 * (D.ntypes.cond : ℝ) ^ C ≤ Y ^ (1 / 4 : ℝ) ∧ 2 * Y ≤ b ^ 9 ∧
    ∃ g₁ g₂ : ℕ, D.ntypes.admissible g₁ ∧ D.ntypes.admissible g₂ ∧
      Y ≤ g₁ ∧ (g₁ : ℝ) ≤ 2 * Y ∧ Y ≤ g₂ ∧ (g₂ : ℝ) ≤ 2 * Y ∧
      g₁ ≠ g₂ ∧ Disjoint (Formalism.CyclotomicNorms.BB D.R.r g₁) (Formalism.CyclotomicNorms.BB D.R.r g₂)

def PointsLemma : Prop :=
  Disjoint (Formalism.CyclotomicNorms.BB D.R.r (D.host.g 0)) (Formalism.CyclotomicNorms.BB D.R.r (D.host.g 1)) →
  ∀ σ : D.what₂.FT, D.nd.goodRow σ →
    (∀ (k : Fin 2) (v : D.nd.PlG k),
      Formalism.MainNotions.N.TameGen D.nd (D.nd.plOm.1 (D.naut.plGw k v)) (D.ntypes.tg k v)) →
    D.ntypes.cuspidal σ ∧ ∀ w : D.what₂.places.Pl,
      haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
      Formalism.CyclotomicNorms.IrredOn (D.ntypes.rbar σ w) ⊤ ∧
      (∀ k : Fin 2, D.what₂.places.resChar w ∉ Formalism.CyclotomicNorms.BB D.R.r (D.host.g k) →
        ∀ (Hs : Subgroup (G D.host.E D.nd.Om)) [Hs.Normal], IsOpen (Hs : Set (G D.host.E D.nd.Om)) →
          Group.IsSolvable (G D.host.E D.nd.Om ⧸ Hs) →
          (∀ u ∈ placesOver D.host.E (D.host.g k), Ine (F := D.host.E) (D.nd.plOm.1 u) ≤ Hs) →
          Formalism.CyclotomicNorms.IrredOn (D.ntypes.rbar σ w) Hs) ∧
      (∀ k : Fin 2, D.what₂.places.resChar w ≠ D.host.g k →
        haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
        ∀ (v : D.nd.PlG k) (j : Fin D.R.m) (u : (ZMod (D.host.g k))ˣ),
          u = D.nd.chiT k v j ∨ u = (D.nd.chiT k v j)⁻¹ →
          ¬ (Matrix.charpoly ((D.ntypes.rbar σ w (D.ntypes.tg k v) : GL (Fin D.R.r) _) :
              Matrix (Fin D.R.r) (Fin D.R.r) _)).IsRoot
            (D.ntypes.iota k v w (Formalism.CyclotomicNorms.primeToPart (D.what₂.places.resChar w)
              (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k))
                ((u : ZMod (D.host.g k)))))))

def TheoremThreePrime : Prop :=
  Disjoint (Formalism.CyclotomicNorms.BB D.R.r (D.host.g 0)) (Formalism.CyclotomicNorms.BB D.R.r (D.host.g 1)) →
  ∀ (i : D.nd.Loc) (Sig : List (Formalism.BasicNotions.Part D.naut.CG)),
    (∃ x, Formalism.MainNotions.N.HasParamX D.nd D.naut i x Sig) →
    (∀ (k : Fin 2) (v : D.nd.PlG k),
      (D.naut.items₂ k (D.naut.plGw k v) (Formalism.MainNotions.N.isoLoc D.nd D.naut Sig (D.naut.plGw k v))).natDegree =
        D.naut.lpDim (Formalism.MainNotions.N.isoLoc D.nd D.naut Sig (D.naut.plGw k v))) →
    Formalism.MainNotions.N.goodSig D.nd D.naut Sig →
    Formalism.MainNotions.N.IsCuspIso D.nd D.naut Sig ∧
    ∀ ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i), Formalism.MainNotions.N.IsRepOfSig D.nd D.naut i Sig ρ →
      Formalism.CyclotomicNorms.IrredOn (Formalism.MainNotions.N.mapRep ((D.naut.kFbar i).comp (IsLocalRing.residue (D.nd.O i))) ρ) ⊤ ∧
      (∀ k : Fin 2, D.nd.l i ∉ Formalism.CyclotomicNorms.BB D.R.r (D.host.g k) →
        ∀ (Hs : Subgroup (G D.host.E D.nd.Om)) [Hs.Normal], IsOpen (Hs : Set (G D.host.E D.nd.Om)) →
          Group.IsSolvable (G D.host.E D.nd.Om ⧸ Hs) →
          (∀ u ∈ placesOver D.host.E (D.host.g k), Ine (F := D.host.E) (D.nd.plOm.1 u) ≤ Hs) →
          Formalism.CyclotomicNorms.IrredOn (Formalism.MainNotions.N.mapRep ((D.naut.kFbar i).comp (IsLocalRing.residue (D.nd.O i))) ρ) Hs) ∧
      (∀ k : Fin 2, D.nd.l i ≠ D.host.g k → ∀ w ∈ placesOver D.host.E (D.host.g k),
        Formalism.MainNotions.N.TameGen D.nd (D.nd.plOm.1 w) (D.nd.gam0 i w) →
        ¬ (((Formalism.MainNotions.N.mapRep ((D.naut.kFbar i).comp (IsLocalRing.residue (D.nd.O i))) ρ (D.nd.gam0 i w) :
              GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) _).charpoly).IsRoot
          (D.naut.kFbar i (IsLocalRing.residue (D.nd.O i) (Formalism.MainNotions.N.chi1 D.nd i (D.nd.gam0 i w)))))

def atPlace (k : Fin 2) (v : D.nd.PlG k) (a : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k)))) :
    MonoidAlgebra ℂ (G0g D.nd) := by
  classical
  exact MonoidAlgebra.ofCoeff (Finsupp.mapDomain
    (fun h => Pi.mulSingle (M := fun kv : (Σ k : Fin 2, D.nd.PlG k) => GL (Fin D.R.r) (ZMod (D.host.g kv.1)))
      ⟨k, v⟩ h)
    a.coeff)

def Conclusion4 : Prop :=
  (∀ g : G0g D.nd, D.ntypes.e0.coeff g ∈ D.ntypes.Qchi) ∧
  (∀ g : G0g D.nd, IsIntegral ℤ ((Nat.card (G0g D.nd) : ℂ) * D.ntypes.e0.coeff g)) ∧
  (∀ a : MonoidAlgebra ℂ (G0g D.nd), D.ntypes.e0 * a = a * D.ntypes.e0) ∧
  (∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (G0g D.nd) V) (MM : AddSubgroup V),
    (∀ a : ℂ, IsIntegral ℤ a → ∀ x ∈ MM, a • x ∈ MM) → (∀ g, ∀ x ∈ MM, ρ g x ∈ MM) →
    let e := ρ.asAlgebraHom D.ntypes.e0
    let c : ℂ := (Nat.card (G0g D.nd) : ℂ)
    (∀ x ∈ MM, c • e x ∈ MM ∧ c • e x ∈ LinearMap.range e) ∧
    (∀ y ∈ MM, y ∈ LinearMap.range e → ∃ x ∈ MM, e x = y) ∧
    (∀ x ∈ MM, ∃ u ∈ MM, ∃ z ∈ MM, u ∈ LinearMap.range e ∧
      z ∈ LinearMap.range (LinearMap.id - e) ∧ c • x = u + z)) ∧
  (∀ μ j, 1 ≤ j → j ≤ D.R.m → ∀ σ' : D.ntypes.Par, ∀ F ∈ D.ntypes.MtPar μ j σ',
    (D.ntypes.goodPar σ' → D.ntypes.onMt μ j D.ntypes.e0 F = F) ∧
    (¬ D.ntypes.goodPar σ' → D.ntypes.onMt μ j D.ntypes.e0 F = 0)) ∧
  (∀ μ, ∀ σ' : D.ntypes.Par, ∀ F ∈ D.ntypes.AmbPar μ σ',
    (D.ntypes.goodPar σ' → D.ntypes.onAmb μ D.ntypes.e0 F = F) ∧
    (¬ D.ntypes.goodPar σ' → D.ntypes.onAmb μ D.ntypes.e0 F = 0))

def labAct (τ : ℂ ≃+* ℂ) (k : Fin 2) (f : (ZMod (D.host.g k))[X]) : (ZMod (D.host.g k))[X] :=
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  Classical.epsilon fun f' : (ZMod (D.host.g k))[X] => f'.Monic ∧
    Formalism.CyclotomicNorms.rootsBar f' = (Formalism.CyclotomicNorms.rootsBar f).map
      (fun x => Function.invFun (D.ntypes.teichC k) (τ (D.ntypes.teichC k x)))

def IsLabel (k : Fin 2) (f : (ZMod (D.host.g k))[X]) : Prop :=
  f.Monic ∧ f.natDegree = D.R.r ∧ f.coeff 0 ≠ 0

def dualLab (k : Fin 2) (f : (ZMod (D.host.g k))[X]) : (ZMod (D.host.g k))[X] :=
  Polynomial.C (f.coeff 0)⁻¹ * f.reverse

def adm3 : Prop :=
  (∀ (τ : ℂ ≃+* ℂ) (k : Fin 2) (f : (ZMod (D.host.g k))[X]), IsLabel D k f →
    (D.ntypes.eSer k f).coeff.mapRange τ (map_zero τ) = (D.ntypes.eSer k (labAct D τ k f)).coeff) ∧
  (∀ μ j, 1 ≤ j → j ≤ D.R.m →
    ∀ (σ' : D.ntypes.Par) (k : Fin 2) (v : D.nd.PlG k) (f : (ZMod (D.host.g k))[X]),
    ∀ F ∈ D.ntypes.MtPar μ j σ',
      D.ntypes.onMt μ j (atPlace D k v (D.ntypes.eSer k f)) F ≠ 0 → f = D.ntypes.labPar k σ' v) ∧
  (∀ μ (σ' : D.ntypes.Par) (k : Fin 2) (v : D.nd.PlG k) (f : (ZMod (D.host.g k))[X]),
    ∀ F ∈ D.ntypes.AmbPar μ σ',
      D.ntypes.onAmb μ (atPlace D k v (D.ntypes.eSer k f)) F ≠ 0 → f = dualLab D k (D.ntypes.labPar k σ' v))

def ArchimedeanSignatureMatching : Prop :=
  ∀ (σ : D.what₂.FT) (k : Fin 2) (v : D.nd.PlG k),
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    (∃ L : List (ℕ × ℕ × Multiset (Formalism.CyclotomicNorms.Fbar (D.host.g k))),
      (L.map fun p => (p.1, p.2.1) : Multiset (ℕ × ℕ)) = D.ntypes.bc σ ∧
      (∀ p ∈ L, Multiset.card p.2.2 = p.1 ∧ p.2.2.map (fun x => x ^ D.host.g k) = p.2.2) ∧
      Formalism.CyclotomicNorms.rootsBar (D.nd.lab k σ v) = (L.map fun p => p.2.1 • p.2.2).sum) ∧
    (D.ntypes.cuspidal σ →
      Formalism.MainNotions.N.TameGen D.nd (D.nd.plOm.1 (D.naut.plGw k v)) (D.ntypes.tg k v) →
      ∀ w : D.what₂.places.Pl, D.what₂.places.resChar w ≠ D.host.g k →
      haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
      Matrix.charpoly ((D.ntypes.rbar σ w (D.ntypes.tg k v) : GL (Fin D.R.r) _) :
          Matrix (Fin D.R.r) (Fin D.R.r) _) =
        ((Formalism.CyclotomicNorms.rootsBar (D.nd.lab k σ v)).map fun x =>
          X - C (D.ntypes.iota k v w (Formalism.CyclotomicNorms.primeToPart (D.what₂.places.resChar w) x))).prod ∧
      ∃ φ : G D.host.E D.nd.Om,
        D.ntypes.rbar σ w (φ * D.ntypes.tg k v * φ⁻¹) = D.ntypes.rbar σ w (D.ntypes.tg k v) ^ D.host.g k)

abbrev Tup (k : Fin 2) : Type := D.nd.PlG k → (ZMod (D.host.g k))[X]

abbrev Tup2 : Type := ∀ k : Fin 2, D.nd.PlG k → (ZMod (D.host.g k))[X]

def cyl (k : Fin 2) (S : Set (Tup D k)) : Set (Tup2 D) := {t | t k ∈ S}

def wtOf (k : Fin 2) (a : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k))))
    (f : (ZMod (D.host.g k))[X]) : ℝ :=
  ((a * D.ntypes.eSer k f).coeff 1).re / (a.coeff 1).re

structure AllRows (D : D7) : Type 1 where
  B : Formalism.MainNotions.S.RowsAut
  n_eq : B.I.n = D.R.r
  f_eq : B.I.f = D.R.f
  labAll : ∀ k, Fin D.what₂.Dall → D.nd.PlG k → (ZMod (D.host.g k))[X]
  labAll_label : ∀ k σ v, IsLabel D k (labAll k σ v)
  inc : Fin D.what₂.Drows → Fin D.what₂.Dall
  eVec : ∀ k, D.nd.PlG k → MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k)))
  eVec_idem : ∀ k v, eVec k v * eVec k v = eVec k v
  eT : Set (Tup2 D) → B.I.Gf → ℂ
  ReT : Set (Tup2 D) → (B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund)
  ReT_spec : ∀ S, B.I.IsRConvF B.μf B.fund B.R (eT S) (ReT S)
  eT_univ : eT Set.univ = B.e
  ReT_univ : ReT Set.univ = B.Re
  eT_one : ∀ (k : Fin 2) (S : Finset (Tup D k)),
    (eT (cyl D k (S : Set (Tup D k))) 1).re =
      (B.e 1).re * ∑ t ∈ S, ∏ v, wtOf D k (eVec k v) (t v)

variable {D}

def AllRows.dimT (A : AllRows D) (S : Set (Tup2 D)) : ℕ :=
  A.B.I.Dcount A.B.σs A.B.μf A.B.fund A.B.R (A.ReT S)

def DimEqTotalCount (A : AllRows D) : Prop := D.what₂.Dall = A.B.D

def DimEqGoodCount (A : AllRows D) : Prop := D.what₂.Drows = A.dimT {t | D.ntypes.goodTuple t}

def LabelCountGoodInjective (A : AllRows D) : Prop :=
  (∀ S : Set (Tup2 D), A.dimT S = Nat.card {τ : Fin D.what₂.Dall // (fun k => A.labAll k τ) ∈ S}) ∧
    Function.Injective A.inc ∧ (∀ k σ, A.labAll k (A.inc σ) = D.nd.lab k (D.what₂.ft σ)) ∧
    ∀ τ : Fin D.what₂.Dall, D.ntypes.goodTuple (fun k => A.labAll k τ) ↔ τ ∈ Set.range A.inc

variable (D)

def TieAdmG : Prop := ∀ k, D.ntypes.admissible (D.host.g k)

abbrev VecAt : Type :=
  ∀ k : Fin 2, D.nd.PlG k → MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k)))

def lawL (eV : VecAt D) (CL : ℝ) : Prop :=
  ∀ (k : Fin 2) (v : D.nd.PlG k),
    (∀ f, 0 ≤ wtOf D k (eV k v) f) ∧
    (∀ f, IsLabel D k f → Squarefree f →
      (1 - 1 / (D.host.g k : ℝ)) / (D.host.g k : ℝ) ^ D.R.r ≤ wtOf D k (eV k v) f ∧
      wtOf D k (eV k v) f ≤ (1 + CL * D.R.r / (D.host.g k : ℝ)) / (D.host.g k : ℝ) ^ D.R.r) ∧
    ∀ S : Finset (ZMod (D.host.g k))[X], (∀ f ∈ S, ¬ Squarefree f) →
      ∑ f ∈ S, wtOf D k (eV k v) f ≤ 3 / (D.host.g k : ℝ)

def entN {A : Type} [Zero A] {N : ℕ} (M : Matrix (Fin N) (Fin N) A) (a b : ℕ) : A :=
  if h : a < N ∧ b < N then M ⟨a, h.1⟩ ⟨b, h.2⟩ else 0

def IsUniUp {A : Type} [Zero A] [One A] {N : ℕ} (M : Matrix (Fin N) (Fin N) A) : Prop :=
  ∀ a b : Fin N, (b < a → M a b = 0) ∧ (a = b → M a b = 1)

def eDat (g N : ℕ) [NeZero g] (P : Matrix (Fin N) (Fin N) (ZMod g) → Prop)
    (φ : Matrix (Fin N) (Fin N) (ZMod g) → ZMod g) (ψ₀ : AddChar (ZMod g) ℂ) :
    MonoidAlgebra ℂ (GL (Fin N) (ZMod g)) := by
  classical
  exact ((Finset.univ.filter fun u : GL (Fin N) (ZMod g) => P (u : Matrix (Fin N) (Fin N) (ZMod g))).card : ℂ)⁻¹ •
    ∑ u ∈ Finset.univ.filter (fun u : GL (Fin N) (ZMod g) => P (u : Matrix (Fin N) (Fin N) (ZMod g))),
      MonoidAlgebra.single u (ψ₀ (φ (u : Matrix (Fin N) (Fin N) (ZMod g))))⁻¹

def eU (g N : ℕ) [NeZero g] (ψ₀ : AddChar (ZMod g) ℂ) : MonoidAlgebra ℂ (GL (Fin N) (ZMod g)) :=
  eDat g N IsUniUp (fun M => ∑ i ∈ Finset.range (N - 1), entN M i (i + 1)) ψ₀

def phiJ {g : ℕ} (kk s : ℕ) {N : ℕ} (M : Matrix (Fin N) (Fin N) (ZMod g)) : ZMod g :=
  (∑ i ∈ Finset.range (s - 1), entN M i (i + 1)) +
    (if 1 ≤ s then entN M (s - 1) (s + kk) + entN M (s + kk) (s + kk + 1) else 0) +
    (∑ i ∈ Finset.range (s - 1), entN M (s + kk + 1 + i) (s + kk + 2 + i)) +
    ∑ a ∈ Finset.range (kk - 1), entN M (s + a) (s + a + 1)

def eJ (g N : ℕ) [NeZero g] (kk s : ℕ) (ψ₀ : AddChar (ZMod g) ℂ) : MonoidAlgebra ℂ (GL (Fin N) (ZMod g)) :=
  eDat g N (fun M => IsUniUp M ∧ ∀ a, s ≤ a → a < s + kk → entN M a (s + kk) = 0) (phiJ kk s) ψ₀

def lawAt (k : Fin 2) (a : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k)))) (CL : ℝ) : Prop :=
  (∀ f, 0 ≤ wtOf D k a f) ∧
  (∀ f, IsLabel D k f → Squarefree f →
    (1 - 1 / (D.host.g k : ℝ)) / (D.host.g k : ℝ) ^ D.R.r ≤ wtOf D k a f ∧
    wtOf D k a f ≤ (1 + CL * D.R.r / (D.host.g k : ℝ)) / (D.host.g k : ℝ) ^ D.R.r) ∧
  ∀ S : Finset (ZMod (D.host.g k))[X], (∀ f ∈ S, ¬ Squarefree f) →
    ∑ f ∈ S, wtOf D k a f ≤ 3 / (D.host.g k : ℝ)

def eUk (k : Fin 2) (ψ₀ : AddChar (ZMod (D.host.g k)) ℂ) :
    MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k))) :=
  haveI : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩
  eU (D.host.g k) D.R.r ψ₀

def eJk (k : Fin 2) (ψ₀ : AddChar (ZMod (D.host.g k)) ℂ) :
    MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k))) :=
  haveI : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩
  eJ (D.host.g k) D.R.r D.R.k (D.R.m / 2 - 1) ψ₀

def ConclusionL : Prop :=
  ∀ (k : Fin 2) (ψ₀ : AddChar (ZMod (D.host.g k)) ℂ), ψ₀ ≠ 1 → 2 * D.R.r ≤ D.host.g k →
    lawAt D k (eUk D k ψ₀) 6 ∧ lawAt D k (eJk D k ψ₀) 6

def admLq : Prop :=
  ∀ (k : Fin 2) (ψ₀ : AddChar (ZMod (D.host.g k)) ℂ), ψ₀ ≠ 1 →
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    (∀ f, 0 ≤ wtOf D k (eUk D k ψ₀) f ∧ 0 ≤ wtOf D k (eJk D k ψ₀) f) ∧
    (∀ f, IsLabel D k f → Squarefree f →
      wtOf D k (eUk D k ψ₀) f =
        1 / ((UniqueFactorizationMonoid.normalizedFactors f).map
          (fun P => (D.host.g k : ℝ) ^ P.natDegree - 1)).prod) ∧
    (∀ f, IsLabel D k f → (1 - 1 / (D.host.g k : ℝ)) * wtOf D k (eUk D k ψ₀) f ≤ wtOf D k (eJk D k ψ₀) f) ∧
    (∀ f, IsLabel D k f → Squarefree f →
      wtOf D k (eJk D k ψ₀) f ≤
        (1 + 1 / (D.host.g k : ℝ)) ^ D.R.r * wtOf D k (eUk D k ψ₀) f)

def LiftingLemmasStatement : Prop := admLq D → ConclusionL D

def goodAt (k : Fin 2) (t : Tup D k) : Prop :=
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  Formalism.CyclotomicNorms.IsGood D.R.r (D.host.g k) t (D.nd.chiT k) ∧
    Formalism.CyclotomicNorms.IsGood D.R.r (D.host.g k) t (fun v j => (D.nd.chiT k v j)⁻¹)

def locShare (eV : VecAt D) (k : Fin 2) (S : Finset (Tup D k)) : ℝ :=
  ∑ t ∈ S, ∏ v, wtOf D k (eV k v) (t v)

def LocalShareBound (eV : VecAt D) (C c o : ℝ) : Prop :=
  ∀ (k : Fin 2) (S : Finset (Tup D k)), (∀ t ∈ S, ¬ goodAt D k t) →
    locShare D eV k S ≤ C * br2 D c o

def LocalShareExpBound (eV : VecAt D) (x eps : ℝ) : Prop :=
  ∀ (k : Fin 2) (S : Finset (Tup D k)), (∀ t ∈ S, ¬ goodAt D k t) →
    locShare D eV k S ≤ Real.exp (-(x ^ (eps / 7)))

variable {D}

def PlaceLawIdempotents (A : AllRows D) (CL : ℝ) : Prop := lawL D A.eVec CL

theorem place_law_of_statement (A : AllRows D) (hL : ConclusionL D) (hg : ∀ k, 2 * D.R.r ≤ D.host.g k)
    (hV : ∀ k v, ∃ ψ₀ : AddChar (ZMod (D.host.g k)) ℂ, ψ₀ ≠ 1 ∧
      (A.eVec k v = eUk D k ψ₀ ∨ A.eVec k v = eJk D k ψ₀)) :
    PlaceLawIdempotents A 6 := by
  intro k v
  obtain ⟨ψ₀, hψ, h | h⟩ := hV k v
  · have h1 := (hL k ψ₀ hψ (hg k)).1
    rw [h]
    exact h1
  · have h2 := (hL k ψ₀ hψ (hg k)).2
    rw [h]
    exact h2

variable (D)

def admitted (c₀ c₂ : ℝ) : Prop := MrayRay D 1 ∧ adm2 D c₀ c₂ ∧ adm3 D ∧ ArchimedeanSignatureMatching D

def Stmt (c₀ c₂ c₁ : ℝ) : Prop :=
  0 < c₀ → 2 ^ 14 / c₀ ≤ c₁ → c₂ ≤ c₁ →
    admitted D c₀ c₂ → Conclusion1 D c₁ ∧ PointsLemma D ∧ Conclusion4 D ∧ Conclusion5 D ∧ Conclusion6 D

end Formalism.MainNotions.ArithmeticCylinders
