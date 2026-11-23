import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
import Formalism.LocalToGlobal.HeckeThetaElements.DefsWt

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Matrix IsDedekindDomain NumberField
open Formalism.L2.Theta
open scoped TensorProduct ContDiff InnerProductSpace

namespace Formalism.IndefR.Mult

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def dualPar (S : SPar) : SPar := S.image fun x => (-x.1, x.2)

variable (D : D7)

def tparHC (eta : D.what₂.Tau → ℚ) (h : ∀ τ, eta τ = 1 / 2 ∨ eta τ = -(1 / 2)) : TPar D where
  t := D.R.t
  t_odd := D.R.t_odd
  t_ge := D.R.rank_add_five_le
  u := fun τ => (D.hc τ).u
  v := fun τ => (D.hc τ).v
  b := fun τ => (D.hc τ).b
  e := fun τ => (D.hc τ).e
  eta := eta
  eta_half := h

variable {D}

def parA (P : TPar D) (j : ℕ) (τ : D.what₂.Tau) : SPar := P.Dpar j τ

def parB (P : TPar D) (j : ℕ) (τ : D.what₂.Tau) : SPar := dualPar (P.Dpar j τ)

def parW (W : HSp D) (κ : ∀ τ : D.what₂.Tau, Fin (W.sig (tauE D τ)).1 ⊕ Fin (W.sig (tauE D τ)).2 → ℤ)
    (τ : D.what₂.Tau) : SPar :=
  Formalism.L2.NTheta.holPar _ _ (κ τ)

def adWt (W : HSp D) (κgeo : ∀ τ : D.what₂.Tau, Fin (W.sig (tauE D τ)).1 ⊕ Fin (W.sig (tauE D τ)).2 → ℤ)
    (e : D.what₂.Tau → ℤ) : ∀ τ : D.what₂.Tau, Fin (W.sig (tauE D τ)).1 ⊕ Fin (W.sig (tauE D τ)).2 → ℤ :=
  fun τ a => κgeo τ a - e τ

def weylDimU {p : ℕ} (lam : Fin p → ℤ) : ℚ :=
  ∏ i : Fin p, ∏ j ∈ Finset.univ.filter (fun j : Fin p => i < j),
    (((lam i - lam j : ℤ) : ℚ) + ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) / (((j : ℕ) : ℚ) - ((i : ℕ) : ℚ))

def dimK (p q : ℕ) (κ : Fin p ⊕ Fin q → ℤ) : ℚ :=
  weylDimU (fun i => κ (Sum.inl i)) * weylDimU (fun i => κ (Sum.inr i))

structure DSModel (V : HSp D) (S : D.what₂.Tau → SPar) where
  H : D.what₂.Tau → Type
  [nacg : ∀ τ, NormedAddCommGroup (H τ)]
  [ips : ∀ τ, InnerProductSpace ℂ (H τ)]
  σ : ∀ τ, Matrix (Fin V.rank) (Fin V.rank) ℂ → (H τ →L[ℂ] H τ)
  lam : D.what₂.Tau → Fin V.rank → ℝ
  ε : D.what₂.Tau → Fin V.rank → Bool
  fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ
  enum : ∀ τ, IsEnum (S τ) (lam τ) (ε τ)
  ds : ∀ τ, IsDS (ε τ) (lam τ) (σ τ)
  fr_unit : ∀ τ, IsUnit (fr τ)
  fr_gram : ∀ τ, (fr τ)ᴴ * Formalism.REAL.Jm (ε τ) * fr τ = gramAt D V τ

attribute [instance] DSModel.nacg DSModel.ips

variable {V : HSp D} {S : D.what₂.Tau → SPar}

def DSModel.rep (M : DSModel V S) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) : M.H τ →L[ℂ] M.H τ :=
  M.σ τ (M.fr τ * g * (M.fr τ)⁻¹)

def DSModel.sm (M : DSModel V S) (τ : D.what₂.Tau) : Submodule ℂ (M.H τ) :=
  Submodule.span ℂ {w | SmoothVec (lieAt V τ) (M.rep τ) w}

abbrev DSModel.Vec (M : DSModel V S) : Type := ∀ τ : D.what₂.Tau, M.sm τ

abbrev MMap (M : DSModel V S) : Type := MultilinearMap ℂ (fun τ : D.what₂.Tau => M.sm τ) (GA D V → ℂ)

variable (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))

open Classical in

structure IsMultMap (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M) : Prop where
  aut : ∀ v, IsAutFunSm θ V (T v)
  cusp : ∀ v, IsCuspFun V (T v)
  lev : ∀ v, ∀ k ∈ J, ∀ g, T v (g * k) = χ k * T v g
  equiv : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ (v : M.Vec) (w : M.sm τ),
    (w : M.H τ) = M.rep τ g (v τ) → T (Function.update v τ w) = rTr V (atTau θ V τ g) (T v)
  cont : ∀ τ (v : M.Vec) (x : GA D V), ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ ∧
    ∀ w : M.sm τ, ℓ w = T (Function.update v τ w) x

def Mult (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) : Submodule ℂ (MMap M) :=
  Submodule.span ℂ {T | IsMultMap θ M J χ T}

def IsMultIP (M : DSModel V S) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (T T' : MMap M) (c : ℂ) : Prop :=
  ∀ v v' : M.Vec, IntegrableOn (fun g => star (T v g) * T' v' g) 𝓕 μ ∧
    ∫ g in 𝓕, star (T v g) * T' v' g ∂μ = c * ∏ τ, ⟪(v τ : M.H τ), (v' τ : M.H τ)⟫_ℂ

open Classical in

def ipM (M : DSModel V S) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (T T' : MMap M) : ℂ :=
  if h : ∃ c, IsMultIP M μ 𝓕 T T' c then h.choose else 0

def ipW {W : HSp D} {κ : ∀ τ : D.what₂.Tau, Fin (W.sig (tauE D τ)).1 ⊕ Fin (W.sig (tauE D τ)).2 → ℤ}
    (M : DSModel W (parW W κ)) (μ : Measure (GA D W)) (𝓕 : Set (GA D W)) (T T' : MMap M) : ℂ :=
  (∏ τ, ((dimK _ _ (κ τ) : ℚ) : ℂ)) * ipM M μ 𝓕 T T'

def postOn (M : DSModel V S) (L : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) : MMap M →ₗ[ℂ] MMap M where
  toFun T := L.compMultilinearMap T
  map_add' T T' := by ext v; simp
  map_smul' c T := by ext v; simp

def heckeLin (V : HSp D) (R : Finset (GA D V)) : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ) where
  toFun F := fun g => ∑ γ ∈ R, F (g * γ)
  map_add' F G := by funext g; simp [Finset.sum_add_distrib]
  map_smul' c F := by funext g; simp [Finset.mul_sum]

def locPart (V : HSp D) (K : Set (GA D V)) (e : Formalism.L2.Theta.AE D) : Set (GA D V) :=
  {k | k ∈ K ∧ Formalism.L2.Theta.SuppAt e V k}

variable (V) in

def IsCosetRep (K : Set (GA D V)) (α : GA D V) (R : Finset (GA D V)) : Prop :=
  (∀ γ ∈ R, γ ∈ GfC V ∧ ∃ k₁ ∈ K, ∃ k₂ ∈ K, γ = k₁ * α * k₂) ∧
    ∀ x : GA D V, (∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * α * k₂) → ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ K

variable (D) in

def OffS (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (P : HeightOneSpectrum (𝓞 D.host.E)) : Prop :=
  ∀ v ∈ S, ∃ x : 𝓞 D.host.F, x ∈ v.asIdeal ∧
    ∀ y : 𝓞 D.host.E, (y : D.host.E) = algebraMap D.host.F D.host.E (x : D.host.F) → y ∉ P.asIdeal

variable (V) in

def IsHeckeOpAt (J : Set (GA D V)) (χ : GA D V → ℂ) (S : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (P : HeightOneSpectrum (𝓞 D.host.E)) (k : ℕ) (R : Finset (GA D V)) : Prop :=
  ∃ (e : Formalism.L2.Theta.AE D) (ϖ : 𝓞 D.host.E) (α : GA D V),
    OffS D S P ∧ Formalism.L2.NTheta.IsIdemAt e P ∧ ϖ ∈ P.asIdeal ∧ ϖ ∉ P.asIdeal ^ 2 ∧ k ≤ V.rank ∧
    (∀ g, Formalism.L2.Theta.SuppAt e V g → (g ∈ J ↔ g ∈ KsphC V ∅)) ∧
    (∀ g ∈ J, Formalism.L2.Theta.SuppAt e V g → χ g = 1) ∧
    Formalism.L2.NTheta.IsHeckeElt V e (ϖ : D.host.E) k α ∧ (∀ γ ∈ R, Formalism.L2.Theta.SuppAt e V γ) ∧
    IsCosetRep V (locPart V J e) α⁻¹ R

def heckeOn (M : DSModel V S) (R : Finset (GA D V)) : MMap M →ₗ[ℂ] MMap M := postOn M (heckeLin V R)

def goodPart (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (e : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) :
    Submodule ℂ (MMap M) :=
  Mult θ M J χ ⊓ LinearMap.ker (postOn M e - LinearMap.id)

def part (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (c : HeightOneSpectrum (𝓞 D.host.E) → ℕ → ℂ) : Submodule ℂ (MMap M) :=
  Mult θ M J χ ⊓ ⨅ (P : HeightOneSpectrum (𝓞 D.host.E)) (k : ℕ) (R : Finset (GA D V))
    (_ : IsHeckeOpAt V J χ Sb P k R), LinearMap.ker (heckeOn M R - c P k • LinearMap.id)

def Ix (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (e : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) : Set (HeightOneSpectrum (𝓞 D.host.E) → ℕ → ℂ) :=
  {c | (∀ P k, (¬ ∃ R, IsHeckeOpAt V J χ Sb P k R) → c P k = 0) ∧ part θ M J χ Sb c ⊓ goodPart θ M J χ e ≠ ⊥}

def IsPrimeIdem (P : HeightOneSpectrum (𝓞 D.host.E)) (e f : Formalism.L2.Theta.AE D) : Prop :=
  (Formalism.L2.NTheta.IsIdemAt e P ∧ f = e + cA D e) ∨
  (f = e ∧ (∃ v ε, IsPlaceIdem D v ε ∧ e = algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) ε) ∧
    ∀ x : 𝓞 D.host.E, x ≠ 0 →
      (x ∈ P.asIdeal ↔ finPart D (e * incA D ((x : D.host.E)⁻¹)) ∉ intAE D))

variable (V) in

def SuppF (f : Formalism.L2.Theta.AE D) (g : GA D V) : Prop :=
  ∀ i j, f * (Formalism.L2.Theta.mt V g - 1) i j = (Formalism.L2.Theta.mt V g - 1) i j

def IntVec {n : ℕ} (z : Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) : Prop := ∀ i, z i ∈ intAE D

variable (V) in

def DivAt (e : Formalism.L2.Theta.AE D) (ϖ : D.host.E) (d : List ℤ) (α : GA D V) : Prop :=
  d.length = V.rank ∧ ∃ B : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E),
    (∀ z, IntVec z → (fun a => finPart D e * B.mulVec z a) ∈ Formalism.L2.NTheta.LamHat V) ∧
    (∀ y ∈ Formalism.L2.NTheta.LamHat V, ∃ z, IntVec z ∧
      (fun a => finPart D e * y a) = fun a => finPart D e * B.mulVec z a) ∧
    (∀ y ∈ Formalism.L2.NTheta.LamHat V, ∃ z, IntVec z ∧
      (fun a => finPart D e * (finMat D.sp.cm.sig V.gram α).mulVec y a) =
        fun a => finPart D e * B.mulVec (fun i => finPart D (incA D (ϖ ^ (d.getD i.1 0))) * z i) a) ∧
    (∀ z, IntVec z → ∃ y ∈ Formalism.L2.NTheta.LamHat V,
      (fun a => finPart D e * (finMat D.sp.cm.sig V.gram α).mulVec y a) =
        fun a => finPart D e * B.mulVec (fun i => finPart D (incA D (ϖ ^ (d.getD i.1 0))) * z i) a)

variable (V) in

def Hecke₂ (J : Set (GA D V)) (χ : GA D V → ℂ) (S : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (P : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ) (R : Finset (GA D V)) : Prop :=
  ∃ (e f : Formalism.L2.Theta.AE D) (ϖ : 𝓞 D.host.E) (α : GA D V),
    OffS D S P ∧ IsPrimeIdem P e f ∧ ϖ ∈ P.asIdeal ∧ ϖ ∉ P.asIdeal ^ 2 ∧ d.Pairwise (fun a b => b ≤ a) ∧
    (∀ g, SuppF V f g → (g ∈ J ↔ g ∈ KsphC V ∅)) ∧ (∀ g ∈ J, SuppF V f g → χ g = 1) ∧
    SuppF V f α ∧ DivAt V e (ϖ : D.host.E) d α ∧ (∀ γ ∈ R, SuppF V f γ) ∧
    IsCosetRep V {k | k ∈ J ∧ SuppF V f k} α R

def partFull (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ) : Submodule ℂ (MMap M) :=
  Mult θ M J χ ⊓ ⨅ (P : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ) (R : Finset (GA D V))
    (_ : Hecke₂ V J χ Sb P d R), LinearMap.ker (heckeOn M R - c P d • LinearMap.id)

def IxFull (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (e : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) : Set (HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ) :=
  {c | (∀ P d, (¬ ∃ R, Hecke₂ V J χ Sb P d R) → c P d = 0) ∧
    partFull θ M J χ Sb c ⊓ goodPart θ M J χ e ≠ ⊥}

def dualLab (d : List ℤ) : List ℤ := (d.map Neg.neg).reverse

def partDual (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ) : Submodule ℂ (MMap M) :=
  partFull θ M J χ Sb (fun P d => c P (dualLab d))

def SphOff (J : Set (GA D V)) (χ : GA D V → ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) : Prop :=
  ∀ P : HeightOneSpectrum (𝓞 D.host.E), OffS D Sb P → ∃ e f : Formalism.L2.Theta.AE D, IsPrimeIdem P e f ∧
    (∀ g, SuppF V f g → (g ∈ J ↔ g ∈ KsphC V ∅)) ∧ (∀ g ∈ J, SuppF V f g → χ g = 1)

def splitLab (n k : ℕ) : List ℤ := List.replicate (n - k) 0 ++ List.replicate k (-1)

def ScalarOnPartsFull (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ)
    (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (e : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ))
    (L : MMap M →ₗ[ℂ] MMap M) : Prop :=
  ∀ c, ∃ l : ℂ, ∀ T ∈ partFull θ M J χ Sb c ⊓ goodPart θ M J χ e, L T = l • T

def ScalarOnParts (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ)
    (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (e : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ))
    (L : MMap M →ₗ[ℂ] MMap M) : Prop :=
  ∀ c, ∃ l : ℂ, ∀ T ∈ part θ M J χ Sb c ⊓ goodPart θ M J χ e, L T = l • T

def tparRec (D : D7) : TPar D := tparHC D (fun _ => -(1 / 2)) (fun _ => Or.inr rfl)

def EE {Y0 : HSp D} (Ptw : TPar D) (M : DSModel Y0 (parB Ptw 0)) (J : Set (GA D Y0)) (χ : GA D Y0 → ℂ)
    (e : (GA D Y0 → ℂ) →ₗ[ℂ] (GA D Y0 → ℂ)) : Submodule ℂ (MMap M) :=
  goodPart θ M J χ e

def Wgood {W : HSp D} {κ : ∀ τ : D.what₂.Tau, Fin (W.sig (tauE D τ)).1 ⊕ Fin (W.sig (tauE D τ)).2 → ℤ}
    (M : DSModel W (parW W κ)) (J : Set (GA D W)) (χ : GA D W → ℂ)
    (e : (GA D W → ℂ) →ₗ[ℂ] (GA D W → ℂ)) : Submodule ℂ (MMap M) :=
  goodPart θ M J χ e

def EErec (M : DSModel (D.sp.Y 0) (parB (tparRec D) 0)) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ)
    (e : (GA D (D.sp.Y 0) → ℂ) →ₗ[ℂ] (GA D (D.sp.Y 0) → ℂ)) : Submodule ℂ (MMap M) :=
  EE θ (tparRec D) M J χ e

def WgoodRec (j : ℕ) (M : DSModel (D.sp.W j) (parW (D.sp.W j) (Formalism.L2.NTheta.wtOf D (D.sp.W j))))
    (J : Set (GA D (D.sp.W j))) (χ : GA D (D.sp.W j) → ℂ)
    (e : (GA D (D.sp.W j) → ℂ) →ₗ[ℂ] (GA D (D.sp.W j) → ℂ)) : Submodule ℂ (MMap M) :=
  Wgood θ M J χ e

def EEpart (M : DSModel (D.sp.Y 0) (parB (tparRec D) 0)) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ)
    (e : (GA D (D.sp.Y 0) → ℂ) →ₗ[ℂ] (GA D (D.sp.Y 0) → ℂ)) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ) : Submodule ℂ (MMap M) :=
  partDual θ M J χ Sb c ⊓ EErec θ M J χ e

def Wpart (j : ℕ) (M : DSModel (D.sp.W j) (parW (D.sp.W j) (Formalism.L2.NTheta.wtOf D (D.sp.W j))))
    (J : Set (GA D (D.sp.W j))) (χ : GA D (D.sp.W j) → ℂ)
    (e : (GA D (D.sp.W j) → ℂ) →ₗ[ℂ] (GA D (D.sp.W j) → ℂ)) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ) : Submodule ℂ (MMap M) :=
  partFull θ M J χ Sb c ⊓ WgoodRec θ j M J χ e

theorem hasPeterssonInner_unique (M : DSModel V S) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (T T' : MMap M) {c c' : ℂ}
    (v : M.Vec) (hv : ∏ τ, ⟪(v τ : M.H τ), (v τ : M.H τ)⟫_ℂ ≠ 0)
    (h : IsMultIP M μ 𝓕 T T' c) (h' : IsMultIP M μ 𝓕 T T' c') : c = c' := by
  have h1 := (h v v).2
  have h2 := (h' v v).2
  rw [h1] at h2
  exact mul_right_cancel₀ hv h2

theorem ipM_spec (M : DSModel V S) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (T T' : MMap M)
    (h : ∃ c, IsMultIP M μ 𝓕 T T' c) : IsMultIP M μ 𝓕 T T' (ipM M μ 𝓕 T T') := by
  rw [ipM, dif_pos h]
  exact h.choose_spec

variable (V) in

def DSExists (S : D.what₂.Tau → SPar) : Prop :=
  V.SigOK → (∀ τ, GoodPar V.rank (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2 (S τ)) → Nonempty (DSModel V S)

def HCFinite (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) : Prop :=
  IsInfFam θ → (∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ k ∈ U, k ∈ GfC V → k ∈ J ∧ χ k = 1) →
    FiniteDimensional ℂ (Mult θ M J χ)

def SchurMult (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) :
    Prop :=
  IsInfFam θ → μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ →
    ∀ T ∈ Mult θ M J χ, ∀ T' ∈ Mult θ M J χ, ∃ c, IsMultIP M μ 𝓕 T T' c

def MultIndep (M M' : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) :
    Prop :=
  IsInfFam θ → ∃ U : ∀ τ, M'.H τ ≃ₗᵢ[ℂ] M.H τ,
    (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, U τ (M'.rep τ g w) = M.rep τ g (U τ w)) ∧
    ∃ Φ : Mult θ M J χ ≃ₗ[ℂ] Mult θ M' J χ,
      (∀ (T : Mult θ M J χ) (v' : M'.Vec) (v : M.Vec), (∀ τ, (v τ : M.H τ) = U τ (v' τ)) →
        (Φ T : MMap M') v' = (T : MMap M) v) ∧
      ∀ T T' : Mult θ M J χ, ipM M' μ 𝓕 (Φ T) (Φ T') = ipM M μ 𝓕 T T'

def LabelUnique (J : Set (GA D V)) (χ : GA D V → ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) : Prop :=
  ∀ P d R R', Hecke₂ V J χ Sb P d R → Hecke₂ V J χ Sb P d R' →
    ∀ F : GA D V → ℂ, (∀ k ∈ J, ∀ g, F (g * k) = χ k * F g) → heckeLin V R F = heckeLin V R' F

def FullDecomp (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (e : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) : Prop :=
  IsInfFam θ → SphOff J χ Sb → μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ →
    (∀ P d R, Hecke₂ V J χ Sb P d R → ∀ T ∈ goodPart θ M J χ e, heckeOn M R T ∈ goodPart θ M J χ e) →
    (goodPart θ M J χ e = ⨆ c ∈ IxFull θ M J χ Sb e, (partFull θ M J χ Sb c ⊓ goodPart θ M J χ e)) ∧
    ∀ c ∈ IxFull θ M J χ Sb e, ∀ c' ∈ IxFull θ M J χ Sb e, c ≠ c' →
      ∀ T ∈ partFull θ M J χ Sb c ⊓ goodPart θ M J χ e, ∀ T' ∈ partFull θ M J χ Sb c' ⊓ goodPart θ M J χ e,
        ipM M μ 𝓕 T T' = 0

def SplitDict (J : Set (GA D V)) (χ : GA D V → ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) : Prop :=
  ∀ P k R, IsHeckeOpAt V J χ Sb P k R → Hecke₂ V J χ Sb P (splitLab V.rank k) R

def DualConj (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (e : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) : Prop :=
  IsInfFam θ → SphOff J χ Sb →
    ∀ c ∈ IxFull θ M J χ Sb e, ∀ P d, (∃ R, Hecke₂ V J χ Sb P d R) → c P (dualLab d) = star (c P d)

theorem dualPar_dualPar (S : SPar) : dualPar (dualPar S) = S := by
  simp [dualPar, Finset.image_image, Function.comp_def]

theorem postOn_apply (M : DSModel V S) (L : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (T : MMap M) (v : M.Vec) :
    postOn M L T v = L (T v) := rfl

theorem heckeLin_apply (R : Finset (GA D V)) (F : GA D V → ℂ) (g : GA D V) :
    heckeLin V R F g = ∑ γ ∈ R, F (g * γ) := rfl

theorem goodPart_le (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (e : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) :
    goodPart θ M J χ e ≤ Mult θ M J χ := inf_le_left

theorem part_le (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (c : HeightOneSpectrum (𝓞 D.host.E) → ℕ → ℂ) : part θ M J χ Sb c ≤ Mult θ M J χ := inf_le_left

theorem mem_goodPart (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (e : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ))
    (T : MMap M) : T ∈ goodPart θ M J χ e ↔ T ∈ Mult θ M J χ ∧ ∀ v, e (T v) = T v := by
  rw [goodPart, Submodule.mem_inf, LinearMap.mem_ker]
  refine and_congr Iff.rfl ?_
  constructor
  · intro h v
    have h1 := congrArg (fun S => S v) h
    simpa [postOn_apply, sub_eq_zero] using h1
  · intro h
    ext v
    simp [postOn_apply, h]

theorem mem_part (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (c : HeightOneSpectrum (𝓞 D.host.E) → ℕ → ℂ) (T : MMap M) :
    T ∈ part θ M J χ Sb c ↔ T ∈ Mult θ M J χ ∧
      ∀ P k R, IsHeckeOpAt V J χ Sb P k R → ∀ v, heckeLin V R (T v) = c P k • T v := by
  simp only [part, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]
  refine and_congr Iff.rfl ?_
  refine forall_congr' fun P => forall_congr' fun k => forall_congr' fun R => forall_congr' fun _ => ?_
  constructor
  · intro h v
    have h1 := congrArg (fun S => S v) h
    simpa [heckeOn, postOn_apply, sub_eq_zero] using h1
  · intro h
    ext v
    simp [heckeOn, postOn_apply, h]

theorem mem_partFull (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ)
    (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ) (T : MMap M) :
    T ∈ partFull θ M J χ Sb c ↔ T ∈ Mult θ M J χ ∧
      ∀ P d R, Hecke₂ V J χ Sb P d R → ∀ v, heckeLin V R (T v) = c P d • T v := by
  simp only [partFull, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]
  refine and_congr Iff.rfl ?_
  refine forall_congr' fun P => forall_congr' fun d => forall_congr' fun R => forall_congr' fun _ => ?_
  constructor
  · intro h v
    have h1 := congrArg (fun S => S v) h
    simpa [heckeOn, postOn_apply, sub_eq_zero] using h1
  · intro h
    ext v
    simp [heckeOn, postOn_apply, h]

def MultT (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) :
    Submodule ℂ ((⨂[ℂ] τ, M.sm τ) →ₗ[ℂ] (GA D V → ℂ)) :=
  (Mult θ M J χ).map (PiTensorProduct.lift : MMap M ≃ₗ[ℂ] _).toLinearMap

def ipT (M : DSModel V S) (μ : Measure (GA D V)) (𝓕 : Set (GA D V))
    (x y : (⨂[ℂ] τ, M.sm τ) →ₗ[ℂ] (GA D V → ℂ)) : ℂ :=
  ipM M μ 𝓕 (PiTensorProduct.lift.symm y) (PiTensorProduct.lift.symm x)

theorem mem_multT (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ)
    (x : (⨂[ℂ] τ, M.sm τ) →ₗ[ℂ] (GA D V → ℂ)) :
    x ∈ MultT θ M J χ ↔ PiTensorProduct.lift.symm x ∈ Mult θ M J χ := by
  unfold MultT
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨_, h, LinearEquiv.apply_symm_apply _ x⟩

end Formalism.IndefR.Mult

end
