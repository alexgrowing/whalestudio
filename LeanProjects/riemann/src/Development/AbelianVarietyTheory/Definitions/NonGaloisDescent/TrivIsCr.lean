import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l}

structure WSeed (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) where

  N : ℕ

  c₁ : ℕ

  c₂ : ℕ

  c₃ : ℕ

  F : Matrix (Fin d) (Fin d) (Wq l bk.a)

  F' : Matrix (Fin d) (Fin d) (Wq l bk.a)
  F_mul : F * F' = (l : Wq l bk.a) ^ c₃ • (1 : Matrix (Fin d) (Fin d) (Wq l bk.a))

  X : Matrix (Fin d) (Fin d) bk.S

  X' : Matrix (Fin d) (Fin d) bk.S
  X_mul : X * X' = ((l : bk.S) ^ c₂ * bk.E ^ (2 * N)) • (1 : Matrix (Fin d) (Fin d) bk.S)

  W : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)

  W' : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)
  W_mul : W * W' = bk.iA τ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀))
  φ : ∀ Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap WittVector.frobenius Φ →
    ((l : bk.DA bk.ρ₀) ^ c₁) • (W * X'.map bk.iS).map Φ =
      bk.iS (frobS l bk.a bk.E) ^ N • (W * X'.map bk.iS * F.map (bk.iS.comp C))

  κ : ↥(GK K) → Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)
  gal : ∀ (g : ↥(GK K)) (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (Per.σA (g : GQ l)) G →
    bk.iA (bk.ev bk.E * τ) ^ N • ((ρ g).map (bk.iA.comp (algebraMap ℤ_[l] (Ainf l))) * (W * X'.map bk.iS).map G) =
      bk.iA (Per.σA (g : GQ l) (bk.ev bk.E * τ)) ^ N • (W * X'.map bk.iS * κ g)
  fix : ∀ g : ↥(GK K), bk.FixFlat g → κ g = 1
  nopole : ∀ (g : ↥(GK K)) (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (Per.σA (g : GQ l)) G → ∀ i j,
    bk.iS bk.E ^ (2 * N) ∣ (X'.map bk.iS * κ g * (X.map bk.iS).map G) i j
  log : ∀ m : ℕ, ∃ (k : ℕ) (Λ : Matrix (Fin d) (Fin d) bk.S), (∀ i j, bk.E ∣ (Λ - (l : bk.S) ^ k • (1 : Matrix (Fin d) (Fin d) bk.S)) i j) ∧
    ∀ (g : ↥(GK K)) (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (Per.σA (g : GQ l)) G → ∀ i j,
      bk.iS bk.E ^ m ∣ (κ g * (Λ.map bk.iS).map G - Λ.map bk.iS) i j

structure Pre (bk : BK K) (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) where

  T : Matrix (Fin d) (Fin d) (WCb l)
  unit : IsUnit T

  A : Matrix (Fin d) (Fin d) bk.S

  A' : Matrix (Fin d) (Fin d) bk.S
  A_mul : A * A' = bk.E ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) bk.S)
  φ : bk.evW bk.E ^ N • T.map (frobW l) = T * A.map bk.evW
  fix : ∀ g : ↥(GK K), bk.FixFlat g → zW (ρ g) * T.map (galW l (g : GQ l)) = T

structure Frame (bk : BK K) (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) extends Pre bk N d ρ where

  ε : ↥(GK K) → Matrix (Fin d) (Fin d) (Ainf l)
  gal : ∀ g : ↥(GK K), zW (ρ g) * T.map (galW l (g : GQ l)) = T * (ε g).map (inclW l)

variable {bk : BK K} {N d : ℕ} {ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]}

def Frame.IsBeta (F : Frame bk N d ρ) (m k : ℕ) (β : Matrix (Fin d) (Fin d) bk.S) : Prop :=
  (∀ i j, bk.E ∣ (β - (l : bk.S) ^ k • (1 : Matrix (Fin d) (Fin d) bk.S)) i j) ∧ ∀ (g : ↥(GK K)) i j,
    bk.ev bk.E ^ m ∣ ((F.ε g).map WittVector.frobenius * (β.map bk.ev).map (Per.σA (g : GQ l)) - β.map bk.ev) i j

def Frame.IsDR (F : Frame bk N d ρ) : Prop := ∀ m : ℕ, ∃ k β, F.IsBeta m k β

def Frame.IsCr (F : Frame bk N d ρ) : Prop :=
  ∀ (g : ↥(GK K)) i j, bk.ev X ∣ (F.ε g - (1 : Matrix (Fin d) (Fin d) (Ainf l))) i j

def Link (bk : BK K) {d' : ℕ} (T : Matrix (Fin d) (Fin d) (WCb l)) (T' : Matrix (Fin d') (Fin d') (WCb l))
    (Pi : Matrix (Fin d) (Fin d') ℤ_[l]) (n r : ℕ) : Prop :=
  ∃ (R : Matrix (Fin d) (Fin d') bk.S) (G : Matrix (Fin d') (Fin d) bk.S),
    (∀ i j, (l : WCb l) ^ n ∣ (zW Pi * T' - T * R.map bk.evW) i j) ∧
    ∀ i j, (l : bk.S) ^ n ∣ (R * G - (l : bk.S) ^ r • (1 : Matrix (Fin d) (Fin d) bk.S)) i j

structure Onto {Γ : Type} {d d' : ℕ} (ρ : Γ → Matrix (Fin d) (Fin d) ℤ_[l]) (ρ' : Γ → Matrix (Fin d') (Fin d') ℤ_[l])
    (Pi : Matrix (Fin d) (Fin d') ℤ_[l]) (n : ℕ) : Prop where
  equi : ∀ g i j, (l : ℤ_[l]) ^ n ∣ (Pi * ρ' g - ρ g * Pi) i j
  surj : ∃ S : Matrix (Fin d') (Fin d) ℤ_[l], ∀ i j, (l : ℤ_[l]) ^ n ∣ (Pi * S - (1 : Matrix (Fin d) (Fin d) ℤ_[l])) i j

structure Tower {Γ : Type} [Group Γ] {d : ℕ} (ρ : Γ →* GL (Fin d) ℤ_[l]) where

  d' : ℕ → ℕ

  ρ' : ∀ n, Γ →* GL (Fin (d' n)) ℤ_[l]

  Pi : ∀ n, Matrix (Fin d) (Fin (d' n)) ℤ_[l]
  onto : ∀ n, Onto (fun g => (ρ g).val) (fun g => (ρ' n g).val) (Pi n) n

  f : ∀ n, Matrix (Fin (d' n)) (Fin (d' (n + 1))) ℤ_[l]
  f_equi : ∀ n g, f n * (ρ' (n + 1) g).val = (ρ' n g).val * f n
  f_Pi : ∀ n i j, (l : ℤ_[l]) ^ n ∣ (Pi n * f n - Pi (n + 1)) i j

def zOm (l : ℕ) [Fact l.Prime] : ℤ_[l] →+* Om l := (algebraMap ℚ_[l] (Om l)).comp (algebraMap ℤ_[l] ℚ_[l])

def qRep {Γ : Type} [Group Γ] {d : ℕ} (ρ : Γ →* GL (Fin d) ℤ_[l]) : Representation ℚ_[l] Γ (Fin d → ℚ_[l]) :=
  ((Matrix.toLinAlgEquiv' : Matrix (Fin d) (Fin d) ℚ_[l] ≃ₐ[ℚ_[l]] _) : _ →* _).comp
    (((algebraMap ℤ_[l] ℚ_[l]).mapMatrix : Matrix (Fin d) (Fin d) ℤ_[l] →+* _).toMonoidHom.comp ((Units.coeHom _).comp ρ))

structure Reads {Γ : Type} [Group Γ] {a d : ℕ} (ρ : Γ →* GL (Fin d) ℤ_[l]) (r : Γ →* GL (Fin a) (Om l))
    (b : Fin d → Matrix (Fin a) (Fin a) (Om l)) (e : Fin d → ℤ_[l]) : Prop where
  equi : ∀ g j, (r g).val * b j = ∑ i, zOm l ((ρ g).val i j) • b i
  one : ∑ i, zOm l (e i) • b i = 1

structure Layer {Γ : Type} [Group Γ] {a d' : ℕ} (L₀ : FinExt l) (Cl : Set (Γ →* GL (Fin a) (Om l))) (ρ' : Γ →* GL (Fin d') ℤ_[l]) where

  m : ℕ

  rep : Fin m → (Γ →* GL (Fin a) (Om l))
  mem : ∀ k, rep k ∈ Cl

  L : Fin m → FinExt l
  le : ∀ k, L₀.1 ≤ (L k).1
  rep_mem : ∀ k g i j, (rep k g).val i j ∈ (L k).1

  b : Fin d' → Fin m → Matrix (Fin a) (Fin a) (Om l)
  b_mem : ∀ s k i j, b s k i j ∈ (L k).1
  indep : LinearIndependent ℚ_[l] b
  span : ∀ x : Fin m → Matrix (Fin a) (Fin a) (Om l), (∀ k i j, x k i j ∈ (L k).1) → x ∈ Submodule.span ℚ_[l] (Set.range b)

  e : Fin d' → ℤ_[l]
  reads : ∀ k, Reads ρ' (rep k) (fun s => b s k) e

  c : Fin m → Om l

structure Cover {Γ : Type} [Group Γ] [TopologicalSpace Γ] {a : ℕ} (L₀ : FinExt l) (r : Γ →* GL (Fin a) (Om l))
    (Cl : Set (Γ →* GL (Fin a) (Om l))) where

  d : ℕ

  ρ : Γ →* GL (Fin d) ℤ_[l]
  cont : Continuous ρ

  b : Fin d → Matrix (Fin a) (Fin a) (Om l)

  e : Fin d → ℤ_[l]
  reads : Reads ρ r b e

  tw : Tower ρ
  cont' : ∀ n, Continuous (tw.ρ' n)

  lay : ∀ n, Layer L₀ Cl (tw.ρ' n)
  unit : ∀ n i, (l : ℤ_[l]) ^ n ∣ (tw.Pi n *ᵥ (lay n).e - e) i
  trace : ∀ n s, ‖(∑ i, zOm l (tw.Pi n i s) • b i).trace - ∑ k, (lay n).c k * ((lay n).b s k).trace‖ ≤ ((l : ℝ) ^ n)⁻¹

def IsHT (C : Core l) (ξ : Ainf l) {a : ℕ} (ρ : ↥(GK K) → Matrix (Fin a) (Fin a) (Om l)) (z : ℂ_[l])
    (u : Matrix (Fin a) (Fin a) ℂ_[l]) : Prop :=
  ∀ (K' : FinExt l) (p q : ℕ) (x : Fin a → Per.BdR l) (y : Fin a → Per.BdRp l),
    (∀ g : ↥(GK K), (g : GQ l) ∈ GK K' →
      (ρ g).map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp C.o) *ᵥ (fun i => Per.σD (g : GQ l) (x i)) = x) →
    (∀ i, algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ) ^ q * x i = algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ ^ p * y i)) →
    u *ᵥ (fun i => Per.θD l (y i)) = z ^ ((p : ℤ) - q) • fun i => Per.θD l (y i)

structure Hodge (C : Core l) (ξ : Ainf l) {a : ℕ} (ρ : ↥(GK K) → Matrix (Fin a) (Fin a) (Om l)) (K' : FinExt l) where

  V : Matrix (Fin a) (Fin a) (Per.BdRp l)
  unit : IsUnit V

  p : Fin a → ℕ

  q : ℕ

  Q : Matrix (Fin a) (Fin a) (Per.BdR l)
  Q_eq : ∀ i j, algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ) ^ q * Q i j =
    algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ ^ p j * V i j)
  inv : ∀ g : ↥(GK K), (g : GQ l) ∈ GK K' →
    (ρ g).map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp C.o) * Q.map (Per.σD (g : GQ l)) = Q

def IsZ (bk : BK K) (g : ↥(GK K)) (z : ℂ_[l]) : Prop :=
  ∃ w : Ainf l, Per.σA (g : GQ l) (bk.ev bk.E) = bk.ev bk.E * w ∧ z * Per.θD l (aDp l w) = 1

def Frame.triv (bk : BK K) (d : ℕ) : Frame bk 0 d (fun _ => 1) where
  T := 1
  unit := isUnit_one
  A := 1
  A' := 1
  A_mul := by simp
  φ := by simp [Matrix.map_one]
  fix g _ := by simp [zW, Matrix.map_one]
  ε _ := 1
  gal g := by simp [zW, Matrix.map_one]

theorem Frame.triv_isCr (bk : BK K) (d : ℕ) : (Frame.triv bk d).IsCr := fun _ i j => by simp [Frame.triv]

end GlobalTheory.BKLim

end
