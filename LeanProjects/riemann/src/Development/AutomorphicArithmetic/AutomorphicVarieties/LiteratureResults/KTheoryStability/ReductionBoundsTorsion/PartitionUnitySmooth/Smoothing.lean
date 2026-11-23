import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SBridgeAlt

noncomputable section

open NumberField Matrix UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.SmoothPartitionUnityBasic

section Defs

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

def Cl (δ : ℝ) (h k : HS L N) : Prop := ∀ z : VR L N, |qR k z - qR h z| ≤ δ * qR h z

abbrev ac (γ : Gm L N) (h : HS L N) : HS L N := actL (emb L N γ) h

def rho (x : ℝ) : ℝ := Real.smoothTransition ((4 - x) / 3)

def rk (h : HS L N) (v : Lat L N) : HS L N :=
  mkHS (fun w => vecMulVec (mat h w *ᵥ toR v w) (star (mat h w *ᵥ toR v w))) fun w => by
    ext i j
    simp [vecMulVec_apply, conjTranspose_apply, mul_comm]

def zed (s : ℝ) (h : HS L N) : ℝ := ∑ᶠ v : Lat L N, rho (q h v / s)

def term (s : ℝ) (h : HS L N) : HS L N := (s ^ 2 * zed s h)⁻¹ • ∑ᶠ v : Lat L N, rho (q h v / s) • rk h v

def ret (μ : HS L N → ℝ) (h : HS L N) : HS L N :=
  μ h • h + ∑ᶠ k : ℤ, rho ((4 : ℝ) ^ k * μ h) • term ((4 : ℝ) ^ k) h

structure Smoothing (ν μ : HS L N → ℝ) : Prop where
  smooth : ContDiffOn ℝ (⊤ : ℕ∞) μ (Pos L N)
  inv : ∀ γ, ∀ h ∈ Pos L N, μ (ac γ h) = μ h
  cmp : ∃ c C : ℝ, 0 < c ∧ ∀ h ∈ Pos L N, c * ν h ≤ μ h ∧ μ h ≤ C * ν h
  lip : ∃ C : ℝ, ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 / 4 → ∀ h ∈ Pos L N, ∀ k, Cl δ h k → |μ k - μ h| ≤ C * δ * μ h

def lamD (h : HS L N) : ℝ := lam (dualH h)

end Defs

def Basic : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (N : ℕ), 1 ≤ N →
    (∀ h ∈ Pos L N, 0 < lam h ∧ (∀ v : Lat L N, v ≠ 0 → lam h ≤ q h v) ∧ (∃ v : Lat L N, v ≠ 0 ∧ q h v = lam h) ∧
      dualH h ∈ Pos L N ∧ ∀ B : ℝ, {v : Lat L N | q h v ≤ B}.Finite) ∧
    (∀ (γ : Gm L N) (h : HS L N) (v : Lat L N), q (ac γ h) v = q h (γ⁻¹ • v)) ∧
    (∀ γ : Gm L N, ∃ γ' : Gm L N, ∀ h ∈ Pos L N, dualH (ac γ h) = ac γ' (dualH h)) ∧
    (∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 / 2 → ∀ h ∈ Pos L N, ∀ k, Cl δ h k → k ∈ Pos L N ∧ Cl (2 * δ) (dualH h) (dualH k)) ∧
    (∀ δ : ℝ, 0 ≤ δ → ∀ h ∈ Pos L N, ∀ k, Cl δ h k → ∀ (w : InfinitePlace L) (u v : Fin N → ℂ),
      ‖star u ⬝ᵥ (mat k w *ᵥ v) - star u ⬝ᵥ (mat h w *ᵥ v)‖ ^ 2 ≤
        4 * δ ^ 2 * (star u ⬝ᵥ (mat h w *ᵥ u)).re * (star v ⬝ᵥ (mat h w *ᵥ v)).re) ∧
    ContDiffOn ℝ (⊤ : ℕ∞) (dualH : HS L N → HS L N) (Pos L N)

def Count : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (N : ℕ) (R : ℝ), ∃ C : ℝ, 0 < C ∧ ∀ h ∈ Pos L N, ∀ s : ℝ, 0 ≤ s →
    (({v : Lat L N | q h v ≤ R * s}.ncard : ℕ) : ℝ) ≤ C * ({v : Lat L N | q h v ≤ s}.ncard : ℕ)

def SmMin : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (N : ℕ), 1 ≤ N → ∃ μ : HS L N → ℝ, Smoothing lamD μ

def TransZ : Prop :=
  ∀ d : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = d → ∀ G : Matrix ι ι ℝ, G.PosDef →
    ∀ δ : ℝ, 0 < δ → (∀ c : ι → ℤ, c ≠ 0 → δ ≤ (fun i => (c i : ℝ)) ⬝ᵥ (G⁻¹ *ᵥ fun i => (c i : ℝ))) →
      ∀ p : ι → ℝ, ∃ c : ι → ℤ, (p - fun i => (c i : ℝ)) ⬝ᵥ (G *ᵥ (p - fun i => (c i : ℝ))) ≤ C / δ

def Trans : Prop :=
  ∀ (L : Type) [Field L] [NumberField L], IsTotallyComplex L → ∀ N : ℕ, 1 ≤ N → ∃ C : ℝ, 0 < C ∧ ∀ h ∈ Pos L N,
    ∀ z : VR L N, ∃ v : Lat L N, qR h (z - toR v) ≤ C / lamD h

def RSmooth : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (N : ℕ), 1 ≤ N → ∀ μ : HS L N → ℝ, Smoothing lamD μ →
    ContDiffOn ℝ (⊤ : ℕ∞) (ret μ) (Pos L N)

def REqv : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (N : ℕ), 1 ≤ N → ∀ μ : HS L N → ℝ, Smoothing lamD μ → ∀ h ∈ Pos L N,
    (∀ γ, ret μ (ac γ h) = ac γ (ret μ h)) ∧ ret μ h ∈ Pos L N ∧ ∀ z, μ h * qR h z ≤ qR (ret μ h) z

def RLow : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (N : ℕ), 1 ≤ N → ∀ μ : HS L N → ℝ, Smoothing lamD μ →
    ∃ c : ℝ, 0 < c ∧ ∀ h ∈ Pos L N, c ≤ lam (ret μ h)

def RDual : Prop :=
  ∀ (L : Type) [Field L] [NumberField L], IsTotallyComplex L → ∀ N : ℕ, 1 ≤ N → ∀ μ : HS L N → ℝ, Smoothing lamD μ →
    ∃ c : ℝ, 0 < c ∧ ∀ h ∈ Pos L N, c ≤ lamD (ret μ h)

def TLip : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (N : ℕ), 1 ≤ N → ∃ C : ℝ, ∀ s : ℝ, 0 < s → ∀ h ∈ Pos L N, ∀ z : VR L N,
    (0 ≤ qR (term s h) z ∧ qR (term s h) z ≤ 4 / s * qR h z) ∧ (4 * s ≤ lam h → term s h = 0) ∧
    ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 / 4 → ∀ k, Cl δ h k → |qR (term s k) z - qR (term s h) z| ≤ C * δ / s * qR h z

def RLip : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (N : ℕ), 1 ≤ N → ∀ μ : HS L N → ℝ, Smoothing lamD μ →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 / 4 → ∀ h ∈ Pos L N, ∀ k, Cl δ h k →
      Cl (C * (1 + (lam h * lamD h)⁻¹) * δ) (ret μ h) (ret μ k)

def Thick : Prop :=
  ∀ (L : Type) [Field L] [NumberField L], IsTotallyComplex L → ∀ N : ℕ, 1 ≤ N → ∀ c : ℝ, 0 < c →
    ∃ K : Set (HS L N), IsCompact K ∧ K ⊆ Pos L N ∧ ∀ h ∈ Pos L N, c ≤ lam h → c ≤ lamD h → ∃ γ, ac γ h ∈ K

def Proper : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (N : ℕ), IsOpen (Pos L N) ∧
    ∀ K : Set (HS L N), IsCompact K → K ⊆ Pos L N → {γ : Gm L N | ∃ h ∈ K, ac γ h ∈ K}.Finite

def Bump : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (N : ℕ) (K : Set (HS L N)), IsCompact K → K ⊆ Pos L N →
    ∃ (ψ : HS L N → ℝ) (K' : Set (HS L N)) (C : ℝ), IsCompact K' ∧ K' ⊆ Pos L N ∧ ContDiff ℝ (⊤ : ℕ∞) ψ ∧
      (∀ h, ψ h ≠ 0 → h ∈ K') ∧ (∀ h, |ψ h| ≤ C) ∧
      (∀ h ∈ Pos L N, (∃ γ, ac γ h ∈ K) → ∑ᶠ γ : Gm L N, ψ (actL (emb L N γ)⁻¹ h) = 1) ∧
      ∀ δ : ℝ, 0 ≤ δ → ∀ h ∈ Pos L N, ∀ k, Cl δ h k → |ψ k - ψ h| ≤ C * δ

def Nrm : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (N : ℕ), 1 ≤ N → ∃ (n : HS L N → HS L N) (C : ℝ), 0 ≤ C ∧
    ContDiffOn ℝ (⊤ : ℕ∞) n (Pos L N) ∧ (∀ h ∈ Pos L N, ∃ t : ℝ, 0 < t ∧ n h = t • h) ∧
    (∀ γ, ∀ h ∈ Pos L N, n (ac γ h) = ac γ (n h)) ∧ (∀ r : ℝ, 0 < r → ∀ h ∈ Pos L N, n (r • h) = n h) ∧
    (∀ r : ℝ, 0 < r → ∀ h ∈ Pos L N, lam (r • h) * lamD (r • h) = lam h * lamD h) ∧
    ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 / 4 → ∀ h ∈ Pos L N, ∀ k, Cl δ h k → Cl (C * δ) (n h) (n k)

def DerB : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (N : ℕ) (φ : HS L N → ℝ) (x : Gp L N) (B ε : ℝ), 0 ≤ B → 0 < ε →
    DifferentiableAt ℝ φ (actL x (one L N).1) →
    (∀ δ : ℝ, 0 ≤ δ → δ ≤ ε → ∀ k, Cl δ (actL x (one L N).1) k → |φ k - φ (actL x (one L N).1)| ≤ B * δ) →
      ‖(fderiv ℝ φ (actL x (one L N).1)).comp (actL x)‖ ≤ N * B

def GCount : Prop := Basic → Count
def GSmMin : Prop := Basic → Count → SmMin
def GTrans : Prop := Basic → TransZ → Trans
def GRSmooth : Prop := Basic → RSmooth
def GREqv : Prop := Basic → REqv
def GRLow : Prop := Basic → Count → REqv → TLip → RLow
def GRDual : Prop := Basic → Trans → REqv → TLip → RDual
def GTLip : Prop := Basic → Count → TLip
def GRLip : Prop := Basic → REqv → TLip → RLip
def GThick : Prop := Basic → Trans → Thick
def GProper : Prop := Basic → Proper
def GBump : Prop := Basic → Proper → Bump
def GNrm : Prop := Basic → Nrm
def GFin : Prop := SHt → SmMin → RSmooth → REqv → RLow → RDual → RLip → Thick → Proper → Bump → Nrm → DerB → SPU

end PositivityTheory.KB.SmoothPartitionUnityBasic

end
