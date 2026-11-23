import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PrCloudAddPrNode
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BaseVectorTEqOne
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.MulConjTransposeEqOneOfOrthonormal

open Matrix MeasureTheory Finset Formalism.QuantumDeterminants Formalism.MainNotions.S
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.Mom

variable {k r : ℕ}

def TensorDec : Prop :=
  ∀ (k r : ℕ) (c Ch : ℝ) (P : Mat k r) lam (bv h q : ℝ) R, 0 < c → 0 < Ch → Setup k r c Ch P lam bv h q R →
    ∀ (dual : Bool) (l : ℕ), l ≤ r + 1 → ∀ μ, InPP lam q μ → (∀ I : Idx k r l, InPP lam q (μ + wtI dual I)) →
      ∃ ι p, IsTensDec R dual P l μ ι p

def LowestK : Prop :=
  ∀ (k r : ℕ) (P : Mat k r) (A : HRep k r) μ, IsCayleyU k r (sgnCN k r) P → IsHCParam μ → A.IsDSAt P μ →
    IsKTypeOf (sgnCN k r) (A.onJ P) (lowK (sgnCN k r) μ) (A.iso P (lowK (sgnCN k r) μ)) ∧
    ∀ a b, a < b → sgnCN k r a ≠ sgnCN k r b → A.iso P (lowK (sgnCN k r) μ - Formalism.REAL.root a b) = ⊥

def KFinAction : Prop :=
  ∀ (k r : ℕ) (P : Mat k r) (A : HRep k r) μ, IsCayleyU k r (sgnCN k r) P → IsHCParam μ → A.IsDSAt P μ →
    (∀ v, IsKFinHpk (k := k) (r := r) A.σ v → v ∈ smoothVecs (k := k) (r := r) A.σ ∧
      ∀ a b, IsKFinHpk (k := k) (r := r) A.σ (A.E P a b v)) ∧
    (∀ a b (t : ℂ), ∀ v ∈ smoothVecs (k := k) (r := r) A.σ, ∀ w ∈ smoothVecs (k := k) (r := r) A.σ,
      A.E P a b v ∈ smoothVecs (k := k) (r := r) A.σ ∧ A.E P a b (t • v + w) = t • A.E P a b v + A.E P a b w ∧
      ⟪A.E P a b v, w⟫_ℂ = (if sgnCN k r a = sgnCN k r b then 1 else -1) * ⟪v, A.E P b a w⟫_ℂ) ∧
    (∀ a b c d, ∀ v ∈ smoothVecs (k := k) (r := r) A.σ,
      A.E P a b (A.E P c d v) - A.E P c d (A.E P a b v) =
        (if b = c then A.E P a d v else 0) - (if d = a then A.E P c b v else 0)) ∧
    (∀ ν, FiniteDimensional ℂ (A.iso P ν) ∧ ∀ v ∈ A.iso P ν, IsKFinHpk (k := k) (r := r) A.σ v) ∧
    (∀ ν ν', ν ≠ ν' → ∀ v ∈ A.iso P ν, ∀ w ∈ A.iso P ν', ⟪v, w⟫_ℂ = 0) ∧
    ∀ v, IsKFinHpk (k := k) (r := r) A.σ v → v ∈ ⨆ ν, A.iso P ν

def CasimirValues : Prop :=
  ∀ (k r : ℕ) (P : Mat k r) (A : HRep k r) μ, IsCayleyU k r (sgnCN k r) P → IsHCParam μ → A.IsDSAt P μ →
    (∀ v ∈ smoothVecs (k := k) (r := r) A.σ, ∑ a, ∑ b, A.E P a b (A.E P b a v) =
      ((Formalism.REAL.nsq μ - Formalism.REAL.nsq (rhoStd (2 * r + k + 1)) : ℝ) : ℂ) • v) ∧
    (∀ ν, ∀ v ∈ A.iso P ν, ∑ a, ∑ b, (if sgnCN k r a = sgnCN k r b then A.E P a b (A.E P b a v) else 0) =
      ((Formalism.REAL.nsq (ν + Formalism.REAL.rhoC (sgnCN k r)) - Formalism.REAL.nsq (Formalism.REAL.rhoC (sgnCN k r)) : ℝ) : ℂ) • v) ∧
    ∀ ω, ∀ v ∈ smoothVecs (k := k) (r := r) A.σ, IsWtOn (Formalism.REAL.Kset (sgnCN k r)) (A.onJ P) ω v →
      ∀ a, A.E P a a v = (ω a : ℂ) • v

def FiltStep : Prop :=
  ∀ (k r : ℕ) (P : Mat k r) (A : HRep k r) μ, IsCayleyU k r (sgnCN k r) P → IsHCParam μ → A.IsDSAt P μ →
    ∀ (μ₀ : Fin (2 * r + k + 1) → ℝ) (j : ℕ), FiniteDimensional ℂ (A.filt P μ₀ j) ∧ ∀ w ∈ A.filt P μ₀ j,
      IsKFinHpk (k := k) (r := r) A.σ w ∧ ∀ a b, A.E P a b w ∈ A.filt P μ₀ (j + 2)

def FiltSize : Prop :=
  ∀ (k r : ℕ) (P : Mat k r) (A : HRep k r) μ (bs : ℝ), IsCayleyU k r (sgnCN k r) P → IsHCParam μ → A.IsDSAt P μ →
    (∀ a, |μ a| + ((2 * r + k + 1 : ℕ) : ℝ) ≤ bs) → ∀ (j : ℕ), ∀ w ∈ A.filt P μ j,
      (∑ a, ∑ b ∈ univ.erase a, ‖A.E P a b w‖ ^ 2 ≤
        8 * (bs + j) * (((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + j) * ‖w‖ ^ 2) ∧
      (∀ a, ‖A.E P a a w‖ ≤ (bs + j) * ‖w‖) ∧
      (∑ a, ∑ b, ‖A.E P a b w‖ ^ 2 ≤ 9 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 * (bs + j) ^ 2 * ‖w‖ ^ 2) ∧
      ∀ q : ℕ, ∑ s : Fin q → Fin (2 * r + k + 1) × Fin (2 * r + k + 1), ‖A.Ew P (List.ofFn s) w‖ ^ 2 ≤
        (3 * ((2 * r + k + 1 : ℕ) : ℝ) * (bs + j + 2 * q)) ^ (2 * q) * ‖w‖ ^ 2

def SplitCasimir : Prop :=
  ∀ (k r : ℕ) (c Ch : ℝ) (P : Mat k r) lam (bv h q : ℝ) R, 0 < c → 0 < Ch → Setup k r c Ch P lam bv h q R →
    ∀ μ, InPP lam (q - 1) μ → ∀ ι p, IsTensDec R true P 1 μ ι p →
      (∀ s, ∀ y ∈ smoothVecs (k := k) (r := r) (R (μ + wtI true s)).σ,
        (R μ).EE P (ι s y) = ((-μ (el s) + (1 - ((2 * r + k + 1 : ℕ) : ℝ)) / 2 : ℝ) : ℂ) • ι s y) ∧
      ∀ j : ℕ, (∀ x : Idx k r 1 → (R μ).H, (∀ a, x a ∈ (R μ).filt P μ j) → x ∈ VV R P μ p j) ∧
        ∀ x ∈ VV R P μ p j, (∀ a, x a ∈ (R μ).filt P μ (j + 2)) ∧
          ∀ s, p s x ∈ (R (μ + wtI true s)).filt P (μ + wtI true s) (j + 2)

def ProjNorms : Prop :=
  ∀ (k r : ℕ) (c Ch : ℝ) (P : Mat k r) lam (bv h q : ℝ) R, 0 < c → 0 < Ch → Setup k r c Ch P lam bv h q R →
    ∀ μ, InPP lam (q - 1) μ → ∀ ι p, IsTensDec R true P 1 μ ι p → ∀ j, HypJ k r bv j → ∀ x ∈ VV R P μ p j,
      nrm2 (∑ s ∈ univ.filter (fun s : Idx k r 1 => (el s).val < k - 1), ι s (p s x)) ≤ (18 / 13) ^ 2 * nrm2 x ∧
      ∀ s : Idx k r 1, k - 1 ≤ (el s).val → nrm2 (ι s (p s x)) ≤ (3 * (6 * bv) ^ (2 * r + 1)) ^ 2 * nrm2 x

def FormNormal : Prop :=
  ∀ (k r : ℕ) (c Ch : ℝ) (P : Mat k r) lam (bv h q : ℝ) R, 0 < c → 0 < Ch → Setup k r c Ch P lam bv h q R →
    ∀ (dual : Bool) (l : ℕ), l ≤ r + 1 → ∀ μ, InPP lam q μ → (∀ I : Idx k r l, InPP lam q (μ + wtI dual I)) →
      (∃ ι p, IsTensDec R dual P l μ ι p) → ∃ ι p ep, IsTensDec R dual P l μ ι p ∧ IsHHNorm R dual l μ ι ep

def CloudSign : Prop :=
  ∀ (k r : ℕ) (c Ch : ℝ) (P : Mat k r) lam (bv h q : ℝ) R, 0 < c → 0 < Ch → Setup k r c Ch P lam bv h q R →
    ∀ μ, InPP lam (q - 1) μ → ∀ ι p ep, IsTensDec R true P 1 μ ι p → IsHHNorm R true 1 μ ι ep →
      ∀ s : Idx k r 1, (el s).val < k - 1 → ep s = 1

def CompSum : Prop :=
  ∀ (k r : ℕ) (c Ch : ℝ) (P : Mat k r) lam (bv h q : ℝ) R, 0 < c → 0 < Ch → Setup k r c Ch P lam bv h q R →
    ∀ μ, InPP lam (q - 1) μ → ∀ ι p ep, IsTensDec R true P 1 μ ι p → IsHHNorm R true 1 μ ι ep →
      ∀ j, HypJ k r bv j → ∀ x ∈ VV R P μ p j, ∑ s, ‖p s x‖ ^ 2 ≤ (6 * bv) ^ (2 * (2 * r + 2)) * nrm2 x

def BesselOne : Prop :=
  ∀ (k r : ℕ) (P : Mat k r) (A : HRep k r) μ (F : Flag k r) (κ : ℝ), IsCayleyU k r (sgnCN k r) P → IsHCParam μ →
    A.IsDSAt P μ → F.Ok κ → ∀ B₁ B₂ : A.H → F.W, IsBesselMapSm F.z (psi k r F.z F.cψ) A.σ F.π B₁ →
      IsBesselMapSm F.z (psi k r F.z F.cψ) A.σ F.π B₂ → (∃ v ∈ smoothVecs (k := k) (r := r) A.σ, B₂ v ≠ 0) →
      ∃ a : ℂ, ∀ v ∈ smoothVecs (k := k) (r := r) A.σ, B₁ v = a • B₂ v

def IsoOrth : Prop :=
  ∀ (k r : ℕ) (P : Mat k r) (A A' : HRep k r) μ μ' (F : Flag k r) (κ : ℝ), IsCayleyU k r (sgnCN k r) P →
    IsHCParam μ → IsHCParam μ' → μ ≠ μ' → A.IsDSAt P μ → A'.IsDSAt P μ' → F.Ok κ → ∀ B B', F.Iso A B → F.Iso A' B' →
      ∀ w ∈ smoothVecs (k := k) (r := r) A.σ, ∀ w' ∈ smoothVecs (k := k) (r := r) A'.σ,
        ∫ x, ⟪B (A.σ (Matrix.of x) w), B' (A'.σ (Matrix.of x) w')⟫_ℂ ∂F.ν = 0 ∧
        Integrable (fun x => ⟪B (A.σ (Matrix.of x) w), B' (A'.σ (Matrix.of x) w')⟫_ℂ) F.ν

def SummandIso : Prop :=
  ∀ c : ℝ, 0 < c → ∃ Ch : ℝ, 0 < Ch ∧ ∀ (k r : ℕ) (P : Mat k r) lam (bv h q : ℝ) R, Setup k r c Ch P lam bv h q R →
    ∀ (F : Flag k r) (κ : ℝ), F.Ok κ → ∀ (dual : Bool) (l : ℕ) (hl : l ≤ r + 1) μ, InPP lam q μ →
      (∀ I : Idx k r l, InPP lam q (μ + wtI dual I)) → ∀ ι p, IsTensDec R dual P l μ ι p → ∀ B, F.Iso (R μ) B →
      ∀ I, (∀ y ∈ smoothVecs (k := k) (r := r) (R (μ + wtI dual I)).σ, omB dual P F.z hl B (ι I y) = 0) ∨
        ∃ (BI : (R (μ + wtI dual I)).H → F.W) (β : ℂ), F.Iso _ BI ∧
          ∀ y ∈ smoothVecs (k := k) (r := r) (R (μ + wtI dual I)).σ, omB dual P F.z hl B (ι I y) = β • BI y

def PieriBound : Prop :=
  ∀ c : ℝ, 0 < c → ∃ Ch : ℝ, 0 < Ch ∧ ∀ (k r : ℕ) (P : Mat k r) lam (bv h q b : ℝ) R, Setup k r c Ch P lam bv h q R →
    8704 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 ≤ bv → ∀ (F : Flag k r) (κ : ℝ), F.Ok κ → F.Size lam bv b →
    ∀ μ, InPP lam (q - 1) μ → ∀ ι p ep, IsTensDec R true P 1 μ ι p → IsHHNorm R true 1 μ ι ep → ∀ B, F.Iso (R μ) B →
      ∀ s (Bs : (R (μ + wtI true s)).H → F.W) (β : ℂ), F.Iso _ Bs →
        (∀ y ∈ smoothVecs (k := k) (r := r) (R (μ + wtI true s)).σ,
          omB true P F.z (by omega : 1 ≤ r + 1) B (ι s y) = β • Bs y) → ‖β‖ ^ 2 ≤ Amax r (Tz k r F.z) κ b 4

def MomentA : Prop :=
  ∀ c : ℝ, 0 < c → ∃ Ch : ℝ, 0 < Ch ∧ ∀ (k r : ℕ) (P : Mat k r) lam (bv h q₀ b : ℝ) R, Setup k r c Ch P lam bv h q₀ R →
    ∀ (F : Flag k r) (κ : ℝ), F.Ok κ → F.Size lam bv b → ∀ (j q : ℕ) μ, InPP lam (q₀ - q) μ → HypJ k r bv (j + 2 * q) →
      ∀ B, F.Iso (R μ) B → ∀ w ∈ (R μ).filt P μ j,
        (R μ).mass F.ν B (fun g => lA k r F.z g 0 ^ (2 * q)) w ≤
          ENNReal.ofReal (H0 k r (Tz k r F.z) κ b 4 bv ^ (2 * q)) * ‖w‖ₑ ^ 2

def MomentB : Prop :=
  ∀ (k r : ℕ) (P : Mat k r) (A : HRep k r) μ (bs : ℝ) (F : Flag k r) (κ : ℝ), IsCayleyU k r (sgnCN k r) P →
    IsHCParam μ → A.IsDSAt P μ → (∀ a, |μ a| + ((2 * r + k + 1 : ℕ) : ℝ) ≤ bs) → F.Ok κ → ∀ B, F.Iso A B →
      ∀ (j q : ℕ) (a : Fin r), ∀ w ∈ A.filt P μ j,
        A.mass F.ν B (fun g => (lA k r F.z g a.succ / lA k r F.z g a.castSucc) ^ (2 * q)) w ≤
          ENNReal.ofReal ((3 * ((2 * r + k + 1 : ℕ) : ℝ) * (bs + j + 2 * q) / κ) ^ (2 * q)) * ‖w‖ₑ ^ 2

def MomentCor : Prop :=
  ∀ c : ℝ, 0 < c → ∃ Ch : ℝ, 0 < Ch ∧ ∀ (k r : ℕ) (P : Mat k r) lam (bv h q₀ b : ℝ) R, Setup k r c Ch P lam bv h q₀ R →
    ∀ (F : Flag k r) (κ : ℝ), F.Ok κ → F.Size lam bv b → 1 ≤ Tz k r F.z → ∀ (j q : ℕ) μ B, F.Iso (R μ) B →
      ∀ w ∈ (R μ).filt P μ j,
        (InPP lam (q₀ - ((r + 1) * q : ℕ)) μ → HypJ k r bv (j + 2 * ((r + 1) * q)) →
          MomAll (R μ) F B (H1 k r (Tz k r F.z) κ b 4 bv) q w) ∧
        ∀ (l : ℕ) (hl : l ≤ r + 1), InPP lam (q₀ - ((r + 1) * l * q : ℕ)) μ → HypJ k r bv (j + 2 * ((r + 1) * l * q)) →
          MomProd (R μ) F B (H1 k r (Tz k r F.z) κ b 4 bv) hl q w

def LowAny : Prop :=
  ∀ (k r : ℕ) (P : Mat k r) (A : HRep k r) μ (F : Flag k r) (κ : ℝ), IsCayleyU k r (sgnCN k r) P → IsHCParam μ →
    A.IsDSAt P μ → F.Ok κ → ∀ B, F.Iso A B → ∀ φ : Mat k r → ℝ, Measurable (fun x : Mt k r => φ (Matrix.of x)) →
      (∀ g ∈ UH (Hpk k r), ∀ s ∈ Sset k r F.z, φ (s * g) = φ g) →
      (∀ g ∈ UH (Hpk k r), ∀ t ∈ UH (Hpk k r), t ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ → φ (g * t) = φ g) →
      ∀ w ∈ A.iso P (lowK (sgnCN k r) μ), ∀ w₀ ∈ A.iso P (lowK (sgnCN k r) μ), ‖w‖ = ‖w₀‖ →
        A.mass F.ν B φ w = A.mass F.ν B φ w₀

def MomentLow : Prop :=
  ∀ c : ℝ, 0 < c → ∃ Ch : ℝ, 0 < Ch ∧ ∀ (k r : ℕ) (P : Mat k r) lam (bv h q₀ b : ℝ) R, Setup k r c Ch P lam bv h q₀ R →
    ∀ (F : Flag k r) (κ : ℝ), F.Ok κ → F.Size lam bv b → 1 ≤ Tz k r F.z → ∀ (q : ℕ) μ B, F.Iso (R μ) B →
      ∀ w ∈ (R μ).iso P (lowK (sgnCN k r) μ),
        (InPP lam (q₀ - ((r + 1) * q : ℕ)) μ → HypJ k r bv (2 * ((r + 1) * q)) →
          MomAll (R μ) F B (H1 k r (Tz k r F.z) κ b 4 bv) q w) ∧
        ∀ (l : ℕ) (hl : l ≤ r + 1), InPP lam (q₀ - ((r + 1) * l * q : ℕ)) μ → HypJ k r bv (2 * ((r + 1) * l * q)) →
          MomProd (R μ) F B (H1 k r (Tz k r F.z) κ b 4 bv) hl q w

def KeyBound : Prop :=
  ∀ c : ℝ, 0 < c → ∃ Ch : ℝ, 0 < Ch ∧ ∀ (k r : ℕ) (P : Mat k r) lam (bv h q : ℝ) R, Setup k r c Ch P lam bv h q R →
    ∀ (F : Flag k r) (κ : ℝ), F.Ok κ → ∀ (dual : Bool) (l : ℕ) (hl : l ≤ r + 1) μ, InPP lam q μ →
      (∀ I : Idx k r l, InPP lam q (μ + wtI dual I)) → ∀ ι p ep, IsTensDec R dual P l μ ι p →
      IsHHNorm R dual l μ ι ep → ∀ B, F.Iso (R μ) B → ∀ I (BI : (R (μ + wtI dual I)).H → F.W) (β : ℂ), F.Iso _ BI →
        (∀ y ∈ smoothVecs (k := k) (r := r) (R (μ + wtI dual I)).σ, omB dual P F.z hl B (ι I y) = β • BI y) →
        ∀ x, IsKFinHpk (k := k) (r := r) (R (μ + wtI dual I)).σ x →
          ‖β‖ₑ ^ 2 * ‖x‖ₑ ^ 2 ≤ (R (μ + wtI dual I)).mass F.ν BI
            (fun g => (∏ a : Fin l, lA k r F.z g (Fin.castLE hl a)) ^ 2) x

def ScalarBound : Prop :=
  ∀ c : ℝ, 0 < c → ∃ Ch C₀ : ℝ, 0 < Ch ∧ ∀ (k r : ℕ) (P : Mat k r) lam (bv h q b : ℝ) R,
    Setup k r c Ch P lam bv h q R → C₀ * ((2 * r + k + 1 : ℕ) : ℝ) ^ 7 ≤ bv →
    ∀ (F : Flag k r) (κ : ℝ), F.Ok κ → F.Size lam bv b → 1 ≤ Tz k r F.z →
    ∀ (dual : Bool) (l : ℕ) (hl : l ≤ r + 1) μ, InPP lam (q - ((r + 1) * (r + 2) : ℕ)) μ →
      ∀ ι p ep, IsTensDec R dual P l μ ι p → IsHHNorm R dual l μ ι ep → ∀ B, F.Iso (R μ) B →
      ∀ I (BI : (R (μ + wtI dual I)).H → F.W) (β : ℂ), F.Iso _ BI →
        (∀ y ∈ smoothVecs (k := k) (r := r) (R (μ + wtI dual I)).σ, omB dual P F.z hl B (ι I y) = β • BI y) →
        ‖β‖ ≤ H1 k r (Tz k r F.z) κ b 4 bv ^ l

def CoefProduct : Prop :=
  ∀ (k r : ℕ) (P : Mat k r) (R : (Fin (2 * r + k + 1) → ℝ) → HRep k r) (dual : Bool) (l : ℕ) μ ι p ep,
    IsCayleyU k r (sgnCN k r) P → IsTensDec R dual P l μ ι p → IsHHNorm R dual l μ ι ep →
    ∀ x y : Idx k r l → (R μ).H, (R μ).SmT x → (R μ).SmT y → ∀ g ∈ UH (Hpk k r),
      (∀ v ∈ smoothVecs (k := k) (r := r) (R μ).σ, (R μ).σ g v ∈ smoothVecs (k := k) (r := r) (R μ).σ) →
      (∀ I : Idx k r l, ∀ v ∈ smoothVecs (k := k) (r := r) (R (μ + wtI dual I)).σ,
        (R (μ + wtI dual I)).σ g v ∈ smoothVecs (k := k) (r := r) (R (μ + wtI dual I)).σ) →
      (R μ).hh ((R μ).tens dual P g x) y = ∑ I, (ep I : ℂ) * ⟪p I y, (R (μ + wtI dual I)).σ g (p I x)⟫_ℂ

def HRep.Dg (A : HRep k r) (P : Mat k r) (x : Idx k r 1 → A.H) : Idx k r 1 → A.H :=
  fun b => -A.E P (el b) (el b) (x b)

def HRep.Off (A : HRep k r) (P : Mat k r) (x : Idx k r 1 → A.H) : Idx k r 1 → A.H :=
  fun b => -∑ c ∈ univ.erase b, A.E P (el b) (el c) (x c)

def HRep.KfT (A : HRep k r) {l : ℕ} (x : Idx k r l → A.H) : Prop := ∀ I, IsKFinHpk (k := k) (r := r) A.σ (x I)

def HRep.casK (A : HRep k r) (P : Mat k r) (v : A.H) : A.H :=
  ∑ a, ∑ b, if sgnCN k r a = sgnCN k r b then A.E P a b (A.E P b a v) else 0

def HRep.casG (A : HRep k r) (P : Mat k r) (v : A.H) : A.H := ∑ a, ∑ b, A.E P a b (A.E P b a v)

def omVec (dual : Bool) (P : Mat k r) (z : Fin (2 * r + k + 1) → ℂ) {l : ℕ} (hl : l ≤ r + 1) (I : Idx k r l) : ℂ :=
  if dual then (epsI I : ℂ) * star (omCoord P z hl I) else omCoord P z hl I

def omTens {H : Type} [SMul ℂ H] (dual : Bool) (P : Mat k r) (z : Fin (2 * r + k + 1) → ℂ) {l : ℕ} (hl : l ≤ r + 1)
    (v : H) : Idx k r l → H :=
  fun I => omVec dual P z hl I • v

def Dsgn (dual : Bool) (z z' : Fin (2 * r + k + 1) → ℂ) {l : ℕ} (hl : l ≤ r + 1) (g : Mat k r) : ℂ :=
  if dual then star (Dmin k r z z' g ⟨l, by omega⟩) else Dmin k r z z' g ⟨l, by omega⟩

def Flag.perInt (F : Flag k r) (A : HRep k r) (w v : A.H) (s : Mt k r) : F.W →L[ℂ] F.W :=
  ⟪v, A.σ (Matrix.of s) w⟫_ℂ • GlobalTheory.SgInf.PiS (psi k r F.z F.cψ) F.π (Matrix.of s)⁻¹

def Flag.IsPeriodMap (F : Flag k r) (A : HRep k r) (l : A.H → F.W) : Prop :=
  IsBesselMapSm F.z (psi k r F.z F.cψ) A.σ F.π l ∧
    ∀ w ∈ smoothVecs (k := k) (r := r) A.σ, ∀ v, IsKFinHpk (k := k) (r := r) A.σ v →
      Integrable (F.perInt A w v) F.μS ∧ ∫ s, F.perInt A w v s ∂F.μS = GlobalTheory.SgInf.rk1 (l w) (l v)

def PeriodIso : Prop :=
  ∀ c : ℝ, 0 < c → ∃ Ch : ℝ, 0 < Ch ∧ ∀ (k r : ℕ) (P : Mat k r) lam (bv h q : ℝ) R, Setup k r c Ch P lam bv h q R →
    ∀ (F : Flag k r) (κ : ℝ), F.Ok κ → ∀ μ, InPP lam q μ →
      (∃ l, F.IsPeriodMap (R μ) l) ∧
      ∀ l, F.IsPeriodMap (R μ) l → (∃ v ∈ smoothVecs (k := k) (r := r) (R μ).σ, l v ≠ 0) → ∀ w₀ : (R μ).H, w₀ ≠ 0 →
        F.Iso (R μ) (fun v => (Real.sqrt (fdegH F.μG (R μ).σ w₀) : ℂ) • l v)

def PeriodNonzero : Prop :=
  ∀ c : ℝ, 0 < c → ∃ Ch : ℝ, 0 < Ch ∧ ∀ (k r : ℕ) (P : Mat k r) lam (bv h q : ℝ) R, Setup k r c Ch P lam bv h q R →
    ∀ (F : Flag k r) (κ : ℝ), F.Ok κ → ∀ μ, InPP lam q μ →
      ∀ B₀, IsBesselMapSm F.z (psi k r F.z F.cψ) (R μ).σ F.π B₀ →
        (∃ v ∈ smoothVecs (k := k) (r := r) (R μ).σ, B₀ v ≠ 0) →
        ∀ l, F.IsPeriodMap (R μ) l → ∃ v ∈ smoothVecs (k := k) (r := r) (R μ).σ, l v ≠ 0

def IsoExists : Prop :=
  ∀ c : ℝ, 0 < c → ∃ Ch : ℝ, 0 < Ch ∧ ∀ (k r : ℕ) (P : Mat k r) lam (bv h q : ℝ) R, Setup k r c Ch P lam bv h q R →
    ∀ (F : Flag k r) (κ : ℝ), F.Ok κ → ∀ μ, InPP lam q μ →
      ∀ B₀, IsBesselMapSm F.z (psi k r F.z F.cψ) (R μ).σ F.π B₀ →
        (∃ v ∈ smoothVecs (k := k) (r := r) (R μ).σ, B₀ v ≠ 0) →
        ∃ a : ℂ, a ≠ 0 ∧ F.Iso (R μ) (fun v => a • B₀ v)

def CasimirSums : Prop :=
  ∀ (k r : ℕ) (P : Mat k r) (A : HRep k r) μ, IsCayleyU k r (sgnCN k r) P → IsHCParam μ → A.IsDSAt P μ →
    ∀ w, IsKFinHpk (k := k) (r := r) A.σ w →
      ((∑ a, ∑ b, if a ≠ b ∧ sgnCN k r a = sgnCN k r b then ‖A.E P a b w‖ ^ 2 else 0 : ℝ) : ℂ) =
        ⟪w, A.casK P w - ∑ a, A.E P a a (A.E P a a w)⟫_ℂ ∧
      ((∑ a, ∑ b, if sgnCN k r a ≠ sgnCN k r b then ‖A.E P a b w‖ ^ 2 else 0 : ℝ) : ℂ) =
        ⟪w, A.casK P w - A.casG P w⟫_ℂ

def VVStable : Prop :=
  ∀ (k r : ℕ) (c Ch : ℝ) (P : Mat k r) lam (bv h q : ℝ) R, 0 < c → 0 < Ch → Setup k r c Ch P lam bv h q R →
    ∀ μ, InPP lam (q - 1) μ → ∀ ι p, IsTensDec R true P 1 μ ι p → ∀ j : ℕ,
      (∃ S : Submodule ℂ (Idx k r 1 → (R μ).H), (S : Set _) = VV R P μ p j ∧ FiniteDimensional ℂ S) ∧
      (∀ x ∈ VV R P μ p j, (R μ).KfT x ∧ (R μ).EE P x ∈ VV R P μ p j ∧ ∀ s, ι s (p s x) ∈ VV R P μ p j) ∧
      ∀ φ : (Idx k r 1 → (R μ).H) → Idx k r 1 → (R μ).H, (∀ x, (R μ).KfT x → (R μ).KfT (φ x)) →
        (∀ (a : ℂ) x y, (R μ).KfT x → (R μ).KfT y → φ (a • x + y) = a • φ x + φ y) →
        (∀ t ∈ UH (Hpk k r), t ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ → ∀ x, (R μ).KfT x →
          φ ((R μ).tens true P t x) = (R μ).tens true P t (φ x)) →
        ∀ x ∈ VV R P μ p j, φ x ∈ VV R P μ p j

def DiagOff : Prop :=
  ∀ (k r : ℕ) (P : Mat k r) (A : HRep k r) μ (bs : ℝ), IsCayleyU k r (sgnCN k r) P → IsHCParam μ → A.IsDSAt P μ →
    (∀ a, |μ a| + ((2 * r + k + 1 : ℕ) : ℝ) ≤ bs) → ∀ j : ℕ,
      (∀ ν ω, ∀ w ∈ A.iso P ν, IsWtOn (Formalism.REAL.Kset (sgnCN k r)) (A.onJ P) ω w → ∀ c : Idx k r 1,
        A.Dg P (Pi.single c w) = ((-ω (el c) : ℝ) : ℂ) • (Pi.single c w : Idx k r 1 → A.H)) ∧
      (∀ ω, dist1 ω (lowK (sgnCN k r) μ) ≤ j + 2 → ∀ c,
        |-ω c - (-μ c + (1 - ((2 * r + k + 1 : ℕ) : ℝ)) / 2)| ≤ j + ((2 * r + k + 1 : ℕ) : ℝ) + 1) ∧
      ∀ x : Idx k r 1 → A.H, (∀ a, x a ∈ A.filt P μ (j + 2)) →
        nrm2 (A.Off P x) ≤ (((2 * r + k + 1 : ℕ) : ℝ) - 1) *
          (8 * (bs + (j + 2)) * (((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + (j + 2))) * nrm2 x

def OpNorms : Prop :=
  ∀ (k r : ℕ) (c Ch : ℝ) (P : Mat k r) lam (bv h q : ℝ) R, 0 < c → 0 < Ch → Setup k r c Ch P lam bv h q R →
    ∀ μ, InPP lam (q - 1) μ → ∀ ι p, IsTensDec R true P 1 μ ι p → ∀ j, HypJ k r bv j → ∀ x ∈ VV R P μ p j,
      nrm2 ((R μ).Off P x) ≤ (bv / 16) ^ 2 * nrm2 x ∧ nrm2 ((R μ).EE P x) ≤ (3 * bv) ^ 2 * nrm2 x ∧
      nrm2 (∑ s ∈ univ.filter (fun s : Idx k r 1 => k - 1 ≤ (el s).val), ι s (p s x)) ≤ (31 / 13) ^ 2 * nrm2 x

def SummandOrth : Prop :=
  ∀ (k r : ℕ) (c Ch : ℝ) (P : Mat k r) lam (bv h q : ℝ) R, 0 < c → 0 < Ch → Setup k r c Ch P lam bv h q R →
    ∀ (dual : Bool) (l : ℕ), l ≤ r + 1 → ∀ μ, InPP lam q μ → (∀ I : Idx k r l, InPP lam q (μ + wtI dual I)) →
      ∀ ι p, IsTensDec R dual P l μ ι p →
        (∀ I, ∃ t : ℝ, t ≠ 0 ∧ ∀ x ∈ smoothVecs (k := k) (r := r) (R (μ + wtI dual I)).σ,
          ∀ y ∈ smoothVecs (k := k) (r := r) (R (μ + wtI dual I)).σ,
            (R μ).hh (ι I x) (ι I y) = (t : ℂ) * ⟪y, x⟫_ℂ) ∧
        ∀ I J, I ≠ J → ∀ x ∈ smoothVecs (k := k) (r := r) (R (μ + wtI dual I)).σ,
          ∀ y ∈ smoothVecs (k := k) (r := r) (R (μ + wtI dual J)).σ, (R μ).hh (ι I x) (ι J y) = 0

def LastLength : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (g : Mat k r), inWb k r z → 0 < Tz k r z → g ∈ UH (Hpk k r) →
    Tz k r z ≤ lA k r z g (Fin.last r) ^ 2

def MomentLowA : Prop :=
  ∀ c : ℝ, 0 < c → ∃ Ch : ℝ, 0 < Ch ∧ ∀ (k r : ℕ) (P : Mat k r) lam (bv h q₀ b : ℝ) R, Setup k r c Ch P lam bv h q₀ R →
    ∀ (F : Flag k r) (κ : ℝ), F.Ok κ → F.Size lam bv b → ∀ (q : ℕ) μ, InPP lam (q₀ - q) μ → HypJ k r bv (2 * q) →
      ∀ B, F.Iso (R μ) B → ∀ w ∈ (R μ).iso P (lowK (sgnCN k r) μ),
        (R μ).mass F.ν B (fun g => lA k r F.z g 0 ^ (2 * q)) w ≤
          ENNReal.ofReal (H0 k r (Tz k r F.z) κ b 4 bv ^ (2 * q)) * ‖w‖ₑ ^ 2

def MomentLowB : Prop :=
  ∀ (k r : ℕ) (P : Mat k r) (A : HRep k r) μ (bs : ℝ) (F : Flag k r) (κ : ℝ), IsCayleyU k r (sgnCN k r) P →
    IsHCParam μ → A.IsDSAt P μ → (∀ a, |μ a| + ((2 * r + k + 1 : ℕ) : ℝ) ≤ bs) → F.Ok κ → ∀ B, F.Iso A B →
      ∀ (q : ℕ) (a : Fin r), ∀ w ∈ A.iso P (lowK (sgnCN k r) μ),
        A.mass F.ν B (fun g => (lA k r F.z g a.succ / lA k r F.z g a.castSucc) ^ (2 * q)) w ≤
          ENNReal.ofReal ((3 * ((2 * r + k + 1 : ℕ) : ℝ) * (bs + 2 * q) / κ) ^ (2 * q)) * ‖w‖ₑ ^ 2

def MinorCoef : Prop :=
  ∀ (k r : ℕ) (P : Mat k r) (A : HRep k r) (dual : Bool) (l : ℕ) (hl : l ≤ r + 1) (z z' : Fin (2 * r + k + 1) → ℂ),
    IsCayleyU k r (sgnCN k r) P → ∀ g ∈ UH (Hpk k r), ∀ v v' : A.H,
      Dsgn dual z z' hl g * ⟪v, A.σ g v'⟫_ℂ = A.hh (A.tens dual P g (omTens dual P z' hl v')) (omTens dual P z hl v)

def KFinProj : Prop :=
  ∀ (k r : ℕ) (c Ch : ℝ) (P : Mat k r) lam (bv h q : ℝ) R, 0 < c → 0 < Ch → Setup k r c Ch P lam bv h q R →
    ∀ (dual : Bool) (l : ℕ) (hl : l ≤ r + 1) μ, InPP lam q μ → (∀ I : Idx k r l, InPP lam q (μ + wtI dual I)) →
      ∀ ι p, IsTensDec R dual P l μ ι p → ∀ I,
        (∀ y, IsKFinHpk (k := k) (r := r) (R (μ + wtI dual I)).σ y → (R μ).KfT (ι I y)) ∧
        (∀ x, (R μ).KfT x → IsKFinHpk (k := k) (r := r) (R (μ + wtI dual I)).σ (p I x)) ∧
        ∀ z v, IsKFinHpk (k := k) (r := r) (R μ).σ v →
          IsKFinHpk (k := k) (r := r) (R (μ + wtI dual I)).σ (p I (omTens dual P z hl v))

def MinorProduct : Prop :=
  ∀ (k r : ℕ) (c Ch : ℝ) (P : Mat k r) lam (bv h q : ℝ) R, 0 < c → 0 < Ch → Setup k r c Ch P lam bv h q R →
    ∀ (dual : Bool) (l : ℕ) (hl : l ≤ r + 1) μ, InPP lam q μ → (∀ I : Idx k r l, InPP lam q (μ + wtI dual I)) →
      ∀ ι p ep, IsTensDec R dual P l μ ι p → IsHHNorm R dual l μ ι ep → ∀ (z z' : Fin (2 * r + k + 1) → ℂ) v v',
        IsKFinHpk (k := k) (r := r) (R μ).σ v → IsKFinHpk (k := k) (r := r) (R μ).σ v' → ∀ g ∈ UH (Hpk k r),
          Dsgn dual z z' hl g * ⟪v, (R μ).σ g v'⟫_ℂ =
            ∑ I, (ep I : ℂ) * ⟪p I (omTens dual P z hl v), (R (μ + wtI dual I)).σ g (p I (omTens dual P z' hl v'))⟫_ℂ

example (dual : Bool) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mat k r) : Dsgn dual z z' (Nat.zero_le _) g = 1 := by
  cases dual <;> simp [Dsgn, Dmin]

example : Dsgn (k := 1) (r := 0) false (Inh.z0 1) (Inh.z0 1) (l := 1) le_rfl 1 = -1 := by
  simp [Dsgn, Dmin, Zhat, fvec, herm, Inh.z0, bvec, wI, Hpk, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Pi.single_apply]

end GlobalTheory.Mom
