import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.KappaOffDiagonal
import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeGluingRadicals
import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AdaptSelf
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GoodLoc

noncomputable section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
namespace GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Gen
variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

def spH (S : HSpace E) : Formalism.HermitianLatticeCounting.S6.HermSpace E S.V where
  B := S.hT.flip
  herm x y := (a_herm y x).symm
  nondeg x h := S.nondeg.2 x h

theorem fv_cast (F : FlagG S r T) (a : Fin r) : F.fvec a.castSucc = F.e a := by
  rw [FlagG.fvec, Fin.snoc_castSucc]

theorem fv_last (F : FlagG S r T) : F.fvec (Fin.last r) = F.z := by
  rw [FlagG.fvec, Fin.snoc_last]

def frF (F : FlagG S r T) (hT : T ≠ 0) : Formalism.HermitianLatticeCounting.S6.FlagD (spH S) r where
  e := F.fvec
  T := T
  indep := by
    have h : (fun a : Fin r => F.fvec a.castSucc) = F.e := funext (fv_cast F)
    rw [h]; exact F.e_indep
  iso a b := by rw [fv_cast, fv_cast]; exact F.e_iso b a
  zperp a := by rw [fv_cast, fv_last]; exact p_symm_zero S (F.z_orth a)
  zz := by rw [fv_last]; exact F.z_norm
  hT := hT
end Gen

theorem tu_ne (D : D7) (u : D.what₂.Word) : ((Tu D u : ℕ) : D.host.E) ≠ 0 :=
  Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero
section Obj
variable {D : D7} {X : HidaSetting D}

abbrev HV (D : D7) : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E (VS D).V := spH (VS D)

def F0 (X : HidaSetting D) (u : D.what₂.Word) : Formalism.HermitianLatticeCounting.S6.FlagD (HV D) D.R.rS := frF (lf D (X.Fu u)).fl (tu_ne D u)

def Ft {Y : Full X} {u : D.what₂.Word} (t : GT Y u) : Formalism.HermitianLatticeCounting.S6.FlagD (HV D) D.R.rS :=
  frF (frq X t.rep).fl (tu_ne D u)

def dI (D : D7) : Ideal (𝓞 D.host.E) :=
  Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))

def AdT {Y : Full X} {u : D.what₂.Word} (t : GT Y u) (N : GlobalTheory.DegCnt.NF (HV D) D.R.rS) : Prop :=
  GlobalTheory.DegAsm.Adapt (F0 X u) (Ft t) (dI D) N

def omT {Y : Full X} {u : D.what₂.Word} (t : GT Y u) : ℝ := GlobalTheory.DegAsm.omI (F0 X u) (Ft t) (dI D) t.lam

def Std (D : D7) (large₂ : SizeData₂ D) : Prop :=
  ∃ C' Cl Cg cb Cw cT CT C0 : ℝ, Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0

def lossV (D : D7) : ℝ := (8 * D.host.v) ^ (2 * (D.R.rS + 1) ^ 2 * D.R.f)
end Obj

def HostC : Prop :=
  ∀ (D : D7) (large₂ : SizeData₂ D), Std D large₂ →
    Formalism.HermitianLatticesTheory.IsCMUnram D.host.E ∧ GlobalTheory.DegVol.IsPlaces (embS D) ∧ Formalism.HermitianLatticesTheory.vInv D.host.E = D.host.v ∧ 1 ≤ D.host.v ∧
    Formalism.HermitianLatticesTheory.fDeg D.host.E = D.R.f ∧ Fintype.card D.what₂.Tau = D.R.f ∧ Module.finrank ℚ D.host.E = 2 * D.R.f ∧
    dI D ≠ ⊥ ∧ (∀ x ∈ dI D, ∃ y ∈ dI D, (y : D.host.E) = star (x : D.host.E)) ∧
    (Ideal.absNorm (dI D) : ℝ) = (2 * D.host.v) ^ (2 * D.R.f) ∧
    Module.finrank D.host.E (VS D).V = 2 * D.R.rS + D.R.k + 1 ∧ 2 ≤ gS D ∧
    ∀ u : D.what₂.Word, (Tu D u).Prime ∧ ∀ P : Ideal (𝓞 D.host.E), P.IsMaximal → ((Tu D u : ℕ) : 𝓞 D.host.E) ∈ P →
      Ideal.absNorm P = Tu D u ∧ ((Tu D u : ℕ) : 𝓞 D.host.E) ∉ P ^ 2

def TermC : Prop :=
  ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Std D large₂ → ∀ (t : GT Y u) N, AdT t N →
    N.IsTerm (gS D) t.lam

def IdNFC : Prop :=
  ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Std D large₂ →
    ∀ Λ : Submodule (𝓞 D.host.E) (VS D).V, (Λ ∈ Y.what₂ u ∨ Λ = (VS D).L0) →
      ∃ N : GlobalTheory.DegCnt.NF (HV D) D.R.rS, N.F = F0 X u ∧ N.F' = F0 X u ∧ N.j = 0 ∧ N.T = Tu D u ∧ N.𝔡 = dI D ∧
        N.IsTerm (gS D) Λ ∧ N.Ref (GlobalTheory.HermLat.latL N.F N.F' Λ) = Λ ∧ (Λ = (VS D).L0 → N.ist = X.fY)

def EmbC : Prop :=
  ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (u : D.what₂.Word), Std D large₂ →
    ∃ (W : Submodule D.host.E (VS D).V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E W),
      GlobalTheory.DegAsm.IsEmb (F0 X u) HW W.subtype ∧ Module.finrank D.host.E W = D.R.k ∧ GlobalTheory.Mass.PD HW.B.flip

def LatticeNormalizationCondition : Prop :=
  ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Std D large₂ →
    ∀ (W : Submodule D.host.E (VS D).V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E W), GlobalTheory.DegAsm.IsEmb (F0 X u) HW W.subtype →
    ∀ Λ ∈ Y.what₂ u, GlobalTheory.Mass.IsIntLat HW.B.flip (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ) ∧
      Nonempty ((↥(Formalism.HermitianLatticesTheory.dual HW.B.flip (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ)) ⧸
        (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ).comap (Formalism.HermitianLatticesTheory.dual HW.B.flip (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ)).subtype)
          ≃ₗ[𝓞 D.host.E] (𝓞 D.host.E ⧸ Ideal.span {((Tu D u : ℕ) : 𝓞 D.host.E)}))

def FibC : Prop :=
  ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Std D large₂ → ∀ t₁ t₂ : GT Y u,
    t₁.lam = t₂.lam → GlobalTheory.DegAsm.FrEqv (F0 X u) t₁.lam (Ft t₁) (Ft t₂) →
      t₁.lam' = t₂.lam' ∧ ∃ n a : (VS D).V ≃ₗ[D.host.E] (VS D).V, n ∈ NLam t₁.lam (lf D (X.Fu u)) ∧
        a ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧ Formalism.HermitianLatticesTheory.gmap a t₁.lam' = t₁.lam' ∧ (∀ b, a ((F0 X u).e b) = (F0 X u).e b) ∧
        ∃ n' ∈ NLam t₁.lam' (lf D (X.Fu u)), t₂.lin = n * t₁.lin * a * n'

def FibCardC : Prop :=
  ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Std D large₂ → ∀ (t₀ : GT Y u) (s : Finset (GT Y u)),
    (∀ t ∈ s, t₀.lam = t.lam ∧ GlobalTheory.DegAsm.FrEqv (F0 X u) t₀.lam (Ft t₀) (Ft t)) →
      (s.card : ℝ) * wRow D (X.Fu u) t₀.lam' ≤ 1

def InjC : Prop :=
  ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Std D large₂ →
    ∀ (W : Submodule D.host.E (VS D).V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E W), GlobalTheory.DegAsm.IsEmb (F0 X u) HW W.subtype →
    ∀ t₁ t₂ : GT Y u, (∃ N, AdT t₁ N) → t₁.lam = t₂.lam → GlobalTheory.DegAsm.FrEqv (F0 X u) t₁.lam (Ft t₁) (Ft t₂) →
      ∀ h : W ≃ₗ[D.host.E] W, GlobalTheory.DegAsm.IsH (F0 X u) (Ft t₁) W.subtype t₁.lin h →
        GlobalTheory.DegAsm.IsH (F0 X u) (Ft t₂) W.subtype t₂.lin h → t₁ = t₂

def CompatC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), ∀ p ∈ (Y.tO u u).allPairs Set.univ,
    p.1.lam = p.2.lam ∧ p.1.lam' = p.2.lam' ∧
      ∀ x ∈ p.1.lam ⊓ GlobalTheory.HermLat.rs (𝓞 D.host.E) (GlobalTheory.HermLat.perp (HV D) (F0 X u).X),
        p.2.lin (p.1.lin.symm x) - x ∈ GlobalTheory.HermLat.smulLat ((gS D : ℕ) : 𝓞 D.host.E) p.1.lam ⊔
          (p.1.lam ⊓ GlobalTheory.HermLat.rs (𝓞 D.host.E) (F0 X u).X)

def RowsOrbC : Prop :=
  ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Std D large₂ →
    ∀ (W : Submodule D.host.E (VS D).V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E W), GlobalTheory.DegAsm.IsEmb (F0 X u) HW W.subtype →
    ∀ φ : Submodule (𝓞 D.host.E) W → ℝ≥0∞, (∀ (s : Formalism.HermitianLatticesTheory.isom HW.B.flip) M, φ (s • M) = φ M) → ∀ Λ₀ ∈ Y.what₂ u,
      ∑ Λ ∈ (Y.what₂ u).filter (fun Λ => GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ ∈
          Formalism.HermitianLatticesTheory.genus HW.B.flip (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ₀)),
          ENNReal.ofReal (wRow D (X.Fu u) Λ) * φ (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ) =
        ((Tu D u - 1 : ℕ) : ℝ≥0∞) ^ D.R.f * GlobalTheory.Mass.orbSum (Formalism.HermitianLatticesTheory.isom HW.B.flip)
          (Formalism.HermitianLatticesTheory.genus HW.B.flip (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ₀)) φ

def RowsMeanC : Prop :=
  ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Std D large₂ →
    ∀ (W : Submodule D.host.E (VS D).V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E W), GlobalTheory.DegAsm.IsEmb (F0 X u) HW W.subtype →
    ∀ (φ : Submodule (𝓞 D.host.E) W → ℝ≥0∞) (B : ℝ), 0 ≤ B → (∀ (s : Formalism.HermitianLatticesTheory.isom HW.B.flip) M, φ (s • M) = φ M) →
      (∀ Λ ∈ Y.what₂ u, GlobalTheory.Mass.orbSum (Formalism.HermitianLatticesTheory.isom HW.B.flip)
          (Formalism.HermitianLatticesTheory.genus HW.B.flip (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ)) φ ≤
        ENNReal.ofReal (Formalism.HermitianLatticesTheory.mass HW.B.flip (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ) * B)) →
      ∑ Λ ∈ Y.what₂ u, ENNReal.ofReal (wRow D (X.Fu u) Λ) * φ (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ) ≤
        ENNReal.ofReal (massRows D (X.Fu u) (Y.what₂ u) * B)

def GramC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (C : Choice X 1) (τ : D.what₂.Tau),
    GlobalTheory.DegVol.IsReal (HV D) D.R.k D.R.rS (embS D τ) (phiV C τ) ∧ ∀ t : GT Y u,
      gamT C t τ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) ∧ (∀ y, gamT C t τ *ᵥ phiV C τ y = phiV C τ (t.lin y)) ∧
      ∀ l : Fin (D.R.rS + 1), ‖Formalism.QuantumDeterminants.Dmin D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u τ) (gamT C t τ) l.castSucc‖ =
        absReal D.host.rdE (embS D τ) D.R.rS l.val (Dl (lf D (X.Fu u)).fl (frq X t.rep).fl l.val)

def FrameC : Prop :=
  ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (C : Choice X 1), Std D large₂ →
    ∀ (t : GT Y u) N, AdT t N → ∃ (β : Fin D.R.rS → ℕ) (n₁ g n₂ : D.what₂.Tau → MatKR D.R.k D.R.rS), ∀ τ,
      n₁ τ ∈ Formalism.QuantumDeterminants.Nset D.R.k D.R.rS ∧ n₂ τ ∈ Formalism.QuantumDeterminants.Nset D.R.k D.R.rS ∧ (gamT C t τ)⁻¹ = n₁ τ * g τ * n₂ τ ∧
      GlobalTheory.DegVol.IsFrameOf N D.R.k (embS D τ) (2 * D.host.v) β (fun y => n₂ τ *ᵥ phiV C τ y)
        (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u τ) (g τ)

def CovTC : Prop :=
  ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (C : Choice X 1), Std D large₂ →
    ∀ (t : GT Y u) N, AdT t N → ∀ (μ : D.what₂.Tau → Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) (K : Set X.B.I.Ginf),
      (∀ τ, GlobalTheory.Amp.IsNormalFormStabilizerMeasure D.R.k D.R.rS N.j_le (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u τ) (gamT C t τ)⁻¹ 1 (μ τ)) → FundR t K →
      Measure.pi μ (trI C '' K) ≤
        ENNReal.ofReal (N.om t.lam * (D.host.v ^ (D.R.k * (D.R.rS - N.j) * D.R.f) * lossV D))

def CovNC : Prop :=
  ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (C : Choice X 1), Std D large₂ →
    covN C Y u ≠ ⊤ ∧ 1 ≤ (covN C Y u).toReal * lossV D
end GlobalTheory.TypeAsm
