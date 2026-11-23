import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.RedTheta
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.IsParI

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Eqv MeasureTheory
  IsDedekindDomain NumberField

namespace Formalism.IndefR.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsQuotFrame (T : HSp D) {r : ℕ} (C C' : Matrix (Fin T.rank) (Fin r) D.host.E) (T0 : HSp D)
    (B0 : Matrix (Fin T.rank) (Fin T0.rank) D.host.E) : Prop :=
  IsIsoFrame T C ∧
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C' * T.gram * C' = 0 ∧
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C' * T.gram * C = 1 ∧
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * T.gram * B0 = 0 ∧
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C' * T.gram * B0 = 0 ∧
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B0 * T.gram * B0 = T0.gram ∧
    T.rank = 2 * r + T0.rank

def desc (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {r : ℕ} (C : Matrix (Fin T.rank) (Fin r) D.host.E)
    (μ : Measure (Mx D r S.rank)) (𝓕 : Set (Mx D r S.rank)) (T0 : HSp D)
    (B0 : Matrix (Fin T.rank) (Fin T0.rank) D.host.E) (f : WO S T → ℂ) : WO S T0 → ℂ :=
  fun x0 => Red ψ S T C μ 𝓕 f (embI S T B0 x0)

def IsLeviEmb (T : HSp D) {r : ℕ} (C C' : Matrix (Fin T.rank) (Fin r) D.host.E) (T0 : HSp D)
    (B0 : Matrix (Fin T.rank) (Fin T0.rank) D.host.E) (h0 : GA D T0) (h : GA D T) : Prop :=
  HMul.hMul (mt T h) (C.map (incA D)) = C.map (incA D) ∧
    HMul.hMul (mt T h) (C'.map (incA D)) = C'.map (incA D) ∧
    HMul.hMul (mt T h) (B0.map (incA D)) = HMul.hMul (B0.map (incA D)) (mt T0 h0)

def IsDescOf (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {r : ℕ} (C C' : Matrix (Fin T.rank) (Fin r) D.host.E)
    (T0 : HSp D) (B0 : Matrix (Fin T.rank) (Fin T0.rank) D.host.E) (μ : Measure (Mx D r S.rank))
    (𝓕 : Set (Mx D r S.rank)) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (om0 : GA D S × GA D T0 →* Module.End ℂ (WO S T0 → ℂ)) : Prop :=
  ∀ g h0 h, IsLeviEmb T C C' T0 B0 h0 h → ∀ f, IsThetaFunO ψ S T f →
    desc ψ S T C μ 𝓕 T0 B0 (om (g, h) f) = om0 (g, h0) (desc ψ S T C μ 𝓕 T0 B0 f)

def hv (T : HSp D) (x y : Fin T.rank → AE D) : AE D :=
  ∑ i, ∑ j, cA D (x i) * incA D (T.gram i j) * y j

def rowH (T : HSp D) (x : Fin T.rank → AE D) (k : Fin T.rank) : AE D :=
  ∑ j, cA D (x j) * incA D (T.gram j k)

def transvMat (T : HSp D) (w v' : Fin T.rank → AE D) : Matrix (Fin T.rank) (Fin T.rank) (AE D) :=
  fun i k => (if i = k then 1 else 0) + w i * rowH T v' k - v' i * rowH T w k -
    incA D (1 / 2) * hv T v' v' * w i * rowH T w k

def DescTheta (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (S T : HSp D) (r : ℕ)
    (C C' : Matrix (Fin T.rank) (Fin r) D.host.E) (T0 : HSp D) (B0 : Matrix (Fin T.rank) (Fin T0.rank) D.host.E),
    IsQuotFrame T C C' T0 B0 →
    ∀ (μ : Measure (Mx D r S.rank)) (𝓕 : Set (Mx D r S.rank)), μ.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratMx D r S.rank) 𝓕 μ → ∀ f, IsThetaFunO ψ S T f →
        IsThetaFunO ψ S T0 (desc ψ S T C μ 𝓕 T0 B0 f)

def DescWeil (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    Formalism.IndefR.Fin.SvNSchurO ψ S T →
    ∀ (r : ℕ) (C C' : Matrix (Fin T.rank) (Fin r) D.host.E) (T0 : HSp D)
      (B0 : Matrix (Fin T.rank) (Fin T0.rank) D.host.E), IsQuotFrame T C C' T0 B0 →
    ∀ (μ : Measure (Mx D r S.rank)) (𝓕 : Set (Mx D r S.rank)), μ.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratMx D r S.rank) 𝓕 μ →
      ∃ om0 : GA D S × GA D T0 →* Module.End ℂ (WO S T0 → ℂ),
        IsWeilDatumO ψ S T0 χS χT om0 ∧ IsDescOf ψ S T C C' T0 B0 μ 𝓕 om om0

def ParabRedN (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    Formalism.IndefR.Fin.SvNSchurO ψ S T →
    ∀ (r : ℕ) (C : Matrix (Fin T.rank) (Fin r) D.host.E), IsIsoFrame T C →
      ∀ (μ : Measure (Mx D r S.rank)) (𝓕 : Set (Mx D r S.rank)), μ.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratMx D r S.rank) 𝓕 μ →
        ∀ n ∈ NI T C, ∀ f, IsThetaFunO ψ S T f → ∀ w,
          Red ψ S T C μ 𝓕 (om (1, n) f) w = Red ψ S T C μ 𝓕 f (actO S T 1 n⁻¹ w)

def ParabolicReductionTransvection (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    Formalism.IndefR.Fin.SvNSchurO ψ S T →
    ∀ (r : ℕ) (C : Matrix (Fin T.rank) (Fin r) D.host.E), IsIsoFrame T C →
      ∀ (μ : Measure (Mx D r S.rank)) (𝓕 : Set (Mx D r S.rank)), μ.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratMx D r S.rank) 𝓕 μ →
        ∀ m : GA D T, IsParI T C m → ∀ (α : Fin r → D.host.E) (β : Fin r → AE D),
          ∑ i, β i * incA D (α i) = 0 →
          HMul.hMul (mt T m) (C.map (incA D)) =
            HMul.hMul (C.map (incA D)) (1 + Matrix.vecMulVec (fun i => incA D (α i)) β) →
          ∀ f, IsThetaFunO ψ S T f → ∀ w,
            Red ψ S T C μ 𝓕 (om (1, m) f) w = Red ψ S T C μ 𝓕 f (actO S T 1 m⁻¹ w)

def MixedLaw (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    Formalism.IndefR.Fin.SvNSchurO ψ S T →
    ∀ (r : ℕ) (C C' : Matrix (Fin T.rank) (Fin r) D.host.E) (T0 : HSp D)
      (B0 : Matrix (Fin T.rank) (Fin T0.rank) D.host.E), IsQuotFrame T C C' T0 B0 →
    ∀ (μ : Measure (Mx D r S.rank)) (𝓕 : Set (Mx D r S.rank)), μ.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratMx D r S.rank) 𝓕 μ →
      ∀ om0 : GA D S × GA D T0 →* Module.End ℂ (WO S T0 → ℂ), IsDescOf ψ S T C C' T0 B0 μ 𝓕 om om0 →
        ∀ g h0 h, IsLeviEmb T C C' T0 B0 h0 h → ∀ f, IsThetaFunO ψ S T f →
          ∀ (b : Mx D r S.rank) (x0 : WO S T0),
            Red ψ S T C μ 𝓕 (om (g, h) f) (embI S T C' b + embI S T B0 x0) =
              om0 (g, h0) (fun x => Red ψ S T C μ 𝓕 f (embI S T C' (HMul.hMul b (mt S g)) + embI S T B0 x)) x0

def TransvRed (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    Formalism.IndefR.Fin.SvNSchurO ψ S T →
    ∀ (r : ℕ) (C C' : Matrix (Fin T.rank) (Fin r) D.host.E) (T0 : HSp D)
      (B0 : Matrix (Fin T.rank) (Fin T0.rank) D.host.E), IsQuotFrame T C C' T0 B0 →
    ∀ (μ : Measure (Mx D r S.rank)) (𝓕 : Set (Mx D r S.rank)), μ.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratMx D r S.rank) 𝓕 μ →
      ∀ (α : Fin r → D.host.E) (v' : Fin T.rank → AE D),
        hv T (fun i => incA D (C.mulVec α i)) v' = 0 →
        ∀ E : GA D T, mt T E = transvMat T (fun i => incA D (C.mulVec α i)) v' →
        ∀ b : Mx D r S.rank, (∀ j, ∑ i, incA D ((D.sp.cm.sig : D.host.E →+* D.host.E) (α i)) * b i j = 0) →
        ∀ f, IsThetaFunO ψ S T f → ∀ x0 : WO S T0,
          Red ψ S T C μ 𝓕 (om (1, E) f) (embI S T C' b + embI S T B0 x0) =
            Red ψ S T C μ 𝓕 f (embI S T C' b + embI S T B0 x0)

example (T : HSp D) {r : ℕ} (C C' : Matrix (Fin T.rank) (Fin r) D.host.E) (T0 : HSp D)
    (B0 : Matrix (Fin T.rank) (Fin T0.rank) D.host.E) : IsLeviEmb T C C' T0 B0 1 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [Formalism.L2.Theta.mt, map_one]

example (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {r : ℕ} (C C' : Matrix (Fin T.rank) (Fin r) D.host.E)
    (T0 : HSp D) (B0 : Matrix (Fin T.rank) (Fin T0.rank) D.host.E) (μ : Measure (Mx D r S.rank))
    (𝓕 : Set (Mx D r S.rank)) : IsDescOf ψ S T C C' T0 B0 μ 𝓕 1 1 := by
  intro g h0 h _ f _
  simp

end Formalism.IndefR.Mi

end
