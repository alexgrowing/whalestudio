import Formalism.SharpRestriction.CuspSpanNormBounds.WeightedMirrorLevelOperator

noncomputable section

namespace Formalism.MainNotions.S.UnitaryLevelOperators

section Gauge

open Matrix MeasureTheory TensorProduct
open scoped ContDiff
open Formalism.QuantumDeterminants Formalism.MainNotions.S.TopsChoicePartA

def stQ_cap : Prop :=
  CapCentralH ∧ CapLeftH ∧ CapHWH ∧ CapComatrix ∧ QMinorLeft ∧ GlRelAd ∧ EabHGl ∧ EabHTransport

def stQ_anti : Prop :=
  ∀ (n t : ℕ) (ε : Fin n → Bool) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (H P Q : Matrix (Fin n) (Fin n) ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E) (a b : Fin t → Fin n)
    (σ : Equiv.Perm (Fin t)) (u : ℂ) (g : Matrix (Fin n) (Fin n) ℂ),
    Q * P = 1 → P * Q = 1 → H = Pᴴ * Formalism.REAL.Jm ε * P → SmoothOnH H f → inUH H g →
      qminorOp (EabH H) (a ∘ σ) b u f g = ((Equiv.Perm.sign σ : ℤ) : ℂ) • qminorOp (EabH H) a b u f g ∧
      qminorOp (EabH H) a (b ∘ σ) u f g = ((Equiv.Perm.sign σ : ℤ) : ℂ) • qminorOp (EabH H) a b u f g

def stQ_branch : Prop :=
  ∀ (L : Lev) (u : Fin (L.k0 + 1) → ℝ) (g : Mat L.k0 L.r), L.Std →
    Formalism.MainNotions.S.IsHCTypeW (L.k0 + 1) L.r L.z' u L.π' → g ∈ UH (Hpk (L.k0 + 1) L.r) →
    ∀ ρ : Fin L.k0 → ℝ, (L.isoSub g ρ ≠ ⊥ ↔ (Interlace u ρ ∧ ∀ j, ∃ m : ℤ, ρ j = m + ((L.k0 : ℝ) - 1) / 2)) ∧
      (L.isoSub g ρ ≠ ⊥ → Formalism.MainNotions.S.IsKTypeOf (Formalism.MainNotions.S.allPos L.k0)
        (fun h => L.π' (L.frameU g * L.blockU h * (L.frameU g)⁻¹)) (lowK (Formalism.MainNotions.S.allPos L.k0) ρ) (L.isoSub g ρ))

def stQ_wigner : Prop :=
  ∀ (k : ℕ) (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [FiniteDimensional ℂ H']
    (σ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ → (H →L[ℂ] H))
    (σ' : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ → (H' →L[ℂ] H'))
    (τ : Fin (k + 1) → ℝ) (s : Fin (k + 1)) (u : Fin k → ℝ)
    (Φ : TensorProduct ℂ H (Fin (k + 1) → ℂ) →ₗ[ℂ] H'),
    Formalism.MainNotions.S.IsHCTypeU (k + 1) τ σ → Formalism.MainNotions.S.IsHCTypeU (k + 1) (τ + Pi.single s 1) σ' →
    (∀ g ∈ Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos (k + 1)), ∀ (v : H) (x : Fin (k + 1) → ℂ),
      Φ (σ g v ⊗ₜ (g *ᵥ x)) = σ' g (Φ (v ⊗ₜ x))) → Φ ≠ 0 →
    (∀ j, ∃ m : ℤ, u j = m + ((k : ℝ) - 1) / 2) →
      ((∃ v ∈ isoK σ u, ∃ v' ∈ isoK σ' u,
          inner ℂ v' (Φ (v ⊗ₜ (Pi.single (Fin.last k) 1 : Fin (k + 1) → ℂ))) ≠ (0 : ℂ)) ↔
        (Interlace τ u ∧ Interlace (τ + Pi.single s 1) u))

def stA_gauge : Prop :=
  (∀ (L : Lev) (u u' : Fin (L.k0 + 1) → ℝ), L.Std → L.HC u u' → ∃ R, L.IsRadQQ R) ∧
  ∀ (L : Lev) (pb : Mat L.k0 (L.r + 1) → (L.Wp →L[ℂ] L.Wp)) (pb' : Mat L.k0 (L.r + 1) → (L.Wq →L[ℂ] L.Wq))
    (u u' : Fin (L.k0 + 1) → ℝ),
    L.Std → (L.up pb pb').Std → L.Compat pb pb' → (L.up pb pb').HC u u' →
      (∃ R, L.IsRadQQ R) ∧
      ∀ R : ℂ → Matrix (Fin 2) (Fin 2) L.POp, L.IsRadQQ R →
        (L.up pb pb').IsRadQQ (fun Y => omMul (omMul (TmatStar (0 : Fin (L.r + 1 + 1)) Y) (liftMat (R Y)))
          (Tmat (0 : Fin (L.r + 1 + 1)) Y))

def stA_herm (C : ℝ) : Prop :=
  ∀ (L : Lev) (u u' : Fin (L.k0 + 1) → ℝ) (h : L.Haar) (A : ℝ) (mm : ℕ),
    L.Std → L.HC u u' → h.Ok → Big C L 0 A mm →
      ∀ R, L.IsRadQQ R → ∀ Y : ℝ, L.HermOn (L.ImgK h A mm) (R (Y : ℂ))

def stA_capelli : Prop :=
  ∀ (Lt : Lev) (i r' : ℕ) (hir : i + r' = Lt.r) (u u' : Fin (Lt.k0 + 1) → ℝ),
    Lt.Std → Lt.HC u u' → (Lt.down i r' hir).Std →
      ∀ R, (Lt.down i r' hir).IsRadQQ R → ∀ Y : ℂ,
        Lt.Rad (Lt.Cap Y) (fun φ => ∑ a : Fin 2, ∑ b : Fin 2,
          TprodStar (m := Lt.r) Y i (by omega) 0 a
            (Lt.liftDown i r' hir (R Y a b) (Tprod (m := Lt.r) Y i (by omega) b 0 φ)))

def cuspSpanTopCondition : Prop :=
  ∀ (L : Lev) (u u' : Fin (L.k0 + 1) → ℝ), L.r = 0 → L.Std → L.HC u u' →
    ∀ R, L.IsRadQQ R →
      (∀ (Y : ℂ), ∀ φ ∈ L.Img, ∀ p ∈ BDom (L.k0 + 1) L.r L.z L.z', ∀ ρ : Fin L.k0 → ℝ,
        L.lineP (L.pt p) ρ (R Y 1 1 φ p) = ((L.GGx p : ℂ) * xPoly ρ Y) • L.lineP (L.pt p) ρ (φ p)) ∧
      (∃ Ac : Fin (L.k0 + 2) → L.POp, ∀ (Y : ℂ), ∀ φ ∈ L.Img, ∀ p ∈ BDom (L.k0 + 1) L.r L.z L.z',
        R Y 0 0 φ p = Y ^ (L.k0 + 2) • φ p + ∑ j : Fin (L.k0 + 2), Y ^ (j : ℕ) • Ac j φ p) ∧
      (∃ Bc : Fin (L.k0 + 1) → L.POp, ∀ (Y : ℂ), ∀ φ ∈ L.Img, ∀ p ∈ BDom (L.k0 + 1) L.r L.z L.z',
        R Y 0 1 φ p = (-(Y ^ (L.k0 + 1) * zOf p)) • φ p + ∑ j : Fin (L.k0 + 1), Y ^ (j : ℕ) • Bc j φ p) ∧
      (∃ Bc : Fin (L.k0 + 1) → L.POp, ∀ (Y : ℂ), ∀ φ ∈ L.Img, ∀ p ∈ BDom (L.k0 + 1) L.r L.z L.z',
        R Y 1 0 φ p = (-(Y ^ (L.k0 + 1) * star (zOf p))) • φ p + ∑ j : Fin (L.k0 + 1), Y ^ (j : ℕ) • Bc j φ p)

def stA_signs : Prop :=
  ∀ (k0 : ℕ) (u u' : Fin (k0 + 1) → ℝ) (T T' : ℝ) (I : Set ℝ), 0 < T → 0 < T' → Formalism.MainNotions.S.IsCutS u u' I →
    (∃ ρ : Fin k0 → ℝ, Interlace u ρ ∧ Interlace u' ρ) →
      (∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ ρ : Fin k0 → ℝ, Interlace u ρ → Interlace u' ρ → ∀ Y ∈ I,
        0 < s * (xPoly ρ (Y : ℂ)).re ∧ 0 < s * (xPoly ρ ((Y : ℂ) + 1)).re ∧ 0 < s * (xPoly ρ ((Y : ℂ) - 1)).re) ∧
      ∀ Y ∈ I, 0 < (qPoly T T' u u' (Y : ℂ)).re

def stA (C : ℝ) : Prop := stA_gauge ∧ stA_herm C ∧ stA_capelli ∧ cuspSpanTopCondition ∧ stA_signs

def stB_rtt : Prop :=
  ∀ (L : Lev) (u u' : Fin (L.k0 + 1) → ℝ), L.Std → L.HC u u' → ∀ R, L.IsRadQQ R →
    ∀ Y Y' : ℂ, Y' - Y ≠ 1 →
      EqOn' L.Img L.BD (omMul (omMul (smat (Rh (Y' - Y))) (t1 (R Y'))) (t2 (R Y)))
        (omMul (omMul (t2 (R Y)) (t1 (R Y'))) (smat (Rh (Y' - Y))))

def stB_det : Prop :=
  ∀ (L : Lev) (u u' : Fin (L.k0 + 1) → ℝ), L.Std → L.HC u u' → ∀ R, L.IsRadQQ R → ∀ Y : ℂ,
    EqOn' L.Img L.BD (omMul (omMul (R (Y + 1)).transpose (smat J2)) (R Y)) (smat (qPoly L.T L.T' u u' Y • J2)) ∧
    EqOn' L.Img L.BD (omMul (omMul (R Y) (smat J2)) (R (Y + 1)).transpose) (smat (qPoly L.T L.T' u u' Y • J2))

def stB : Prop := stB_rtt ∧ stB_det

def stC_module (C : ℝ) : Prop :=
  ∀ (L : Lev) (u u' : Fin (L.k0 + 1) → ℝ) (I : Set ℝ), HypC L u u' I →
    ∀ R, L.IsRadQQ R → ∀ w : Word, Generic w →
      (∀ (h : L.Haar) (A : ℝ) (mm : ℕ), h.Ok → Big C L w.length A mm → ∀ Y : ℝ, OffPoles w (Y : ℂ) →
        L.HermOn (L.ImgK h A mm)
          (omMul (actOnPositions (L.wmod R (sCut u u' I) u u' w).RR) ((L.wmod R (sCut u u' I) u u' w).TT (Y : ℂ)))) ∧
      (∀ Y Y' : ℂ, OffPoles w Y → OffPoles w Y' → Y' - Y ≠ 1 →
        EqOn' L.Img L.BD
          (omMul (omMul (Rh12 (Y' - Y)) (one_le_card_tops ((L.wmod R (sCut u u' I) u u' w).TT Y')))
            (tensorSecondPosition ((L.wmod R (sCut u u' I) u u' w).TT Y)))
          (omMul (omMul (tensorSecondPosition ((L.wmod R (sCut u u' I) u u' w).TT Y)) (one_le_card_tops ((L.wmod R (sCut u u' I) u u' w).TT Y')))
            (Rh12 (Y' - Y)))) ∧
      (∀ Y : ℂ, OffPoles w Y → OffPoles w (Y + 1) →
        EqOn' L.Img L.BD (omMul (omMul (tr0 ((L.wmod R (sCut u u' I) u u' w).TT (Y + 1))) (onPosition0 J2))
            ((L.wmod R (sCut u u' I) u u' w).TT Y)) (onPosition0 ((L.wmod R (sCut u u' I) u u' w).q Y • J2)) ∧
        EqOn' L.Img L.BD (omMul (omMul ((L.wmod R (sCut u u' I) u u' w).TT Y) (onPosition0 J2))
            (tr0 ((L.wmod R (sCut u u' I) u u' w).TT (Y + 1)))) (onPosition0 ((L.wmod R (sCut u u' I) u u' w).q Y • J2)))

def stC_rrherm (C : ℝ) : Prop :=
  ∀ (L : Lev) (u u' : Fin (L.k0 + 1) → ℝ) (I : Set ℝ), HypC L u u' I →
    ∀ R, L.IsRadQQ R → ∀ w : Word, Generic w →
      ∀ (h : L.Haar) (A : ℝ) (mm : ℕ), h.Ok → Big C L w.length A mm →
        L.HermOn (L.ImgK h A mm) (L.wmod R (sCut u u' I) u u' w).RR

def stC_tele : Prop :=
  ∀ (L : Lev) (pb : Mat L.k0 (L.r + 1) → (L.Wp →L[ℂ] L.Wp)) (pb' : Mat L.k0 (L.r + 1) → (L.Wq →L[ℂ] L.Wq))
    (u u' : Fin (L.k0 + 1) → ℝ) (I : Set ℝ),
    L.Std → L.Compat pb pb' → HypC (L.up pb pb') u u' I →
      ∀ Rs, L.IsRadQQ Rs → ∀ Rb, (L.up pb pb').IsRadQQ Rb → ∀ w : Word, Generic w →
        EqOn' (L.up pb pb').Img (L.up pb pb').BD
          (omMul (omMul (bTstar (0 : Fin (L.r + 1 + 1)) w) (liftOM (L.wmod Rs (sCut u u' I) u u' w).RR))
            (bT (0 : Fin (L.r + 1 + 1)) w))
          ((L.up pb pb').wmod Rb (sCut u u' I) u u' w).RR

def stC_entry : Prop :=
  ∀ (L : Lev) (u u' : Fin (L.k0 + 1) → ℝ) (I : Set ℝ), HypC L u u' I →
    ∀ R, L.IsRadQQ R → ∀ w : Word, Generic w → ∀ φ ∈ L.Img, ∀ x ∈ L.BD,
      (L.wmod R (sCut u u' I) u u' w).RR (e1s _) (e1s _) φ x =
        capProd ((sCut u u' I : ℝ) : ℂ) (fun Y => R Y 0 0) w φ x

def stC_dual (C : ℝ) : Prop :=
  ∀ (L : Lev) (u u' : Fin (L.k0 + 1) → ℝ) (I : Set ℝ), HypC L u u' I →
    ∀ R, L.IsRadQQ R → ∀ (h : L.Haar) (A : ℝ) (mm : ℕ), h.Ok →
    ∀ (w : Word) (Y : ℝ), Big C L (w.length + 1) A mm → Generic ((true, Y) :: w) → Generic ((false, Y + 1) :: w) →
      (L.wmod R (sCut u u' I) u u' w).q (Y : ℂ) ≠ 0 →
      L.PosOn (L.ImgK h A mm) (L.wmod R (sCut u u' I) u u' ((true, Y) :: w)).RR →
      ∀ x₁ x₂ : AuxiliarySlotStates (w.length + 1) → L.PF, (∀ α, x₁ α ∈ L.ImgK h A mm) → (∀ α, x₂ α ∈ L.ImgK h A mm) →
        Complex.normSq (L.form (JRR (L.wmod R (sCut u u' I) u u' w).RR) x₁ x₂) ≤
          (L.form (L.wmod R (sCut u u' I) u u' ((true, Y) :: w)).RR x₁ x₁).re *
            (L.form (L.wmod R (sCut u u' I) u u' ((false, Y + 1) :: w)).RR x₂ x₂).re /
              ((L.wmod R (sCut u u' I) u u' w).q (Y : ℂ)).re

def cuspSpanWaveCondition : Prop :=
  ∀ (L : Lev) (u u' : Fin (L.k0 + 1) → ℝ) (I : Set ℝ), HypC L u u' I →
    ∀ R, L.IsRadQQ R → ∀ w : Word, Generic w → ∀ s : ℂ,
      EqOn' L.Img L.BD (omMul (omMul (VopStar s w) (L.wmod R (sCut u u' I) u u' w).RR) (Vop s w))
        (L.wmod R (sCut u u' I) u u' w).RR ∧
      ∀ Y : ℂ, OffPoles w Y →
        EqOn' L.Img L.BD (omMul (omMul (actOnPositions (VopInv s w)) ((L.wmod R (sCut u u' I) u u' w).TT Y)) (actOnPositions (Vop s w)))
          (omMul (omMul (onPosition0 (Us s)ᴴ) ((L.wmod R (sCut u u' I) u u' w).TT Y)) (onPosition0 (Us s)))

def stC (C : ℝ) : Prop := stC_module C ∧ stC_rrherm C ∧ stC_tele ∧ stC_entry ∧ stC_dual C ∧ cuspSpanWaveCondition

def stD (C : ℝ) : Prop :=
  ∀ (Lt : Lev) (u u' : Fin (Lt.k0 + 1) → ℝ) (I : Set ℝ) (hr : Lt.r + 0 = Lt.r),
    HypC Lt u u' I → HypC (Lt.down Lt.r 0 hr) u u' I →
    ∀ w : Word, Admissible I w →
      ∃ (F : Matrix (AuxiliarySlotStates w.length) (AuxiliarySlotStates w.length) (Lt.down Lt.r 0 hr).POp)
        (c : AuxiliarySlotStates w.length → (Fin Lt.k0 → ℝ) → ℝ),
        (Lt.down Lt.r 0 hr).IsTriDiff F ∧ (∀ α ρ, 0 < c α ρ) ∧
        (∀ R, (Lt.down Lt.r 0 hr).IsRadQQ R → ∀ (h : (Lt.down Lt.r 0 hr).Haar) (A : ℝ) (mm : ℕ), h.Ok →
          Big C Lt w.length A mm →
          ∀ x x' : AuxiliarySlotStates w.length → (Lt.down Lt.r 0 hr).PF,
            (∀ α, x α ∈ (Lt.down Lt.r 0 hr).ImgK h A mm) → (∀ α, x' α ∈ (Lt.down Lt.r 0 hr).ImgK h A mm) →
            (Lt.down Lt.r 0 hr).form ((Lt.down Lt.r 0 hr).wmod R (sCut u u' I) u u' w).RR x x' =
              ∫ p, ∑ α, Formalism.MainNotions.S.hsInner ((Lt.down Lt.r 0 hr).dw w.length c α p (omApply F x α p))
                (omApply F x' α p) ∧
            ∃ φt : ℂ → ℂ, Continuous φt ∧ Integrable φt ∧
              (∀ p ∈ (Lt.down Lt.r 0 hr).Dom, φt (zOf p) = ∑ α, Formalism.MainNotions.S.hsInner
                ((Lt.down Lt.r 0 hr).dw w.length c α p (omApply F x α p)) (omApply F x' α p)) ∧
              ∀ s : ℂ, ∫ ζ, fsC s ζ * φt ζ =
                (Lt.down Lt.r 0 hr).form ((Lt.down Lt.r 0 hr).wmod R (sCut u u' I) u u' w).RR
                  (omApply (Vop s w) x) x') ∧
        ∀ α, ∃ Θ ∈ Lt.AA, Lt.Rad Θ (fun φ => ∑ β, Lt.liftDown Lt.r 0 hr (F α β)
          (bTprod (m := Lt.r) w Lt.r le_rfl β (e1s _) φ))

def stE (C : ℝ) : Prop :=
  (∀ (L : Lev) (u u' : Fin (L.k0 + 1) → ℝ) (I : Set ℝ), HypC L u u' I →
    ∀ R, L.IsRadQQ R → ∀ (h : L.Haar) (A : ℝ) (mm : ℕ), h.Ok → ∀ w : Word, Admissible I w →
      Big C L w.length A mm → L.PosOn (L.ImgK h A mm) (L.wmod R (sCut u u' I) u u' w).RR) ∧
  ∀ (L : Lev) (pb : Mat L.k0 (L.r + 1) → (L.Wp →L[ℂ] L.Wp)) (pb' : Mat L.k0 (L.r + 1) → (L.Wq →L[ℂ] L.Wq))
    (u u' : Fin (L.k0 + 1) → ℝ) (I : Set ℝ),
    L.Std → L.Compat pb pb' → HypC (L.up pb pb') u u' I →
    ∀ Rs, L.IsRadQQ Rs → ∀ Rb, (L.up pb pb').IsRadQQ Rb →
    ∀ (h : (L.up pb pb').Haar) (A : ℝ) (mm : ℕ), h.Ok → ∀ w : Word, Admissible I w →
      Big C (L.up pb pb') w.length A mm →
      ∀ x x' : AuxiliarySlotStates w.length → (L.up pb pb').PF,
        (∀ α, x α ∈ (L.up pb pb').ImgK h A mm) → (∀ α, x' α ∈ (L.up pb pb').ImgK h A mm) →
        ∃ φt : ℂ → ℂ, Continuous φt ∧ Integrable φt ∧
          (∀ c : ℂ, c ≠ 0 → φt c = ((Complex.normSq c)⁻¹ : ℂ) *
            L.form (L.wmod Rs (sCut u u' I) u u' w).RR
              (fun β y => omApply (bT (0 : Fin (L.r + 1 + 1)) w) x β (Fin.cons c y))
              (fun β y => omApply (bT (0 : Fin (L.r + 1 + 1)) w) x' β (Fin.cons c y))) ∧
          ∀ s : ℂ, ∫ c, fsC s c * φt c =
            (L.up pb pb').form ((L.up pb pb').wmod Rb (sCut u u' I) u u' w).RR (omApply (Vop s w) x) x'

def stGauge (C : ℝ) : Prop := stA C ∧ stB ∧ stC C ∧ stD C ∧ stE C

end Gauge

section LevelR

open Matrix MeasureTheory TensorProduct
open scoped ContDiff
open Formalism.QuantumDeterminants Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.LevR

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

section Parts

variable {B : Base E} {r : ℕ} (C : Ctx B r) (Γ : GCtx E r)

def lenI (B : Base E) : ℝ := sSup B.I - sInf B.I

def stLevR (h : (Fin (r + 1) → ℂ) → E →L[ℂ] E) (SS : Fin B.k0 → (Fin (r + 1) → ℂ) → E →L[ℂ] E) :
    Prop :=

  (∀ Y : ℂ, NoPoleRho B Y →
    C.OpEq (lOp B.T B.T' B.rhoP C.P C.Q Y) (lDec B.T B.T' B.rhoP C.P h SS Y)) ∧

  (∀ l : Fin B.k0, ∀ x ∈ C.Dom, ∀ ρ ρ' : B.Rho, B.rhoP ρ' ≠ B.rhoP ρ + Pi.single l 1 →
    (C.P ρ' x).comp ((SS l x).comp (C.P ρ x)) = 0) ∧

  (∃ κ : Fin B.k0 → B.Rho → ℂ, ∀ l ρ, ∀ x ∈ C.Dom,
    (B.fadj (SS l x)).comp ((SS l x).comp (C.P ρ x)) = κ l ρ • C.P ρ x) ∧

  (∀ Y : ℝ, NoPoleRho B Y → NoPoleRho B ((Y : ℂ) + 1) →
    C.IsAdj (lOp B.T B.T' B.rhoP C.P C.Q Y) (mOp B.T B.T' B.rhoP C.P C.Q ((Y : ℂ) + 1))) ∧

  (∀ Y : ℂ, NoPoleRho B Y →
    C.OpEq (mOp B.T B.T' B.rhoP C.P C.Q Y)
      (m0 r B.T B.T' (C.fstar h) Y + mulF (fun x => (GG B.T B.T' x)⁻¹) ∘
        ∑ l : Fin B.k0, mulE (shInv B.rhoP C.P l Y) ∘ mulE (C.fstar (SS l))))

def stLev0 (h : (Fin (r + 1) → ℂ) → E →L[ℂ] E) (SS : Fin B.k0 → (Fin (r + 1) → ℂ) → E →L[ℂ] E) : Prop :=

  (∀ n (hn : n ≤ r), ∀ Y : ℂ,
    let u := Y + ((Γ.nV : ℂ) - 1) / 2
    Γ.cminor n hn u ∈ Γ.PolyInv ∧ Γ.Rad (Γ.cminor n hn u) (DnVn n hn Y 0) ∧
    (∀ hn1 : n + 1 ≤ r, Γ.Rad (Γ.cminor n hn u) (DnVn (n + 1) hn1 Y 1))) ∧

  (∀ Y : ℂ, ∃ Θ ∈ Γ.PolyInv, Γ.Rad Θ (Rhat r C.Q Y)) ∧

  (∀ l, SSnat (SS l) ∈ C.AA) ∧ (∀ Y : ℂ, R0 r B.T B.T' h Y ∈ C.AA) ∧

  (∃ cf : Fin (r + 2) → Op (r + 1) E,
    (∀ Y : ℂ, C.OpEq (R0 r B.T B.T' h Y) (∑ j : Fin (r + 2), Y ^ (j : ℕ) • cf j)) ∧
    C.OpEq (cf (Fin.last (r + 1))) (mulF (fun x => -star (Dr1 x)))) ∧

  (∀ Y : ℂ, NoPoleRho B Y →
    C.OpEq (R0 r B.T B.T' h Y)
      (mulE (xInvFib B.rhoP C.P Y) ∘ Rhat r C.Q Y -
        ∑ l, mulE (shInv B.rhoP C.P l Y) ∘ SSnat (SS l) ∘ Ahat r Y)) ∧

  (∀ Y : ℂ, NoPoleRho B Y →
    C.OpEq (mulE (xInvFib B.rhoP C.P Y) ∘ C.RhatV Y)
      (weightedMirrorLevelOperator r B.T B.T' (C.fstar h) Y +
        ∑ l, mulE (shInv B.rhoP C.P l Y) ∘ (mulF (fun x => Dr x / star (Dr x)) ∘ mulE (C.fstar (SS l))) ∘ AhatV r Y))

def stRules (h : (Fin (r + 1) → ℂ) → E →L[ℂ] E) (SS : Fin B.k0 → (Fin (r + 1) → ℂ) → E →L[ℂ] E) :
    Prop :=
  let A := fun Y => Ahat (E := E) r Y
  let R := fun Y => R0 r B.T B.T' h Y
  let Av := fun Y => AhatV (E := E) r Y
  let Rv := fun Y => weightedMirrorLevelOperator r B.T B.T' (C.fstar h) Y
  let Gp := fun (s : ℂ) => mulF (E := E) (fun x => Gfn B.T B.T' x ^ s)
  let Dm := fun (f : (Fin (r + 1) → ℂ) → ℂ) => mulF (E := E) f

  (∀ s Y : ℂ, C.OpEq (Gp (-s) ∘ A Y ∘ Gp s) (A (Y + s)) ∧ C.OpEq (Gp (-s) ∘ R Y ∘ Gp s) (R (Y + s)) ∧
    C.OpEq (Gp (-s) ∘ Av Y ∘ Gp s) (Av (Y - s)) ∧ C.OpEq (Gp (-s) ∘ Rv Y ∘ Gp s) (Rv (Y - s))) ∧

  (∀ Y : ℂ, C.OpEq (Dm (fun x => (Dr1 x)⁻¹) ∘ A Y ∘ Dm Dr1) (A (Y + 1)) ∧
    C.OpEq (Dm (fun x => (Dr1 x)⁻¹) ∘ R Y ∘ Dm Dr1)
      (R (Y + 1) + Dm (fun x => ((B.T * B.T' : ℝ) : ℂ) * star (Dr x) / Dr1 x) ∘ A (Y + 1)) ∧
    C.OpEq (Dm (fun x => (star (Dr1 x))⁻¹) ∘ Av Y ∘ Dm (fun x => star (Dr1 x))) (Av (Y - 1)) ∧
    C.OpEq (Dm (fun x => (star (Dr1 x))⁻¹) ∘ Rv Y ∘ Dm (fun x => star (Dr1 x)))
      (Rv (Y - 1) - Dm (fun x => ((B.T * B.T' : ℝ) : ℂ) * Dr x / star (Dr1 x)) ∘ Av (Y - 1))) ∧

  (∀ f : (Fin (r + 1) → ℂ) → ℂ, DifferentiableOn ℂ (fun x => star (f x)) C.Dom → ∀ Y : ℂ,
    C.OpEq (Dm f ∘ A Y) (A Y ∘ Dm f) ∧ C.OpEq (Dm f ∘ R Y) (R Y ∘ Dm f)) ∧
  (∀ f : (Fin (r + 1) → ℂ) → ℂ, DifferentiableOn ℂ f C.Dom → ∀ Y : ℂ,
    C.OpEq (Dm f ∘ Av Y) (Av Y ∘ Dm f) ∧ C.OpEq (Dm f ∘ Rv Y) (Rv Y ∘ Dm f)) ∧

  (∀ l : Fin B.k0, ∀ Y : ℂ,
    let Sn := SSnat (E := E) (SS l)
    let Sa := mulF (E := E) (fun x => Dr x / star (Dr x)) ∘ mulE (C.fstar (SS l))
    (C.OpEq (A Y ∘ Sn) (Sn ∘ A (Y - 1)) ∧ C.OpEq (R Y ∘ Sn) (Sn ∘ R (Y - 1)) ∧
      C.OpEq (Av Y ∘ Sn) (Sn ∘ Av (Y - 1)) ∧ C.OpEq (Rv Y ∘ Sn) (Sn ∘ Rv (Y - 1))) ∧
    (C.OpEq (A Y ∘ Sa) (Sa ∘ A (Y + 1)) ∧ C.OpEq (R Y ∘ Sa) (Sa ∘ R (Y + 1)) ∧
      C.OpEq (Av Y ∘ Sa) (Sa ∘ Av (Y + 1)) ∧ C.OpEq (Rv Y ∘ Sa) (Sa ∘ Rv (Y + 1)))) ∧

  (∀ Y : ℂ,
    let zi := Dm (fun x => (zOf x)⁻¹)
    let zbi := Dm (fun x => (star (zOf x))⁻¹)
    C.OpEq (zbi ∘ A Y) (A Y ∘ zbi) ∧ C.OpEq (zbi ∘ R Y) (R Y ∘ zbi) ∧ C.OpEq (zbi ∘ Av Y) (Av Y ∘ zbi) ∧
    C.OpEq (Rv Y ∘ zbi - zbi ∘ Rv Y) (-(Dm (fun x => Gfn B.T B.T' x / star (Dr1 x) ^ 2) ∘ Av Y)) ∧
    C.OpEq (zi ∘ A Y) (A Y ∘ zi) ∧ C.OpEq (zi ∘ Av Y) (Av Y ∘ zi) ∧ C.OpEq (zi ∘ Rv Y) (Rv Y ∘ zi) ∧
    C.OpEq (R Y ∘ zi - zi ∘ R Y) (Dm (fun x => Gfn B.T B.T' x / Dr1 x ^ 2) ∘ A Y))

def stProd (Cv : ℝ) (h : (Fin (r + 1) → ℂ) → E →L[ℂ] E)
    (SS : Fin B.k0 → (Fin (r + 1) → ℂ) → E →L[ℂ] E) : Prop :=
  0 < lenI B → ∀ (N : ℕ) (fs : Fin N → ℂ × Op (r + 1) E), (∀ j, C.IsFac h SS (fs j).1 (fs j).2) →
    ∃ (L : Finset ℝ), (↑L : Set ℝ) ⊆ B.I ∧ L.card = r + 2 ∧ (∀ y ∈ L, NoPoleRho B y) ∧
    ∃ (M : ℕ) (b : Fin M → (Fin (r + 1) → ℂ) → E →L[ℂ] E) (n n' n'' : Fin M → ℕ)
      (len : Fin M → ℕ) (blk : (j : Fin M) → Fin (len j) → Fin 4 × ℂ),
      (∀ j, C.IsBdd SS (b j)) ∧
      (∀ j, ((n j + n' j + n'' j : ℕ) : ℝ) ≤ Cv * N) ∧
      (∀ j i, (∃ (i0 : Fin N) (m : ℤ), ((blk j i).2 = (fs i0).1 + m) ∧ (|m| : ℝ) ≤ Cv * N) ∨
        ∃ y ∈ L, (blk j i).2 = y) ∧
      C.OpEq (C.compL (List.ofFn fun j => (fs j).2))
        (∑ j, mulE (b j) ∘ mulF (fun x => Gfn B.T B.T' x ^ (-(n j : ℤ)) * Dr1 x ^ (-(n' j : ℤ)) *
            star (Dr1 x) ^ (-(n'' j : ℤ))) ∘ C.compL (List.ofFn fun i => C.blk4 (blk j i).1 (blk j i).2))

def AEq {n : ℕ} (M N : C.AM n) : Prop := ∀ s t, C.OpEq (M s t) (N s t)

def stFrameR (okF : ℕ → Prop) (h : (Fin (r + 1) → ℂ) → E →L[ℂ] E)
    (SS : Fin B.k0 → (Fin (r + 1) → ℂ) → E →L[ℂ] E) : Prop :=
  ∀ w : List (Bool × ℝ), Admissible B.I w →
    (okF w.length → ∀ φ ψ : (Fin w.length → Fin 2) → (Fin (r + 1) → ℂ) → E, (∀ s, φ s ∈ C.clsF) → (∀ s, ψ s ∈ C.clsF) →
      C.form (C.RR w) φ ψ = C.bsum (C.aapp (C.dM w) (C.aapp (C.F h SS w) φ)) (C.aapp (C.F h SS w) ψ)) ∧
    (∀ s ρ, B.IsType ρ → 0 < (C.cw w s ρ).re ∧ (C.cw w s ρ).im = 0) ∧
    (∀ Y : ℂ, NoPoleRho B Y → OffPoles w Y →
      AEq C (C.amul (C.F h SS w) (C.TT w Y 1 1)) (C.amul (C.alm (mulF C.gg) (C.toAM (C.xM w Y))) (C.F h SS w)) ∧
      AEq C (C.amul (C.F h SS w) (C.TT w Y 1 0))
        (C.amul (C.alm (mulF C.gg) (C.toAM (C.xM w Y))) (C.amul (C.lfr h SS w Y) (C.F h SS w))) ∧
      (∀ s t, mulE (C.ee SS w Y s t) ∈ C.AA) ∧
      C.IsEePM SS true w.length (C.ee SS w Y)) ∧
    (∀ Y Y' : ℂ, C.IsEePM SS false w.length (C.ee SS w Y - C.ee SS w Y'))

def stFrameG (Cr : Ctx B 0) (C0 : Ctx B r) (lift : Op 1 E → Op (r + 1) E)
    (pull : ((Fin 1 → ℂ) → E →L[ℂ] E) → (Fin (r + 1) → ℂ) → E →L[ℂ] E)
    (h : (Fin 1 → ℂ) → E →L[ℂ] E) (SS : Fin B.k0 → (Fin 1 → ℂ) → E →L[ℂ] E) : Prop :=
  ∀ w : List (Bool × ℝ), Admissible B.I w →
    let g := fun (v : Fin w.length → Fin 2) => ∑ t, lift (Cr.F h SS w v t) ∘ C0.uw w t
    (∀ s, g s ∈ C0.AA) ∧
    (∀ ya : ℝ, Admissible B.I ((true, ya) :: w) → ∀ s : Fin w.length → Fin 2,
      let w' := (true, ya) :: w
      let g' := fun (v : Fin w'.length → Fin 2) => ∑ t, lift (Cr.F h SS w' v t) ∘ C0.uw w' t
      C0.OpEq (g' (Fin.cons 0 s)) (mulF (fun x => (Dr1 x)⁻¹) ∘ Ahat r ya ∘ g s) ∧
      C0.OpEq (g' (Fin.cons 1 s))
        (mulF (fun x => (star (Dr1 x))⁻¹) ∘ R0 r B.T B.T' (pull h) ya ∘ g s +
          ∑ t, mulE (pull (Cr.ee SS w ya s t)) ∘ mulF (fun x => (Dr1 x)⁻¹) ∘ Ahat r ya ∘ g t))

def mid3 (B : Base E) : Set ℝ := Set.Icc (sInf B.I + lenI B / 3) (sSup B.I - lenI B / 3)

def wnormSq {n : ℕ} (wt : (Fin n → Fin 2) → B.Rho → ℂ) (x : Fin (r + 1) → ℂ) (v : (Fin n → Fin 2) → E) : ℝ :=
  ∑ s, ∑ᶠ ρ, ‖wt s ρ‖ * (B.hs (C.P ρ x (v s)) (C.P ρ x (v s))).re

def stRes (C1 C2 : ℝ) (SS : Fin B.k0 → (Fin (r + 1) → ℂ) → E →L[ℂ] E) : Prop :=
  ∀ w : List (Bool × ℝ), Admissible B.I w → Ctx.IsPlus w → (∀ a ∈ w, a.2 ∈ mid3 B) →
    (∀ x ∈ C.Dom, ∀ s t, ∃ (Γ0 : Finset ℂ) (m : ℕ) (cf : ℕ → E →L[ℂ] E),
      (∀ γ ∈ Γ0, (∃ ρ, B.IsType ρ ∧ ∃ l, γ = -(B.rhoP ρ l : ℂ)) ∨ ∃ a ∈ w, γ = a.2) ∧
      ∀ Y : ℂ, Y ∉ Γ0 → (∏ γ ∈ Γ0, (Y - γ)) • C.ee SS w Y s t x = ∑ j ∈ Finset.range m, Y ^ j • cf j) ∧
    (6 ≤ lenI B → (w.length : ℝ) ≤ lenI B →
      (∀ i : Fin w.length, (∑ j : Fin w.length, if j = i then 0 else 1 / |(w.get i).2 - (w.get j).2|) ≤ C1) →
      ∀ Y Y' : ℝ, Y ∈ mid3 B → Y' ∈ mid3 B → (∀ a ∈ w, 2 < |Y - a.2| ∧ 2 < |Y' - a.2|) →
      (w.map fun a => 1 / |Y - a.2|).sum ≤ C1 → (w.map fun a => 1 / |Y' - a.2|).sum ≤ C1 →
      ∀ x ∈ C.Dom, ∀ v : (Fin w.length → Fin 2) → E,
        wnormSq C (fun s ρ => C.cw w s ρ * C.xw w Y s ρ) x
            (fun s => ∑ t, (C.ee SS w Y s t x - C.ee SS w Y' s t x) (v t)) ≤
          (C2 * |Y - Y'| * ((B.k0 + 1 : ℝ) / lenI B + (w.map fun a => 1 / (|Y - a.2| * |Y' - a.2|)).sum)) ^ 2 *
            wnormSq C (fun s ρ => C.cw w s ρ * C.qw w Y / C.xw w ((Y : ℂ) + 1) s ρ) x v)

end Parts

def stOm (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : Prop :=
  ∃ p p' : Fin (k + 1) → MvPolynomial ((Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) ⊕
      (Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) ℂ,
    ∀ c : Fin r → ℂ, (∀ a, c a ≠ 0) → ∀ μ ∈ UH (Hb k),
      (fun j => evG (bigCell k r c μ) (p j)) = omF k r z z' c μ ∧
      (fun j => evG (bigCell k r c μ) (p' j)) = omF' k r z z' c μ ∧
      (herm (Hb k) (omF k r z z' c μ) (omF k r z z' c μ)).re = Gf k r z z' (bigCell k r c μ) / Tz k r z ∧
      (herm (Hb k) (omF' k r z z' c μ) (omF' k r z z' c μ)).re = Gf k r z z' (bigCell k r c μ) / Tz k r z'

def stLevel (C Cv C1 C2 : ℝ) : Prop :=
  ∀ (Lt : Lev) (u u' : Fin (Lt.k0 + 1) → ℝ) (I : Set ℝ) (hr : Lt.r + 0 = Lt.r),
    HypC Lt u u' I → HypC (Lt.down Lt.r 0 hr) u u' I →
    ∀ R : ℂ → Matrix (Fin 2) (Fin 2) (Lt.down Lt.r 0 hr).POp, (Lt.down Lt.r 0 hr).IsRadQQ R →
    ∃ (h : (Fin 1 → ℂ) → Lt.Hom →L[ℂ] Lt.Hom) (SS : Fin Lt.k0 → (Fin 1 → ℂ) → Lt.Hom →L[ℂ] Lt.Hom),

      (∀ (hh : (Lt.down Lt.r 0 hr).Haar) (A : ℝ) (mm : ℕ), hh.Ok → Big C Lt 0 A mm →
        stLevR (ctxR Lt u u' I hr R ((Lt.down Lt.r 0 hr).ImgK hh A mm)) h SS) ∧

      stLev0 (ctx0 Lt u u' I hr R) (gctxOf Lt) (pullZ h) (fun l => pullZ (SS l)) ∧

      stRules (ctx0 Lt u u' I hr R) (pullZ h) (fun l => pullZ (SS l)) ∧
      stProd (ctx0 Lt u u' I hr R) Cv (pullZ h) (fun l => pullZ (SS l)) ∧

      (∀ (hh : (Lt.down Lt.r 0 hr).Haar) (A : ℝ) (mm : ℕ), hh.Ok →
        stFrameR (ctxR Lt u u' I hr R ((Lt.down Lt.r 0 hr).ImgK hh A mm)) (fun N => Big C Lt N A mm) h SS) ∧
      stFrameG (ctxR Lt u u' I hr R (Lt.down Lt.r 0 hr).Img) (ctx0 Lt u u' I hr R) (Lt.liftDown Lt.r 0 hr)
        pullZ h SS ∧

      stOm (Lt.k0 + 1) Lt.r Lt.z Lt.z' ∧
      stRes (ctxR Lt u u' I hr R (Lt.down Lt.r 0 hr).Img) C1 C2 SS

end LevelR

section Further

open Matrix MeasureTheory Filter Topology Polynomial
open scoped ContDiff
open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.LevR

def Jop {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] : Matrix (Fin 2) (Fin 2) (Op m E) :=
  Matrix.of ![![fun _ => 0, fun f => f], ![fun f => -f, fun _ => 0]]

def scalMat {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (φ : (Fin m → ℂ) → ℂ)
    (M : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) (Op m E) :=
  fun a b f x => (M a b * φ x) • f x

def mulAfter {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (φ : (Fin m → ℂ) → ℂ)
    (M : Matrix (Fin 2) (Fin 2) (Op m E)) : Matrix (Fin 2) (Fin 2) (Op m E) :=
  fun a b f x => φ x • M a b f x

abbrev Op4 (m : ℕ) (E : Type*) := Fin 2 × Fin 2 → Fin 2 × Fin 2 → Op m E

def op4Mul {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (M N : Op4 m E) : Op4 m E :=
  fun p q f => ∑ r : Fin 2 × Fin 2, M p r (N r q f)

def tens1 {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (M : Matrix (Fin 2) (Fin 2) (Op m E)) :
    Op4 m E := fun p q f => if p.2 = q.2 then M p.1 q.1 f else 0

def tens2 {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (M : Matrix (Fin 2) (Fin 2) (Op m E)) :
    Op4 m E := fun p q f => if p.1 = q.1 then M p.2 q.2 f else 0

def RhOp {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (D : ℂ) : Op4 m E := fun p q f =>
  ((D * (if p = q then 1 else 0) - (if p.1 = q.2 ∧ p.2 = q.1 then 1 else 0)) / (D - 1)) • f

def stLetters : Prop :=
  ∀ (m : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (l : Fin m) (f : (Fin m → ℂ) → E),
    f ∈ WSm m E →
    (∀ (Y : ℂ) (a b : Fin 2),
      opMatMul (opMatMul (Tmat (E := E) l (Y + 1)).transpose Jop) (Tmat l Y) a b f = Jop a b f ∧
      opMatMul (opMatMul (TmatV (E := E) l (Y + 1)) Jop) (TmatStar l Y) a b f = Jop a b f) ∧
    ∀ (Y Y' : ℂ), Y' - Y ≠ 1 → ∀ p q : Fin 2 × Fin 2,
      op4Mul (op4Mul (RhOp (Y' - Y)) (tens1 (Tmat (E := E) l Y'))) (tens2 (Tmat l Y)) p q f =
        op4Mul (op4Mul (tens2 (Tmat (E := E) l Y)) (tens1 (Tmat l Y'))) (RhOp (Y' - Y)) p q f

def thLog {m : ℕ} (l : Fin m) (h : (Fin m → ℂ) → ℝ) (x : Fin m → ℂ) : ℂ :=
  star (x l) * wirtBar l (fun y => ((Real.log (h y) : ℝ) : ℂ)) x

def stThLog : Prop :=
  ∀ (m : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (l : Fin m) (h : (Fin m → ℂ) → ℝ),
    (∀ x, 0 < h x) → ContDiffOn ℝ ∞ h (OmX m) → ∀ (Y : ℂ) (f : (Fin m → ℂ) → E), f ∈ WSm m E →
    ∀ (a b : Fin 2), ∀ x ∈ OmX m,
      opMatMul (Tmat (E := E) l Y) (scalMat (fun y => ((h y)⁻¹ : ℂ)) 1) a b f x =
        (((h x)⁻¹ : ℝ) : ℂ) • (Tmat l Y a b f x -
          (if a = 0 ∧ b = 0 then star (thLog l h x) • f x else 0)) ∧
      opMatMul (TmatV (E := E) l Y) (scalMat (fun y => ((h y)⁻¹ : ℂ)) 1) a b f x =
        (((h x)⁻¹ : ℝ) : ℂ) • (TmatV l Y a b f x +
          (if a = 0 ∧ b = 0 then thLog l h x • f x else 0))

def fsFun {m : ℕ} (s : ℂ) (l : Fin m) (x : Fin m → ℂ) : ℂ := Complex.exp (s * x l - star (s * x l))

def Umat (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; -s, 1]

def stWaveLetters : Prop :=
  (∀ (m : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (l : Fin m) (s Y : ℂ)
      (f : (Fin m → ℂ) → E), f ∈ WSm m E → ∀ a b : Fin 2,
      opMatMul (Tmat (E := E) l Y) (scalMat (fsFun s l) (Umat s)⁻¹) a b f =
        mulAfter (fsFun s l) (Tmat l Y) a b f ∧
      opMatMul (TmatV (E := E) l Y) (scalMat (fsFun s l) (Umat (star s))⁻¹) a b f =
        mulAfter (fsFun s l) (TmatV l Y) a b f) ∧
    ∀ s : ℂ, (Umat s).transpose * !![0, 1; -1, 0] * Umat s = !![0, 1; -1, 0]

def IsKFinCoefT {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H))
    (f : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wq →L[ℂ] Wp)) : Prop :=
  ∃ a ∈ UH (Hpk k r), ∃ b ∈ UH (Hpk k r), IsKFinCoefH σ (fun g => f (a * g * b))

def ncGap {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) : ℝ :=
  sInf {d | ∃ a b : Fin n, ε a ≠ ε b ∧ d = |lam a - lam b|}

def thrCap {n : ℕ} (ε : Fin n → Bool) : ℝ :=
  max ((n : ℝ) * ((Finset.univ.filter fun a => ε a = true).card : ℝ) * ((Finset.univ.filter fun a => ε a = false).card : ℝ) + 1)
    (120 * (n : ℝ) * ((min (Finset.univ.filter fun a => ε a = true).card (Finset.univ.filter fun a => ε a = false).card : ℕ) : ℝ) ^
      ((3 : ℝ) / 2))

def stCapEig : Prop :=
  ∀ (k r : ℕ) (L : LocBessel k r), thrCap L.ε < ncGap L.ε L.lam →
    ∀ (f : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (L.Wq →L[ℂ] L.Wp)), IsKFinCoefT L.σ f →
    ∀ Y : ℂ, ∀ g ∈ UH (Hpk k r), capC (k := k) (r := r) Y f g = capP (fun s => (L.lam s : ℂ)) Y • f g

def DiagonalEntryIdentity : Prop :=
  ∀ (L : Lev) (pb : Mat L.k0 (L.r + 1) → (L.Wp →L[ℂ] L.Wp)) (pb' : Mat L.k0 (L.r + 1) → (L.Wq →L[ℂ] L.Wq))
    (u u' : Fin (L.k0 + 1) → ℝ),
    L.Std → (L.up pb pb').Std → L.Compat pb pb' → (L.up pb pb').HC u u' →
      ∀ Rs, L.IsRadQQ Rs → ∀ Rb, (L.up pb pb').IsRadQQ Rb → ∀ Y : ℂ, ∀ φ ∈ (L.up pb pb').Img,
        ∀ x ∈ (L.up pb pb').BD,
          Rb Y 1 1 φ x = ((Complex.normSq (x 0) : ℝ) : ℂ) • liftOp (Rs Y 0 0) φ x

section Lists

variable {m : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]

def modL {w : Word} (dual : Bool) (M0 : Mod m E w.length) : (Ls : Word) → Mod m E (Ls ++ w).length
  | [] => M0
  | l :: Ls => step (if dual then (false, l.2 + 1) else l) (modL dual M0 Ls)

def JL {w : Word} (M : Matrix (AuxiliarySlotStates w.length) (AuxiliarySlotStates w.length) (Op m E)) :
    (Ls : Word) → Matrix (AuxiliarySlotStates (Ls ++ w).length) (AuxiliarySlotStates (Ls ++ w).length) (Op m E)
  | [] => M
  | _ :: Ls => JRR (JL M Ls)

end Lists

def stDualList (C Co Cd : ℝ) : Prop :=
  ∀ (L : Lev) (u u' : Fin (L.k0 + 1) → ℝ) (I : Set ℝ), HypC L u u' I →
    ∀ R, L.IsRadQQ R → ∀ (h : L.Haar) (A : ℝ) (mm : ℕ), h.Ok →
    ∀ (w Ls : Word), Big C L (Ls ++ w).length A mm → (∀ l ∈ Ls, l.1 = true) →
      (Ls ++ w).Pairwise (fun a b => 3 ≤ |a.2 - b.2|) →
      (∀ i : Fin (Ls ++ w).length, (∑ j : Fin (Ls ++ w).length,
        if j = i then 0 else 1 / |((Ls ++ w).get i).2 - ((Ls ++ w).get j).2|) ≤ Co) →
      (∀ l ∈ Ls, (L.wmod R (sCut u u' I) u u' w).q (l.2 : ℂ) ≠ 0) →
      L.PosOn (L.ImgK h A mm) (modL false (L.wmod R (sCut u u' I) u u' w) Ls).RR →
      ∀ x₁ x₂ : AuxiliarySlotStates (Ls ++ w).length → L.PF, (∀ α, x₁ α ∈ L.ImgK h A mm) → (∀ α, x₂ α ∈ L.ImgK h A mm) →
        Complex.normSq (L.form (JL (L.wmod R (sCut u u' I) u u' w).RR Ls) x₁ x₂) ≤
          Cd ^ Ls.length * (L.form (modL false (L.wmod R (sCut u u' I) u u' w) Ls).RR x₁ x₁).re *
            (L.form (modL true (L.wmod R (sCut u u' I) u u' w) Ls).RR x₂ x₂).re /
              (Ls.map fun l => ((L.wmod R (sCut u u' I) u u' w).q (l.2 : ℂ)).re).prod

def TmatVStar {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (l : Fin m) (Y : ℂ) :
    Matrix (Fin 2) (Fin 2) (Op m E) :=
  Matrix.of ![![fun f => Y • f + pOp l f, ciOp l], ![fun f => -(cOp l f), fun _ => 0]]

def stIBP : Prop :=
  ∀ (m : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (B : E →L⋆[ℂ] E →L[ℂ] ℂ) (l : Fin m) (Y : ℝ)
    (x z : Fin 2 → (Fin m → ℂ) → E), (∀ a, x a ∈ WSm m E) → (∀ a, z a ∈ WSm m E) → ∀ c ∈ OmX m,
    ((∑ a, B (opMatApply (Tmat l (Y : ℂ)) x a c) (z a c)) =
      (∑ a, B (x a c) (opMatApply (TmatStar l (Y : ℂ)) z a c)) -
        (Complex.normSq (c l) : ℂ) * wirtBar l (fun c' =>
          B (x 0 c') (opMatApply (TmatStar l (Y : ℂ)) z 1 c') / (Complex.normSq (c' l) : ℂ)) c) ∧
    ((∑ a, B (opMatApply (TmatV l (Y : ℂ)) x a c) (z a c)) =
      (∑ a, B (x a c) (opMatApply (TmatVStar l (Y : ℂ)) z a c)) +
        (Complex.normSq (c l) : ℂ) * wirt l (fun c' =>
          B (x 0 c') (opMatApply (TmatVStar l (Y : ℂ)) z 1 c') / (Complex.normSq (c' l) : ℂ)) c)

def headEl (k j r' : ℕ) (h : Matrix (Fin j) (Fin j) ℂ)
    (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) :
    Matrix (Fin (2 * (j + r') + k + 1)) (Fin (2 * (j + r') + k + 1)) ℂ := fun p q =>
  if hq : q.val < j then
    (if hp : 2 * (j + r') + k + 1 - j ≤ p.val then h ⟨2 * (j + r') + k - p.val, by omega⟩ ⟨q.val, hq⟩ else 0)
  else if hq2 : q.val < 2 * r' + k + 1 + j then
    (if hp : j ≤ p.val ∧ p.val < 2 * r' + k + 1 + j then g ⟨p.val - j, by omega⟩ ⟨q.val - j, by omega⟩ else 0)
  else
    (if hp : p.val < j then (hᴴ)⁻¹ ⟨p.val, hp⟩ ⟨2 * (j + r') + k - q.val, by omega⟩ else 0)

def headLt (Lt : Lev) (j r' : ℕ) (hj : j + r' = Lt.r) (h : Matrix (Fin j) (Fin j) ℂ) (g : Mat Lt.k0 r') :
    Mat Lt.k0 Lt.r :=
  fun p q => headEl (Lt.k0 + 1) j r' h g (Fin.cast (by omega) p) (Fin.cast (by omega) q)

def stSlices (Cs : ℝ) : Prop :=
  ∀ (Lt : Lev) (u u' : Fin (Lt.k0 + 1) → ℝ) (j r' : ℕ) (hj : j + r' = Lt.r) (hd : Point ℂ j), Lt.Std → Lt.HC u u' →
    (∀ g ∈ UH (Hpk (Lt.k0 + 1) r'),
      Gf (Lt.k0 + 1) Lt.r Lt.z Lt.z' (headLt Lt j r' hj (ptMat hd) g) =
        Complex.normSq (ptMat hd).det * Gf (Lt.k0 + 1) r' (Lt.down j r' hj).z (Lt.down j r' hj).z' g) ∧
    ((∀ b ∈ hd.1, b.2 = 1) →
    ∀ (h : Lt.Haar) (h' : (Lt.down j r' hj).Haar) (A : ℝ) (mm : ℕ) (F : Lt.GF), h.Ok → h'.Ok → Lt.CC A mm F →
      0 ≤ A / (Cs * ((Lt.r : ℝ) + 1) ^ 2) -
        Cs * (((2 * Lt.r + Lt.k0 + 2 : ℕ) : ℝ) ^ 2 + ((Lt.r : ℝ) + 1) * mm) →
      ∃ Fh : (Lt.down j r' hj).GF,
        (Lt.down j r' hj).CC (A / (Cs * ((Lt.r : ℝ) + 1) ^ 2) -
          Cs * (((2 * Lt.r + Lt.k0 + 2 : ℕ) : ℝ) ^ 2 + ((Lt.r : ℝ) + 1) * mm)) mm Fh ∧
        ∀ c : Fin r' → ℂ, (∀ a, c a ≠ 0) → ∀ μ ∈ UH (Hb (Lt.k0 + 1)),
          lJ (Lt.down j r' hj) h' Fh (bigCell (Lt.k0 + 1) r' c μ) =
            lJ Lt h F (headLt Lt j r' hj (ptMat hd) (bigCell (Lt.k0 + 1) r' c μ)))

def stSmooth (CB : ℝ) : Prop :=
  ∀ (L : Lev) (u u' : Fin (L.k0 + 1) → ℝ) (I : Set ℝ), HypC L u u' I → 0 < L.r →
    ∀ (h : L.Haar) (A : ℝ) (mm M : ℕ), h.Ok → Big CB L M A mm →
    ∀ F F' : L.GF, L.CC A mm F → L.CC A mm F' → (∃ ε : ℝ, 0 < ε ∧ SuppGe L ε F ∧ SuppGe L ε F') →
      ∃ CM : ℝ, ∀ s : ℂ,
        ‖s‖ ^ M * ‖lbeta L h (fun g => fsC s (Zhat (L.k0 + 1) L.r L.z L.z' g 0 0) • F g) F'‖ ≤ CM

def stDecay (D : Formalism.BasicNotions.D7) (c C₁ : ℝ) : Prop :=
  0 < c ∧ c ≤ Real.sqrt 2 / 8 ∧ 120 ≤ C₁ ∧ ∀ (k0 : ℕ) (_hk : k0 + 1 = D.R.k) (L : LocBessel (k0 + 1) D.R.rS),
    C₁ * (D.R.r : ℝ) * ((D.R.m : ℝ) / 2) ^ ((3 : ℝ) / 2) ≤ ncGap L.ε L.lam →
    ∀ f : Matrix (Fin (2 * D.R.rS + (k0 + 1) + 1)) (Fin (2 * D.R.rS + (k0 + 1) + 1)) ℂ → (L.Wq →L[ℂ] L.Wp),
      IsKFinCoefT L.σ f → ∀ mm : ℕ,
      IsCC (k0 + 1) D.R.rS (c * ncGap L.ε L.lam * (D.R.m : ℝ) ^ (-(1 : ℝ) / 2)) mm f

def stMarkov : Prop :=
  ∀ (n k : ℕ) (p : ℝ[X]), p.natDegree ≤ n → k ≤ n → ∀ x ∈ Set.Icc (-1 : ℝ) 1,
    |(derivative^[k] p).eval x| ≤
      (∏ j ∈ Finset.range k, (((n : ℝ) ^ 2 - (j : ℝ) ^ 2) / (2 * (j : ℝ) + 1))) *
        sSup ((fun y => |p.eval y|) '' Set.Icc (-1 : ℝ) 1)

def IsPosDefZ {d : ℕ} (φ : (Fin d → ℤ) → ℂ) : Prop :=
  ∀ a : (Fin d → ℤ) →₀ ℂ,
    0 ≤ (∑ m ∈ a.support, ∑ n ∈ a.support, star (a m) * a n * φ (n - m)).re ∧
    (∑ m ∈ a.support, ∑ n ∈ a.support, star (a m) * a n * φ (n - m)).im = 0

def stHerglotz : Prop :=
  ∀ (d : ℕ) (φ : (Fin d → ℤ) → ℂ), IsPosDefZ φ ↔
    ∃ μ : Measure (Fin d → UnitAddCircle), IsFiniteMeasure μ ∧
      ∀ n : Fin d → ℤ, φ n = ∫ x, ∏ j, fourier (n j) (x j) ∂μ

def zpt {d : ℕ} (n : Fin d → ℤ) : EuclideanSpace ℝ (Fin d) := (WithLp.equiv 2 _).symm (fun j => (n j : ℝ))

def fhat {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℂ) (w : EuclideanSpace ℝ (Fin d)) : ℂ :=
  ∫ x, Complex.exp (-(2 * Real.pi * Complex.I * (inner ℝ x w : ℝ))) * f x

def stPoisson : Prop :=
  ∀ (d : ℕ) (f : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ),
    Summable (fun n : Fin d → ℤ => f (zpt n)) ∧
    Summable (fun m : Fin d → ℤ => fhat (fun x => f x) (zpt m)) ∧
    ∑' n : Fin d → ℤ, f (zpt n) = ∑' m : Fin d → ℤ, fhat (fun x => f x) (zpt m)

def stStatPhase : Prop :=
  ∀ (a : ℝ → ℂ) (φ : ℝ → ℝ) (x₀ : ℝ), ContDiff ℝ ∞ a → HasCompactSupport a → ContDiff ℝ ∞ φ →
    deriv φ x₀ = 0 → deriv (deriv φ) x₀ ≠ 0 → (∀ x ∈ tsupport a, x ≠ x₀ → deriv φ x ≠ 0) →
    (fun l : ℝ => (∫ x, Complex.exp (Complex.I * (l * φ x)) * a x) -
        Complex.exp (Complex.I * (l * φ x₀ + Real.pi * (SignType.sign (deriv (deriv φ) x₀) : ℝ) / 4)) *
          ((Real.sqrt (2 * Real.pi / (l * |deriv (deriv φ) x₀|)) : ℝ) : ℂ) * a x₀) =O[atTop]
      (fun l : ℝ => l ^ (-(3 : ℝ) / 2))

def stJSZ1 : Prop :=
  ∀ (k r : ℕ) (L : LocBessel k r) (B₁ B₂ : L.Hs → L.Wp), L.c = cStd →
    IsBesselMapSm (k := k) (r := r) L.z (psi k r L.z L.c) L.σ L.π B₁ →
    IsBesselMapSm (k := k) (r := r) L.z (psi k r L.z L.c) L.σ L.π B₂ →
    ∃ a b : ℂ, (a ≠ 0 ∨ b ≠ 0) ∧ ∀ v ∈ smoothVecs (k := k) (r := r) L.σ, a • B₁ v + b • B₂ v = 0

def stJSZ : Prop :=
  ∀ (k r : ℕ) (L : LocBessel k r) (B₁ B₂ : L.Hs → L.Wp), L.c ≠ 0 →
    IsBesselMapSm (k := k) (r := r) L.z (psi k r L.z L.c) L.σ L.π B₁ →
    IsBesselMapSm (k := k) (r := r) L.z (psi k r L.z L.c) L.σ L.π B₂ →
    ∃ a b : ℂ, (a ≠ 0 ∨ b ≠ 0) ∧ ∀ v ∈ smoothVecs (k := k) (r := r) L.σ, a • B₁ v + b • B₂ v = 0

def levOf {k0 r : ℕ} (L : LocBessel (k0 + 1) r) (μsec : ℂ → Matrix (Fin (k0 + 1 + 1)) (Fin (k0 + 1 + 1)) ℂ) : Lev where
  k0 := k0
  r := r
  z := L.z
  z' := L.z'
  Wp := L.Wp
  Wq := L.Wq
  π := L.π
  π' := L.π'
  μsec := μsec

def haarOf {k0 r : ℕ} (L : LocBessel (k0 + 1) r) (μsec : ℂ → Matrix (Fin (k0 + 1 + 1)) (Fin (k0 + 1 + 1)) ℂ) :
    (levOf L μsec).Haar where
  μW := L.μW
  μN := L.μN
  μW' := L.μW'

def cutF {k r : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] (z z' : Fin (2 * r + k + 1) → ℂ)
    (χ : ℝ → ℝ) (ε : ℝ) (F : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → V) :
    Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → V :=
  fun g => ((χ (Gf k r z z' g / ε) : ℝ) : ℂ) • F g

def energy {k0 r : ℕ} (L : LocBessel (k0 + 1) r) (μsec : ℂ → Matrix (Fin (k0 + 1 + 1)) (Fin (k0 + 1 + 1)) ℂ)
    (I : Set ℝ) (w : Word)
    (F : Matrix (Fin (2 * r + (k0 + 1) + 1)) (Fin (2 * r + (k0 + 1) + 1)) ℂ → (L.Wq →L[ℂ] L.Wp)) : ℂ :=
  L.beta μsec (capW (k := k0 + 1) (r := r) (sCut L.u L.u' I) (w.map fun l => (l.2 : ℂ)) F) F

def Std (D : Formalism.BasicNotions.D7) {k0 : ℕ} (hk : k0 + 1 = D.R.k) (L : LocBessel (k0 + 1) D.R.rS)
    (μsec : ℂ → Matrix (Fin (k0 + 1 + 1)) (Fin (k0 + 1 + 1)) ℂ) (I : Set ℝ) : Prop :=
  (∀ i, L.ε i = epsSH D.R (Fin.cast (by rw [hk]) i)) ∧ L.c = cStd ∧
    IsSection (k0 + 1) D.R.rS L.z L.z' μsec ∧ IsCutS L.u L.u' I ∧
    ∃ ρ : Fin k0 → ℝ, Interlace L.u ρ ∧ Interlace L.u' ρ

def stLemE' (D : Formalism.BasicNotions.D7) (C0 CA : ℝ) : Prop :=
  ∀ (k0 : ℕ) (hk : k0 + 1 = D.R.k) (L : LocBessel (k0 + 1) D.R.rS)
    (μsec : ℂ → Matrix (Fin (k0 + 1 + 1)) (Fin (k0 + 1 + 1)) ℂ) (I : Set ℝ) (N : ℕ) (A : ℝ) (p : ℕ)
    (F0 : Matrix (Fin (2 * D.R.rS + (k0 + 1) + 1)) (Fin (2 * D.R.rS + (k0 + 1) + 1)) ℂ → (L.Wq →L[ℂ] L.Wp))
    (χ : ℝ → ℝ) (w : Word),
    Std D hk L μsec I → D.R.rS + 1 ≤ N →
    CA * ((D.R.rS : ℝ) + 1) ^ 3 * ((N : ℝ) * (D.R.r : ℝ) ^ 2 + (D.R.r : ℝ) ^ 3) + (2 * (D.R.rS : ℝ) + 2) * p ≤ A →
    (∀ mm : ℕ, IsCC (k0 + 1) D.R.rS A mm F0) →
    C0 * N ≤ p →
    IsCutoff χ → Admissible I w → w.length ≤ N →
    Tendsto (fun ε : ℝ => energy L μsec I w
        (cutF L.z L.z' χ ε (fun g => ((Gf (k0 + 1) D.R.rS L.z L.z' g ^ p : ℝ) : ℂ) • F0 g)))
      (𝓝[>] 0)
      (𝓝 (energy L μsec I w (fun g => ((Gf (k0 + 1) D.R.rS L.z L.z' g ^ p : ℝ) : ℂ) • F0 g)))

abbrev Msq (s : ℕ) := Fin s → Fin s → ℂ

def mm {s : ℕ} (a b : Msq s) : Msq s := (Matrix.of a * Matrix.of b : Matrix (Fin s) (Fin s) ℂ)

def minv {s : ℕ} (a : Msq s) : Msq s := ((Matrix.of a)⁻¹ : Matrix (Fin s) (Fin s) ℂ)

def mdet {s : ℕ} (a : Msq s) : ℂ := (Matrix.of a).det

def psiC (c x : ℂ) : ℂ := Complex.exp (Complex.I * ((c * x).re : ℂ))

def psiLow {s : ℕ} (c : ℂ) (l : Msq s) : ℂ := psiC c (∑ i : Fin s, ∑ j : Fin s, if i.val = j.val + 1 then l i j else 0)

def psiUp {s : ℕ} (c : ℂ) (u : Msq s) : ℂ := psiC c (∑ i : Fin s, ∑ j : Fin s, if j.val = i.val + 1 then u i j else 0)

def lowOf {s : ℕ} (x : {p : Fin s × Fin s // p.2 < p.1} → ℂ) : Msq s := fun i j =>
  if h : j < i then x ⟨(i, j), h⟩ else if i = j then 1 else 0

def upOf {s : ℕ} (x : {p : Fin s × Fin s // p.1 < p.2} → ℂ) : Msq s := fun i j =>
  if h : i < j then x ⟨(i, j), h⟩ else if i = j then 1 else 0

def sdScale (c : ℂ) (d : ℕ) : ENNReal := ENNReal.ofReal ((‖c‖ / (2 * Real.pi)) ^ d)

def muLow (s : ℕ) (c : ℂ) : Measure (Msq s) :=
  sdScale c (Fintype.card {p : Fin s × Fin s // p.2 < p.1}) • Measure.map lowOf volume

def muUp (s : ℕ) (c : ℂ) : Measure (Msq s) :=
  sdScale c (Fintype.card {p : Fin s × Fin s // p.1 < p.2}) • Measure.map upOf volume

def stabU {s : ℕ} (g : Msq s) : Set (Matrix (Fin s) (Fin s) ℂ) :=
  {u | IsUpUni u ∧ IsLoUni (Matrix.of g * u⁻¹ * (Matrix.of g)⁻¹)}

def muStab {s : ℕ} (c : ℂ) (g : Msq s) : Measure (Msq s) :=
  sdScale c (Module.finrank ℝ (lieE (stabU g)) / 2) •
    Measure.map (fun x : lieE (stabU g) =>
      (fun i j => NormedSpace.exp (unrealify ((x : lieE (stabU g)) : EuclideanSpace ℝ (Fin s × Fin s × Bool))) i j : Msq s)) volume

def IsOrbMeas {s : ℕ} (c : ℂ) (g : Msq s) (ν : Measure (Msq s × Msq s)) : Prop :=
  ∀ F : Msq s × Msq s → ℂ, Integrable F ((muLow s c).prod (muUp s c)) →
    ∫ p, F p ∂((muLow s c).prod (muUp s c)) =
      ∫ p, (∫ u', F (mm p.1 (mm g (mm (minv u') (minv g))), mm u' p.2) ∂(muStab c g)) ∂ν

def IsOrbMeasLU {s : ℕ} (c : ℂ) (g : Msq s) (ν : Measure (Msq s × Msq s)) : Prop :=
  IsOrbMeas c g ν ∧ ν {p | ¬ (IsLoUni (Matrix.of p.1) ∧ IsUpUni (Matrix.of p.2))} = 0

def OmG {s : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (c : ℂ) (ν : Measure (Msq s × Msq s))
    (Φ : Msq s → E) (g : Msq s) : E :=
  ∫ p, (psiLow c p.1 * psiUp c p.2) • Φ (mm (mm p.1 g) p.2) ∂ν

def gTC (s : ℕ) (t c : ℂ) : Msq s := fun i j => ptEntry [(t, s - 1), (c, 1)] i.val j.val

def gZW (s : ℕ) (z : ℂ) : Msq s := fun i j => ptEntry [(z, s)] i.val j.val

def fNorm {s : ℕ} (Z : Msq s) : ℝ := Real.sqrt (∑ i, ∑ j, Complex.normSq (Z i j))

def stGerm (C₁ C₂ : ℝ) : Prop :=
  ∀ (s : ℕ) (cψ : ℂ), 2 ≤ s → cψ ≠ 0 →
  ∃ ph : ℂ → ℂ, (∀ z, ‖ph z‖ = 1) ∧
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (Φ : Msq s → E) (A : ℝ),
    C₂ * (s : ℝ) ^ 3 ≤ A → ContDiffOn ℝ ∞ Φ {Z | mdet Z ≠ 0} →
    (∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K → ∃ CK : ℝ, ∀ (j : ℕ), (j : ℝ) ≤ C₁ * (s : ℝ) ^ 2 →
      ∀ Z : Msq s, mdet Z ∈ K → ‖iteratedFDeriv ℝ j Φ Z‖ ≤ CK * fNorm Z ^ (-A)) →
    ∀ (ν : Msq s → Measure (Msq s × Msq s)), (∀ g, mdet g ≠ 0 → IsOrbMeasLU cψ g (ν g)) →
    ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K → ∀ ε > 0, ∃ δ > 0, ∀ t c : ℂ, t ≠ 0 → ‖t‖ < δ →
      c * t ^ (s - 1) ∈ K →
      ‖(‖t‖ ^ ((s - 1) ^ 2) : ℝ) • OmG cψ (ν (gTC s t c)) Φ (gTC s t c) -
        ((s : ℂ)⁻¹ • ∑ z ∈ (Polynomial.nthRoots s ((-1) ^ (s + 1) * (c * t ^ (s - 1)))).toFinset,
          ((‖z‖ ^ ((s - 1) ^ 2) : ℝ) * ph z * psiC cψ (s * z / t)) • OmG cψ (ν (gZW s z)) Φ (gZW s z))‖ ≤ ε

end Further

end Formalism.MainNotions.S.UnitaryLevelOperators
