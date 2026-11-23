import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Columns
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Formalism.LocalRingCardinality.SpanPowerMembership.EntPlNonempty

open NumberField Formalism.BasicNotions Classical

noncomputable section

namespace Formalism.L2.Ker

open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.G

abbrev Cw (D : D7) (w : D.what₂.places.Pl) : Type := ℂ_[D.what₂.places.resChar w]

abbrev FrP (D : D7) (w : D.what₂.places.Pl) (N : ℕ) : Type := D.what₂.Tau → Matrix (Fin N) (Fin N) (Cw D w)

abbrev PlaceMatrixFamily (D : D7) : Type :=
  ∀ u μ (w : D.what₂.places.Pl) (i : ℕ), (D.chTw u μ).cls i → D.what₂.Tau → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) (Cw D w)

section Obj

variable {D : D7} (P : Examples₂.EntPl D) (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) (B : PlaceMatrixFamily D)

def IsBasC (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl) (i : ℕ) (c : (D.chTw u μ).cls i) (τ : D.what₂.Tau)
    (M : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) (Cw D w)) : Prop :=
  GL3Columns.BasR D (P.lam w) τ ((O u μ).lat i c).1 M ∧ ∀ a b, ∃ x : D.what₂.LL, M a b = P.iL w x

def basC : PlaceMatrixFamily D := fun u μ w i c τ => Classical.epsilon (IsBasC P O u μ w i c τ)

def BasEx : Prop :=
  ∀ u μ (w : D.what₂.places.Pl) i, i ≤ D.R.m → ∀ (c : (D.chTw u μ).cls i) τ, ∃ M, IsBasC P O u μ w i c τ M

def BasOk : Prop :=
  ∀ u μ (w : D.what₂.places.Pl) i, i ≤ D.R.m → ∀ (c : (D.chTw u μ).cls i) τ, GL3Columns.BasR D (P.lam w) τ ((O u μ).lat i c).1 (B u μ w i c τ)

def thAtW (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl) (i : ℕ) (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)) :
    MvPowerSeries ((Bool × HH D) × Fin (D.R.N i) × Fin (D.R.N (i + 1))) (Cw D w) :=
  atLin (fun (k : D.what₂.Tau × Fin (D.R.N (i + 1)) × Fin (D.R.N i)) (j : (Bool × HH D) × Fin (D.R.N i) × Fin (D.R.N (i + 1))) =>
      if tauPl D j.1 = k.1 then
        1 * lamC (P.lam w) ((O u μ).dgen k.1) * B u μ w (i + 1) c' k.1 k.2.1 j.2.2 * (B u μ w i c k.1)⁻¹ j.2.1 k.2.2
      else 0)
    (fun j => MvPowerSeries.X j) (pSer D (P.lam w) ((O u μ).Th i c c'))

def twB (D : D7) (u : D.what₂.Word) (μ : D.what₂.Tup) : ℕ → D.what₂.Tau → ℤ
  | 0 => (D.chTw u μ).sSharp 0
  | j + 1 => (D.chTw u μ).sDiv j

def polV (D : D7) (u : D.what₂.Word) : (i : ℕ) → Submodule D.what₂.LL (MvPolynomial (GL3Theta.FrV D (D.R.N i)) D.what₂.LL)
  | 0 => WtPol D.what₂.LL (nuT D u 0)
  | j + 1 => WtPol D.what₂.LL (extNu (D.R.N (j + 1)) (nuT D u j))

def evP (u : D.what₂.Word) (μ : D.what₂.Tup) (i : ℕ) : polV D u i →ₛₗ[D.what₂.embLL] ((D.chTw u μ).Y i → ℂ) where
  toFun v := fun y => (∏ τ, ((D.chTw u μ).de i y τ) ^ (-(twB D u μ i τ))) *
    GL3Theta.evFr D (MvPolynomial.map D.what₂.embLL (v : MvPolynomial (GL3Theta.FrV D (D.R.N i)) D.what₂.LL)) ((O u μ).frm i y)
  map_add' a b := by
    funext y
    simp [GL3Theta.evFr, mul_add]
  map_smul' a b := by
    funext y
    simp [GL3Theta.evFr, MvPolynomial.smul_eq_C_mul]
    ring

abbrev ValQ (u : D.what₂.Word) (μ : D.what₂.Tup) (i : ℕ) : Type := (polV D u i) ⧸ LinearMap.ker (evP O u μ i)

def evC (u : D.what₂.Word) (μ : D.what₂.Tup) (i : ℕ) : ValQ O u μ i →ₛₗ[D.what₂.embLL] ((D.chTw u μ).Y i → ℂ) :=
  (LinearMap.ker (evP O u μ i)).liftQ (evP O u μ i) le_rfl

def secC (u : D.what₂.Word) (μ : D.what₂.Tup) (i : ℕ) : ValQ O u μ i →ₗ[D.what₂.LL] polV D u i :=
  Classical.choose ((LinearMap.ker (evP O u μ i)).mkQ.exists_rightInverse_of_surjective (Submodule.range_mkQ _))

def canM (D : D7) (w : D.what₂.places.Pl) (N : ℕ) (nu : Bool × HH D → YoungDiagram) :
    Module.Dual (Cw D w) (MvPolynomial ((Bool × HH D) × ℕ × Fin N) (Cw D w)) →ₗ[Cw D w] (FrP D w N → Cw D w) where
  toFun ph := fun y => ph (GL3Columns.DeX N nu fun s => GL3Columns.colsOf (y (tauPl D s)))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def canInv (D : D7) (w : D.what₂.places.Pl) (N : ℕ) (nu : Bool × HH D → YoungDiagram) :
    (FrP D w N → Cw D w) →ₗ[Cw D w] Module.Dual (Cw D w) (MvPolynomial ((Bool × HH D) × ℕ × Fin N) (Cw D w)) :=
  Classical.epsilon fun g => ∀ F ∈ LinearMap.range (canM D w N nu), canM D w N nu (g F) = F

def onMin (D : D7) (w : D.what₂.places.Pl) (N : ℕ) (nu : Bool × HH D → YoungDiagram) :
    Module.Dual (Cw D w) (MvPolynomial ((Bool × HH D) × ℕ × Fin N) (Cw D w)) →ₗ[Cw D w] (KM.ColChoice N nu → Cw D w) :=
  LinearMap.pi fun I => LinearMap.applyₗ (MvPolynomial.map (Int.castRingHom (Cw D w)) (KM.nablaX N nu I))

def srcPol (u : D.what₂.Word) (μ : D.what₂.Tup) (i : ℕ) (v : MvPolynomial (GL3Theta.FrV D (D.R.N i)) D.what₂.LL) : MvPolynomial (GL3Theta.FrV D (D.R.N i)) D.what₂.LL :=
  v * ∏ τ, frDet D.what₂.LL (D.R.N i) τ ^ ((D.chTw u μ).sSharp i τ - twB D u μ i τ).toNat

def atBas (w : D.what₂.places.Pl) {N : ℕ} (M : D.what₂.Tau → Matrix (Fin N) (Fin N) (Cw D w)) :
    MvPolynomial (GL3Theta.FrV D N) D.what₂.LL →ₛₗ[P.iL w] (FrP D w N → Cw D w) where
  toFun Q := fun y => MvPolynomial.eval (fun k : GL3Theta.FrV D N => (M k.1 * y k.1) k.2.1 k.2.2) (MvPolynomial.map (P.iL w) Q)
  map_add' a b := by
    funext y
    simp
  map_smul' a b := by
    funext y
    simp [MvPolynomial.smul_eq_C_mul]

def srcFun (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl) (i : ℕ) (c : (D.chTw u μ).cls i) :
    polV D u i →ₛₗ[P.iL w] (FrP D w (D.R.N i) → Cw D w) :=
  ((∏ τ, (B u μ w i c τ).det ^ (-(D.chTw u μ).sSharp i τ)) • (LinearMap.id : (FrP D w (D.R.N i) → Cw D w) →ₗ[Cw D w] _)).comp
    ((atBas P w (B u μ w i c)).comp
      ((LinearMap.mulRight D.what₂.LL (∏ τ, frDet D.what₂.LL (D.R.N i) τ ^ ((D.chTw u μ).sSharp i τ - twB D u μ i τ).toNat)).comp (polV D u i).subtype))

def prSC (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl) (i : ℕ) (c : (D.chTw u μ).cls i) :
    ValQ O u μ i →ₛₗ[P.iL w] Module.Dual (Cw D w) (MvPolynomial ((Bool × HH D) × ℕ × Fin (D.R.N i)) (Cw D w)) :=
  (canInv D w (D.R.N i) (nuD D u i)).comp ((srcFun P B u μ w i c).comp (secC O u μ i))

def tgtFun (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl) (i : ℕ) (c' : (D.chTw u μ).cls (i + 1)) :
    polV D u (i + 1) →ₛₗ[P.iL w] (FrP D w (D.R.N (i + 1)) → Cw D w) :=
  ((∏ τ, (B u μ w (i + 1) c' τ).det ^ (-(D.chTw u μ).sDiv i τ)) • (LinearMap.id : (FrP D w (D.R.N (i + 1)) → Cw D w) →ₗ[Cw D w] _)).comp
    ((atBas P w (B u μ w (i + 1) c')).comp (polV D u (i + 1)).subtype)

def tgtPh (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl) (i : ℕ) (c' : (D.chTw u μ).cls (i + 1)) :
    ValQ O u μ (i + 1) →ₛₗ[P.iL w] Module.Dual (Cw D w) (MvPolynomial ((Bool × HH D) × ℕ × Fin (D.R.N (i + 1))) (Cw D w)) :=
  (canInv D w (D.R.N (i + 1)) (nuD D u i)).comp ((tgtFun P B u μ w i c').comp (secC O u μ (i + 1)))

def prTC (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl) (i : ℕ) (c' : (D.chTw u μ).cls (i + 1)) :
    ValQ O u μ (i + 1) →ₛₗ[P.iL w] (KM.ColChoice (D.R.N (i + 1)) (nuD D u i) → Cw D w) :=
  (onMin D w (D.R.N (i + 1)) (nuD D u i)).comp (tgtPh P O B u μ w i c')

def unF (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl) (i : ℕ) (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)) : Cw D w :=
  (lamC (P.lam w) ((GL3Theta.rhoOf D (O u μ).mt i ((O u μ).dt i c) : ℂˣ) : ℂ) * ∏ τ, (B u μ w i c τ).det ^ ((D.chTw u μ).sSharp i τ)) *
    (lamC (P.lam w) ((GL3Theta.rhoOf' D (O u μ).mt i ((O u μ).dt (i + 1) c') : ℂˣ) : ℂ) *
      ∏ τ, (B u μ w (i + 1) c' τ).det ^ (-(D.chTw u μ).sDiv i τ))

def unC (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl) (i : ℕ) (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)) : Cw D w :=
  if unF P O B u μ w i c c' = 0 then 1 else unF P O B u μ w i c c'

def CanS : Prop :=
  ∀ u μ (w : D.what₂.places.Pl) i, i < D.R.m → ∀ (c : (D.chTw u μ).cls i) (v : polV D u i),
    srcFun P B u μ w i c v ∈ LinearMap.range (canM D w (D.R.N i) (nuD D u i))

def CanT : Prop :=
  ∀ u μ (w : D.what₂.places.Pl) i, i < D.R.m → ∀ (c' : (D.chTw u μ).cls (i + 1)) (v : polV D u (i + 1)),
    tgtFun P B u μ w i c' v ∈ LinearMap.range (canM D w (D.R.N (i + 1)) (nuD D u i))

def NuFits (D : D7) {N : ℕ} (nu : Bool × HH D → YoungDiagram) (ν : D.what₂.Tau → Fin N → ℕ) : Prop :=
  (∀ z (r : Fin N), (nu z).rowLen r = ν (tauPl D z) r) ∧ ∀ z r, N ≤ r → (nu z).rowLen r = 0

def CanOnto : Prop :=
  ∀ (w : D.what₂.places.Pl) (N : ℕ) (nu : Bool × HH D → YoungDiagram) (ν : D.what₂.Tau → Fin N → ℕ), NuFits D nu ν →
    ∀ Q ∈ WtPol D.what₂.LL ν, ∀ M : FrP D w N, atBas P w M Q ∈ LinearMap.range (canM D w N nu)

def TwLe (D : D7) : Prop := ∀ u μ i, i < D.R.m → ∀ τ, twB D u μ i τ ≤ (D.chTw u μ).sSharp i τ

variable (Dx : DivX D) (Tw : TwForms D)

structure KerEntHyp : Prop where
  val : ∀ u μ w, LevFree Dx u μ w → ∀ i, i < D.R.m → ∀ c' (v' : ValQ O u μ (i + 1)) I,
    ∃ b : D.what₂.LL, ‖prTC P O B u μ w i c' v' I‖ = ‖P.iL w b‖
  latS : ∀ u μ w, LevFree Dx u μ w → ∀ i, i < D.R.m → ∀ φ : (D.chTw u μ).cls i → (D.chTw u μ).Y i → ℂ,
    (∃ x ∈ locW D.what₂.places w ((Tw.fm u μ).lat i).L, (Tw.fm u μ).emb i x = φ) ↔
      (φ ∈ (Tw.fm u μ).Fi i ∧ ∀ c, ∃ v : ValQ O u μ i, evC O u μ i v = φ c ∧
        ∀ J : KM.ColChoice (D.R.N i) (nuD D u i),
          ‖prSC P O B u μ w i c v (MvPolynomial.map (Int.castRingHom _) (KM.nablaX (D.R.N i) (nuD D u i) J))‖ ≤ 1)
  latT : ∀ u μ w, LevFree Dx u μ w → ∀ i, i < D.R.m →
    ∀ φ : (D.chTw u μ).cls (i + 1) → (D.chTw u μ).Y (i + 1) → ℂ,
    (∃ y ∈ locW D.what₂.places w ((Tw.fm u μ).lat (i + 1)).L, (Tw.fm u μ).emb (i + 1) y = φ) ↔
      (φ ∈ (Tw.fm u μ).Fi (i + 1) ∧ ∀ c', ∃ v' : ValQ O u μ (i + 1), evC O u μ (i + 1) v' = φ c' ∧
        ∀ I, ‖prTC P O B u μ w i c' v' I‖ ≤ 1)
  kform : ∀ u μ w, LevFree Dx u μ w → ∀ i, i < D.R.m → ∀ (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1))
    (v : ValQ O u μ i) (v' : ValQ O u μ (i + 1)),
    evC O u μ (i + 1) v' = (D.chTw u μ).Kmap i c c' (evC O u μ i v) →
    ∀ I, prTC P O B u μ w i c' v' I =
      unC P O B u μ w i c c' *
        prSC P O B u μ w i c v (KM.applyAt0 (D.R.N i) (D.R.N (i + 1)) (D.what₂.places.resChar w) (thAtW P O B u μ w i c c')
          (KM.Gxz (D.R.N i) (D.R.N (i + 1)) (nuD D u i) I))

theorem evC_inj (u : D.what₂.Word) (μ : D.what₂.Tup) (i : ℕ) : Function.Injective (evC O u μ i) := by
  rw [← LinearMap.ker_eq_bot]
  exact Submodule.ker_liftQ_eq_bot _ _ _ le_rfl

theorem unC_ne (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl) (i : ℕ) (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)) :
    unC P O B u μ w i c c' ≠ 0 := by
  unfold unC
  split_ifs with h
  · exact one_ne_zero
  · exact h

variable {Dx Tw}

def kerEntC (h : KerEntHyp P O B Dx Tw) : KerEnt D Dx Tw where
  lam := P.lam
  iL := P.iL
  iL_lam := P.iL_lam
  iL_int := P.iL_int
  Th := thAtW P O B
  VQ := fun u μ i _ => ValQ O u μ i
  ev := fun u μ i _ => evC O u μ i
  ev_inj := fun u μ i _ => evC_inj O u μ i
  prS := prSC P O B
  prT := prTC P O B
  prT_val := h.val
  lat_S := h.latS
  levelFree_lattice_condition := h.latT
  un := unC P O B
  un_ne := unC_ne P O B
  kform := h.kform

end Obj

end Formalism.L2.Ker

end
