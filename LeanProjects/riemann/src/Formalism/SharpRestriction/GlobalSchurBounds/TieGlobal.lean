import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.GlobalSchurBounds.Chosen
import Formalism.SizeWindowBrackets.SChain
import Formalism.SizeWindowBrackets.GaloisToProductIsIso

noncomputable section

namespace Formalism.MainNotions

open Formalism.BasicNotions Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost

instance (D : D7) : Nonempty D.what₂.Word := ⟨D.u₀⟩

def hval (φ : Formalism.HC.Frame) (h : φ.A) : ℕ := Formalism.HC.Frame.A.val h

def sgnZ (s : ℤˣ) : ZMod 2 := if s = 1 then 0 else 1

def gcode (φ : Formalism.HC.Frame) (g : φ.GG) : (ZMod 2 × ZMod 2) × ℕ :=
  ((sgnZ g.1.2, sgnZ g.1.1), Formalism.HC.Frame.A.val (φ.iotaInv g.2))

def mcode (φ : Formalism.HC.Frame) (g : E0 × φ.A) : (ZMod 2 × ZMod 2) × ℕ := (g.1, hval φ g.2)

def recOf {φ : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ) : (ZMod H.condN)ˣ →* Multiplicative (E0 × φ.A) where
  toFun u := Multiplicative.ofAdd
    ((Multiplicative.toAdd (sgn2 (H.art u).1.2), Multiplicative.toAdd (sgn2 (H.art u).1.1)), φ.iotaInv (H.art u).2)
  map_one' := by
    simp only [Prod.snd_one, Prod.fst_one, map_one]
    rfl
  map_mul' u v := by
    simp only [Prod.snd_mul, Prod.fst_mul, map_mul]
    rfl

def arithOf {φ : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ) : ArithData φ.A := cftData H.q H.d (recOf H)

section
variable {eps : ℝ} (Fm : FamP eps) (x : ℝ) (φ : Formalism.HC.Frame) (m f q d : ℕ)

def TiePts (pt : φ.A → Fm.Ix x) (av bv : ℕ → ℤ) : Prop :=
  ∀ u0 : φ.A,
    (Fm.D x (pt u0)).R.toFrame = φ ∧ (Fm.D x (pt u0)).R.m = m ∧ (Fm.D x (pt u0)).R.f = f ∧
    (Fm.D x (pt u0)).host.q = q ∧ (Fm.D x (pt u0)).host.d = d ∧
    (Fm.D x (pt u0)).host.u0.val = hval φ u0 ∧
    ∀ t : (Fm.D x (pt u0)).host.TT,
      (Fm.L x (pt u0)).aT t = av (t : (Fm.D x (pt u0)).R.A).val ∧
      (Fm.L x (pt u0)).bT t = bv (t : (Fm.D x (pt u0)).R.A).val

variable {φ m f}

def TieGlobal (pt : φ.A → Fm.Ix x) {Top : Type}
    (Dd : Data φ.A (fun u0 => (Fm.D x (pt u0)).what₂.Word) Top m f) (Xpp η X' : ℝ) : Prop :=
  ∀ u0 : φ.A,
    Dd.a = (Fm.L x (pt u0)).sc.a ∧ Dd.b = (Fm.L x (pt u0)).sc.b ∧ Dd.b' = (Fm.L x (pt u0)).sc.b' ∧
    Dd.k = ((Fm.D x (pt u0)).R.k : ℝ) ∧ Dd.L = (Fm.L x (pt u0)).sc.L ∧ Dd.La = (Fm.L x (pt u0)).La ∧
    Dd.B0 = (Fm.L x (pt u0)).B0 ∧ Dd.Nc = (Fm.L x (pt u0)).Nc ∧
    Dd.gam = Real.eulerMascheroniConstant ∧ Dd.LpL = (Fm.L x (pt u0)).logDerivativeAtOne ∧
    Dd.v = (Fm.D x (pt u0)).host.v ∧
    Dd.lg = Real.log (((Fm.D x (pt u0)).host.g 0 : ℝ) * ((Fm.D x (pt u0)).host.g 1 : ℝ)) ∧
    Dd.logGam = Real.log (GamL (Fm.L x (pt u0))) ∧
    Xpp = (Fm.L x (pt u0)).sc.X'' (Fm.D x (pt u0)).R.n ∧ η = (Fm.L x (pt u0)).etaSz ∧
    X' = (Fm.L x (pt u0)).sc.X'

def TieLocal (pt : φ.A → Fm.Ix x) {Top : Type}
    (Dd : Data φ.A (fun u0 => (Fm.D x (pt u0)).what₂.Word) Top m f) : Prop :=
  ∀ u0 : φ.A,
    (∀ u : (Fm.D x (pt u0)).what₂.Word,
      Dd.d u0 u = (((Fm.D x (pt u0)).div.Nu u).rank : ℝ) ∧
      Dd.T u0 u = (((Fm.D x (pt u0)).mem u).A.T : ℝ) ∧
      Dd.muN u0 u = ((Fm.D x (pt u0)).div.Nu u).mu ∧
      Dd.muMaxN u0 u = ((Fm.D x (pt u0)).div.Nu u).muMax ∧
      Dd.h u0 u = (Fm.D x (pt u0)).div.h u ∧
      Dd.muM u0 u = (((Fm.D x (pt u0)).fm u).lat 0).mu ∧
      Dd.muMaxM u0 u = (((Fm.D x (pt u0)).fm u).lat 0).muMax ∧
      ∀ j : Fin m, Dd.EeJ u0 u j =
        ∑ w ∈ (Fm.L x (pt u0)).supp, SizeData₂.sz w ((Fm.L x (pt u0)).E u (j.val + 1) w)) ∧
    Dd.muCC u0 = (Fm.D x (pt u0)).div.RR.muDual ∧
    Dd.muMinCC u0 = (Fm.D x (pt u0)).div.RR.muMinDual ∧
    Dd.Fo u0 = (Fm.L x (pt u0)).Fo ∧ Dd.Ga u0 = (Fm.L x (pt u0)).Ga ∧
    Dd.Ta u0 = ∑ w ∈ (Fm.L x (pt u0)).supp, SizeData₂.sz w ((Fm.L x (pt u0)).tau w) ∧
    Dd.IO u0 = ∑ w ∈ (Fm.L x (pt u0)).supp,
      SizeData₂.lwP w * ((Fm.D x (pt u0)).what₂.places.ramIdx w : ℝ) * (Fm.L x (pt u0)).io w ∧
    Dd.del u0 = (Fm.D x (pt u0)).what₂.delp

def TieArith (pt : φ.A → Fm.Ix x) (av : ℕ → ℤ) (D : ArithData φ.A) (ell : AddChar (E0 × φ.A) ℂ → ℂ)
    (TT T2 : Finset φ.A) (a : φ.A → ℝ) (w : φ.A → Fin m → E0 × φ.A → ℝ) : Prop :=
  (∀ h, h ∈ TT ↔ hval φ h ∈ Fm.TTn x) ∧
  (∀ u0 h, h ∈ T2 ↔ ∃ s ∈ (Fm.D x (pt u0)).host.T2, h = φ.dig s) ∧
  (∀ h, a h = (av (hval φ h) : ℝ)) ∧
  (∀ u0 (j : Fin m) (g : E0 × φ.A) (τ : (Fm.D x (pt u0)).what₂.Tau),
    gcode (Fm.D x (pt u0)).R.toFrame (((Fm.D x (pt u0)).eTau τ : (Fm.D x (pt u0)).R.Psi) : (Fm.D x (pt u0)).R.GG)
      = mcode φ g → w u0 j g = wj (Fm.D x (pt u0)) (j.val + 1) τ) ∧
  (∀ ψ : AddChar (E0 × φ.A) ℂ, ψ ≠ 0 → ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    (∀ n : ℕ, n ≠ 0 → χ (n : ZMod N) = primVal D ψ n) → ell ψ = GlobalTheoryTheory.logDerivativeAtOne χ)

end

def ChainTied {eps : ℝ} (Fm : FamP eps) (eD eL K cHH eK CL x : ℝ) : Prop :=
  ∃ (i0 : Fm.Ix x) (m f : ℕ) (pt : (Fm.D x i0).R.A → Fm.Ix x) (av bv : ℕ → ℤ)
    (Top : Type) (_ : Fintype Top)
    (Dd : Data (Fm.D x i0).R.A (fun u0 => (Fm.D x (pt u0)).what₂.Word) Top m f) (C : Consts) (Xpp : ℝ)
    (ell : AddChar (E0 × (Fm.D x i0).R.A) ℂ → ℂ) (N : ℕ) (TT T2 : Finset (Fm.D x i0).R.A) (a : (Fm.D x i0).R.A → ℝ)
    (w : (Fm.D x i0).R.A → Fin m → E0 × (Fm.D x i0).R.A → ℝ) (eT : Top ≃ TT)
    (eP : Fin f ≃ PhiSet (H := (Fm.D x i0).R.A)) (η X' θ : ℝ),
    TiePts Fm x (Fm.D x i0).R.toFrame m f (Fm.D x i0).host.q (Fm.D x i0).host.d pt av bv ∧
    TieGlobal Fm x pt Dd Xpp η X' ∧ TieLocal Fm x pt Dd ∧
    TieArith Fm x pt av (arithOf (Fm.D x i0).host.toHostRaw) ell TT T2 a w ∧
    Dd.x = x ∧ Dd.ε = eps ∧ C.eDiv ≤ eD ∧ C.eLoss ≤ eL ∧ C.cHH ≤ cHH ∧
    Ident Dd (arithOf (Fm.D x i0).host.toHostRaw) N ell TT a w eT eP ∧
    Formalism.LFunctionChainParameters.LChain.SizeData₂ Dd C Xpp ∧
    ErrWindows Dd C Xpp eK K ∧
    BNBounds Dd T2 ∧
    GrowthInequalityRemainingHyps (arithOf (Fm.D x i0).host.toHostRaw) ell N TT T2 a w x eps Dd.b Dd.b' η X' θ CL ∧
    CostWindows x (fPl (Fm.D x i0).R.A) Dd.b η θ ∧
    RestSize eps x (Fintype.card (Fm.D x i0).R.A) TT.card T2.card m Dd.b Dd.k Dd.a

theorem ChainTied.core_of {eps : ℝ} {Fm : FamP eps} {eD eL K cHH eK CL x : ℝ}
    (hF : ∀ i : Fm.Ix x, HostFacts (arithOf (Fm.D x i).host.toHostRaw))
    (h : ChainTied Fm eD eL K cHH eK CL x) : ChainCore eD eL K cHH eK CL eps x := by
  obtain ⟨i0, m, f, pt, av, bv, Top, iT, Dd, C, Xpp, ell, N, TT, T2, a, w, eT, eP, η, X', θ,
    -, -, -, -, h1, h2, h3, h4, h5, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨(Fm.D x i0).R.A, inferInstance, inferInstance, inferInstance, fun u0 => (Fm.D x (pt u0)).what₂.Word,
    fun _ => inferInstance, fun _ => inferInstance, Top, iT, m, f, Dd, C, Xpp, _, ell, N, TT, T2, a, w,
    eT, eP, η, X', θ, h1, h2, h3, h4, h5, hF i0, h7, h8, h9, h10, h11, h12, h13⟩

end Formalism.MainNotions

end
