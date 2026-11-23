import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermTop

namespace Formalism.FourierDecayAlt.P.CutBP.GT

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

abbrev HS (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] : Type :=
  PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp)

abbrev HT (I : Type) [Fintype I] (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] : Type :=
  PiLp 2 (fun _ : I => HS Wp Wq)

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {I : Type} [Fintype I]

def vecT (p : KB.Pl P Wp Wq) (N : ℕ) (c : I → ℝ) (Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (L : I → (Wq →L[ℂ] Wp) →L[ℂ] HS Wp Wq) (Q : C.LPt) : HT I Wp Wq :=
  WithLp.toLp 2 (fun i => ((√(c i) * omT p N Q : ℝ) : ℂ) • L i (p.V (Fi i) Q))

theorem vecT_apply (p : KB.Pl P Wp Wq) (N : ℕ) (c : I → ℝ) (Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (L : I → (Wq →L[ℂ] Wp) →L[ℂ] HS Wp Wq) (Q : C.LPt) (i : I) :
    vecT p N c Fi L Q i = ((√(c i) * omT p N Q : ℝ) : ℂ) • L i (p.V (Fi i) Q) := rfl

theorem inner_vecT (p : KB.Pl P Wp Wq) (N : ℕ) (c : I → ℝ) (hc : ∀ i, 0 ≤ c i)
    (Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (L : I → (Wq →L[ℂ] Wp) →L[ℂ] HS Wp Wq) (Q Q' : C.LPt) :
    ⟪vecT p N c Fi L Q, vecT p N c Fi L Q'⟫_ℂ =
      ∑ i, (c i : ℂ) * ⟪(omT p N Q : ℂ) • L i (p.V (Fi i) Q), (omT p N Q' : ℂ) • L i (p.V (Fi i) Q')⟫_ℂ := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hs : ((√(c i) : ℝ) : ℂ) * ((√(c i) : ℝ) : ℂ) = (c i : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hc i)]
  rw [vecT_apply, vecT_apply, inner_smul_left, inner_smul_right, inner_smul_left, inner_smul_right]
  simp only [Complex.conj_ofReal, Complex.ofReal_mul, map_mul]
  rw [← hs]
  ring

def utT (p : KB.Pl P Wp Wq) (N : ℕ) (c : I → ℝ) (Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (L : I → (Wq →L[ℂ] Wp) →L[ℂ] HS Wp Wq) (s : ℕ) (h : C.LPt) (x D : ℂ) : HT I Wp Wq :=
  ((‖x‖ ^ (s - 1) : ℝ) : ℂ) • vecT p N c Fi L (h ++ [(s - 1, x⁻¹), (1, x ^ (s - 1) * D)])

def btT (p : KB.Pl P Wp Wq) (N : ℕ) (c : I → ℝ) (Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (L : I → (Wq →L[ℂ] Wp) →L[ℂ] HS Wp Wq) (s : ℕ) (h : C.LPt) (u : ℂ) : HT I Wp Wq :=
  if u = 0 then 0 else ((Real.pi ^ (s - 1) * ((s : ℝ) * ‖u‖ ^ (s - 1))⁻¹ : ℝ) : ℂ) • vecT p N c Fi L (h ++ [(s, u)])

end place

structure VecHyp {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {I : Type} [Fintype I]
    (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (c : I → ℝ)
    (Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (L : I → (Wq →L[ℂ] Wp) →L[ℂ] HS Wp Wq) : Prop where
  hc : ∀ i, 0 ≤ c i
  hFi : ∀ i, KB.CptCoef p.T.base (Fi i)
  gram : ∀ Q Q' : C.LPt, TBB.NP p nn F (P.r + 1) w Q Q' =
    ∑ i, (c i : ℂ) * ⟪(omT p w.length Q' : ℂ) • L i (p.V (Fi i) Q'), (omT p w.length Q : ℂ) • L i (p.V (Fi i) Q)⟫_ℂ
  int : ∀ a : C.LPt, D.IsLocPt a P.r →
    Integrable (fun c : ℂ => TBB.NP p nn F (P.r + 1) w (a ++ [(1, c)]) (a ++ [(1, c)]))
  fibre : ∀ a a' : C.LPt, D.IsLocPt a P.r → D.IsLocPt a' P.r →
    TBB.NP p nn F P.r w a a' = ∫ c : ℂ, TBB.NP p nn F (P.r + 1) w (a ++ [(1, c)]) (a' ++ [(1, c)])
  cont : ∀ i (m : ℕ) (h : C.LPt), (∀ q ∈ h, 1 ≤ q.1 ∧ q.2 ≠ 0) → 1 ≤ m → D.ptSize h + m = P.r + 1 →
    ContinuousOn (fun c : ℂ => (omT p w.length (h ++ [(m, c)]) : ℂ) • p.V (Fi i) (h ++ [(m, c)])) {0}ᶜ

def FieldMemU : Prop :=
  ∀ {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {I : Type} [Fintype I]
    (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (c : I → ℝ)
    (Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (L : I → (Wq →L[ℂ] Wp) →L[ℂ] HS Wp Wq),
    VecHyp p nn F w c Fi L → ∀ (b s : ℕ), 1 ≤ b → 2 ≤ s → b + s = P.r + 2 → ∀ h : C.LPt, D.IsLocPt h (b - 1) →
    ∀ x : ℂ, x ≠ 0 → MemLp (utT p w.length c Fi L s h x) 2 volume

def FieldSup : Prop :=
  ∀ {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {I : Type} [Fintype I]
    (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (c : I → ℝ)
    (Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (L : I → (Wq →L[ℂ] Wp) →L[ℂ] HS Wp Wq),
    VecHyp p nn F w c Fi L → ∀ (b s : ℕ), 1 ≤ b → 2 ≤ s → b + s = P.r + 2 → ∀ h : C.LPt, D.IsLocPt h (b - 1) →
    ∀ x : ℂ, x ≠ 0 → ∫ D, ‖utT p w.length c Fi L s h x D‖ ^ 2 = TBB.Ew p nn F P.r w (h ++ [(s - 1, x⁻¹)])

def FieldMeas : Prop :=
  ∀ {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {I : Type} [Fintype I]
    (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (c : I → ℝ)
    (Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (L : I → (Wq →L[ℂ] Wp) →L[ℂ] HS Wp Wq),
    VecHyp p nn F w c Fi L → ∀ (b s : ℕ), 1 ≤ b → 2 ≤ s → b + s = P.r + 2 → ∀ h : C.LPt, D.IsLocPt h (b - 1) →
    StronglyMeasurable (btT p w.length c Fi L s h)

def FieldLoc : Prop :=
  ∀ {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {I : Type} [Fintype I]
    (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (c : I → ℝ)
    (Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (L : I → (Wq →L[ℂ] Wp) →L[ℂ] HS Wp Wq),
    VecHyp p nn F w c Fi L → ∀ (b s : ℕ), 1 ≤ b → 2 ≤ s → b + s = P.r + 2 → ∀ h : C.LPt, D.IsLocPt h (b - 1) →
    ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K → IntegrableOn (fun z => ‖PBK.bz s (btT p w.length c Fi L s h) z‖ ^ 2) K

end

end Formalism.FourierDecayAlt.P.CutBP.GT
