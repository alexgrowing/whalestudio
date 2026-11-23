import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGerm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TendstoRatioPow

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate ENNReal InnerProductSpace

noncomputable section

open Classical

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def GermContAt (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (K N : ℕ) :
    Prop :=
  ∀ b s : ℕ, 1 ≤ b → 2 ≤ s → b + s - 1 ≤ P.r + 1 → ∀ h : C.LPt, D.IsLocPt h (b - 1) → ∀ w, TBB.AdmW P p.l0 Y w →
    w.length + K ≤ N → ContinuousOn (fun z : ℂ => TBB.Ew p nn F (b + s - 1) w (h ++ [(s, z)])) {0}ᶜ

def GermDataAt (lev : ℕ → Prop) (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (Y : Finset ℝ) (K N : ℕ) : Prop :=
  ∀ b s : ℕ, 1 ≤ b → 2 ≤ s → b + s - 1 ≤ P.r + 1 → lev (b + s - 1) → ∀ h : C.LPt, D.IsLocPt h (b - 1) →
    ∀ w, TBB.AdmW P p.l0 Y w → w.length + K ≤ N →
    (∀ w', TBB.IsExt P p.l0 Y N K w w' →
      BddAbove (Set.range fun t : {t : ℂ // t ≠ 0} => TBB.Ew p nn F (b + s - 2) w' (h ++ [(s - 1, t.1)]))) →
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (ut : ℂ → ℂ → H) (bt : ℂ → H) (β ε' η : ℂ) (SS κ₁ κ₂ : ℝ),
      0 ≤ κ₂ ∧ κ₂ ≤ Real.pi * κ₁ ∧ (η = 1 ∨ η = -1) ∧
      PBK.GermD s β ε' ({()} : Finset Unit) (fun _ => ut) (fun _ => bt) SS ∧
      (∀ σ z : ℂ, P5.fsv σ z = G.psi β (η * σ * z)) ∧
      (∀ t t' : ℂ, t ≠ 0 → t' ≠ 0 →
        ‖TBB.NP p nn F (b + s - 2) w (h ++ [(s - 1, t)]) (h ++ [(s - 1, t')])‖ =
          κ₁ * ‖PBK.gramL volume (PBK.Uc s fun _ => ut) (PBK.Uc s fun _ => ut) ((), t⁻¹) ((), t'⁻¹)‖) ∧
      ∀ z : ℂ, z ≠ 0 → TBB.Ew p nn F (b + s - 1) w (h ++ [(s, z)]) = κ₂ * ‖PBK.bz s bt z‖ ^ 2

end place

def GermContAll : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (K N : ℕ) (Cb : ℝ),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base F → (∀ y, 0 < nn y) → GermContAt p nn F Y K N

def GermDataLowAll : Prop :=
  P5.ThmPActual → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (K N : ℕ) (Cb : ℝ),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base F → (∀ y, 0 < nn y) →
    GermDataAt (fun i => i ≤ P.r) p nn F Y K N

def GermDataTopAll : Prop :=
  P5.ThmPActual → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (K N : ℕ) (Cb : ℝ),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base F → (∀ y, 0 < nn y) →
    GermDataAt (fun i => i = P.r + 1) p nn F Y K N

def PropGMean : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (s : ℕ) (β ε' η : ℂ)
    (ut : ℂ → ℂ → H) (bt : ℂ → H) (SS κ₁ κ₂ : ℝ) (E : ℂ → ℝ) (Nk : ℂ → ℂ → ℂ),
    2 ≤ s → 0 ≤ κ₂ → κ₂ ≤ Real.pi * κ₁ → (η = 1 ∨ η = -1) →
    PBK.GermD s β ε' ({()} : Finset Unit) (fun _ => ut) (fun _ => bt) SS →
    (∀ σ z : ℂ, P5.fsv σ z = G.psi β (η * σ * z)) →
    (∀ t t' : ℂ, t ≠ 0 → t' ≠ 0 →
      ‖Nk t t'‖ = κ₁ * ‖PBK.gramL volume (PBK.Uc s fun _ => ut) (PBK.Uc s fun _ => ut) ((), t⁻¹) ((), t'⁻¹)‖) →
    (∀ z : ℂ, z ≠ 0 → E z = κ₂ * ‖PBK.bz s bt z‖ ^ 2) →
    Integrable E ∧
      ∀ ω₁ ω₂ : ℂ, (conj ω₁ * ω₂).im ≠ 0 → ∃ A : ℂ → ℂ, PDDual ω₁ ω₂ A ∧
        ∀ σ : ℂ, TBB.InDual ω₁ ω₂ σ →
          (‖(Real.pi⁻¹ : ℂ) * (∫ z : ℂ, P5.fsv σ z * (E z : ℂ)) + A σ‖₊ : ℝ≥0∞) ≤
            limsup (fun t : ℂ => (‖Nk t (t⁻¹ + σ)⁻¹‖₊ : ℝ≥0∞)) (𝓝[≠] 0)

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem germAtPD_of_parts (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ)
    (K N : ℕ) (hC : GermContAt p nn F Y K N) (hL : GermDataAt (fun i => i ≤ P.r) p nn F Y K N)
    (hT : GermDataAt (fun i => i = P.r + 1) p nn F Y K N) (hM : PropGMean) : GermAtPD p nn F Y K N := by
  intro b s hb hs hbs h hh w hw hN hBdd
  have hcont := hC b s hb hs hbs h hh w hw hN
  have hdata : ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (ut : ℂ → ℂ → H) (bt : ℂ → H) (β ε' η : ℂ) (SS κ₁ κ₂ : ℝ),
      0 ≤ κ₂ ∧ κ₂ ≤ Real.pi * κ₁ ∧ (η = 1 ∨ η = -1) ∧
      PBK.GermD s β ε' ({()} : Finset Unit) (fun _ => ut) (fun _ => bt) SS ∧
      (∀ σ z : ℂ, P5.fsv σ z = G.psi β (η * σ * z)) ∧
      (∀ t t' : ℂ, t ≠ 0 → t' ≠ 0 →
        ‖TBB.NP p nn F (b + s - 2) w (h ++ [(s - 1, t)]) (h ++ [(s - 1, t')])‖ =
          κ₁ * ‖PBK.gramL volume (PBK.Uc s fun _ => ut) (PBK.Uc s fun _ => ut) ((), t⁻¹) ((), t'⁻¹)‖) ∧
      ∀ z : ℂ, z ≠ 0 → TBB.Ew p nn F (b + s - 1) w (h ++ [(s, z)]) = κ₂ * ‖PBK.bz s bt z‖ ^ 2 := by
    rcases Nat.lt_or_ge (b + s - 1) (P.r + 1) with hlt | hge
    · exact hL b s hb hs hbs (by omega) h hh w hw hN hBdd
    · exact hT b s hb hs hbs (by omega) h hh w hw hN hBdd
  obtain ⟨H, _, _, _, ut, bt, β, ε', η, SS, κ₁, κ₂, hκ₂, hκ, hη, hGD, hpsi, hNk, hE⟩ := hdata
  obtain ⟨hint, hlat⟩ := hM H s β ε' η ut bt SS κ₁ κ₂
    (fun z => TBB.Ew p nn F (b + s - 1) w (h ++ [(s, z)]))
    (fun t t' => TBB.NP p nn F (b + s - 2) w (h ++ [(s - 1, t)]) (h ++ [(s - 1, t')]))
    hs hκ₂ hκ hη hGD hpsi hNk hE
  exact ⟨hcont, hint, hlat⟩

end place

theorem germCutPD_of_parts (hA : P5.ThmPActual) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}
    (p : KB.Pl P Wp Wq) (nn χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (K N : ℕ) (Cb : ℝ)
    (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (hF : KB.CptCoef p.T.base F) (hχ : C6.IsCut0 χ)
    (hnn : ∀ y, 0 < nn y) (hC : GermContAll) (hL : GermDataLowAll) (hT : GermDataTopAll) (hM : PropGMean) :
    GermCutPD p nn χ F Y K N := by
  intro ε _
  have hGc : KB.CptCoef p.T.base (D.cutF p.T.base χ F ε) := cptCoef_cutF p.T.base hχ hF ε
  exact germAtPD_of_parts p nn _ Y K N (hC Wp Wq P p nn _ Y K N Cb hCb hGc hnn)
    (hL hA Wp Wq P p nn _ Y K N Cb hCb hGc hnn) (hT hA Wp Wq P p nn _ Y K N Cb hCb hGc hnn) hM

end

end Formalism.FourierDecayAlt.P.CutBP

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt

theorem block_growth_bound_of_germ_data (hA : P5.ThmPActual) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}
    (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (K N : ℕ) (Cb : ℝ)
    (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (hG : KB.CptCoef p.T.base G) (hnn : ∀ y, 0 < nn y)
    (hC : GermContAll) (hL : GermDataLowAll) (hT : GermDataTopAll) (hM : PropGMean) : TBB.BlockGrowthBound p nn G Y K N :=
  block_growth_bound_of_positive_germ p nn G Y K N (posAt_of_cpt hA p nn G Y N (fun y => (hnn y).le) hG)
    (germAtPD_of_parts p nn G Y K N (hC Wp Wq P p nn G Y K N Cb hCb hG hnn) (hL hA Wp Wq P p nn G Y K N Cb hCb hG hnn)
      (hT hA Wp Wq P p nn G Y K N Cb hCb hG hnn) hM)

end Formalism.FourierDecayAlt.P.CutBP
