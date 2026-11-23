import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousCutc

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Em

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace GlobalTheory.CompanionTheory.EisE

variable {D : D7} {n r t a b : ℕ}

theorem good_rows {S : Finset (Pl D)} {e : AE D} {η : Fin a → Mx D 1 b → ℂ} (h : ∀ i, Good S e (η i)) :
    Good S e (fun y : Mx D a b => ∏ i, η i (y.submatrix (fun _ => i) id)) := by
  intro y
  by_cases hy : IntOff S y
  · rw [if_pos hy]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hi : IntOff S (y.submatrix (fun _ : Fin 1 => i) id) := fun v hv _ j => hy v hv i j
    have := h i (y.submatrix (fun _ : Fin 1 => i) id)
    rw [if_pos hi] at this
    exact this
  · rw [if_neg hy]
    simp only [IntOff] at hy
    push Not at hy
    obtain ⟨v, hv, i, j, hij⟩ := hy
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    have := h i (y.submatrix (fun _ : Fin 1 => i) id)
    rw [if_neg (fun hi => hij (hi v hv 0 j))] at this
    exact this

theorem prod_nonneg_real {ι : Type} (s : Finset ι) (w : ι → ℂ) (h : ∀ i, 0 ≤ (w i).re ∧ (w i).im = 0) :
    0 ≤ (∏ i ∈ s, w i).re ∧ (∏ i ∈ s, w i).im = 0 := by
  refine Finset.prod_induction w (fun x : ℂ => 0 ≤ x.re ∧ x.im = 0) ?_ (by simp) fun i _ => h i
  rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
  simp [Complex.mul_re, Complex.mul_im, hx', hy', mul_nonneg hx hy]

theorem blockMatrix_add_zero {R : Type} (A : Matrix (Fin t) (Fin t) R) (b' : Matrix (Fin t) (Fin 0) R) (c : Matrix (Fin 0) (Fin t) R)
    (d : Matrix (Fin 0) (Fin 0) R) : bl (add_zero t) A b' c d = A := by
  have h : ∀ i : Fin t, (finSumFinEquiv.trans (finCongr (add_zero t))).symm i = Sum.inl i := by
    intro i
    rw [Equiv.symm_apply_eq]
    ext
    simp only [Equiv.trans_apply, finSumFinEquiv_apply_left]
    rfl
  ext i j
  simp only [bl, Matrix.submatrix_apply, h, Matrix.fromBlocks_apply₁₁]

theorem exists_isW (D : D7) (t : ℕ) : ∃ w : G D t, IsW w := by
  obtain ⟨⟨M⟩, -⟩ := GlobalTheory.CompanionTheory.JacobiMaps.mapsExist D t t 0 (add_zero t)
  refine ⟨M.w, ?_⟩
  have := M.w_mat
  simp only [blockMatrix_add_zero] at this
  exact this

theorem rsec_inv {hn : r + t = n} (M : Maps D hn) (m : Meas D r t) (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D r)
    {θ : InfFam D} (ω : G D n →* Module.End ℂ (schwartzA θ a n)) (Φ : schwartzA θ a n) {Ω : G D t → Mx D r t → ℂ} (u : G D t)
    (h1 : ω (M.emb u) Φ = Φ) (h2 : ∀ h, Ω (h * u) = Ω h) (g : G D t) :
    Rsec M m ψ b₀ (fun g => (ω g Φ).1 0) 1 Ω (g * u) = Rsec M m ψ b₀ (fun g => (ω g Φ).1 0) 1 Ω g := by
  have hf : ∀ x, (ω (x * M.emb u) Φ).1 0 = (ω x Φ).1 0 := fun x => by
    rw [map_mul, Module.End.mul_apply, h1]
  have e1 : ∀ y z, M.w * M.nzx z 0 * (M.sh y * M.emb (g * u) * 1) =
      (M.w * M.nzx z 0 * (M.sh y * M.emb g * 1)) * M.emb u := fun y z => by
    rw [map_mul]
    simp only [mul_one, mul_assoc]
  simp only [Rsec, Wz, h2, e1, hf]

section Xi

variable (V : HSp D) (b₀ : HermE D r) (hn : r + t = n)

def xiP (Φ : Mx D V.rank n → ℂ) (η : Mx D r t → ℂ) (z : Mx D V.rank r × Mx D V.rank t) : ℂ :=
  Φ (jn hn z.1 z.2) * conj (η (yv V b₀ z))

variable {V b₀ hn}

theorem continuous_xiP {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {Φ : Mx D V.rank n → ℂ} {η : Mx D r t → ℂ}
    (hΦ : Continuous Φ) (hη : Continuous η) : Continuous (xiP V b₀ hn Φ η) := by
  have hy := (GlobalTheory.CompanionTheory.RCellCont.continuity_characters_projection (t := t) hψ V b₀ (0 : hermA D t)).2.1
  exact (hΦ.comp (continuous_jn hn)).mul (Complex.continuous_conj.comp (hη.comp hy))

theorem xiP_cond {S : Finset (Pl D)} {e : AE D} (he : e * e = e) (hc : cA D e = e) {Φ : Mx D V.rank n → ℂ} {η : Mx D r t → ℂ}
    (hΦ : Good S e Φ) (hη : Good S e η)
    (hy : ∀ z : Mx D V.rank r × Mx D V.rank t, IntOff S z.1 → IntOff S z.2 → IntOff S (yv V b₀ z))
    (p : Mx D V.rank r × Mx D V.rank t → ℂ) (hp : ∀ z, p (e • z.1, e • z.2) = p z) (z : Mx D V.rank r × Mx D V.rank t) :
    (IntOff S z.1 ∧ IntOff S z.2 → xiP V b₀ hn Φ η z * p z = xiP V b₀ hn Φ η (e • z.1, e • z.2) * p (e • z.1, e • z.2)) ∧
      (¬ (IntOff S z.1 ∧ IntOff S z.2) → xiP V b₀ hn Φ η z * p z = 0) := by
  refine ⟨fun ⟨h1, h2⟩ => ?_, fun h => ?_⟩
  · have a1 := hΦ (jn hn z.1 z.2)
    rw [if_pos ((intOff_jn hn _ _).2 ⟨h1, h2⟩), jn_smul] at a1
    have a2 := hη (yv V b₀ z)
    rw [if_pos (hy z h1 h2), ← yv_smul he hc] at a2
    rw [hp]
    simp only [xiP]
    rw [a1, a2]
  · have a1 := hΦ (jn hn z.1 z.2)
    rw [if_neg (fun hh => h ((intOff_jn hn _ _).1 hh))] at a1
    simp [xiP, a1]

set_option synthInstance.maxHeartbeats 400000 in

theorem cell_id {S : Finset (Pl D)} {e : AE D} (he : e * e = e) (hc : cA D e = e) {ψ : AddChar (AF D.host.F) ℂ}
    (hψ : IsCharAF D.host.F ψ) [BorelSpace (Mx D V.rank r × Mx D V.rank t)]
    {P : Measure (Mx D V.rank r × Mx D V.rank t)} {σ : Measure (XS D V.rank r t e)}
    (hL : ∀ Ξ : Mx D V.rank r × Mx D V.rank t → ℂ, Continuous Ξ →
      (∀ z, (IntOff S z.1 ∧ IntOff S z.2 → Ξ z = Ξ (e • z.1, e • z.2)) ∧ (¬ (IntOff S z.1 ∧ IntOff S z.2) → Ξ z = 0)) →
      (Integrable Ξ P → Integrable (fun z : XS D V.rank r t e => Ξ z.1) σ) ∧ ∫ z, Ξ z ∂P = ∫ z : XS D V.rank r t e, Ξ z.1 ∂σ)
    (hy : ∀ z : Mx D V.rank r × Mx D V.rank t, IntOff S z.1 → IntOff S z.2 → IntOff S (yv V b₀ z))
    {Φ : Mx D V.rank n → ℂ} {η : Mx D r t → ℂ} (hΦc : Continuous Φ) (hηc : Continuous η) (hΦ : Good S e Φ) (hη : Good S e η)
    {B : ℝ} (hB : ∀ y, ‖η y‖ ≤ B) (hI : Integrable (fun z : Mx D V.rank r × Mx D V.rank t => Φ (jn hn z.1 z.2)) P) :
    Integrable (fun z : XS D V.rank r t e => xiP V b₀ hn Φ η z.1) σ ∧
      ∀ x : hermS D t e, ∫ z, xiP V b₀ hn Φ η z * pch ψ x.1.1 (qv V b₀ z) ∂P =
        ∫ z : XS D V.rank r t e, xiP V b₀ hn Φ η z.1 * pch ψ x.1.1 (qv V b₀ z.1) ∂σ := by
  have hx := continuous_xiP (b₀ := b₀) (hn := hn) hψ hΦc hηc
  haveI : OpensMeasurableSpace (Mx D V.rank r × Mx D V.rank t) := BorelSpace.opensMeasurable
  constructor
  · have hc1 := xiP_cond (hn := hn) he hc hΦ hη hy (fun _ => 1) (fun _ => rfl)
    simp only [mul_one] at hc1
    refine (hL _ hx hc1).1 ?_
    refine (hI.norm.const_mul B).mono' hx.aestronglyMeasurable (ae_of_all _ fun z => ?_)
    simp only [xiP, norm_mul, RCLike.norm_conj]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)
  · intro x
    have hcp := (GlobalTheory.CompanionTheory.RCellCont.continuity_characters_projection (t := t) hψ V b₀ x.1).2.2.2.1
    refine (hL (fun z => xiP V b₀ hn Φ η z * pch ψ x.1.1 (qv V b₀ z)) (hx.mul hcp) ?_).2
    refine xiP_cond (hn := hn) he hc hΦ hη hy _ fun z => ?_
    rw [qv_smul he hc]
    exact pch_smul x.2 _

end Xi

end GlobalTheory.CompanionTheory.EisE

end
