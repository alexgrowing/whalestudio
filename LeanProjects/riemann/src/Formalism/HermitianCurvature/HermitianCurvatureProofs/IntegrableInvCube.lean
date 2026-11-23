import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBCChain

namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

def GSup (S : C.HidaSetting E Wp Wq) (ε : ℝ) (b n : ℕ) (P : ℝ) : Prop :=
  ∀ w' ∈ S.base.Wall, S.base.cnt w' + n * C.Kst ≤ S.Ntop →
    ∃ θ : S.W → ℝ, TB.IsProb (S.base.Wb (S.base.cnt w' + n * C.Kst)) θ ∧
      ∀ Y : Finset (TB.Pt E), (∀ h ∈ Y, TB.level h = b - 1) → ∀ κ, TB.PSDOn Y κ →
        ∀ t : crystallineComparison.V S.f, Good t →
          (KB.NstV S ε (b + n - 1) n w' Y κ t t).re ≤
            P * ∑ u ∈ S.base.Wb (S.base.cnt w' + n * C.Kst), θ u * S.base.N0 ε (b - 1) u Y κ

theorem integrable_inv_cube : Integrable (fun c : ℂ => ((1 + ‖c‖) ^ 3)⁻¹) := by
  have hi : Integrable (fun c : ℂ => (1 + ‖c‖) ^ (-(3 : ℝ))) :=
    integrable_one_add_norm (by rw [Complex.finrank_real_complex]; norm_num)
  refine hi.congr (Eventually.of_forall fun c => ?_)
  show (1 + ‖c‖) ^ (-(3 : ℝ)) = ((1 + ‖c‖) ^ 3)⁻¹
  rw [Real.rpow_neg (by positivity)]
  norm_cast

theorem zero_mem_dual {f : ℕ} (La : Submodule ℤ (crystallineComparison.V f)) : (0 : crystallineComparison.V f) ∈ crystallineComparison.dualSet La := by
  intro z _; simp [Lat.psi_zero]

theorem one_le_tsum_mL {f : ℕ} (La : Submodule ℤ (crystallineComparison.V f)) (K : ℕ) (L : Fin f → ℝ) (hL : ∀ v, 0 ≤ L v) (g : ℝ)
    (hs : Summable fun σ : crystallineComparison.dualSet La => crystallineComparison.mL K L (g • (σ : crystallineComparison.V f))) :
    1 ≤ ∑' σ : crystallineComparison.dualSet La, crystallineComparison.mL K L (g • (σ : crystallineComparison.V f)) := by
  have := hs.le_tsum (⟨0, zero_mem_dual La⟩ : crystallineComparison.dualSet La) (fun σ _ => mL_nonneg K L hL _)
  simpa [mL_zero] using this

theorem gN_one_reg (S : C.HidaSetting E Wp Wq) (hI : KB.IntAll S) (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (b : ℕ)
    (hb : 1 ≤ b) (hbr : b ≤ S.G.r + 1) (w : S.W) (h h' : C.LPt) (hh : D.ptSize h = b - 1)
    (hh' : D.ptSize h' = b - 1) :
    ContinuousOn (fun c => KB.gN S v ε (b + 1 - 1) (w.1 v) (h ++ [(1, c)]) (h' ++ [(1, c)])) {0}ᶜ ∧
    Integrable (fun c => KB.gN S v ε (b + 1 - 1) (w.1 v) (h ++ [(1, c)]) (h' ++ [(1, c)])) := by
  obtain ⟨φ, hφc, hφ, ⟨Cφ, hC⟩, -⟩ := hI v ε hε b hb hbr w h h' hh hh'
  have e : b + 1 - 1 = b := by omega
  rw [e]
  have hcongr : ∀ c ∈ ({0}ᶜ : Set ℂ), φ c / (S.sizeAt v (w.1 v) : ℂ) =
      KB.gN S v ε b (w.1 v) (h ++ [(1, c)]) (h' ++ [(1, c)]) := by
    intro c hc
    unfold KB.gN
    rw [hφ c hc]
  have hφi : Integrable φ :=
    Integrable.mono' (integrable_inv_cube.const_mul Cφ) hφc.aestronglyMeasurable (ae_of_all _ hC)
  refine ⟨(hφc.div_const _).continuousOn.congr fun c hc => (hcongr c hc).symm, ?_⟩
  refine (hφi.div_const (S.sizeAt v (w.1 v) : ℂ)).congr ?_
  filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℂ))] with c hc
  exact hcongr c hc

def SumBound (f : ℕ) (Cs : ℝ) : Prop :=
  ∀ (R g : ℝ) (L : Fin f → ℝ), 0 < R → 0 < g → (∀ v, 0 ≤ L v) →
    Summable (fun σ : crystallineComparison.dualSet (Lstd f R) => crystallineComparison.mL C.Kst L (g • (σ : crystallineComparison.V f))) ∧
    ∑' σ : crystallineComparison.dualSet (Lstd f R), crystallineComparison.mL C.Kst L (g • (σ : crystallineComparison.V f)) ≤ ∏ v, Cs * (1 + (R * L v / g) ^ 2)

theorem size_step (f : ℕ) (Cs : ℝ) (hCs1 : 1 ≤ Cs) (dl R g : ℝ) (hdl : 0 ≤ dl) (hR : 0 < R) (hg : 0 < g)
    (L thr : Fin f → ℝ) (hL : ∀ v, 0 ≤ L v ∧ L v ≤ thr v) (M V : ℝ) (hM : M ≤ ∏ v, Cs * (1 + (R * L v / g) ^ 2))
    (hV : dl * (∏ v, Cs * (1 + (R * thr v / g) ^ 2)) / R ^ (2 * f) ≤ V) : dl * M / R ^ (2 * f) ≤ V := by
  refine le_trans ?_ hV
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  refine mul_le_mul_of_nonneg_left (hM.trans ?_) hdl
  refine Finset.prod_le_prod (fun v _ => by positivity) fun v _ => ?_
  refine mul_le_mul_of_nonneg_left ?_ (by linarith)
  have h1 : R * L v / g ≤ R * thr v / g := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hL v).2 hR.le) hg.le
  have h0 : 0 ≤ R * L v / g := div_nonneg (mul_nonneg hR.le (hL v).1) hg.le
  nlinarith

theorem gsup_one (S : C.HidaSetting E Wp Wq) (hg : 0 < S.g) (hpos : C.ThmPPos S) (hI : KB.IntAll S)
    (X : ℕ → Fin S.f → ℝ) (hW : ∀ v, KB.WaveLoc S v fun i => X i v) (ε : ℝ) (hε : 0 < ε) (b : ℕ) (hb : 1 ≤ b)
    (hbr : b ≤ S.G.r + 1) (hX : ∀ v, 0 ≤ X b v ∧ X b v ≤ thr S b 1 v) (Cs : ℝ) (hCs1 : 1 ≤ Cs)
    (hCs : SumBound S.f Cs) (B R : ℝ) (hR : 0 < R)
    (hRB : (∏ _v : Fin S.f, KB.dlB S b 1) * (∏ v, Cs * (1 + (R * thr S b 1 v / S.g) ^ 2)) / R ^ (2 * S.f) ≤
      B ^ S.f * S.base.vol b 1) :
    ∃ P, 0 ≤ P ∧ P ≤ B ^ S.f * S.base.vol b 1 ∧ GSup S ε b 1 P := by
  obtain ⟨i1, i2, hcov, -⟩ := pbc_lstdFacts S.f R hR
  have := i1; have := i2
  have hg' : (0 : ℝ) < S.g := by exact_mod_cast hg
  have hL0 : ∀ v, 0 ≤ X b v := fun v => (hX v).1
  obtain ⟨hsm, hsle⟩ := hCs R S.g (fun v => X b v) hR hg' hL0
  have hM1 := one_le_tsum_mL (Lstd S.f R) C.Kst (fun v => X b v) hL0 (S.g : ℝ) hsm
  set M := ∑' σ : crystallineComparison.dualSet (Lstd S.f R), crystallineComparison.mL C.Kst (fun v => X b v) ((S.g : ℝ) • (σ : crystallineComparison.V S.f)) with hMdef
  have hdl0 : 0 ≤ ∏ _v : Fin S.f, KB.dlB S b 1 := Finset.prod_nonneg fun v _ => (dlB_pos S hg b 1).le
  refine ⟨(∏ _v : Fin S.f, KB.dlB S b 1) * M / R ^ (2 * S.f), by positivity,
    size_step S.f Cs hCs1 _ R S.g hdl0 hR hg' _ (thr S b 1) hX M _ hsle hRB, ?_⟩
  intro w' hw' hcnt
  simp only [one_mul] at hcnt ⊢
  obtain ⟨θ, hθ, hWV⟩ := Formalism.FourierDecayAlt.P.plane_wave_bound E Wp Wq S X hW ε hε b hb hbr w' hw' hcnt
  obtain ⟨θ', hθ', hmix⟩ := tsum_mix (S.base.Wb (S.base.cnt w' + C.Kst))
    (fun σ : crystallineComparison.dualSet (Lstd S.f R) => crystallineComparison.mL C.Kst (fun v => X b v) ((S.g : ℝ) • (σ : crystallineComparison.V S.f)))
    (fun σ => mL_nonneg _ _ hL0 _) hsm (by linarith)
    (fun σ => θ (crystallineComparison.pat (fun v => X b v) ((S.g : ℝ) • (σ : crystallineComparison.V S.f)))) (fun σ => hθ _)
  refine ⟨θ', hθ', fun Y hY κ hκ t ht => ?_⟩
  let D : Fin S.f → TB.Pt E → TB.Pt E → ℂ → ℂ := fun v h h' c =>
    KB.gN S v ε (b + 1 - 1) (w'.1 v) (C.loc (S.σ v) h ++ [(1, c)]) (C.loc (S.σ v) h' ++ [(1, c)])
  have hD : ∀ v (z : ℂ), z ≠ 0 → TB.PSDOn Y (fun h h' => D v h h' z) := by
    intro v z _
    have := PBB.gN_psd S hpos v ε hε (b + 1 - 1) (by omega) w' (Y.image fun h => C.loc (S.σ v) h ++ [(1, z)])
    exact JCx1.decay.psd_pull _ _ this Y (fun h => C.loc (S.σ v) h ++ [(1, z)])
      (fun h hh => Finset.mem_image_of_mem _ hh)
  have hreg := fun v h (hh : h ∈ Y) h' (hh' : h' ∈ Y) =>
    gN_one_reg S hI v ε hε b hb hbr w' (C.loc (S.σ v) h) (C.loc (S.σ v) h')
      (by rw [JCx1.needs.ptSize_loc]; exact hY h hh) (by rw [JCx1.needs.ptSize_loc]; exact hY h' hh')
  set N0 : S.W → ℝ := fun u => S.base.N0 ε (b - 1) u Y κ
  have hF : ∀ σ ∈ crystallineComparison.dualSet (Lstd S.f R),
      ‖Hh Y κ (fun v l h h' => KB.hatB S v ε b 1 (w'.1 v) l (C.loc (S.σ v) h) (C.loc (S.σ v) h'))
        ((S.g : ℝ) • σ)‖ ≤ crystallineComparison.mL C.Kst (fun v => X b v) ((S.g : ℝ) • σ) *
          ∑ u ∈ S.base.Wb (S.base.cnt w' + C.Kst), θ (crystallineComparison.pat (fun v => X b v) ((S.g : ℝ) • σ)) u * N0 u := by
    intro σ _
    exact bound_mL C.Kst (fun v => X b v) hL0 _ _ _ (hWV Y hY κ hκ _ _)
  have hH := herglotz_plain (H := TB.Pt E) Y κ hκ D hD (fun v h hh h' hh' => (hreg v h hh h' hh').1)
    (fun v h hh h' hh' => (hreg v h hh h' hh').2) (S.g : ℝ) hg' (fun _ => KB.dlB S b 1)
    (fun _ => dlB_pos S hg b 1)
    (fun v l h h' => KB.hatB S v ε b 1 (w'.1 v) l (C.loc (S.σ v) h) (C.loc (S.σ v) h')) (fun _ _ _ _ => rfl)
    (Lstd S.f R)
    (fun σ : crystallineComparison.V S.f => crystallineComparison.mL C.Kst (fun v => X b v) ((S.g : ℝ) • σ) *
      ∑ u ∈ S.base.Wb (S.base.cnt w' + C.Kst), θ (crystallineComparison.pat (fun v => X b v) ((S.g : ℝ) • σ)) u * N0 u)
    (hmix N0).1 (fun σ hσ => hF σ hσ)
    t {t} (by simp)
  rw [(hmix N0).2, hcov, Finset.sum_singleton] at hH
  have hN : Nz Y κ D t = (KB.NstV S ε (b + 1 - 1) 1 w' Y κ t t).re := by
    simp only [Nz, if_pos ht]
    rw [nstV_eq]
    rfl
  rw [hN] at hH
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity), mul_comm]
  linarith [hH]

end

end Formalism.FourierDecayAlt.P.PBC
