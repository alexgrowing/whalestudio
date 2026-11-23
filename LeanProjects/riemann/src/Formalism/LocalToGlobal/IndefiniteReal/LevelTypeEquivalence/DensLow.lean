import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.VanishTranslates
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ApproxId

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Matrix Topology Filter
open Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.SchurOrthogonalityAlt
open scoped InnerProductSpace ContDiff

namespace Formalism.IndefR.Eqv.KerDiag

attribute [local instance] Formalism.BasicNotions.Host.cmStar Matrix.normedAddCommGroup Matrix.normedSpace

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)

theorem uh_mul {a b : Matrix (Fin V.rank) (Fin V.rank) ℂ} (ha : a ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ))
    (hb : b ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) : a * b ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
  have ha' : aᴴ * gramAt D V τ * a = gramAt D V τ := ha
  have hb' : bᴴ * gramAt D V τ * b = gramAt D V τ := hb
  show (a * b)ᴴ * gramAt D V τ * (a * b) = gramAt D V τ
  calc (a * b)ᴴ * gramAt D V τ * (a * b) = bᴴ * (aᴴ * gramAt D V τ * a) * b := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = gramAt D V τ := by rw [ha', hb']

theorem one_uh : (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
  show (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᴴ * gramAt D V τ * 1 = gramAt D V τ
  simp

theorem gt_of_uh (M : DSModel V S) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) :
    ∃ gg : Gt V τ, gm gg = g := by
  have hc := conj_mem M τ hg
  have hu : IsUnit (M.fr τ * g * (M.fr τ)⁻¹) := isUnit_of_mem_UJ (M.ε τ) hc
  have hfu : IsUnit (M.fr τ)⁻¹ := (Matrix.isUnit_nonsing_inv_iff).2 (M.fr_unit τ)
  have e : (M.fr τ)⁻¹ * (M.fr τ * g * (M.fr τ)⁻¹) * M.fr τ = g := by
    simp only [Matrix.mul_assoc, fr_inv_mul M τ, Matrix.mul_one]
    rw [← Matrix.mul_assoc, fr_inv_mul M τ, Matrix.one_mul]
  have hgu : IsUnit g := by rw [← e]; exact (hfu.mul hu).mul (M.fr_unit τ)
  exact ⟨⟨hgu.unit, hg⟩, rfl⟩

theorem rep_one' : M.rep τ 1 = 1 := by
  show M.σ τ (M.fr τ * 1 * (M.fr τ)⁻¹) = 1
  rw [Matrix.mul_one, fr_mul_inv]
  exact (M.ds τ).2.2.1.1.1

def Ksub : Submodule ℂ (M.H τ) :=
  Submodule.span ℂ {x | ∃ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∃ w0 : lowT M τ, x = M.rep τ g ((w0 : M.sm τ) : M.H τ)}

theorem ksub_sm : ∀ x ∈ Ksub M τ, ∃ w ∈ KfLow M τ, (w : M.H τ) = x := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, hg, w0, rfl⟩ := hx
    obtain ⟨gg, rfl⟩ := gt_of_uh (M := M) (τ := τ) hg
    exact ⟨⟨_, sm_stable M τ gg (w0 : M.sm τ).2⟩, Submodule.subset_span ⟨gm gg, hg, w0, rfl⟩, rfl⟩
  | zero => exact ⟨0, Submodule.zero_mem _, rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact ⟨a + b, Submodule.add_mem _ ha hb, rfl⟩
  | smul c x _ hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    exact ⟨c • a, Submodule.smul_mem _ c ha, rfl⟩

theorem ksub_rep {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) :
    ∀ x ∈ Ksub M τ, M.rep τ g x ∈ Ksub M τ := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g', hg', w0, rfl⟩ := hx
    refine Submodule.subset_span ⟨g * g', uh_mul τ hg hg', w0, ?_⟩
    rw [rep_mul M τ hg hg', ContinuousLinearMap.comp_apply]
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem ksub_closure_top (hlow : ∃ w0 : lowT M τ, ((w0 : M.sm τ) : M.H τ) ≠ 0) :
    (Ksub M τ).topologicalClosure = ⊤ := by
  obtain ⟨w0, hw0⟩ := hlow
  rcases (M.ds τ).2.2.2.1 (Ksub M τ).topologicalClosure (Submodule.isClosed_topologicalClosure _) (by
      intro h hh v hv
      obtain ⟨g, hg⟩ := exists_gt_of_UJ M τ hh
      rw [← hg]
      have hc : Continuous (M.rep τ (gm g)) := (M.rep τ (gm g)).continuous
      have hsub : (M.rep τ (gm g)) '' (Ksub M τ : Set (M.H τ)) ⊆ (Ksub M τ : Set (M.H τ)) := by
        rintro _ ⟨x, hx, rfl⟩; exact ksub_rep M τ (gm_mem g) x hx
      have hv' : v ∈ closure (Ksub M τ : Set (M.H τ)) := by
        rwa [← Submodule.topologicalClosure_coe]
      have := image_closure_subset_closure_image hc ⟨v, hv', rfl⟩
      have h2 := closure_mono hsub this
      rw [← Submodule.topologicalClosure_coe] at h2
      exact h2) with h | h
  · exfalso
    have hmem : ((w0 : M.sm τ) : M.H τ) ∈ (Ksub M τ).topologicalClosure := by
      apply Submodule.le_topologicalClosure
      refine Submodule.subset_span ⟨1, one_uh τ, w0, ?_⟩
      rw [rep_one' M τ, ContinuousLinearMap.one_apply]
    rw [h, Submodule.mem_bot] at hmem
    exact hw0 hmem
  · exact h

theorem cont_orbit {ℓ : M.H τ →ₗ[ℂ] ℂ} (hℓ : Sobolev₂ (lieAt V τ) (M.rep τ) ℓ) {w : M.H τ} (hw : w ∈ M.sm τ) :
    Continuous fun h : PI.UpqRep.UJ (M.ε τ) => ℓ (M.σ τ (PI.UpqRep.umat h) w) := by
  obtain ⟨L, C, hL, hC⟩ := hℓ
  have hsw := gp_sv_of_mem hw
  have hsv : ∀ h : PI.UpqRep.UJ (M.ε τ), SmoothVec (lieAt V τ) (M.rep τ) (M.σ τ (PI.UpqRep.umat h) w) :=
    fun h => gp_sv_sigma M τ h hsw
  have hcl : ∀ l ∈ L, Continuous fun h : PI.UpqRep.UJ (M.ε τ) =>
      l.foldr (dRep (M.rep τ)) (M.σ τ (PI.UpqRep.umat h) w) :=
    fun l hl => orbitDerivCont_holds M τ w hsw l (hL l hl)
  rw [continuous_iff_continuousAt]
  intro h0
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hbound : ∀ h : PI.UpqRep.UJ (M.ε τ), ‖ℓ (M.σ τ (PI.UpqRep.umat h) w) - ℓ (M.σ τ (PI.UpqRep.umat h0) w)‖ ≤
      |C| * (L.map fun l => ‖l.foldr (dRep (M.rep τ)) (M.σ τ (PI.UpqRep.umat h) w) -
        l.foldr (dRep (M.rep τ)) (M.σ τ (PI.UpqRep.umat h0) w)‖).sum := by
    intro h
    have hs := gp_sv_add (hsv h) (gp_sv_smul (-1) (hsv h0))
    have e1 : ℓ (M.σ τ (PI.UpqRep.umat h) w) - ℓ (M.σ τ (PI.UpqRep.umat h0) w) =
        ℓ (M.σ τ (PI.UpqRep.umat h) w + (-1 : ℂ) • M.σ τ (PI.UpqRep.umat h0) w) := by
      rw [map_add, map_smul]; simp [sub_eq_add_neg]
    rw [e1]
    refine (hC _ hs).trans ?_
    have e2 : (L.map fun l => ‖l.foldr (dRep (M.rep τ)) (M.σ τ (PI.UpqRep.umat h) w +
        (-1 : ℂ) • M.σ τ (PI.UpqRep.umat h0) w)‖) = (L.map fun l => ‖l.foldr (dRep (M.rep τ))
          (M.σ τ (PI.UpqRep.umat h) w) - l.foldr (dRep (M.rep τ)) (M.σ τ (PI.UpqRep.umat h0) w)‖) := by
      refine List.map_congr_left fun l hl => ?_
      rw [gp_foldr_add l (hL l hl) (hsv h) (gp_sv_smul (-1) (hsv h0)), gp_foldr_smul (-1) l (hL l hl) (hsv h0)]
      simp [sub_eq_add_neg]
    rw [e2]
    exact mul_le_mul_of_nonneg_right (le_abs_self C) (List.sum_nonneg (by simp))
  refine squeeze_zero (fun h => norm_nonneg _) hbound ?_
  have hz : Tendsto (fun h : PI.UpqRep.UJ (M.ε τ) => |C| * (L.map fun l => ‖l.foldr (dRep (M.rep τ))
      (M.σ τ (PI.UpqRep.umat h) w) - l.foldr (dRep (M.rep τ)) (M.σ τ (PI.UpqRep.umat h0) w)‖).sum) (𝓝 h0)
      (𝓝 (|C| * (L.map fun l => ‖l.foldr (dRep (M.rep τ)) (M.σ τ (PI.UpqRep.umat h0) w) -
        l.foldr (dRep (M.rep τ)) (M.σ τ (PI.UpqRep.umat h0) w)‖).sum)) := by
    refine tendsto_const_nhds.mul ?_
    have : Continuous fun h : PI.UpqRep.UJ (M.ε τ) => (L.map fun l => ‖l.foldr (dRep (M.rep τ))
        (M.σ τ (PI.UpqRep.umat h) w) - l.foldr (dRep (M.rep τ)) (M.σ τ (PI.UpqRep.umat h0) w)‖).sum :=
      continuous_list_sum (f := fun l (h : PI.UpqRep.UJ (M.ε τ)) => ‖l.foldr (dRep (M.rep τ))
        (M.σ τ (PI.UpqRep.umat h) w) - l.foldr (dRep (M.rep τ)) (M.σ τ (PI.UpqRep.umat h0) w)‖) L
        fun l hl => ((hcl l hl).sub continuous_const).norm
    exact this.tendsto h0
  simpa using hz

theorem densLow_model (hlow : ∃ w0 : lowT M τ, ((w0 : M.sm τ) : M.H τ) ≠ 0) (ℓ : M.H τ →ₗ[ℂ] ℂ)
    (hℓ : Sobolev₂ (lieAt V τ) (M.rep τ) ℓ) (hK : ∀ w ∈ KfLow M τ, ℓ (w : M.H τ) = 0) :
    ∀ w : M.sm τ, ℓ (w : M.H τ) = 0 := by
  have : CompleteSpace (M.H τ) := (M.ds τ).1
  have hKs : ∀ x ∈ Ksub M τ, ℓ x = 0 := fun x hx => by
    obtain ⟨w, hw, rfl⟩ := ksub_sm M τ x hx; exact hK w hw

  have hsmooth : ∀ Φ : Matrix (Fin V.rank) (Fin V.rank) ℂ → ℂ, ContDiff ℝ ∞ Φ → HasCompactSupport Φ →
      ∀ x : M.H τ, ℓ (gvT M τ Φ x) = 0 := by
    intro Φ hΦ hΦc
    obtain ⟨L, C, hL, hC⟩ := hℓ
    obtain ⟨c, hc⟩ := sum_gvT_le M τ hΦ hΦc L hL
    let LΦ : M.H τ →L[ℂ] ℂ := (ℓ ∘ₗ gvTL M τ Φ hΦ.continuous hΦc).mkContinuous (|C| * c)
      (fun x => gvT_bd M τ hΦ hΦc hC hc x)
    have hvan : ∀ x ∈ Ksub M τ, LΦ x = 0 := by
      intro x hx
      show ℓ (gvT M τ Φ x) = 0
      obtain ⟨w, -, hwx⟩ := ksub_sm M τ x hx
      have hxs : x ∈ M.sm τ := hwx ▸ w.2
      rw [gvPair_holds M τ Φ hΦ hΦc ℓ ⟨L, C, hL, hC⟩ x hxs]
      have : ∀ h : PI.UpqRep.UJ (M.ε τ), ℓ (M.σ τ (PI.UpqRep.umat h) x) = 0 := by
        intro h
        rw [← rep_conj_back M τ h]
        exact hKs _ (ksub_rep M τ (conj_back_mem M τ h) x hx)
      simp [this]
    have hall : ∀ x ∈ (Ksub M τ).topologicalClosure, LΦ x = 0 := by
      intro x hx
      have hcl : IsClosed {y : M.H τ | LΦ y = 0} := isClosed_eq LΦ.continuous continuous_const
      have : (Ksub M τ : Set (M.H τ)) ⊆ {y | LΦ y = 0} := fun y hy => hvan y hy
      rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hx
      exact closure_minimal this hcl hx
    intro x
    have := hall x (by rw [ksub_closure_top M τ hlow]; trivial)
    exact this
  intro w
  have hcont := cont_orbit M τ (ℓ := ℓ) hℓ w.2
  have h1 : ℓ (M.σ τ (PI.UpqRep.umat (1 : PI.UpqRep.UJ (M.ε τ))) (w : M.H τ)) = ℓ (w : M.H τ) := by
    rw [show PI.UpqRep.umat (1 : PI.UpqRep.UJ (M.ε τ)) = 1 from rfl, (M.ds τ).2.2.1.1.1,
      ContinuousLinearMap.one_apply]
  refine norm_eq_zero.1 (le_antisymm (le_of_forall_pos_le_add fun δ hδ => ?_) (norm_nonneg _))
  obtain ⟨Φ, hΦ, hΦc, hle⟩ := approx_id (M.ε τ) _ hcont hδ
  rw [← gvPair_holds M τ Φ hΦ hΦc ℓ hℓ _ w.2, hsmooth Φ hΦ hΦc, h1, zero_sub, norm_neg] at hle
  linarith

section R

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T D.R.m}
variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

def LowTNZ : Prop :=
  ∀ i τ, ∃ w0 : lowT (R.MW i (sg0 D A)) τ, (((w0 : (R.MW i (sg0 D A)).sm τ)) : (R.MW i (sg0 D A)).H τ) ≠ 0

theorem densLow_of (h : LowTNZ R) : DensLow R :=
  fun i τ ℓ hℓ hK => densLow_model (R.MW i (sg0 D A)) τ (h i τ) ℓ hℓ hK

theorem spanP_of_lowTNZ (h : LowTNZ R) : Formalism.IndefR.Eqv.Act.SpanP R := spanP_of R (densLow_of R h)

end R

end Formalism.IndefR.Eqv.KerDiag

end
