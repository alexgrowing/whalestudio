import CompanionTheory.AutomorphicTheory.SchurLimitBounds.ZuckermanDuality.ZuckDualTOfZuckDual
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.UniformCoefficientBounds.CoefBoundUniform

open Matrix MeasureTheory Set
open scoped ContDiff InnerProductSpace

noncomputable section

namespace CompanionTheory.CapEig

open CompanionTheory.D.Upq.Sm Formalism.FourierDecayAlt CompanionTheory.LimBd.Main

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Deriv

variable {k r : ℕ} {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup E] [NormedSpace ℂ E] {G : Set (B.Mat k r)} {σ : B.Mat k r → (H →L[ℂ] H)}

def cf (σ : B.Mat k r → (H →L[ℂ] H)) (x₀ : E) (a b : H) (g : B.Mat k r) : E := ⟪a, σ g b⟫_ℂ • x₀

theorem rw_cf (h : RepOn G σ) (x₀ : E) (a : H) {b : H} (hb : IsSm G σ b) {f : B.Mat k r → E}
    (hf : ∀ g ∈ G, f g = cf σ x₀ a b g) :
    ∀ {v : List (B.Mat k r)}, LieW G v → ∀ g ∈ G, B.Rw v f g = cf σ x₀ a (dsW σ v b) g
  | [], _, g, hg => hf g hg
  | X :: v, hv, g, hg => by
    have hv' : LieW G v := fun Y hY => hv Y (List.mem_cons_of_mem _ hY)
    have hX := hv X List.mem_cons_self
    change deriv (fun t : ℝ => B.Rw v f (g * ex X t)) 0 = _
    have e : (fun t : ℝ => B.Rw v f (g * ex X t)) =
        fun t => ⟪a, σ g (σ (ex X t) (dsW σ v b))⟫_ℂ • x₀ := by
      ext1 t
      rw [rw_cf h x₀ a hb hf hv' _ (h.mul_mem _ hg _ (hX t)), cf, h.apply_mul hg (hX t)]
    rw [e]
    have h1 := ((hb.dsW h hv').differentiableAt h hX).hasDerivAt
    let L : H →L[ℝ] E := (((innerSL ℂ a).comp (σ g)).smulRight x₀).restrictScalars ℝ
    exact (L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1).deriv

theorem lw_cf (h : RepOn G σ) (hiso : ∀ g ∈ G, ∀ v, ‖σ g v‖ = ‖v‖) (x₀ : E) {a : H}
    (ha : IsSm G σ a) (b : H) {f : B.Mat k r → E} (hf : ∀ g ∈ G, f g = cf σ x₀ a b g) :
    ∀ {u : List (B.Mat k r)}, LieW G u → ∀ g ∈ G,
      u.foldr B.LdV f g = cf σ x₀ (dsW σ u a) b g
  | [], _, g, hg => hf g hg
  | X :: u, hu, g, hg => by
    have hu' : LieW G u := fun Y hY => hu Y (List.mem_cons_of_mem _ hY)
    have hX := hu X List.mem_cons_self
    change deriv (fun t : ℝ => u.foldr B.LdV f (NormedSpace.exp (-((t : ℂ) • X)) * g)) 0 = _
    have e : (fun t : ℝ => u.foldr B.LdV f (NormedSpace.exp (-((t : ℂ) • X)) * g)) =
        fun t => ⟪σ (ex X t) (dsW σ u a), σ g b⟫_ℂ • x₀ := by
      ext1 t
      have e1 : NormedSpace.exp (-((t : ℂ) • X)) = ex X (-t) := by simp [ex]
      rw [e1, lw_cf h hiso x₀ ha b hf hu' _ (h.mul_mem _ (hX _) _ hg), cf]
      let I : H →ₗᵢ[ℂ] H := ⟨σ (ex X t), hiso _ (hX t)⟩
      rw [← I.inner_map_map]
      change ⟪σ (ex X t) _, σ (ex X t) (σ (ex X (-t) * g) b)⟫_ℂ • x₀ = _
      rw [← h.apply_mul (hX t) (h.mul_mem _ (hX _) _ hg), ← Matrix.mul_assoc, ← ex_add,
        add_neg_cancel, ex_zero, Matrix.one_mul]
    rw [e]
    have h1 := ((ha.dsW h hu').differentiableAt h hX).hasDerivAt
    have h2 := (h1.inner ℂ (hasDerivAt_const (0 : ℝ) (σ g b))).smul_const x₀
    rw [h2.deriv]
    simp [cf, dsW_cons, ds]

end Deriv

theorem capelli_coefficient_smooth : CoefSmooth := by
  intro hK k r ε μ φ E _ _ T hφ g₀ hg₀
  obtain ⟨H, _, _, _, σ, v, w, hμ, hσ, hv, -, he⟩ := hφ
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hK k r ε μ H σ hμ hσ v hv g₀ hg₀
  refine ⟨U, fun x => (((innerSL ℂ w).smulRight T).restrictScalars ℝ) (F x), hU, hgU,
    (((innerSL ℂ w).smulRight T).restrictScalars ℝ).contDiff.comp_contDiffOn hF, fun g hg hgG => ?_⟩
  have e := hfF g hg hgG
  simp only at e
  simp [he g hgG, e]

theorem capelli_coefficient_continuity : CoefCC := by
  intro hK k r ε A h hD μ φ E _ _ x₀ m hφ hgap
  have hsm := capelli_coefficient_smooth hK k r ε μ φ E x₀ hφ
  obtain ⟨H, _, _, _, σ, v, w, hμ, hσ, hv, hw, he⟩ := hφ
  obtain ⟨P, ⟨⟨hP, hPJ⟩, -⟩, -, -, ⟨⟨h1, hm⟩, hiso, -⟩, -⟩ := id hσ
  obtain ⟨hc1, -⟩ := conj_facts hP hPJ
  have hG : PI.IsMatGroup (B.GV k r) := PI.QuotSetU.UnitaryGroupMassFormula.unitary_hermitian_group k r
  have hrep : RepOn (B.GV k r) σ := repOn_of_conj hP hPJ h1 hm
  have hiso' : ∀ g ∈ B.GV k r, ∀ v, ‖σ g v‖ = ‖v‖ := fun g hg v => by
    obtain ⟨b, hb, rfl⟩ := hc1 g hg
    exact hiso b hb v
  have good : ∀ {x : H}, PI.UpqRep.IsKFinHpk (k := k) (r := r) σ x → IsSm (B.GV k r) σ x ∧
      ∃ (T' : Submodule ℂ H) (C : ℝ), GoodSub (B.GV k r)
        (B.GV k r ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _)) σ T' ∧ 0 ≤ C ∧
        ∀ W : List (B.Mat k r), LieW (B.GV k r) W → (∀ X ∈ W, ‖X‖ ≤ 1) → W.length ≤ m →
          dsW σ W x ∈ T' ∧ ‖dsW σ W x‖ ≤ C := by
    rintro x ⟨S, hS, hxS, hSK⟩
    have hT : GoodSub (B.GV k r) (B.GV k r ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _))
        σ S := ⟨hS, fun v hv => hK k r ε μ H σ hμ hσ v ⟨S, hS, hv, hSK⟩, hSK⟩
    exact ⟨hT.sm x hxS, hT.words hG hrep inter_subset_left hxS m⟩
  obtain ⟨hvs, Tv, Cv, hTv, hCv, hWv⟩ := good hv
  obtain ⟨hws, Tw, Cw, hTw, hCw, hWw⟩ := good hw
  have := hTv.fin
  have := hTw.fin
  have hkf : ∀ a ∈ Tv ⊔ Tw, PI.UpqRep.IsKFinHpk (k := k) (r := r) σ a := by
    intro a ha
    refine ⟨Tv ⊔ Tw, inferInstance, ha, fun g hg x hx => ?_⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add]
    exact Submodule.add_mem_sup (hTv.stab g hg y hy) (hTw.stab g hg z hz)
  obtain ⟨C', hC', hb⟩ := coef_bound_uniform (G := B.GV k r) (σ := σ) (T := Tv ⊔ Tw)
    (ρ := fun g => (B.gN g ^ A)⁻¹) (fun g _ => inv_nonneg.2 (Real.rpow_nonneg (Real.sqrt_nonneg _) _))
    (fun a ha b hb => by
      obtain ⟨C, hd⟩ := hD μ H σ hμ hσ hgap b a (hkf b hb) (hkf a ha)
      refine ⟨C, fun g hg => ?_⟩
      have hp : 0 < B.gN g ^ A := Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hg)) A
      rw [← div_eq_mul_inv, le_div_iff₀ hp, mul_comm]
      exact hd g hg)
  refine ⟨C' * Cw * Cv * ‖x₀‖, fun g₀ hg₀ => ?_, fun u v' hu hv' huv g hg => ?_⟩
  · obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hsm g₀ hg₀
    exact ⟨U, F, hU, hgU, hF.of_le (by exact_mod_cast le_top), hfF⟩
  · have hlie : ∀ W : List (B.Mat k r), (∀ X ∈ W, B.unitLie k r X) →
        LieW (B.GV k r) W ∧ ∀ X ∈ W, ‖X‖ ≤ 1 := fun W hW =>
      ⟨fun X hX t => ex_mem_of_lie (hW X hX).1 t,
        fun X hX => (Matrix.norm_le_iff zero_le_one).2 (hW X hX).2⟩
    obtain ⟨hu1, hu2⟩ := hWw u (hlie u hu).1 (hlie u hu).2 (by omega)
    obtain ⟨hv1, hv2⟩ := hWv v' (hlie v' hv').1 (hlie v' hv').2 (by omega)
    have e : B.dLR u v' (fun g => φ g • x₀) g = cf σ x₀ (dsW σ u w) (dsW σ v' v) g :=
      lw_cf hrep hiso' x₀ hws _ (rw_cf hrep x₀ w hvs (fun g hg => by rw [he g hg]; rfl) (hlie v' hv').1)
        (hlie u hu).1 g hg
    rw [e, cf, norm_smul]
    have hp : 0 < B.gN g ^ A := Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hg)) A
    have h2 := hb _ (Submodule.mem_sup_right hu1) _ (Submodule.mem_sup_left hv1) g hg
    have h5 : 0 ≤ (B.gN g ^ A)⁻¹ := inv_nonneg.2 hp.le
    calc _ ≤ B.gN g ^ A * (C' * Cw * Cv * (B.gN g ^ A)⁻¹ * ‖x₀‖) := by
          gcongr
          exact h2.trans (by gcongr)
      _ = (B.gN g ^ A * (B.gN g ^ A)⁻¹) * (C' * Cw * Cv * ‖x₀‖) := by ring
      _ = _ := by rw [mul_inv_cancel₀ hp.ne', one_mul]

end CompanionTheory.CapEig

end
