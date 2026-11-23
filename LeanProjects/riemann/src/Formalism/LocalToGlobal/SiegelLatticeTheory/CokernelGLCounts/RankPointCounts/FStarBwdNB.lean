import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdNA

noncomputable section

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdNA

variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E)

theorem oSmulW {W : Type*} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W]
    (o : 𝓞 E) (w : W) : o • w = (o : E) • w := by
  first
  | exact (algebraMap_smul E o w).symm
  | rfl
  | simp [Algebra.smul_def]

private theorem coe_ne_zero_of_ne_zero (o : 𝓞 E) (h : o ≠ 0) : (o : E) ≠ 0 := by
  intro h'
  apply h
  first
  | exact_mod_cast h'
  | exact RingOfIntegers.ext h'
  | simpa using h'

private theorem inv_smul_apply_smul_eq_of_smul_mem {W : Type*} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W]
    (P : Submodule (𝓞 E) S.V) (f : P →ₗ[𝓞 E] W) (u : S.V) (a b : 𝓞 E) (ha : a ≠ 0) (hb : b ≠ 0)
    (hau : a • u ∈ P) (hbu : b • u ∈ P) :
    ((a : E))⁻¹ • f ⟨a • u, hau⟩ = ((b : E))⁻¹ • f ⟨b • u, hbu⟩ := by
  have ha' := coe_ne_zero_of_ne_zero a ha
  have hb' := coe_ne_zero_of_ne_zero b hb
  have h1 : (b : E) • f ⟨a • u, hau⟩ = (a : E) • f ⟨b • u, hbu⟩ := by
    rw [← oSmulW, ← oSmulW, ← map_smul, ← map_smul]
    congr 1
    apply Subtype.ext
    exact smul_comm b a u
  calc ((a : E))⁻¹ • f ⟨a • u, hau⟩ = (((a : E))⁻¹ * ((b : E))⁻¹) • ((b : E) • f ⟨a • u, hau⟩) := by
        rw [smul_smul, mul_assoc, inv_mul_cancel₀ hb', mul_one]
    _ = (((a : E))⁻¹ * ((b : E))⁻¹) • ((a : E) • f ⟨b • u, hbu⟩) := by rw [h1]
    _ = ((b : E))⁻¹ • f ⟨b • u, hbu⟩ := by
        rw [smul_smul, mul_comm ((a : E))⁻¹, mul_assoc, inv_mul_cancel₀ ha', mul_one]

theorem ext_lat {W : Type*} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W]
    (U : Submodule E S.V) (P : Submodule (𝓞 E) S.V) (hPU : ∀ x ∈ P, x ∈ U)
    (hfull : ∀ u ∈ U, ∃ d : 𝓞 E, d ≠ 0 ∧ d • u ∈ P) (f : P →ₗ[𝓞 E] W) :
    ∃ F : U →ₗ[E] W, ∀ (x : S.V) (hx : x ∈ P), F ⟨x, hPU x hx⟩ = f ⟨x, hx⟩ := by
  classical
  choose d hd0 hdP using hfull
  have hmul : ∀ (u : S.V) (a b : 𝓞 E), a • u ∈ P → (b * a) • u ∈ P := by
    intro u a b h
    rw [mul_smul]
    exact P.smul_mem b h
  have hal : ∀ o : 𝓞 E, algebraMap (𝓞 E) E o = (o : E) := fun o => by first | rfl | simp
  refine ⟨{ toFun := fun x => ((d x.1 x.2 : E))⁻¹ • f ⟨d x.1 x.2 • x.1, hdP x.1 x.2⟩,
            map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro x y
    have e0 : d y.1 y.2 * d x.1 x.2 ≠ 0 := mul_ne_zero (hd0 _ _) (hd0 _ _)
    have hex : (d y.1 y.2 * d x.1 x.2) • x.1 ∈ P := hmul _ _ _ (hdP x.1 x.2)
    have hey : (d y.1 y.2 * d x.1 x.2) • y.1 ∈ P := by
      rw [mul_comm]
      exact hmul _ _ _ (hdP y.1 y.2)
    have hexy : (d y.1 y.2 * d x.1 x.2) • (x + y).1 ∈ P := by
      rw [Submodule.coe_add, smul_add]
      exact P.add_mem hex hey
    rw [inv_smul_apply_smul_eq_of_smul_mem S P f (x + y).1 _ _ (hd0 _ _) e0 (hdP _ _) hexy,
      inv_smul_apply_smul_eq_of_smul_mem S P f x.1 _ _ (hd0 _ _) e0 (hdP _ _) hex,
      inv_smul_apply_smul_eq_of_smul_mem S P f y.1 _ _ (hd0 _ _) e0 (hdP _ _) hey, ← smul_add, ← map_add]
    congr 2
    apply Subtype.ext
    simp only [Submodule.coe_add, Submodule.coe_add, smul_add]
  · intro c x
    simp only [RingHom.id_apply]
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) c
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    have hq' := coe_ne_zero_of_ne_zero q hq0
    have ha' := coe_ne_zero_of_ne_zero _ (hd0 x.1 x.2)
    have e0 : q * d x.1 x.2 ≠ 0 := mul_ne_zero hq0 (hd0 _ _)
    have hcq : (q * d x.1 x.2) • ((algebraMap (𝓞 E) E p / algebraMap (𝓞 E) E q) • x.1) =
        p • (d x.1 x.2 • x.1) := by
      rw [oSmulW, oSmulW, oSmulW (o := d x.1 x.2), smul_smul, smul_smul, hal, hal]
      congr 1
      push_cast
      field_simp
    have hmem : (q * d x.1 x.2) • (((algebraMap (𝓞 E) E p / algebraMap (𝓞 E) E q) • x : U) : S.V) ∈ P := by
      rw [Submodule.coe_smul, hcq]
      exact P.smul_mem p (hdP x.1 x.2)
    rw [inv_smul_apply_smul_eq_of_smul_mem S P f _ _ _ (hd0 _ _) e0 (hdP _ _) hmem]
    have hsub : (⟨(q * d x.1 x.2) • (((algebraMap (𝓞 E) E p / algebraMap (𝓞 E) E q) • x : U) : S.V), hmem⟩ : P) =
        p • ⟨d x.1 x.2 • x.1, hdP x.1 x.2⟩ := by
      apply Subtype.ext
      simp only [Submodule.coe_smul]
      exact hcq
    rw [hsub, map_smul, oSmulW (o := p), smul_smul, smul_smul, hal, hal]
    congr 1
    push_cast
    field_simp
  · intro x hx
    have h1 : (1 : 𝓞 E) • x ∈ P := by
      rw [one_smul]
      exact hx
    refine (inv_smul_apply_smul_eq_of_smul_mem S P f x _ 1 (hd0 _ _) one_ne_zero (hdP _ _) h1).trans ?_
    have h2 : (⟨(1 : 𝓞 E) • x, h1⟩ : P) = ⟨x, hx⟩ := Subtype.ext (one_smul _ x)
    rw [h2]
    simp

theorem ext_top {W : Type*} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W]
    (P : Submodule (𝓞 E) S.V) (hfull : ∀ u : S.V, ∃ d : 𝓞 E, d ≠ 0 ∧ d • u ∈ P) (f : P →ₗ[𝓞 E] W) :
    ∃ F : S.V →ₗ[E] W, ∀ (x : S.V) (hx : x ∈ P), F x = f ⟨x, hx⟩ := by
  obtain ⟨G, hG⟩ := ext_lat S ⊤ P (fun _ _ => Submodule.mem_top) (fun u _ => hfull u) f
  refine ⟨G.comp (LinearMap.codRestrict ⊤ LinearMap.id (fun _ => Submodule.mem_top)), fun x hx => ?_⟩
  exact hG x hx

theorem dual_sum (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.IsLattice E Λ) (hSD : SD S Λ) (U : Submodule E S.V)
    (v : S.V) (hv : ∀ m ∈ Λ, m ∈ U → IsIntegral ℤ (S.hT m v)) : ∃ w ∈ Λ, v - w ∈ orth S U := by
  obtain ⟨π, hπ, hπU⟩ := retract S Λ hΛ.fg U
  let g : Λ →ₗ[𝓞 E] E := ((S.hT v).restrictScalars (𝓞 E)) ∘ₗ π
  obtain ⟨G, hG⟩ := ext_top S (W := E) Λ (fun u => PI.UnitaryGroupMassFormula.BetaLUniq.exists_smul_mem S Λ hΛ u) g
  obtain ⟨w, hw⟩ := riesz S G
  have hgw : ∀ (m : S.V) (hm : m ∈ Λ), S.hT m w = star (S.hT v (π ⟨m, hm⟩)) := fun m hm => by
    rw [hsw S w m, hw, hG m hm]
    rfl
  refine ⟨w, (hSD w).2 fun y hy => ?_, (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth S).2 fun u hu => ?_⟩
  · rw [hgw y hy, hsw S (π ⟨y, hy⟩) v, star_star]
    exact hv _ (hπ ⟨y, hy⟩).1 (hπ ⟨y, hy⟩).2
  · have hm : ∀ m ∈ Λ, m ∈ U → S.hT m (v - w) = 0 := fun m hmΛ hmU => by
      rw [map_sub, hgw m hmΛ, hπU ⟨m, hmΛ⟩ hmU, hsw S m v, star_star]
      simp
    obtain ⟨d, hd, hdu⟩ := PI.UnitaryGroupMassFormula.BetaLUniq.exists_smul_mem S Λ hΛ u
    have h1 := hm _ hdu (by rw [oSmul]; exact U.smul_mem _ hu)
    rw [oSmul, hT_smulL] at h1
    have hd' : star ((d : E)) ≠ 0 := by
      rw [star_ne_zero]; exact coe_ne_zero hd
    exact (mul_eq_zero.1 h1).resolve_left hd'

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdNA
