import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabCountPfLeviSteps

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.SlabCount

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.PoincareInHH.Cut Formalism.L2.SG.Full

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace LeviAlg

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u' : D.what₂.Word)

abbrev XS : Submodule D.host.E (VS D).V := Submodule.span D.host.E (Set.range X.eX)

theorem xsp_eq : Xsp (lf D (X.Fu u')) = XS X := by
  show Submodule.span D.host.E (Set.range (X.Fu u').e) = _
  rw [X.Fu_e]

theorem mem_orth' {U : Submodule D.host.E (VS D).V} {v : (VS D).V} :
    v ∈ orth (VS D) U ↔ ∀ y ∈ U, (VS D).hT y v = 0 := by
  simp [orth, Submodule.mem_iInf, LinearMap.mem_ker]

theorem orth_span_iff {T : Set (VS D).V} {v : (VS D).V} :
    v ∈ orth (VS D) (Submodule.span D.host.E T) ↔ ∀ y ∈ T, (VS D).hT y v = 0 := by
  rw [mem_orth']
  refine ⟨fun h y hy => h y (Submodule.subset_span hy), fun h y hy => ?_⟩
  induction hy using Submodule.span_induction with
  | mem y hy => exact h y hy
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, LinearMap.add_apply, ha, hb, add_zero]
  | smul c a _ ha => rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, ha, smul_zero]

variable {X} in
theorem hconj (x y : (VS D).V) : (VS D).hT y x = starRingEnd D.host.E ((VS D).hT x y) :=
  ((VS D).herm.eq x y).symm

theorem fe (a b : Fin D.R.rS) : (VS D).hT (X.fY a) (X.eX b) = if a = b then 1 else 0 := by
  rw [hconj, X.ef]
  by_cases h : b = a
  · subst h; simp
  · have h' : ¬ a = b := fun e => h e.symm
    simp [h, h']

theorem ze (a : Fin D.R.rS) : (VS D).hT (X.zu u') (X.eX a) = 0 := by
  rw [hconj, (X.zu_orth u' a).1, map_zero]

theorem zf (a : Fin D.R.rS) : (VS D).hT (X.zu u') (X.fY a) = 0 := by
  rw [hconj, (X.zu_orth u' a).2, map_zero]

theorem zz_ne : (VS D).hT (X.zu u') (X.zu u') ≠ 0 := by
  rw [X.zu_norm]
  exact neg_ne_zero.2 (Nat.cast_ne_zero.2 (D.mem u').A.T_prime.ne_zero)

theorem piW_apply (x : (VS D).V) : piWL X u' x = x - ∑ a, (VS D).hT (X.fY a) x • X.eX a -
    ∑ a, (VS D).hT (X.eX a) x • X.fY a -
      (VS D).hT (X.zu u') x • (((VS D).hT (X.zu u') (X.zu u'))⁻¹ • X.zu u') := by
  simp [piWL, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smulRight_apply]

theorem mem_W_iff {w : (VS D).V} : w ∈ Wsp X u' ↔ (∀ a, (VS D).hT (X.eX a) w = 0) ∧
    (∀ a, (VS D).hT (X.fY a) w = 0) ∧ (VS D).hT (X.zu u') w = 0 := by
  unfold Wsp Usp
  rw [orth_span_iff]
  constructor
  · intro h
    exact ⟨fun a => h _ (Or.inl (Or.inl ⟨a, rfl⟩)), fun a => h _ (Or.inl (Or.inr ⟨a, rfl⟩)), h _ (Or.inr rfl)⟩
  · rintro ⟨h1, h2, h3⟩ y hy
    rcases hy with (⟨a, rfl⟩ | ⟨a, rfl⟩) | hy
    · exact h1 a
    · exact h2 a
    · rw [Set.mem_singleton_iff.1 hy]; exact h3

theorem piW_mem (x : (VS D).V) : piWL X u' x ∈ Wsp X u' := by
  rw [mem_W_iff, piW_apply]
  have hz := zz_ne X u'
  refine ⟨fun b => ?_, fun b => ?_, ?_⟩
  · simp [map_sub, map_sum, X.ee, X.ef, (X.zu_orth u' b).1, mul_ite, Finset.sum_ite_eq]
  · simp [map_sub, map_sum, fe, X.ff, (X.zu_orth u' b).2, mul_ite, Finset.sum_ite_eq]
  · simp [map_sub, map_sum, ze, zf, hz]

theorem levi_projection_of_mem {w : (VS D).V} (hw : w ∈ Wsp X u') : piWL X u' w = w := by
  obtain ⟨h1, h2, h3⟩ := (mem_W_iff X u').1 hw
  rw [piW_apply]
  simp [h1, h2, h3]

theorem piW_e (b : Fin D.R.rS) : piWL X u' (X.eX b) = 0 := by
  rw [piW_apply]
  simp [fe, X.ee, ze, ite_smul]

theorem levi_projection_z_eq_zero : piWL X u' (X.zu u') = 0 := by
  have hz := zz_ne X u'
  rw [piW_apply]
  simp [(X.zu_orth u' _).1, (X.zu_orth u' _).2, smul_smul, hz]

abbrev XZ : Submodule D.host.E (VS D).V := XS X ⊔ Submodule.span D.host.E {X.zu u'}

theorem piW_XZ {x : (VS D).V} (hx : x ∈ XZ X u') : piWL X u' x = 0 := by
  have : XZ X u' ≤ LinearMap.ker (piWL X u') := by
    refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨b, rfl⟩; exact piW_e X u' b
    · intro y hy; rw [Set.mem_singleton_iff.1 hy]; exact levi_projection_z_eq_zero X u'
  exact this hx

theorem xs_le_usp : XS X ≤ Usp X u' :=
  Submodule.span_mono (fun _ h => Or.inl (Or.inl h))

theorem W_le_orth : Wsp X u' ≤ orth (VS D) (XS X) := by
  intro w hw
  rw [mem_orth']
  intro y hy
  exact (mem_orth'.1 hw) y (xs_le_usp X u' hy)

theorem xs_le_orth : XS X ≤ orth (VS D) (XS X) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨b, rfl⟩
  show X.eX b ∈ orth (VS D) (XS X)
  rw [orth_span_iff]
  rintro _ ⟨a, rfl⟩
  exact X.ee a b

theorem sub_piW {x : (VS D).V} (hx : x ∈ orth (VS D) (XS X)) : x - piWL X u' x ∈ XZ X u' := by
  have he : ∀ a, (VS D).hT (X.eX a) x = 0 := fun a => (mem_orth'.1 hx) _ (Submodule.subset_span ⟨a, rfl⟩)
  rw [piW_apply]
  simp only [he, zero_smul, Finset.sum_const_zero, sub_zero]
  have e : x - (x - ∑ a, (VS D).hT (X.fY a) x • X.eX a -
      (VS D).hT (X.zu u') x • (((VS D).hT (X.zu u') (X.zu u'))⁻¹ • X.zu u')) =
      ∑ a, (VS D).hT (X.fY a) x • X.eX a +
        ((VS D).hT (X.zu u') x * ((VS D).hT (X.zu u') (X.zu u'))⁻¹) • X.zu u' := by
    rw [mul_smul]; abel
  rw [e]
  refine add_mem (Submodule.mem_sup_left (Submodule.sum_mem _ fun a _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))) (Submodule.mem_sup_right
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))

end LeviAlg

namespace LeviAlg

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u' : D.what₂.Word)

def Gd (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Prop :=
  σ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧ (∀ a, σ (X.eX a) - X.eX a ∈ XS X) ∧ σ (X.zu u') - X.zu u' ∈ XS X

variable {X u'}

theorem gd_xz_sub {σ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hσ : Gd X u' σ) {x : (VS D).V} (hx : x ∈ XZ X u') :
    σ x - x ∈ XS X := by
  have : XZ X u' ≤ (XS X).comap (σ.toLinearMap - LinearMap.id) := by
    refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨b, rfl⟩; exact hσ.2.1 b
    · intro y hy; rw [Set.mem_singleton_iff.1 hy]; exact hσ.2.2
  exact this hx

theorem gd_xs {σ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hσ : Gd X u' σ) {x : (VS D).V} (hx : x ∈ XS X) :
    σ x ∈ XS X := by
  have h := gd_xz_sub hσ (Submodule.mem_sup_left hx : x ∈ XZ X u')
  have e : σ x = (σ x - x) + x := by abel
  rw [e]; exact add_mem h hx

theorem gd_xz {σ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hσ : Gd X u' σ) {x : (VS D).V} (hx : x ∈ XZ X u') :
    σ x ∈ XZ X u' := by
  have h := gd_xz_sub hσ hx
  have e : σ x = (σ x - x) + x := by abel
  rw [e]; exact add_mem (Submodule.mem_sup_left h) hx

theorem gd_orth {σ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hσ : Gd X u' σ) (hσ' : Gd X u' σ⁻¹) {x : (VS D).V}
    (hx : x ∈ orth (VS D) (XS X)) : σ x ∈ orth (VS D) (XS X) := by
  rw [mem_orth']
  intro y hy
  have e : y = σ (σ⁻¹ y) := by rw [Formalism.L2.SG.Pf.le_inv_app, LinearEquiv.apply_symm_apply]
  rw [e, hσ.1]
  exact (mem_orth'.1 hx) _ (gd_xs hσ' hy)

theorem levi_preserves_z_orthogonal {σ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hσ : Gd X u' σ) (hσ' : Gd X u' σ⁻¹) {w : (VS D).V}
    (hw : w ∈ Wsp X u') : (VS D).hT (X.zu u') (σ w) = 0 := by
  have h0 := hσ.1 (X.zu u') w
  rw [((mem_W_iff X u').1 hw).2.2] at h0
  have e : σ (X.zu u') = X.zu u' + (σ (X.zu u') - X.zu u') := by abel
  rw [e, map_add, LinearMap.add_apply,
    (mem_orth'.1 (gd_orth hσ hσ' (W_le_orth X u' hw))) _ hσ.2.2, add_zero] at h0
  exact h0

theorem gd_W_sub {σ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hσ : Gd X u' σ) (hσ' : Gd X u' σ⁻¹) {w : (VS D).V}
    (hw : w ∈ Wsp X u') : σ w - piWL X u' (σ w) ∈ XS X := by
  have ho := gd_orth hσ hσ' (W_le_orth X u' hw)
  have he : ∀ a, (VS D).hT (X.eX a) (σ w) = 0 := fun a => (mem_orth'.1 ho) _ (Submodule.subset_span ⟨a, rfl⟩)
  rw [piW_apply]
  simp only [he, zero_smul, Finset.sum_const_zero, sub_zero, levi_preserves_z_orthogonal hσ hσ' hw]
  have e : σ w - (σ w - ∑ a, (VS D).hT (X.fY a) (σ w) • X.eX a) = ∑ a, (VS D).hT (X.fY a) (σ w) • X.eX a := by
    abel
  rw [e]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem gd_piW {σ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hσ : Gd X u' σ) {x : (VS D).V}
    (hx : x ∈ orth (VS D) (XS X)) : piWL X u' (σ x) = piWL X u' (σ (piWL X u' x)) := by
  have hr := sub_piW X u' hx
  have e : σ x = σ (piWL X u' x) + σ (x - piWL X u' x) := by rw [← map_add]; congr 1; abel
  rw [e, map_add, piW_XZ X u' (gd_xz hσ hr), add_zero]

def psiL (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Wsp X u' →ₗ[D.host.E] Wsp X u' :=
  LinearMap.codRestrict (Wsp X u') ((piWL X u').comp (σ.toLinearMap.comp (Wsp X u').subtype))
    (fun w => piW_mem X u' _)

theorem psiL_coe (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (w : Wsp X u') :
    ((psiL σ w : Wsp X u') : (VS D).V) = piWL X u' (σ w) := rfl

theorem psiL_iso {σ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hσ : Gd X u' σ) (hσ' : Gd X u' σ⁻¹) (w w' : Wsp X u') :
    (VS D).hT (psiL σ w) (psiL σ w') = (VS D).hT w w' := by
  rw [psiL_coe, psiL_coe]
  have h1 := gd_W_sub hσ hσ' w.2
  have h2 := gd_W_sub hσ hσ' w'.2
  set p := piWL X u' (σ w)
  set p' := piWL X u' (σ w')
  have hp : p ∈ orth (VS D) (XS X) := W_le_orth X u' (piW_mem X u' _)
  have hp' : p' ∈ orth (VS D) (XS X) := W_le_orth X u' (piW_mem X u' _)
  have e1 : σ w = p + (σ w - p) := by abel
  have e2 : σ w' = p' + (σ w' - p') := by abel
  have hiso := hσ.1 w w'
  rw [e1, e2] at hiso
  simp only [map_add, LinearMap.add_apply] at hiso
  rw [(mem_orth'.1 hp') _ h1, (mem_orth'.1 (xs_le_orth X h2)) _ h1, hconj (σ w' - p') p,
    (mem_orth'.1 hp) _ h2, map_zero, add_zero, add_zero, add_zero] at hiso
  exact hiso

theorem psiL_comp {σ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hσ : Gd X u' σ) (hσ' : Gd X u' σ⁻¹) (w : Wsp X u') :
    psiL σ⁻¹ (psiL σ w) = w := by
  apply Subtype.ext
  rw [psiL_coe, psiL_coe, ← gd_piW hσ' (gd_orth hσ hσ' (W_le_orth X u' w.2)), Formalism.L2.SG.Pf.le_inv_app,
    LinearEquiv.symm_apply_apply, levi_projection_of_mem X u' w.2]

def psiE (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hσ : Gd X u' σ) (hσ' : Gd X u' σ⁻¹) :
    Wsp X u' ≃ₗ[D.host.E] Wsp X u' :=
  LinearEquiv.ofLinear (psiL σ) (psiL σ⁻¹)
    (LinearMap.ext fun w => by
      have h := psiL_comp (σ := σ⁻¹) hσ' (by rwa [inv_inv]) w
      simp only [inv_inv] at h
      exact h)
    (LinearMap.ext fun w => psiL_comp hσ hσ' w)

theorem key {σ τ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hσ : Gd X u' σ) (hσ' : Gd X u' σ⁻¹) (hτ : Gd X u' τ)
    (hτ' : Gd X u' τ⁻¹) (he : ∀ w : Wsp X u', piWL X u' (τ w) = piWL X u' (σ w)) {x : (VS D).V}
    (hx : x ∈ orth (VS D) (XS X)) : (τ⁻¹ * σ) x - x ∈ XS X := by
  have hr := sub_piW X u' hx
  have hw := piW_mem X u' x
  have dec : ∀ ρ : (VS D).V ≃ₗ[D.host.E] (VS D).V, Gd X u' ρ → Gd X u' ρ⁻¹ →
      ρ x - (piWL X u' (ρ (piWL X u' x)) + (x - piWL X u' x)) ∈ XS X := by
    intro ρ h1 h2
    have e : ρ x - (piWL X u' (ρ (piWL X u' x)) + (x - piWL X u' x)) =
        (ρ (piWL X u' x) - piWL X u' (ρ (piWL X u' x))) + (ρ (x - piWL X u' x) - (x - piWL X u' x)) := by
      rw [map_sub ρ x]; abel
    rw [e]
    exact add_mem (gd_W_sub h1 h2 hw) (gd_xz_sub h1 hr)
  have h1 := dec σ hσ hσ'
  have h2 := dec τ hτ hτ'
  rw [← he ⟨_, hw⟩] at h1
  have h3 : σ x - τ x ∈ XS X := by
    have e : σ x - τ x = (σ x - (piWL X u' (τ (piWL X u' x)) + (x - piWL X u' x))) -
        (τ x - (piWL X u' (τ (piWL X u' x)) + (x - piWL X u' x))) := by abel
    rw [e]; exact sub_mem h1 h2
  have e : (τ⁻¹ * σ) x - x = τ⁻¹ (σ x - τ x) := by
    rw [map_sub, Formalism.L2.SG.Pf.le_mul_app, Formalism.L2.SG.Pf.le_inv_app τ (τ x), LinearEquiv.symm_apply_apply]
  rw [e]
  exact gd_xs hτ' h3

end LeviAlg

namespace LeviAlg

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u' : D.what₂.Word}

theorem psiE_iso {σ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hσ : Gd X u' σ) (hσ' : Gd X u' σ⁻¹) :
    psiE σ hσ hσ' ∈ Formalism.HermitianLatticesTheory.isom (hW X u') := by
  intro w w'
  exact psiL_iso hσ hσ' w w'

theorem mem_LW {Λ : Submodule (𝓞 D.host.E) (VS D).V} {y : Wsp X u'} :
    y ∈ LW X u' Λ ↔ ∃ x, x ∈ Λ ∧ x ∈ orth (VS D) (XS X) ∧ piWL X u' x = y := by
  unfold LW
  rw [Submodule.mem_comap, Submodule.mem_map]
  constructor
  · rintro ⟨x, hx, hxy⟩
    rw [Submodule.mem_inf] at hx
    refine ⟨x, hx.1, ?_, hxy⟩
    have := hx.2
    rwa [Submodule.restrictScalars_mem, xsp_eq] at this
  · rintro ⟨x, h1, h2, h3⟩
    refine ⟨x, Submodule.mem_inf.2 ⟨h1, ?_⟩, h3⟩
    rw [Submodule.restrictScalars_mem, xsp_eq]; exact h2

theorem psiE_le {σ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hσ : Gd X u' σ) (hσ' : Gd X u' σ⁻¹)
    {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Formalism.HermitianLatticesTheory.gmap σ Λ = Λ) :
    Formalism.HermitianLatticesTheory.gmap (psiE σ hσ hσ') (LW X u' Λ) ≤ LW X u' Λ := by
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨x, hxΛ, hxo, hxw⟩ := mem_LW.1 hw
  have hσx : σ x ∈ Λ := by
    rw [← hΛ]; exact ⟨x, hxΛ, rfl⟩
  refine mem_LW.2 ⟨σ x, hσx, gd_orth hσ hσ' hxo, ?_⟩
  show piWL X u' (σ x) = piWL X u' (σ w)
  rw [← hxw, gd_piW hσ hxo]

theorem psiE_lat {σ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hσ : Gd X u' σ) (hσ' : Gd X u' σ⁻¹)
    {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Formalism.HermitianLatticesTheory.gmap σ Λ = Λ) :
    Formalism.HermitianLatticesTheory.gmap (psiE σ hσ hσ') (LW X u' Λ) = LW X u' Λ := by
  refine le_antisymm (psiE_le hσ hσ' hΛ) fun y hy => ?_
  have hσ'' : Gd X u' σ⁻¹⁻¹ := by rwa [inv_inv]
  have h1 := psiE_le hσ' hσ'' (Formalism.L2.SG.Pf.gmap_inv hΛ) ⟨y, hy, rfl⟩
  refine ⟨_, h1, ?_⟩
  have h := psiL_comp (σ := σ⁻¹) hσ' hσ'' y
  simp only [inv_inv] at h
  exact h

theorem gd_of_point (hZ : SratZC) {σ : (VS D).V ≃ₗ[D.host.E] (VS D).V} {s : X.B.I.GA} (hs : RatLink X s σ)
    (hσ : σ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (hS : s ∈ Srat X u') : Gd X u' σ := by
  refine ⟨hσ, fun a => Submodule.span_mono (Set.image_subset_range _ _)
    (Formalism.L2.SG.Pf.RegroupPf.StabFlagPf.flag_e X hs hS a), ?_⟩
  have := hZ D X u' s σ hs hS
  rwa [xsp_eq] at this

end LeviAlg

open LeviAlg in

theorem leviStabFinC_of (hWF : LeviWFinC) (hZ : SratZC) : LeviStabFinC := by
  intro D X Y u' Λ hΛ
  let G : Set ((VS D).V ≃ₗ[D.host.E] (VS D).V) := {σ | σ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧
    Formalism.HermitianLatticesTheory.gmap σ Λ = Λ ∧ ∃ t : X.B.I.GA, RatLink X t σ ∧ t ∈ Srat X u'}
  have hG : ∀ σ ∈ G, Gd X u' σ ∧ Gd X u' σ⁻¹ := by
    rintro σ ⟨hi, -, t, ht, hS⟩
    exact ⟨gd_of_point hZ ht hi hS, gd_of_point hZ (ratLink_inv X ht) ((Formalism.HermitianLatticesTheory.isom _).inv_mem hi)
      ((Srat X u').inv_mem hS)⟩
  let Φ : G → (Wsp X u' ≃ₗ[D.host.E] Wsp X u') := fun σ => psiE σ.1 (hG σ.1 σ.2).1 (hG σ.1 σ.2).2
  have hrange : Set.range Φ ⊆ {g : Wsp X u' ≃ₗ[D.host.E] Wsp X u' | g ∈ Formalism.HermitianLatticesTheory.isom (hW X u') ∧
      Formalism.HermitianLatticesTheory.gmap g (LW X u' Λ) = LW X u' Λ} := by
    rintro _ ⟨σ, rfl⟩
    exact ⟨psiE_iso _ _, psiE_lat _ _ σ.2.2.1⟩
  have hfin : (Set.range Φ).Finite := (hWF D X Y u' Λ hΛ).subset hrange
  let ch : (Wsp X u' ≃ₗ[D.host.E] Wsp X u') → ((VS D).V ≃ₗ[D.host.E] (VS D).V) := fun g =>
    if hg : ∃ σ : G, Φ σ = g then (hg.choose : (VS D).V ≃ₗ[D.host.E] (VS D).V) else 1
  refine ⟨hfin.toFinset.image ch, ?_, ?_⟩
  · intro τ hτ
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hτ
    have hg' : ∃ σ : G, Φ σ = g := hfin.mem_toFinset.1 hg
    simp only [ch, dif_pos hg']
    exact hg'.choose.2
  · intro σ s hs hσ hS hgσ
    have hσG : σ ∈ G := ⟨hσ, hgσ, s, hs, hS⟩
    have hg' : ∃ ρ : G, Φ ρ = Φ ⟨σ, hσG⟩ := ⟨_, rfl⟩
    refine ⟨ch (Φ ⟨σ, hσG⟩), Finset.mem_image.2 ⟨_, hfin.mem_toFinset.2 ⟨_, rfl⟩, rfl⟩, ?_⟩
    simp only [ch, dif_pos hg']
    have hτ := hg'.choose_spec
    intro x hx
    rw [LeviAlg.xsp_eq] at hx ⊢
    refine key (hG σ hσG).1 (hG σ hσG).2 (hG _ hg'.choose.2).1 (hG _ hg'.choose.2).2 (fun w => ?_) hx
    exact congrArg (fun g : Wsp X u' ≃ₗ[D.host.E] Wsp X u' => ((g w : Wsp X u') : (VS D).V)) hτ

end Formalism.L2.SG.Pf.SlabCount
