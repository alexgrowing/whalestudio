import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LatSpanLeSpan

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.Pf Formalism.L2.SG.Pf.Act Formalism.L2.SG.Saturated

namespace GlobalTheory.RowRep

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

def chg (e f f' : Fin r → S.V) (σ : S.V ≃ₗ[E] S.V) : S.V →ₗ[E] S.V :=
  pX e f' + pY e f + pj e f ∘ₗ (σ : S.V →ₗ[E] S.V) ∘ₗ pj e f'

theorem chg_apply (e f f' : Fin r → S.V) (σ : S.V ≃ₗ[E] S.V) (v : S.V) :
    chg e f f' σ v = pX e f' v + pY e f v + pj e f (σ (pj e f' v)) := by
  simp [chg]

variable {e f f' : Fin r → S.V}
  (hee : ∀ a b, S.hT (e a) (e b) = 0) (hff : ∀ a b, S.hT (f a) (f b) = 0)
  (hef : ∀ a b, S.hT (e a) (f b) = if a = b then 1 else 0)
  (hff' : ∀ a b, S.hT (f' a) (f' b) = 0)
  (hef' : ∀ a b, S.hT (e a) (f' b) = if a = b then 1 else 0)
  {σ : S.V ≃ₗ[E] S.V} (hσ : σ ∈ Formalism.HermitianLatticesTheory.isom S.hT)
  (hX' : ∀ x ∈ Submodule.span E (Set.range e), σ.symm x ∈ Submodule.span E (Set.range e))

include hee hef hef' in
theorem hT_e_chg (v : S.V) (b : Fin r) : S.hT (e b) (chg e f f' σ v) = S.hT (e b) v := by
  rw [chg_apply, map_add, map_add, hT_e_pX hee, hT_e_pY hef, hT_e_pj hee hef]
  simp

include hff hef in
theorem hT_f_chg (v : S.V) (b : Fin r) : S.hT (f b) (chg e f f' σ v) = S.hT (f' b) v := by
  rw [chg_apply, map_add, map_add, hT_f_pY hff, hT_f_pj hff hef, pX_apply, map_sum]
  simp [map_smul, hfe' hef]

include hee hff hef in
theorem pj_chg (v : S.V) : pj e f (chg e f f' σ v) = pj e f (σ (pj e f' v)) := by
  rw [chg_apply, map_add, map_add, pj_of_memX hee hef _ (pX_mem v), pj_of_memY hff hef _ (pY_mem v),
    pj_pj hee hff hef]
  simp

include hee hff hef hff' hef' hσ hX' in
theorem hT_chg (v w : S.V) : S.hT (chg e f f' σ v) (chg e f f' σ w) = S.hT v w := by
  rw [hT_coord hee hff hef (chg e f f' σ v), hT_coord hee hff' hef' v w]
  simp only [hT_f_chg hff hef, hT_e_chg hee hef hef', pj_chg hee hff hef]
  congr 1
  have hp : ∀ u, ∀ a, S.hT (e a) (σ (pj e f' u)) = 0 := fun u a =>
    perpX_map σ hσ hX' _ (fun b => hT_e_pj hee hef' u b) a
  rw [hT_modX hee (hp v) (hp w) (pj_sub_mem _ (hp v)) (pj_sub_mem _ (hp w)), isom_apply hσ]

include hee hff hef hff' hef' hσ hX' in
theorem chg_chg (v : S.V) : chg e f' f σ.symm (chg e f f' σ v) = v := by
  have hp : ∀ a, S.hT (e a) (σ (pj e f' v)) = 0 := perpX_map σ hσ hX' _ (fun b => hT_e_pj hee hef' v b)
  have h1 : pX e f (chg e f f' σ v) = pX e f' v := by
    rw [chg_apply, map_add, map_add, pX_of_mem hef _ (pX_mem v), pX_of_memY hff _ (pY_mem v), pX_pj hff hef]
    simp
  have h2 : pY e f' (chg e f f' σ v) = pY e f' v := by
    rw [pY_apply, pY_apply]
    simp only [hT_e_chg hee hef hef']
  have h3 : pj e f' (σ.symm (pj e f (chg e f f' σ v))) = pj e f' v := by
    rw [pj_chg hee hff hef]
    have hx : σ.symm (pj e f (σ (pj e f' v))) - pj e f' v ∈ Submodule.span E (Set.range e) := by
      have := hX' _ (pj_sub_mem (f := f) _ hp)
      rwa [map_sub, LinearEquiv.symm_apply_apply] at this
    have : σ.symm (pj e f (σ (pj e f' v))) = pj e f' v + (σ.symm (pj e f (σ (pj e f' v))) - pj e f' v) := by abel
    rw [this, map_add, pj_pj hee hff' hef', pj_of_memX hee hef' _ hx, add_zero]
  rw [chg_apply, h1, h2, h3, ← decomp (e := e) (f := f') v]

include hee hef' in
theorem chg_e (b : Fin r) : chg e f f' σ (e b) = e b := by
  have hb : e b ∈ Submodule.span E (Set.range e) := Submodule.subset_span ⟨b, rfl⟩
  rw [chg_apply, pX_of_mem hef' _ hb, pY_of_memX hee _ hb, pj_of_memX hee hef' _ hb]
  simp

include hff' hef' in
theorem chg_f (b : Fin r) : chg e f f' σ (f' b) = f b := by
  have hb : f' b ∈ Submodule.span E (Set.range f') := Submodule.subset_span ⟨b, rfl⟩
  rw [chg_apply, pX_of_memY hff' _ hb, pj_f hff' hef', pY_apply]
  simp [hef']

theorem chg_perp (l : S.V) (hl : ∀ a, S.hT (e a) l = 0 ∧ S.hT (f' a) l = 0) :
    chg e f f' σ l = pj e f (σ l) := by
  rw [chg_apply, pj_perp l hl, pX_apply, pY_apply]
  simp [(hl _).1, (hl _).2]

include hee hef in
theorem chg_apply_of_orthogonal (z : S.V) (hz : ∀ a, S.hT (e a) z = 0 ∧ S.hT (f' a) z = 0) (hzf : ∀ a, S.hT (f a) z = 0)
    (hσz : σ z - z ∈ Submodule.span E (Set.range e)) : chg e f f' σ z = z := by
  rw [chg_perp z hz, show σ z = z + (σ z - z) by abel, map_add, pj_of_memX hee hef _ hσz, add_zero,
    pj_perp z fun a => ⟨(hz a).1, hzf a⟩]

include hee hff hef in
theorem pj_mem_L (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E) {Λ L : Submodule (𝓞 E) S.V}
    (hΛ : Λ = latSpan aa e ⊔ L ⊔ latSpan (fun a => (aa a)⁻¹) f)
    (hLp : ∀ x ∈ L, ∀ a, S.hT (e a) x = 0 ∧ S.hT (f a) x = 0) (v : S.V) (hv : v ∈ Λ) : pj e f v ∈ L := by
  have h : Λ ≤ L.comap ((pj e f).restrictScalars (𝓞 E)) := by
    rw [hΛ]
    refine sup_le (sup_le ?_ ?_) ?_
    · rw [latSpan, Submodule.span_le]
      rintro _ ⟨a, x, -, rfl⟩
      show pj e f (x • e a) ∈ L
      rw [map_smul, pj_e hee hef, smul_zero]
      exact L.zero_mem
    · intro l hl
      show pj e f l ∈ L
      rw [pj_perp l (fun a => hLp l hl a)]
      exact hl
    · rw [latSpan, Submodule.span_le]
      rintro _ ⟨a, x, -, rfl⟩
      show pj e f (x • f a) ∈ L
      rw [map_smul, pj_f hff hef, smul_zero]
      exact L.zero_mem
  exact h hv

include hee hff hef hff' hef' in
theorem chg_mem (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E) {Λ L Λ' L' : Submodule (𝓞 E) S.V}
    (hΛ : Λ = latSpan aa e ⊔ L ⊔ latSpan (fun a => (aa a)⁻¹) f)
    (hLp : ∀ x ∈ L, ∀ a, S.hT (e a) x = 0 ∧ S.hT (f a) x = 0)
    (hΛ' : Λ' = latSpan aa e ⊔ L' ⊔ latSpan (fun a => (aa a)⁻¹) f')
    (hLp' : ∀ x ∈ L', ∀ a, S.hT (e a) x = 0 ∧ S.hT (f' a) x = 0)
    (hσΛ : ∀ v ∈ Λ', σ v ∈ Λ) (v : S.V) (hv : v ∈ Λ') : chg e f f' σ v ∈ Λ := by
  have hXΛ : latSpan aa e ≤ Λ := by rw [hΛ]; exact le_sup_left.trans le_sup_left
  have hLΛ : L ≤ Λ := by rw [hΛ]; exact le_sup_right.trans le_sup_left
  have hYΛ : latSpan (fun a => (aa a)⁻¹) f ≤ Λ := by rw [hΛ]; exact le_sup_right
  have hL'Λ' : L' ≤ Λ' := by rw [hΛ']; exact le_sup_right.trans le_sup_left
  have h : Λ' ≤ Λ.comap ((chg e f f' σ).restrictScalars (𝓞 E)) := by
    conv_lhs => rw [hΛ']
    refine sup_le (sup_le ?_ ?_) ?_
    · rw [latSpan, Submodule.span_le]
      rintro _ ⟨a, x, hx, rfl⟩
      show chg e f f' σ (x • e a) ∈ Λ
      rw [map_smul, chg_e hee hef']
      exact hXΛ (Submodule.subset_span ⟨a, x, hx, rfl⟩)
    · intro l hl
      show chg e f f' σ l ∈ Λ
      rw [chg_perp l (hLp' l hl)]
      exact hLΛ (pj_mem_L hee hff hef aa hΛ hLp _ (hσΛ l (hL'Λ' hl)))
    · rw [latSpan, Submodule.span_le]
      rintro _ ⟨a, x, hx, rfl⟩
      show chg e f f' σ (x • f' a) ∈ Λ
      rw [map_smul, chg_f hff' hef']
      exact hYΛ (Submodule.subset_span ⟨a, x, hx, rfl⟩)
  exact h hv

end Gen

end GlobalTheory.RowRep

namespace GlobalTheory.RowRep

open Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData
  Formalism.L2.SG.TermLoc GlobalTheory.Unfold

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section D7

variable {D : D7} {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word)

theorem exists_adapt (Λ : LV D) (hΛ : IsRowLat D (X.Fu u) Λ) :
    ∃ Λ' ∈ Y.what₂ u, ∃ σ, Adapt σ (lf D (X.Fu u)) (lf D (X.Fu u)) ∧ Formalism.HermitianLatticesTheory.gmap σ Λ' = Λ := by
  obtain ⟨Λ', ⟨hΛ'm, δ, ⟨hδi, hδX, hδz⟩, hδΛ⟩, -⟩ := (Y.rowsOK u).2 Λ hΛ
  obtain ⟨f, L, hff, hef, hLp, hzL, hsplit⟩ := Y.split u Λ' hΛ'm
  have hee := (X.Fu u).e_iso
  obtain ⟨-, ⟨-, hunΛ', -, -⟩, hXΛ'⟩ := (Y.rowsOK u).1 Λ' hΛ'm
  obtain ⟨-, -, hXΛ⟩ := hΛ
  have hXX : ((X.Fu u).X).map (δ : (VS D).V →ₗ[D.host.E] (VS D).V) = (X.Fu u).X := by
    rw [← Xa_r' (X.Fu u)]; exact hδX _
  have hXd : ∀ x ∈ Submodule.span D.host.E (Set.range (X.Fu u).e),
      δ x ∈ Submodule.span D.host.E (Set.range (X.Fu u).e) := fun x hx => by
    change δ x ∈ (X.Fu u).X
    rw [← hXX]
    exact Submodule.mem_map_of_mem hx
  have hXs : ∀ x ∈ Submodule.span D.host.E (Set.range (X.Fu u).e),
      δ.symm x ∈ Submodule.span D.host.E (Set.range (X.Fu u).e) := fun x hx => by
    change x ∈ (X.Fu u).X at hx
    rw [← hXX, Submodule.mem_map_equiv] at hx
    exact hx
  have hlatΛ' : latSpan (aaS D) (X.Fu u).e ≤ Λ' := by
    rw [hsplit]; exact le_sup_left.trans le_sup_left
  have hXLam : ∀ x ∈ latSpan (aaS D) (X.Fu u).e, x ∈ XLam Λ' (lf D (X.Fu u)) := fun x hx =>
    ⟨hlatΛ' hx, latSpan_le_span _ _ x hx⟩
  have hδ1 : ∀ x ∈ latSpan (aaS D) (X.Fu u).e, δ.symm x ∈ Λ' := fun x hx => by
    have h1 : x ∈ XLam Λ (lf D (X.Fu u)) := (hXΛ'.trans hXΛ.symm).le (hXLam x hx)
    have h2 : x ∈ Formalism.HermitianLatticesTheory.gmap δ Λ' := by rw [hδΛ]; exact h1.1
    rwa [mem_gmap_iff] at h2
  have hδ2 : ∀ x ∈ latSpan (aaS D) (X.Fu u).e, δ.symm.symm x ∈ Λ' := fun x hx => by
    rw [LinearEquiv.symm_symm]
    have hx' := hXLam x hx
    have h1 : δ x ∈ XLam Λ (lf D (X.Fu u)) := by
      refine ⟨?_, hXd x hx'.2⟩
      rw [← hδΛ]
      exact (gmap_apply_mem δ Λ' x).2 hx'.1
    exact ((hXΛ.trans hXΛ'.symm).le h1).1
  let a := lequiv hee hff hef (δ := δ.symm) (inv_mem hδi) hXs
  have ha : Formalism.HermitianLatticesTheory.gmap a Λ' = Λ' :=
    gmap_lequiv hee hff hef (inv_mem hδi) hXs (aaS D) hsplit hLp hunΛ' hδ1 hδ2
  have hγe : ∀ b, (δ * a) ((X.Fu u).e b) = (X.Fu u).e b := fun b => by
    show δ (a ((X.Fu u).e b)) = (X.Fu u).e b
    rw [show a ((X.Fu u).e b) = δ.symm ((X.Fu u).e b) from lequiv_e hee hff hef (inv_mem hδi) hXs b,
      LinearEquiv.apply_symm_apply]
  have hγz : (δ * a) (X.Fu u).z = (X.Fu u).z := by
    show δ (a (X.Fu u).z) = (X.Fu u).z
    rw [show a (X.Fu u).z = (X.Fu u).z from lmap_perp _ (hLp _ hzL), hδz]
  refine ⟨Λ', hΛ'm, δ * a, ⟨mul_mem hδi (lequiv_isom hee hff hef (inv_mem hδi) hXs), fun b => ?_⟩, ?_⟩
  · have hfix : (δ * a) (frame (lf D (X.Fu u)) b) = frame (lf D (X.Fu u)) b := by
      refine Fin.lastCases ?_ (fun i => ?_) b
      · rw [frame_last_sat]; exact hγz
      · rw [frame_castSucc_sat]; exact hγe i
    rw [hfix, sub_self]
    exact Submodule.zero_mem _
  · rw [gmap_mul_sat, ha, hδΛ]

theorem eq_of_adapt (Λ : LV D) (hΛ : Λ ∈ Y.what₂ u) (Λ' : LV D) (hΛ' : Λ' ∈ Y.what₂ u) (σ : GV D)
    (hσ : Adapt σ (lf D (X.Fu u)) (lf D (X.Fu u))) (hσΛ : Formalism.HermitianLatticesTheory.gmap σ Λ' = Λ) : Λ' = Λ := by
  obtain ⟨f, L, hff, hef, hLp, hzL, hsplit⟩ := Y.split u Λ hΛ
  obtain ⟨f', L', hff', hef', hLp', hzL', hsplit'⟩ := Y.split u Λ' hΛ'
  have hee := (X.Fu u).e_iso
  obtain ⟨hσi, hσf⟩ := hσ
  have he : ∀ b, σ ((X.Fu u).e b) ∈ Submodule.span D.host.E (Set.range (X.Fu u).e) := fun b => by
    have h := hσf (Fin.castSucc b)
    rw [frame_castSucc_sat] at h
    have h2 : σ ((X.Fu u).e b) - (X.Fu u).e b ∈ Xsp (lf D (X.Fu u)) := Xflag_le_X (lf D (X.Fu u)) _ h
    have h3 : σ ((X.Fu u).e b) - (X.Fu u).e b + (X.Fu u).e b ∈ Xsp (lf D (X.Fu u)) :=
      Submodule.add_mem _ h2 (Submodule.subset_span ⟨b, rfl⟩)
    rw [sub_add_cancel] at h3
    exact h3
  have hX : ∀ x ∈ Submodule.span D.host.E (Set.range (X.Fu u).e),
      σ x ∈ Submodule.span D.host.E (Set.range (X.Fu u).e) := by
    have : Submodule.span D.host.E (Set.range (X.Fu u).e) ≤
        (Submodule.span D.host.E (Set.range (X.Fu u).e)).comap (σ : (VS D).V →ₗ[D.host.E] (VS D).V) :=
      Submodule.span_le.2 (by rintro _ ⟨b, rfl⟩; exact he b)
    exact fun x hx => this hx
  have hmap : (Submodule.span D.host.E (Set.range (X.Fu u).e)).map (σ : (VS D).V →ₗ[D.host.E] (VS D).V) =
      Submodule.span D.host.E (Set.range (X.Fu u).e) := by
    have hle : (Submodule.span D.host.E (Set.range (X.Fu u).e)).map (σ : (VS D).V →ₗ[D.host.E] (VS D).V) ≤
        Submodule.span D.host.E (Set.range (X.Fu u).e) :=
      Submodule.map_le_iff_le_comap.2 (fun x hx => hX x hx)
    exact Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq σ _)
  have hX' : ∀ x ∈ Submodule.span D.host.E (Set.range (X.Fu u).e),
      σ.symm x ∈ Submodule.span D.host.E (Set.range (X.Fu u).e) := fun x hx => by
    rw [← hmap, Submodule.mem_map_equiv] at hx
    exact hx
  have hz : σ (X.Fu u).z - (X.Fu u).z ∈ Submodule.span D.host.E (Set.range (X.Fu u).e) := by
    have h := hσf (Fin.last _)
    rw [frame_last_sat] at h
    have h2 : σ (X.Fu u).z - (X.Fu u).z ∈ Xsp (lf D (X.Fu u)) := Xflag_le_X (lf D (X.Fu u)) _ h
    exact h2
  have hσs : σ.symm ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := inv_mem hσi
  have hXs' : ∀ x ∈ Submodule.span D.host.E (Set.range (X.Fu u).e),
      σ.symm.symm x ∈ Submodule.span D.host.E (Set.range (X.Fu u).e) := fun x hx => by
    rw [LinearEquiv.symm_symm]; exact hX x hx
  let γ : GV D := LinearEquiv.ofLinear (chg (X.Fu u).e f f' σ) (chg (X.Fu u).e f' f σ.symm)
    (LinearMap.ext fun v => by
      have := chg_chg hee hff' hef' hff hef hσs hXs' v
      rw [LinearEquiv.symm_symm] at this
      exact this)
    (LinearMap.ext fun v => chg_chg hee hff hef hff' hef' hσi hX' v)
  have hγe : ∀ b, γ ((X.Fu u).e b) = (X.Fu u).e b := fun b => chg_e hee hef' b
  have hγz : γ (X.Fu u).z = (X.Fu u).z :=
    chg_apply_of_orthogonal hee hef _ (fun a => ⟨(X.Fu u).z_orth a, (hLp' _ hzL' a).2⟩) (fun a => (hLp _ hzL a).2) hz
  have hγ : γ ∈ stabF D (X.Fu u) := by
    refine ⟨fun v w => hT_chg hee hff hef hff' hef' hσi hX' v w, fun j => ?_, hγz⟩
    rw [FlagG.Xa, Submodule.map_span, Set.image_image]
    congr 1
    exact Set.image_congr fun i _ => hγe i
  have hσΛ1 : ∀ v ∈ Λ', σ v ∈ Λ := fun v hv => by rw [← hσΛ]; exact (gmap_apply_mem σ Λ' v).2 hv
  have hσΛ2 : ∀ v ∈ Λ, σ.symm v ∈ Λ' := fun v hv => by rw [← hσΛ, mem_gmap_iff] at hv; exact hv
  have hγΛ : Formalism.HermitianLatticesTheory.gmap γ Λ' = Λ := by
    ext x
    rw [mem_gmap_iff]
    constructor
    · intro h
      have h1 : γ (γ.symm x) ∈ Λ := chg_mem hee hff hef hff' hef' (aaS D) hsplit hLp hsplit' hLp' hσΛ1 _ h
      rwa [LinearEquiv.apply_symm_apply] at h1
    · intro h
      exact chg_mem hee hff' hef' hff hef (aaS D) hsplit' hLp' hsplit hLp hσΛ2 _ h
  have hone : (1 : GV D) ∈ stabF D (X.Fu u) := by
    refine ⟨one_mem _, fun j => ?_, rfl⟩
    rw [show ((1 : GV D) : (VS D).V →ₗ[D.host.E] (VS D).V) = LinearMap.id from rfl, Submodule.map_id]
  obtain ⟨Λ0, -, huniq⟩ := (Y.rowsOK u).2 Λ ((Y.rowsOK u).1 Λ hΛ)
  rw [huniq Λ' ⟨hΛ', γ, hγ, hγΛ⟩, huniq Λ ⟨hΛ, 1, hone, gmap_one_sat Λ⟩]

end D7

theorem rowReps : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    (∀ Λ, IsRowLat D (X.Fu u) Λ → ∃ Λ' ∈ Y.what₂ u, ∃ σ, Adapt σ (lf D (X.Fu u)) (lf D (X.Fu u)) ∧
      Formalism.HermitianLatticesTheory.gmap σ Λ' = Λ) ∧
    ∀ Λ ∈ Y.what₂ u, ∀ Λ' ∈ Y.what₂ u, ∀ σ, Adapt σ (lf D (X.Fu u)) (lf D (X.Fu u)) →
      Formalism.HermitianLatticesTheory.gmap σ Λ' = Λ → Λ' = Λ :=
  fun _ _ Y u _ => ⟨fun Λ hΛ => exists_adapt Y u Λ hΛ,
    fun Λ hΛ Λ' hΛ' σ hσ hσΛ => eq_of_adapt Y u Λ hΛ Λ' hΛ' σ hσ hσΛ⟩

end GlobalTheory.RowRep
