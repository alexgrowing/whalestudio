import Formalism.LocalToGlobal.GlobalTheory.GL6.RndLinkAdmTOf

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG

variable {D : D7} {u : D.what₂.Word}

set_option maxHeartbeats 2000000 in

def RUpLocM (Tf : FormsTied D u) : Prop :=
  ∀ i (hi : i ≤ D.R.m) v c (z : ↥(Ld D u i hi c)), (D.fm u).fv i v c ((Tf.lv i hi).pr v c z) = 1 →
    ∀ (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi)) (η : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ : (Tf.cls i hi).lev.U),
        (∀ v', v' ≠ (Tf.atT.eV v).1 → bc (prV (E := D.host.E) v') η.1 = 1) →
        bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 *
          ((Tf.cls i hi).y ((D.fm u).up i v c ((Tf.lv i hi).pr v c z))).1 = ((Tf.cls i hi).y c).1 * η.1 * κ.1 →
        Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ.1.1 (clsCrd D u i hi ((D.fm u).up i v c ((Tf.lv i hi).pr v c z)))) =
          Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (Ld D u i hi c) →
        Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ.1.1 (Ld D u i hi ((D.fm u).up i v c ((Tf.lv i hi).pr v c z)))) =
          Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (Ld D u i hi c ⊔
            Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z.1}) →
        (∀ (x : ↥(Ld D u i hi ((D.fm u).up i v c ((Tf.lv i hi).pr v c z))))
          (hx : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ.1.1 *ᵥ x.1) ∈ Ld D u i hi c),
          (D.fm u).fv i v _ ((Tf.lv i hi).pr v _ x) = (D.fm u).fv i v c ((Tf.lv i hi).pr v c ⟨_, hx⟩)) →
    ∃ e : (D.fm u).lk i v ((D.fm u).up i v c ((Tf.lv i hi).pr v c z)) ≃ₗ[(D.mem u).A.Fv v] (D.fm u).lv i v c,
      e ((D.fm u).te i v ((D.fm u).up i v c ((Tf.lv i hi).pr v c z))) = (Tf.lv i hi).pr v c z ∧
      ∀ (γ' : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi)) (η' : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ' : (Tf.cls i hi).lev.U),
        (∀ v', v' ≠ (Tf.atT.eV v).1 → bc (prV (E := D.host.E) v') η'.1 = 1) →
        bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ'.1 *
          ((Tf.cls i hi).y ((D.fm u).dn i v ((D.fm u).up i v c ((Tf.lv i hi).pr v c z)) (((D.fm u).fv i v c).comp e.toLinearMap))).1 =
          ((Tf.cls i hi).y ((D.fm u).up i v c ((Tf.lv i hi).pr v c z))).1 * η'.1 * κ'.1 →
        Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ'.1.1 (Ld D u i hi ((D.fm u).dn i v ((D.fm u).up i v c ((Tf.lv i hi).pr v c z)) (((D.fm u).fv i v c).comp e.toLinearMap)))) =
          Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi ((D.fm u).up i v c ((Tf.lv i hi).pr v c z))) →
        (∀ (x : ↥(Ld D u i hi ((D.fm u).dn i v ((D.fm u).up i v c ((Tf.lv i hi).pr v c z)) (((D.fm u).fv i v c).comp e.toLinearMap))))
          (hx : γ'.1.1 *ᵥ x.1 ∈ Lk Tf.atT i hi v ((D.fm u).up i v c ((Tf.lv i hi).pr v c z))),
          (D.fm u).fv i v _ ((Tf.lv i hi).pr v _ x) =
            (((D.fm u).fv i v c).comp e.toLinearMap)
              ((Tf.lv i hi).prk v ((D.fm u).up i v c ((Tf.lv i hi).pr v c z)) ⟨_, hx⟩)) →
      η.1 * κ.1 * η'.1 * κ'.1 ∈ (Tf.cls i hi).lev.U

set_option maxHeartbeats 2000000 in

def RDnLocM (Tf : FormsTied D u) : Prop :=
  ∀ i (hi : i ≤ D.R.m) v c (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c)), g ((D.fm u).te i v c) = 1 →
    ∀ (γ' : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi)) (η' : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ' : (Tf.cls i hi).lev.U),
        (∀ v', v' ≠ (Tf.atT.eV v).1 → bc (prV (E := D.host.E) v') η'.1 = 1) →
        bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ'.1 *
          ((Tf.cls i hi).y ((D.fm u).dn i v c g)).1 = ((Tf.cls i hi).y c).1 * η'.1 * κ'.1 →
        Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ'.1.1 (Ld D u i hi ((D.fm u).dn i v c g))) =
          Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi c) →
        (∀ (x : ↥(Ld D u i hi ((D.fm u).dn i v c g))) (hx : γ'.1.1 *ᵥ x.1 ∈ Lk Tf.atT i hi v c),
          (D.fm u).fv i v _ ((Tf.lv i hi).pr v _ x) = g ((Tf.lv i hi).prk v c ⟨_, hx⟩)) →
    ∃ e : (D.fm u).lv i v ((D.fm u).dn i v c g) ≃ₗ[(D.mem u).A.Fv v] (D.fm u).lk i v c,
      (D.fm u).fv i v ((D.fm u).dn i v c g) = g.comp e.toLinearMap ∧
      ∀ (z : ↥(Ld D u i hi ((D.fm u).dn i v c g))),
        (Tf.lv i hi).pr v ((D.fm u).dn i v c g) z = e.symm ((D.fm u).te i v c) →
      ∀ (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi)) (η : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ : (Tf.cls i hi).lev.U),
        (∀ v', v' ≠ (Tf.atT.eV v).1 → bc (prV (E := D.host.E) v') η.1 = 1) →
        bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 *
          ((Tf.cls i hi).y ((D.fm u).up i v ((D.fm u).dn i v c g) ((Tf.lv i hi).pr v _ z))).1 =
          ((Tf.cls i hi).y ((D.fm u).dn i v c g)).1 * η.1 * κ.1 →
        Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v)
                  (mulLat γ.1.1 (clsCrd D u i hi ((D.fm u).up i v ((D.fm u).dn i v c g) ((Tf.lv i hi).pr v _ z)))) =
          Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (Ld D u i hi ((D.fm u).dn i v c g)) →
        Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v)
                  (mulLat γ.1.1 (Ld D u i hi ((D.fm u).up i v ((D.fm u).dn i v c g) ((Tf.lv i hi).pr v _ z)))) =
          Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (Ld D u i hi ((D.fm u).dn i v c g) ⊔
            Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z.1}) →
        (∀ (x : ↥(Ld D u i hi ((D.fm u).up i v ((D.fm u).dn i v c g) ((Tf.lv i hi).pr v _ z))))
          (hx : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ.1.1 *ᵥ x.1) ∈ Ld D u i hi ((D.fm u).dn i v c g)),
          (D.fm u).fv i v _ ((Tf.lv i hi).pr v _ x) =
            (D.fm u).fv i v ((D.fm u).dn i v c g) ((Tf.lv i hi).pr v ((D.fm u).dn i v c g) ⟨_, hx⟩)) →
      η'.1 * κ'.1 * η.1 * κ.1 ∈ (Tf.cls i hi).lev.U

set_option maxHeartbeats 4000000 in
theorem rupLocM_of (Tf : FormsTied D u) (h : RUpLoc Tf) : RUpLocM Tf := by
  intro i hi v c z hz γ η κ hsup hrel hl1 hl2 hfun
  obtain ⟨e, he1, he2⟩ := h i hi v c z hz
  exact ⟨e, he1, fun γ' η' κ' hsup' hrel' hl1' hfun' =>
    he2 γ η κ hsup hrel hl1 hl2 hfun γ' η' κ' hsup' hrel' hl1' hfun'⟩

set_option maxHeartbeats 4000000 in
theorem rdnLocM_of (Tf : FormsTied D u) (h : RDnLoc Tf) : RDnLocM Tf := by
  intro i hi v c g hg γ' η' κ' hsup' hrel' hl1' hfun'
  obtain ⟨e, he1, he2⟩ := h i hi v c g hg
  exact ⟨e, he1, fun z hz γ η κ hsup hrel hl1 hl2 hfun =>
    he2 z hz γ' η' κ' hsup' hrel' hl1' hfun' γ η κ hsup hrel hl1 hl2 hfun⟩

set_option maxHeartbeats 4000000 in

theorem rnd_roundUpM (Tf : FormsTied D u) (hL : RUpLocM Tf) (hS : RndStab Tf) : Formalism.MainNotions.product_first_zeroth_parts.RoundUp D u := by
  intro i hi v c x hx
  obtain ⟨z, rfl⟩ := (Tf.lv i hi).pr_surj v c x
  obtain ⟨γ, η, κ, hsup, hrel, hl1, hl2, hfun, htr⟩ := Tf.up i hi v c z hx
  obtain ⟨e, he1, he2⟩ := hL i hi v c z hx γ η κ hsup hrel hl1 hl2 hfun
  have hg0 : ((D.fm u).fv i v c).comp e.toLinearMap ≠ 0 := by
    intro h0
    have h1 := LinearMap.congr_fun h0 ((D.fm u).te i v ((D.fm u).up i v c ((Tf.lv i hi).pr v c z)))
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, he1, hx, LinearMap.zero_apply] at h1
    exact one_ne_zero h1
  obtain ⟨γ', η', κ', hsup', hrel', hl1', hfun', htr'⟩ := Tf.dn i hi v _ _ hg0
  have hk := he2 γ' η' κ' hsup' hrel' hl1' hfun'
  have hcls : (D.fm u).dn i v ((D.fm u).up i v c ((Tf.lv i hi).pr v c z)) (((D.fm u).fv i v c).comp e.toLinearMap) = c := by
    apply (Tf.cls i hi).y_bij.1
    apply rnd_cls _ (γ.1 * γ'.1) ((UJ _ _).mul_mem γ.2 γ'.2) _ _ ⟨_, hk⟩
    rw [map_mul, mul_assoc, hrel', ← mul_assoc, ← mul_assoc, hrel]
    group
  refine ⟨e, he1, hcls, fun φ hφ => ?_⟩
  obtain ⟨g, hg, hgφ⟩ := forms_from_adelic_function Tf i hi φ hφ
  have hgA := (Submodule.mem_inf.1 hg).1
  rw [hgφ, htr' g hgA]
  obtain ⟨G, hG, hGv⟩ := rnd_fill (Tf.cls i hi).lev (embT D) (fun τ x => embedding_conj_compat D τ x)
    ((Tf.cls i hi).y ((D.fm u).up i v c ((Tf.lv i hi).pr v c z))) (hS i hi _)
    (g ((Tf.cls i hi).y ((D.fm u).up i v c ((Tf.lv i hi).pr v c z)) * η'))
  rw [← hGv, htr G hG, hgφ c]
  rw [hcls] at hrel'
  have hχ := rnd_chi (Tf.cls i hi).lev (Tf.atT.eV v).1 (level_places_not_bad Tf.atT v) η η' hsup hsup' κ κ' ⟨_, hk⟩ rfl
  rw [rnd_core (Tf.cls i hi).lev (embT D) (fun τ x => embedding_conj_compat D τ x) hgA hG _ _ η η' γ.1 γ'.1 γ.2 γ'.2
    κ κ' ⟨_, hk⟩ hrel hrel' rfl hχ hGv]

set_option maxHeartbeats 4000000 in

theorem rnd_roundDnM (Tf : FormsTied D u) (hL : RDnLocM Tf) (hS : RndStab Tf) : Formalism.MainNotions.product_first_zeroth_parts.RoundDn D u := by
  intro i hi v c g hg
  have hg0 : g ≠ 0 := by
    intro h0; rw [h0, LinearMap.zero_apply] at hg; exact zero_ne_one hg
  obtain ⟨γ', η', κ', hsup', hrel', hl1', hfun', htr'⟩ := Tf.dn i hi v c g hg0
  obtain ⟨e, he1, he2⟩ := hL i hi v c g hg γ' η' κ' hsup' hrel' hl1' hfun'
  obtain ⟨z, hz⟩ := (Tf.lv i hi).pr_surj v ((D.fm u).dn i v c g) (e.symm ((D.fm u).te i v c))
  have hfz : (D.fm u).fv i v ((D.fm u).dn i v c g) ((Tf.lv i hi).pr v _ z) = 1 := by
    rw [hz, he1, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, hg]
  obtain ⟨γ, η, κ, hsup, hrel, hl1, hl2, hfun, htr⟩ := Tf.up i hi v _ z hfz
  have hk := he2 z hz γ η κ hsup hrel hl1 hl2 hfun
  have hcls : (D.fm u).up i v ((D.fm u).dn i v c g) ((Tf.lv i hi).pr v _ z) = c := by
    apply (Tf.cls i hi).y_bij.1
    apply rnd_cls _ (γ'.1 * γ.1) ((UJ _ _).mul_mem γ'.2 γ.2) _ _ ⟨_, hk⟩
    rw [map_mul, mul_assoc, hrel, ← mul_assoc, ← mul_assoc, hrel']
    group
  refine ⟨e, he1, ?_, fun φ hφ => ?_⟩
  · rw [← hz]; exact hcls
  rw [← hz]
  obtain ⟨f0, hf0, hgφ⟩ := forms_from_adelic_function Tf i hi φ hφ
  have hgA := (Submodule.mem_inf.1 hf0).1
  rw [hgφ, htr f0 hgA]
  obtain ⟨G, hG, hGv⟩ := rnd_fill (Tf.cls i hi).lev (embT D) (fun τ x => embedding_conj_compat D τ x)
    ((Tf.cls i hi).y ((D.fm u).dn i v c g)) (hS i hi _)
    (f0 ((Tf.cls i hi).y ((D.fm u).dn i v c g) * η))
  rw [← hGv, htr' G hG, hgφ c]
  rw [hcls] at hrel
  have hχ := rnd_chi (Tf.cls i hi).lev (Tf.atT.eV v).1 (level_places_not_bad Tf.atT v) η' η hsup' hsup κ' κ ⟨_, hk⟩ rfl
  rw [rnd_core (Tf.cls i hi).lev (embT D) (fun τ x => embedding_conj_compat D τ x) hgA hG _ _ η' η γ'.1 γ.1 γ'.2 γ.2
    κ' κ ⟨_, hk⟩ hrel' hrel rfl hχ hGv]

def natTr (Tf : FormsTied D u) (i : ℕ) (hi : i ≤ D.R.m) (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi)) (κ : (Tf.cls i hi).lev.U)
    (h : (D.mem u).C.Y i → ℂ) : (D.mem u).C.Y i → ℂ :=
  fun s => (((Tf.cls i hi).lev.chi κ : ℂˣ) : ℂ)⁻¹ *
    h ((Tf.val i hi).eY.symm (frameTranslate (embT D) (fun τ x => embedding_conj_compat D τ x) γ.1⁻¹
      ((UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi)).inv_mem γ.2) ((Tf.val i hi).eY s)))

set_option maxHeartbeats 2000000 in

def UpNat (Tf : FormsTied D u) : Prop :=
  ∀ i (hi : i ≤ D.R.m) v c (z : ↥(Ld D u i hi c)), (D.fm u).fv i v c ((Tf.lv i hi).pr v c z) = 1 →
    ∃ (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi)) (η : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ : (Tf.cls i hi).lev.U),
      (∀ v', v' ≠ (Tf.atT.eV v).1 → bc (prV (E := D.host.E) v') η.1 = 1) ∧
        bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 *
          ((Tf.cls i hi).y ((D.fm u).up i v c ((Tf.lv i hi).pr v c z))).1 = ((Tf.cls i hi).y c).1 * η.1 * κ.1 ∧
        Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ.1.1 (clsCrd D u i hi ((D.fm u).up i v c ((Tf.lv i hi).pr v c z)))) =
          Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (Ld D u i hi c) ∧
        Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ.1.1 (Ld D u i hi ((D.fm u).up i v c ((Tf.lv i hi).pr v c z)))) =
          Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (Ld D u i hi c ⊔
            Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z.1}) ∧
        (∀ (x : ↥(Ld D u i hi ((D.fm u).up i v c ((Tf.lv i hi).pr v c z))))
          (hx : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ.1.1 *ᵥ x.1) ∈ Ld D u i hi c),
          (D.fm u).fv i v _ ((Tf.lv i hi).pr v _ x) = (D.fm u).fv i v c ((Tf.lv i hi).pr v c ⟨_, hx⟩)) ∧
      ∀ h, (D.fm u).upT i v c ((Tf.lv i hi).pr v c z) h = natTr Tf i hi γ κ h

set_option maxHeartbeats 2000000 in

def DnNat (Tf : FormsTied D u) : Prop :=
  ∀ i (hi : i ≤ D.R.m) v c (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c)), g ≠ 0 →
    ∃ (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi)) (η : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ : (Tf.cls i hi).lev.U),
      (∀ v', v' ≠ (Tf.atT.eV v).1 → bc (prV (E := D.host.E) v') η.1 = 1) ∧
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 *
        ((Tf.cls i hi).y ((D.fm u).dn i v c g)).1 = ((Tf.cls i hi).y c).1 * η.1 * κ.1 ∧
      Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (mulLat γ.1.1 (Ld D u i hi ((D.fm u).dn i v c g))) =
        Formalism.HermitianLatticesTheory.localization₂ (Tf.atT.Pv v) (clsCrd D u i hi c) ∧
      (∀ (x : ↥(Ld D u i hi ((D.fm u).dn i v c g))) (hx : γ.1.1 *ᵥ x.1 ∈ Lk Tf.atT i hi v c),
        (D.fm u).fv i v _ ((Tf.lv i hi).pr v _ x) = g ((Tf.lv i hi).prk v c ⟨_, hx⟩)) ∧
      ∀ h, (D.fm u).dnT i v c g h = natTr Tf i hi γ κ h

set_option maxHeartbeats 4000000 in

theorem rnd_natCore (Tf : FormsTied D u) (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT)
    {g : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) → Fr D i hi → ℂ} (hg : g ∈ AdFun (Tf.cls i hi).lev (embT D))
    (yc yu yd η η' : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (γ γ' : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi)) (κ κ' : (Tf.cls i hi).lev.U)
    (hsup : ∀ v', v' ≠ (Tf.atT.eV v).1 → bc (prV (E := D.host.E) v') η.1 = 1)
    (hsup' : ∀ v', v' ≠ (Tf.atT.eV v).1 → bc (prV (E := D.host.E) v') η'.1 = 1)
    (hU : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 * yu.1 = yc.1 * η.1 * κ.1)
    (hD : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ'.1 * yd.1 = yu.1 * η'.1 * κ'.1)
    (hk : η.1 * κ.1 * η'.1 * κ'.1 ∈ (Tf.cls i hi).lev.U) :
    natTr Tf i hi γ κ (natTr Tf i hi γ' κ' (fun s => g yd ((Tf.val i hi).eY s))) = fun s => g yc ((Tf.val i hi).eY s) := by
  have hχ := rnd_chi (Tf.cls i hi).lev (Tf.atT.eV v).1 (level_places_not_bad Tf.atT v) η η' hsup hsup' κ κ' ⟨_, hk⟩ rfl
  have e0 : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (γ.1 * γ'.1) * yd.1 = yc.1 * (⟨_, hk⟩ : (Tf.cls i hi).lev.U).1 := by
    rw [map_mul, mul_assoc, hD, ← mul_assoc, ← mul_assoc, hU]; simp only; group
  have e3 : yc.1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (γ.1 * γ'.1) * yd.1 * ((⟨_, hk⟩ : (Tf.cls i hi).lev.U)⁻¹ : (Tf.cls i hi).lev.U).1 := by
    rw [e0, InvMemClass.coe_inv]; group
  have hγγ : γ.1 * γ'.1 ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) := (UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi)).mul_mem γ.2 γ'.2
  funext s
  have a3 := adelic_value_translate (Tf.cls i hi).lev (embT D) (fun τ x => embedding_conj_compat D τ x) hg (γ.1 * γ'.1) hγγ yd yc
    (⟨_, hk⟩ : (Tf.cls i hi).lev.U)⁻¹ e3 ((Tf.val i hi).eY s)
  simp only [natTr, Equiv.apply_symm_apply]
  rw [a3, rnd_tr_tr,
    rnd_tr_congr (embT D) (fun τ x => embedding_conj_compat D τ x) (mul_inv_rev γ.1 γ'.1).symm _
      ((UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi)).inv_mem hγγ)]
  rw [map_inv, hχ]
  simp only [mul_inv, Units.val_mul, Units.val_inv_eq_inv_val]
  ring

set_option maxHeartbeats 4000000 in

theorem rnd_roundUpN (Tf : FormsTied D u) (hU : UpNat Tf) (hD : DnNat Tf) (hL : RUpLocM Tf) :
    Formalism.MainNotions.product_first_zeroth_parts.RoundUp D u := by
  intro i hi v c x hx
  obtain ⟨z, rfl⟩ := (Tf.lv i hi).pr_surj v c x
  obtain ⟨γ, η, κ, hsup, hrel, hl1, hl2, hfun, htr⟩ := hU i hi v c z hx
  obtain ⟨e, he1, he2⟩ := hL i hi v c z hx γ η κ hsup hrel hl1 hl2 hfun
  have hg0 : ((D.fm u).fv i v c).comp e.toLinearMap ≠ 0 := by
    intro h0
    have h1 := LinearMap.congr_fun h0 ((D.fm u).te i v ((D.fm u).up i v c ((Tf.lv i hi).pr v c z)))
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, he1, hx, LinearMap.zero_apply] at h1
    exact one_ne_zero h1
  obtain ⟨γ', η', κ', hsup', hrel', hl1', hfun', htr'⟩ := hD i hi v _ _ hg0
  have hk := he2 γ' η' κ' hsup' hrel' hl1' hfun'
  have hcls : (D.fm u).dn i v ((D.fm u).up i v c ((Tf.lv i hi).pr v c z)) (((D.fm u).fv i v c).comp e.toLinearMap) = c := by
    apply (Tf.cls i hi).y_bij.1
    apply rnd_cls _ (γ.1 * γ'.1) ((UJ _ _).mul_mem γ.2 γ'.2) _ _ ⟨_, hk⟩
    rw [map_mul, mul_assoc, hrel', ← mul_assoc, ← mul_assoc, hrel]
    group
  refine ⟨e, he1, hcls, fun φ hφ => ?_⟩
  obtain ⟨g, hg, hgφ⟩ := forms_from_adelic_function Tf i hi φ hφ
  have hgA := (Submodule.mem_inf.1 hg).1
  rw [htr', htr, hgφ, hgφ c]
  exact rnd_natCore Tf i hi v hgA _ _ _ η η' γ γ' κ κ' hsup hsup' hrel hrel' hk

set_option maxHeartbeats 4000000 in

theorem rnd_roundDnN (Tf : FormsTied D u) (hU : UpNat Tf) (hD : DnNat Tf) (hL : RDnLocM Tf) :
    Formalism.MainNotions.product_first_zeroth_parts.RoundDn D u := by
  intro i hi v c g hg
  have hg0 : g ≠ 0 := by
    intro h0; rw [h0, LinearMap.zero_apply] at hg; exact zero_ne_one hg
  obtain ⟨γ', η', κ', hsup', hrel', hl1', hfun', htr'⟩ := hD i hi v c g hg0
  obtain ⟨e, he1, he2⟩ := hL i hi v c g hg γ' η' κ' hsup' hrel' hl1' hfun'
  obtain ⟨z, hz⟩ := (Tf.lv i hi).pr_surj v ((D.fm u).dn i v c g) (e.symm ((D.fm u).te i v c))
  have hfz : (D.fm u).fv i v ((D.fm u).dn i v c g) ((Tf.lv i hi).pr v _ z) = 1 := by
    rw [hz, he1, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, hg]
  obtain ⟨γ, η, κ, hsup, hrel, hl1, hl2, hfun, htr⟩ := hU i hi v _ z hfz
  have hk := he2 z hz γ η κ hsup hrel hl1 hl2 hfun
  have hcls : (D.fm u).up i v ((D.fm u).dn i v c g) ((Tf.lv i hi).pr v _ z) = c := by
    apply (Tf.cls i hi).y_bij.1
    apply rnd_cls _ (γ'.1 * γ.1) ((UJ _ _).mul_mem γ'.2 γ.2) _ _ ⟨_, hk⟩
    rw [map_mul, mul_assoc, hrel, ← mul_assoc, ← mul_assoc, hrel']
    group
  refine ⟨e, he1, ?_, fun φ hφ => ?_⟩
  · rw [← hz]; exact hcls
  rw [← hz]
  obtain ⟨f0, hf0, hgφ⟩ := forms_from_adelic_function Tf i hi φ hφ
  have hgA := (Submodule.mem_inf.1 hf0).1
  rw [htr, htr', hgφ, hgφ c]
  exact rnd_natCore Tf i hi v hgA _ _ _ η' η γ' γ κ' κ hsup' hsup hrel' hrel hk

theorem rnd_linkAdmT_ofN
    (h : ∀ (D : D7) (u : D.what₂.Word) (Tf : FormsTied D u), ChiFin Tf →
      UpNat Tf ∧ DnNat Tf ∧ RUpLocM Tf ∧ RDnLocM Tf ∧ SplitAtT Tf.atT) :
    LinkAdmT := by
  apply admissible_of_split_and_round_trips
  · intro D u Tf hc; exact (h D u Tf hc).2.2.2.2
  · rintro D u ⟨Tf, hc⟩
    obtain ⟨h1, h2, h3, h4, _⟩ := h D u Tf hc
    exact ⟨rnd_roundUpN Tf h1 h2 h3, rnd_roundDnN Tf h1 h2 h4⟩

theorem natTr_adFun (Tf : FormsTied D u) (i : ℕ) (hi : i ≤ D.R.m)
    {g : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) → Fr D i hi → ℂ} (hg : g ∈ AdFun (Tf.cls i hi).lev (embT D))
    (yc yu η : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi)) (κ : (Tf.cls i hi).lev.U)
    (hU : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 * yu.1 = yc.1 * η.1 * κ.1) :
    natTr Tf i hi γ κ (fun s => g yu ((Tf.val i hi).eY s)) = fun s => g (yc * η) ((Tf.val i hi).eY s) := by
  funext s
  have e1 : (yc * η).1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 * yu.1 * (κ⁻¹ : (Tf.cls i hi).lev.U).1 := by
    simp only [Subgroup.coe_mul, hU, InvMemClass.coe_inv]; group
  have a1 := adelic_value_translate (Tf.cls i hi).lev (embT D) (fun τ x => embedding_conj_compat D τ x) hg γ.1 γ.2 yu (yc * η) κ⁻¹ e1
    ((Tf.val i hi).eY s)
  simp only [natTr, Equiv.apply_symm_apply]
  rw [a1, map_inv, Units.val_inv_eq_inv_val]

set_option maxHeartbeats 4000000 in

theorem upNat_upTie (Tf : FormsTied D u) (h : UpNat Tf) (i : ℕ) (hi : i ≤ D.R.m) :
    UpTie (Tf.lv i hi) (Tf.cls i hi) (Tf.val i hi) := by
  intro v c z hz
  obtain ⟨γ, η, κ, h1, h2, h3, h4, h5, h6⟩ := h i hi v c z hz
  exact ⟨γ, η, κ, h1, h2, h3, h4, h5, fun g hg => by rw [h6]; exact natTr_adFun Tf i hi hg _ _ η γ κ h2⟩

set_option maxHeartbeats 4000000 in

theorem dnNat_dnTie (Tf : FormsTied D u) (h : DnNat Tf) (i : ℕ) (hi : i ≤ D.R.m) :
    DnTie (Tf.lv i hi) (Tf.cls i hi) (Tf.val i hi) := by
  intro v c g hg0
  obtain ⟨γ, η, κ, h1, h2, h3, h4, h5⟩ := h i hi v c g hg0
  exact ⟨γ, η, κ, h1, h2, h3, h4, fun f hf => by rw [h5]; exact natTr_adFun Tf i hi hf _ _ η γ κ h2⟩

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
