import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.BcStmt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIsoSymm

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands UpperTheory.V UpperTheory.V.Af

theorem UpperTheory.V.Br.wdAway :
    UpperTheory.V.Br.WdAway := by
  intro F K Ω _ _ _ _ _ _ _ _ _ _ _ l _ ι A v w h h' i hP hl hl' n r x y hx hy
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  obtain ⟨c, hc, hdegc, hq, hsm⟩ := GlobalTheory.T.place_over_transport_ring_iso F Ω A v h K Ω A w h' _ _ i hP
  have hd1 : ∀ σ, deg (c.symm σ) = deg σ := fun σ => by
    rw [← hdegc, MulEquiv.apply_symm_apply]
  have hs1 : ∀ (M : Type) [Monoid M] (g : Weil h →* M), IsSmooth g →
      IsSmooth (g.comp c.symm.toMonoidHom) := fun M _ g hg => by
    have e : (g.comp c.symm.toMonoidHom).comp c.toMonoidHom = g := by ext σ; simp
    have hg' : IsSmooth ((g.comp c.symm.toMonoidHom).comp c.toMonoidHom) := by rwa [e]
    exact (hsm M _).mpr hg'
  have key : ∀ σ : Weil h', ((c.symm σ : Weil h) : G F Ω) = Bc.res F Ω K (σ : G K Ω) := fun σ =>
    AlgEquiv.ext fun z => (hc (c.symm σ) σ).mpr (c.apply_symm_apply σ) z
  have hres : Continuous (Bc.res F Ω K : G K Ω →* G F Ω) := by
    refine continuous_of_continuousAt_one _ ?_
    rw [ContinuousAt, map_one]
    intro U' hU'
    obtain ⟨U, hU, hU1, H⟩ := GlobalTheory.WeilTransport.conj_nhds K Ω F Ω (RingEquiv.refl Ω) U' hU'
    exact Filter.mem_map.mpr (Filter.mem_of_superset (hU.mem_nhds hU1) fun σ hσ => H σ hσ _ fun z => rfl)
  have hmem : ∀ σ : Ine (F := K) A, Bc.res F Ω K (σ : G K Ω) ∈ Ine (F := F) A := fun σ => by
    have h1 : ((c.symm (ineIncl h' σ) : Weil h) : G F Ω) ∈ Ine (F := F) A := by
      rw [← deg_eq_zero_iff, hd1, deg_ineIncl]
    rwa [key] at h1
  let d : Ine (F := K) A →* Ine (F := F) A :=
    ((Bc.res F Ω K).comp (Ine (F := K) A).subtype).codRestrict _ hmem
  have hdc : Continuous d := (hres.comp continuous_subtype_val).subtype_mk _
  have hds : Function.Surjective d := fun τ => by
    have h1 : ((c (ineIncl h τ) : Weil h') : G K Ω) ∈ Ine (F := K) A := by
      rw [← deg_eq_zero_iff, hdegc, deg_ineIncl]
    refine ⟨⟨_, h1⟩, Subtype.ext ?_⟩
    have h2 := key (c (ineIncl h τ))
    rw [MulEquiv.symm_apply_apply] at h2
    exact h2.symm
  obtain ⟨t, ht, φ, hφ, N, a, hN, ha, rfl⟩ := hx
  have hφ' : deg (c φ) = 1 := by rw [hdegc, hφ]
  have hine : ∀ g : Weil h', d (inePart hφ' g) = inePart hφ (c.symm g) := fun g => by
    refine Subtype.ext ?_
    have h2 := key (((c φ) ^ deg g)⁻¹ * g)
    rw [map_mul, map_inv, map_zpow, MulEquiv.symm_apply_apply, ← hd1] at h2
    refine Eq.trans ?_ h2.symm
    rw [hd1]; rfl
  have hmat : ∀ g : Weil h', wdMat (t.comp d) hφ' (r.comp (Bc.res F Ω K)) N g =
      wdMat t hφ r N (c.symm g) := fun g => by
    rw [wdMat, wdMat, key, ← hine]; rfl
  let b := GlobalTheory.WDTransport.pull c.symm.toMonoidHom hd1 hq.symm hs1 a
  have hb : IsWDOf ι (r.comp (Bc.res F Ω K)) (WD.mk b) := by
    refine ⟨t.comp d, ⟨ht.1.comp hdc, ht.2.comp hds⟩, c φ, hφ', N, b, ?_, ?_, rfl⟩
    · obtain ⟨h1, U, hU, H⟩ := hN
      exact ⟨h1, U.comap d, hU.preimage hdc, fun σ hσ => H (d σ) hσ⟩
    · refine ⟨ha.1, fun σ => ?_⟩
      simp only [hmat]
      exact ha.2 (c.symm σ)
  rw [hy.unique hl' hb]
  refine ⟨n, a, b, rfl, rfl, rfl, fun σ σ' hσ => ?_⟩
  rw [← (hc σ σ').mp hσ]
  exact congrArg a.ρ (c.symm_apply_apply σ).symm
