import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.RhoUpperBoundSmallDepth

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.LatticeSystems

def mapE {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] {k : ℕ} (g : GL (Fin k) Qq) (e : Edge W Qq k) :
    Edge W Qq k := ⟨e.src.map (nt_phi W g), e.tgt.map (nt_phi W g)⟩

theorem mapE_inv {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] {k : ℕ} (g : GL (Fin k) Qq)
    (e : Edge W Qq k) : mapE g (mapE g⁻¹ e) = e := by
  have hid : (nt_phi W g).comp (nt_phi W g⁻¹) = LinearMap.id := LinearMap.ext fun x => by
    simp only [LinearMap.comp_apply, nt_phi, LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply,
      Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, LinearMap.id_apply]
  cases e with
  | mk src tgt =>
    simp only [mapE, Edge.mk.injEq]
    constructor <;> rw [← Submodule.map_comp, hid, Submodule.map_id]

def RestFunct : Prop :=
  ∀ (p n' : ℕ) (R : RS p n') (m : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ), IsDominant lam0 →
    ∀ g : GL (Fin (m + 1)) R.Qq, ∃ T : Vsp R.Kf lam0 ≃ₗ[R.Kf] Vsp R.Kf lam0,
      (∀ L : Submodule R.W (Fin (m + 1) → R.Qq), IsLattice R.W L →
        ∀ x, x ∈ HL (O := R.O) R.ι R.σ lam0 L ↔ T x ∈ HL (O := R.O) R.ι R.σ lam0 (L.map (nt_phi R.W g))) ∧
      (∀ e : Edge R.W R.Qq (m + 1), IsEdge p n' 1 e →
        ∀ x, x ∈ HLe p R.ι R.σ R.w lam0 e ↔ T x ∈ HLe p R.ι R.σ R.w lam0 (mapE g e))

section Formal

variable {O Kf V : Type*} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup V] [Module Kf V] [Module O V]
  [IsScalarTower O Kf V]

theorem scale_alt (T : V ≃ₗ[Kf] V) (c : Kf) {M M' : Submodule O V} (h : ∀ x, x ∈ M ↔ T x ∈ M') {x : V}
    (hx : x ∈ scale c M) : T x ∈ scale c M' := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨T y, (h y).1 hy, by simp⟩

theorem comp_symm_mem_dualLat_of_mem_iff (T : V ≃ₗ[Kf] V) {M M' : Submodule O V} (h : ∀ x, x ∈ M ↔ T x ∈ M') {φ : Module.Dual Kf V}
    (hφ : φ ∈ Formalism.GradedWeylDivisibility.dualLat O Kf M) : φ.comp T.symm.toLinearMap ∈ Formalism.GradedWeylDivisibility.dualLat O Kf M' := by
  intro v hv
  exact hφ (T.symm v) ((h _).2 (by rwa [LinearEquiv.apply_symm_apply]))

theorem comp_symm_mem_scale_dualLat_of_mem_iff (T : V ≃ₗ[Kf] V) (c : Kf) {M M' : Submodule O V} (h : ∀ x, x ∈ M ↔ T x ∈ M')
    {φ : Module.Dual Kf V} (hφ : φ ∈ scale c (Formalism.GradedWeylDivisibility.dualLat O Kf M)) :
    φ.comp T.symm.toLinearMap ∈ scale c (Formalism.GradedWeylDivisibility.dualLat O Kf M') := by
  obtain ⟨ψ, hψ, rfl⟩ := hφ
  exact ⟨ψ.comp T.symm.toLinearMap, comp_symm_mem_dualLat_of_mem_iff T h hψ, by ext v; simp⟩

theorem apply_mem_scale_scale_of_mem_iff (T : V ≃ₗ[Kf] V) (c d : Kf) {M M' : Submodule O V} (h : ∀ x, x ∈ M ↔ T x ∈ M') {x : V}
    (hx : x ∈ scale c (scale d M)) : T x ∈ scale c (scale d M') := by
  have hs : ∀ y, y ∈ M' ↔ T.symm y ∈ M := fun y => by rw [h (T.symm y), LinearEquiv.apply_symm_apply]
  have hiff : ∀ y, y ∈ scale d M ↔ T y ∈ scale d M' := fun y =>
    ⟨fun hy => scale_alt T d h hy, fun hy => by
      have := scale_alt T.symm d hs hy
      rwa [LinearEquiv.symm_apply_apply] at this⟩
  exact scale_alt T c hiff hx

theorem scaled_dual_lattice_transport (T : V ≃ₗ[Kf] V) (c d : Kf) {M M' : Submodule O V} (h : ∀ x, x ∈ M ↔ T x ∈ M')
    {φ : Module.Dual Kf V} (hφ : φ ∈ scale c (scale d (Formalism.GradedWeylDivisibility.dualLat O Kf M))) :
    φ.comp T.symm.toLinearMap ∈ scale c (scale d (Formalism.GradedWeylDivisibility.dualLat O Kf M')) := by
  obtain ⟨ψ, hψ, rfl⟩ := hφ
  exact ⟨ψ.comp T.symm.toLinearMap, comp_symm_mem_scale_dualLat_of_mem_iff T d h hψ, by ext v; simp⟩

end Formal

theorem restEdge_of (hFun : RestFunct) : RestEdge := by
  classical
  intro p n' R m lam0 hDom t c n D e e' he he' hfac
  have hfrW : IsFractionRing R.W R.Qq := R.std.1.frac_alt
  obtain ⟨g, hg, hsrc, htgt⟩ := lc_main p n' 1 (m + 1) R.std.1.p_unif R.std.1.res_card R.std.1.prime.two_le
    (by have := R.std.1.two_le; omega) e he
  obtain ⟨g', hg', hsrc', htgt'⟩ := lc_main p n' 1 (m + 1) R.std.1.p_unif R.std.1.res_card R.std.1.prime.two_le
    (by have := R.std.1.two_le; omega) e' he'
  have hug : IsUnit g := (Matrix.isUnit_iff_isUnit_det _).2 hg
  have hug' : IsUnit g' := (Matrix.isUnit_iff_isUnit_det _).2 hg'
  let γ : GL (Fin (m + 1)) R.Qq := hug'.unit * hug.unit⁻¹
  have hγg : (γ : Matrix (Fin (m + 1)) (Fin (m + 1)) R.Qq) * g = g' := by
    have : γ * hug.unit = hug'.unit := by simp [γ]
    have h2 := congrArg Units.val this
    simpa using h2
  have hee : e' = mapE γ e := by
    cases e with
    | mk s tg =>
      cases e' with
      | mk s' tg' =>
        simp only at hsrc htgt hsrc' htgt'
        simp only [mapE]
        rw [hsrc, htgt, hsrc', htgt', map_colSpan, map_colSpan, ← Matrix.mul_assoc, hγg]
  obtain ⟨T, hT1, hT2⟩ := hFun p n' R m lam0 hDom γ
  have hedge : ∀ e'' : Edge R.W R.Qq (m + 1), IsEdge p n' 1 e'' → IsEdge p n' 1 (mapE γ⁻¹ e'') :=
    fun e'' h => nt_edge_map p n' 1 γ⁻¹ _ _ h
  have hsrcC : ∀ x, x ∈ CCL R lam0 t c e → T x ∈ CCL R lam0 t c (mapE γ e) := by
    intro x hx
    refine Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
    · exact scale_alt T _ (hT1 e.src he.1) hx.1.1
    · exact scale_alt T _ (hT2 e he) hx.1.2
    · rw [Submodule.mem_iInf]
      intro e''
      rw [Submodule.mem_iInf]
      rintro ⟨h1, h2, h3⟩
      have h4 : (mapE γ⁻¹ e'').src = e.src := by
        show e''.src.map (nt_phi R.W γ⁻¹) = e.src
        rw [h2]
        exact nt_map_inv γ e.src
      have h5 : mapE γ⁻¹ e'' ≠ e := by
        intro h
        apply h3
        rw [← h, mapE_inv]
      have h6 := CCL_other R lam0 t c e (mapE γ⁻¹ e'') (hedge e'' h1) h4 h5 hx
      have h7 := apply_mem_scale_scale_of_mem_iff T _ _ (hT2 (mapE γ⁻¹ e'') (hedge e'' h1)) h6
      rwa [mapE_inv] at h7
  have htgtC : ∀ y, y ∈ CCL' R lam0 t c e → y.comp T.symm.toLinearMap ∈ CCL' R lam0 t c (mapE γ e) := by
    intro y hy
    refine Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
    · exact comp_symm_mem_scale_dualLat_of_mem_iff T _ (hT1 e.tgt he.2.1) hy.1.1
    · exact comp_symm_mem_scale_dualLat_of_mem_iff T _ (hT2 e he) hy.1.2
    · rw [Submodule.mem_iInf]
      intro e''
      rw [Submodule.mem_iInf]
      rintro ⟨h1, h2, h3⟩
      have h4 : (mapE γ⁻¹ e'').tgt = e.tgt := by
        show e''.tgt.map (nt_phi R.W γ⁻¹) = e.tgt
        rw [h2]
        exact nt_map_inv γ e.tgt
      have h5 : mapE γ⁻¹ e'' ≠ e := by
        intro h
        apply h3
        rw [← h, mapE_inv]
      have h6 := CCL'_other R lam0 t c e (mapE γ⁻¹ e'') (hedge e'' h1) h4 h5 hy
      have h7 := scaled_dual_lattice_transport T _ _ (hT2 (mapE γ⁻¹ e'') (hedge e'' h1)) h6
      rwa [mapE_inv] at h7
  rw [hee]
  rcases hfac with h0 | ⟨x, y, hx, hy, z, M, hz, hv, hM⟩
  · exact Or.inl h0
  · refine Or.inr ⟨fun i => T (x i), fun l => (y l).comp T.symm.toLinearMap, fun i => hsrcC _ (hx i),
      fun l => htgtC _ (hy l), z, M, hz, hv, fun i j => ?_⟩
    rw [← hM i j]
    refine Finset.sum_congr rfl fun l _ => ?_
    congr 1
    unfold be
    rw [LinearMap.comp_apply, ← map_smul]
    simp

end Formalism.MainNotions.flipOneThree.Pf

end
