import Development.WeilBound.CoreStatements.VolumeEquality.RootBranches
import Development.WeilBound.CoreStatements.VolumeEquality.LocInjA
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BallAutomorphismInverseExists

noncomputable section

namespace SheetDecomposition

open NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

theorem InLevel.congr {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Tor.Level H} {D : Datum H}
    {γ : D.La ≃ₗ[𝓞 E] D.La} (h : InLevel l D γ) (v : D.La) : ∃ e, γ v = v + l.M • e := by
  obtain ⟨hf, h1, -⟩ := h
  have hM : (l.M : ℤ) ≠ 0 := by
    have := l.three_le
    omega
  have key : ∀ c ∈ l.Mb, ∃ e, γ (c • v) = c • v + l.M • e := fun c hc => by
    have hd : ∀ y, (l.M : ℤ) ∣ D.EF (γ (c • v) - c • v) y := fun y => by
      obtain ⟨e, he⟩ := h1 (H.bar c • γ.symm y)
        (Submodule.smul_mem_smul (Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hc) Submodule.mem_top)
      rw [map_smul, γ.apply_symm_apply] at he
      have e1 : D.EF (γ (c • v)) y = D.EF v (H.bar c • γ.symm y) := by
        rw [← D.adj, ← hf (c • v), γ.apply_symm_apply]
      rw [map_sub, LinearMap.sub_apply, e1, D.adj, he, map_add, map_nsmul]
      exact ⟨-D.EF v e, by simp⟩
    choose φ hφ using hd
    let ψ : D.La →ₗ[ℤ] ℤ := (AddMonoidHom.mk' φ fun y y' => by
      apply mul_left_cancel₀ hM
      rw [mul_add, ← hφ, ← hφ, ← hφ, map_add]).toIntLinearMap
    obtain ⟨e, he⟩ := D.unimod.2 ψ
    refine ⟨e, sub_eq_iff_eq_add'.1 (D.unimod.1 ?_)⟩
    ext y
    rw [hφ, map_nsmul, he]
    simp [ψ]
  have : (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := l.coprime ▸ Submodule.mem_top
  obtain ⟨c, hc, c', hc', e1⟩ := Submodule.mem_sup.1 this
  obtain ⟨e, he⟩ := key c hc
  obtain ⟨e', he'⟩ := h1 (c' • v) (Submodule.smul_mem_smul hc' Submodule.mem_top)
  have hv : v = c • v + c' • v := by rw [← add_smul, e1, one_smul]
  refine ⟨e + e', ?_⟩
  calc γ v = γ (c • v) + γ (c' • v) := by rw [← map_add, ← hv]
    _ = (c • v + c' • v) + l.M • (e + e') := by rw [he, he', smul_add]; abel
    _ = _ := by rw [← hv]

theorem locInj : LocInj := by
  intro E _ _ _ H l D Ψ _ j j' n g F Γ hF hΓ t₀ ht₀
  have hO : IsOpen (ballDom F.q) := BallInverse.isOpen_ballDom F.q
  let R : ↥(ballDom F.q) → RiemLat E g D.La := fun t => F.R t.1
  have hP : ∀ v, Continuous fun x => (R x).P v := fun v =>
    continuousOn_iff_continuous_restrict.1 (F.hol.2 v).continuousOn
  have hH : Continuous fun x => (R x).Hm :=
    HmCont.continuous_Hm E g D.La _ R F.form (fun x => F.form_eq _) hP
  have h := near_trivial R hP hH ⟨t₀, ht₀⟩ l.M l.three_le
  rw [nhds_prod_eq] at h
  obtain ⟨A, hA, hA'⟩ := (eventually_prod_self_iff (r := fun x y => ∀ γ : D.La ≃ₗ[𝓞 E] D.La,
    (∀ v, ∃ e, γ v = v + l.M • e) → (∀ u v, reForm (R y) (γ u) (γ v) = reForm (R x) u v) → γ = 1)).1 h
  refine ⟨Subtype.val '' interior A, hO.isOpenMap_subtype_val _ isOpen_interior,
    ⟨_, mem_interior_iff_mem_nhds.2 hA, rfl⟩, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ ⟨γ, hγ, he⟩
    have hl := hΓ γ hγ
    have hf : ∀ u v, (F.R y.1).form (γ u) (γ v) = (F.R x.1).form u v := fun u v => by
      rw [F.form_eq, F.form_eq]
      rcases hF with e | e
      · rw [e]
        exact hl.1 u v
      · rw [e]
        exact congrArg Neg.neg (hl.1 u v)
    obtain rfl := hA' x (interior_subset hx) y (interior_subset hy) γ hl.congr (reForm_eqv hf he)
    exact (F.univ (F.R y.1) (F.form_eq _) (F.sig _ y.2)).unique ⟨x.2, he⟩ ⟨y.2, LinearEquiv.refl _ _, fun _ => rfl⟩

end SheetDecomposition
