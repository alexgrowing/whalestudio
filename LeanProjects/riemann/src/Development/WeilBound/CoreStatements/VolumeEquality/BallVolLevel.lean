import Development.WeilBound.CoreStatements.VolumeEquality.BallVolDefs
import Development.WeilBound.CoreStatements.EqualVolumeCompactOpens.RmulScalOne
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsLatticeEmbedding

noncomputable section

namespace SheetDecomposition

open NumberField Matrix ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CompanionTheory.Ar.Cmp PositivityTheory.EqVol
open scoped nonZeroDivisors

section

variable {E : Type} [Field E] [NumberField E] {N : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]
  {e : Λ →ₗ[𝓞 E] (Fin N → E)}

theorem lat_multiple (hL : IsLat (LinearMap.range e)) (v : Fin N → E) : ∃ (s : (𝓞 E)⁰) (x : Λ), s • v = e x := by
  obtain ⟨s, hs⟩ := multiple_mem_span_of_mem_localization_span (𝓞 E)⁰ E
    (LinearMap.range e : Set (Fin N → E)) v (hL.2 ▸ Submodule.mem_top)
  rw [Submodule.span_eq] at hs
  obtain ⟨x, hx⟩ := hs
  exact ⟨s, x, hx.symm⟩

theorem lat_extend (hi : Function.Injective e) (hL : IsLat (LinearMap.range e)) (f : Λ →ₗ[𝓞 E] (Fin N → E)) :
    ∃ g : (Fin N → E) →ₗ[E] (Fin N → E), ∀ x, g (e x) = f x := by
  have hu : ∀ s : (𝓞 E)⁰, IsUnit (algebraMap (𝓞 E) (Module.End (𝓞 E) (Fin N → E)) s) := by
    have := isLocalizedModule_id (𝓞 E)⁰ (Fin N → E) E
    exact IsLocalizedModule.map_units (LinearMap.id : (Fin N → E) →ₗ[𝓞 E] (Fin N → E))
  have : IsLocalizedModule (𝓞 E)⁰ e :=
    { map_units := hu
      surj := fun v => by
        obtain ⟨s, x, h⟩ := lat_multiple hL v
        exact ⟨(x, s), h⟩
      exists_of_eq := fun h => ⟨1, by rw [hi h]⟩ }
  exact ⟨(IsLocalizedModule.lift (𝓞 E)⁰ e f hu).extendScalarsOfIsLocalization (𝓞 E)⁰ E,
    fun x => IsLocalizedModule.lift_apply (𝓞 E)⁰ e f hu x⟩

theorem lat_matrix (hi : Function.Injective e) (hL : IsLat (LinearMap.range e)) (δ : Λ ≃ₗ[𝓞 E] Λ) :
    ∃ γ : GL (Fin N) E, ∀ x, e (δ x) = (γ : Matrix (Fin N) (Fin N) E) *ᵥ e x := by
  obtain ⟨g, hg⟩ := lat_extend hi hL (e ∘ₗ δ.toLinearMap)
  obtain ⟨g', hg'⟩ := lat_extend hi hL (e ∘ₗ δ.symm.toLinearMap)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hg hg'
  have h1 : g ∘ₗ g' = LinearMap.id := LinearMap.ext_on hL.2 (by
    rintro _ ⟨x, rfl⟩
    simp [hg, hg'])
  have h2 : g' ∘ₗ g = LinearMap.id := LinearMap.ext_on hL.2 (by
    rintro _ ⟨x, rfl⟩
    simp [hg, hg'])
  refine ⟨⟨LinearMap.toMatrix' g, LinearMap.toMatrix' g', ?_, ?_⟩, fun x => ?_⟩
  · rw [← LinearMap.toMatrix'_comp, h1, LinearMap.toMatrix'_id]
  · rw [← LinearMap.toMatrix'_comp, h2, LinearMap.toMatrix'_id]
  · show _ = LinearMap.toMatrix' g *ᵥ e x
    rw [LinearMap.toMatrix'_mulVec, hg]

omit [NumberField E] in
theorem mem_smul_range (hi : Function.Injective e) (I : Ideal (𝓞 E)) (x : Λ) :
    e x ∈ I • LinearMap.range e ↔ x ∈ I • (⊤ : Submodule (𝓞 E) Λ) := by
  rw [← Submodule.map_top, ← Submodule.map_smul'']
  exact ⟨fun ⟨y, hy, h⟩ => hi h ▸ hy, fun h => ⟨x, h, rfl⟩⟩

omit [NumberField E] in
theorem congr_iff (hi : Function.Injective e) {δ : Λ ≃ₗ[𝓞 E] Λ} {γ : Matrix (Fin N) (Fin N) E}
    (h : ∀ x, e (δ x) = γ *ᵥ e x) (M : ℕ) (x : Λ) :
    (∃ y ∈ LinearMap.range e, γ *ᵥ e x = e x + M • y) ↔ ∃ y, δ x = x + M • y := by
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, hy⟩
    exact ⟨y, hi (by rw [h, hy, map_add, map_nsmul])⟩
  · rintro ⟨y, hy⟩
    exact ⟨e y, ⟨y, rfl⟩, by rw [← h, hy, map_add, map_nsmul]⟩

variable [IsCMField E]

theorem herm_smul_smul (G : Matrix (Fin N) (Fin N) E) (a b : E) (x y : Fin N → E) :
    herm G (a • x) (b • y) = a * cc b * herm G x y := by
  simp only [herm, cc, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

theorem eq_of_herm_lat (hL : IsLat (LinearMap.range e)) {G G' : Matrix (Fin N) (Fin N) E}
    (h : ∀ x y, herm G (e x) (e y) = herm G' (e x) (e y)) : G = G' := by
  have h1 : ∀ u v, herm G u v = herm G' u v := fun u v => by
    obtain ⟨s, x, hx⟩ := lat_multiple hL u
    obtain ⟨t, y, hy⟩ := lat_multiple hL v
    have hs : ((s : 𝓞 E) : E) ≠ 0 := by exact_mod_cast nonZeroDivisors.coe_ne_zero s
    have ht : ((t : 𝓞 E) : E) ≠ 0 := by exact_mod_cast nonZeroDivisors.coe_ne_zero t
    have ht' : cc ((t : 𝓞 E) : E) ≠ 0 := (map_ne_zero (IsCMField.complexConj E)).2 ht
    have e1 : e x = ((s : 𝓞 E) : E) • u := hx.symm
    have e2 : e y = ((t : 𝓞 E) : E) • v := hy.symm
    have := h x y
    rw [e1, e2, herm_smul_smul, herm_smul_smul] at this
    exact mul_left_cancel₀ (mul_ne_zero hs ht') this
  ext c d
  have e0 : ∀ G : Matrix (Fin N) (Fin N) E, herm G (Pi.single c 1) (Pi.single d 1) = G c d := fun G => by
    simp [herm, cc, Pi.single_apply, apply_ite (IsCMField.complexConj E)]
  rw [← e0 G, ← e0 G', h1]

theorem herm_eq_of_trace {ξ : E} (hξ : ξ ≠ 0) {G G' : Matrix (Fin N) (Fin N) E}
    (h : ∀ x y, EFf ξ G (e x) (e y) = EFf ξ G' (e x) (e y)) (x y : Λ) : herm G (e x) (e y) = herm G' (e x) (e y) := by
  have h0 : -ξ * (herm G (e x) (e y) - herm G' (e x) (e y)) = 0 := by
    refine GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatEmbEx.trace_zero_of_int _ fun a => ?_
    have h1 := h (a • x) y
    have e1 : e (a • x) = (a : E) • e x := by rw [map_smul]; rfl
    have e2 : ∀ G : Matrix (Fin N) (Fin N) E, herm G ((a : E) • e x) (e y) = a * herm G (e x) (e y) := fun G => by
      have := herm_smul_smul G (a : E) 1 (e x) (e y)
      rwa [one_smul, cc, map_one, mul_one] at this
    rw [EFf, EFf, e1, e2, e2, ← sub_eq_zero, ← map_sub] at h1
    rw [← h1]
    congr 1
    ring
  exact sub_eq_zero.1 ((mul_eq_zero.1 h0).resolve_left (neg_ne_zero.2 hξ))

end

theorem levelDict : LevelDict := by
  intro E _ _ _ H l D N G e ξ form hF hi hL hξ hf
  have hbij : Function.Bijective form := by
    rcases hF with rfl | rfl
    · exact D.unimod
    · exact neg_involutive.bijective.comp D.unimod
  have hpres : ∀ δ : D.La ≃ₗ[𝓞 E] D.La,
      (∀ a b, D.EF (δ a) (δ b) = D.EF a b) ↔ ∀ a b, form (δ a) (δ b) = form a b := fun δ => by
    rcases hF with rfl | rfl
    · rfl
    · simp
  have hM : 0 < l.M := by have := l.three_le; omega
  have hcong : ∀ (δ : D.La ≃ₗ[𝓞 E] D.La) (γ : Matrix (Fin N) (Fin N) E), (∀ x, e (δ x) = γ *ᵥ e x) →
      (((∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∃ y, δ a = a + l.M • y) ∧
        ∀ a, ∃ y, δ a = a + l.A • y) ↔
        ∀ x ∈ LinearMap.range e, γ *ᵥ x - x ∈ levIdeal l • LinearMap.range e) := fun δ γ h => by
    refine Iff.trans ?_ (levelIdeal E N (LinearMap.range e) _ l.Mb l.M l.A γ hL hM l.prod (by
      rintro _ ⟨x, rfl⟩
      exact ⟨δ x, h x⟩))
    refine and_congr ⟨fun h1 x hx => ?_, fun h1 a ha => ?_⟩ ⟨?_, fun h1 a => ?_⟩
    · obtain ⟨a, rfl⟩ := Submodule.smul_le_right hx
      exact (congr_iff hi h _ _).2 (h1 a ((mem_smul_range hi _ _).1 hx))
    · exact (congr_iff hi h _ _).1 (h1 _ ((mem_smul_range hi _ _).2 ha))
    · rintro h1 _ ⟨a, rfl⟩
      exact (congr_iff hi h _ _).2 (h1 a)
    · exact (congr_iff hi h _ _).1 (h1 _ ⟨a, rfl⟩)
  refine ⟨⟨?_, fun φ => ?_⟩, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    exact ⟨form x y, (hf x y).symm⟩
  · obtain ⟨x, hx⟩ := hbij.2 (φ.comp e.rangeRestrict.toAddMonoidHom).toIntLinearMap
    refine ⟨e x, ⟨x, rfl⟩, ?_⟩
    rintro ⟨_, y, rfl⟩
    rw [← hf, hx]
    rfl
  · rintro γ ⟨hu, hs, hc⟩
    let φ := LinearEquiv.ofInjective e hi
    let γ₀ : (Fin N → E) ≃ₗ[𝓞 E] (Fin N → E) :=
      (Matrix.GeneralLinearGroup.toLin γ).toLinearEquiv.restrictScalars (𝓞 E)
    have hγ₀ : ∀ v, γ₀ v = (γ : Matrix (Fin N) (Fin N) E) *ᵥ v := fun _ => rfl
    have hm : (LinearMap.range e).map γ₀.toLinearMap = LinearMap.range e := by
      ext v
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact (hs u).1 hu
      · intro hv
        refine ⟨γ₀.symm v, (hs _).2 ?_, γ₀.apply_symm_apply v⟩
        rw [← hγ₀, γ₀.apply_symm_apply]
        exact hv
    let δ : D.La ≃ₗ[𝓞 E] D.La := φ.trans ((γ₀.ofSubmodules _ _ hm).trans φ.symm)
    have hδ : ∀ x, e (δ x) = (γ : Matrix (Fin N) (Fin N) E) *ᵥ e x := fun x =>
      congrArg Subtype.val (φ.apply_symm_apply ((γ₀.ofSubmodules _ _ hm) (φ x)))
    refine ⟨δ, ⟨(hpres δ).2 fun a b => ?_, (hcong δ _ hδ).2 hc⟩, hδ⟩
    have : ((form (δ a) (δ b) : ℤ) : ℚ) = form a b := by
      rw [hf, hf, hδ, hδ, EFf, EFf, herm_mulVec', show _ * G * _ = G from hu]
    exact_mod_cast this
  · rintro δ ⟨h1, h2⟩
    obtain ⟨γ, hγ⟩ := lat_matrix hi hL δ
    refine ⟨γ, ⟨?_, fun v => ⟨?_, fun hv => ?_⟩, (hcong δ _ hγ).1 h2⟩, hγ⟩
    · refine eq_of_herm_lat hL (herm_eq_of_trace hξ fun x y => ?_)
      rw [EFf, ← herm_mulVec', ← hγ, ← hγ, ← EFf, ← hf, ← hf, (hpres δ).1 h1]
    · rintro ⟨x, rfl⟩
      exact ⟨δ x, hγ x⟩
    · obtain ⟨y, hy⟩ := hv
      refine ⟨δ.symm y, ?_⟩
      have h3 := hγ (δ.symm y)
      rw [δ.apply_symm_apply, hy] at h3
      have h4 := congrArg (fun u => ((γ⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ u) h3
      simpa only [mulVec_mulVec, Units.inv_mul, one_mulVec] using h4.symm

end SheetDecomposition
