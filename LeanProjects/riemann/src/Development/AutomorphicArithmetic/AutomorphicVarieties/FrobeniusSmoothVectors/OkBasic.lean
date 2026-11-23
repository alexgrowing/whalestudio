import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrobeniusSplitPrimeDatum
import ReciprocityTheory.GaloisValuations.ArithOfA

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V
open scoped Pointwise

private theorem padic_hom_ext {l : ℕ} [Fact l.Prime] {k : Type} [CommRing k] [CharP k l] (f g : ℤ_[l] →+* k) : f = g := by
  ext x
  have h := PadicInt.sub_zmodRepr_mem x
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at h
  obtain ⟨y, hy⟩ := h
  have e : x = y * l + (x.zmodRepr : ℤ_[l]) := by rw [hy]; ring
  rw [e]
  simp

private theorem cc_sq {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {c : G F Ω} {j : Ω →+* ℂ}
    (h : ∀ x, j (c x) = starRingEnd ℂ (j x)) : c * c = 1 := by
  refine AlgEquiv.ext fun x => j.injective ?_
  rw [AlgEquiv.mul_apply, h, h, starRingEnd_self_apply]
  rfl

private theorem eta_cc {Ω : Type} [Field Ω] [CharZero Ω] {η : G ℚ Ω →* ℤˣ} {D : ℕ} {δ : Ω} (hD : 0 < D)
    (hδ : δ ^ 2 = -(D : Ω)) (hη : ∀ s : G ℚ Ω, s δ = (η s : ℤ) • δ) {c : G ℚ Ω} {j : Ω →+* ℂ}
    (h : ∀ x, j (c x) = starRingEnd ℂ (j x)) : η c = -1 := by
  refine (Int.units_eq_one_or _).resolve_left fun h1 => ?_
  have h2 := h δ
  rw [hη, h1, Units.val_one, one_smul] at h2
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 h2.symm
  have h3 := congrArg j hδ
  rw [map_pow, map_neg, map_natCast, hr] at h3
  have h4 : r ^ 2 = -(D : ℝ) := by exact_mod_cast h3
  have h5 : (0 : ℝ) < D := by exact_mod_cast hD
  nlinarith [sq_nonneg r]

private theorem smul_over {Ω : Type} [Field Ω] [CharZero Ω] {l : ℕ} {B : ValuationSubring Ω} (γ : G ℚ Ω)
    (h : B.valuation (l : Ω) < 1) : (γ • B).valuation (l : Ω) < 1 := by
  rw [valuation_lt_one_iff'] at h ⊢
  simpa only [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, map_natCast, map_inv₀] using h

private theorem cpt_gal (F Ω : Type) [Field F] [CharZero F] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra F Ω] :
    CompactSpace (G F Ω) := by
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  haveI : IsGalois F Ω := IsGalois.tower_top_of_isGalois ℚ F Ω
  infer_instance

theorem UpperTheory.V.Fr.ok_basic :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [CharP (ResidueField O) l] (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* Oˣ) (σ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ) (Hb : Subgroup (G ℚ Ω)), Gen l η Ψ σ B M Hb → ∀ (m : ℕ) (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] (g₁ : G ℚ Ω) (Φ : Frame l (ResidueField O)), UFacts l η Ψ M m (upl Ω L) → Linked l η Ψ σ g₁ B M L Φ → barChar O Ψ g₁ ^ 2 ≠ 1 → IsOpen (Φ.del.ker : Set Φ.Γ) ∧ Φ.c * Φ.c = 1 ∧ Φ.del Φ.c = -1 ∧ (∀ v, Continuous (Φ.loc0 v)) ∧ Continuous Φ.eps ∧ IsOpen (Φ.Ψ.ker : Set Φ.Γ) ∧ Φ.Ψ Φ.c = 1 ∧ Φ.Ψ Φ.g0 ^ 2 ≠ 1 ∧ Fintype.card Φ.Inf = Φ.d ∧ (∀ w, Φ.cw w * Φ.cw w = 1) ∧ (∀ w, Φ.del (Φ.cw w) = -1) ∧ (∃ g : Φ.G0, Φ.om (ResidueField O) g ≠ 1) ∧ (∀ j : ℤ, j = 1 ∨ j = -1 → ∃ g : Φ.G0, Φ.om (ResidueField O) g * Φ.Ψ g ^ j ≠ 1) ∧ (∀ j : ℤ, j = 2 ∨ j = -2 → ∃ g, Φ.om (ResidueField O) g * Φ.Ψ g ^ j * Φ.delK (ResidueField O) g ≠ 1) ∧ (∀ v, ∃ g, Φ.Ψ (Φ.loc v g) ^ 2 ≠ 1) ∧ (¬ ∃ j : ℤ, ∀ g : Φ.G0, Φ.om (ResidueField O) g = Φ.Ψ g ^ j) ∧ (∀ v, ∀ g ∈ Φ.Nv v, Φ.Ψ (Φ.loc v g) = 1) ∧ (∀ v, l ^ m ≤ Φ.dv v) ∧ Nonempty Φ.V := by
  intro Ω _ _ _ l _ O _ _ _ η Ψ σ B M Hb hG m L _ _ _ _ g₁ Φ hU hL hg₁
  obtain ⟨k, S, π, ι, pl, e, c, F, hπ, -⟩ := hL
  haveI : CompactSpace (G (W.Lp L) Ω) := cpt_gal _ _
  have hq : Topology.IsQuotientMap π := F.g.cont.isClosedMap.isQuotientMap F.g.cont F.g.onto
  have hom : ∀ s, Φ.om (ResidueField O) (k.p s) = omO Ω l O s := fun s => by
    apply Units.ext
    show (ZMod.castHom (dvd_refl l) (ResidueField O)).comp PadicInt.toZMod (Φ.eps (k.p s) : ℤ_[l]ˣ) =
      (ZMod.castHom (dvd_pow_self l one_ne_zero) (ResidueField O)).comp (PadicInt.toZModPow 1) (cycZ ℚ Ω l s : ℤ_[l]ˣ)
    rw [k.eps, padic_hom_ext ((ZMod.castHom (dvd_refl l) (ResidueField O)).comp PadicInt.toZMod)]
  have hpl : ∀ v, (k.pl v).valuation (l : Ω) < 1 := fun v => by
    obtain ⟨γ, -, h⟩ := k.pl_conj v
    exact h ▸ smul_over γ hG.over_l
  have h0 : ∀ s (h : s ∈ upl Ω L ⊓ η.ker), k.p ⟨s, h.1⟩ ∈ Φ.del.ker := fun s h => (k.del _).trans h.2
  have f5 : ¬ ∃ j : ℤ, ∀ g : Φ.G0, Φ.om (ResidueField O) g = Φ.Ψ g ^ j := by
    rintro ⟨j, hj⟩
    refine hU.f5 ⟨j, fun s hs => ?_⟩
    have := hj ⟨_, h0 s hs⟩
    rwa [hom, k.psi] at this
  obtain ⟨hσ, hc⟩ := k.c
  obtain ⟨hg, hg0⟩ := k.g0
  obtain ⟨D, δ, hD, -, hδ, hη⟩ := hG.quad
  refine ⟨F.del_open, ?_, F.del_c, fun v => ?_, ?_, ?_, ?_, ?_, ?_, fun w => ?_, fun w => ?_, ?_, fun j hj => ?_,
    fun j hj => ?_, fun v => ?_, f5, fun v g hg => ?_, fun v => ?_, ?_⟩
  · obtain ⟨j, hj⟩ := hG.cc
    rw [← hc, ← map_mul, ← map_one k.p]
    exact congrArg k.p (Subtype.ext (cc_sq hj))
  · refine continuous_induced_rng.2 ?_
    have : Subtype.val ∘ Φ.loc0 v = k.p ∘ k.j v := funext (k.j_loc v)
    exact this ▸ k.p_cont.comp (k.j_cont v)
  · refine hq.continuous_iff.2 ?_
    have : Φ.eps ∘ π = cycZ (W.Lp L) Ω l := funext F.eps
    exact this ▸ continuous_cycZ _ _ l
  · exact hq.isOpen_preimage.1 (Subgroup.isOpen_mono (H₂ := Φ.Ψ.ker.comap π) F.K_Ψ F.g.isOpen)
  · rw [← hc, k.psi]
    exact hG.even
  · rw [← hg0, k.psi]
    exact hg₁
  · classical
    haveI := F.real
    rw [Fintype.card_congr e, Frame.d, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyReal.nrComplexPlaces_eq_zero, add_zero, ← IsTotallyReal.finrank,
      ← sum_locDegree l (Finset.univ.image pl) fun v => by
        rw [← F.loc.mem, Finset.mem_image]; exact ⟨fun ⟨a, _, h⟩ => ⟨a, h⟩, fun ⟨a, h⟩ => ⟨a, Finset.mem_univ _, h⟩⟩,
      Finset.sum_image fun a _ b _ h => F.loc.inj h]
    exact Finset.sum_congr rfl fun v _ => (F.dv v).symm
  · obtain ⟨j, hj, -⟩ := F.cc w
    rw [F.cw, ← map_mul, cc_sq hj, map_one]
  · obtain ⟨j, hj, -⟩ := F.cc w
    rw [F.cw, hπ _ fun x hx => (c w).commutes ⟨x, hx⟩, k.del]
    exact eta_cc hD hδ hη hj
  · by_contra h
    exact f5 ⟨0, fun g => by_contra fun h' => h ⟨g, by simpa using h'⟩⟩
  · obtain ⟨s, hs, h⟩ := hU.f2b j hj
    exact ⟨⟨_, h0 s hs⟩, by rwa [hom, k.psi]⟩
  · obtain ⟨s, hs, h⟩ := hU.f2c j hj
    refine ⟨k.p ⟨s, hs.1⟩, ?_⟩
    rwa [hom, k.psi, Frame.delK, MonoidHom.comp_apply, MonoidHom.mem_ker.1 (h0 s hs), map_one, mul_one]
  · obtain ⟨s, hs, h⟩ := hU.f3 _ (hpl v)
    obtain ⟨g, hg⟩ := (k.j_range v ⟨s, hs.2⟩).2 hs.1
    exact ⟨g, by rwa [k.j_loc, k.psi, hg]⟩
  · obtain ⟨j, hj⟩ := hG.Ψ_l
    have h1 : Φ.eps (Φ.loc v g) = 1 := hg.2
    have h2 : Φ.om (ResidueField O) (Φ.loc v g) = 1 := by rw [Frame.om, MonoidHom.comp_apply, h1, map_one]
    rw [k.j_loc, hom] at h2
    rw [k.j_loc, k.psi, hj _ (hpl v) _ ((k.j_ine v g).1 hg.1), h2, one_pow]
  · exact k.dv v ▸ hU.deg _ (hpl v)
  · exact ⟨(k.pl_all B hG.over_l).exists.choose⟩
