import Development.WeilBound.CoreStatements.FlagImmersions.SpecMapFactorisation
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CptFlatInputsOfPropZ
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFlatHermHodgeCptConst
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PropZProvedStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateFreeCmTypeWeightStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSandwichOfHodgeTateFreeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointExistsUniqueEmbeddingStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl

namespace RootFieldNumerics.RF

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

theorem tauIn_injective {l : Level H} (c : Coeff l) (τ : E →+* ℂ) : Function.Injective (tauIn c τ) := by
  intro a b hab
  have h : τ (a : E) = τ (b : E) := by
    have := congrArg (fun x : c.F => (x : ℂ)) hab
    simpa [tauIn] using this
  exact RingOfIntegers.ext (τ.injective h)

set_option maxHeartbeats 1600000 in
theorem core (hSm : SmoothLine) (hLc : LocalCmp) (hNu : Numerics) (hF : HT.FarguesHodgeTate) {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} [NumberField c.F] {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {U : Set (Xo.XF c)}
    (Z : CptOver Y U) (φ : FrameFn Xo c) (τ : CMType H) (N : LogNorms c.F) {S : Finset ℕ} {Ω : Type} [Field Ω]
    {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y)
    (Fl : 𝔐.Flag) (xdeg : CMType H × Fin (D.p + D.q) → K → ℤ) (e : CMType H × Fin (D.p + D.q) → Ω)
    (hx : CMType H × Fin (D.p + D.q) → HermLine J) (n : ℕ) (hflat : FlatOnModel Z τ.1 φ)
    (hinf : ∀ s, HasInfNorm U τ.1 φ s (N.inf s)) (hconj : ∀ s, N.inf (ComplexEmbedding.conjugate s) = N.inf s)
    (hfin : ∀ p κ, HasFinNorm U τ.1 φ p κ (N.fin p κ)) (had : N.IsAdelic)
    (hNdeg : N.deg = ((D.p : ℝ) - D.q) / 2 *
      (Real.eulerMascheroniConstant + Real.log (2 * Real.pi) - Real.log (hostRd E) - hostLval H))
    (hgp : genPt 𝔐.ξ₀ = genPt (Z.ξ₀ ≫ Y.j)) (hbir : Birational y) (hvar : IsArithVar (mCoordIdeal y) n)
    (hroot : Fl.RootLines xdeg e) (hhod : ∀ r, Fl.IsHodgeLine r (e r) (hx r)) (hxa : ∀ r, (hx r).a = xdeg r)
    (h2S : 2 ∈ S) (hdS : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S) (hfree : ∀ p ∈ S, HT.HTFree 𝔐 p)
    (hpq : 0 < D.p + D.q)
    (hnum : ∀ p : ℕ, p.Prime → p ∉ S → ∀ (a : ⋀[Ω]^D.p 𝔐.Li) (b : ⋀[Ω]^D.q 𝔐.Li), a ≠ 0 → b ≠ 0 →
      (∃ x f, IsCoeffAt (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) D.p D.q a b x f) →
      NumTrivMod (lineLat (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) D.p D.q a b) (p : Ω)) :
    ∃ (F' : Type) (_ : Field F') (_ : NumberField F') (ψ : F' →+* Ω) (A : HermLine J) (Sf : FlatHerm y ψ A),
      OverInt y ψ ∧ IsSmoothHerm A ∧ A.a = ∑ i, xdeg (τ, i) ∧
      (∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (w : (Σ k, J k) → ℂ), w ∈ mcPts (mCoordIdeal y) → CoordsAt 𝔐.ξ y z w →
        𝔐.Interior z → A.h w = ∏ i, (hx (τ, i)).h w) ∧
      NearRecord (D.p + D.q) S (hostRd E) (hostLval H) Sf.ht := by
  obtain ⟨F', _, _, ι, ψ, hψ, hcl⟩ := CptInputs.exists_constants hbir 𝔐.cst
  haveI : Nonempty K := hvar.1
  have hN : NormalCpt 𝔐.ξ := XR.normalCpt_of_isCptGen 𝔐.tie.gen 𝔐.normal
  obtain ⟨hφ, a, b, hgen, hrep⟩ := id hflat
  obtain ⟨i, j, hT⟩ := GlobalTheory.T.hodge_component_matches_model_component E H D l Xo c Y U Z S Ω K J y 𝔐 hgp
  obtain ⟨a', b', d₁, d₂, h₁, h₂, ha0, hb0, ha', hb', ea, eb⟩ :=
    GlobalTheory.T.flag_cm_type_lattice_comparison E H D l Xo c Y U Z S Ω K J y 𝔐 Fl τ i j a b hT hgen
  have hdeg := GlobalTheory.T.hodge_cpt_flag_degree E H D l Xo c _ _ Y S Ω K J y 𝔐 Fl xdeg e τ hroot
  have he : ∏ i, e (τ, i) ≠ 0 := hdeg.1
  have hchar : CharZero Ω := charZero_of_injective_ringHom ψ.injective
  have hfr : ∀ p ∈ genFibre ℤ 𝔐.ξ, IsCoeffAt (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) D.p D.q a' b' p 1 := by
    intro p hp
    obtain ⟨⟨x₀, hx₀, ex⟩, hs₁, hs₂⟩ := GlobalTheory.T.cm_type_lattice_comparison E H D l Xo c Y U Z S Ω K J y 𝔐 τ i j hT p hp
    obtain ⟨hv₁, hv₂, -, -⟩ := GlobalTheory.CompanionTheory.Ar.Flat.isVBOn_eig_genFib E H D l Xo c _ _ Y U Z τ.1 (int_frac c.F) τ.2
    obtain ⟨W₁, hW₁, u₁, -, hu₁⟩ := hv₁ x₀ hx₀
    obtain ⟨W₂, hW₂, u₂, -, hu₂⟩ := hv₂ x₀ hx₀
    exact GlobalTheory.T.exterior_coeff_base_change_compat _ _ _ _ _ _ 𝔐.f i _ _ j _ _ _ _ D.p D.q a b a' b' p x₀ u₁ u₂ Z.gen 𝔐.tie.gen hT.1 hT.2.2.1 ex
      (hu₁ x₀ hx₀ hW₁) (hu₂ x₀ hx₀ hW₂) hs₁ hs₂ (hgen.2.2 x₀ hx₀) ha' hb'
  let x₀ : Cpt 𝔐.ξ := ⟨genPt 𝔐.ξ, specializes_rfl⟩
  have hx₀ : x₀ ∈ genFibre ℤ 𝔐.ξ := fun o ho =>
    ⟨by simpa using ho, CoordBase.mem_regAt_gen 𝔐.tie.gen _, CoordBase.mem_regAt_gen 𝔐.tie.gen _⟩
  have haF : exteriorPower.ιMulti Ω _ (Fl.b (.inl τ)) ≠ 0 := fun h => ha0 (by
    have e2 : d₁ • (exteriorPower.ιMulti Ω (labelRk D (.inl τ)) (Fl.b (.inl τ))) = 0 := by rw [h, smul_zero]
    exact ea.trans e2)
  have hbF : exteriorPower.ιMulti Ω _ (Fl.b (.inr τ)) ≠ 0 := fun h => hb0 (by
    have e2 : d₂ • (exteriorPower.ιMulti Ω (labelRk D (.inr τ)) (Fl.b (.inr τ))) = 0 := by rw [h, smul_zero]
    exact eb.trans e2)
  have hVA : (𝔐.V (.inl τ)).IsVB (labelRk D (.inl τ)) _ := 𝔐.vb (.inl τ)
  have hVB : (𝔐.V (.inr τ)).IsVB (labelRk D (.inr τ)) _ := 𝔐.vb (.inr τ)
  have hco : ∀ p ∈ genFibre ℤ 𝔐.ξ, IsCoeffAt (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) (labelRk D (.inl τ)) (labelRk D (.inr τ))
      (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ))) p (d₁ / d₂)⁻¹ :=
    fun p hp => CptIn.isCoeffAt_of_smul h₁ h₂ ea eb (hfr p hp)
  obtain ⟨hL1, hL2, -⟩ := GlobalTheory.T.wedge_line_lattice_vector_bundle 𝔐.X Ω 𝔐.ξ 𝔐.Li (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) _ _ _ _ Set.univ
    (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ))) hVA hVB haF hbF
    ⟨x₀, trivial, _, hco x₀ hx₀⟩
  have hd0 : d₁ / d₂ ≠ 0 := div_ne_zero h₁ h₂
  have hc₁ : (d₁ / d₂ / ∏ i, e (τ, i)) * ∏ i, e (τ, i) = d₁ / d₂ := div_mul_cancel₀ _ he
  have hgn : ∀ p ∈ genFibre ℤ 𝔐.ξ, (lineLat (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) (labelRk D (.inl τ)) (labelRk D (.inr τ))
      (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ)))).IsGenAt p (d₁ / d₂) :=
    fun p hp => (hL2 p trivial _).2 ⟨hd0, hco p hp⟩
  have htriv : ∀ ℓ : ℕ, ℓ.Prime → TrivMod (lineLat (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) (labelRk D (.inl τ)) (labelRk D (.inr τ))
      (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ)))) (ℓ : Ω) ∨
      NumTrivMod (lineLat (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) (labelRk D (.inl τ)) (labelRk D (.inr τ))
      (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ)))) (ℓ : Ω) := by
    intro ℓ hℓ
    by_cases hS : ℓ ∈ S
    · haveI : Fact ℓ.Prime := ⟨hℓ⟩
      refine Or.inl (GlobalTheory.T.wedge_line_lattice_trivial_mod 𝔐.X Ω 𝔐.ξ 𝔐.Li _ _ _ _ _ _ _ _ (ℓ : Ω) 𝔐.tie.gen (Nat.cast_ne_zero.2 hℓ.ne_zero)
        (fun q => ?_) hVA hVB haF hbF ⟨x₀, _, hco x₀ hx₀⟩
        (GlobalTheory.T.hodge_tate_free_cm_type_weight hF E H D l Xo c _ _ Y S Ω K J y 𝔐 ℓ hS hpq (hfree ℓ hS) τ))
      exact natCast_mem _ _
    · exact Or.inr (hnum ℓ hℓ hS _ _ haF hbF ⟨x₀, _, hco x₀ hx₀⟩)
  obtain ⟨r, hr⟩ := CptIn.exists_orders GlobalTheory.T.PropZ_proved ψ hcl 𝔐.all 𝔐.tie hN _ (d₁ / d₂) hL1 hgn htriv
  have hO : OverInt y ψ := overInt_of_normalCpt 𝔐.tie hN ψ
  obtain ⟨A, hAa, hAs, hAc, hAn, hAf⟩ := hSm 𝔐.X Ω 𝔐.ξ K J y F' ψ _ _ _ (d₁ / d₂ / ∏ i, e (τ, i))
    (fun σ => Real.exp (N.inf (σ.comp ι))) n 𝔐.all 𝔐.tie hN hO hbir hvar hdeg (by rw [hc₁]; exact hgn)
    (fun _ => Real.exp_pos _) (fun σ => congrArg Real.exp (hconj (σ.comp ι)))
  obtain ⟨-, Sf, hSf⟩ := exists_flatHerm_hodgeCpt_const E H D l Xo c _ _ Y S Ω K J y 𝔐 Fl xdeg e τ F' ψ A
    (d₁ / d₂ / ∏ i, e (τ, i)) r (fun σ => Real.exp (N.inf (σ.comp ι))) hroot hAa hbir hAc (div_ne_zero hd0 he)
    (by rw [hc₁]; exact hgn) (by rw [hc₁]; exact hr) (fun _ => Real.exp_pos _) hAn
  refine ⟨F', inferInstance, inferInstance, ψ, A, Sf, hO, hAs, hAa, fun z w hw hz hint => ?_, ?_⟩
  · obtain ⟨σ, hσ, -⟩ := GlobalTheory.T.complex_point_existsUnique_embedding K J Ω F' y ψ hO w hw
    obtain ⟨g, h, dg, dh, hg, hh, hdg, hgh, hne⟩ := hAf w hw
    let A₀ : HermLine J := Top.combLine (fun i => hx (τ, i)) fun _ => 1
    have hA₀a : A₀.a = ∑ i, xdeg (τ, i) := by
      show ∑ i, (1 : ℤ) • (hx (τ, i)).a = _
      simp only [one_smul, hxa]
    have hA₀h : ∀ w', A₀.h w' = ∏ i, (hx (τ, i)).h w' := fun w' => by
      show ∏ i, (hx (τ, i)).h w' ^ (1 : ℤ) = _
      simp only [zpow_one]
    have hlies := GlobalTheory.T.point_over_number_field_value 𝔐.X Ω 𝔐.ξ K J y F' ψ σ z w hN 𝔐.tie hz hσ (𝔐.all _)
    have k1 := hAn σ w g h dg dh hσ hg hh (by rw [hAa]; exact hdg) hgh
    have k2 : ‖evC w g‖ = Real.exp (N.inf (σ.comp ι)) * A₀.h w * ‖evC w h‖ := by
      refine GlobalTheory.T.hermitian_norm_section_value 𝔐.X Ω 𝔐.ξ K J y z w A₀ (d₁ / d₂ / ∏ i, e (τ, i)) _ g h dg dh 𝔐.tie.gen hz ?_ hg hh
        (by rw [hA₀a]; exact hdg) hgh hne
      intro cc u hcc hu
      refine GlobalTheory.T.flag_weighted_degree_section E H D l Xo c Y S Ω K J y 𝔐 Fl xdeg e hx A₀ τ (N.inf (σ.comp ι)) (d₁ / d₂) z w hroot hhod hA₀a
        (fun w'' _ => hA₀h w'') hz hint hd0 ?_ cc u hcc (by rw [mul_comm, ← div_div]; exact hu)
      intro hc bp bq Γ Δ α κ u' h1 h2 h3 h4 h5 h6 h7 h8 h9
      refine GlobalTheory.T.cm_type_exterior_lattice_comparison E H D l Xo c Y U Z S Ω K J y 𝔐 τ i j a b a' b' φ (σ.comp ι) _ z hc bp bq Γ Δ (d₁ * α) (d₂ * κ)
        u' hT hφ hgen hrep (hinf _) ha' hb' hint (fun a => ?_) h1 h2 h3 h4 h5 h6 ?_ ?_ ?_
      · rw [← hψ]
        exact hlies (ι a)
      · rw [mul_smul]
        exact ea.trans (congrArg (d₁ • ·) h7)
      · rw [mul_smul]
        exact eb.trans (congrArg (d₂ • ·) h8)
      · rw [← div_mul_div_comm, ← mul_div_assoc]
        exact h9
    rw [← hA₀h]
    exact mul_left_cancel₀ (Real.exp_pos _).ne' (mul_right_cancel₀ (norm_ne_zero_iff.2 hne) (k1.symm.trans k2))
  · rw [hSf]
    simp only [Real.log_exp]
    refine hNu E H D.p D.q c.F F' ι (tauIn c τ.1) N r S (tauIn_injective c τ.1) h2S 𝔐.S_prime had hNdeg ?_
    intro ℓ κ' v π hv hπ
    obtain ⟨m, k, hm, hk, hord⟩ := hr v π hπ
    have hπ0 : π ≠ 0 := by
      rintro rfl
      simp at hπ
      exact WithZero.exp_ne_zero hπ.symm
    have hrv : (r v : ℝ) = (k : ℝ) / m := by
      have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
      have : (k : ℝ) = m * (r v : ℝ) := by exact_mod_cast hk
      rw [this]; field_simp
    obtain ⟨c1, c2⟩ := hLc E H D l Xo c Y U Z S Ω K J y 𝔐 Fl τ i j a b a' b' d₁ d₂ φ F' ι ψ ℓ κ' π m k _ hgp hT hφ hgen
      hrep ha' hb' h₁ h₂ ea eb ha0 hb0 hψ hπ0 hm (fun x hx => hord x fun u hu => hx u ((hv u).1 hu)) (hfin ℓ _)
    rw [hrv]
    refine ⟨fun hS => c1 hS fun hd => hS (hdS ℓ ℓ.2 hd), fun hS => ?_⟩
    obtain ⟨κ, hκ1, hκ2⟩ := GlobalTheory.T.exists_sandwich_of_hodge_tate_free hF E H D l Xo c _ _ Y S Ω K J y 𝔐 ℓ hS hpq (hfree ℓ hS)
    exact c2 hS (hfree ℓ hS) κ hκ1 hκ2

end RootFieldNumerics.RF
