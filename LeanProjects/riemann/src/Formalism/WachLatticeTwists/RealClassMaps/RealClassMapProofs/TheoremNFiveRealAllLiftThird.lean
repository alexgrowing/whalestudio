import Formalism.WachLatticeTwists.RealClassMaps.RealClassMapLiftEveryThirdPlace
import Formalism.WachLatticeTwists.RealClassMaps.RealClassMapProofs.TopAll

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.FIN

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.JS Formalism.RepresentationBoundsCohomology.SplitClassesAll Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.T2
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff FracTop IsFGTop cupFG IsCycOn)

theorem lc_of_torsion (p : ℕ) {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    {A T' G : Type} [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group G] [TopologicalSpace G]
    [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousConstSMul O A] [ContinuousMul A]
    (r : G →* A) (χ : G →* T'ˣ) (E : A)
    (hO : PadicCoeff p O) (hA : IsFGTop O A) (hur : Continuous fun g : G => uElt r χ g)
    {M : Type} [AddCommGroup M] [Module O M] (htors : ∀ m : M, ∃ c : O, c ≠ 0 ∧ c • m = 0)
    (ψ : Ymod r χ E →ₗ[O] M) : IsLocallyConstant fun g => ψ (yY r χ E g) := by
  have hfg : IsFGTop O (Ymod r χ E) := by
    have := hA.fg
    have := hA.t2
    have := hA.csmul
    refine ⟨?_, inferInstance, ?_⟩
    · exact Module.Finite.of_injective ((Ymod r χ E).subtype.restrictScalars O) Subtype.val_injective
    · exact ⟨Continuous.subtype_mk (f := fun q : O × (Ymod r χ E) => q.1 • (q.2 : A))
        (continuous_fst.smul (continuous_subtype_val.comp continuous_snd)) _⟩
  obtain ⟨a, ha, hka⟩ : ∃ a : O, a ≠ 0 ∧ ∀ y : Ymod r χ E, a • ψ y = 0 := by
    obtain ⟨s, hs⟩ := hfg.fg.fg_top
    choose f hf0 hf using fun y : Ymod r χ E => htors (ψ y)
    refine ⟨∏ y ∈ s, f y, Finset.prod_ne_zero_iff.2 (fun y _ => hf0 y), fun y => ?_⟩
    have hy : y ∈ Submodule.span O (s : Set (Ymod r χ E)) := hs ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem f hx
      rw [hc, mul_comm, mul_smul, hf, smul_zero]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, smul_add, hx, hy, add_zero]
    | smul c x _ hx => rw [map_smul, smul_comm, hx, smul_zero]
  have hopen := hfg.isOpen_mulSub hO ha
  have hy : Continuous fun g => yY r χ E g :=
    Continuous.subtype_mk (f := fun g => (uElt r χ g - 1) * E)
      ((hur.sub continuous_const).mul continuous_const) _
  rw [IsLocallyConstant.iff_exists_open]
  intro g₀
  refine ⟨(fun g => yY r χ E g - yY r χ E g₀) ⁻¹' _, hopen.preimage (hy.sub continuous_const), ?_, ?_⟩
  · show yY r χ E g₀ - yY r χ E g₀ ∈ Formalism.RepresentationBoundsCohomology.LOC.mulSub a (Ymod r χ E)
    rw [sub_self]
    exact zero_mem _
  · rintro g ⟨z, hz⟩
    have hz' : a • z = yY r χ E g - yY r χ E g₀ := hz
    have h1 : ψ (yY r χ E g - yY r χ E g₀) = 0 := by
      rw [← hz', map_smul, hka]
    rw [map_sub, sub_eq_zero] at h1
    exact h1

theorem colPsi_lc (p : ℕ) {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    {A T' G : Type} [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group G] [TopologicalSpace G]
    [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousConstSMul O A] [ContinuousMul A]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T')
    (hO : PadicCoeff p O) (hA : IsFGTop O A) (hur : Continuous fun g : G => uElt r χ g)
    {M : Type} [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M] [IsScalarTower O A M]
    (htors : ∀ m : M, ∃ c : O, c ≠ 0 ∧ c • m = 0)
    {ι : Type} [DecidableEq ι] (D : ι → Subgroup G) (j : ι → ℕ) (Kc : ∀ l, Fin (j l) → G → A) (k0 : ι → G → A)
    (φ : ColNNJ r χ E e₁ δ D j Kc k0 →ₗ[A] M) :
    Submodule.mkQ _ (colPsi (O := O) (M := M) r χ E e₁ δ D j Kc k0 φ) ∈ lcH1 (uRep O (M := M) r χ) := by
  refine ⟨colPsi (O := O) (M := M) r χ E e₁ δ D j Kc k0 φ, ?_, rfl⟩
  let ψ : Ymod r χ E →ₗ[O] M :=
    (φ ∘ₗ (colRelJ r χ E e₁ δ D j Kc k0).mkQ ∘ₗ LinearMap.inl A (Ymod r χ E) _).restrictScalars O
  exact lc_of_torsion p r χ E hO hA hur htors ψ

theorem pi_ko_torsion (O : Type) [CommRing O] [IsDomain O] (d : Type) [Fintype d] (m : d → KO O) :
    ∃ c : O, c ≠ 0 ∧ c • m = 0 := by
  classical
  have h1 : ∀ y : KO O, ∃ c : O, c ≠ 0 ∧ c • y = 0 := by
    intro y
    induction y using Submodule.Quotient.induction_on with
    | H x =>
      obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors O) x
      refine ⟨b, nonZeroDivisors.ne_zero b.2, ?_⟩
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_one]
      exact ⟨a, by rw [Algebra.smul_def, mul_comm]; exact hab.symm⟩
  choose c hc0 hc using fun i => h1 (m i)
  refine ⟨∏ i, c i, Finset.prod_ne_zero_iff.2 fun i _ => hc0 i, ?_⟩
  funext i
  rw [Pi.smul_apply, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), mul_smul, hc i, smul_zero]
  rfl

theorem finite_H1V'_dec (ℓ : ℕ) [Fact ℓ.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    {VT VT' : Type}
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
    [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
    [ContinuousSMul O VT'] [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT']
    {Ek Ω : Type} [Field Ek] [NumberField Ek] [Field Ω] [Algebra Ek Ω] [IsAlgClosure Ek Ω]
    (Aw : ValuationSubring Ω) (hp : Aw.valuation (ℓ : Ω) < 1)
    (D : LatData O (Aw.decompositionSubgroup Ek) VT VT') (ε : (Ω ≃ₐ[Ek] Ω) →* Oˣ)
    [Module (FractionRing O) (H1 D.ρT')] [IsScalarTower O (FractionRing O) (H1 D.ρT')]
    (hO : PadicCoeff ℓ O) (hF : FracTop O) (hcyc : IsCycG ℓ ε) (hε : ∀ g, D.ε g = ε g) (hD : RealLat D) :
    Module.Finite (FractionRing O) (H1 D.ρT') := by
  obtain ⟨K, hK, i, h1, -, -⟩ := ReciprocityTheory.ChartRestriction.T2.exists_dec_equiv (F := Ek) Aw hp
  have hεD : D.ε = ε.comp (Aw.decompositionSubgroup Ek).subtype := by
    ext g; simp [hε g]
  have hcw : IsCycOn ℓ (Aw.decompositionSubgroup Ek) (ε.comp (Aw.decompositionSubgroup Ek).subtype) :=
    fun g n ζ h => hcyc g.1 n ζ h
  have hcD : ReciprocityTheory.ChartRestriction.T2.IsCyc ℓ K (ReciprocityTheory.ChartRestriction.T2.carry i D.ε) := h1 O D.ε (hεD ▸ hcw)
  have hD' : ReciprocityTheory.ChartRestriction.T2.RealLatG i D :=
    ⟨hcD, hD.lat, hD.perf, hD.contT, hD.openT, hD.t2, hD.t2', hD.cs, hD.cs'⟩
  have hfin : Module.Finite O (H1 D.ρTl') := ReciprocityTheory.ChartRestriction.T2.finite_H1_of_iso hK hO i hD'
  have hspan : ∀ y : H1 D.ρT', ∃ c : O, c ≠ 0 ∧ c • y ∈ LinearMap.range D.j' :=
    ReciprocityTheory.ChartRestriction.T2.j'_span_iso hO hF i hD'
  obtain ⟨s, hs⟩ : (LinearMap.range D.j').FG := by
    rw [LinearMap.range_eq_map]; exact Submodule.FG.map _ Module.Finite.fg_top
  refine ⟨⟨s, eq_top_iff.2 fun y _ => ?_⟩⟩
  obtain ⟨c, hc, hy⟩ := hspan y
  rw [← hs] at hy
  have hy' : c • y ∈ Submodule.span (FractionRing O) (s : Set (H1 D.ρT')) :=
    Submodule.span_le_restrictScalars O (FractionRing O) _ hy
  rw [← ReciprocityTheory.ChartRestriction.T2.inv_smul_smul_frac hc y]
  exact Submodule.smul_mem _ _ hy'

theorem finite_Hf_dec (ℓ : ℕ) [Fact ℓ.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    {VT VT' : Type}
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
    [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
    [ContinuousSMul O VT'] [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT']
    {Ek Ω : Type} [Field Ek] [NumberField Ek] [Field Ω] [Algebra Ek Ω] [IsAlgClosure Ek Ω]
    (Aw : ValuationSubring Ω) (hp : Aw.valuation (ℓ : Ω) < 1)
    (D : LatData O (Aw.decompositionSubgroup Ek) VT VT') (ε : (Ω ≃ₐ[Ek] Ω) →* Oˣ)
    [Module (FractionRing O) (H1 D.ρT')] [IsScalarTower O (FractionRing O) (H1 D.ρT')]
    (hO : PadicCoeff ℓ O) (hF : FracTop O) (hcyc : IsCycG ℓ ε) (hε : ∀ g, D.ε g = ε g) (hD : RealLat D)
    (Hf : Submodule (FractionRing O) (H1 D.ρT')) : Module.Finite (FractionRing O) Hf := by
  haveI := finite_H1V'_dec ℓ Aw hp D ε hO hF hcyc hε hD
  infer_instance

set_option maxHeartbeats 8000000 in

theorem theorem_n_five_real_third : RealClassMapThirdPlace := by
  intro ℓ _ O _ _ _ _ _ _ _ _ _ X X' T T' Z p q b h1 h2 d _ _ R' _ _ _ _ _ hdet Tc _ _ _ _ Ek Ω _ _ _ _ _
    r χ E e₁ δ ι _ _ colIdx hinj
    Aw pl Av j e' hE2 he1 π' ρπ hρπ t ht bl hbl ρk hsurj hblk _ _ _ _ hcard1 sE tE δO what₂ qs s H0
    Sha uT wT sT mT dT UT hEsum cols eO cB vδ N h0 c1
    L _ _ _ _ _ _ tens v₁ κ V _ _ _ _ _ _ iL qV Ff κz F Vo VS Io IS ε T₁ T₂ _ _ _ _ _ _ _ ρ₁ ρ₂ inc π
    γ lam VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ Dat uD huD vD hpD heD _ _ _ _ Fs Hf₁ I γQ ζ ζO nQ u rr gI s₀ u₁ y
    _ _ _ _ HfW Hf₂ gR Im
    Pe _ _ _ _ _ _ ince eve heve PE _ _ _ _ _ _ incE evE hevE Hfe₁ HfE₁ HfE₂ uz
    hinjO hO hFr hA hcyc hinc hur hAv hreal hs1 hs2 hε hδ hδO hrr hse hsE hincE hact huz hu hLe hLE hrat0 hb1 hb3 hb4
    hFix hRows hC hOne hrest
    conj nlam m cloudC lowsC cloudR lowsR h0C h0R V₂ _ _ _ _ ρV ρA iV qA wD
    τH DatH bH wH mH hrows hnlam hseq hwD hliftR hH0 hJC hJR
  have hfin : ∀ w ∈ cols, Module.Finite (FractionRing O) (Hf₂ (conj w)) := by
    intro w hw
    have hr := hRows (conj w) (hrows ▸ Finset.mem_image_of_mem conj hw)
    exact finite_Hf_dec ℓ (Aw (conj w)) hr.1 (Dat (conj w)) ε hO hFr hcyc hr.2.2.1 hr.2.2.2.1 (Hf₂ (conj w))
  exact theorem_n_five_real_second ℓ O X X' T T' Z p q b h1 h2 d R' hdet Tc Ek Ω r χ E e₁ δ ι colIdx hinj Aw pl Av j e' hE2 he1
    π' ρπ hρπ t ht bl hbl ρk hsurj hblk hcard1 sE tE δO what₂ qs s H0 Sha uT wT sT mT dT UT hEsum
    L tens v₁ κ V iL qV Ff κz F Vo VS Io IS ε T₁ T₂ ρ₁ ρ₂ inc π
    γ lam VT VT' Dat uD huD vD hpD heD Fs Hf₁ I γQ ζ ζO nQ u rr gI s₀ u₁ y HfW Hf₂
    Pe ince eve heve PE incE evE hevE Hfe₁ HfE₁ HfE₂ uz
    hinjO hO hFr hA hcyc hinc hur hAv hreal hs1 hs2 hε hδ hδO hrr hse hsE hincE hact huz hu hLe hLE hrat0 hb1 hb3 hb4
    hFix hRows hC hOne
    (fun Kc k0 hK hk => ⟨hrest Kc k0 hK hk, fun c φ =>
      colPsi_lc ℓ (M := blockRestrictedRepresentationType bl ρk c) r χ E e₁ δ hO hA hur (fun m => pi_ko_torsion O _ m) _ _ Kc k0 φ⟩)
    conj nlam m cloudC lowsC cloudR lowsR h0C h0R V₂ ρV ρA iV qA wD
    τH DatH bH wH mH hrows hseq hwD hliftR hH0 hJC
    (fun w hw => ⟨(hJR w hw).1, (hJR w hw).2.1, hfin w hw, (hJR w hw).2.2⟩)

set_option maxHeartbeats 8000000 in

theorem theorem_n_five_real_lift_third : RealClassMapLiftThirdPlace := by
  intro ℓ _ O _ _ _ _ _ _ _ _ _ X X' T T' Z p q b h1 h2 d _ _ R' _ _ _ _ _ hdet Tc _ _ _ _ Ek Ω _ _ _ _ _
    r χ E e₁ δ ι _ _ colIdx hinj
    Aw pl Av j e' hE2 he1 π' ρπ hρπ t ht bl hbl ρk hsurj hblk _ _ _ _ hcard1 sE tE δO what₂ qs s H0
    Sha uT wT sT mT dT UT hEsum cols eO cB vδ N h0 c1
    L _ _ _ _ _ _ tens v₁ κ V _ _ _ _ _ _ iL qV Ff κz F Vo VS Io IS ε T₁ T₂ _ _ _ _ _ _ _ ρ₁ ρ₂ inc π
    γ lam VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ Dat uD huD vD hpD heD _ _ _ _ Fs Hf₁ I γQ ζ ζO nQ u rr gI s₀ u₁ y
    _ _ _ _ HfW Hf₂ gR Im
    Pe _ _ _ _ _ _ ince eve heve PE _ _ _ _ _ _ incE evE hevE Hfe₁ HfE₁ HfE₂ uz
    hinjO hO hFr hA hcyc hinc hur hAv hreal hs1 hs2 hε hδ hδO hrr hse hsE hincE hact huz hu hLe hLE hrat0 hb1 hb3 hb4
    hFix hRows hC hOne hrest
    conj nlam m cloudC lowsC cloudR lowsR h0C h0R V₂ _ _ _ _ ρV ρA iV qA wD
    τH DatH bH wH mH hrows hnlam hseq hwD hliftR hH0 hJC hJR
  have hfin : ∀ w ∈ cols, Module.Finite (FractionRing O) (Hf₂ (conj w)) := by
    intro w hw
    have hr := hRows (conj w) (hrows ▸ Finset.mem_image_of_mem conj hw)
    exact finite_Hf_dec ℓ (Aw (conj w)) hr.1 (Dat (conj w)) ε hO hFr hcyc hr.2.2.1 hr.2.2.2.1 (Hf₂ (conj w))
  exact theorem_n_five_real_lift ℓ O X X' T T' Z p q b h1 h2 d R' hdet Tc Ek Ω r χ E e₁ δ ι colIdx hinj Aw pl Av j e' hE2 he1
    π' ρπ hρπ t ht bl hbl ρk hsurj hblk hcard1 sE tE δO what₂ qs s H0 Sha uT wT sT mT dT UT hEsum
    L tens v₁ κ V iL qV Ff κz F Vo VS Io IS ε T₁ T₂ ρ₁ ρ₂ inc π
    γ lam VT VT' Dat uD huD vD hpD heD Fs Hf₁ I γQ ζ ζO nQ u rr gI s₀ u₁ y HfW Hf₂
    Pe ince eve heve PE incE evE hevE Hfe₁ HfE₁ HfE₂ uz
    hinjO hO hFr hA hcyc hinc hur hAv hreal hs1 hs2 hε hδ hδO hrr hse hsE hincE hact huz hu hLe hLE hrat0 hb1 hb3 hb4
    hFix hRows hC hOne
    (fun Kc k0 hK hk => ⟨hrest Kc k0 hK hk, fun c φ =>
      colPsi_lc ℓ (M := blockRestrictedRepresentationType bl ρk c) r χ E e₁ δ hO hA hur (fun m => pi_ko_torsion O _ m) _ _ Kc k0 φ⟩)
    conj nlam m cloudC lowsC cloudR lowsR h0C h0R V₂ ρV ρA iV qA wD
    τH DatH bH wH mH hrows hseq hwD hliftR hH0 hJC
    (fun w hw => ⟨(hJR w hw).1, (hJR w hw).2.1, hfin w hw, (hJR w hw).2.2⟩)

set_option maxHeartbeats 8000000 in

theorem theorem_n_five_real_all_third : RealClassMapEveryThirdPlace := by
  intro ℓ _ O _ _ _ _ _ _ _ _ _ X X' T T' Z p q b h1 h2 d _ _ R' _ _ _ _ _ hdet Tc _ _ _ _ Ek Ω _ _ _ _ _
    r χ E e₁ δ ι _ _ colIdx hinj
    Aw pl Av j e' hE2 he1 π' ρπ hρπ t ht bl hbl ρk hsurj hblk _ _ _ _ hcard1 sE tE δO what₂ qs s H0
    Sha uT wT sT mT dT UT hEsum cols eO cB vδ N h0 c1
    L _ _ _ _ _ _ tens v₁ κ V _ _ _ _ _ _ iL qV Ff κz F Vo VS Io IS ε T₁ T₂ _ _ _ _ _ _ _ ρ₁ ρ₂ inc π
    γ lam VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ Dat uD huD vD hpD heD Fs Hf₁ I γQ ζ ζO nQ u rr gI s₀ u₁ y
    _ _ _ _ HfW Hf₂ gR Im
    Pe _ _ _ _ _ _ ince eve heve PE _ _ _ _ _ _ incE evE hevE Hfe₁ HfE₁ HfE₂ uz
    hinjO hO hFr hA hcyc hinc hur hAv hreal hs1 hs2 hε hδ hδO hrr hse hsE hincE hact huz hu hLe hLE hrat0 hb1 hb3 hb4
    hFix hRows hC hOne hrest
  exact theorem_n_five_real_all_second ℓ O X X' T T' Z p q b h1 h2 d R' hdet Tc Ek Ω r χ E e₁ δ ι colIdx hinj Aw pl Av j e' hE2 he1
    π' ρπ hρπ t ht bl hbl ρk hsurj hblk hcard1 sE tE δO what₂ qs s H0 Sha uT wT sT mT dT UT hEsum
    L tens v₁ κ V iL qV Ff κz F Vo VS Io IS ε T₁ T₂ ρ₁ ρ₂ inc π
    γ lam VT VT' Dat uD huD vD hpD heD Fs Hf₁ I γQ ζ ζO nQ u rr gI s₀ u₁ y HfW Hf₂
    Pe ince eve heve PE incE evE hevE Hfe₁ HfE₁ HfE₂ uz
    hinjO hO hFr hA hcyc hinc hur hAv hreal hs1 hs2 hε hδ hδO hrr hse hsE hincE hact huz hu hLe hLE hrat0 hb1 hb3 hb4
    hFix hRows hC hOne
    (fun Kc k0 hK hk => ⟨hrest Kc k0 hK hk, fun c φ =>
      colPsi_lc ℓ (M := blockRestrictedRepresentationType bl ρk c) r χ E e₁ δ hO hA hur (fun m => pi_ko_torsion O _ m) _ _ Kc k0 φ⟩)

set_option maxHeartbeats 8000000 in

theorem theorem_n_five_real_all_lift_third : RealClassMapLiftEveryThirdPlace := by
  intro ℓ _ O _ _ _ _ _ _ _ _ _ X X' T T' Z p q b h1 h2 d _ _ R' _ _ _ _ _ hdet Tc _ _ _ _ Ek Ω _ _ _ _ _
    r χ E e₁ δ ι _ _ colIdx hinj
    Aw pl Av j e' hE2 he1 π' ρπ hρπ t ht bl hbl ρk hsurj hblk _ _ _ _ hcard1 sE tE δO what₂ qs s H0
    Sha uT wT sT mT dT UT hEsum cols eO cB vδ N h0 c1
    L _ _ _ _ _ _ tens v₁ κ V _ _ _ _ _ _ iL qV Ff κz F Vo VS Io IS ε T₁ T₂ _ _ _ _ _ _ _ ρ₁ ρ₂ inc π
    γ lam VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ Dat uD huD vD hpD heD Fs Hf₁ I γQ ζ ζO nQ u rr gI s₀ u₁ y
    _ _ _ _ HfW Hf₂ gR Im
    Pe _ _ _ _ _ _ ince eve heve PE _ _ _ _ _ _ incE evE hevE Hfe₁ HfE₁ HfE₂ uz
    hinjO hO hFr hA hcyc hinc hur hAv hreal hs1 hs2 hε hδ hδO hrr hse hsE hincE hact huz hu hLe hLE hrat0 hb1 hb3 hb4
    hFix hRows hC hOne hrest
  exact theorem_n_five_real_all_lift ℓ O X X' T T' Z p q b h1 h2 d R' hdet Tc Ek Ω r χ E e₁ δ ι colIdx hinj Aw pl Av j e' hE2 he1
    π' ρπ hρπ t ht bl hbl ρk hsurj hblk hcard1 sE tE δO what₂ qs s H0 Sha uT wT sT mT dT UT hEsum
    L tens v₁ κ V iL qV Ff κz F Vo VS Io IS ε T₁ T₂ ρ₁ ρ₂ inc π
    γ lam VT VT' Dat uD huD vD hpD heD Fs Hf₁ I γQ ζ ζO nQ u rr gI s₀ u₁ y HfW Hf₂
    Pe ince eve heve PE incE evE hevE Hfe₁ HfE₁ HfE₂ uz
    hinjO hO hFr hA hcyc hinc hur hAv hreal hs1 hs2 hε hδ hδO hrr hse hsE hincE hact huz hu hLe hLE hrat0 hb1 hb3 hb4
    hFix hRows hC hOne
    (fun Kc k0 hK hk => ⟨hrest Kc k0 hK hk, fun c φ =>
      colPsi_lc ℓ (M := blockRestrictedRepresentationType bl ρk c) r χ E e₁ δ hO hA hur (fun m => pi_ko_torsion O _ m) _ _ Kc k0 φ⟩)

end Formalism.RepresentationBoundsCohomology.FIN
