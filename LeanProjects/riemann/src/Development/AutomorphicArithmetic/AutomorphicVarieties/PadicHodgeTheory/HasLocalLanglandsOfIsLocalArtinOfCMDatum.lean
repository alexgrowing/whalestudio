import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaWDDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedIsCrysAndJumpEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ConclusionFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOddPrimeGtTwoBounds
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormEqOfSamePlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlaceEqOfContEmbCompEq
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W

private theorem emb_eq {M Ω : Type} [Field M] [NumberField M] [Field Ω] [Algebra M Ω] [IsAlgClosure M Ω] {l : ℕ}
    [Fact l.Prime] {A : ValuationSubring Ω} {u : Plc M} (h : IsPlaceOver A u) {O : Type} [CommRing O]
    [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l M Ω (Dec (F := M) A) O) (hj : GlobalTheory.Pst.Induces Bw)
    (δ : M) (d : ℚ_[l]) (hd : Bw.j (algebraMap M Ω δ) = algebraMap ℚ_[l] (Om l) d) (τ : Emb l u) :
    τ.1 (algebraMap M (u.adicCompletion M) δ) = algebraMap ℚ_[l] (Om l) d := by
  let jE : M →+* Om l := Bw.j.comp (algebraMap M Ω)
  let t : M →+* Om l := τ.1.comp (algebraMap M (u.adicCompletion M))
  have hjE : ∀ x : 𝓞 M, ‖jE (x : M)‖ < 1 ↔ x ∈ u.asIdeal := fun x =>
    (hj.valuation_lt_one_iff _).symm.trans (h x)
  have ht : ∀ x : 𝓞 M, ‖t (x : M)‖ < 1 ↔ x ∈ u.asIdeal := fun x => by
    refine ⟨fun hx => ?_, norm_lt_one_of_contEmb u τ.1 τ.2 x⟩
    by_contra hxu
    obtain ⟨y, a, ha, e⟩ := u.isMaximal.exists_inv hxu
    have h1 : ‖t (a : M)‖ < 1 := norm_lt_one_of_contEmb u τ.1 τ.2 a ha
    have h2 : ‖t ((y * x : 𝓞 M) : M)‖ < 1 := by
      rw [show ((y * x : 𝓞 M) : M) = (y : M) * (x : M) from map_mul _ _ _, map_mul, norm_mul]
      exact mul_lt_one_of_nonneg_of_lt_one_right (PI.CompDegEF.norm_le_one_of_integer t y) (norm_nonneg _) hx
    have h3 := IsUltrametricDist.norm_add_le_max (t ((y * x : 𝓞 M) : M)) (t (a : M))
    rw [← map_add, show ((y * x : 𝓞 M) : M) + (a : M) = 1 by
      rw [← map_add (algebraMap (𝓞 M) M), e, map_one], map_one, norm_one] at h3
    exact absurd (h3.trans_lt (max_lt h2 h1)) (lt_irrefl _)
  have hn := GlobalTheory.GalFirstClause.Emb.norm_eq_of_samePlace jE t u (hj.mem_placesOver h) hjE ht
  have key := GlobalTheory.GalFirstClause.Emb.norm_tensLift_le jE t hn ((1 : ℚ_[l]) ⊗ₜ[ℚ] δ - d ⊗ₜ[ℚ] (1 : M))
  simp only [map_sub, GlobalTheory.GalFirstClause.Emb.tensLift_tmul, map_one, one_mul, mul_one] at key
  rw [show jE δ = algebraMap ℚ_[l] (Om l) d from hd, sub_self, norm_zero, norm_le_zero_iff, sub_eq_zero] at key
  exact key

theorem UpperTheory.hasLocalLanglands_of_isLocalArtin_of_CMDatum :
    HeckeLAdicCharacter → HeckeLAdicCharacterDeRham → AlgebraicCharacterWD → DeRhamPotSemistable → ∀ {M Ω : Type} [Field M] [NumberField M] [IsCMField M] [Field Ω] [Algebra M Ω] [IsAlgClosure M Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {u : Plc M} (h : IsPlaceOver A u) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l M Ω (Dec (F := M) A) O) (hj : GlobalTheory.Pst.Induces Bw) (ι : Qbar l ≃+* ℂ) (δ : M) (d : ℚ_[l]), δ ≠ 0 → Bw.j (algebraMap M Ω δ) = algebraMap ℚ_[l] (Om l) d → (∀ φ : M →+* ℂ, starRingEnd ℂ (φ δ) = -φ δ) → ∀ (wt : Emb l u → ℤ) (a : Weil h →* (u.adicCompletion M)ˣ), IsLocalArtin h a → UpperTheory.V.Loc.HasLT h Bw hj ι wt a := by
  intro hH hR hW hD M Ω _ _ _ _ _ _ l _ A u h O _ _ _ Bw hj ι δ d hδ hd hc wt a ha
  classical
  let r : Emb l u → (M →+* ℂ) := fun τ => (ι.toRingHom.comp τ.1).comp (algebraMap M (u.adicCompletion M))
  have hrδ : ∀ τ, r τ δ = ι (algebraMap ℚ_[l] (Om l) d) := fun τ =>
    congrArg ι (emb_eq h Bw hj δ d hd τ)
  have hr : Function.Injective r := fun τ τ' e => by
    apply Subtype.ext
    apply DFunLike.coe_injective
    refine (HeightOneSpectrum.denseRange_algebraMap M u).equalizer τ.2 τ'.2 (funext fun k => ?_)
    exact ι.injective (DFunLike.congr_fun e k)
  let g : (M →+* ℂ) → ℤ := Function.extend r wt 0
  let n : (M →+* ℂ) → ℤ := fun φ => g (ComplexEmbedding.conjugate φ) - g φ
  have hn : ∀ τ, n (r τ) = -wt τ := fun τ => by
    have h1 : g (r τ) = wt τ := hr.extend_apply _ _ _
    have h2 : g (ComplexEmbedding.conjugate (r τ)) = 0 := by
      refine Function.extend_apply' _ _ _ ?_
      rintro ⟨τ', e⟩
      have e1 : r τ' δ = starRingEnd ℂ (r τ δ) := DFunLike.congr_fun e δ
      rw [hc, hrδ τ', ← hrδ τ, self_eq_neg] at e1
      exact hδ ((map_eq_zero _).1 e1)
    simp only [n, h1, h2, zero_sub]
  obtain ⟨χ, hχ, -⟩ := GlobalTheory.AlgCharUnr.exists_algChar_unr M l Fact.out n 0 fun φ => by
    have : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate φ) = φ := star_star φ
    simp only [n, this]
    ring
  obtain ⟨art, hart, hμ⟩ := hH M Ω
  obtain ⟨μ, ⟨hμc, hL⟩, -⟩ := hμ l ι χ n hχ
  obtain ⟨T⟩ := UpperTheory.V.Loc.tiedP l
  have hrk : GlobalTheory.TripleGal.rk1 (μ.comp (Dec (F := M) A).subtype) =
      (GlobalTheory.TripleGal.rk1 μ).comp (Dec (F := M) A).subtype := by
    ext σ i j
    simp [GlobalTheory.TripleGal.rk1]
  have hcμ : Continuous fun σ : ↥(Dec (F := M) A) =>
      (((GlobalTheory.TripleGal.rk1 μ).comp (Dec (F := M) A).subtype σ : GL (Fin 1) (Om l)) :
        Matrix (Fin 1) (Fin 1) (Om l)) := by
    refine continuous_matrix fun i j => ?_
    fin_cases i; fin_cases j
    have := Units.continuous_val.comp (hμc.comp (continuous_subtype_val (p := fun x => x ∈ Dec (F := M) A)))
    simpa [GlobalTheory.TripleGal.rk1, Function.comp_def] using this
  have hcp := GlobalTheory.Published.ParamAboveModel.isComp_loc (w := u) χ
  refine ⟨μ.comp (Dec (F := M) A).subtype, (χ.loc u).comp a, hμc.comp continuous_subtype_val, ha.smooth hcp.1,
    ?_, fun σ => ?_, fun σ => ?_⟩
  · rw [hrk]
    exact hD.isPstAt T Bw _ hcμ (hR M Ω l _ _ ⟨T⟩ ι art hart χ n μ hχ hμc hL u A h O Bw hj).1
  · have h1 := hL.loc (a σ) _ (ha.glob art hart σ)
    haveI := finite_contEmb (l := l) u
    have h2 : locPow ι n u (a σ) * ∏ᶠ τ : Emb l u, τ.1 (a σ : u.adicCompletion M) ^ wt τ = 1 := by
      unfold locPow
      rw [← finprod_mul_distrib (Set.toFinite _) (Set.toFinite _)]
      refine finprod_eq_one_of_forall_eq_one fun τ => ?_
      rw [← zpow_add₀ ((map_ne_zero τ.1).2 (a σ).ne_zero), show n _ = -wt τ from hn τ, neg_add_cancel, zpow_zero]
    show ((χ.loc u (a σ) : ℂˣ) : ℂ) = ι (((μ (σ : G M Ω) : (Qbar l)ˣ) : Qbar l) * _)
    rw [h1, mul_assoc, h2, mul_one, ι.apply_symm_apply]
  · rw [hrk, hW M Ω l _ _ ⟨T⟩ ι art hart χ n μ hχ hμc hL u A h O Bw hj _ hcp a ha, eig_lpOfChar]
    exact Multiset.mem_singleton_self _
