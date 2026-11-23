import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.TracePow
import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.GlnMixed
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.JacquetBorelNontrivialOfCharacterSupport
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwJqMult
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSatakeParameterOfIsSubquotientOfInjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportOfPrincipalSeriesSubquotient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalSegmentRepLengthOneUnramified
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalArtinLocalIdeleInjective

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel Matrix UpperTheory.ConvolutionTheory.Loc

namespace UpperTheory.Gal.LocD

theorem jFacts : JFacts := by
  intro E _ _ _ _ n V _ _ π hi ω hω h
  have hs : IsSmooth π := h.isSmooth (isSmooth_parInd _ _)
  have hsupp := GlobalTheory.CompanionTheory.SphSupp.hasSupport_prinSeries n ω hω ⟨V, π, hs, hi⟩ h
  obtain ⟨hf, -, hm⟩ := UpperTheory.V.AlgebraTools.jqMult UpperTheory.Lit.Mix.geometricLemma GlobalTheory.bernsteinZelevinskyFiniteness_holds
    E n V π ω hs hω h
  refine ⟨hs, UpperTheory.jacquet_borel_nontrivial_of_character_support UpperTheory.Lit.Mix.geometricLemma UpperTheory.Lit.Mix.polynomialRing E n V π _ hsupp fun y hy => ?_,
    hf, fun μ hμ => ?_⟩
  · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hy
    rfl
  · have h1 := lt_of_lt_of_le (Nat.pos_of_ne_zero fun e => hμ (Submodule.finrank_eq_zero.1 e)) (hm μ)
    obtain ⟨w⟩ := (Nat.card_pos_iff.1 h1).1
    exact ⟨w.1, w.2⟩

theorem ofSupport : OfSupport := by
  intro k _ _ _ _ n V _ _ π μ hμ
  refine ⟨fun hs => ⟨hs.isIrreducible, ?_⟩, fun h =>
    GlobalTheory.CompanionTheory.SphSupp.hasSupport_prinSeries n μ hμ ⟨V, π, h.2.isSmooth (isSmooth_parInd _ _), h.1⟩ h.2⟩
  have hd : ∑ i, (IrrGL.ofChar (μ i) (hμ i)).1 = n := by simp [IrrGL.ofChar]
  refine IsSubquotient.trans ?_ (GlobalTheory.SphSeg.isSubquotient_prodIrr_prinSeries _ hd μ hμ fun _ => rfl)
  obtain ⟨Z, Ψ, -, hΨ, -⟩ := UpperTheory.Lit.Mix.polynomialRing k
  have h1 := SupportRing.pos_pc_sub hΨ hs hs.isSmooth hs.isIrreducible
  obtain ⟨hp, ep⟩ := SupportRing.prodIrr_cls hΨ _ hd
  refine SupportRing.isSubquotient_of_clsGL_ne hp hs.isSmooth hs.isIrreducible ?_
  have h2 := h1 (IrrGL.of π hs.isSmooth hs.isIrreducible)
  rw [SupportRing.pc_map, ← ep] at h2
  have e1 : ∀ (A : GrothGL k) (y : IrrGL k), Ψ.symm (Ψ A - SupportRing.bas Ψ y) y = A y - 1 := by
    intro A y
    rw [SupportRing.bas, ← map_sub, Ψ.symm_apply_apply, Finsupp.sub_apply, Finsupp.single_eq_same]
  rw [e1] at h2
  intro h3
  rw [h3] at h2
  exact absurd h2 (by norm_num)

theorem scalar_of (hE : Eig) (hB : ToBorel) (hJ : JacSemi) (hC : Core) : Scalar := by
  intro E _ _ _ _ n σ q hσ V _ _ π hi ω hω hinv h A hA
  obtain ⟨hs, hn, hf, hm⟩ := jFacts E n V π hi ω hω h
  obtain ⟨μ, l, c, hl, hμ, hlt, hlA⟩ := hE _ _ (jacB π) (fun t i => Units.map (σ : E →* E) (t i)) (jacA hA)
    (hJ E n σ hσ.isom V π A hA) fun μ hμ t => by
      obtain ⟨w, rfl⟩ := hm μ hμ
      simp only [torusChar_apply]
      exact Finset.prod_congr rfl fun i _ => hinv _ _
  obtain ⟨χ, hχ, hχl⟩ := hB E n σ hσ.isom V π μ hμ l hlt
  refine ⟨c, hC E n σ q hσ V π hs hi A hA χ hχ (l ∘ₗ Submodule.mkQ _) c (fun e => hl ?_) hχl fun v => hlA (Submodule.Quotient.mk v)⟩
  refine LinearMap.ext fun y => ?_
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  exact LinearMap.congr_fun e v

theorem locDesc_of (hS : Scalar) (hT : TracePow) : LocDesc := by
  intro E _ _ _ _ n σ q hσ V _ _ π hi ω hω hinv h A hA h0
  obtain ⟨hs, hn, hf, hm⟩ := jFacts E n V π hi ω hω h
  obtain ⟨c, hc, hψ⟩ := hS E n σ q hσ V π hi ω hω hinv h A hA
  have hw : whitChar (1 : AddChar E Circle) n = 1 := by
    ext u
    simp [whitChar]
  have hj : jacA hA = c • LinearMap.id := by
    refine LinearMap.ext fun y => ?_
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have := hψ 1 continuous_const (fun _ => rfl) v
    rw [hw] at this
    exact (Submodule.Quotient.eq _).2 this
  refine ⟨hn, hf, hm, c, hc h0, hj, fun ψ h1 h2 l a hl hu ha => ?_, fun U hU hst t k₀ => ?_⟩
  · have hk : twKer π (unipB E (Fin n)) (whitChar ψ n) ≤ LinearMap.ker l := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨u, v, rfl⟩
      simp [hu]
    obtain ⟨v, hv⟩ : ∃ v, l v ≠ 0 := by
      by_contra! e
      exact hl (LinearMap.ext e)
    have := hk (hψ ψ h1 h2 v)
    rw [LinearMap.mem_ker, map_sub, map_smul, ha, smul_eq_mul, sub_eq_zero] at this
    exact (mul_right_cancel₀ hv this).symm
  · haveI : Nontrivial U := Submodule.nontrivial_iff_ne_bot.2 hU
    let φ : U →ₗ[ℂ] U := (jacB π t).restrict (hst t)
    have hφ : Function.Injective φ := fun a b e => by
      have e' : jacB π t a = jacB π t b := congrArg Subtype.val e
      have := congrArg (jacB π t⁻¹) e'
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one] at this
      exact Subtype.ext this
    obtain ⟨k, hk, hne⟩ := hT U φ hφ k₀
    have hmem : ∀ y ∈ U, (jacB π (t ^ k) ∘ₗ jacA hA) y ∈ U := fun y hy => by
      rw [hj]
      exact hst _ _ (U.smul_mem c hy)
    refine ⟨k, hk, hmem, ?_⟩
    have : (jacB π (t ^ k) ∘ₗ jacA hA).restrict hmem = c • φ ^ k := by
      ext y
      simp only [φ, Module.End.pow_restrict k (hst t), LinearMap.restrict_apply, LinearMap.smul_apply,
        Submodule.coe_smul, LinearMap.comp_apply, hj, LinearMap.id_apply, map_smul, map_pow]
    rw [this, map_smul, smul_eq_mul]
    exact mul_ne_zero (hc h0) hne

end UpperTheory.Gal.LocD
