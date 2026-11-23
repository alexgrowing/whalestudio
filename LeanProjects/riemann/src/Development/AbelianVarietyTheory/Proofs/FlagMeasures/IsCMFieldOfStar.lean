import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AdaptSelf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LandherrHasse
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GenusMassSignature

noncomputable section

open NumberField GlobalTheory.DegCnt

namespace GlobalTheory.OrthoLattice

theorem isCMField_of_star (K : Type) [Field K] [NumberField K] [StarRing K] (htc : IsTotallyComplex K)
    (hst : ∀ (φ : K →+* ℂ) (a : K), φ (star a) = starRingEnd ℂ (φ a)) : IsCMField K := by
  let φ : K →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  have hmem : ∀ x : K, star x = x → x ∈ maximalRealSubfield K := fun x hx ψ => by
    have := hst ψ x
    rw [hx] at this
    exact this.symm
  have hfix : ∀ x : maximalRealSubfield K, star (x : K) = x := fun x =>
    φ.injective (by rw [hst]; exact x.2 φ)
  obtain ⟨a, ha⟩ : ∃ a : K, star a ≠ a := by
    by_contra h
    push Not at h
    apply IsTotallyComplex.complexEmbedding_not_isReal φ
    rw [ComplexEmbedding.isReal_iff]
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq, ← hst, h]
  set d : K := a - star a with hd
  have hd0 : d ≠ 0 := sub_ne_zero.2 ha.symm
  have hds : star d = -d := by simp [hd]
  have hli : LinearIndependent (maximalRealSubfield K) ![(1 : K), d] := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have h1 : (s : K) + (t : K) * d = 0 := by simpa [Subfield.smul_def] using h
    have h2 := congrArg star h1
    rw [star_add, star_mul, hfix, hfix, hds, star_zero] at h2
    have h3 : (s : K) = 0 := by linear_combination (h1 + h2) / 2
    have h4 : (t : K) * d = 0 := by linear_combination h1 - h3
    exact ⟨Subtype.ext h3, Subtype.ext ((mul_eq_zero.1 h4).resolve_right hd0)⟩
  have hsp : ⊤ ≤ Submodule.span (maximalRealSubfield K) (Set.range ![(1 : K), d]) := by
    intro x _
    have h1 : star ((x + star x) / 2) = (x + star x) / 2 := by
      rw [star_div₀, star_add, star_star, star_ofNat, add_comm]
    have h2 : star ((x - star x) / (2 * d)) = (x - star x) / (2 * d) := by
      rw [star_div₀, star_sub, star_star, star_mul, star_ofNat, hds]
      field_simp
      ring
    have h3 : x = (⟨_, hmem _ h1⟩ : maximalRealSubfield K) • (1 : K) +
        (⟨_, hmem _ h2⟩ : maximalRealSubfield K) • d := by
      simp only [Subfield.smul_def, smul_eq_mul]
      field_simp
      ring
    rw [h3]
    exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  have : Algebra.IsQuadraticExtension (maximalRealSubfield K) K :=
    { finrank_eq_two' := by simpa using Module.finrank_eq_card_basis (Module.Basis.mk hli hsp) }
  exact ⟨⟩

theorem hasOrtho : ∀ (K : Type) [Field K] [NumberField K] [StarRing K],
    Formalism.HermitianLatticesTheory.IsCMUnram K → HasOrtho K := by
  intro K _ _ st hc
  have := isCMField_of_star K hc.1 hc.2.1
  have hs : st = IsCMField.starRing K := by
    let φ : K →+* ℂ := Classical.choice (inferInstance : Nonempty _)
    have h : ∀ x, st.star x = IsCMField.complexConj K x := fun x =>
      φ.injective (by rw [IsCMField.complexEmbedding_complexConj]; exact hc.2.1 φ x)
    obtain @⟨@⟨@⟨@⟨f⟩, _⟩, _⟩, _⟩ := st
    obtain rfl : f = IsCMField.complexConj K := funext h
    rfl
  subst hs
  let := IsCMField.starRing K
  intro W _ _ _ _ _ k hk hp ⟨L, hL, hU⟩
  let φ : K →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  have hnd : k.Nondegenerate := by
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩ <;>
    · by_contra h0
      have := hp φ x h0
      rw [hx x] at this
      simp at this
  let S : Formalism.BasicNotions.HSpace K := Formalism.BasicNotions.HSpace.mk W k hk hnd (Module.finrank K W) rfl (Module.finBasis K W)
    (fun _ => (Module.finrank K W, 0)) L hL hU
  have hsig : S.SigOK := fun τ => GlobalTheory.Proof.GenusMassSignature.hasSignature_of_posDef
    ((GlobalTheory.Proof.GenusMassSignature.pos_iff_posDef hc.1 hc.2.1 S τ).1 (hp τ))
  obtain ⟨b, hb, ho⟩ := GlobalTheory.DefiniteOrthonormal.exists_orthonormal hc S hsig fun _ => rfl
  exact ⟨_, b, hb, hb.span_eq_top_of_card_eq_finrank' (Fintype.card_fin _), rfl, ho⟩

end GlobalTheory.OrthoLattice
