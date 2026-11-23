import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueEqZeroIffV
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FrTanDirAlg
open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PrimePart

open Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDirAlg

theorem exists_inv_of_not_dvd_discr (E : Type) [Field E] [NumberField E] {V : Type} [CommRing V] [IsDomain V]
    [IsLocalRing V] {Fr : Type} [Field Fr] [Algebra V Fr]
    [DecidableEq (E →+* ℂ)] (hinj : Function.Injective (algebraMap V Fr)) {F : Type} [Field F] (j : F →+* ℂ)
    (io : F →+* Fr)
    (φ : (E →+* ℂ) → (E →+* F)) (hφ : ∀ σ x, j (φ σ x) = σ x)
    (χ : (E →+* ℂ) → (𝓞 E →+* V)) (hχ : ∀ σ (a : 𝓞 E), algebraMap V Fr (χ σ a) = io (φ σ (a : E)))
    (g : ℕ) (hg : g.Prime) (hgV : ¬ IsUnit (g : V)) (hd : ¬ (g : ℤ) ∣ discr E) :
    ∃ Cm : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → (E →+* ℂ) → V,
      (∀ σ τ, ∑ i, χ σ (RingOfIntegers.basis E i) * Cm i τ = if σ = τ then 1 else 0) ∧
      (∀ i i', ∑ τ, Cm i τ * χ τ (RingOfIntegers.basis E i') = if i = i' then 1 else 0) := by
  classical
  let bs := RingOfIntegers.basis E
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) = Fintype.card (E →ₐ[ℚ] ℂ) := by
    rw [AlgHom.card, ← RingOfIntegers.rank, Module.finrank_eq_card_chooseBasisIndex]
  let e : Module.Free.ChooseBasisIndex ℤ (𝓞 E) ≃ (E →ₐ[ℚ] ℂ) := Fintype.equivOfCardEq hcard
  let e' : Module.Free.ChooseBasisIndex ℤ (𝓞 E) ≃ (E →+* ℂ) := e.trans (RingHom.equivRatAlgHom E ℂ).symm
  let A : Matrix (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) V :=
    fun i k => χ (e' k) (bs i)
  have hAij : ∀ i k, A i k = χ (e' k) (bs i) := fun _ _ => rfl
  let AF : Matrix (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) F :=
    fun i k => φ (e' k) (bs i : E)
  have hAF : AF.map j = Algebra.embeddingsMatrixReindex ℚ ℂ (fun i => (bs i : E)) e := by
    ext i k
    simp only [Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix,
      Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply, Equiv.refl_symm, Equiv.refl_apply,
      Equiv.symm_symm]
    show j (φ (e' k) (bs i : E)) = (e k) (bs i : E)
    rw [hφ]
    rfl
  have hdF : AF.det ^ 2 = ((discr E : ℤ) : F) := by
    apply j.injective
    rw [map_pow, RingHom.map_det, RingHom.mapMatrix_apply, hAF,
      ← Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two, map_intCast]
    have hb : (fun i => (bs i : E)) = ⇑(integralBasis E) := funext fun i => (integralBasis_apply E i).symm
    rw [hb, ← coe_discr, map_intCast]
  have hdV : A.det ^ 2 = ((discr E : ℤ) : V) := by
    apply hinj
    rw [map_pow, RingHom.map_det, map_intCast]
    have hA : (algebraMap V Fr).mapMatrix A = io.mapMatrix AF := by
      ext i k
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, hAij, AF, hχ]
      rfl
    rw [hA, ← RingHom.map_det, ← map_pow, hdF, map_intCast]
  have hu : IsUnit A.det := by
    have h := isUnit_of_not_dvd g hg hgV _ hd
    rw [← hdV] at h
    exact (isUnit_pow_iff two_ne_zero).1 h
  refine ⟨fun i τ => A⁻¹ (e'.symm τ) i, ?_, ?_⟩
  · intro σ τ
    have h1 := congrFun (congrFun (Matrix.nonsing_inv_mul A hu) (e'.symm τ)) (e'.symm σ)
    rw [Matrix.mul_apply, Matrix.one_apply] at h1
    simp only [hAij, Equiv.apply_symm_apply] at h1
    rw [show (∑ i, χ σ (bs i) * A⁻¹ (e'.symm τ) i) = ∑ i, A⁻¹ (e'.symm τ) i * χ σ (bs i) from
      Finset.sum_congr rfl fun _ _ => mul_comm _ _, h1]
    by_cases h : σ = τ
    · subst h; simp
    · rw [if_neg (fun h' => h (e'.symm.injective h').symm), if_neg h]
  · intro i i'
    have h1 := congrFun (congrFun (Matrix.mul_nonsing_inv A hu) i') i
    rw [Matrix.mul_apply, Matrix.one_apply] at h1
    simp only [hAij] at h1
    rw [← Equiv.sum_comp e' (fun τ => A⁻¹ (e'.symm τ) i * χ τ (bs i'))]
    simp only [Equiv.symm_apply_apply]
    rw [show (∑ k, A⁻¹ k i * χ (e' k) (bs i')) = ∑ k, χ (e' k) (bs i') * A⁻¹ k i from
      Finset.sum_congr rfl fun _ _ => mul_comm _ _, h1]
    by_cases h : i = i'
    · subst h; simp
    · rw [if_neg (Ne.symm h), if_neg h]

theorem red_bijective (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H)
    (c : Coeff l) (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (X : ValExt T p)
    (hp : UnramIn E p) : Function.Bijective (red io X) := by
  classical
  haveI : IsDomain X.O := X.ints.hom_inj.isDomain _
  obtain ⟨Cm, hAC, hCA⟩ := exists_inv_of_not_dvd_discr E (V := X.O) (Fr := X.C) X.ints.hom_inj
    (c.F.val : c.F →+* ℂ) (X.ιF.comp io) (embF c) (fun σ x => by simp [embF])
    (embO io X) (fun σ a => algebraMap_embO io X σ a) p Fact.out X.nonunit.out hp
  set b := RingOfIntegers.basis E
  let Cr : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → (E →+* ℂ) → ResidueField X.O := fun i τ => residue X.O (Cm i τ)
  have hAC' : ∀ σ τ, ∑ i, red io X σ (b i) * Cr i τ = if σ = τ then 1 else 0 := by
    intro σ τ
    have := congrArg (residue X.O) (hAC σ τ)
    simpa [map_sum, red, Cr, apply_ite (residue X.O)] using this
  have hCA' : ∀ i i', ∑ τ, Cr i τ * red io X τ (b i') = if i = i' then 1 else 0 := by
    intro i i'
    have := congrArg (residue X.O) (hCA i i')
    simpa [map_sum, red, Cr, apply_ite (residue X.O)] using this
  refine ⟨fun σ τ hst => ?_, fun χ => ?_⟩
  · by_contra hne
    have h1 := hAC' σ τ
    rw [if_neg hne, hst, hAC' τ τ, if_pos rfl] at h1
    exact one_ne_zero h1
  · let ρ : 𝓞 E →+* Module.End (ResidueField X.O) (ResidueField X.O) :=
      (Algebra.lmul (ResidueField X.O) (ResidueField X.O)).toRingHom.comp χ
    obtain ⟨mσ, hm, hs⟩ := ((decomp_of_inv ρ (red io X) b Cr hAC' hCA').1 1)
    obtain ⟨σ, hσ⟩ : ∃ σ, mσ σ ≠ 0 := by
      by_contra h
      simp only [not_exists, not_not] at h
      simp [h] at hs
    refine ⟨σ, RingHom.ext fun a => ?_⟩
    have : χ a * mσ σ = red io X σ a * mσ σ := hm σ a
    exact (mul_right_cancel₀ hσ this).symm

end GlobalTheory.PrimePart
