import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProjectionRows.AsmBound

noncomputable section

namespace PI.DvRows

open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv Formalism.LFunctionChainParameters.LLcv

def Adapted : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K] [IsGalois ℚ K]
    (A : HLat K) (e : Module.End K A.V) (n : ℕ) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K), Hyp K A e n h →
    ∀ U : Submodule K A.V, U ≤ LinearMap.range e →
    ∃ (k d : ℕ) (u : Fin k → A.V) (z : Fin d → A.V) (y : Fin d → A.V),
      LinearIndependent K (Fin.append u z) ∧
      Submodule.span K (Set.range (Fin.append u z)) = LinearMap.range e ∧
      Submodule.span K (Set.range u) = U ∧
      (∀ i, Fin.append u z i ∈ cutE A e A.L) ∧
      LinearIndependent K y ∧ (∀ i, y i ∈ lamSub A e h U) ∧
      Submodule.span K (lamSub A e h U : Set A.V) = Submodule.span K (Set.range y) ∧
      (cutE A e A.L).FG ∧ (cutE A e A.L ⊓ U.restrictScalars (𝓞 K)).FG ∧
      Submodule.span K (cutE A e A.L : Set A.V) = Submodule.span K (Set.range (Fin.append u z)) ∧
      Submodule.span K ((cutE A e A.L ⊓ U.restrictScalars (𝓞 K) : Submodule (𝓞 K) A.V) : Set A.V) =
        Submodule.span K (Set.range u)

lemma linInd_left {K V : Type} [Field K] [AddCommGroup V] [Module K V] {k d : ℕ} (u : Fin k → V)
    (z : Fin d → V) (h : LinearIndependent K (Fin.append u z)) : LinearIndependent K u := by
  have : u = Fin.append u z ∘ Fin.castAdd d := by funext i; simp
  rw [this]
  exact h.comp _ (Fin.castAdd_injective k d)

theorem degDual_of (hFG : LamFG) (hAd : Adapted) (hAI : ArchIdentity) (hLP : LocalPairing)
    (hCP : ConjPrime) (hNF : NormFinsum) : DegDual := by
  intro K _ _ _ _ _ A e n h hS hP hH hC U hU
  have hyp : Hyp K A e n h := ⟨hS, hP, hH, hC⟩
  obtain ⟨k, d, u, z, y, hlin, hspz, hspu, hzM, hy, hyM, hspy, hMfg, hSfg, hspM, hspS⟩ :=
    hAd K A e n h hyp U hU
  have hfg := hFG K A e n h hyp U hU
  have hu : LinearIndependent K u := linInd_left u z hlin
  set M := cutE A e A.L with hM
  set S := cutE A e A.L ⊓ U.restrictScalars (𝓞 K) with hS'
  set Λ := lamSub A e h U with hΛ
  rw [degL_eq_neg_lcv A hP.1 S hSfg u hu hspS, degL_eq_neg_lcv A hP.1 M hMfg _ hlin hspM,
    degL_eq_neg_lcv A hP.1 Λ hfg y hy hspy]
  have hyU : ∀ i, ∀ x ∈ U, h (y i) x = 0 := fun i => (hyM i).2.1
  have hye : ∀ i, y i ∈ LinearMap.range e := fun i => (hyM i).1
  have harch := hAI K A e n h hyp U hU k d u z y hlin hspz hspu hy hye hyU
  obtain ⟨c, hcinv, hc⟩ := hCP K
  have hlwc : ∀ w, lw K (c w) = lw K w := fun w => by unfold lw; rw [(hc w).2]
  set D := (Matrix.of fun i j => h (y i) (z j)).det with hD
  set zf := Fin.append u z with hzf
  set Ly := Submodule.span (𝓞 K) (Set.range y)
  set Lz := Submodule.span (𝓞 K) (Set.range zf)
  set Lu := Submodule.span (𝓞 K) (Set.range u)
  have hloc : ∀ w, (vAdd w D : ℝ) + (Formalism.HermitianLatticesTheory.lidx (c w).asIdeal Ly Λ : ℝ) +
      (Formalism.HermitianLatticesTheory.lidx w.asIdeal Lz M : ℝ) - (Formalism.HermitianLatticesTheory.lidx w.asIdeal Lu S : ℝ) = 0 := by
    intro w
    have := hLP K A e n h hyp U hU k d u z y hlin hspz hspu hzM hy hyM hspy w (c w) (hc w).1
    exact_mod_cast this

  have fV := vAdd_support_finite (K := K) D
  have fY := lidx_support_finite A hP.1 Λ hfg y hy hspy
  have fZ := lidx_support_finite A hP.1 M hMfg zf hlin hspM
  have fU := lidx_support_finite A hP.1 S hSfg u hu hspS
  set a : HeightOneSpectrum (𝓞 K) → ℝ := fun w => lw K w * (vAdd w D : ℝ)
  set gy : HeightOneSpectrum (𝓞 K) → ℝ := fun w => lw K w * (Formalism.HermitianLatticesTheory.lidx w.asIdeal Ly Λ : ℝ)
  set gz : HeightOneSpectrum (𝓞 K) → ℝ := fun w => lw K w * (Formalism.HermitianLatticesTheory.lidx w.asIdeal Lz M : ℝ)
  set gu : HeightOneSpectrum (𝓞 K) → ℝ := fun w => lw K w * (Formalism.HermitianLatticesTheory.lidx w.asIdeal Lu S : ℝ)
  have sub : ∀ {x : HeightOneSpectrum (𝓞 K) → ℤ}, (Function.support x).Finite →
      (Function.support fun w => lw K w * (x w : ℝ)).Finite := fun hx =>
    hx.subset (fun w hw => by
      simp only [Function.mem_support] at hw ⊢
      intro h0; apply hw; rw [h0]; simp)
  have fa : (Function.support a).Finite := sub fV
  have fgy : (Function.support gy).Finite := sub fY
  have fgz : (Function.support gz).Finite := sub fZ
  have fgu : (Function.support gu).Finite := sub fU
  have fgyc : (Function.support fun w => gy (c w)).Finite :=
    (fgy.preimage (hcinv.injective.injOn)).subset (fun w hw => hw)
  have hsum0 : (∑ᶠ w, (a w + gy (c w) + gz w - gu w)) = 0 := by
    have : (fun w => a w + gy (c w) + gz w - gu w) = fun _ => (0 : ℝ) := by
      funext w
      simp only [a, gy, gz, gu]
      rw [hlwc w]
      have := hloc w
      linear_combination lw K w * this
    rw [this, finsum_zero]
  have hsym : (∑ᶠ w, gy (c w)) = ∑ᶠ w, gy w := by
    have : (fun w => gy (c w)) = fun w => gy (Function.Involutive.toPerm c hcinv w) := by
      funext w; simp
    rw [this]
    exact finsum_comp_equiv (Function.Involutive.toPerm c hcinv)
  have hsplit : (∑ᶠ w, (a w + gy (c w) + gz w - gu w)) =
      (∑ᶠ w, a w) + (∑ᶠ w, gy (c w)) + (∑ᶠ w, gz w) - ∑ᶠ w, gu w := by
    rw [finsum_sub_distrib ((fa.union fgyc).union fgz |>.subset ?_) fgu,
      finsum_add_distrib ((fa.union fgyc).subset (Function.support_add _ _)) fgz,
      finsum_add_distrib fa fgyc]
    intro w hw
    simp only [Function.mem_support] at hw
    by_contra hn
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hn
    apply hw
    rw [hn.1.1, hn.1.2, hn.2]; ring
  rw [hsplit, hsym] at hsum0

  have hnorm : Real.log |((Algebra.norm ℚ D : ℚ) : ℝ)| / (Module.finrank ℚ K : ℝ) = ∑ᶠ w, a w := by
    by_cases hD0 : D = 0
    · simp only [a]
      rw [hD0]
      simp [vAdd]
    · exact (hNF K D hD0).symm
  unfold lcv lcvInf
  rw [lcvFin_eq A u, lcvFin_eq A zf, lcvFin_eq A y]
  have hk := finrank_eq_two_nPl (K := K)
  have hnpos : (0 : ℝ) < Formalism.HN.nPl K := by
    unfold Formalism.HN.nPl
    exact_mod_cast Fintype.card_pos
  rw [hk] at hnorm
  have e1 : (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (Formalism.HN.gramPl A.b A.X v zf).det.re -
      (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (Formalism.HN.gramPl A.b A.X v u).det.re =
      2 * (∑ᶠ w, a w) - (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (Formalism.HN.gramPl A.b A.X v y).det.re := by
    rw [← hnorm, ← harch]
    field_simp
    ring
  change -((1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (Formalism.HN.gramPl A.b A.X v u).det.re + 2 * ∑ᶠ w, gu w) -
      -((1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (Formalism.HN.gramPl A.b A.X v zf).det.re + 2 * ∑ᶠ w, gz w) =
      -((1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (Formalism.HN.gramPl A.b A.X v y).det.re + 2 * ∑ᶠ w, gy w)
  linarith

theorem partB_of_pieces (hFG : LamFG) (hAd : Adapted) (hCS : GramCS) (hAI : ArchIdentity)
    (hLG : LocalGamma) (hLP : LocalPairing) (hCP : ConjPrime) (hNF : NormFinsum) : PartB :=
  partB_of (degDual_of hFG hAd hAI hLP hCP hNF) (degDualBound_of hFG hCS hLG hCP hNF)

theorem dvProjRows_of_pieces (hFG : LamFG) (hAd : Adapted) (hCS : GramCS) (hAI : ArchIdentity)
    (hLG : LocalGamma) (hLP : LocalPairing) (hCP : ConjPrime) (hNF : NormFinsum) : PI.Dv.division_rows_base_level :=
  dvProjRows_of (partB_of_pieces hFG hAd hCS hAI hLG hLP hCP hNF)

end PI.DvRows
