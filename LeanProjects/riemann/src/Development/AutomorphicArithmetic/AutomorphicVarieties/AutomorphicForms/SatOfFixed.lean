import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAveragingProjection
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactUnitaryIntegralPoints

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep

namespace UpperTheory.V.Af

theorem hasFixed_of_sum {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G V) (hσ : GlobalTheory.PRep.IsSmooth σ) (ρ : Representation ℂ G W)
    (K : Subgroup G) (hK : IsCompact (K : Set G))
    (h : ⨆ f : {f : V →ₗ[ℂ] W // ∀ g v, f (σ g v) = ρ g (f v)}, LinearMap.range f.1 = ⊤) (hf : HasFixed ρ K) :
    HasFixed σ K := by
  classical
  open GlobalTheory.OrbitAvg in
  by_contra hn
  obtain ⟨x, hx0, hx⟩ := hf
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have hfi : ∀ y, (stab σ K y).FiniteIndex := fun y => by
    have ho : IsOpen (stab σ K y : Set K) := (hσ y).preimage continuous_subtype_val
    haveI := (stab σ K y).quotient_finite_of_isOpen ho
    exact Subgroup.finiteIndex_of_finite_quotient
  have hz : ∀ y, avg σ K y = 0 := fun y => by
    by_contra h0
    exact hn ⟨_, h0, fun u hu => avg_invariant σ K (hfi y) ⟨u, hu⟩⟩
  have key : ∀ z ∈ (⊤ : Submodule ℂ W), (stab ρ K z).FiniteIndex ∧ avg ρ K z = 0 := fun z hz' => by
    rw [← h] at hz'
    refine Submodule.iSup_induction _ (motive := fun z => (stab ρ K z).FiniteIndex ∧ avg ρ K z = 0) hz' ?_ ?_ ?_
    · rintro ⟨f, hf⟩ _ ⟨y, rfl⟩
      haveI := hfi y
      have hle : stab σ K y ≤ stab ρ K (f y) := fun l hl => by
        rw [mem_stab] at hl ⊢
        rw [← hf, hl]
      refine ⟨Subgroup.finiteIndex_of_le hle, ?_⟩
      haveI := Fintype.ofFinite (K ⧸ stab σ K y)
      have := congrArg f (hz y)
      rw [avg_eq ρ K hle, ← map_zero f, ← this]
      simp only [avg, avgH, cv, finsum_eq_sum_of_fintype, map_smul, map_sum, hf]
    · have : stab ρ K (0 : W) = ⊤ := eq_top_iff.2 fun l _ => by rw [mem_stab, map_zero]
      have h1 : (stab ρ K (0 : W)).FiniteIndex := this ▸ inferInstance
      exact ⟨h1, avg_fixed ρ K h1 fun l _ => map_zero _⟩
    · rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
      exact ⟨Subgroup.finiteIndex_of_le (stab_le_add ρ K a b), by rw [avg_add ρ K ha hb, ha', hb', add_zero]⟩
  obtain ⟨h1, h2⟩ := key x trivial
  exact hx0 ((avg_fixed ρ K h1 hx).symm.trans h2)

variable {F : Type} [Field F] [NumberField F]

private def sInt (w : HeightOneSpectrum (𝓞 F)) : (w.adicCompletionIntegers F).toSubring →ₙ+* Ohat F where
  toFun x := ⟨sLoc F w x, Subring.mem_iInf.2 fun v => by
    classical
    change Pi.single (M := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) w (x : w.adicCompletion F) v ∈
      v.adicCompletionIntegers F
    by_cases hv : v = w
    · subst hv
      rw [Pi.single_eq_same]
      exact x.2
    · rw [Pi.single_eq_of_ne hv]
      exact zero_mem _⟩
  map_mul' x y := Subtype.ext (map_mul (sLoc F w) _ _)
  map_zero' := Subtype.ext (map_zero (sLoc F w))
  map_add' x y := Subtype.ext (map_add (sLoc F w) _ _)

private theorem sInt_natMul (w : HeightOneSpectrum (𝓞 F)) (M : ℕ) (x : (w.adicCompletionIntegers F).toSubring) :
    sInt w (M * x) = M * sInt w x := by
  rw [← nsmul_eq_mul, ← nsmul_eq_mul, map_nsmul]

private theorem isUnit_nat (w : HeightOneSpectrum (𝓞 F)) {M : ℕ} (hM : (M : 𝓞 F) ∉ w.asIdeal) :
    IsUnit (M : (w.adicCompletionIntegers F).toSubring) := by
  have h1 : Valued.v (M : w.adicCompletion F) = 1 := by
    have : (M : w.adicCompletion F) = algebraMap F _ (algebraMap (𝓞 F) F M) := by simp
    rw [this]
    have h2 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w (algebraMap (𝓞 F) F M)
    refine h2.trans ?_
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact (HeightOneSpectrum.intValuation_eq_one_iff).2 hM
  have h0 : (M : w.adicCompletion F) ≠ 0 := fun h => by simp [h] at h1
  refine IsUnit.of_mul_eq_one ⟨(M : w.adicCompletion F)⁻¹, ?_⟩ (Subtype.ext ?_)
  · change Valued.v (M : w.adicCompletion F)⁻¹ ≤ 1
    rw [map_inv₀, h1, inv_one]
  · simpa using mul_inv_cancel₀ h0

theorem locGL_mem_KLev (n : ℕ) (w : HeightOneSpectrum (𝓞 F)) {M : ℕ} (hM : (M : 𝓞 F) ∉ w.asIdeal)
    {k : GL (Fin n) (w.adicCompletion F)} (hk : k ∈ GlobalTheory.LFun.KGL w n) : locGL F n w k ∈ KLev F n M := by
  obtain ⟨k, rfl⟩ := hk
  refine ⟨cornerGL n (sInt w) k, map_cornerGL_of_zero _ _ (fun x => ?_) k, ?_⟩
  · obtain ⟨y, rfl⟩ := (isUnit_nat w hM).dvd (a := x)
    rw [sInt_natMul]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
  · ext i j : 2
    change ((1 : Matrix (Fin n) (Fin n) (Ohat F)) i j : Af F) - sLoc F w ((1 : Matrix (Fin n) (Fin n) (w.adicCompletionIntegers F).toSubring) i j) + sLoc F w _ =
      (1 : Matrix (Fin n) (Fin n) (Af F)) i j - sLoc F w ((1 : Matrix (Fin n) (Fin n) (w.adicCompletion F)) i j) + sLoc F w _
    by_cases h : i = j
    · subst h
      simp only [Matrix.one_apply_eq]
      rfl
    · simp only [Matrix.one_apply_ne h]
      rfl

theorem sat_of_isotypic (hS : SatLoc) {n M : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin n) (Af F)) V) (hρ : HasFixed ρ (KLev F n M)) (w : HeightOneSpectrum (𝓞 F))
    (hw : (M : 𝓞 F) ∉ w.asIdeal) (σ : SmIrr (GL (Fin n) (w.adicCompletion F))) (hi : LocIsotypic ρ w σ) :
    ∃ B, GlobalTheory.LFun.HasSatGL w (ρ.comp (locGL F n w)) B := by
  obtain ⟨h1, h2⟩ := hS F n w σ
  obtain ⟨x, hx0, hx⟩ := hρ
  have hK : IsCompact (GlobalTheory.LFun.KGL w n : Set (GL (Fin n) (w.adicCompletion F))) :=
    GlobalTheory.LFun.IntPtsUnitary.isCompact_GLint _ (PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F w)
  obtain ⟨B, hB⟩ := h1 (hasFixed_of_sum σ.ρ σ.smooth (ρ.comp (locGL F n w)) _ hK hi.2
    ⟨x, hx0, fun u hu => hx _ (locGL_mem_KLev n w hw hu)⟩)
  exact ⟨B, (h2 _ _ hi B).2 hB⟩

end UpperTheory.V.Af
