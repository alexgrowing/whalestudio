import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CqStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatFrob
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocCompC
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp

open UpperTheory.V.Af

namespace UpperTheory.V.Br

private theorem inv_mem_eig {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} {h : IsPlaceOver A w} (x : WD h) (φ : Weil h) {b : ℂ}
    (hb : (x.charPol φ⁻¹).IsRoot b) : b ≠ 0 ∧ b⁻¹ ∈ x.eig φ := by
  obtain ⟨n, a, rfl⟩ := WD.exists_rep x
  rw [WD.charPol_mk, ← Module.End.hasEigenvalue_iff_isRoot_charpoly] at hb
  obtain ⟨v, hv⟩ := hb.exists_hasEigenvector
  have h1 : v = b • a.ρ φ v := by
    rw [← map_smul, ← hv.apply_eq_smul, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hv.2 (by simpa using h1)
  refine ⟨hb0, ?_⟩
  rw [WD.eig_mk, mem_roots (LinearMap.charpoly_monic _).ne_zero, ← Module.End.hasEigenvalue_iff_isRoot_charpoly]
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := v) ⟨Module.End.mem_eigenspace_iff.2 ?_, hv.2⟩
  conv_rhs => rw [h1]
  rw [smul_smul, inv_mul_cancel₀ hb0, one_smul]

private theorem norm_of_pure {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {n : ℕ} {r : G F Ω →* GL (Fin n) (Qbar l)}
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} {h : IsPlaceOver A w} (hl : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal)
    {B : Multiset ℂ} (hB : FrobEig ι r w B) {x : WD h} (hx : IsWDOf ι r x) {s : ℝ} (ht : (x.lpTw s).tempered) :
    ∀ b ∈ B, ‖b‖ = (normV w : ℝ) ^ s := by
  intro b hb
  obtain ⟨hu, hf⟩ := hB A h
  have e := hx.wdOf_eq hl
  obtain ⟨t, ht', φ, hφ, N, a, hN, -, -⟩ := id hx
  have hxu : x.unr := e ▸ (hN.unr_wdOf_iff hl ht' ι).2 hu
  have hc := hN.charPol_wdOf (h := h) hl ht' ι (frob h)⁻¹
  rw [e] at hc
  have hr : (x.charPol (frob h)⁻¹).IsRoot b := by
    rw [hc]
    erw [hf _ isFrob_frob]
    have := (mem_roots (Polynomial.monic_multiset_prod_of_monic B (fun b => X - C b)
      fun b _ => monic_X_sub_C b).ne_zero).1 ((roots_multiset_prod_X_sub_C B).symm ▸ hb)
    exact this
  obtain ⟨hb0, hm⟩ := inv_mem_eig x _ hr
  have h1 := (WD.tempered_unr _ ((WD.unr_tw x s).2 hxu)).1 ht (b⁻¹ * ((normV w : ℕ) : ℂ) ^ ((s : ℝ) : ℂ)) (by
    rw [WD.frobEig_tw x s hxu]
    exact Multiset.mem_map_of_mem _ hm)
  rw [norm_mul, norm_inv, Complex.norm_natCast_cpow_of_pos (zero_lt_one.trans (GlobalTheory.WeilDeligne.one_lt_normV w)), Complex.ofReal_re,
    inv_mul_eq_one₀ (norm_ne_zero_iff.2 hb0)] at h1
  exact h1

private theorem wt_eq {n : ℕ} (hn : 1 ≤ n) {m : Fin n → ℤ} {wt wt' : ℤ} (hm : ∀ i, m i + m i.rev = wt) {H : Multiset ℤ}
    (h1 : H.map (fun n : ℤ => (n : ℂ)) = (infOf m).map fun z => ((n : ℂ) - 1) / 2 - z) (h2 : H = H.map (wt' - ·)) :
    wt' = -wt := by
  have e : H = Finset.univ.val.map fun i => -m i := by
    refine Multiset.map_injective (Int.cast_injective (α := ℂ)) ?_
    rw [h1, infOf, Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl fun i _ => ?_
    simp
  have s1 := congrArg Multiset.sum h2
  rw [e, Multiset.map_map] at s1
  change ∑ i, -m i = ∑ i, (wt' - -m i) at s1
  have s2 : ∑ i : Fin n, (m i + m i.rev) = ∑ _i : Fin n, wt := Finset.sum_congr rfl fun i _ => hm i
  have s3 : ∑ i : Fin n, m i.rev = ∑ i, m i := Equiv.sum_comp Fin.revPerm m
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, s3] at s1 s2
  have hn' : (n : ℤ) ≠ 0 := by omega
  refine mul_left_cancel₀ hn' ?_
  linarith

private theorem exists_prime_not_mem {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) :
    ∃ l : ℕ, l.Prime ∧ ((l : ℕ) : 𝓞 K) ∉ w.asIdeal := by
  by_contra H
  push_neg at H
  have h2 := H 2 Nat.prime_two
  have h3 := H 3 Nat.prime_three
  refine w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
  have := w.asIdeal.sub_mem h3 h2
  norm_num at this
  exact this

end UpperTheory.V.Br

theorem UpperTheory.V.Br.pureP :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Br.PureP := by
  intro P K _ _ _ n hn m wt hm hwt M π hπ w B hB
  obtain ⟨hinf, ⟨χ, hχ⟩, -⟩ := hπ
  obtain ⟨l, hlp, hl⟩ := UpperTheory.V.Br.exists_prime_not_mem w
  haveI : Fact l.Prime := ⟨hlp⟩
  obtain ⟨ι⟩ : Nonempty (Qbar l ≃+* ℂ) := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex l
  have hic : ∀ τ, (CG.mk π).infChar τ = UpperTheory.V.Af.infOf m := fun τ => CG.HasInfChar.infChar_eq (hinf τ)
  have hreg : (CG.mk π).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
    rw [hic]
    refine ⟨Finset.univ.nodup.map fun i j e => hm.injective ?_, fun z hz => ?_⟩
    · exact_mod_cast add_left_cancel e
    · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hz
      exact ⟨m i, add_comm _ _⟩
  obtain ⟨r, wt', HT, hr⟩ := P.litN.aut.gal K (AlgebraicClosure K) l ι n (by omega) π χ hreg hχ
  have hHT : ∀ τ, (HT τ).map (fun n : ℤ => (n : ℂ)) = (UpperTheory.V.Af.infOf m).map fun z => ((n : ℂ) - 1) / 2 - z := fun τ => by
    rw [hr.weights τ, hic]
  obtain ⟨τ₀⟩ : Nonempty (K →+* ℂ) := inferInstance
  have e : wt' = -wt := by
    refine UpperTheory.V.Br.wt_eq (by omega) hwt (hHT (ι.symm.toRingHom.comp τ₀)) ?_
    rw [← hr.weights_conj]
    exact Multiset.map_injective (Int.cast_injective (α := ℂ)) ((hHT _).trans (hHT _).symm)
  obtain ⟨⟨σ, hσ⟩, hiso⟩ := UpperTheory.V.Af.locCompC P K n π w
  have hs := ((UpperTheory.V.Af.satLoc P K n w σ).2 _ π.finPart (hiso σ hσ) B).1 hB
  have hF := UpperTheory.V.Af.satFrob P K (AlgebraicClosure K) l ι n r hr.cont w hl σ B hs
    fun A h rc hrc => hr.away w hl A h rc hrc σ hσ
  obtain ⟨A, hA⟩ := exists_isPlaceOver (AlgebraicClosure K) w
  obtain ⟨x, hx, ht⟩ := hr.pure w hl A hA
  have := UpperTheory.V.Br.norm_of_pure hl hF hx ht
  rw [e] at this
  simpa using this
