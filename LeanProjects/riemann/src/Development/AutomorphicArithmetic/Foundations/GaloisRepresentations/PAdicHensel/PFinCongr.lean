import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PadicUnitNorm

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

theorem UpperTheory.Gal.G1.pFinCongr :
    PadMap → LocRoot → TrivMat → CongrScale → SplitCongr → DefSign → FinCongr := by
  classical
  intro hPad hLoc hTriv hScale hSplit hD E _ _ _ A n p _ S B B' x x' t t' hT hT' s hs hloc w
  set D : ℤ := A.tr ^ 2 - 4 * A.nm with hDdef
  have hD0 : D ≠ 0 := ne_of_lt A.disc_neg
  set θ : E := (A.ω : E) - (A.bar A.ω : E) with hθdef
  have hθc : (IsCMField.complexConj E) θ = -θ := by
    rw [hθdef, map_sub, A.bar_eq, IsCMField.complexConj_apply_apply]
    ring
  have hθ2 : θ ^ 2 = (D : E) := by
    have h1 : ((A.ω + A.bar A.ω : 𝓞 E) : E) = ((A.tr : 𝓞 E) : E) := by rw [A.tr_eq]
    have h2 : ((A.ω * A.bar A.ω : 𝓞 E) : E) = ((A.nm : 𝓞 E) : E) := by rw [A.nm_eq]
    have c1 : ((A.tr : 𝓞 E) : E) = (A.tr : E) := map_intCast (algebraMap (𝓞 E) E) A.tr
    have c2 : ((A.nm : 𝓞 E) : E) = (A.nm : E) := map_intCast (algebraMap (𝓞 E) E) A.nm
    rw [c1] at h1
    rw [c2] at h2
    push_cast at h1 h2
    rw [hθdef, hDdef]
    push_cast
    linear_combination ((A.ω : E) + (A.bar A.ω : E) + (A.tr : E)) * h1 - 4 * h2
  obtain ⟨hM1, hM2, hM3⟩ := hD E A n p S B
  obtain ⟨hN1, hN2, hN3⟩ := hD E A n p S B'
  have hs0 : (s : E) ≠ 0 := by exact_mod_cast hs.ne'
  have hsym : ∀ a b, (IsCMField.complexConj E) (((s : E) • (mat S ↑B.β * (A.H n)⁻¹)) a b) =
      ((s : E) • (mat S ↑B.β * (A.H n)⁻¹)) b a := by
    intro a b
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul, map_ratCast, hM1 a b]
  have hdet : ((s : E) • (mat S ↑B.β * (A.H n)⁻¹)).det ≠ 0 := by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hs0) hM2
  obtain ⟨v, ι, hv⟩ := hPad (maximalRealSubfield E) w
  by_cases hvp : v.asIdeal = Ideal.span {(p : ℤ)}
  · have hpw : ((p : ℤ) : 𝓞 (maximalRealSubfield E)) ∈ w.asIdeal :=
      hv _ (by rw [hvp]; exact Ideal.subset_span rfl)
    obtain ⟨hnd, hr⟩ := (S.good).1
    obtain ⟨ρ, hρ, -⟩ := hLoc (maximalRealSubfield E) w A.tr A.nm p (Fact.out) (by exact_mod_cast hpw) hnd hr
    refine hSplit E n _ _ hsym hN1 hdet hN2 (HeightOneSpectrum.adicCompletion (maximalRealSubfield E) w)
      θ D hD0 hθc hθ2 (2 * (ρ : HeightOneSpectrum.adicCompletion (maximalRealSubfield E) w) - A.tr) ?_
    have hρ' := congrArg (fun z : HeightOneSpectrum.adicCompletionIntegers (maximalRealSubfield E) w =>
      (z : HeightOneSpectrum.adicCompletion (maximalRealSubfield E) w)) hρ
    push_cast at hρ'
    rw [hDdef]
    push_cast
    linear_combination 4 * hρ'
  · let v' : AwayP p := ⟨v, hvp⟩
    obtain ⟨a, b, hab⟩ := hloc v'
    let ψ : AfP p →+* HeightOneSpectrum.adicCompletion (maximalRealSubfield E) w :=
      ι.comp (AfP.eval v').toRingHom
    have hH' : (A.H n).map (cj E) = A.H n := by
      have h := congrArg Matrix.transpose (A.herm n)
      rw [Matrix.transpose_transpose] at h
      rw [h]
      exact Matrix.diagonal_transpose _
    obtain ⟨X, hX, hXeq⟩ := hTriv E n (A.H n) (A.herm n) hH' (A.det_ne n) (AfP p)
      (HeightOneSpectrum.adicCompletion (maximalRealSubfield E) w) ψ (mat S ↑B.β) x ↑t hT
    obtain ⟨X', hX', hXeq'⟩ := hTriv E n (A.H n) (A.herm n) hH' (A.det_ne n) (AfP p)
      (HeightOneSpectrum.adicCompletion (maximalRealSubfield E) w) ψ (mat S ↑B'.β) x' ↑t' hT'
    have ht0 : ψ ↑t' ≠ 0 := (t'.isUnit.map ψ).ne_zero
    have heq : ψ ↑t' = (s : HeightOneSpectrum.adicCompletion (maximalRealSubfield E) w) * ψ ↑t *
        (ι a ^ 2 - (D : HeightOneSpectrum.adicCompletion (maximalRealSubfield E) w) * ι b ^ 2) := by
      show ι (AfP.eval v' ↑t') = _
      rw [hab, map_mul, map_mul, map_sub, map_mul, map_pow, map_pow, map_intCast]
      congr 2
      exact eq_ratCast (ι.comp (algebraMap ℚ _)) s
    exact hScale E n (A.H n)⁻¹ _ _ (HeightOneSpectrum.adicCompletion (maximalRealSubfield E) w)
      θ D hθc hθ2 (ψ ↑t) (ψ ↑t') (ι a) (ι b) s ht0 heq X X' hX hX' hXeq hXeq'
