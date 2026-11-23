import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.IndexExponentDegree
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

noncomputable section

namespace GlobalTheory.PeriodIdealUnit

theorem not_dvd_different {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] {l : ℕ} (hl : l.Prime)
    (v : Ideal (𝓞 E)) [hvp : v.IsPrime] (hv : ((l : ℕ) : 𝓞 E) ∈ v) (h2 : ((l : ℕ) : 𝓞 E) ∉ v ^ 2) :
    ¬ v ∣ differentIdeal (𝓞 K) (𝓞 E) := by
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  have hmax : (Ideal.span {(l : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(l : ℤ)}) = Ideal.span {((l : ℕ) : 𝓞 E)} := by
    rw [Ideal.map_span]; simp
  have hle : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(l : ℤ)}) ≤ v := by
    rw [hmap, Ideal.span_le]; simpa using hv
  have : v.LiesOver (Ideal.span {(l : ℤ)}) :=
    ⟨hmax.eq_of_le (Ideal.comap_ne_top _ hvp.ne_top) (Ideal.map_le_iff_le_comap.mp hle)⟩
  have hb : Ideal.span {(l : ℤ)} ≠ ⊥ := by simpa using hl.ne_zero
  have he : v.ramificationIdx ℤ = 1 := by
    rw [← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(l : ℤ)}) v hb]
    by_contra hne
    rw [← ne_eq, Ideal.ramificationIdx'_ne_one_iff hle, hmap, Ideal.span_le] at hne
    exact h2 (by simpa using hne)
  have : Algebra.IsUnramifiedAt ℤ v := Ideal.ramificationIdx_eq_one_iff.1 he
  exact not_dvd_differentIdeal_iff.2 (Algebra.IsUnramifiedAt.of_restrictScalars ℤ v)

theorem locP_eq_one {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (I : Submodule (𝓞 E) E)
    (h1 : I ≤ localization₂ P.asIdeal (1 : Submodule (𝓞 E) E)) (h2 : ∃ n, n ∉ P.asIdeal ∧ n • (1 : E) ∈ I) :
    localization₂ P.asIdeal I = localization₂ P.asIdeal (1 : Submodule (𝓞 E) E) :=
  le_antisymm ((ThetaMove.localization_mono P h1).trans (localization_localization₂ P _).le)
    ((ThetaMove.localization_mono P (Submodule.one_le.2 h2 : (1 : Submodule (𝓞 E) E) ≤ localization₂ P.asIdeal I)).trans (localization_localization₂ P _).le)

theorem b_ne_zero (D : D7) :
    ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
  FractionalIdeal.coeIdeal_ne_zero.2 fun h => by
    have h3 := D.host.𝔟_spec.2
    simp [h] at h3

theorem one_mem_inv_b (D : D7) : (1 : D.host.E) ∈ D.host.AA0 := by
  refine (FractionalIdeal.mem_inv_iff (b_ne_zero D)).2 fun y hy => ?_
  rw [one_mul]; exact FractionalIdeal.coeIdeal_le_one hy

theorem locP_AA_eq_one : ∀ (X : Fields) (D : D7) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (P : HeightOneSpectrum (𝓞 X.E)), (Ideal.absNorm P.asIdeal).Prime → ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 X.E) ∉ P.asIdeal ^ 2 → Nat.Coprime (Ideal.absNorm cc) (Ideal.absNorm P.asIdeal) → localization₂ P.asIdeal (ambOf s B χ cD).AA = localization₂ P.asIdeal (1 : Submodule (𝓞 X.E) X.E) := by
  intro X D s cc δ B χ cD P hp h2 hc
  let e : 𝓞 D.host.E ≃+* 𝓞 X.E := RingOfIntegers.mapRingEquiv s.iE.symm
  have he : ∀ x : 𝓞 D.host.E, algebraMap (𝓞 X.E) X.E (e x) = s.iE.symm (algebraMap _ D.host.E x) := fun x => rfl
  have := P.isPrime
  let v : Ideal (𝓞 D.host.E) := P.asIdeal.comap (e : 𝓞 D.host.E →+* 𝓞 X.E)
  have hvp : v.IsPrime := Ideal.comap_isPrime _ _
  have hmem : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 X.E) ∈ P.asIdeal := Ideal.absNorm_mem _
  have hv1 : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 D.host.E) ∈ v := by
    rw [Ideal.mem_comap, map_natCast]; exact hmem
  have hv2 : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 D.host.E) ∉ v ^ 2 := fun h => by
    have h3 := Ideal.le_comap_pow (e : 𝓞 D.host.E →+* 𝓞 X.E) 2 h
    rw [Ideal.mem_comap, map_natCast] at h3
    exact h2 h3
  have hnd := not_dvd_different (K := D.host.K) hp v hv1 hv2
  have hnot : ¬ D.host.𝔟 ≤ v := fun hle => hnd (by
    rw [D.host.𝔟_spec.1]
    exact (Ideal.dvd_iff_le.2 hle).mul_right _)
  obtain ⟨z, hz, hzP⟩ := SetLike.not_le_iff_exists.1 hnot
  have hN : ((Ideal.absNorm cc : ℕ) : 𝓞 X.E) ∉ P.asIdeal := fun h => by
    have h3 : IsCoprime ((Ideal.absNorm cc : ℕ) : 𝓞 X.E) ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 X.E) := hc.cast
    obtain ⟨a, b, hab⟩ := h3
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (hab ▸ P.asIdeal.add_mem (P.asIdeal.mul_mem_left _ h) (P.asIdeal.mul_mem_left _ hmem)))
  refine locP_eq_one P _ ?_ ?_
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨c, -, t, ht, rfl⟩
    obtain ⟨w, hw⟩ := (FractionalIdeal.mem_one_iff _).1
      ((FractionalIdeal.mem_inv_iff (b_ne_zero D)).1 ht _ (FractionalIdeal.mem_coeIdeal_of_mem _ hz))
    refine ⟨e z, hzP, Submodule.mem_one.2 ⟨e (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c * w), ?_⟩⟩
    rw [Algebra.smul_def, he, he, ← map_mul, map_mul (algebraMap _ D.host.E), hw]
    congr 1
    have : algebraMap (𝓞 D.host.E) D.host.E (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c) = ((c : D.host.K) : D.host.E) := rfl
    rw [this]
    ring
  · refine ⟨_, hN, Submodule.subset_span ⟨((Ideal.absNorm cc : ℕ) : 𝓞 D.host.K), Ideal.absNorm_mem cc, 1, one_mem_inv_b D, ?_⟩⟩
    have h1 : (((((Ideal.absNorm cc : ℕ) : 𝓞 D.host.K) : D.host.K)) : D.host.E) = ((Ideal.absNorm cc : ℕ) : D.host.E) :=
      map_natCast ((algebraMap D.host.K D.host.E).comp (algebraMap (𝓞 D.host.K) D.host.K)) _
    rw [h1, mul_one, map_natCast, Algebra.smul_def, map_natCast, mul_one]

end GlobalTheory.PeriodIdealUnit
