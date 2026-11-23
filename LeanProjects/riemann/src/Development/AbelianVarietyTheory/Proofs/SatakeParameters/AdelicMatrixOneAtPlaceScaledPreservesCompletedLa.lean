import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeBasisHermitianSpace
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat
open Formalism.UG (bc prV)
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.AwayScale
variable {F : Type} [Field F] [NumberField F]

theorem scalar (v : HeightOneSpectrum (𝓞 F)) (a : FiniteAdeleRing (𝓞 F) F) (ha : a v = 0) (M : ℕ) (hM : 0 < M) :
    ∃ t : 𝓞 F, t ∉ v.asIdeal ∧ ∃ y ∈ Formalism.UG.intAd F,
      algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F t) * a =
        algebraMap F (FiniteAdeleRing (𝓞 F) F) (M : F) * y := by
  classical
  obtain ⟨b, hb0, hb⟩ := GlobalTheory.Idele.exists_mul_integral a
  set c : 𝓞 F := b * (M : 𝓞 F) with hc
  have hc0 : c ≠ 0 := mul_ne_zero hb0 (by exact_mod_cast hM.ne')
  have hfin : {w : HeightOneSpectrum (𝓞 F) | w.asIdeal ∣ Ideal.span {c}}.Finite :=
    Ideal.finite_factors (by simpa [Ideal.span_singleton_eq_bot] using hc0)
  let e : HeightOneSpectrum (𝓞 F) → ℕ := fun w => if w = v then 1 else
    (Associates.mk w.asIdeal).count (Associates.mk (Ideal.span {c})).factors
  obtain ⟨t, ht⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := insert v hfin.toFinset)
    (fun w => w.asIdeal) e (fun w _ => w.prime) (fun w _ w' _ h h' => h (HeightOneSpectrum.ext h'))
    (fun w => if (w : HeightOneSpectrum (𝓞 F)) = v then 1 else 0)
  have htv : t ∉ v.asIdeal := by
    intro h
    have h1 := ht v (Finset.mem_insert_self _ _)
    simp only [e, if_true, pow_one] at h1
    apply v.isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have h2 : (1 : 𝓞 F) = t - (t - 1) := by ring
    rw [h2]
    exact sub_mem h h1
  have hval : ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → w.intValuation t ≤ w.intValuation c := by
    intro w hw
    by_cases hws : w ∈ hfin.toFinset
    · have h1 := ht w (Finset.mem_insert_of_mem hws)
      simp only [hw, if_false, sub_zero, e] at h1
      rw [w.intValuation_if_neg hc0]
      exact (w.intValuation_le_pow_iff_mem t _).2 h1
    · have h1 : c ∉ w.asIdeal := by
        intro h; apply hws
        rw [Set.Finite.mem_toFinset]
        exact Ideal.dvd_span_singleton.2 h
      rw [(w.intValuation_eq_one_iff_mem_primeCompl c).2 h1]
      exact w.intValuation_le_one t
  have hcF : algebraMap (𝓞 F) F c ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)]; exact hc0
  have hbF : algebraMap (𝓞 F) F b ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)]; exact hb0
  have hMF : (M : F) ≠ 0 := by exact_mod_cast hM.ne'
  refine ⟨t, htv, algebraMap F _ (algebraMap (𝓞 F) F t / algebraMap (𝓞 F) F c) *
    (algebraMap F _ (algebraMap (𝓞 F) F b) * a), ?_, ?_⟩
  · intro w
    show (algebraMap F _ (algebraMap (𝓞 F) F t / algebraMap (𝓞 F) F c) *
      (algebraMap F _ (algebraMap (𝓞 F) F b) * a)) w ∈ w.adicCompletionIntegers F
    by_cases hw : w = v
    · subst hw
      rw [GlobalTheory.Idele.adele_mul_apply, GlobalTheory.Idele.adele_mul_apply, ha, mul_zero, mul_zero]
      exact zero_mem _
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers, GlobalTheory.Idele.adele_mul_apply, map_mul]
      refine mul_le_one' ?_ (hb w)
      rw [GlobalTheory.Idele.adele_algebraMap_apply, GlobalTheory.Idele.valued_algebraMap, map_div₀,
        HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
      rw [div_le_one₀ (by rw [pos_iff_ne_zero]; exact w.intValuation_ne_zero c hc0)]
      exact hval w hw
  · rw [← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul]
    congr 2
    rw [hc, map_mul, map_natCast]
    field_simp

theorem algebraMap_mem_intAd (r : 𝓞 F) :
    algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F r) ∈ Formalism.UG.intAd F := by
  intro w
  show algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F r) w ∈ w.adicCompletionIntegers F
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, GlobalTheory.Idele.adele_algebraMap_apply,
    GlobalTheory.Idele.valued_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
  exact w.intValuation_le_one r

theorem scalarFam (v : HeightOneSpectrum (𝓞 F)) {ι : Type} [Fintype ι] (a : ι → FiniteAdeleRing (𝓞 F) F)
    (ha : ∀ i, a i v = 0) (M : ℕ) (hM : 0 < M) :
    ∃ t : 𝓞 F, t ∉ v.asIdeal ∧ ∀ i, ∃ y ∈ Formalism.UG.intAd F,
      algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F t) * a i =
        algebraMap F (FiniteAdeleRing (𝓞 F) F) (M : F) * y := by
  classical
  choose t ht y hy he using fun i => scalar v (a i) (ha i) M hM
  have hT : ∏ i, t i ∈ v.asIdeal.primeCompl := Submonoid.prod_mem _ fun i _ => ht i
  refine ⟨∏ i, t i, hT, fun i => ?_⟩
  refine ⟨algebraMap F _ (algebraMap (𝓞 F) F (∏ j ∈ Finset.univ.erase i, t j)) * y i,
    mul_mem (algebraMap_mem_intAd _) (hy i), ?_⟩
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), map_mul, map_mul, mul_comm (algebraMap F _ _),
    mul_assoc, he i]
  ring

theorem prV_tmul {E : Type} [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (x : E)
    (a : FiniteAdeleRing (𝓞 F) F) : prV (E := E) v (x ⊗ₜ[F] a) = x ⊗ₜ[F] a v := by
  show (Algebra.TensorProduct.map (AlgHom.id F E) (Formalism.UG.evalV F v)) (x ⊗ₜ[F] a) = _
  rw [Algebra.TensorProduct.map_tmul]
  rfl

theorem basis_coeff {E N : Type} [Field E] [AddCommGroup N] [Module F N] [Algebra F E] {d : ℕ}
    (bE : Module.Basis (Fin d) F E) (x : Fin d → N) (k : Fin d) :
    TensorProduct.equivFinsuppOfBasisLeft bE (∑ j, bE j ⊗ₜ[F] x j) k = x k := by
  classical
  simp [map_sum, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply, Module.Basis.repr_self,
    Finsupp.single_apply]

theorem basis_expand {E N : Type} [Field E] [AddCommGroup N] [Module F N] [Algebra F E] {d : ℕ}
    (bE : Module.Basis (Fin d) F E) (z : E ⊗[F] N) :
    z = ∑ j, bE j ⊗ₜ[F] TensorProduct.equivFinsuppOfBasisLeft bE z j := by
  classical
  have h := TensorProduct.equivFinsuppOfBasisLeft_symm_apply bE (TensorProduct.equivFinsuppOfBasisLeft bE z)
  rw [LinearEquiv.symm_apply_apply, Finsupp.sum_fintype _ _ (by simp)] at h
  exact h

theorem tensorFam {E : Type} [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F))
    {ι : Type} [Fintype ι] (m : ι → E ⊗[F] FiniteAdeleRing (𝓞 F) F) (hm : ∀ i, prV (E := E) v (m i) = 0)
    (M : ℕ) (hM : 0 < M) :
    ∃ t : 𝓞 F, t ∉ v.asIdeal ∧ ∀ i, ∃ y ∈ Formalism.L2.Herm.intAf F E,
      Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((algebraMap (𝓞 F) (𝓞 E) t : 𝓞 E) : E) * m i =
        Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (M : E) * y := by
  classical
  let bE := Module.finBasis F E
  obtain ⟨c, hc0, hcb⟩ := GlobalTheory.LatAdelicBasis.exists_nat_multiples (Finset.univ.image bE)
  choose o ho using fun j => hcb (bE j) (Finset.mem_image_of_mem _ (Finset.mem_univ j))
  let a : ι × Fin (Module.finrank F E) → FiniteAdeleRing (𝓞 F) F :=
    fun p => TensorProduct.equivFinsuppOfBasisLeft bE (m p.1) p.2
  have hexp : ∀ i, m i = ∑ j, bE j ⊗ₜ[F] a (i, j) := fun i => basis_expand bE (m i)
  have ha : ∀ p, a p v = 0 := by
    intro p
    have h := hm p.1
    rw [hexp p.1, map_sum] at h
    simp only [prV_tmul] at h
    have := congrArg (fun z => TensorProduct.equivFinsuppOfBasisLeft bE z p.2) h
    simp only [basis_coeff, map_zero, Finsupp.coe_zero, Pi.zero_apply] at this
    exact this
  obtain ⟨t, ht, hty⟩ := scalarFam v a ha (M * c) (Nat.mul_pos hM hc0)
  choose y hy he using hty
  refine ⟨t, ht, fun i => ⟨∑ j, (algebraMap (𝓞 E) E (o j) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) *
      ((1 : E) ⊗ₜ[F] y (i, j)), ?_, ?_⟩⟩
  · exact sum_mem fun j _ => mul_mem (GlobalTheory.LatAdelicBasis.left_mem F E (o j))
      (GlobalTheory.LatAdelicBasis.right_mem F E (y (i, j)) (hy (i, j)))
  · have htE : ((algebraMap (𝓞 F) (𝓞 E) t : 𝓞 E) : E) = algebraMap F E (algebraMap (𝓞 F) F t) := rfl
    rw [hexp i, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Formalism.UG.inclE, Algebra.TensorProduct.includeLeftRingHom_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    rw [htE, ← ho j, ← Algebra.smul_def, TensorProduct.smul_tmul, Algebra.smul_def, he (i, j)]
    rw [← Algebra.smul_def, ← TensorProduct.smul_tmul, Algebra.smul_def]
    congr 1
    rw [Nat.cast_mul, map_mul, map_natCast, map_natCast]
    ring

end GlobalTheory.AwayScale

theorem GlobalTheory.AwayScale.main : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    (Lb : Submodule (𝓞 E) (Fin N → E)), Lb.FG → Submodule.span E (Lb : Set (Fin N → E)) = ⊤ →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (k : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)), bc (prV (E := E) v) k = 1 →
    ∃ t : 𝓞 F, t ∉ v.asIdeal ∧ ∀ z ∈ Formalism.L2.Herm.hatL (F := F) Lb,
      Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((algebraMap (𝓞 F) (𝓞 E) t : 𝓞 E) : E) •
        ((k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ z) ∈ Formalism.L2.Herm.hatL (F := F) Lb := by
  intro F E _ _ _ _ _ N Lb hfg hsp v k hk
  classical
  obtain ⟨n, hn0, hn1, hn2⟩ := GlobalTheory.LatAdelicBasis.exists_level Lb hfg hsp
  let ι := Formalism.UG.inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  let K : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := (k : Matrix _ _ _)
  let m : Fin N × Fin N → E ⊗[F] FiniteAdeleRing (𝓞 F) F := fun p => (K - 1) p.1 p.2
  have hK : K.map (prV (E := E) v) = 1 := congrArg Units.val hk
  have hm : ∀ p, prV (E := E) v (m p) = 0 := by
    intro p
    have h1 : (K - 1).map (prV (E := E) v) = 0 := by
      rw [Matrix.map_sub _ (fun a b => map_sub _ a b), hK, Matrix.map_one _ (map_zero _) (map_one _), sub_self]
    exact congrFun (congrFun h1 p.1) p.2
  obtain ⟨t, ht, hty⟩ := GlobalTheory.AwayScale.tensorFam v m hm (n * n) (Nat.mul_pos hn0 hn0)
  choose y hy he using hty
  refine ⟨t, ht, fun z hz => ?_⟩
  have hι : ∀ o : 𝓞 E, ι (algebraMap (𝓞 E) E o) ∈ Formalism.L2.Herm.intAf F E :=
    fun o => GlobalTheory.LatAdelicBasis.left_mem F E o

  have hZ : ∀ w ∈ Formalism.L2.Herm.hatL (F := F) Lb, ∀ i, ι (n : E) * w i ∈ Formalism.L2.Herm.intAf F E := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨x, hx, rfl⟩ := hw
      intro i
      obtain ⟨o, ho⟩ := hn2 x hx i
      show ι (n : E) * ι (x i) ∈ _
      rw [← map_mul, ho]
      exact hι o
    | zero => intro i; simp
    | add w w' _ _ hw hw' => intro i; rw [Pi.add_apply, mul_add]; exact add_mem (hw i) (hw' i)
    | smul r w _ hw =>
      intro i
      rw [Subring.smul_def, Pi.smul_apply, smul_eq_mul, mul_left_comm]
      exact mul_mem r.2 (hw i)

  have hW : ∀ w : Fin N → E ⊗[F] FiniteAdeleRing (𝓞 F) F,
      (∀ i, ∃ u ∈ Formalism.L2.Herm.intAf F E, w i = ι (n : E) * u) → w ∈ Formalism.L2.Herm.hatL (F := F) Lb := by
    intro w hw
    choose u hu hwu using hw
    have hw' : w = ∑ i, (⟨u i, hu i⟩ : Formalism.L2.Herm.intAf F E) •
        (fun l => ι (((n : E) • (Pi.single i 1 : Fin N → E)) l)) := by
      funext l
      rw [Finset.sum_apply, Finset.sum_eq_single l]
      · rw [Subring.smul_def, Pi.smul_apply, smul_eq_mul, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one,
          hwu l, mul_comm]
      · intro i _ hil
        rw [Subring.smul_def, Pi.smul_apply, Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hil), smul_zero, map_zero,
          smul_zero]
      · intro h; exact absurd (Finset.mem_univ l) h
    rw [hw']
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hn1 i, rfl⟩)
  have htE : ι ((algebraMap (𝓞 F) (𝓞 E) t : 𝓞 E) : E) ∈ Formalism.L2.Herm.intAf F E := hι _
  have hsplit : K *ᵥ z = z + (K - 1) *ᵥ z := by rw [Matrix.sub_mulVec, Matrix.one_mulVec, add_sub_cancel]
  show ι ((algebraMap (𝓞 F) (𝓞 E) t : 𝓞 E) : E) • (K *ᵥ z) ∈ _
  rw [hsplit, smul_add]
  refine add_mem ?_ ?_
  · have := (Formalism.L2.Herm.hatL (F := F) Lb).smul_mem (⟨_, htE⟩ : Formalism.L2.Herm.intAf F E) hz
    rwa [Subring.smul_def] at this
  · refine hW _ fun i => ?_
    have hent : (ι ((algebraMap (𝓞 F) (𝓞 E) t : 𝓞 E) : E) • ((K - 1) *ᵥ z)) i =
        ι (n : E) * ∑ j, y (i, j) * (ι (n : E) * z j) := by
      rw [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have h1 := he (i, j)
      rw [← mul_assoc]
      change ι _ * m (i, j) * z j = _
      rw [h1, Nat.cast_mul, map_mul]
      ring
    exact ⟨_, sum_mem fun j _ => mul_mem (hy (i, j)) (hZ z hz j), hent⟩
