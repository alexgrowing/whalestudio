import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLeadIdealDim
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

variable {n : ℕ}

theorem leadForm_ne_zero {f : MvPolynomial (Fin n) ℂ} (hf : f ≠ 0) : leadForm f ≠ 0 := by
  obtain ⟨d, hd, hdeg⟩ := Finset.exists_mem_eq_sup f.support (support_nonempty.mpr hf)
    (fun m => m.sum fun _ e => e)
  intro h0
  have hc := congrArg (coeff d) h0
  rw [leadForm, coeff_homogeneousComponent, coeff_zero] at hc
  rw [if_pos (by rw [totalDegree, hdeg]; rfl)] at hc
  exact (mem_support_iff.mp hd) hc

theorem vars_leadForm_subset (f : MvPolynomial (Fin n) ℂ) : (leadForm f).vars ⊆ f.vars := by
  intro i hi
  rw [mem_vars_iff_mem_support] at hi ⊢
  obtain ⟨d, hd, hid⟩ := hi
  refine ⟨d, ?_, hid⟩
  rw [mem_support_iff, leadForm, coeff_homogeneousComponent] at hd
  rw [mem_support_iff]
  split_ifs at hd
  · exact hd
  · exact absurd rfl hd

theorem aeval_mk_X (I : Ideal (MvPolynomial (Fin n) ℂ)) (u : Set (Fin n))
    (q : MvPolynomial u ℂ) :
    aeval (fun i : u => Ideal.Quotient.mk I (X (i : Fin n))) q =
      Ideal.Quotient.mk I (rename Subtype.val q) := by
  induction q using MvPolynomial.induction_on with
  | C a => rw [aeval_C, rename_C]; rfl
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

theorem algebraicIndependent_mk_X_iff (I : Ideal (MvPolynomial (Fin n) ℂ)) (u : Set (Fin n)) :
    AlgebraicIndependent ℂ (fun i : u => Ideal.Quotient.mk I (X (i : Fin n))) ↔
      ∀ q : MvPolynomial u ℂ, rename Subtype.val q ∈ I → q = 0 := by
  rw [algebraicIndependent_iff]
  simp only [aeval_mk_X, Ideal.Quotient.eq_zero_iff_mem]

theorem rename_mem_of_leadIdeal (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Set (Fin n))
    (h : ∀ q : MvPolynomial u ℂ, rename Subtype.val q ∈ leadIdeal J → q = 0)
    (q : MvPolynomial u ℂ) (hq : rename Subtype.val q ∈ J) : q = 0 := by
  by_contra hq0
  have hf : rename Subtype.val q ≠ 0 := by
    rwa [Ne, ← map_zero (rename (Subtype.val : u → Fin n)),
      (rename_injective _ Subtype.val_injective).eq_iff]
  have hvars : ((leadForm (rename Subtype.val q)).vars : Set (Fin n)) ⊆
      Set.range (Subtype.val : u → Fin n) := by
    intro i hi
    obtain ⟨j, -, rfl⟩ := mem_vars_rename _ _ (vars_leadForm_subset _ hi)
    exact ⟨j, rfl⟩
  obtain ⟨r, hr⟩ := exists_rename_eq_of_vars_subset_range _ _ Subtype.val_injective hvars
  have hr0 : r = 0 := h r (hr ▸ Ideal.subset_span ⟨_, hq, rfl⟩)
  exact leadForm_ne_zero hf (by rw [← hr, hr0, map_zero])

theorem quotient_dim_le_of_minimalPrimes {R : Type*} [CommRing R] (I : Ideal R)
    {N : WithBot ℕ∞} (h : ∀ Z ∈ I.minimalPrimes, ringKrullDim (R ⧸ Z) ≤ N) :
    ringKrullDim (R ⧸ I) ≤ N := by
  rw [ringKrullDim_quotient, Order.krullDim_eq_iSup_coheight, iSup_le_iff]
  intro a
  obtain ⟨Z, hZ, hZa⟩ :=
    Ideal.exists_minimalPrimes_le ((PrimeSpectrum.mem_zeroLocus _ _).mp a.2)
  have : Z.IsPrime := hZ.1.1
  let z : PrimeSpectrum.zeroLocus (R := R) (I : Set R) :=
    ⟨⟨Z, inferInstance⟩, (PrimeSpectrum.mem_zeroLocus _ _).mpr hZ.1.2⟩
  have hza : z ≤ a := hZa
  let e : Set.Ici z ↪o PrimeSpectrum.zeroLocus (R := R) (Z : Set R) :=
    OrderEmbedding.ofMapLEIff
      (fun x => ⟨x.1.1, (PrimeSpectrum.mem_zeroLocus _ _).mpr (show Z ≤ x.1.1.asIdeal from x.2)⟩)
      fun _ _ => Iff.rfl
  calc ((Order.coheight a : ℕ∞) : WithBot ℕ∞) ≤ ((Order.coheight z : ℕ∞) : WithBot ℕ∞) :=
        WithBot.coe_le_coe.mpr (Order.coheight_anti hza)
    _ = Order.krullDim (Set.Ici z) := Order.coheight_eq_krullDim_Ici z
    _ ≤ Order.krullDim (PrimeSpectrum.zeroLocus (R := R) (Z : Set R)) :=
        Order.krullDim_le_of_orderEmbedding e
    _ = ringKrullDim (R ⧸ Z) := (ringKrullDim_quotient Z).symm
    _ ≤ N := h Z hZ

theorem exists_vars_isTranscendenceBasis (P : Ideal (MvPolynomial (Fin n) ℂ)) [P.IsPrime] :
    ∃ u : Set (Fin n), AlgebraicIndependent ℂ (fun i : u => Ideal.Quotient.mk P (X (i : Fin n))) ∧
      Cardinal.mk u = Algebra.trdeg ℂ (MvPolynomial (Fin n) ℂ ⧸ P) := by
  set x : Fin n → MvPolynomial (Fin n) ℂ ⧸ P := fun i => Ideal.Quotient.mk P (X i) with hx
  have hrange : Set.range x = Ideal.Quotient.mkₐ ℂ P '' Set.range X := by
    rw [← Set.range_comp]; rfl
  have hadj : Algebra.adjoin ℂ (Set.range x) = ⊤ := by
    rw [hrange, ← AlgHom.map_adjoin, MvPolynomial.adjoin_range_X, Algebra.map_top,
      AlgHom.range_eq_top]
    exact Ideal.Quotient.mkₐ_surjective ℂ P
  have _ : Algebra.IsAlgebraic (Algebra.adjoin ℂ (Set.range x)) (MvPolynomial (Fin n) ℂ ⧸ P) :=
    ⟨fun a => isAlgebraic_algebraMap (R := Algebra.adjoin ℂ (Set.range x))
      (⟨a, hadj ▸ Algebra.mem_top⟩ : Algebra.adjoin ℂ (Set.range x))⟩
  have _ := (faithfulSMul_iff_algebraMap_injective ℂ (MvPolynomial (Fin n) ℂ ⧸ P)).mpr
    (algebraMap ℂ _).injective
  obtain ⟨t, hts, ht⟩ := exists_isTranscendenceBasis_subset (R := ℂ) (Set.range x)
  obtain ⟨u, hu, hinj⟩ := Set.exists_image_eq_injOn_of_subset_range hts
  let g : u → t := fun i => ⟨x i, hu ▸ Set.mem_image_of_mem x i.2⟩
  have hg : Function.Injective g := fun i j hij =>
    Subtype.ext (hinj i.2 j.2 (congrArg Subtype.val hij))
  refine ⟨u, ht.1.comp g hg, ?_⟩
  rw [← ht.cardinalMk_eq_trdeg, ← hu, Cardinal.mk_image_eq_of_injOn _ _ hinj]

theorem LeadIdealDim.proof : LeadIdealDim.Statement := by
  intro n J
  apply quotient_dim_le_of_minimalPrimes
  intro P hP
  have _ : P.IsPrime := hP.1.1
  obtain ⟨u, hu, hcard⟩ := exists_vars_isTranscendenceBasis P
  have hJ : ∀ q : MvPolynomial u ℂ, rename Subtype.val q ∈ J → q = 0 :=
    rename_mem_of_leadIdeal J u fun q hq => (algebraicIndependent_mk_X_iff P u).mp hu q (hP.1.2 hq)

  let M : Submonoid (MvPolynomial (Fin n) ℂ) :=
    (nonZeroDivisors (MvPolynomial u ℂ)).map (rename (R := ℂ) (Subtype.val : u → Fin n))
  have hdis : Disjoint (J : Set (MvPolynomial (Fin n) ℂ)) M := by
    rw [Set.disjoint_left]
    rintro _ hJf ⟨q, hq, rfl⟩
    exact (mem_nonZeroDivisors_iff_ne_zero.mp hq) (hJ q hJf)
  obtain ⟨Q, hQ, hJQ, hQM⟩ := Ideal.exists_le_prime_disjoint J M hdis
  have hQu : AlgebraicIndependent ℂ (fun i : u => Ideal.Quotient.mk Q (X (i : Fin n))) := by
    rw [algebraicIndependent_mk_X_iff]
    intro q hq
    by_contra hq0
    exact Set.disjoint_left.mp hQM hq ⟨q, mem_nonZeroDivisors_of_ne_zero hq0, rfl⟩
  obtain ⟨a, haP, htP⟩ :=
    GroundTheory.Arith.Abelian.Jacobian.exists_ringKrullDim_eq_trdeg ℂ (A := MvPolynomial (Fin n) ℂ ⧸ P)
  obtain ⟨b, hbQ, htQ⟩ :=
    GroundTheory.Arith.Abelian.Jacobian.exists_ringKrullDim_eq_trdeg ℂ (A := MvPolynomial (Fin n) ℂ ⧸ Q)
  have hab : a ≤ b := by
    have h := hQu.cardinalMk_le_trdeg
    rw [hcard, htP, htQ] at h
    exact_mod_cast h
  calc ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ P) = a := haP
    _ ≤ b := by exact_mod_cast hab
    _ = ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ Q) := hbQ.symm
    _ ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) :=
      ringKrullDim_le_of_surjective (Ideal.Quotient.factor hJQ) (Ideal.Quotient.factor_surjective hJQ)

end

end GroundTheory.Heights₂.Heights.ComplexSets
