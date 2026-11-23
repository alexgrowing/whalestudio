import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA
import ReciprocityTheory.SemistableReduction.GaussValExists
import ReciprocityTheory.SemistableReduction.GaussValLeIffDivMem
import ReciprocityTheory.SemistableReduction.GaussIndepOfLeTrdeg
import ReciprocityTheory.SemistableReduction.IntegralClosureRankAndResidueTrdegLe

namespace ReciprocityTheory.ChartRestriction.G.T0

open MvPolynomial

theorem mem_valuationRing {E : Type} [Field E] (v : AddValuation E (WithTop ℤ)) (x : E) :
    x ∈ vRing v ↔ 0 ≤ v x :=
  (Valuation.mem_valuationSubring_iff (v : Valuation E (Multiplicative (WithTop ℤ)ᵒᵈ)) x).trans Iff.rfl

theorem algebraicIndependent_residue_of_isUnit {A R E : Type} [CommRing A] [Field R] [Field E] (V : ValuationSubring E)
    [Algebra R (IsLocalRing.ResidueField V)] (φ : A →+* V) (ψ : A →+* R)
    (hψ : Function.Surjective ψ)
    (hc : ∀ a, algebraMap R (IsLocalRing.ResidueField V) (ψ a) = IsLocalRing.residue V (φ a))
    {τ : Type} (t : τ → V) (h : ∀ q : MvPolynomial τ A, q.map ψ ≠ 0 → IsUnit (eval₂ φ t q)) :
    AlgebraicIndependent R (fun j => IsLocalRing.residue V (t j)) := by
  rw [algebraicIndependent_iff]
  intro P hP
  by_contra hne
  obtain ⟨q, rfl⟩ := MvPolynomial.map_surjective ψ hψ P
  have hu := (h q hne).map (IsLocalRing.residue V)
  have key : IsLocalRing.residue V (eval₂ φ t q) =
      MvPolynomial.aeval (fun j => IsLocalRing.residue V (t j)) (q.map ψ) := by
    rw [MvPolynomial.hom_eval₂, MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
    congr 1
    exact RingHom.ext fun a => (hc a).symm
  rw [key, hP] at hu
  exact not_isUnit_zero hu

theorem trdeg_residue_le {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (D : ℕ)
    (hD : Algebra.trdeg K Ω = D) (v : AddValuation Ω (WithTop ℤ))
    (hK : ∀ a : K, a ≠ 0 → v (algebraMap K Ω a) = 0) (a0 : Ω) (ha0 : a0 ≠ 0) (hva0 : v a0 ≠ 0) :
    letI := resAlg (F := K) v
    Algebra.trdeg (IsLocalRing.ResidueField ((vRing v).comap (algebraMap K Ω)))
      (IsLocalRing.ResidueField (vRing v)) ≤ ((D - 1 : ℕ) : Cardinal) := by
  set V := vRing v with hV
  set k := IsLocalRing.ResidueField (V.comap (algebraMap K Ω)) with hk
  set κ := IsLocalRing.ResidueField V with hκ
  letI inst : Algebra k κ := resAlg (F := K) v
  have hKV : ∀ a : K, algebraMap K Ω a ∈ V := by
    intro a
    rw [hV, mem_valuationRing]
    by_cases ha : a = 0
    · rw [ha, map_zero, AddValuation.map_zero]
      exact le_top
    · exact le_of_eq (hK a ha).symm
  let jK : K →+* V := (algebraMap K Ω).codRestrict V hKV
  let jW : K →+* V.comap (algebraMap K Ω) :=
    (RingHom.id K).codRestrict (V.comap (algebraMap K Ω)) fun a => ValuationSubring.mem_comap.mpr (hKV a)
  let ιK : K →+* k := (IsLocalRing.residue _).comp jW
  have hcompat : ∀ a : K, algebraMap k κ (ιK a) = IsLocalRing.residue V (jK a) := by
    intro a
    show IsLocalRing.ResidueField.map (comapIncl V (algebraMap K Ω)) (IsLocalRing.residue _ (jW a)) = _
    rw [IsLocalRing.ResidueField.map_residue]
    rfl
  have hle : Algebra.trdeg k κ ≤ D := by
    have h := ReciprocityTheory.MultiplicativeHeights.residueTrdegLe K Ω V
    rw [hD] at h
    exact h
  obtain ⟨r, hr⟩ : ∃ r : ℕ, Algebra.trdeg k κ = r :=
    Cardinal.lt_aleph0.mp (lt_of_le_of_lt hle (Cardinal.nat_lt_aleph0 D))
  haveI : FaithfulSMul k κ :=
    (faithfulSMul_iff_algebraMap_injective k κ).mpr (algebraMap k κ).injective
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k κ
  have hsr : Cardinal.mk s = r := by rw [hs.cardinalMk_eq_trdeg, hr]
  obtain ⟨e⟩ := Cardinal.mk_eq_nat_iff.mp hsr
  let ρ : Fin r → κ := fun i => (e.symm i : κ)
  have hρ : AlgebraicIndependent k ρ := hs.1.comp e.symm e.symm.injective
  choose tV htV using fun i => IsLocalRing.residue_surjective (R := V) (ρ i)
  let t : Fin r → Ω := fun i => (tV i : Ω)
  let ψ : MvPolynomial (Fin r) K →+* V := MvPolynomial.eval₂Hom jK tV
  have hψ : ∀ p, (ψ p : Ω) = MvPolynomial.aeval t p := by
    intro p
    show V.subtype (MvPolynomial.eval₂ jK tV p) = _
    rw [MvPolynomial.hom_eval₂, MvPolynomial.aeval_def]
    congr 1
  have hres : ∀ p, IsLocalRing.residue V (ψ p) = MvPolynomial.aeval ρ (p.map ιK) := by
    intro p
    show IsLocalRing.residue V (MvPolynomial.eval₂ jK tV p) = _
    have hf : (IsLocalRing.residue V).comp jK = (algebraMap k κ).comp ιK :=
      RingHom.ext fun a => (hcompat a).symm
    have hg : (fun i => IsLocalRing.residue V (tV i)) = ρ := funext htV
    rw [MvPolynomial.hom_eval₂, hf, hg, MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
  have hG : ∀ p : MvPolynomial (Fin r) K, p ≠ 0 → v (MvPolynomial.aeval t p) = 0 := by
    intro p hp
    have hne : MvPolynomial.aeval ρ (p.map ιK) ≠ 0 := by
      intro h0
      apply hp
      apply MvPolynomial.map_injective ιK ιK.injective
      rw [map_zero]
      exact (algebraicIndependent_iff.mp hρ) _ h0
    rw [← hres] at hne
    have hu := (IsLocalRing.residue_ne_zero_iff_isUnit _).mp hne
    rw [← hψ]
    obtain ⟨u, hu'⟩ := hu
    have hmul : (ψ p : Ω) * ((↑u⁻¹ : V) : Ω) = 1 := by
      have h1 := u.mul_inv
      rw [hu'] at h1
      exact congrArg Subtype.val h1
    have hsum : v (ψ p : Ω) + v ((↑u⁻¹ : V) : Ω) = 0 := by
      rw [← AddValuation.map_mul, hmul, AddValuation.map_one]
    exact ((add_eq_zero_iff_of_nonneg ((mem_valuationRing v _).mp (ψ p).2)
      ((mem_valuationRing v _).mp (↑u⁻¹ : V).2)).mp hsum).1
  have ht : AlgebraicIndependent K t := by
    rw [algebraicIndependent_iff]
    intro p hp
    by_contra hne
    have h1 := hG p hne
    rw [hp, AddValuation.map_zero] at h1
    exact WithTop.top_ne_coe h1
  obtain ⟨m, hm⟩ : ∃ m : ℤ, (m : WithTop ℤ) = v a0 :=
    WithTop.ne_top_iff_exists.mp (by rw [Ne, AddValuation.top_iff]; exact ha0)
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hva0 hm.symm
  have htr : Transcendental (Algebra.adjoin K (Set.range t)) a0 := by
    rintro ⟨q, hq0, hq⟩
    have hcv : ∀ j, q.coeff j ≠ 0 → v ((q.coeff j : Ω)) = 0 := by
      intro j hj
      have hmem : (q.coeff j : Ω) ∈ (MvPolynomial.aeval (R := K) t).range := by
        rw [← Algebra.adjoin_range_eq_range_aeval K t]
        exact (q.coeff j).2
      obtain ⟨p, hp⟩ := hmem
      have hp0 : p ≠ 0 := by
        rintro rfl
        apply hj
        apply Subtype.ext
        rw [← hp, map_zero]
        rfl
      rw [← hp]
      exact hG p hp0
    rw [Polynomial.aeval_eq_sum_range] at hq
    obtain ⟨j0, hj0, hmin⟩ := Finset.exists_min_image q.support (fun j => (j : ℤ) * m)
      (Polynomial.nonempty_support_iff.mpr hq0)
    have hj0S : j0 ∈ Finset.range (q.natDegree + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le (Polynomial.le_natDegree_of_mem_supp j0 hj0))
    have hterm : ∀ j, q.coeff j ≠ 0 → v (q.coeff j • a0 ^ j) = (((j : ℤ) * m : ℤ) : WithTop ℤ) := by
      intro j hj
      rw [Algebra.smul_def, AddValuation.map_mul, AddValuation.map_pow, ← hm]
      have e1 : algebraMap (Algebra.adjoin K (Set.range t)) Ω (q.coeff j) = (q.coeff j : Ω) := rfl
      rw [e1, hcv j hj, zero_add, ← WithTop.coe_nsmul, nsmul_eq_mul]
    have hg : v (q.coeff j0 • a0 ^ j0) = (((j0 : ℤ) * m : ℤ) : WithTop ℤ) :=
      hterm j0 (Polynomial.mem_support_iff.mp hj0)
    have hrest : v (q.coeff j0 • a0 ^ j0) <
        v (∑ j ∈ (Finset.range (q.natDegree + 1)).erase j0, q.coeff j • a0 ^ j) := by
      rw [hg]
      apply AddValuation.map_lt_sum _ WithTop.coe_ne_top
      intro j hj
      by_cases hc : q.coeff j = 0
      · rw [hc, zero_smul, AddValuation.map_zero]
        exact WithTop.coe_lt_top _
      · rw [hterm j hc, WithTop.coe_lt_coe]
        have hne : j ≠ j0 := Finset.ne_of_mem_erase hj
        have hle := hmin j (Polynomial.mem_support_iff.mpr hc)
        have hneq : (j0 : ℤ) * m ≠ (j : ℤ) * m := by
          intro h
          apply hne
          exact_mod_cast (mul_right_cancel₀ hm0 h).symm
        exact lt_of_le_of_ne hle hneq
    rw [← Finset.add_sum_erase _ _ hj0S] at hq
    have h2 := AddValuation.map_add_eq_of_lt_left v hrest
    rw [hq, AddValuation.map_zero, hg] at h2
    exact WithTop.top_ne_coe h2
  have hind : AlgebraicIndependent K (fun o : Option (Fin r) => o.elim a0 t) :=
    AlgebraicIndependent.option_iff.mpr ⟨ht, htr⟩
  have hcardle := hind.cardinalMk_le_trdeg
  rw [hD, Cardinal.mk_option, Cardinal.mk_fintype, Fintype.card_fin] at hcardle
  have hrD : r + 1 ≤ D := by exact_mod_cast hcardle
  have hfin : Algebra.trdeg k κ ≤ ((D - 1 : ℕ) : Cardinal) := by
    rw [hr]
    exact_mod_cast (by omega : r ≤ D - 1)
  exact hfin

theorem trdeg_eq_of_card {F E C : Type} [Field F] [Field E] [Field C] [Algebra F E] [Algebra E C]
    [Algebra F C] {σ τ : Type} [Fintype σ] [Fintype τ] (tb : σ → C)
    (ub : τ → C) (hu : AlgebraicIndependent F ub)
    (hmem : ∀ j, ub j ∈ Algebra.adjoin E (Set.range tb)) (n : ℕ)
    (hE : Algebra.trdeg F E ≤ n) (hcard : Fintype.card τ = Fintype.card σ + n)
    (hT : ∀ x : F, algebraMap F C x = algebraMap E C (algebraMap F E x)) :
    Algebra.trdeg F E = n ∧ AlgebraicIndependent E tb := by
  haveI : IsScalarTower F E C := IsScalarTower.of_algebraMap_eq hT
  have h1 := ReciprocityTheory.MultiplicativeHeights.gauss_card_le_trdeg_add tb ub hu hmem
  have h2 := ReciprocityTheory.MultiplicativeHeights.gauss_trdeg_adjoin_le (E := E) tb
  obtain ⟨a, ha⟩ : ∃ a : ℕ, Algebra.trdeg F E = a :=
    Cardinal.lt_aleph0.mp (lt_of_le_of_lt hE (Cardinal.nat_lt_aleph0 n))
  rw [Cardinal.mk_fintype] at h2
  obtain ⟨b, hb⟩ : ∃ b : ℕ, Algebra.trdeg E (Algebra.adjoin E (Set.range tb)) = b :=
    Cardinal.lt_aleph0.mp (lt_of_le_of_lt h2 (Cardinal.nat_lt_aleph0 _))
  rw [Cardinal.mk_fintype, hcard, ha, hb] at h1
  rw [ha] at hE
  rw [hb] at h2
  have h1' : Fintype.card σ + n ≤ a + b := by exact_mod_cast h1
  have hE' : a ≤ n := by exact_mod_cast hE
  have h2' : b ≤ Fintype.card σ := by exact_mod_cast h2
  have han : a = n := by omega
  have hbs : b = Fintype.card σ := by omega
  refine ⟨by rw [ha, han], ReciprocityTheory.MultiplicativeHeights.gauss_indep_of_le_trdeg tb ?_⟩
  rw [hb, hbs, Cardinal.mk_fintype]

theorem isUnit_of_val_eq_zero' {E : Type} [Field E] (v : AddValuation E (WithTop ℤ)) {z : E}
    (h : z ∈ vRing v) (hz : v z = 0) : IsUnit (⟨z, h⟩ : vRing v) := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [AddValuation.map_zero] at hz
    exact WithTop.top_ne_coe hz
  have hinv : z⁻¹ ∈ vRing v := by
    rw [mem_valuationRing, AddValuation.map_inv, hz, neg_zero]
  exact IsUnit.of_mul_eq_one (⟨z⁻¹, hinv⟩ : vRing v) (Subtype.ext (mul_inv_cancel₀ hz0))

theorem val_eq_zero_of_isUnit' {E : Type} [Field E] (v : AddValuation E (WithTop ℤ)) {z : E}
    (h : z ∈ vRing v) (hu : IsUnit (⟨z, h⟩ : vRing v)) : v z = 0 := by
  obtain ⟨u, hu⟩ := hu
  have hmul : z * ((↑u⁻¹ : vRing v) : E) = 1 := by
    have h1 := u.mul_inv
    rw [hu] at h1
    exact congrArg Subtype.val h1
  have hsum : v z + v ((↑u⁻¹ : vRing v) : E) = 0 := by
    rw [← AddValuation.map_mul, hmul, AddValuation.map_one]
  exact ((add_eq_zero_iff_of_nonneg ((mem_valuationRing v z).mp h)
    ((mem_valuationRing v _).mp (↑u⁻¹ : vRing v).2)).mp hsum).1

theorem scalarRatio_eq {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] {f g : V} {a : Ω}
    (hg : g ≠ 0) (h : f = a • g) : ratio f g = a := by
  have he : ∃ b : Ω, f = b • g := ⟨a, h⟩
  rw [ratio, dif_pos he]
  exact smul_left_injective Ω hg (he.choose_spec.symm.trans h)

theorem genericImage_base {Ω : Type} [Field Ω] {D N : ℕ} (j₀ : Fin (N + 1)) (x : Fin N → Ω)
    (i : Fin (D + 1)) :
    sImg j₀ x (i, j₀) = algebraMap (MvPolynomial (SVar D N) Ω) (OmS Ω D N)
      (if i = 0 then MvPolynomial.X (Sum.inl ())
        else -∑ k, MvPolynomial.X (Sum.inr (i, k)) * MvPolynomial.C (x k)) := by
  rw [sImg, Fin.succAbove_cases_eq_insertNth, Fin.insertNth_apply_same]

theorem genericImage_succAbove {Ω : Type} [Field Ω] {D N : ℕ} (j₀ : Fin (N + 1)) (x : Fin N → Ω)
    (i : Fin (D + 1)) (k : Fin N) :
    sImg j₀ x (i, j₀.succAbove k) =
      algebraMap (MvPolynomial (SVar D N) Ω) (OmS Ω D N) (MvPolynomial.X (Sum.inr (i, k))) := by
  rw [sImg, Fin.succAbove_cases_eq_insertNth, Fin.insertNth_apply_succAbove]

end ReciprocityTheory.ChartRestriction.G.T0
