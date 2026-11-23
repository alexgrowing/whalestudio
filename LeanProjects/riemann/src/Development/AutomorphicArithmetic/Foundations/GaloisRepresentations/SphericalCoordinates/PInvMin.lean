import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem aeval_inv_reverse_eq_zero_iff {K A : Type} [Field K] [Ring A] [Algebra K A] (u : Aˣ) (f : K[X]) :
    Polynomial.aeval (↑u⁻¹ : A) f.reverse = 0 ↔ Polynomial.aeval (u : A) f = 0 := by
  let S : Subalgebra K A := Algebra.adjoin K {(u : A), ↑u⁻¹}
  letI : CommRing S := Algebra.adjoinCommRingOfComm K (by
    intro a ha b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp)
  let x : S := ⟨u, Algebra.subset_adjoin (by simp)⟩
  let y : S := ⟨↑u⁻¹, Algebra.subset_adjoin (by simp)⟩
  letI : Invertible x := ⟨y, Subtype.ext (by simp [x, y]), Subtype.ext (by simp [x, y])⟩
  have key := Polynomial.eval₂_reverse_eq_zero_iff (algebraMap K S) x f
  have h1 : Polynomial.aeval (↑u⁻¹ : A) f.reverse = S.val (Polynomial.aeval y f.reverse) :=
    Polynomial.aeval_algHom_apply S.val y f.reverse
  have h2 : Polynomial.aeval (u : A) f = S.val (Polynomial.aeval x f) :=
    Polynomial.aeval_algHom_apply S.val x f
  rw [h1, h2, map_eq_zero_iff S.val Subtype.val_injective, map_eq_zero_iff S.val Subtype.val_injective,
    Polynomial.aeval_def, Polynomial.aeval_def]
  exact key

private theorem squarefree_mirror {F : Type} [Field F] (f : F[X]) (h : Squarefree f) :
    Squarefree f.mirror := by
  intro r hr
  obtain ⟨s, hs⟩ := hr
  have hf : f = r.mirror * r.mirror * s.mirror := by
    rw [← Polynomial.mirror_mul_of_domain, ← Polynomial.mirror_mul_of_domain, ← hs,
      Polynomial.mirror_mirror]
  have hu : IsUnit r.mirror := h _ ⟨_, hf⟩
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [Polynomial.mirror_zero] at hu
    exact not_isUnit_zero hu
  rw [Polynomial.isUnit_iff_degree_eq_zero] at hu ⊢
  rw [Polynomial.degree_eq_natDegree hr0]
  rw [Polynomial.degree_eq_natDegree (Polynomial.mirror_eq_zero.not.mpr hr0),
    Polynomial.mirror_natDegree] at hu
  exact hu

private theorem separable_reverse_of_coeff_zero_ne_zero {K : Type} [Field K] (f : K[X]) (h0 : f.coeff 0 ≠ 0)
    (hs : f.Separable) : f.reverse.Separable := by
  rw [← Polynomial.separable_map (algebraMap K (AlgebraicClosure K))]
  have hm : (f.reverse).map (algebraMap K (AlgebraicClosure K)) =
      (f.map (algebraMap K (AlgebraicClosure K))).mirror := by
    have htd : (f.map (algebraMap K (AlgebraicClosure K))).natTrailingDegree = 0 :=
      Polynomial.natTrailingDegree_eq_zero.mpr
        (Or.inr (by rw [Polynomial.coeff_map]; exact (_root_.map_ne_zero _).mpr h0))
    rw [Polynomial.mirror, htd, pow_zero, _root_.mul_one]
    simp only [Polynomial.reverse, Polynomial.natDegree_map, Polynomial.reflect_map]
  rw [hm, PerfectField.separable_iff_squarefree]
  exact squarefree_mirror _ ((Polynomial.separable_map _).mpr hs).squarefree

theorem UpperTheory.Gal.W2.invMin_of :
    UpperTheory.Gal.W2.InvMin := by
  intro K A _ _ _ _ _ u
  have hint : ∀ v : Aˣ, IsIntegral K (v : A) := fun v => .of_finite K _
  have hc : ∀ v : Aˣ, (minpoly K (v : A)).coeff 0 ≠ 0 := by
    intro v h0
    obtain ⟨q, hq⟩ := Polynomial.X_dvd_iff.mpr h0
    have hne := minpoly.ne_zero (hint v)
    have hq0 : q ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hq
      exact hne hq
    have hev : Polynomial.aeval (v : A) q = 0 := by
      have := minpoly.aeval K (v : A)
      rw [hq, map_mul, Polynomial.aeval_X] at this
      simpa using congrArg (fun z => (↑v⁻¹ : A) * z) this
    have hdeg := minpoly.degree_le_of_ne_zero K (v : A) hq0 hev
    have h2 := Polynomial.natDegree_le_natDegree hdeg
    rw [hq, Polynomial.natDegree_X_mul hq0] at h2
    omega
  set p := minpoly K (u : A) with hp
  have htd : p.natTrailingDegree = 0 := Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr (hc u))
  have hdegrev : p.reverse.natDegree = p.natDegree := by
    rw [Polynomial.reverse_natDegree, htd, Nat.sub_zero]
  have hinvMonic : (invPoly p).Monic := by
    show (Polynomial.C (p.coeff 0)⁻¹ * p.reverse).leadingCoeff = 1
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, Polynomial.reverse_leadingCoeff,
      Polynomial.trailingCoeff_eq_coeff_zero (hc u), inv_mul_cancel₀ (hc u)]
  have hinvDeg : (invPoly p).natDegree = p.natDegree := by
    show (Polynomial.C (p.coeff 0)⁻¹ * p.reverse).natDegree = _
    rw [Polynomial.natDegree_C_mul (inv_ne_zero (hc u)), hdegrev]
  have hinvEval : Polynomial.aeval (↑u⁻¹ : A) (invPoly p) = 0 := by
    show Polynomial.aeval (↑u⁻¹ : A) (Polynomial.C (p.coeff 0)⁻¹ * p.reverse) = 0
    rw [map_mul, (aeval_inv_reverse_eq_zero_iff u p).mpr (minpoly.aeval K _), mul_zero]
  have heq : minpoly K (↑u⁻¹ : A) = invPoly p := by
    refine (minpoly.unique K _ hinvMonic hinvEval ?_).symm
    intro q hqm hqe
    have hq0 : q ≠ 0 := hqm.ne_zero
    have h1 : Polynomial.aeval (u : A) q.reverse = 0 := by
      have := (aeval_inv_reverse_eq_zero_iff u⁻¹ q).mpr hqe
      simpa using this
    have h2 := minpoly.degree_le_of_ne_zero K (u : A) (mt Polynomial.reverse_eq_zero.mp hq0) h1
    have h3 := Polynomial.natDegree_le_natDegree h2
    have h4 := Polynomial.reverse_natDegree_le q
    rw [Polynomial.degree_eq_natDegree hinvMonic.ne_zero, Polynomial.degree_eq_natDegree hq0, hinvDeg]
    exact_mod_cast h3.trans h4
  refine ⟨heq, by rw [heq, hinvDeg], fun hs => ?_⟩
  rw [heq]
  have hrev : p.reverse.Separable := separable_reverse_of_coeff_zero_ne_zero p (hc u) hs
  refine hrev.of_dvd ⟨Polynomial.C (p.coeff 0), ?_⟩
  show p.reverse = Polynomial.C (p.coeff 0)⁻¹ * p.reverse * Polynomial.C (p.coeff 0)
  rw [_root_.mul_comm, ← _root_.mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ (hc u),
    Polynomial.C_1, _root_.one_mul]
