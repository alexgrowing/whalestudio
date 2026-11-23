import Formalism.LocalToGlobal.ProjectiveLattices.CurveLoc

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor MvPolynomial

namespace CurveCount

variable {K : Type*} [Field K] {N : ℕ}

def homog (a : Fin N) (Q : MvPolynomial (Fin N) K) : MvPolynomial (Fin N) K :=
  ∑ m ∈ Q.support, monomial (m + Finsupp.single a (Q.totalDegree - m.degree)) (Q.coeff m)

theorem homog_isHomogeneous (a : Fin N) (Q : MvPolynomial (Fin N) K) :
    (homog a Q).IsHomogeneous Q.totalDegree := by
  classical
  refine IsHomogeneous.sum _ _ _ fun m hm => isHomogeneous_monomial _ ?_
  have hle : m.degree ≤ Q.totalDegree := le_totalDegree hm
  rw [map_add, Finsupp.degree_single]
  omega

theorem aeval_homog {L : Type*} [Field L] [Algebra K L] (a : Fin N) (Q : MvPolynomial (Fin N) K) (y : Fin N → L)
    (hy : y a ≠ 0) : aeval y (homog a Q) = y a ^ Q.totalDegree * aeval (fun i => y i / y a) Q := by
  classical
  have hQ : aeval (fun i => y i / y a) Q =
      ∑ m ∈ Q.support, aeval (fun i => y i / y a) (monomial m (Q.coeff m)) := by
    conv_lhs => rw [Q.as_sum]
    rw [map_sum]
  rw [hQ, homog, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hle : m.degree ≤ Q.totalDegree := le_totalDegree hm
  rw [aeval_monomial, aeval_monomial, Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
    Finsupp.prod_single_index (by simp)]
  simp only [Finsupp.prod, div_pow, Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
  have hd : m.degree = ∑ i ∈ m.support, m i := rfl
  rw [← hd]
  have e : y a ^ Q.totalDegree = y a ^ (Q.totalDegree - m.degree) * y a ^ m.degree := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  rw [e]
  field_simp

theorem adjoin_ratio_eq {L : Type*} [Field L] [Algebra K L] (v : Fin N → L) {a b : Fin N} (ha : v a ≠ 0)
    (hb : v b ≠ 0) :
    IntermediateField.adjoin K (Set.range fun i => v i / v a) = IntermediateField.adjoin K (Set.range fun i => v i / v b) := by
  have key : ∀ a b : Fin N, v a ≠ 0 → v b ≠ 0 →
      IntermediateField.adjoin K (Set.range fun i => v i / v a) ≤ IntermediateField.adjoin K (Set.range fun i => v i / v b) := by
    intro a b ha hb
    rw [IntermediateField.adjoin_le_iff, Set.range_subset_iff]
    intro i
    have e : v i / v a = (v i / v b) / (v a / v b) := by field_simp
    rw [SetLike.mem_coe, e]
    exact IntermediateField.div_mem _ (IntermediateField.subset_adjoin K _ ⟨i, rfl⟩)
      (IntermediateField.subset_adjoin K _ ⟨a, rfl⟩)
  exact le_antisymm (key a b ha hb) (key b a hb ha)

end CurveCount

namespace CurveLoc

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO))
  (N : ℕ) {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)

theorem tv_indep :
    AlgebraicIndependent (X.Kl la) (fun p : Idx D j N => algebraMap (Op X la N) (Kp X la N) (Tv X la N p)) := by
  have h0 := MvPolynomial.algebraicIndependent_X (Idx D j N) (X.Ol la)
  have hinj1 : Function.Injective (algebraMap (Pol X la N) (Op X la N)) :=
    IsLocalization.injective (Op X la N) (Ideal.primeCompl_le_nonZeroDivisors (gI X la N))
  have hinj2 : Function.Injective (algebraMap (Op X la N) (Kp X la N)) := IsFractionRing.injective _ _
  let g : Pol X la N →ₐ[X.Ol la] Kp X la N :=
    (IsScalarTower.toAlgHom (X.Ol la) (Op X la N) (Kp X la N)).comp
      (IsScalarTower.toAlgHom (X.Ol la) (Pol X la N) (Op X la N))
  have h1 : AlgebraicIndependent (X.Ol la)
      (fun p : Idx D j N => algebraMap (Op X la N) (Kp X la N) (Tv X la N p)) :=
    h0.map' (f := g) (hinj2.comp hinj1)
  have : Algebra.IsAlgebraic (X.Ol la) (X.Kl la) := IsLocalization.isAlgebraic (X.Kl la) (nonZeroDivisors (X.Ol la))
  exact h1.extendScalars (X.Kl la)

theorem sfr_eq (i : Fin (WeightFamilies.dimY D j + 1)) :
    sfr X la w i = ∑ k, algebraMap (Kp X la N) ↥(Frac0 X la w)
      (algebraMap (Op X la N) (Kp X la N) (Tv X la N (i, k))) * xw X la N w k := by
  apply Subtype.ext
  rw [coe_sfr, Formalism.MainNotions.Gaps.EtaleWeightGaps.sec, map_sum]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, Algebra.smul_def]
  rfl

theorem sfr_zero : sfr X la w 0 = 1 := by
  apply Subtype.ext
  rw [coe_sfr, frac_apply, pow_one, section_mul_inverse_eq_one]
  rfl

variable {Ω : Type} [Field Ω] [Algebra B.KO Ω] (gF : X.Forms →ₐ[B.KO] Ω)

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in

theorem countQAt_of (v : Fin N → Ω) (hv : ∀ i, gF (X.inc wL (w i)) = v i)
    (htr : ∃ a₀, v a₀ ≠ 0 ∧
      Algebra.trdeg B.KO (IntermediateField.adjoin B.KO (Set.range fun i => v i / v a₀)) ≤ WeightFamilies.dimY D j) :
    CountQAt X la N w gF := by
  classical
  intro 𝔮 h𝔮 hJ hK Pw k hPw hne hmem
  have : 𝔮.IsPrime := h𝔮
  have hvf : (fun i => gF (X.inc wL (w i))) = v := funext hv
  rw [hvf] at hne
  let Fr := ↥(Frac0 X la w)
  let κ := FractionRing (Fr ⧸ 𝔮)
  let ρ : Fr →+* κ := (algebraMap (Fr ⧸ 𝔮) κ).comp (Ideal.Quotient.mk 𝔮)
  have hρ : ∀ f, ρ f = 0 ↔ f ∈ 𝔮 := fun f => by
    rw [RingHom.comp_apply, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
  let ρK : Kp X la N →+* κ := ρ.comp (algebraMap (Kp X la N) Fr)
  let algKl : Algebra (X.Kl la) κ := (ρK.comp (algebraMap (X.Kl la) (Kp X la N))).toAlgebra
  let algK : Algebra B.KO κ :=
    ((ρK.comp (algebraMap (X.Kl la) (Kp X la N))).comp (algebraMap B.KO (X.Kl la))).toAlgebra
  let _ := algKl
  let _ := algK
  have : IsScalarTower B.KO (X.Kl la) κ :=
    @IsScalarTower.of_algebraMap_eq B.KO (X.Kl la) κ _ _ _ _ algKl algK (fun _ => rfl)
  let x : Fin N → κ := fun i => ρ (xw X la N w i)
  let t : Fin (WeightFamilies.dimY D j + 1) × Fin N → κ :=
    fun p => ρK (algebraMap (Op X la N) (Kp X la N) (Tv X la N p))
  have ht : AlgebraicIndependent B.KO t := by
    let g : Kp X la N →ₐ[X.Kl la] κ := { ρK with commutes' := fun _ => rfl }
    have h1 := (tv_indep X la N).map' (f := g) ρK.injective
    exact h1.restrictScalars (algebraMap B.KO (X.Kl la)).injective
  have hρpol : ∀ Q : MvPolynomial (Fin N) B.KO, ρ (polX X la N w Q) = aeval x Q := fun Q => by
    rw [polX, MvPolynomial.eval₂_comp_left, aeval_def]
    rfl
  have hlin : ∀ i : Fin (WeightFamilies.dimY D j), ∑ k, t (i.succ, k) * x k = 0 := by
    intro i
    have h := congrArg ρ (sfr_eq X la N w i.succ)
    rw [map_sum] at h
    simp only [map_mul] at h
    rw [← (hρ _).mpr (hJ (sfr_succ_mem_Jid X la w i)), h]
    rfl
  have hlin0 : ∑ k, t (0, k) * x k = 1 := by
    have h := congrArg ρ (sfr_eq X la N w 0)
    rw [map_sum, sfr_zero, map_one] at h
    simp only [map_mul] at h
    rw [h]
    rfl
  obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hlin0.symm ▸ one_ne_zero : ∑ k, t (0, k) * x k ≠ 0)
  have hxa : x a ≠ 0 := right_ne_zero_of_mul ha
  have hva : v a ≠ 0 := by
    intro h0
    apply hxa
    refine (hρ _).mpr (hK ?_)
    rw [RingHom.mem_ker, phiZ_xw, hv, h0, map_zero, zero_mul]
  obtain ⟨a₀, ha₀, htr₀⟩ := htr
  have htra : Algebra.trdeg B.KO (IntermediateField.adjoin B.KO (Set.range fun i => v i / v a)) ≤ WeightFamilies.dimY D j := by
    rw [CurveCount.adjoin_ratio_eq v hva ha₀]
    exact htr₀
  have htrans : ∀ Q : MvPolynomial (Fin N) B.KO, aeval (fun i => v i / v a) Q = 0 →
      aeval (fun i => x i / x a) Q = 0 := by
    intro Q hQ
    have hH := CurveCount.homog_isHomogeneous a Q
    have hv0 : aeval v (CurveCount.homog a Q) = 0 := by rw [CurveCount.aeval_homog a Q v hva, hQ, mul_zero]
    have hq : polX X la N w (CurveCount.homog a Q) ∈ 𝔮 := hK (by
      rw [RingHom.mem_ker, phiZ_polX X la N w gF hH, hvf, hv0, map_zero, mul_zero])
    have hx0 : aeval x (CurveCount.homog a Q) = 0 := by rw [← hρpol]; exact (hρ _).mpr hq
    rw [CurveCount.aeval_homog a Q x hxa] at hx0
    exact (mul_eq_zero.mp hx0).resolve_left (pow_ne_zero _ hxa)
  exact CurveCount.countCore v x a hva hxa htra htrans t ht hlin hlin0 Pw hPw hne
    (by rw [← hρpol]; exact (hρ _).mpr hmem)

end CurveLoc

end Formalism.L2.Pj
