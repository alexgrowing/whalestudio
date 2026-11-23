import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.NoOpStep
import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.TwistedMonomialFiltration.MaxTwistDegreePderivLeAddOne

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.LetterSubstitution

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.PairMembershipBlocks

section Coef

variable {σ τ Kf : Type} [Field Kf]

theorem coeff_oneT (A : Module.End Kf (MvPolynomial τ Kf)) (F : MvPolynomial σ (MvPolynomial τ Kf)) (mo : σ →₀ ℕ) :
    (oneT A F).coeff mo = A (F.coeff mo) := by
  unfold oneT
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.notMem_support_iff.1 h, map_zero]

theorem coeff_planeCoeff (nu : τ →₀ ℕ) (F : MvPolynomial σ (MvPolynomial τ Kf)) (mo : σ →₀ ℕ) :
    (planeCoeff nu F).coeff mo = (F.coeff mo).coeff nu := by
  unfold planeCoeff
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.notMem_support_iff.1 h, MvPolynomial.coeff_zero]

def nuSet (F : MvPolynomial σ (MvPolynomial τ Kf)) : Finset (τ →₀ ℕ) :=
  F.support.biUnion fun mo => (F.coeff mo).support

theorem support_sub_nuSet (F : MvPolynomial σ (MvPolynomial τ Kf)) (mo : σ →₀ ℕ) :
    (F.coeff mo).support ⊆ nuSet F := by
  intro nu h
  unfold nuSet
  rw [Finset.mem_biUnion]
  refine ⟨mo, ?_, h⟩
  rw [MvPolynomial.mem_support_iff]
  intro h0
  rw [h0, MvPolynomial.support_zero] at h
  exact Finset.notMem_empty _ h

theorem expand_sub (y : MvPolynomial τ Kf) (N : Finset (τ →₀ ℕ)) (hN : y.support ⊆ N) :
    y = ∑ nu' ∈ N, y.coeff nu' • monomial nu' (1 : Kf) := by
  simp_rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [← Finset.sum_subset hN]
  · exact (MvPolynomial.support_sum_monomial_coeff y).symm
  · intro x _ hx
    rw [MvPolynomial.notMem_support_iff.1 hx, MvPolynomial.monomial_zero]

theorem planeCoeff_oneT (A : Module.End Kf (MvPolynomial τ Kf)) (F : MvPolynomial σ (MvPolynomial τ Kf))
    (nu : τ →₀ ℕ) :
    planeCoeff nu (oneT A F) = ∑ nu' ∈ nuSet F, (A (monomial nu' 1)).coeff nu • planeCoeff nu' F := by
  ext mo : 1
  rw [coeff_planeCoeff, coeff_oneT, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_smul, coeff_planeCoeff, smul_eq_mul]
  conv_lhs => rw [expand_sub (F.coeff mo) (nuSet F) (support_sub_nuSet F mo)]
  rw [map_sum, MvPolynomial.coeff_sum]
  refine Finset.sum_congr rfl fun nu' _ => ?_
  rw [map_smul, MvPolynomial.coeff_smul, smul_eq_mul, mul_comm]

theorem oneT_mul (A B : Module.End Kf (MvPolynomial τ Kf)) (F : MvPolynomial σ (MvPolynomial τ Kf)) :
    oneT (A * B) F = oneT A (oneT B F) := by
  ext mo : 1
  rw [coeff_oneT, coeff_oneT, coeff_oneT, Module.End.mul_apply]

theorem oneT_eq_zero (A : Module.End Kf (MvPolynomial τ Kf)) (F : MvPolynomial σ (MvPolynomial τ Kf))
    (h : ∀ mo, A (F.coeff mo) = 0) : oneT A F = 0 := by
  ext mo : 1
  rw [coeff_oneT, h, MvPolynomial.coeff_zero]

theorem planeCoeff_zero' (nu : τ →₀ ℕ) : planeCoeff nu (0 : MvPolynomial σ (MvPolynomial τ Kf)) = 0 := by
  unfold planeCoeff
  simp

theorem planeCoeff_sum {κ : Type} (S : Finset κ) (f : κ → MvPolynomial σ (MvPolynomial τ Kf)) (nu : τ →₀ ℕ) :
    planeCoeff nu (∑ k ∈ S, f k) = ∑ k ∈ S, planeCoeff nu (f k) := by
  ext mo : 1
  rw [coeff_planeCoeff, MvPolynomial.coeff_sum, MvPolynomial.coeff_sum, MvPolynomial.coeff_sum]
  simp only [coeff_planeCoeff]

end Coef

section XXLin

variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {r J : ℕ} [NeZero J] [NeZero r]
  (Dt : SignedChainData p O r J) (d : TL J Dt.nL r → ℕ) (th : ∀ j, Fin (Dt.nch j) → ℝ) (thL : ZMod J → Fin r → ℝ)

private theorem geZ_of_le {a b : WithTop ℤ} {t : ℝ} (ha : geZ a t) (hab : a ≤ b) : geZ b t := by
  intro k hk
  subst hk
  induction a using WithTop.recTopCoe with
  | top => exact absurd hab (by simp)
  | coe a =>
    have h1 := ha a rfl
    have h2 : a ≤ k := WithTop.coe_le_coe.1 hab
    exact le_trans h1 (by exact_mod_cast h2)

private theorem geZ_inf {a b : WithTop ℤ} {t : ℝ} (ha : geZ a t) (hb : geZ b t) : geZ (a ⊓ b) t := by
  rcases le_total a b with h | h
  · rw [inf_of_le_left h]
    exact ha
  · rw [inf_of_le_right h]
    exact hb

private theorem valS_inf_le_valS_add {R : Type} [CommRing R] {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    (F G : MvPolynomial (ι × Fin n) R) : valS LL S F ⊓ valS LL S G ≤ valS LL S (F + G) := by
  unfold valS
  rw [← Finset.inf_union]
  apply Finset.inf_mono
  intro k hk
  unfold sDegs at hk ⊢
  rw [map_add] at hk
  rw [Finset.mem_union, Finset.mem_biUnion, Finset.mem_biUnion]
  rw [Finset.mem_biUnion] at hk
  obtain ⟨m, -, hk⟩ := hk
  rw [MvPolynomial.coeff_add, AddMonoidAlgebra.coeff_add] at hk
  rcases Finset.mem_union.1 (Finsupp.support_add hk) with h | h
  · refine Or.inl ⟨m, ?_, h⟩
    rw [MvPolynomial.mem_support_iff]
    intro h0
    rw [h0, AddMonoidAlgebra.coeff_zero] at h
    simp at h
  · refine Or.inr ⟨m, ?_, h⟩
    rw [MvPolynomial.mem_support_iff]
    intro h0
    rw [h0, AddMonoidAlgebra.coeff_zero] at h
    simp at h

private theorem valS_le_valS_C_mul {R : Type} [CommRing R] {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    (c : R) (F : MvPolynomial (ι × Fin n) R) : valS LL S F ≤ valS LL S (MvPolynomial.C c * F) := by
  unfold valS
  apply Finset.inf_mono
  intro k hk
  unfold sDegs at hk ⊢
  rw [map_mul] at hk
  rw [Finset.mem_biUnion] at hk ⊢
  obtain ⟨m, -, hk⟩ := hk
  have hC : twistSub LL S (lastIdx n) (MvPolynomial.C c) = MvPolynomial.C (coefL R n c) := by
    unfold twistSub
    rw [MvPolynomial.eval₂Hom_C, RingHom.comp_apply]
  rw [hC, MvPolynomial.coeff_C_mul] at hk
  unfold coefL at hk
  rw [RingHom.comp_apply, ← LaurentPolynomial.single_eq_C] at hk
  have hk2 := Finsupp.mem_support_iff.1 hk
  rw [AddMonoidAlgebra.coeff_single_zero_mul] at hk2
  have hk3 := right_ne_zero_of_mul hk2
  refine ⟨m, ?_, Finsupp.mem_support_iff.2 hk3⟩
  rw [MvPolynomial.mem_support_iff]
  intro h0
  rw [h0, AddMonoidAlgebra.coeff_zero] at hk3
  exact hk3 rfl

private theorem fdig_eq_sum_filter_digOK_of_support_subset (rho : (ZMod J × Fin r) × Fin r → ℕ) (F : MvPolynomial (TL J Dt.nL r × Fin r) (KK O))
    (T : Finset (TL J Dt.nL r × Fin r →₀ ℕ)) (hT : F.support ⊆ T) :
    Dt.Fdig rho F = ∑ mo ∈ T with Dt.digOK rho mo,
      MvPolynomial.C (MvPolynomial.coeff mo F) * ∏ v ∈ mo.support, MvPolynomial.X (Dt.liftVar v) ^ Dt.liftExp mo v := by
  unfold SignedChainData.Fdig
  apply Finset.sum_subset (Finset.filter_subset_filter _ hT)
  intro x hx hnx
  have hxF : x ∉ F.support := fun h => hnx (Finset.mem_filter.2 ⟨h, (Finset.mem_filter.1 hx).2⟩)
  rw [MvPolynomial.notMem_support_iff.1 hxF, MvPolynomial.C_0, zero_mul]

private theorem fdig_add (rho : (ZMod J × Fin r) × Fin r → ℕ) (F G : MvPolynomial (TL J Dt.nL r × Fin r) (KK O)) :
    Dt.Fdig rho (F + G) = Dt.Fdig rho F + Dt.Fdig rho G := by
  rw [fdig_eq_sum_filter_digOK_of_support_subset Dt rho (F + G) (F.support ∪ G.support) MvPolynomial.support_add,
    fdig_eq_sum_filter_digOK_of_support_subset Dt rho F (F.support ∪ G.support) Finset.subset_union_left,
    fdig_eq_sum_filter_digOK_of_support_subset Dt rho G (F.support ∪ G.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun mo _ => ?_
  rw [MvPolynomial.coeff_add, MvPolynomial.C_add, add_mul]

private theorem fdig_smul (rho : (ZMod J × Fin r) × Fin r → ℕ) (c : KK O)
    (F : MvPolynomial (TL J Dt.nL r × Fin r) (KK O)) :
    Dt.Fdig rho (c • F) = MvPolynomial.C c * Dt.Fdig rho F := by
  rw [fdig_eq_sum_filter_digOK_of_support_subset Dt rho (c • F) F.support MvPolynomial.support_smul,
    fdig_eq_sum_filter_digOK_of_support_subset Dt rho F F.support subset_rfl, Finset.mul_sum]
  refine Finset.sum_congr rfl fun mo _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul, MvPolynomial.C_mul, mul_assoc]

theorem XXg_add {F G : MvPolynomial (TL J Dt.nL r × Fin r) (KK O)} (hF : XXg Dt d th thL F)
    (hG : XXg Dt d th thL G) : XXg Dt d th thL (F + G) := by
  obtain ⟨h1, h2, h3⟩ := hF
  obtain ⟨g1, g2, g3⟩ := hG
  refine ⟨Submodule.add_mem _ h1 g1, fun rho j i => ?_, fun j m hm => ?_⟩
  · rw [fdig_add]
    exact geZ_of_le (geZ_inf (h2 rho j i) (g2 rho j i)) (valS_inf_le_valS_add _ _ _ _)
  · exact geZ_of_le (geZ_inf (h3 j m hm) (g3 j m hm)) (valS_inf_le_valS_add _ _ _ _)

theorem XXg_smul (c : KK O) {F : MvPolynomial (TL J Dt.nL r × Fin r) (KK O)} (hF : XXg Dt d th thL F) :
    XXg Dt d th thL (c • F) := by
  obtain ⟨h1, h2, h3⟩ := hF
  refine ⟨Submodule.smul_mem _ c h1, fun rho j i => ?_, fun j m hm => ?_⟩
  · rw [fdig_smul]
    exact geZ_of_le (h2 rho j i) (valS_le_valS_C_mul _ _ _ _)
  · rw [MvPolynomial.smul_eq_C_mul]
    exact geZ_of_le (h3 j m hm) (valS_le_valS_C_mul _ _ _ _)

theorem XXg_zero : XXg Dt d th thL (0 : MvPolynomial (TL J Dt.nL r × Fin r) (KK O)) := by
  refine ⟨Submodule.zero_mem _, fun rho j i => ?_, fun j m hm => ?_⟩
  · intro k hk
    simp [valS, sDegs, SignedChainData.Fdig] at hk
  · intro k hk
    simp [valS, sDegs] at hk

theorem XXg_sum {κ : Type} (S : Finset κ) (f : κ → MvPolynomial (TL J Dt.nL r × Fin r) (KK O))
    (h : ∀ k ∈ S, XXg Dt d th thL (f k)) : XXg Dt d th thL (∑ k ∈ S, f k) := by
  induction S using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact XXg_zero Dt d th thL
  | insert a S ha ih =>
    rw [Finset.sum_insert ha]
    exact XXg_add Dt d th thL (h a (Finset.mem_insert_self a S))
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

end XXLin

section Dec

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {ι : Type*} [Fintype ι] [DecidableEq ι]
  (E : ι → GLOps n K V) (ee : ι → (Fin n → ℤ) → Module.End K V)

def isoOn (I : Finset ι) : Set V := {x | ∃ ka : ι → Fin n → ℤ, ∀ i ∈ I, x ∈ isoSub (E i) (ka i)}

theorem span_isoOn (hee : ∀ i mu, IsIsoProj (E i) mu (ee i mu))
    (hcomm : ∀ i i' mu mu', ee i mu * ee i' mu' = ee i' mu' * ee i mu)
    (hdec : ∀ i (G : V), ∃ T : Finset (Fin n → ℤ), G = ∑ mu ∈ T, ee i mu G ∧ ∀ mu, ee i mu G ∈ isoSub (E i) mu)
    (I : Finset ι) : ∀ y : V, y ∈ Submodule.span K (isoOn E I) := by
  induction I using Finset.induction_on with
  | empty =>
    intro y
    exact Submodule.subset_span ⟨fun _ => 0, fun i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert i0 I hi0 ih =>
    have key : ∀ x ∈ isoOn E I, x ∈ Submodule.span K (isoOn E (insert i0 I)) := by
      rintro x ⟨ka, hka⟩
      obtain ⟨T, hT, hmem⟩ := hdec i0 x
      rw [hT]
      refine Submodule.sum_mem _ fun mu _ => Submodule.subset_span ⟨Function.update ka i0 mu, fun i hi => ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hi'
      · rw [Function.update_self]; exact hmem mu
      · have hne : i ≠ i0 := fun h => hi0 (h ▸ hi')
        rw [Function.update_of_ne hne]
        have hfix : ee i (ka i) x = x := (hee i (ka i)).1 x (hka i hi')
        have : ee i0 mu x = ee i (ka i) (ee i0 mu x) := by
          conv_lhs => rw [← hfix]
          rw [← Module.End.mul_apply, hcomm i0 i mu (ka i), Module.End.mul_apply]
        rw [this]
        obtain ⟨_, _, h3⟩ := hdec i (ee i0 mu x)
        exact h3 (ka i)
    intro y
    exact (Submodule.span_le.2 key) (ih y)

theorem joint_dec (hee : ∀ i mu, IsIsoProj (E i) mu (ee i mu))
    (hcomm : ∀ i i' mu mu', ee i mu * ee i' mu' = ee i' mu' * ee i mu)
    (hdec : ∀ i (G : V), ∃ T : Finset (Fin n → ℤ), G = ∑ mu ∈ T, ee i mu G ∧ ∀ mu, ee i mu G ∈ isoSub (E i) mu)
    (y : V) : ∃ S : Finset (ι → Fin n → ℤ), ∀ S', S ⊆ S' → y = ∑ ka ∈ S', jointE ee ka y := by
  have hall := span_isoOn E ee hee hcomm hdec Finset.univ y
  obtain ⟨N, f, g, hy⟩ := (Submodule.mem_span_set').1 hall
  have hg : ∀ j, ∃ ka : ι → Fin n → ℤ, ∀ i, (g j : V) ∈ isoSub (E i) (ka i) := by
    intro j
    obtain ⟨ka, hka⟩ := (g j).2
    exact ⟨ka, fun i => hka i (Finset.mem_univ i)⟩
  choose kx hkx using hg
  have key : ∀ (x : V) (ka : ι → Fin n → ℤ), (∀ i, x ∈ isoSub (E i) (ka i)) →
      ∀ ka' : ι → Fin n → ℤ, jointE ee ka' x = if ka' = ka then x else 0 := by
    intro x ka hx ka'
    unfold jointE
    have hL : ∀ L : List ι, (L.map fun i => ee i (ka' i)).prod x = if ∀ i ∈ L, ka' i = ka i then x else 0 := by
      intro L
      induction L with
      | nil => simp
      | cons a L ih =>
        rw [List.map_cons, List.prod_cons, Module.End.mul_apply, ih]
        by_cases hL : ∀ i ∈ L, ka' i = ka i
        · rw [if_pos hL]
          by_cases ha : ka' a = ka a
          · rw [ha, (hee a (ka a)).1 x (hx a), if_pos]
            intro i hi
            rcases List.mem_cons.1 hi with rfl | hi
            · exact ha
            · exact hL i hi
          · rw [(hee a (ka' a)).2 (ka a) (Ne.symm ha) x (hx a), if_neg]
            intro h
            exact ha (h a List.mem_cons_self)
        · rw [if_neg hL, map_zero, if_neg]
          intro h
          exact hL fun i hi => h i (List.mem_cons_of_mem _ hi)
    rw [hL]
    congr 1
    apply propext
    constructor
    · intro h
      funext i
      exact h i (Finset.mem_toList.2 (Finset.mem_univ i))
    · intro h i _
      rw [h]
  refine ⟨Finset.univ.image kx, fun S' hS' => ?_⟩
  rw [← hy]
  simp_rw [map_sum, map_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.smul_sum]
  congr 1
  rw [Finset.sum_congr rfl fun ka _ => key _ _ (hkx j) ka, Finset.sum_ite_eq']
  rw [if_pos (hS' (Finset.mem_image_of_mem kx (Finset.mem_univ j)))]

end Dec

end Formalism.MainNotions.LetterSubstitution
