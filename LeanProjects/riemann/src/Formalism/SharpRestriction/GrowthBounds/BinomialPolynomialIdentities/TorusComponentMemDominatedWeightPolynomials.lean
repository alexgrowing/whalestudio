import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.RestSplit

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory

section fwd

variable {R : Type} [Field R] {ι : Type} [Fintype ι] (LL : Letters ι) {n : ℕ} (S : Set ι)
  (Pr : (Fin n → ℤ) → Prop)

def dominatedWeightPolynomials : Submodule R (MvPolynomial (ι × Fin n) R) where
  carrier := {y | ∀ (k1 : Type) [CommRing k1] (φ : R →+* k1) (g0 g0inv : Matrix (Fin n) (Fin n) k1),
    g0 * g0inv = 1 → ∀ m ∈ (matrixSubst LL S φ g0inv g0 y).support, Pr (wtS LL S m)}
  zero_mem' := by
    intro k1 _ φ g0 g0inv _ m hm
    simp at hm
  add_mem' := by
    classical
    intro x y hx hy k1 _ φ g0 g0inv h m hm
    rw [map_add] at hm
    rcases Finset.mem_union.1 (MvPolynomial.support_add hm) with h1 | h1
    · exact hx k1 φ g0 g0inv h m h1
    · exact hy k1 φ g0 g0inv h m h1
  smul_mem' := by
    intro c y hy k1 _ φ g0 g0inv h m hm
    rw [MvPolynomial.smul_eq_C_mul, map_mul, matrixSubst_C, ← MvPolynomial.smul_eq_C_mul] at hm
    exact hy k1 φ g0 g0inv h m (MvPolynomial.support_smul hm)

theorem laurentCoeff_mem_dominatedWeightPolynomials (y : MvPolynomial (ι × Fin n) R) (K : Finset ℤ) (yk : ℤ → MvPolynomial (ι × Fin n) R)
    (hh : ∀ (k1 : Type) [CommRing k1] (φ : R →+* k1), ∃ h h' : Matrix (Fin n) (Fin n) (LaurentPolynomial k1),
      h' * h = 1 ∧ matrixSubst LL S (LaurentPolynomial.C.comp φ) h h' y =
        ∑ k ∈ K, C (LaurentPolynomial.T k) * MvPolynomial.map (LaurentPolynomial.C.comp φ) (yk k))
    (hy : y ∈ dominatedWeightPolynomials LL S Pr) : ∀ k ∈ K, yk k ∈ dominatedWeightPolynomials LL S Pr := by
  classical
  intro k0 hk0 k1 _ φ g0 g0inv hg m hm
  obtain ⟨h, h', hh1, hh2⟩ := hh k1 φ
  set ψ : k1 →+* LaurentPolynomial k1 := LaurentPolynomial.C with hψ
  have hone : (h' * g0.map ψ) * (g0inv.map ψ * h) = 1 := by
    have : g0.map ψ * g0inv.map ψ = 1 := by
      rw [← Matrix.map_mul, hg]; simp
    calc (h' * g0.map ψ) * (g0inv.map ψ * h) = h' * (g0.map ψ * g0inv.map ψ) * h := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [this, Matrix.mul_one, hh1]
  refine hy (LaurentPolynomial k1) (ψ.comp φ) (h' * g0.map ψ) (g0inv.map ψ * h) hone m ?_
  rw [← matrixSubst_comp, hh2, map_sum]
  have h1 : ∀ k, matrixSubst LL S (RingHom.id _) (g0inv.map ψ) (g0.map ψ)
      (C (LaurentPolynomial.T k) * MvPolynomial.map (ψ.comp φ) (yk k)) =
      C (LaurentPolynomial.T k) * MvPolynomial.map ψ (matrixSubst LL S φ g0inv g0 (yk k)) := by
    intro k
    rw [map_mul, matrixSubst_C, RingHom.id_apply, matrixSubst_map, map_matrixSubst]
  simp only [h1]
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sum]
  intro h0
  have h2 := congrArg (fun f : LaurentPolynomial k1 => f.coeff k0) h0
  simp only [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map] at h2
  have h3 : ∀ k, (LaurentPolynomial.T k * ψ (coeff m (matrixSubst LL S φ g0inv g0 (yk k)))) =
      AddMonoidAlgebra.single k (coeff m (matrixSubst LL S φ g0inv g0 (yk k))) := by
    intro k
    rw [LaurentPolynomial.single_eq_C_mul_T, mul_comm]
  simp only [h3, AddMonoidAlgebra.coeff_sum, AddMonoidAlgebra.coeff_single, Finsupp.coe_finsetSum,
    Finset.sum_apply, Finsupp.single_apply, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] at h2
  rw [Finset.sum_ite_eq' K k0] at h2
  rw [if_pos hk0] at h2
  exact (MvPolynomial.mem_support_iff.1 hm) h2

theorem dividedPower_mem_dominatedWeightPolynomials (hT : TransvectionExpansion) (a b : Fin n) (hab : a ≠ b) (k : ℕ) (y : MvPolynomial (ι × Fin n) R)
    (hy : y ∈ dominatedWeightPolynomials LL S Pr) : divPow R LL S a b k y ∈ dominatedWeightPolynomials LL S Pr := by
  classical
  have := laurentCoeff_mem_dominatedWeightPolynomials LL S Pr y ((Finset.range (y.totalDegree + k + 1)).map Nat.castEmbedding)
    (fun z => divPow R LL S a b z.toNat y) ?_ hy (k : ℤ) ?_
  · simpa using this
  · intro k1 _ φ
    refine ⟨Matrix.transvection a b (LaurentPolynomial.T 1), Matrix.transvection a b (-LaurentPolynomial.T 1), ?_, ?_⟩
    · rw [Matrix.transvection_mul_transvection_same a b hab]; simp
    · rw [hT R (LaurentPolynomial k1) ι LL n S (LaurentPolynomial.C.comp φ) a b hab (LaurentPolynomial.T 1) y
        (y.totalDegree + k + 1) (by omega), Finset.sum_map]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [LaurentPolynomial.T_pow]
  · simp only [Finset.mem_map, Finset.mem_range]
    exact ⟨k, by omega, rfl⟩

theorem torusComponent_mem_dominatedWeightPolynomials (hTo : TorusActsThroughWeight) (a : Fin n) (w : ℤ) (y : MvPolynomial (ι × Fin n) R)
    (hy : y ∈ dominatedWeightPolynomials LL S Pr) : weightEntryComponent LL S a w y ∈ dominatedWeightPolynomials LL S Pr := by
  classical
  by_cases hw : w ∈ y.support.image (fun m => wtS LL S m a)
  · refine laurentCoeff_mem_dominatedWeightPolynomials LL S Pr y (y.support.image (fun m => wtS LL S m a)) (fun z => weightEntryComponent LL S a z y) ?_ hy w hw
    intro k1 _ φ
    set D : Fin n → (LaurentPolynomial k1)ˣ := fun c => if c = a then laurentUnit k1 else 1 with hD
    refine ⟨Matrix.diagonal fun c => ((D c : (LaurentPolynomial k1)ˣ) : LaurentPolynomial k1),
      Matrix.diagonal fun c => (((D c)⁻¹ : (LaurentPolynomial k1)ˣ) : LaurentPolynomial k1), ?_, ?_⟩
    · rw [Matrix.diagonal_mul_diagonal]
      simp
    · have hprod : ∀ m : ι × Fin n →₀ ℕ, ((∏ c, D c ^ (wtS LL S m c) : (LaurentPolynomial k1)ˣ) :
          LaurentPolynomial k1) = LaurentPolynomial.T (wtS LL S m a) := by
        intro m
        rw [← laurentUnit_zpow]
        congr 1
        rw [Finset.prod_eq_single a]
        · simp [hD]
        · intro c _ hc; simp [hD, hc]
        · intro h; exact absurd (Finset.mem_univ a) h
      conv_lhs => rw [y.as_sum, map_sum]
      rw [← Finset.sum_fiberwise_of_maps_to (s := y.support) (t := y.support.image (fun m => wtS LL S m a))
        (g := fun m => wtS LL S m a) (fun m hm => Finset.mem_image_of_mem _ hm)]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [weightEntryComponent, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m hm => ?_
      rw [hTo R (LaurentPolynomial k1) ι LL n S (LaurentPolynomial.C.comp φ) D m (y.coeff m), hprod,
        (Finset.mem_filter.1 hm).2, MvPolynomial.map_monomial, MvPolynomial.C_mul_monomial, mul_comm]
  · have : weightEntryComponent LL S a w y = 0 := by
      rw [weightEntryComponent]
      apply Finset.sum_eq_zero
      intro m hm
      exact absurd (Finset.mem_image.2 ⟨m, (Finset.mem_filter.1 hm).1, (Finset.mem_filter.1 hm).2⟩) hw
    rw [this]; exact Submodule.zero_mem _

theorem binomialPol_mem_dominatedWeightPolynomials (hTo : TorusActsThroughWeight) (a : Fin n) (k : ℕ) (y : MvPolynomial (ι × Fin n) R)
    (hy : y ∈ dominatedWeightPolynomials LL S Pr) : binomPol R LL S a k y ∈ dominatedWeightPolynomials LL S Pr := by
  classical
  have : binomPol R LL S a k y = ∑ z ∈ y.support.image (fun m => wtS LL S m a),
      (((Ring.choose z k : ℤ) : R)) • weightEntryComponent LL S a z y := by
    conv_lhs => rw [y.as_sum, map_sum]
    rw [← Finset.sum_fiberwise_of_maps_to (s := y.support) (t := y.support.image (fun m => wtS LL S m a))
        (g := fun m => wtS LL S m a) (fun m hm => Finset.mem_image_of_mem _ hm)]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [weightEntryComponent, Finset.smul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [binomialOperator_monomial, (Finset.mem_filter.1 hm).2, MvPolynomial.smul_monomial, smul_eq_mul, mul_comm]
  rw [this]
  exact Submodule.sum_mem _ fun z _ => Submodule.smul_mem _ _ (torusComponent_mem_dominatedWeightPolynomials LL S Pr hTo a z y hy)

end fwd

theorem restFwd : RestFwd := by
  classical
  intro R _ ι _ LL n S Pr G hG
  have hGN : G ∈ dominatedWeightPolynomials LL S Pr := hG
  have hstab : ∀ u ∈ Submonoid.closure (polUZgens R LL S), ∀ y ∈ dominatedWeightPolynomials LL S Pr, u y ∈ dominatedWeightPolynomials LL S Pr := by
    intro u hu
    induction hu using Submonoid.closure_induction with
    | mem u hu =>
      intro y hy
      rcases hu with ⟨a, b, k, hab, rfl⟩ | ⟨a, k, rfl⟩
      · exact dividedPower_mem_dominatedWeightPolynomials LL S Pr transvectionExpansion a b hab k y hy
      · exact binomialPol_mem_dominatedWeightPolynomials LL S Pr torus_acts_through_weight a k y hy
    | one => intro y hy; exact hy
    | mul u v _ _ hu hv => intro y hy; exact hu _ (hv y hy)
  have hW : polGenSub R LL S G ≤ dominatedWeightPolynomials LL S Pr := by
    rw [polGenSub, Submodule.span_le]
    rintro x ⟨u, hu, rfl⟩
    exact hstab u hu G hGN
  rintro mu ⟨x, hx, hx0, hmu⟩
  obtain ⟨m, hm⟩ := MvPolynomial.support_nonempty.2 hx0
  have := hW hx R (RingHom.id R) 1 1 (by simp) m (by rw [matrixSubst_one, MvPolynomial.map_id]; exact hm)
  rw [hmu m hm] at this
  exact this

theorem restAct : RestAct := by
  classical
  intro R B' _ _ N n i LL φ m m' G
  have : ((rename (iv N n) : MvPolynomial (Fin N × Fin n) B' →ₐ[B'] MvPolynomial (ℕ × Fin n) B').toRingHom.comp
        (matrixSubst LL {j : Fin N | j.val < i} φ m m')) =
      ((actI (isV LL) i m m').toRingHom.comp ((MvPolynomial.map φ).comp
        (rename (iv N n) : MvPolynomial (Fin N × Fin n) R →ₐ[R] MvPolynomial (ℕ × Fin n) R).toRingHom)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [matrixSubst_C, actI]
    · rintro ⟨l, a⟩
      have hv : isV LL l.val = LL.vec l := by simp [isV, l.2]
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, matrixSubst_X, rename_X, map_X, actI,
        aeval_X, iv, Set.mem_ofPred_eq, hv]
      by_cases hS : l.val < i
      · by_cases hvec : LL.vec l = true
        · simp only [if_pos hS, if_pos hvec, map_sum, map_mul, rename_C, rename_X, iv]
          exact Finset.sum_congr rfl fun b _ => mul_comm _ _
        · simp only [if_pos hS, if_neg hvec, map_sum, map_mul, rename_C, rename_X, iv]
          exact Finset.sum_congr rfl fun b _ => mul_comm _ _
      · simp only [if_neg hS, rename_X, iv]
  exact congrArg (fun f => f G) this

theorem monomialWeight_eq_letterWeight {N n : ℕ} (LL : Letters (Fin N)) (i : ℕ) (m : Fin N × Fin n →₀ ℕ) :
    Finsupp.weight (wtI (isV LL) i) (m.mapDomain (iv N n)) = wtS LL {j : Fin N | j.val < i} m := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_mapDomain_index (h := fun x c => c • wtI (isV LL) i x)
    (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
  funext a
  rw [Finsupp.sum_fintype m (fun x c => c • wtI (isV LL) i (iv N n x)) (fun _ => zero_smul _ _), Finset.sum_apply,
    Fintype.sum_prod_type, wtS]
  refine Finset.sum_congr rfl fun l _ => ?_
  have hv : isV LL l.val = LL.vec l := by simp [isV, l.2]
  simp only [Pi.smul_apply, wtI, iv, Set.mem_ofPred_eq, Formalism.InvariantFactorPaths.GelfandTsetlinBases.torusW, hv]
  by_cases hS : l.val < i
  · by_cases hvec : LL.vec l = true
    · simp only [if_pos hS, if_pos hvec]
      rw [Finset.sum_eq_single a]
      · simp
      · intro b _ hb; simp [Ne.symm hb]
      · intro h; exact absurd (Finset.mem_univ a) h
    · simp only [if_pos hS, if_neg hvec]
      rw [Finset.sum_eq_single a]
      · simp
      · intro b _ hb; simp [Ne.symm hb]
      · intro h; exact absurd (Finset.mem_univ a) h
  · simp [if_neg hS]

theorem dominanceOrder_iff {n : ℕ} (nu mu : Fin n → ℤ) : DomLE nu mu ↔ Formalism.InvariantFactorPaths.GelfandTsetlinBases.DomLe nu mu := by
  classical
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h2, fun j => ?_⟩
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp
    · by_cases hjn : j ≤ n
      · have e : (univ.filter fun m : Fin n => m.val < j) = univ.filter (· ≤ (⟨j - 1, by omega⟩ : Fin n)) := by
          ext m
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def]
          omega
        rw [e]
        exact h1 _
      · have e : (univ.filter fun m : Fin n => m.val < j) = univ := by
          ext m
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
          have := m.2
          omega
        rw [e, h2]
  · rintro ⟨h1, h2⟩
    refine ⟨fun a => ?_, h1⟩
    have e : (univ.filter (· ≤ a)) = univ.filter fun m : Fin n => m.val < a.val + 1 := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def]
      omega
    rw [e]
    exact h2 _

theorem standardWord_monomial_weight_dominated (hW : RestWord) (F : Type) [Field F] {N n : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ}
    (i : Fin (N + 1)) (P : PPath n N LL B) (I : ℤ → Finset (Fin n)) (hI : IsSt P.mu I)
    (k1 : Type) [CommRing k1] (φ : F →+* k1) (g0 g0inv : Matrix (Fin n) (Fin n) k1) (hg : g0 * g0inv = 1)
    (m : Fin N × Fin n →₀ ℕ)
    (hm : m ∈ (matrixSubst LL {j : Fin N | j.val < i.val} φ g0inv g0 (Psi F P.mu I)).support) :
    DomLE (wtS LL {j : Fin N | j.val < i.val} m) (P.mu i) := by
  classical
  have hidx : Formalism.InvariantFactorPaths.GelfandTsetlinBases.IsIndex (pEnd P.mu) I := ((restStd n N P.mu I).1 hI).1
  have hidx' : Formalism.InvariantFactorPaths.GelfandTsetlinBases.IsIndex (ext P.mu N) I := by rw [ext_last]; exact hidx
  have hpath := restPathTo n N LL B P
  have h1 := hW k1 n N i.val (isV LL) (Bn B) (ext P.mu) I g0inv g0 (mul_eq_one_comm.1 hg) hpath hidx'
    (Nat.lt_succ_iff.1 i.2) (m.mapDomain (iv N n)) ?_
  · rw [monomialWeight_eq_letterWeight, ext_val] at h1
    exact (dominanceOrder_iff _ _).2 h1
  · rw [← Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3ev.map_psi φ hpath hidx', ← restPsi F n N LL B P I hidx,
      ← restAct F k1 N n i.val LL φ g0inv g0, MvPolynomial.mem_support_iff,
      MvPolynomial.coeff_rename_mapDomain _ (iv_inj N n)]
    exact MvPolynomial.mem_support_iff.1 hm

theorem firstLettersLowerSet_of_restWord_restOne (D : Formalism.BasicNotions.D7) (hW : RestWord) (hO : RestOne) : Formalism.MainNotions.CovariantDegrees.FirstLettersLowerSet D := by
  classical
  intro F _ N n LL B i pi hpi G hG
  have hLow : LowerC pi := fun μ hμ ν hν hd => hpi.2 μ hμ ν hν ((dominanceOrder_iff ν μ).2 hd)
  constructor
  · intro hGs mu hmu hdom
    have key := restFwd F (Fin N) LL n {j : Fin N | j.val < i.val} (fun mu => ∃ ν ∈ pi, DomLE mu ν) G ?_ mu hmu
    · obtain ⟨ν, hν, hd⟩ := key
      exact hpi.2 ν hν mu hdom hd
    · intro k1 _ φ g0 g0inv hg
      refine Submodule.span_induction
        (p := fun x _ => ∀ m ∈ (matrixSubst LL {j : Fin N | j.val < i.val} φ g0inv g0 x).support,
          ∃ ν ∈ pi, DomLE (wtS LL {j : Fin N | j.val < i.val} m) ν) ?_ ?_ ?_ ?_ hGs
      · rintro x ⟨P, I, hI, hPi, rfl⟩ m hm
        exact ⟨P.mu i, hPi, standardWord_monomial_weight_dominated hW F i P I hI k1 φ g0 g0inv hg m hm⟩
      · intro m hm
        simp at hm
      · intro x y _ _ hx hy m hm
        rw [map_add] at hm
        rcases Finset.mem_union.1 (MvPolynomial.support_add hm) with h1 | h1
        · exact hx m h1
        · exact hy m h1
      · intro c x _ hx m hm
        rw [MvPolynomial.smul_eq_C_mul, map_mul, matrixSubst_C, ← MvPolynomial.smul_eq_C_mul] at hm
        exact hx m (MvPolynomial.support_smul hm)
  · intro H
    have hGood : GoodC F (isV LL) i.val pi (rename (iv N n) G) := by
      intro e he hanti
      rw [← restAct F (Formalism.InvariantFactorPaths.GelfandTsetlinBases.GenField F n) N n i.val LL (algebraMap F (Formalism.InvariantFactorPaths.GelfandTsetlinBases.GenField F n))
        (Formalism.InvariantFactorPaths.GelfandTsetlinBases.genMat F n) (Formalism.InvariantFactorPaths.GelfandTsetlinBases.genMat F n)⁻¹ G,
        MvPolynomial.support_rename_of_injective (iv_inj N n)] at he
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 he
      rw [monomialWeight_eq_letterWeight] at hanti ⊢
      have hm' := generic_monomials_specialise F (Fin N) LL n {j : Fin N | j.val < i.val} (Formalism.InvariantFactorPaths.GelfandTsetlinBases.GenField F n)
        (algebraMap F (Formalism.InvariantFactorPaths.GelfandTsetlinBases.GenField F n)) (Formalism.InvariantFactorPaths.GelfandTsetlinBases.genMat F n)⁻¹ (Formalism.InvariantFactorPaths.GelfandTsetlinBases.genMat F n)
        (Matrix.nonsing_inv_mul _ Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS.genMat_isUnit) G hm
      exact H _ (generic_translate_weights_mem LL _ transvectionExpansion torus_acts_through_weight binomial_stable_contains_components G m hm') hanti
    have hmem : rename (iv N n) G ∈ Formalism.InvariantFactorPaths.GelfandTsetlinBases.polB F n N (Bn B) := by
      rw [← restPol F n N B]
      exact Submodule.mem_map_of_mem hG
    have h1 := hO F n N i.val (isV LL) (Bn B) pi (rename (iv N n) G) hLow (Nat.lt_succ_iff.1 i.2) hmem hGood
    set f : MvPolynomial (Fin N × Fin n) F →ₗ[F] MvPolynomial (ℕ × Fin n) F :=
      (rename (iv N n) : MvPolynomial (Fin N × Fin n) F →ₐ[F] MvPolynomial (ℕ × Fin n) F).toLinearMap with hf
    have hinj : Function.Injective f := rename_injective _ (iv_inj N n)
    set T : Set (MvPolynomial (Fin N × Fin n) F) := {H | ∃ P : PPath n N LL B, ∃ I : ℤ → Finset (Fin n),
      IsSt P.mu I ∧ P.mu i ∈ pi ∧ H = Psi F P.mu I} with hT
    have hle : Submodule.span F (Formalism.InvariantFactorPaths.GelfandTsetlinBases.psiFam F n N (isV LL) (Bn B) '' {x | x.1.1 i.val ∈ pi}) ≤
        (Submodule.span F T).map f := by
      rw [Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨x, rfl⟩ := (e17 restPathTo restPathFrom restStd n N LL B).surjective y
      refine ⟨Psi F x.1.1.mu x.1.2, Submodule.subset_span ⟨x.1.1, x.1.2, x.2, ?_, rfl⟩,
        rename_Psi restPathTo restPathFrom restStd restPsi F x⟩
      have hy' : ext x.1.1.mu i.val ∈ pi := hy
      rwa [ext_val] at hy'
    obtain ⟨G', hG', hGG⟩ := hle h1
    rw [← hinj hGG]
    exact hG'

end Formalism.MainNotions.G.ColumnFamilies
