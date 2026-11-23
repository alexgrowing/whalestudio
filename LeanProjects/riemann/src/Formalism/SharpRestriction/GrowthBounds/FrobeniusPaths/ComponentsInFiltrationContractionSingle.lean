import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.DividedPowerZeroOfGlActionZero
import Formalism.SharpRestriction.GrowthBounds.RootWeights.DerivativeValuationBounds

noncomputable section

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

namespace Formalism.MainNotions.LemmaBAlt

open Classical in

def twistedMatrixSubstitution {R B : Type*} [CommRing R] [CommRing B] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι)
    (φ : R →+* B) (m m' : Matrix (Fin n) (Fin n) B) :
    MvPolynomial (ι × Fin n) R →+* MvPolynomial (ι × Fin n) B :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp φ) fun v =>
    if v.1 ∈ S then
      (if LL.vec v.1 then ∑ b : Fin n, MvPolynomial.C (m b v.2) * X (v.1, b)
       else ∑ b : Fin n, MvPolynomial.C (m' v.2 b) * X (v.1, b))
    else X v

section basic

variable {R R' B B' : Type*} [CommRing R] [CommRing R'] [CommRing B] [CommRing B'] {ι : Type*} {n : ℕ}
  (LL : Letters ι) (S : Set ι)

theorem twist_substitution_eq_action (j : Fin n) :
    twistSub (R := R) LL S j = twistedMatrixSubstitution LL S (coefL R n) (twistMat R n j 1) (twistMat R n j (-1)) := rfl

theorem twisted_action_C (φ : R →+* B) (m m' : Matrix (Fin n) (Fin n) B) (c : R) :
    twistedMatrixSubstitution LL S φ m m' (C c) = C (φ c) := by
  simp [twistedMatrixSubstitution]

open Classical in
theorem twisted_action_X (φ : R →+* B) (m m' : Matrix (Fin n) (Fin n) B) (v : ι × Fin n) :
    twistedMatrixSubstitution LL S φ m m' (X v) = if v.1 ∈ S then
      (if LL.vec v.1 then ∑ b : Fin n, MvPolynomial.C (m b v.2) * X (v.1, b)
       else ∑ b : Fin n, MvPolynomial.C (m' v.2 b) * X (v.1, b))
    else X v := by
  simp [twistedMatrixSubstitution]

theorem map_twisted_action (φ : R →+* B) (ψ : B →+* B') (m m' : Matrix (Fin n) (Fin n) B)
    (F : MvPolynomial (ι × Fin n) R) :
    MvPolynomial.map ψ (twistedMatrixSubstitution LL S φ m m' F) = twistedMatrixSubstitution LL S (ψ.comp φ) (m.map ψ) (m'.map ψ) F := by
  classical
  have : (MvPolynomial.map ψ).comp (twistedMatrixSubstitution LL S φ m m') = twistedMatrixSubstitution LL S (ψ.comp φ) (m.map ψ) (m'.map ψ) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [twisted_action_C]
    · intro v
      simp only [RingHom.comp_apply, twisted_action_X]
      split_ifs <;> simp
  exact congrArg (fun f => f F) this

theorem twisted_action_of_map (φ : R →+* R') (ψ : R' →+* B) (m m' : Matrix (Fin n) (Fin n) B)
    (F : MvPolynomial (ι × Fin n) R) :
    twistedMatrixSubstitution LL S ψ m m' (MvPolynomial.map φ F) = twistedMatrixSubstitution LL S (ψ.comp φ) m m' F := by
  classical
  have : (twistedMatrixSubstitution LL S ψ m m').comp (MvPolynomial.map φ) = twistedMatrixSubstitution LL S (ψ.comp φ) m m' := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [twisted_action_C]
    · intro v
      simp only [RingHom.comp_apply, twisted_action_X, map_X]
  exact congrArg (fun f => f F) this

end basic

section coord

variable {R R' : Type*} [CommRing R] [CommRing R'] (φ : R →+* R') (n : ℕ)

theorem map_generic_matrix : (MvPolynomial.map φ).mapMatrix (genMat R n) = genMat R' n := by
  ext a b; simp [genMat]

def coordinateMap : GLCoord R n →+* GLCoord R' n :=
  IsLocalization.Away.lift (genMat R n).det
    (g := (algebraMap (MvPolynomial (Fin n × Fin n) R') (GLCoord R' n)).comp (MvPolynomial.map φ))
    (by rw [RingHom.comp_apply, RingHom.map_det, map_generic_matrix]
        exact IsLocalization.Away.algebraMap_isUnit _)

theorem coordinate_map_algebraMap (x : MvPolynomial (Fin n × Fin n) R) :
    coordinateMap φ n (algebraMap _ _ x) = algebraMap _ _ (MvPolynomial.map φ x) :=
  IsLocalization.Away.lift_eq _ _ x

theorem coordinate_map_inv_det :
    coordinateMap φ n (IsLocalization.Away.invSelf (genMat R n).det) = IsLocalization.Away.invSelf (genMat R' n).det := by
  have h1 : coordinateMap φ n (algebraMap _ _ (genMat R n).det * IsLocalization.Away.invSelf (genMat R n).det) = 1 := by
    rw [IsLocalization.Away.mul_invSelf, map_one]
  rw [map_mul, coordinate_map_algebraMap, RingHom.map_det, map_generic_matrix] at h1
  have h2 := IsLocalization.Away.mul_invSelf (S := GLCoord R' n) (genMat R' n).det
  have hu : IsUnit (algebraMap _ (GLCoord R' n) (genMat R' n).det) := IsLocalization.Away.algebraMap_isUnit _
  exact hu.mul_left_cancel (h1.trans h2.symm)

def laurentBaseChange : GLLaurent R n →+* GLLaurent R' n := AddMonoidAlgebra.mapRingHom ℤ (coordinateMap φ n)

theorem laurent_map_C (x : GLCoord R n) : laurentBaseChange φ n (LaurentPolynomial.C x) = LaurentPolynomial.C (coordinateMap φ n x) := by
  rw [← LaurentPolynomial.single_eq_C, ← LaurentPolynomial.single_eq_C]
  exact AddMonoidAlgebra.mapRingHom_single _ _ _

theorem laurentRingMap_T_eq_T (k : ℤ) : laurentBaseChange φ n (LaurentPolynomial.T k) = LaurentPolynomial.T k := by
  unfold LaurentPolynomial.T
  exact (AddMonoidAlgebra.mapRingHom_single _ _ _).trans (by rw [map_one])

theorem map_generic_inverse_matrix : (gL R n).map (laurentBaseChange φ n) = gL R' n := by
  ext a b
  simp [gL, laurent_map_C, coordinate_map_algebraMap, genMat]

theorem map_inverse_matrix : (gLinv R n).map (laurentBaseChange φ n) = gLinv R' n := by
  ext a b
  have h : MvPolynomial.map φ ((genMat R n).adjugate a b) = (genMat R' n).adjugate a b := by
    have := RingHom.map_adjugate (MvPolynomial.map φ) (genMat R n)
    rw [map_generic_matrix] at this
    rw [← this]; rfl
  simp only [gLinv, Matrix.map_apply, laurent_map_C, map_mul, coordinate_map_inv_det, coordinate_map_algebraMap, h]

theorem map_twist_matrix (j : Fin n) (k : ℤ) : (twistMat R n j k).map (laurentBaseChange φ n) = twistMat R' n j k := by
  unfold twistMat
  rw [Matrix.map_mul, Matrix.map_mul, map_generic_inverse_matrix, map_inverse_matrix, Matrix.diagonal_map (map_zero _)]
  congr 3
  funext a
  by_cases h : a = j <;> simp [h, laurentRingMap_T_eq_T]

theorem laurent_map_comp_coefficient : (laurentBaseChange φ n).comp (coefL R n) = (coefL R' n).comp φ := by
  ext r
  simp [coefL, laurent_map_C, coordinate_map_algebraMap]

end coord

theorem twist_substitution_map {R R' : Type*} [CommRing R] [CommRing R'] (φ : R →+* R') {ι : Type*} {n : ℕ}
    (LL : Letters ι) (S : Set ι) (j : Fin n) (G : MvPolynomial (ι × Fin n) R) :
    twistSub LL S j (MvPolynomial.map φ G) = MvPolynomial.map (laurentBaseChange φ n) (twistSub LL S j G) := by
  rw [twist_substitution_eq_action, twist_substitution_eq_action, twisted_action_of_map, map_twisted_action, map_twist_matrix, map_twist_matrix, laurent_map_comp_coefficient]

theorem mem_support_degrees_iff {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι) (j : Fin n)
    (G : MvPolynomial (ι × Fin n) R) (k : ℤ) :
    k ∈ sDegs LL S j G ↔ ∃ m, ((twistSub LL S j G).coeff m).coeff k ≠ 0 := by
  unfold sDegs
  simp only [Finset.mem_biUnion, Finsupp.mem_support_iff, MvPolynomial.mem_support_iff]
  constructor
  · rintro ⟨m, _, h⟩; exact ⟨m, h⟩
  · rintro ⟨m, h⟩
    refine ⟨m, ?_, h⟩
    intro h0
    apply h
    rw [h0]; simp

theorem support_degrees_map_subset {R R' : Type*} [CommRing R] [CommRing R'] (φ : R →+* R') {ι : Type*} {n : ℕ}
    (LL : Letters ι) (S : Set ι) (j : Fin n) (G : MvPolynomial (ι × Fin n) R) :
    sDegs LL S j (MvPolynomial.map φ G) ⊆ sDegs LL S j G := by
  intro k hk
  rw [mem_support_degrees_iff] at hk ⊢
  obtain ⟨m, hm⟩ := hk
  refine ⟨m, fun h0 => hm ?_⟩
  rw [twist_substitution_map, MvPolynomial.coeff_map]
  unfold laurentBaseChange
  rw [AddMonoidAlgebra.coeff_mapRingHom, h0, map_zero]

theorem support_degrees_add_subset {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι) (j : Fin n)
    (F G : MvPolynomial (ι × Fin n) R) {k : ℤ} (hk : k ∈ sDegs LL S j (F + G)) :
    k ∈ sDegs LL S j F ∨ k ∈ sDegs LL S j G := by
  rw [mem_support_degrees_iff] at hk
  obtain ⟨m, hm⟩ := hk
  by_contra hcon
  rw [not_or, mem_support_degrees_iff, mem_support_degrees_iff] at hcon
  push Not at hcon
  apply hm
  rw [map_add, MvPolynomial.coeff_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hcon.1 m, hcon.2 m, add_zero]

theorem support_degrees_smul_subset {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι) (j : Fin n)
    (a : R) (G : MvPolynomial (ι × Fin n) R) {k : ℤ} (hk : k ∈ sDegs LL S j (a • G)) :
    k ∈ sDegs LL S j G := by
  rw [mem_support_degrees_iff] at hk ⊢
  obtain ⟨m, hm⟩ := hk
  refine ⟨m, fun h0 => hm ?_⟩
  rw [MvPolynomial.smul_eq_C_mul, map_mul, twist_substitution_eq_action, twisted_action_C, MvPolynomial.coeff_C_mul]
  rw [twist_substitution_eq_action] at h0
  have hc : coefL R n a = AddMonoidAlgebra.single 0 ((algebraMap (MvPolynomial (Fin n × Fin n) R) (GLCoord R n)) (C a)) := rfl
  rw [hc, AddMonoidAlgebra.coeff_single_zero_mul, h0, mul_zero]

theorem support_degrees_zero {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι) (j : Fin n) :
    sDegs LL S j (0 : MvPolynomial (ι × Fin n) R) = ∅ := by
  ext k
  rw [mem_support_degrees_iff]
  simp

theorem le_valuation_iff_support_degrees {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    (G : MvPolynomial (ι × Fin n) R) (t : ℤ) :
    (t : WithTop ℤ) ≤ valS LL S G ↔ ∀ k ∈ sDegs LL S (lastIdx n) G, t ≤ k := by
  unfold valS
  rw [Finset.le_inf_iff]
  simp only [WithTop.coe_le_coe]

theorem lambda_le_iff_support_degrees {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    (G : MvPolynomial (ι × Fin n) R) (M : ℤ) :
    lam1S LL S G ≤ (M : WithBot ℤ) ↔ ∀ k ∈ sDegs LL S (0 : Fin n) G, k ≤ M := by
  unfold lam1S
  rw [Finset.sup_le_iff]
  simp only [WithBot.coe_le_coe]

def boundedDominantWeights {n : ℕ} [NeZero n] (th M : ℤ) : Set (Fin n → ℤ) := {mu | Dominant mu ∧ th ≤ mu (lastIdx n) ∧ mu 0 ≤ M}

theorem bounded_dominant_lower_set {n : ℕ} [NeZero n] (th M : ℤ) : DomLowerSet (boundedDominantWeights (n := n) th M) := by
  refine ⟨fun mu h => h.1, ?_⟩
  rintro mu ⟨_, h1, h2⟩ nu hnu ⟨hle, htot⟩
  refine ⟨hnu, ?_, ?_⟩
  · by_cases hn : n = 1
    · subst hn
      have e : lastIdx 1 = 0 := Subsingleton.elim _ _
      rw [e] at h1 ⊢
      simp only [Fin.sum_univ_one, Fin.isValue] at htot
      omega
    · have hpos := NeZero.pos n
      let a : Fin n := ⟨n - 2, by omega⟩
      have hf : (univ.filter fun b : Fin n => ¬ b ≤ a) = {lastIdx n} := by
        ext b
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.le_def, Fin.ext_iff, lastIdx, a]
        have := b.2
        omega
      have s1 := Finset.sum_filter_add_sum_filter_not univ (fun b : Fin n => b ≤ a) nu
      have s2 := Finset.sum_filter_add_sum_filter_not univ (fun b : Fin n => b ≤ a) mu
      rw [hf, Finset.sum_singleton] at s1 s2
      have := hle a
      omega
  · have hf : (univ.filter fun b : Fin n => b ≤ 0) = {0} := by
      ext b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.le_def, Fin.ext_iff,
        Fin.val_zero]
      omega
    have := hle 0
    rw [hf, Finset.sum_singleton, Finset.sum_singleton] at this
    omega

theorem support_subset_of_mem_span_image {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] {v : ι → M}
    (hv : LinearIndependent R v) (l : ι →₀ R) (s : Set ι)
    (h : Finsupp.linearCombination R v l ∈ Submodule.span R (v '' s)) : (l.support : Set ι) ⊆ s := by
  obtain ⟨l', hl', e⟩ := (Finsupp.mem_span_image_iff_linearCombination R).1 h
  have : l' = l := hv e
  subst this
  exact (Finsupp.mem_supported R _).1 hl'

section words

variable {N n : ℕ} (LL : Letters (Fin N)) (B : Fin N → ℕ)

abbrev StandardWordIndex (n : ℕ) {N : ℕ} (LL : Letters (Fin N)) (B : Fin N → ℕ) :=
  {x : PPath n N LL B × (ℤ → Finset (Fin n)) // IsSt x.1.mu x.2}

def columnWord (R : Type*) [CommRing R] (x : StandardWordIndex n LL B) : MvPolynomial (Fin N × Fin n) R := Psi R x.1.1.mu x.1.2

theorem standard_word_set_eq_image (R : Type*) [CommRing R] (cond : PPath n N LL B → Prop) :
    {G | ∃ P : PPath n N LL B, ∃ I : ℤ → Finset (Fin n), IsSt P.mu I ∧ cond P ∧ G = Psi R P.mu I} =
      columnWord LL B R '' {x | cond x.1.1} := by
  ext G
  constructor
  · rintro ⟨P, I, hI, hc, rfl⟩; exact ⟨⟨(P, I), hI⟩, hc, rfl⟩
  · rintro ⟨⟨⟨P, I⟩, hI⟩, hc, rfl⟩; exact ⟨P, I, hI, hc, rfl⟩

theorem standard_words_eq_range (R : Type*) [CommRing R] :
    {G | ∃ P : PPath n N LL B, ∃ I : ℤ → Finset (Fin n), IsSt P.mu I ∧ G = Psi R P.mu I} =
      Set.range (columnWord LL B R) := by
  ext G
  constructor
  · rintro ⟨P, I, hI, rfl⟩; exact ⟨⟨(P, I), hI⟩, rfl⟩
  · rintro ⟨⟨⟨P, I⟩, hI⟩, rfl⟩; exact ⟨P, I, hI, rfl⟩

theorem exists_linear_combination_words (D : Formalism.BasicNotions.D7) (h17 : PathBasisOverRing D) [NeZero n] (R : Type) [CommRing R]
    {G : MvPolynomial (Fin N × Fin n) R} (hG : G ∈ Pol R n B) :
    ∃ l : StandardWordIndex n LL B →₀ R, Finsupp.linearCombination R (columnWord LL B R) l = G := by
  rw [← (h17 R N n LL B).2, standard_words_eq_range] at hG
  obtain ⟨l, hl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hG
  exact ⟨l, by rw [Finsupp.linearCombination_apply]; exact hl⟩

theorem lt_succ_set_eq_le_set (i : Fin N) : {j : Fin N | j.val < i.succ.val} = {j : Fin N | j ≤ i} := by
  ext j
  simp only [Set.mem_ofPred_eq, Fin.val_succ, Fin.le_def]
  omega

theorem mem_span_words_of_valuation_bounds (D : Formalism.BasicNotions.D7) (hV : ValuationsAdditive D) (h17 : PathBasisOverRing D) (h18 : FirstLettersLowerSet D) [NeZero n]
    (F : Type) [Field F] (th M : Fin N → ℤ) {G : MvPolynomial (Fin N × Fin n) F} (hG : G ∈ Pol F n B)
    (hc : ∀ i : Fin N, ((th i : ℤ) : WithTop ℤ) ≤ valS LL {j | j ≤ i} G ∧
      lam1S LL {j | j ≤ i} G ≤ ((M i : ℤ) : WithBot ℤ)) :
    G ∈ Submodule.span F (columnWord LL B F '' {x | ∀ i : Fin N, th i ≤ x.1.1.mu i.succ (lastIdx n) ∧
      x.1.1.mu i.succ 0 ≤ M i}) := by
  obtain ⟨l, rfl⟩ := exists_linear_combination_words LL B D h17 F hG
  have hli : LinearIndependent F (columnWord LL B F) := (h17 F N n LL B).1
  refine (Finsupp.mem_span_image_iff_linearCombination F).2 ⟨l, (Finsupp.mem_supported F _).2 ?_, rfl⟩
  intro x hx i
  have hVi := hV F (Fin N) LL n {j | j ≤ i}
  have h := (h18 F N n LL B i.succ (boundedDominantWeights (th i) (M i)) (bounded_dominant_lower_set _ _) _ hG).2 (by
    rw [lt_succ_set_eq_le_set]
    intro mu hmu hdom
    exact ⟨hdom, (hVi.2.2.2.2.1 _ _).1 (hc i).1 mu hmu, (hVi.2.2.2.2.2 _ _).1 (hc i).2 mu hmu⟩)
  rw [standard_word_set_eq_image LL B F (fun P => P.mu i.succ ∈ boundedDominantWeights (th i) (M i))] at h
  have := support_subset_of_mem_span_image hli l _ h hx
  exact this.2

def WordValuationBounds : Prop :=
  ∀ (N n : ℕ) [NeZero n] (LL : Letters (Fin N)) (B : Fin N → ℕ) (P : PPath n N LL B) (I : ℤ → Finset (Fin n))
    (i : Fin N), ((P.mu i.succ (lastIdx n) : ℤ) : WithTop ℤ) ≤ valS LL {j | j ≤ i} (Psi ℤ P.mu I) ∧
      lam1S LL {j | j ≤ i} (Psi ℤ P.mu I) ≤ ((P.mu i.succ 0 : ℤ) : WithBot ℤ)

theorem valuation_bounds_of_mem_span_words (D : Formalism.BasicNotions.D7) (hW : WordValuationBounds) (h17 : PathBasisOverRing D) [NeZero n]
    (R : Type) [CommRing R] (th M : Fin N → ℤ) {G : MvPolynomial (Fin N × Fin n) R}
    (hG : G ∈ Submodule.span R (columnWord LL B R '' {x | ∀ i : Fin N, th i ≤ x.1.1.mu i.succ (lastIdx n) ∧
      x.1.1.mu i.succ 0 ≤ M i})) :
    G ∈ Pol R n B ∧ ∀ i : Fin N, ((th i : ℤ) : WithTop ℤ) ≤ valS LL {j | j ≤ i} G ∧
      lam1S LL {j | j ≤ i} G ≤ ((M i : ℤ) : WithBot ℤ) := by
  refine ⟨?_, fun i => ?_⟩
  · rw [← (h17 R N n LL B).2, standard_words_eq_range]
    exact Submodule.span_mono (Set.image_subset_range _ _) hG
  · rw [le_valuation_iff_support_degrees, lambda_le_iff_support_degrees]
    induction hG using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, hx, rfl⟩ := hy
      have h := hW N n LL B x.1.1 x.1.2 i
      rw [le_valuation_iff_support_degrees, lambda_le_iff_support_degrees] at h
      have e : columnWord LL B R x = MvPolynomial.map (Int.castRingHom R) (Psi ℤ x.1.1.mu x.1.2) := (map_Psi' _ _ _).symm
      rw [e]
      exact ⟨fun k hk => (hx i).1.trans (h.1 k (support_degrees_map_subset _ _ _ _ _ hk)),
        fun k hk => (h.2 k (support_degrees_map_subset _ _ _ _ _ hk)).trans (hx i).2⟩
    | zero => simp [support_degrees_zero]
    | add y z _ _ hy hz =>
      exact ⟨fun k hk => (support_degrees_add_subset _ _ _ _ _ hk).elim (hy.1 k) (hz.1 k),
        fun k hk => (support_degrees_add_subset _ _ _ _ _ hk).elim (hy.2 k) (hz.2 k)⟩
    | smul a y _ hy =>
      exact ⟨fun k hk => hy.1 k (support_degrees_smul_subset _ _ _ _ _ hk), fun k hk => hy.2 k (support_degrees_smul_subset _ _ _ _ _ hk)⟩

theorem valuation_bounds_iff_mem_span_words (R : Type) [CommRing R] [NeZero n] (th M : Fin N → ℤ) :
    A3at R N n LL B th M ↔ ∀ G : MvPolynomial (Fin N × Fin n) R,
      (G ∈ Pol R n B ∧ ∀ i : Fin N, ((th i : ℤ) : WithTop ℤ) ≤ valS LL {j | j ≤ i} G ∧
        lam1S LL {j | j ≤ i} G ≤ ((M i : ℤ) : WithBot ℤ)) ↔
      G ∈ Submodule.span R (columnWord LL B R '' {x | ∀ i : Fin N, th i ≤ x.1.1.mu i.succ (lastIdx n) ∧
        x.1.1.mu i.succ 0 ≤ M i}) := by
  unfold A3at
  rw [standard_word_set_eq_image LL B R (fun P => ∀ i : Fin N, th i ≤ P.mu i.succ (lastIdx n) ∧ P.mu i.succ 0 ≤ M i), Set.ext_iff]
  rfl

theorem lemma_A3_over_field (D : Formalism.BasicNotions.D7) (hW : WordValuationBounds) (hV : ValuationsAdditive D) (h17 : PathBasisOverRing D) (h18 : FirstLettersLowerSet D) [NeZero n]
    (F : Type) [Field F] (th M : Fin N → ℤ) : A3at F N n LL B th M :=
  (valuation_bounds_iff_mem_span_words LL B F th M).2 fun _ =>
    ⟨fun h => mem_span_words_of_valuation_bounds LL B D hV h17 h18 F th M h.1 h.2, fun h => valuation_bounds_of_mem_span_words LL B D hW h17 F th M h⟩

theorem map_linear_combination_words {R R' : Type*} [CommRing R] [CommRing R'] (φ : R →+* R') (l : StandardWordIndex n LL B →₀ R) :
    MvPolynomial.map φ (Finsupp.linearCombination R (columnWord LL B R) l) =
      Finsupp.linearCombination R' (columnWord LL B R') (l.mapRange φ (map_zero φ)) := by
  rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index (by simp),
    Finsupp.sum, Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C]
  unfold columnWord
  rw [map_Psi']

theorem map_mem_polynomials {R R' : Type*} [CommRing R] [CommRing R'] (φ : R →+* R') {G : MvPolynomial (Fin N × Fin n) R}
    (hG : G ∈ Pol R n B) : MvPolynomial.map φ G ∈ Pol R' n B := by
  unfold Pol at hG ⊢
  rw [MvPolynomial.mem_restrictSupport_iff] at hG ⊢
  exact (Finset.coe_subset.2 (MvPolynomial.support_map_subset φ G)).trans hG

theorem lemma_A3_over_domain (D : Formalism.BasicNotions.D7) (hW : WordValuationBounds) (hV : ValuationsAdditive D) (h17 : PathBasisOverRing D) (h18 : FirstLettersLowerSet D) [NeZero n]
    (O : Type) [CommRing O] [IsDomain O] (th M : Fin N → ℤ) : A3at O N n LL B th M := by
  refine (valuation_bounds_iff_mem_span_words LL B O th M).2 fun G => ⟨fun h => ?_, fun h => valuation_bounds_of_mem_span_words LL B D hW h17 O th M h⟩
  obtain ⟨l, rfl⟩ := exists_linear_combination_words LL B D h17 O h.1
  have hK := mem_span_words_of_valuation_bounds LL B D hV h17 h18 (KK O) th M (map_mem_polynomials B (algebraMap O (KK O)) h.1) (fun i => by
    have hi := h.2 i
    rw [le_valuation_iff_support_degrees, lambda_le_iff_support_degrees] at hi ⊢
    exact ⟨fun k hk => hi.1 k (support_degrees_map_subset _ _ _ _ _ hk), fun k hk => hi.2 k (support_degrees_map_subset _ _ _ _ _ hk)⟩)
  rw [map_linear_combination_words] at hK
  have hs := support_subset_of_mem_span_image (h17 (KK O) N n LL B).1 _ _ hK
  rw [Finsupp.support_mapRange_of_injective _ _ (IsFractionRing.injective O (KK O))] at hs
  exact (Finsupp.mem_span_image_iff_linearCombination O).2 ⟨l, (Finsupp.mem_supported O _).2 hs, rfl⟩

end words

theorem lemma_A3_of_word_bound (D : Formalism.BasicNotions.D7) (hW : WordValuationBounds) (hV : ValuationLemmaField D) (hB : AdmB D) : DefiniteRankOne D := by
  have h17 : PathBasisOverRing D := hB.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h18 : FirstLettersLowerSet D := hB.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  intro p _ O _ _ _ _ N n _ LL B th M
  exact ⟨lemma_A3_over_domain LL B D hW hV.1 h17 h18 O th M, lemma_A3_over_field LL B D hW hV.1 h17 h18 (FF O) th M⟩

section rank1

variable {n : ℕ} {P : Type*} [CommRing P]

def totalWedge (v : Fin n → P) : Module.End P (Finset (Fin n) → P) := ∑ m, v m • exteriorWedge P m

def totalContraction (u : Fin n → P) : Module.End P (Finset (Fin n) → P) := ∑ m, u m • exteriorContraction P m

theorem total_contraction_wedge (u : Fin n → P) (b : Fin n) : totalContraction u * exteriorWedge P b = u b • 1 - exteriorWedge P b * totalContraction u := by
  unfold totalContraction
  rw [Finset.sum_mul, Finset.mul_sum]
  have h : ∀ m, exteriorContraction P m * exteriorWedge P b = (if b = m then 1 else 0) - exteriorWedge P b * exteriorContraction P m := fun m => by
    rw [← wedge_contraction_anticommute b m]; abel
  simp only [smul_mul_assoc, mul_smul_comm, h, smul_sub, Finset.sum_sub_distrib]
  congr 1
  simp [smul_ite, Finset.sum_ite_eq]

theorem total_wedge_contraction (v : Fin n → P) (b : Fin n) : totalWedge v * exteriorContraction P b = v b • 1 - exteriorContraction P b * totalWedge v := by
  unfold totalWedge
  rw [Finset.sum_mul, Finset.mul_sum]
  have h : ∀ m, exteriorWedge P m * exteriorContraction P b = (if m = b then 1 else 0) - exteriorContraction P b * exteriorWedge P m := fun m => by
    rw [← wedge_contraction_anticommute m b]; abel
  simp only [smul_mul_assoc, mul_smul_comm, h, smul_sub, Finset.sum_sub_distrib]
  congr 1
  simp [smul_ite, Finset.sum_ite_eq']

theorem total_wedge_anticommute_wedge (v : Fin n → P) (b : Fin n) : totalWedge v * exteriorWedge P b = -(exteriorWedge P b * totalWedge v) := by
  unfold totalWedge
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [smul_mul_assoc, mul_smul_comm, wedge_anticommute m b, smul_neg]

theorem total_contraction_anticommute (u : Fin n → P) (b : Fin n) : totalContraction u * exteriorContraction P b = -(exteriorContraction P b * totalContraction u) := by
  unfold totalContraction
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [smul_mul_assoc, mul_smul_comm, contraction_anticommute m b, smul_neg]

theorem antisymmetric_double_sum_eq_zero {A : Type*} [AddCommGroup A] (f : Fin n → Fin n → A) (h0 : ∀ a, f a a = 0)
    (h : ∀ a b, f a b = -f b a) : ∑ a, ∑ b, f a b = 0 := by
  rw [← Finset.sum_product']
  refine Finset.sum_involution (fun x _ => (x.2, x.1)) ?_ ?_ ?_ ?_
  · intro x _; rw [h x.1 x.2]; simp
  · intro x _ hx hxe
    apply hx
    have e : x.2 = x.1 := congrArg Prod.fst hxe
    rw [e]; exact h0 _
  · intro x _; simp
  · intro x _; rfl

theorem exterior_wedge_sq_zero (a : Fin n) : exteriorWedge P a * exteriorWedge P a = 0 := by
  refine LinearMap.ext fun K => funext fun J => ?_
  simp [Module.End.mul_apply, exterior_wedge_apply]

theorem exterior_contraction_sq_zero (a : Fin n) : exteriorContraction P a * exteriorContraction P a = 0 := by
  refine LinearMap.ext fun K => funext fun J => ?_
  simp [Module.End.mul_apply, exterior_contraction_apply]

theorem totalWedge_mul_self (v : Fin n → P) : totalWedge v * totalWedge v = 0 := by
  unfold totalWedge
  rw [Finset.sum_mul_sum]
  refine antisymmetric_double_sum_eq_zero _ (fun a => ?_) (fun a b => ?_)
  · rw [smul_mul_smul_comm, exterior_wedge_sq_zero, smul_zero]
  · rw [smul_mul_smul_comm, smul_mul_smul_comm, wedge_anticommute a b, smul_neg, mul_comm (v a)]

theorem total_contraction_sq_zero (u : Fin n → P) : totalContraction u * totalContraction u = 0 := by
  unfold totalContraction
  rw [Finset.sum_mul_sum]
  refine antisymmetric_double_sum_eq_zero _ (fun a => ?_) (fun a b => ?_)
  · rw [smul_mul_smul_comm, exterior_contraction_sq_zero, smul_zero]
  · rw [smul_mul_smul_comm, smul_mul_smul_comm, contraction_anticommute a b, smul_neg, mul_comm (u a)]

theorem totalContraction_mul_totalWedge (u v : Fin n → P) : totalContraction u * totalWedge v = (∑ m, u m * v m) • 1 - totalWedge v * totalContraction u := by
  have e : totalWedge v = ∑ m, v m • exteriorWedge P m := rfl
  rw [e, Finset.mul_sum, Finset.sum_mul, Finset.sum_smul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [mul_smul_comm, total_contraction_wedge, smul_sub, smul_smul, smul_mul_assoc, mul_comm (v m)]

def lambdaOperator (u v : Fin n → P) (θ : P) : Module.End P (Finset (Fin n) → P) := 1 + (θ - 1) • (totalWedge v * totalContraction u)

theorem lambda_wedge_conjugate (u v : Fin n → P) (θ : P) (b : Fin n) :
    lambdaOperator u v θ * exteriorWedge P b = (exteriorWedge P b + ((θ - 1) * u b) • totalWedge v) * lambdaOperator u v θ := by
  have h1 : totalWedge v * totalContraction u * exteriorWedge P b = u b • totalWedge v + exteriorWedge P b * (totalWedge v * totalContraction u) := by
    rw [mul_assoc, total_contraction_wedge, mul_sub, mul_smul_comm, mul_one, ← mul_assoc, total_wedge_anticommute_wedge, neg_mul, sub_neg_eq_add, mul_assoc]
  have h2 : totalWedge v * (totalWedge v * totalContraction u) = 0 := by rw [← mul_assoc, totalWedge_mul_self, zero_mul]
  unfold lambdaOperator
  simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, h1, h2, smul_zero, add_zero,
    smul_add, smul_smul]
  abel

theorem lambda_contraction_conjugate (u v : Fin n → P) (θ θ' : P) (hθ : θ * θ' = 1) (hd : ∑ m, u m * v m = 1) (b : Fin n) :
    lambdaOperator u v θ * exteriorContraction P b = (exteriorContraction P b + ((θ' - 1) * v b) • totalContraction u) * lambdaOperator u v θ := by
  have h1 : totalWedge v * totalContraction u * exteriorContraction P b = -(v b • totalContraction u) + exteriorContraction P b * (totalWedge v * totalContraction u) := by
    rw [mul_assoc, total_contraction_anticommute, mul_neg, ← mul_assoc, total_wedge_contraction, sub_mul, smul_mul_assoc, one_mul, mul_assoc]; abel
  have h3 : totalContraction u * (totalWedge v * totalContraction u) = totalContraction u := by
    rw [← mul_assoc, totalContraction_mul_totalWedge, hd, one_smul, sub_mul, one_mul, mul_assoc, total_contraction_sq_zero, mul_zero, sub_zero]
  unfold lambdaOperator
  simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, h1, h3, smul_add, smul_smul, smul_neg]
  have e : -(((θ - 1) * v b) • totalContraction u) =
      ((θ' - 1) * v b) • totalContraction u + ((θ - 1) * ((θ' - 1) * v b)) • totalContraction u := by
    rw [← add_smul, ← neg_smul]
    congr 1
    linear_combination (-(v b)) * hθ
  rw [e]
  abel

theorem conjugate_operator_sum {Q F : Type*} [CommRing Q] [AddCommGroup F] [Module Q F] (o : Fin n → Module.End Q F)
    (Lm : Module.End Q F) (al be : Fin n → Q) (τ : Q)
    (hI : ∀ b, Lm * o b = (o b + (τ * al b) • ∑ m, be m • o m) * Lm) (x : Fin n → Q) (K : F) :
    ∑ m, (x m + τ * be m * ∑ b, al b * x b) • o m (Lm K) = Lm (∑ b, x b • o b K) := by
  have h : ∀ b, Lm (o b K) = o b (Lm K) + (τ * al b) • ∑ m, be m • o m (Lm K) := by
    intro b
    have := congrArg (fun f => f K) (hI b)
    simpa [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sum_apply] using this
  rw [map_sum]
  simp only [map_smul, h, smul_add, add_smul, Finset.sum_add_distrib]
  congr 1
  simp only [smul_smul]
  rw [← Finset.sum_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [smul_smul]
  congr 1
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

theorem wedge_lambda_intertwine (u v : Fin n → P) (θ : P) (x : Fin n → P) (K : Finset (Fin n) → P) :
    wedgeR (fun m => x m + (θ - 1) * v m * ∑ b, u b * x b) (lambdaOperator u v θ K) = lambdaOperator u v θ (wedgeR x K) := by
  rw [right_wedge_eq_sum, right_wedge_eq_sum]
  exact conjugate_operator_sum (exteriorWedge P) (lambdaOperator u v θ) u v (θ - 1) (fun b => lambda_wedge_conjugate u v θ b) x K

theorem contraction_lambda_intertwine (u v : Fin n → P) (θ θ' : P) (hθ : θ * θ' = 1) (hd : ∑ m, u m * v m = 1) (x : Fin n → P)
    (K : Finset (Fin n) → P) :
    contrR (fun m => x m + (θ' - 1) * u m * ∑ b, v b * x b) (lambdaOperator u v θ K) = lambdaOperator u v θ (contrR x K) := by
  rw [right_contraction_eq_sum, right_contraction_eq_sum]
  exact conjugate_operator_sum (exteriorContraction P) (lambdaOperator u v θ) v u (θ' - 1) (fun b => lambda_contraction_conjugate u v θ θ' hθ hd b) x K

end rank1

section twist

open Formalism.MainNotions.G.GLWeightTheory

theorem twist_matrix_apply (R : Type*) [CommRing R] (n : ℕ) (j : Fin n) (k : ℤ) (b m : Fin n) :
    twistMat R n j k b m = (if b = m then 1 else 0) + (LaurentPolynomial.T k - 1) * gL R n b j * gLinv R n j m := by
  unfold twistMat
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal]
  have h : ∀ a, gL R n b a * (if a = j then (LaurentPolynomial.T k : GLLaurent R n) else 1) * gLinv R n a m =
      gL R n b a * gLinv R n a m + (if a = j then (LaurentPolynomial.T k - 1) * gL R n b j * gLinv R n j m else 0) := by
    intro a
    split_ifs with h
    · subst h; ring
    · ring
  simp only [h]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' , if_pos (Finset.mem_univ j), ← Matrix.mul_apply, flt_gL_mul_gLinv,
    Matrix.one_apply]

variable {N n : ℕ} (LL : Letters (Fin N)) (S : Set (Fin N)) (jj : Fin n)

abbrev TwistedRing (N n : ℕ) := MvPolynomial (Fin N × Fin n) (GLLaurent ℤ n)

def twistColumnVector (N : ℕ) {n : ℕ} (jj : Fin n) (b : Fin n) : TwistedRing N n := C (gL ℤ n b jj)

def twistRowVector (N : ℕ) {n : ℕ} (jj : Fin n) (m : Fin n) : TwistedRing N n := C (gLinv ℤ n jj m)

def laurentPower (N n : ℕ) (k : ℤ) : TwistedRing N n := C (LaurentPolynomial.T k)

theorem sum_U_mul_V_eq_one : ∑ m, twistColumnVector N jj m * twistRowVector N jj m = 1 := by
  have := congrFun (congrFun (flt_gLinv_mul_gL ℤ n) jj) jj
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at this
  unfold twistColumnVector twistRowVector
  simp only [← map_mul]
  rw [← map_sum, ← map_one (C : GLLaurent ℤ n →+* TwistedRing N n), ← this]
  congr 1
  exact Finset.sum_congr rfl fun m _ => mul_comm _ _

theorem sum_V_mul_U_eq_one : ∑ m, twistRowVector N jj m * twistColumnVector N jj m = 1 := by
  rw [← sum_U_mul_V_eq_one (N := N) jj]; exact Finset.sum_congr rfl fun m _ => mul_comm _ _

theorem laurent_power_mul_neg (k : ℤ) : laurentPower N n k * laurentPower N n (-k) = 1 := by
  unfold laurentPower
  rw [← map_mul, ← LaurentPolynomial.T_add]; simp

theorem twist_substitution_X_vector {l : Fin N} (hl : l ∈ S) (hv : LL.vec l = true) (m : Fin n) :
    twistSub (R := ℤ) LL S jj (X (l, m)) =
      X (l, m) + (laurentPower N n 1 - 1) * twistRowVector N jj m * ∑ b, twistColumnVector N jj b * X (l, b) := by
  rw [twist_substitution_eq_action, twisted_action_X, if_pos hl, if_pos hv]
  simp only [twist_matrix_apply, map_add, map_mul, map_sub, map_one, add_mul, Finset.sum_add_distrib]
  congr 1
  · simp [apply_ite C, Finset.sum_ite_eq']
  · unfold laurentPower twistRowVector twistColumnVector
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring

theorem twist_substitution_X_covector {l : Fin N} (hl : l ∈ S) (hv : ¬ LL.vec l = true) (m : Fin n) :
    twistSub (R := ℤ) LL S jj (X (l, m)) =
      X (l, m) + (laurentPower N n (-1) - 1) * twistColumnVector N jj m * ∑ b, twistRowVector N jj b * X (l, b) := by
  rw [twist_substitution_eq_action, twisted_action_X, if_pos hl, if_neg hv]
  simp only [twist_matrix_apply, map_add, map_mul, map_sub, map_one, add_mul, Finset.sum_add_distrib]
  congr 1
  · simp [apply_ite C, Finset.sum_ite_eq]
  · unfold laurentPower twistRowVector twistColumnVector
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring

theorem twist_vector_letters_fun {l : Fin N} (hl : l ∈ S) (hv : LL.vec l = true) :
    (fun m => twistSub (R := ℤ) LL S jj (letVec (n := n) ℤ l m)) =
      fun m => letVec (GLLaurent ℤ n) l m + (laurentPower N n 1 - 1) * twistRowVector N jj m *
        ∑ b, twistColumnVector N jj b * letVec (GLLaurent ℤ n) l b := by
  funext m
  simp only [letVec]
  exact twist_substitution_X_vector LL S jj hl hv m

theorem twist_covector_letters_fun {l : Fin N} (hl : l ∈ S) (hv : ¬ LL.vec l = true) :
    (fun m => twistSub (R := ℤ) LL S jj (letVec (n := n) ℤ l m)) =
      fun m => letVec (GLLaurent ℤ n) l m + (laurentPower N n (-1) - 1) * twistColumnVector N jj m *
        ∑ b, twistRowVector N jj b * letVec (GLLaurent ℤ n) l b := by
  funext m
  simp only [letVec]
  exact twist_substitution_X_covector LL S jj hl hv m

theorem twist_substitution_outside {l : Fin N} (hl : l ∉ S) (m : Fin n) : twistSub (R := ℤ) LL S jj (X (l, m)) = X (l, m) := by
  rw [twist_substitution_eq_action, twisted_action_X, if_neg hl]

def columnLambdaOperator (N : ℕ) {n : ℕ} (jj : Fin n) (c : ℤ) : Module.End (TwistedRing N n) (Finset (Fin n) → TwistedRing N n) :=
  if 1 ≤ c then lambdaOperator (twistColumnVector N jj) (twistRowVector N jj) (laurentPower N n 1) else lambdaOperator (twistRowVector N jj) (twistColumnVector N jj) (laurentPower N n (-1))

theorem total_contraction_exterior_one {P : Type*} [CommRing P] (u : Fin n → P) : totalContraction u (extOne : Finset (Fin n) → P) = 0 := by
  unfold totalContraction
  rw [LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun m _ => ?_
  funext J
  simp [exterior_contraction_apply, extOne]

theorem twist_column_kernel_eq_lambda {B : Fin N → ℕ} (Pa : PPath n N LL B) (c : ℤ) (j : ℕ) (hj : ∀ l : Fin N, l.val < j → l ∈ S)
    (J : Finset (Fin n)) :
    twistSub (R := ℤ) LL S jj (Kcol ℤ Pa.mu c j J) = columnLambdaOperator N jj c (Kcol (GLLaurent ℤ n) Pa.mu c j) J := by
  induction j generalizing J with
  | zero =>
    have h0 : columnLambdaOperator N jj c (extOne : Finset (Fin n) → TwistedRing N n) = extOne := by
      unfold columnLambdaOperator lambdaOperator
      split_ifs <;> simp [Module.End.mul_apply, total_contraction_exterior_one]
    simp only [Kcol]
    rw [h0, map_exterior_one]
  | succ j ih =>
    have ih' := ih (fun l hl => hj l (by omega))
    simp only [Kcol]
    split_ifs with h
    · have hst := Pa.step ⟨j, h⟩
      have hS : (⟨j, h⟩ : Fin N) ∈ S := hj ⟨j, h⟩ (by simp)
      rw [map_column_operator]
      have hK : (fun J => twistSub (R := ℤ) LL S jj (Kcol ℤ Pa.mu c j J)) =
          columnLambdaOperator N jj c (Kcol (GLLaurent ℤ n) Pa.mu c j) := funext ih'
      rw [hK]
      by_cases hv : LL.vec ⟨j, h⟩ = true
      · rw [if_pos hv] at hst
        have hle : colH (Pa.mu ⟨j, by omega⟩) c ≤ colH (Pa.mu ⟨j + 1, by omega⟩) c := column_height_mono hst.1 c
        rw [twist_vector_letters_fun LL S jj hS hv]
        unfold colStep
        by_cases hlt : colH (Pa.mu ⟨j, by omega⟩) c < colH (Pa.mu ⟨j + 1, by omega⟩) c
        · rw [if_pos hlt, if_pos hlt]
          by_cases hc : 1 ≤ c
          · have hL : columnLambdaOperator N jj c = lambdaOperator (twistColumnVector N jj) (twistRowVector N jj) (laurentPower N n 1) := if_pos hc
            rw [if_pos hc, if_pos hc, hL, wedge_lambda_intertwine]
          · have hL : columnLambdaOperator N jj c = lambdaOperator (twistRowVector N jj) (twistColumnVector N jj) (laurentPower N n (-1)) := if_neg hc
            rw [if_neg hc, if_neg hc, hL, contraction_lambda_intertwine (twistRowVector N jj) (twistColumnVector N jj) (laurentPower N n (-1)) (laurentPower N n 1)
              (by rw [mul_comm]; exact laurent_power_mul_neg 1) (sum_V_mul_U_eq_one jj)]
        · rw [if_neg hlt, if_neg hlt, if_neg (by omega), if_neg (by omega)]
      · rw [if_neg hv] at hst
        have hle : colH (Pa.mu ⟨j + 1, by omega⟩) c ≤ colH (Pa.mu ⟨j, by omega⟩) c := column_height_mono hst.1 c
        rw [twist_covector_letters_fun LL S jj hS hv]
        unfold colStep
        have hnl : ¬ colH (Pa.mu ⟨j, by omega⟩) c < colH (Pa.mu ⟨j + 1, by omega⟩) c := by omega
        simp only [if_neg hnl]
        by_cases hlt : colH (Pa.mu ⟨j + 1, by omega⟩) c < colH (Pa.mu ⟨j, by omega⟩) c
        · simp only [if_pos hlt]
          by_cases hc : 1 ≤ c
          · have hL : columnLambdaOperator N jj c = lambdaOperator (twistColumnVector N jj) (twistRowVector N jj) (laurentPower N n 1) := if_pos hc
            rw [if_pos hc, if_pos hc, hL, contraction_lambda_intertwine (twistColumnVector N jj) (twistRowVector N jj) (laurentPower N n 1) (laurentPower N n (-1))
              (laurent_power_mul_neg 1) (sum_U_mul_V_eq_one jj)]
          · have hL : columnLambdaOperator N jj c = lambdaOperator (twistRowVector N jj) (twistColumnVector N jj) (laurentPower N n (-1)) := if_neg hc
            rw [if_neg hc, if_neg hc, hL, wedge_lambda_intertwine]
        · simp only [if_neg hlt]
    · exact ih' J

end twist

section supp

variable {n : ℕ}

def SupportDegree {P : Type*} [Zero P] (d : ℕ) (K : Finset (Fin n) → P) : Prop := ∀ J, J.card ≠ d → K J = 0

theorem support_degree_wedge {P : Type*} [CommRing P] (x : Fin n → P) {K : Finset (Fin n) → P} {d : ℕ}
    (h : SupportDegree d K) : SupportDegree (d + 1) (wedgeR x K) := by
  intro J hJ
  unfold wedgeR
  refine Finset.sum_eq_zero fun m hm => ?_
  rw [h (J.erase m) (by rw [Finset.card_erase_of_mem hm]; have := Finset.card_pos.2 ⟨m, hm⟩; omega), mul_zero]

theorem support_degree_contraction {P : Type*} [CommRing P] (x : Fin n → P) {K : Finset (Fin n) → P} {d : ℕ}
    (h : SupportDegree (d + 1) K) : SupportDegree d (contrR x K) := by
  intro J hJ
  unfold contrR
  refine Finset.sum_eq_zero fun m hm => ?_
  have hm' : m ∉ J := (Finset.mem_sdiff.1 hm).2
  rw [h (insert m J) (by rw [Finset.card_insert_of_notMem hm']; omega), mul_zero]

theorem column_height_horizontal_strip {nu mu : Fin n → ℤ} (hnu : Dominant nu) (hmu : Dominant mu) {b : ℕ} (hs : HStrip nu mu b)
    (c : ℤ) : colH mu c ≤ colH nu c + 1 := by
  by_contra hcon
  have hle := colH_le mu c
  have h1 : colH nu c + 1 < n := by omega
  have h2 : c ≤ mu ⟨colH nu c + 1, h1⟩ := (column_height_lt_iff hmu c ⟨colH nu c + 1, h1⟩).1 (by simp only; omega)
  have h3 := hs.2.1 ⟨colH nu c, by omega⟩ h1
  have h4 := (column_height_lt_iff hnu c ⟨colH nu c, by omega⟩).2 (h2.trans h3)
  simp only at h4
  omega

def columnDegree (mu : Fin n → ℤ) (c : ℤ) : ℕ := if 1 ≤ c then colH mu c else n - colH mu c

theorem column_kernel_support_degree (R : Type*) [CommRing R] {N : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ} (Pa : PPath n N LL B)
    (c : ℤ) (j : ℕ) (hj : j < N + 1) : SupportDegree (columnDegree (Pa.mu ⟨j, hj⟩) c) (Kcol R Pa.mu c j) := by
  induction j with
  | zero =>
    have h0 : Pa.mu ⟨0, hj⟩ = 0 := Pa.zero
    have hd : columnDegree (Pa.mu ⟨0, hj⟩) c = 0 := by
      rw [h0]; unfold columnDegree colH
      by_cases hc : 1 ≤ c
      · rw [if_pos hc, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro m _; simp only [Pi.zero_apply]; omega
      · rw [if_neg hc, Finset.filter_true_of_mem (fun m _ => by simp only [Pi.zero_apply]; omega)]
        simp
    rw [hd]
    intro J hJ
    simp only [Kcol, extOne]
    rw [if_neg (fun h => hJ (by rw [h]; rfl))]
  | succ j ih =>
    have h : j < N := by omega
    have ih' := ih (by omega)
    have hst := Pa.step ⟨j, h⟩
    have hnP := colH_le (Pa.mu ⟨j, by omega⟩) c
    have hnN := colH_le (Pa.mu ⟨j + 1, hj⟩) c
    simp only [Kcol, dif_pos h]
    unfold colStep
    unfold columnDegree at ih' ⊢
    by_cases hv : LL.vec ⟨j, h⟩ = true
    · rw [if_pos hv] at hst
      have hle : colH (Pa.mu ⟨j, by omega⟩) c ≤ colH (Pa.mu ⟨j + 1, hj⟩) c := column_height_mono hst.1 c
      have hle2 : colH (Pa.mu ⟨j + 1, hj⟩) c ≤ colH (Pa.mu ⟨j, by omega⟩) c + 1 :=
        column_height_horizontal_strip (Pa.dom _) (Pa.dom _) hst c
      by_cases hlt : colH (Pa.mu ⟨j, by omega⟩) c < colH (Pa.mu ⟨j + 1, hj⟩) c
      · have e : colH (Pa.mu ⟨j + 1, hj⟩) c = colH (Pa.mu ⟨j, by omega⟩) c + 1 := by omega
        rw [if_pos hlt]
        by_cases hc : 1 ≤ c
        · rw [if_pos hc] at ih' ⊢
          rw [if_pos hc, e]
          exact support_degree_wedge _ ih'
        · rw [if_neg hc] at ih' ⊢
          rw [if_neg hc]
          refine support_degree_contraction _ ?_
          have e2 : n - colH (Pa.mu ⟨j + 1, hj⟩) c + 1 = n - colH (Pa.mu ⟨j, by omega⟩) c := by omega
          rw [e2]; exact ih'
      · have e : colH (Pa.mu ⟨j + 1, hj⟩) c = colH (Pa.mu ⟨j, by omega⟩) c := by omega
        have hnl' : ¬ colH (Pa.mu ⟨j + 1, hj⟩) c < colH (Pa.mu ⟨j, by omega⟩) c := by omega
        rw [if_neg hlt, if_neg hnl', e]
        exact ih'
    · rw [if_neg hv] at hst
      have hle : colH (Pa.mu ⟨j + 1, hj⟩) c ≤ colH (Pa.mu ⟨j, by omega⟩) c := column_height_mono hst.1 c
      have hle2 : colH (Pa.mu ⟨j, by omega⟩) c ≤ colH (Pa.mu ⟨j + 1, hj⟩) c + 1 :=
        column_height_horizontal_strip (Pa.dom _) (Pa.dom _) hst c
      have hnl : ¬ colH (Pa.mu ⟨j, by omega⟩) c < colH (Pa.mu ⟨j + 1, hj⟩) c := by omega
      rw [if_neg hnl]
      by_cases hlt : colH (Pa.mu ⟨j + 1, hj⟩) c < colH (Pa.mu ⟨j, by omega⟩) c
      · have e : colH (Pa.mu ⟨j, by omega⟩) c = colH (Pa.mu ⟨j + 1, hj⟩) c + 1 := by omega
        rw [if_pos hlt]
        by_cases hc : 1 ≤ c
        · rw [if_pos hc] at ih' ⊢
          rw [if_pos hc]
          rw [e] at ih'
          exact support_degree_contraction _ ih'
        · rw [if_neg hc] at ih' ⊢
          rw [if_neg hc]
          have e2 : n - colH (Pa.mu ⟨j + 1, hj⟩) c = n - colH (Pa.mu ⟨j, by omega⟩) c + 1 := by omega
          rw [e2]
          exact support_degree_wedge _ ih'
      · have e : colH (Pa.mu ⟨j + 1, hj⟩) c = colH (Pa.mu ⟨j, by omega⟩) c := by omega
        rw [if_neg hlt, e]
        exact ih'

theorem total_contraction_zero_of_empty_support {P : Type*} [CommRing P] (u : Fin n → P) {K : Finset (Fin n) → P} (h : SupportDegree 0 K) :
    totalContraction u K = 0 := by
  unfold totalContraction
  rw [LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun m _ => ?_
  funext J
  rw [LinearMap.smul_apply, Pi.smul_apply, exterior_contraction_apply]
  split_ifs with hm
  · simp
  · rw [h (insert m J) (by rw [Finset.card_insert_of_notMem hm]; omega)]; simp

theorem total_wedge_zero_of_top_support {P : Type*} [CommRing P] (v : Fin n → P) {K : Finset (Fin n) → P} (h : SupportDegree n K) :
    totalWedge v K = 0 := by
  unfold totalWedge
  rw [LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun m _ => ?_
  funext J
  rw [LinearMap.smul_apply, Pi.smul_apply, exterior_wedge_apply]
  split_ifs with hm
  · have hc : J.card ≤ n := by simpa using Finset.card_le_univ J
    rw [h (J.erase m) (by rw [Finset.card_erase_of_mem hm]; have := Finset.card_pos.2 ⟨m, hm⟩; omega)]; simp
  · simp

theorem lambda_eq_self_of_contraction_zero {P : Type*} [CommRing P] (u v : Fin n → P) (θ : P) {K : Finset (Fin n) → P}
    (h : totalContraction u K = 0) : lambdaOperator u v θ K = K := by
  simp [lambdaOperator, Module.End.mul_apply, h]

theorem lambda_eq_smul_of_total_wedge_zero {P : Type*} [CommRing P] (u v : Fin n → P) (θ : P) (hd : ∑ m, u m * v m = 1)
    {K : Finset (Fin n) → P} (h : totalWedge v K = 0) : lambdaOperator u v θ K = θ • K := by
  have e : totalWedge v * totalContraction u = 1 - totalContraction u * totalWedge v := by rw [totalContraction_mul_totalWedge, hd, one_smul]; abel
  unfold lambdaOperator
  rw [e]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply,
    Module.End.mul_apply, h, map_zero, sub_zero]
  rw [sub_smul, one_smul]; abel

end supp

section filt

open Formalism.MainNotions.G.GLWeightTheory

variable {n : ℕ} {Q : Type*} [CommRing Q] (Fl : flt_Fil Q)

def ComponentsInFiltration (s : ℤ) (K : Finset (Fin n) → Q) : Prop := ∀ J, K J ∈ Fl.F s

theorem exterior_sign_mem_filtration {s : ℤ} {y : Q} (hy : y ∈ Fl.F s) (J : Finset (Fin n)) (m : Fin n) : exteriorSign Q J m * y ∈ Fl.F s := by
  unfold exteriorSign
  rcases neg_one_pow_eq_or Q (J.filter fun j => m < j).card with h | h <;> rw [h]
  · rwa [one_mul]
  · rw [neg_one_mul]; exact (Fl.F s).neg_mem hy

theorem components_in_filtration_wedge {s : ℤ} {K : Finset (Fin n) → Q} (h : ComponentsInFiltration Fl s K) (m : Fin n) : ComponentsInFiltration Fl s (exteriorWedge Q m K) := by
  intro J
  rw [exterior_wedge_apply]
  split_ifs
  · exact exterior_sign_mem_filtration Fl (h _) J m
  · exact (Fl.F s).zero_mem

theorem components_in_filtration_contraction_single {s : ℤ} {K : Finset (Fin n) → Q} (h : ComponentsInFiltration Fl s K) (m : Fin n) : ComponentsInFiltration Fl s (exteriorContraction Q m K) := by
  intro J
  rw [exterior_contraction_apply]
  split_ifs
  · exact (Fl.F s).zero_mem
  · exact exterior_sign_mem_filtration Fl (h _) J m

theorem componentsInFiltration_totalWedge {s : ℤ} {K : Finset (Fin n) → Q} (v : Fin n → Q) (hv : ∀ m, v m ∈ Fl.F 0) (h : ComponentsInFiltration Fl s K) :
    ComponentsInFiltration Fl s (totalWedge v K) := by
  intro J
  unfold totalWedge
  rw [LinearMap.sum_apply, Finset.sum_apply]
  refine (Fl.F s).sum_mem fun m _ => ?_
  have := Fl.mul_mem (hv m) (components_in_filtration_wedge Fl h m J)
  rw [zero_add] at this
  exact this

theorem components_in_filtration_contraction {s : ℤ} {K : Finset (Fin n) → Q} (u : Fin n → Q) (hu : ∀ m, u m ∈ Fl.F 0) (h : ComponentsInFiltration Fl s K) :
    ComponentsInFiltration Fl s (totalContraction u K) := by
  intro J
  unfold totalContraction
  rw [LinearMap.sum_apply, Finset.sum_apply]
  refine (Fl.F s).sum_mem fun m _ => ?_
  have := Fl.mul_mem (hu m) (components_in_filtration_contraction_single Fl h m J)
  rw [zero_add] at this
  exact this

theorem right_wedge_eq_total (x : Fin n → Q) (K : Finset (Fin n) → Q) : wedgeR x K = totalWedge x K := by
  rw [right_wedge_eq_sum]; simp [totalWedge, LinearMap.sum_apply]

theorem right_contraction_eq_total (x : Fin n → Q) (K : Finset (Fin n) → Q) : contrR x K = totalContraction x K := by
  rw [right_contraction_eq_sum]; simp [totalContraction, LinearMap.sum_apply]

theorem components_in_filtration_column {s : ℤ} {K : Finset (Fin n) → Q} (x : Fin n → Q) (hx : ∀ m, x m ∈ Fl.F 0)
    (h : ComponentsInFiltration Fl s K) (c : ℤ) (hP hN : ℕ) : ComponentsInFiltration Fl s (colStep c hP hN x K) := by
  unfold colStep
  split_ifs
  · rw [right_wedge_eq_total]; exact componentsInFiltration_totalWedge Fl x hx h
  · rw [right_contraction_eq_total]; exact components_in_filtration_contraction Fl x hx h
  · rw [right_contraction_eq_total]; exact components_in_filtration_contraction Fl x hx h
  · rw [right_wedge_eq_total]; exact componentsInFiltration_totalWedge Fl x hx h
  · exact h

theorem components_in_filtration_lambda {K : Finset (Fin n) → Q} (u v : Fin n → Q) (hu : ∀ m, u m ∈ Fl.F 0) (hv : ∀ m, v m ∈ Fl.F 0)
    {θ : Q} {a a' : ℤ} (hθ : θ ∈ Fl.F a) (ha : a' ≤ a) (h0 : a' ≤ 0) (h : ComponentsInFiltration Fl 0 K) :
    ComponentsInFiltration Fl a' (lambdaOperator u v θ K) := by
  intro J
  have e : lambdaOperator u v θ K J = K J + (θ - 1) * totalWedge v (totalContraction u K) J := by
    simp [lambdaOperator, Module.End.mul_apply]
  rw [e]
  refine (Fl.F a').add_mem (Fl.anti h0 (h J)) ?_
  have h1 : θ - 1 ∈ Fl.F a' := (Fl.F a').sub_mem (Fl.anti ha hθ) (Fl.anti h0 Fl.one_mem)
  have := Fl.mul_mem h1 (componentsInFiltration_totalWedge Fl v hv (components_in_filtration_contraction Fl u hu h) J)
  rw [add_zero] at this
  exact this

theorem components_in_filtration_smul {K : Finset (Fin n) → Q} {θ : Q} {a : ℤ} (hθ : θ ∈ Fl.F a) (h : ComponentsInFiltration Fl 0 K) :
    ComponentsInFiltration Fl a (θ • K) := by
  intro J
  have := Fl.mul_mem hθ (h J)
  rw [add_zero] at this
  exact this

end filt

section final

open Formalism.MainNotions.G.GLWeightTheory

variable {N n : ℕ} (LL : Letters (Fin N))

abbrev laurentDegreeFiltration (N n : ℕ) (e : ℤ) : flt_Fil (TwistedRing N n) := laurentCoeffFiltration ℤ n (Fin N × Fin n) e

theorem twist_column_mem_filtration (e : ℤ) (jj b : Fin n) : twistColumnVector N jj b ∈ (laurentDegreeFiltration N n e).F 0 :=
  flt_C_mem (flt_L_C e _)

theorem twist_row_mem_filtration (e : ℤ) (jj b : Fin n) : twistRowVector N jj b ∈ (laurentDegreeFiltration N n e).F 0 :=
  flt_C_mem (flt_L_C e _)

theorem laurent_power_mem_filtration (e k : ℤ) : laurentPower N n k ∈ (laurentDegreeFiltration N n e).F (e * k) :=
  flt_C_mem (T_mem_laurentFiltration e k)

theorem X_mem_laurentDegreeFiltration_zero (e : ℤ) (v : Fin N × Fin n) : (X v : TwistedRing N n) ∈ (laurentDegreeFiltration N n e).F 0 := by
  refine flt_monomial_mem ?_
  simpa using (flt_L (GLCoord ℤ n) e).one_mem

theorem column_kernel_in_filtration_zero (e : ℤ) (mu : Fin (N + 1) → Fin n → ℤ) (c : ℤ) (j : ℕ) :
    ComponentsInFiltration (laurentDegreeFiltration N n e) 0 (Kcol (GLLaurent ℤ n) mu c j) := by
  induction j with
  | zero =>
    intro J
    simp only [Kcol, extOne]
    split_ifs
    · exact (laurentDegreeFiltration N n e).one_mem
    · exact ((laurentDegreeFiltration N n e).F 0).zero_mem
  | succ j ih =>
    simp only [Kcol]
    split_ifs with h
    · exact components_in_filtration_column _ _ (fun m => X_mem_laurentDegreeFiltration_zero e _) ih _ _ _
    · exact ih

def columnBoundEntry (x c : ℤ) : ℤ := if 1 ≤ c then (if c ≤ x then 1 else 0) else (if ¬ c ≤ x then -1 else 0)

theorem twisted_column_lower_filtration [NeZero n] {B : Fin N → ℕ} (Pa : PPath n N LL B) (S : Set (Fin N)) (c : ℤ) (j0 : ℕ)
    (hj0 : j0 < N + 1) (hS : ∀ l : Fin N, l.val < j0 → l ∈ S) :
    ComponentsInFiltration (laurentDegreeFiltration N n 1) (columnBoundEntry (Pa.mu ⟨j0, hj0⟩ (lastIdx n)) c)
      (fun J => twistSub (R := ℤ) LL S (lastIdx n) (Kcol ℤ Pa.mu c j0 J)) := by
  rw [funext (twist_column_kernel_eq_lambda LL S (lastIdx n) Pa c j0 hS)]
  have hK0 := column_kernel_in_filtration_zero (N := N) 1 Pa.mu c j0
  have hSu := column_kernel_support_degree (GLLaurent ℤ n) Pa c j0 hj0
  have hiff := column_height_lt_iff (Pa.dom ⟨j0, hj0⟩) c (lastIdx n)
  have hle := colH_le (Pa.mu ⟨j0, hj0⟩) c
  have hpos := NeZero.pos n
  have hlast : (lastIdx n).val = n - 1 := rfl
  unfold columnLambdaOperator columnBoundEntry
  unfold columnDegree at hSu
  by_cases hc : 1 ≤ c
  · rw [if_pos hc, if_pos hc]
    rw [if_pos hc] at hSu
    by_cases hx : c ≤ Pa.mu ⟨j0, hj0⟩ (lastIdx n)
    · rw [if_pos hx]
      have hn : colH (Pa.mu ⟨j0, hj0⟩) c = n := by have := hiff.2 hx; omega
      rw [hn] at hSu
      rw [lambda_eq_smul_of_total_wedge_zero _ _ _ (sum_U_mul_V_eq_one _) (total_wedge_zero_of_top_support _ hSu)]
      exact components_in_filtration_smul _ (by simpa using laurent_power_mem_filtration (N := N) (n := n) 1 1) hK0
    · rw [if_neg hx]
      exact components_in_filtration_lambda _ _ _ (twist_column_mem_filtration 1 _) (twist_row_mem_filtration 1 _) (laurent_power_mem_filtration (N := N) (n := n) 1 1) (by norm_num) le_rfl hK0
  · rw [if_neg hc, if_neg hc]
    rw [if_neg hc] at hSu
    by_cases hx : c ≤ Pa.mu ⟨j0, hj0⟩ (lastIdx n)
    · rw [if_neg (not_not.2 hx)]
      have hn : n - colH (Pa.mu ⟨j0, hj0⟩) c = 0 := by have := hiff.2 hx; omega
      rw [hn] at hSu
      rw [lambda_eq_self_of_contraction_zero _ _ _ (total_contraction_zero_of_empty_support _ hSu)]
      exact hK0
    · rw [if_pos hx]
      exact components_in_filtration_lambda _ _ _ (twist_row_mem_filtration 1 _) (twist_column_mem_filtration 1 _) (laurent_power_mem_filtration (N := N) (n := n) 1 (-1)) (by norm_num)
        (by norm_num) hK0

theorem twisted_column_upper_filtration [NeZero n] {B : Fin N → ℕ} (Pa : PPath n N LL B) (S : Set (Fin N)) (c : ℤ) (j0 : ℕ)
    (hj0 : j0 < N + 1) (hS : ∀ l : Fin N, l.val < j0 → l ∈ S) :
    ComponentsInFiltration (laurentDegreeFiltration N n (-1)) (-columnBoundEntry (Pa.mu ⟨j0, hj0⟩ 0) c)
      (fun J => twistSub (R := ℤ) LL S (0 : Fin n) (Kcol ℤ Pa.mu c j0 J)) := by
  rw [funext (twist_column_kernel_eq_lambda LL S (0 : Fin n) Pa c j0 hS)]
  have hK0 := column_kernel_in_filtration_zero (N := N) (-1) Pa.mu c j0
  have hSu := column_kernel_support_degree (GLLaurent ℤ n) Pa c j0 hj0
  have hiff := column_height_lt_iff (Pa.dom ⟨j0, hj0⟩) c (0 : Fin n)
  have hz : ((0 : Fin n) : ℕ) = 0 := Fin.val_zero n
  rw [hz] at hiff
  unfold columnLambdaOperator columnBoundEntry
  unfold columnDegree at hSu
  by_cases hc : 1 ≤ c
  · rw [if_pos hc, if_pos hc]
    rw [if_pos hc] at hSu
    by_cases hx : c ≤ Pa.mu ⟨j0, hj0⟩ 0
    · rw [if_pos hx]
      exact components_in_filtration_lambda _ _ _ (twist_column_mem_filtration (-1) _) (twist_row_mem_filtration (-1) _) (laurent_power_mem_filtration (N := N) (n := n) (-1) 1) (by norm_num)
        (by norm_num) hK0
    · rw [if_neg hx, neg_zero]
      have hn : colH (Pa.mu ⟨j0, hj0⟩) c = 0 := by
        by_contra h; exact hx (hiff.1 (Nat.pos_of_ne_zero h))
      rw [hn] at hSu
      rw [lambda_eq_self_of_contraction_zero _ _ _ (total_contraction_zero_of_empty_support _ hSu)]
      exact hK0
  · rw [if_neg hc, if_neg hc]
    rw [if_neg hc] at hSu
    by_cases hx : c ≤ Pa.mu ⟨j0, hj0⟩ 0
    · rw [if_neg (not_not.2 hx), neg_zero]
      exact components_in_filtration_lambda _ _ _ (twist_row_mem_filtration (-1) _) (twist_column_mem_filtration (-1) _) (laurent_power_mem_filtration (N := N) (n := n) (-1) (-1)) (by norm_num)
        le_rfl hK0
    · rw [if_pos hx]
      have hn : n - colH (Pa.mu ⟨j0, hj0⟩) c = n := by
        have : colH (Pa.mu ⟨j0, hj0⟩) c = 0 := by
          by_contra h; exact hx (hiff.1 (Nat.pos_of_ne_zero h))
        omega
      rw [hn] at hSu
      rw [lambda_eq_smul_of_total_wedge_zero _ _ _ (sum_V_mul_U_eq_one _) (total_wedge_zero_of_top_support _ hSu)]
      exact components_in_filtration_smul _ (by simpa using laurent_power_mem_filtration (N := N) (n := n) (-1) (-1)) hK0

theorem filtration_bound_later_columns (e : ℤ) (S : Set (Fin N)) (jj : Fin n) (mu : Fin (N + 1) → Fin n → ℤ) (c s : ℤ) (j0 : ℕ)
    (hout : ∀ l : Fin N, j0 ≤ l.val → l ∉ S)
    (h0 : ComponentsInFiltration (laurentDegreeFiltration N n e) s (fun J => twistSub (R := ℤ) LL S jj (Kcol ℤ mu c j0 J))) (j : ℕ) (hj : j0 ≤ j) :
    ComponentsInFiltration (laurentDegreeFiltration N n e) s (fun J => twistSub (R := ℤ) LL S jj (Kcol ℤ mu c j J)) := by
  induction j, hj using Nat.le_induction with
  | base => exact h0
  | succ j hj ih =>
    simp only [Kcol]
    split_ifs with h
    · intro J
      simp only
      rw [map_column_operator]
      refine components_in_filtration_column _ _ (fun m => ?_) ih _ _ _ J
      simp only [letVec]
      rw [twist_substitution_outside LL S jj (hout ⟨j, h⟩ hj)]
      exact X_mem_laurentDegreeFiltration_zero e _
    · exact ih

theorem prod_mem_filtration_sum {Q : Type*} [CommRing Q] (Fl : flt_Fil Q) (s : Finset ℤ) (f : ℤ → Q) (τ : ℤ → ℤ)
    (h : ∀ c ∈ s, f c ∈ Fl.F (τ c)) : ∏ c ∈ s, f c ∈ Fl.F (∑ c ∈ s, τ c) := by
  induction s using Finset.induction_on with
  | empty => simpa using Fl.one_mem
  | insert c s hc ih =>
    rw [Finset.prod_insert hc, Finset.sum_insert hc]
    exact Fl.mul_mem (h c (Finset.mem_insert_self c s)) (ih fun c' hc' => h c' (Finset.mem_insert_of_mem hc'))

theorem tau_sum_over_columns (mu : Fin (N + 1) → Fin n → ℤ) (q : Fin (N + 1)) (a : Fin n) :
    ∑ c ∈ colRange mu, columnBoundEntry (mu q a) c = mu q a := by
  have hT := abs_entry_le_total mu q a
  rw [abs_le] at hT
  exact signed_column_count_eq _ (mu q a) hT.1 hT.2

theorem word_valuation_bounds : WordValuationBounds := by
  intro N n _ LL B P I i
  have hj0 : i.val + 1 < N + 1 := by have := i.2; omega
  have hq : (⟨i.val + 1, hj0⟩ : Fin (N + 1)) = i.succ := rfl
  have hS : ∀ l : Fin N, l.val < i.val + 1 → l ∈ {j : Fin N | j ≤ i} := fun l hl => by
    show l ≤ i
    rw [Fin.le_def]; omega
  have hout : ∀ l : Fin N, i.val + 1 ≤ l.val → l ∉ {j : Fin N | j ≤ i} := fun l hl h => by
    have h' : l ≤ i := h
    rw [Fin.le_def] at h'; omega
  have hN : i.val + 1 ≤ N := by have := i.2; omega
  constructor
  · rw [flt_le_valS]
    unfold Psi
    rw [map_prod, ← tau_sum_over_columns P.mu i.succ (lastIdx n)]
    refine prod_mem_filtration_sum _ _ _ _ fun c _ => ?_
    have h0 := twisted_column_lower_filtration LL P {j : Fin N | j ≤ i} c (i.val + 1) hj0 hS
    rw [hq] at h0
    exact filtration_bound_later_columns LL 1 _ _ P.mu c _ (i.val + 1) hout h0 N hN (I c)
  · rw [flt_lam1S_le]
    unfold Psi
    rw [map_prod, ← tau_sum_over_columns P.mu i.succ 0, ← Finset.sum_neg_distrib]
    refine prod_mem_filtration_sum _ _ _ _ fun c _ => ?_
    have h0 := twisted_column_upper_filtration LL P {j : Fin N | j ≤ i} c (i.val + 1) hj0 hS
    rw [hq] at h0
    exact filtration_bound_later_columns LL (-1) _ _ P.mu c _ (i.val + 1) hout h0 N hN (I c)

end final

theorem prvA3_of_valuationField_of_admB (D : Formalism.BasicNotions.D7) (hV : ValuationLemmaField D) (hB : AdmB D) : DefiniteRankOne D := lemma_A3_of_word_bound D word_valuation_bounds hV hB

end Formalism.MainNotions.LemmaBAlt
