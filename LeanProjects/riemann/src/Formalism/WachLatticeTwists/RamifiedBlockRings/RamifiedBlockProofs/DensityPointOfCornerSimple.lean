import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.FinrankRangeEq
import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.IdemFactor
import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.IdempotentImageSurjective

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

theorem blockPoly_factor {A : Type*} [CommRing A] {d S : Type*} [Fintype d] [DecidableEq d] [Fintype S]
    [DecidableEq S] (U : Matrix d S A) (W : Matrix S d A) (hWU : W * U = 1) (B : Matrix S S A) :
    blockPoly (U * W) (U * B * W) = B.charpoly := by
  classical
  have hWU' : W.map (Polynomial.C : A →+* Polynomial A) * U.map Polynomial.C = 1 := by
    simpa [Matrix.map_mul] using congrArg (fun M => M.map (Polynomial.C : A →+* Polynomial A)) hWU
  have key : (Polynomial.X : Polynomial A) • (U * W).map Polynomial.C - (U * B * W).map Polynomial.C +
      (1 - U * W).map Polynomial.C =
      1 + U.map Polynomial.C * (((Polynomial.X : Polynomial A) • 1 - B.map Polynomial.C - 1) *
        W.map Polynomial.C) := by
    have h1 : (1 - U * W).map (Polynomial.C : A →+* Polynomial A) = 1 - U.map Polynomial.C * W.map Polynomial.C := by
      have := map_sub (Polynomial.C : A →+* Polynomial A).mapMatrix 1 (U * W)
      rwa [map_one, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_mul] at this
    rw [h1, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.mul_sub, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_assoc]
    abel
  unfold blockPoly
  rw [key, Matrix.det_one_add_mul_comm, Matrix.mul_assoc, hWU', Matrix.mul_one]
  unfold Matrix.charpoly
  congr 1
  ext i j
  by_cases h : i = j <;> simp [h, Matrix.charmatrix_apply, Matrix.one_apply]

theorem sep_iff_resultant {K : Type*} [Field K] (f : Polynomial K) (hf : f.Monic) :
    f.resultant f.derivative f.natDegree f.natDegree ≠ 0 ↔ f.Separable := by
  have hd : (Polynomial.derivative f).natDegree ≤ f.natDegree :=
    (Polynomial.natDegree_derivative_le f).trans (Nat.sub_le _ _)
  have h := Polynomial.resultant_add_right_deg f (Polynomial.derivative f) f.natDegree
    (Polynomial.derivative f).natDegree (f.natDegree - (Polynomial.derivative f).natDegree) le_rfl
  rw [Nat.add_sub_cancel' hd, Polynomial.coeff_natDegree, hf.leadingCoeff, one_pow, one_mul] at h
  rw [h, ← isUnit_iff_ne_zero, Polynomial.isUnit_resultant_iff_isCoprime hf]
  exact Iff.rfl

theorem pencil_disc {K : Type*} [Field K] {S : Type*} [Fintype S] [DecidableEq S] (B0 B1 : Matrix S S K)
    (h : B1.charpoly.Separable) :
    ∃ D : Polynomial K, D ≠ 0 ∧ ∀ c, D.eval c ≠ 0 → (c • B0 + B1).charpoly.Separable := by
  classical
  set M : Matrix S S (Polynomial K) :=
    (Polynomial.X : Polynomial K) • B0.map Polynomial.C + B1.map Polynomial.C with hM
  set p := M.charpoly with hp
  have hev : ∀ c : K, (p.resultant (Polynomial.derivative p) (Fintype.card S) (Fintype.card S)).eval c =
      (c • B0 + B1).charpoly.resultant (Polynomial.derivative (c • B0 + B1).charpoly)
        (Fintype.card S) (Fintype.card S) := by
    intro c
    have hm : M.map (Polynomial.evalRingHom c) = c • B0 + B1 := by
      ext i j
      simp [hM]
      try ring
    rw [← hm, Matrix.charpoly_map, Polynomial.derivative_map, Polynomial.resultant_map_map]
    rfl
  have hsep : ∀ c : K, (p.resultant (Polynomial.derivative p) (Fintype.card S) (Fintype.card S)).eval c ≠ 0 ↔
      (c • B0 + B1).charpoly.Separable := by
    intro c
    rw [hev, ← sep_iff_resultant (c • B0 + B1).charpoly (Matrix.charpoly_monic _),
      Matrix.charpoly_natDegree_eq_dim]
  refine ⟨p.resultant (Polynomial.derivative p) (Fintype.card S) (Fintype.card S), fun h0 => ?_,
    fun c hc => (hsep c).mp hc⟩
  have h1 := (hsep 0).mpr (by simpa using h)
  rw [h0, Polynomial.eval_zero] at h1
  exact h1 rfl

private theorem separable_comp_C_mul_X_of_ne_zero {K : Type*} [Field K] {p : Polynomial K} (hp : p.Separable) {a : K}
    (ha : a ≠ 0) : (p.comp (Polynomial.C a * Polynomial.X)).Separable := by
  rw [Polynomial.separable_def] at hp ⊢
  obtain ⟨u, v, e⟩ := hp
  set q := Polynomial.C a * Polynomial.X with hqdef
  have hcomp : (u * p + v * Polynomial.derivative p).comp q = 1 := by rw [e, Polynomial.one_comp]
  rw [Polynomial.add_comp, Polynomial.mul_comp, Polynomial.mul_comp] at hcomp
  have hq : Polynomial.derivative q = Polynomial.C a := by simp [hqdef]
  have hC : Polynomial.C a⁻¹ * Polynomial.C a = 1 := by
    rw [← Polynomial.C_mul, inv_mul_cancel₀ ha, Polynomial.C_1]
  refine ⟨u.comp q, v.comp q * Polynomial.C a⁻¹, ?_⟩
  rw [Polynomial.derivative_comp, hq]
  linear_combination hcomp + (v.comp q * (Polynomial.derivative p).comp q) * hC

theorem charpoly_smul_sep {K : Type*} [Field K] {S : Type*} [Fintype S] [DecidableEq S] (B : Matrix S S K)
    (c : K) (hc : c ≠ 0) (h : B.charpoly.Separable) : (c • B).charpoly.Separable := by
  classical
  have key : Matrix.charmatrix (c • B) = Polynomial.C c •
      (Matrix.charmatrix B).map (Polynomial.compRingHom (Polynomial.C c⁻¹ * Polynomial.X)) := by
    ext i j
    rcases eq_or_ne i j with rfl | hij
    · simp only [Matrix.charmatrix_apply, Matrix.diagonal_apply_eq, Matrix.smul_apply, Matrix.map_apply,
        Polynomial.coe_compRingHom_apply, Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp,
        smul_eq_mul]
      rw [mul_sub, ← mul_assoc, ← Polynomial.C_mul, ← Polynomial.C_mul, mul_inv_cancel₀ hc,
        Polynomial.C_1, one_mul]
    · simp only [Matrix.charmatrix_apply, Matrix.diagonal_apply_ne _ hij, zero_sub, Matrix.smul_apply,
        Matrix.map_apply, Polynomial.coe_compRingHom_apply, Polynomial.neg_comp, Polynomial.C_comp,
        smul_eq_mul, mul_neg]
      rw [Polynomial.C_mul]
  have hcp : (c • B).charpoly =
      Polynomial.C (c ^ Fintype.card S) * B.charpoly.comp (Polynomial.C c⁻¹ * Polynomial.X) := by
    rw [Matrix.charpoly, key, Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      Polynomial.coe_compRingHom_apply, Polynomial.C_pow, Matrix.charpoly]
  rw [hcp]
  exact Polynomial.Separable.unit_mul
    (Polynomial.isUnit_C.mpr ((isUnit_iff_ne_zero.mpr hc).pow _)) (separable_comp_C_mul_X_of_ne_zero h (inv_ne_zero hc))

theorem pencil_choose {O : Type*} [CommRing O] [Infinite O] {K : Type*} [Field K] [Algebra O K]
    (hinj : Function.Injective (algebraMap O K)) {S : Type*} [Fintype S] [DecidableEq S]
    (B0 B1 : Matrix S S K) (h : B1.charpoly.Separable) (c0 : K) (hc0 : c0 ≠ 0) :
    ∃ l : O, (B0 + (c0 * algebraMap O K l) • B1).charpoly.Separable := by
  classical
  obtain ⟨D, hD0, hD⟩ := pencil_disc B0 B1 h
  have hfin : Set.Finite {l : O | D.eval (c0 * algebraMap O K l)⁻¹ = 0} := by
    apply Set.Finite.of_finite_image (f := fun l => (c0 * algebraMap O K l)⁻¹)
    · refine (D.roots.toFinset.finite_toSet).subset ?_
      rintro _ ⟨l, hl, rfl⟩
      simp only [Finset.mem_coe, Multiset.mem_toFinset]
      exact (Polynomial.mem_roots hD0).2 hl
    · intro l1 _ l2 _ h12
      exact hinj (mul_left_cancel₀ hc0 (inv_inj.1 h12))
  obtain ⟨l, hl⟩ := (hfin.union (Set.finite_singleton (0 : O))).infinite_compl.nonempty
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff, not_or] at hl
  obtain ⟨hDl, hl0⟩ := hl
  have hν : c0 * algebraMap O K l ≠ 0 :=
    mul_ne_zero hc0 fun h0 => hl0 (hinj (by rw [h0, map_zero]))
  refine ⟨l, ?_⟩
  have heq : B0 + (c0 * algebraMap O K l) • B1 =
      (c0 * algebraMap O K l) • ((c0 * algebraMap O K l)⁻¹ • B0 + B1) := by
    rw [smul_add, smul_smul, mul_inv_cancel₀ hν, one_smul]
  rw [heq]
  exact charpoly_smul_sep _ _ hν (hD _ hDl)

section Pts
variable {O : Type} [CommRing O] [IsDomain O] {X : Type} (T : Subalgebra O (X → O)) {d : Type} [Fintype d]
  [DecidableEq d] {G : Type} [Group G] (r : G →* (X → Matrix d d O))

theorem clearDen (x : X) (A : Matrix d d (FractionRing O))
    (hA : A ∈ Submodule.span (FractionRing O)
      (Set.range fun g => (r g x).map (algebraMap O (FractionRing O)))) :
    ∃ b : O, b ≠ 0 ∧ ∃ a ∈ tSpan T r,
      (a x).map (algebraMap O (FractionRing O)) = algebraMap O (FractionRing O) b • A := by
  classical
  obtain ⟨cf, hcf⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hA
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (R := O) (M := nonZeroDivisors O)
    cf.support cf
  have hint : ∀ g, ∃ y : O, algebraMap O (FractionRing O) y = (b : O) • cf g := by
    intro g
    by_cases hg : g ∈ cf.support
    · exact RingHom.mem_rangeS.mp (hb g hg)
    · rw [Finsupp.mem_support_iff, not_not] at hg
      exact ⟨0, by simp [hg]⟩
  choose o ho using hint
  refine ⟨b, nonZeroDivisors.ne_zero b.2,
    ∑ g ∈ cf.support, fun y => algebraMap O O ((fun g (_ : X) => o g) g y) • r g y, ?_, ?_⟩
  · unfold tSpan
    exact ⟨cf.support, fun g _ => o g, fun g => T.algebraMap_mem (o g), rfl⟩
  · have ho' : ∀ g, algebraMap O (FractionRing O) (o g) =
        algebraMap O (FractionRing O) (b : O) * cf g := fun g => by rw [ho, Algebra.smul_def]
    ext i j
    rw [← hcf]
    simp only [Finsupp.sum, Finset.sum_apply, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul, Algebra.algebraMap_self_apply, map_sum, map_mul, ho', Finset.mul_sum, mul_assoc]

theorem blockDiag_of_mem (x : X) {m : ℕ} (c : d → Fin m) (P : Matrix d d (FractionRing O))
    (h : ∀ g i j, c i ≠ c j → (P * (r g x).map (algebraMap O (FractionRing O)) * P⁻¹) i j = 0)
    (a : X → Matrix d d O) (ha : a ∈ tSpan T r) :
    ∀ i j, c i ≠ c j → (P * (a x).map (algebraMap O (FractionRing O)) * P⁻¹) i j = 0 := by
  intro i j hij
  obtain ⟨s, cc, hcc, rfl⟩ := ha
  have hN : ((∑ g ∈ s, fun y => algebraMap O O (cc g y) • r g y) x).map (algebraMap O (FractionRing O)) =
      ∑ g ∈ s, algebraMap O (FractionRing O) (cc g x) • (r g x).map (algebraMap O (FractionRing O)) := by
    ext k l
    simp [Finset.sum_apply, Matrix.sum_apply, map_sum, Matrix.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Algebra.smul_def]
  rw [hN, Finset.mul_sum, Finset.sum_mul, Matrix.sum_apply]
  exact Finset.sum_eq_zero fun g _ => by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, h g i j hij, smul_zero]

end Pts

theorem point_generic (hD : StatDensity) (hC : StatCornerSimple) {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {X : Type} [Fintype X] (T : Subalgebra O (X → O)) {d : Type} [Fintype d]
    [DecidableEq d] {G : Type} [Group G] (r : G →* (X → Matrix d d O))
    (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ T, f x ≠ f y) (eB : X → Matrix d d O) (heBm : eB ∈ tSpan T r)
    (heBB : eB * eB = eB) (x : X) (m : ℕ) (c : d → Fin m) (P : Matrix d d (FractionRing O))
    (hG : BlockDiagonalIrreducibleAt (fun g => (r g x).map (algebraMap O (FractionRing O))) m c P) (S0 : Matrix d d O) (w : O)
    (hw : w ≠ 0) :
    ∃ (j : X → O) (a : X → Matrix d d O), j ∈ T ∧ (∀ y, y ≠ x → j y = 0) ∧ a ∈ tSpan T r ∧
      (blockPoly ((eB x).map (algebraMap O (FractionRing O)))
        ((eB x * S0 * eB x + w • (j x • (eB x * a x * eB x))).map
          (algebraMap O (FractionRing O)))).Separable := by
  classical
  have hφ : Function.Injective (algebraMap O (FractionRing O)) := IsFractionRing.injective O _
  have hOinf : Infinite O := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    exact Infinite.of_injective (fun k : ℕ => ϖ ^ k)
      (pow_injective_of_not_isUnit hϖ.not_isUnit hϖ.ne_zero)
  have hKinf : Infinite (FractionRing O) := Infinite.of_injective _ hφ
  have he : (eB x).map (algebraMap O (FractionRing O)) * (eB x).map (algebraMap O (FractionRing O)) =
      (eB x).map (algebraMap O (FractionRing O)) := by
    rw [← Matrix.map_mul, ← Pi.mul_apply eB eB x, heBB]
  have heblk := blockDiag_of_mem T r x c P hG.2.1 eB heBm
  obtain ⟨A, hAblk, hAsep⟩ := hC (FractionRing O) d m c P _ hG.1 he heblk
  let ρ : G →* Matrix d d (FractionRing O) :=
    ((algebraMap O (FractionRing O)).mapMatrix : Matrix d d O →+* Matrix d d (FractionRing O)).toMonoidHom.comp
      ((Pi.evalMonoidHom (fun _ : X => Matrix d d O) x).comp r)
  have hAspan : A ∈ Submodule.span (FractionRing O)
      (Set.range fun g => (r g x).map (algebraMap O (FractionRing O))) :=
    hD (FractionRing O) d G ρ m c P hG A hAblk
  obtain ⟨b, hb0, a, ha, hab⟩ := clearDen T r x A hAspan
  obtain ⟨f, hfT, hfx, hfy⟩ := sepPoint O X T hsep x
  obtain ⟨S, hS1, hS2, U, W, hUW, hWU⟩ := idem_factor _ he
  have hfac : ∀ M : Matrix d d (FractionRing O),
      blockPoly ((eB x).map (algebraMap O (FractionRing O)))
        ((eB x).map (algebraMap O (FractionRing O)) * M * (eB x).map (algebraMap O (FractionRing O))) =
      (W * M * U).charpoly := by
    intro M
    have h1 := blockPoly_factor U W hWU (W * M * U)
    rw [hUW] at h1
    rw [← h1, ← hUW]
    simp only [Matrix.mul_assoc]
  have hB1 : (W * A * U).charpoly.Separable := by rw [← hfac]; exact hAsep
  set c0 : FractionRing O := algebraMap O (FractionRing O) w * algebraMap O (FractionRing O) (f x) *
    algebraMap O (FractionRing O) b with hc0def
  have hc0 : c0 ≠ 0 :=
    mul_ne_zero (mul_ne_zero ((map_ne_zero_iff _ hφ).mpr hw) ((map_ne_zero_iff _ hφ).mpr hfx))
      ((map_ne_zero_iff _ hφ).mpr hb0)
  obtain ⟨l, hl⟩ := pencil_choose hφ (W * S0.map (algebraMap O (FractionRing O)) * U) (W * A * U) hB1 c0 hc0
  refine ⟨fun y => f y * l, a, T.mul_mem hfT (T.algebraMap_mem l), fun y hy => by simp [hfy y hy], ha, ?_⟩
  have hs : ∀ (t : O) (N : Matrix d d O),
      (t • N).map (algebraMap O (FractionRing O)) = algebraMap O (FractionRing O) t • N.map (algebraMap O (FractionRing O)) :=
    fun t N => by ext; simp
  have hadd : ∀ N N' : Matrix d d O, (N + N').map (algebraMap O (FractionRing O)) =
      N.map (algebraMap O (FractionRing O)) + N'.map (algebraMap O (FractionRing O)) :=
    fun N N' => by ext; simp
  have hM : (eB x * S0 * eB x + w • ((f x * l) • (eB x * a x * eB x))).map (algebraMap O (FractionRing O)) =
      (eB x).map (algebraMap O (FractionRing O)) *
        (S0.map (algebraMap O (FractionRing O)) + (c0 * algebraMap O (FractionRing O) l) • A) *
        (eB x).map (algebraMap O (FractionRing O)) := by
    rw [hadd, hs, hs, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, hab]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, map_mul]
    congr 2
    rw [hc0def]
    ring
  beta_reduce
  rw [hM, hfac, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  exact hl

theorem point_pi {O : Type} [CommRing O] [IsDomain O] {X : Type} (T : Subalgebra O (X → O)) {d : Type}
    [Fintype d] [DecidableEq d] {G : Type} [Group G] (r : G →* (X → Matrix d d O)) (π : X) {t : ℕ}
    (bl : d → Fin (t + 1)) (χ₁ ε : G →* Oˣ) (hP : PrimHyp O T r π bl χ₁ ε) (eB : X → Matrix d d O)
    (heBπ : eB π = Matrix.diagonal (fun a => if bl a = 0 then 0 else 1)) (g₀ : G)
    (hε : ∀ i j : ℕ, i < t → j < t → (ε g₀) ^ i = (ε g₀) ^ j → i = j) :
    (blockPoly ((eB π).map (algebraMap O (FractionRing O)))
      ((eB π * r g₀ π * eB π).map (algebraMap O (FractionRing O)))).Separable := by
  classical
  obtain ⟨-, -, -, hblk, hcard, hdiag⟩ := hP
  have hφ : Function.Injective (algebraMap O (FractionRing O)) := IsFractionRing.injective O _
  set φ := algebraMap O (FractionRing O) with hφdef
  set lam : d → FractionRing O := fun a => if bl a = 0 then 0 else
    φ ((χ₁ g₀ : O) * (((ε g₀)⁻¹ ^ ((bl a : ℕ) - 1) : Oˣ) : O)) with hlam
  have hone : ∀ a b : d, bl a ≠ 0 → bl a = bl b → a = b := by
    intro a b ha hbl
    have h2 := Fintype.card_le_one_iff.mp (hcard (bl a) ha).le ⟨a, rfl⟩ ⟨b, hbl.symm⟩
    exact congrArg Subtype.val h2
  have he : (eB π).map φ = Matrix.diagonal (fun a => if bl a = 0 then (0 : FractionRing O) else 1) := by
    rw [heBπ]
    ext i j
    rcases eq_or_ne i j with rfl | h
    · by_cases h0 : bl i = 0 <;> simp [h0]
    · simp [h]
  have hA : (eB π * r g₀ π * eB π).map φ = Matrix.diagonal lam := by
    ext a b
    rw [Matrix.map_apply, heBπ, Matrix.mul_diagonal, Matrix.diagonal_mul]
    rcases eq_or_ne a b with rfl | hab
    · by_cases h0 : bl a = 0
      · simp [h0, hlam]
      · simp [h0, hlam, hdiag g₀ a h0]
    · rw [Matrix.diagonal_apply_ne _ hab]
      by_cases ha0 : bl a = 0
      · simp [ha0]
      by_cases hb0 : bl b = 0
      · simp [hb0]
      have hne : bl a ≠ bl b := fun hbl => hab (hone a b ha0 hbl)
      simp [hblk g₀ a b hne]
  rw [he, hA]
  have hm : (Polynomial.X : Polynomial (FractionRing O)) •
        (Matrix.diagonal (fun a => if bl a = 0 then (0 : FractionRing O) else 1)).map Polynomial.C -
        (Matrix.diagonal lam).map Polynomial.C +
        (1 - Matrix.diagonal (fun a => if bl a = 0 then (0 : FractionRing O) else 1)).map Polynomial.C =
      Matrix.diagonal (fun a => if bl a = 0 then 1 else Polynomial.X - Polynomial.C (lam a)) := by
    ext i j
    rcases eq_or_ne i j with rfl | h
    · by_cases h0 : bl i = 0 <;> simp [h0, hlam]
    · simp [h, Matrix.one_apply_ne h]
  have hbp : blockPoly (Matrix.diagonal (fun a => if bl a = 0 then (0 : FractionRing O) else 1))
      (Matrix.diagonal lam) =
      ∏ a ∈ Finset.univ.filter (fun a => bl a ≠ 0), (Polynomial.X - Polynomial.C (lam a)) := by
    unfold blockPoly
    rw [hm, Matrix.det_diagonal, Finset.prod_filter]
    refine Finset.prod_congr rfl fun a _ => ?_
    by_cases h0 : bl a = 0 <;> simp [h0]
  rw [hbp, Polynomial.separable_prod_X_sub_C_iff']
  intro a ha0 b hb0 hlab
  have ha : bl a ≠ 0 := (Finset.mem_filter.mp ha0).2
  have hb : bl b ≠ 0 := (Finset.mem_filter.mp hb0).2
  simp only [hlam, if_neg ha, if_neg hb] at hlab
  have h1 := mul_left_cancel₀ (Units.ne_zero (χ₁ g₀)) (hφ hlab)
  have h2 : (ε g₀)⁻¹ ^ ((bl a : ℕ) - 1) = (ε g₀)⁻¹ ^ ((bl b : ℕ) - 1) := Units.ext h1
  rw [inv_pow, inv_pow, inv_inj] at h2
  have ha' : (bl a : ℕ) ≠ 0 := fun h => ha (by ext; simpa using h)
  have hb' : (bl b : ℕ) ≠ 0 := fun h => hb (by ext; simpa using h)
  have hia : (bl a : ℕ) - 1 < t := by have := (bl a).isLt; omega
  have hib : (bl b : ℕ) - 1 < t := by have := (bl b).isLt; omega
  have h3 := hε _ _ hia hib h2
  exact hone a b ha (Fin.ext (by omega))

theorem density_point_of_corner_simple (hD : StatDensity) (hC : StatCornerSimple) : DensityPointExists := by
  intro O _ _ _ X _ T d _ _ G _ r π t bl χ₁ ε hP eB e₁ hI hG3 g₀ hε L ϖ hϖ
  classical
  have hsep := hP.2.1
  obtain ⟨heBm, -, heBB, -, -, -, -, -, heBπ, -⟩ := hI
  have hpt : ∀ y : {y : X // y ≠ π}, ∃ (j : X → O) (a : X → Matrix d d O), j ∈ T ∧
      (∀ z, z ≠ y.1 → j z = 0) ∧ a ∈ tSpan T r ∧
      (blockPoly ((eB y.1).map (algebraMap O (FractionRing O)))
        ((eB y.1 * r g₀ y.1 * eB y.1 + ϖ ^ L • (j y.1 • (eB y.1 * a y.1 * eB y.1))).map
          (algebraMap O (FractionRing O)))).Separable := by
    intro y
    obtain ⟨m, c, P, hG⟩ := hG3 y.1
    exact point_generic hD hC T r hsep eB heBm heBB y.1 m c P hG (r g₀ y.1) (ϖ ^ L) (pow_ne_zero _ hϖ)
  choose j a hjT hj0 haT hjsep using hpt
  let eqv := Fintype.equivFin {y : X // y ≠ π}
  refine ⟨Fintype.card {y : X // y ≠ π}, fun i => j (eqv.symm i), fun i => a (eqv.symm i),
    fun i => ⟨hjT _, hj0 _ π (eqv.symm i).2.symm, haT _⟩, fun x => ?_⟩
  beta_reduce
  by_cases hx : x = π
  · rw [hx]
    have hzero : ∑ i, j (eqv.symm i) π • (eB π * a (eqv.symm i) π * eB π) = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [hj0 _ π (eqv.symm i).2.symm, zero_smul]
    rw [hzero, smul_zero, add_zero]
    exact point_pi T r π bl χ₁ ε hP eB heBπ g₀ hε
  · have hsum : ∑ i, j (eqv.symm i) x • (eB x * a (eqv.symm i) x * eB x) =
        j ⟨x, hx⟩ x • (eB x * a ⟨x, hx⟩ x * eB x) := by
      rw [Finset.sum_eq_single (eqv ⟨x, hx⟩)]
      · simp
      · intro i _ hi
        rw [hj0 _ x, zero_smul]
        intro hxe
        apply hi
        rw [← eqv.apply_symm_apply i]
        exact congrArg eqv (Subtype.ext hxe.symm)
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [hsum]
    exact hjsep ⟨x, hx⟩

end Formalism.RepresentationBoundsCohomology.ringDataObjects
