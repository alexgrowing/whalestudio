import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEqZpowMulUnit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardSubmoduleAndHomLe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToLePerp

noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.FrameOver

theorem card_coker_dvr {R M : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] {ϖ : R}
    (hϖ : Irreducible ϖ) (φ : M →ₗ[R] M) (n : ℕ) (hd : Associated (LinearMap.det φ) (ϖ ^ n)) :
    Nat.card (M ⧸ LinearMap.range φ) = Nat.card (R ⧸ Ideal.span {ϖ}) ^ n := by
  have hd0 : LinearMap.det φ ≠ 0 := hd.ne_zero_iff.2 (pow_ne_zero _ hϖ.ne_zero)
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot]
    by_contra h
    exact hd0 (LinearMap.det_eq_zero_iff_ker_ne_bot.2 h)
  let N := LinearMap.range φ
  let e : M ≃ₗ[R] N := LinearEquiv.ofInjective φ hinj
  let b := Module.Free.chooseBasis R M
  have h : Module.finrank R N = Module.finrank R M := e.symm.finrank_eq
  let a := Submodule.smithNormalFormCoeffs b h
  let b' := Submodule.smithNormalFormTopBasis b h
  let ab := Submodule.smithNormalFormBotBasis b h
  have ab_eq := Submodule.smithNormalFormBotBasis_def b h
  let e' : M ≃ₗ[R] N := b'.equiv ab (Equiv.refl _)
  let f : M →ₗ[R] M := N.subtype.comp (e' : M →ₗ[R] N)
  have ha : ∀ i, f (b' i) = a i • b' i := by
    intro i
    have : f (b' i) = b'.equiv ab (Equiv.refl _) (b' i) := rfl
    rw [this, b'.equiv_apply, Equiv.refl_apply]
    exact ab_eq i
  have h1 : Associated (LinearMap.det φ) (LinearMap.det f) :=
    LinearMap.associated_det_comp_equiv N.subtype e e'
  have h2 : LinearMap.det f = ∏ i, a i := by
    rw [← LinearMap.det_toMatrix b', ← Matrix.det_diagonal]
    congr 1; ext i j
    rw [LinearMap.toMatrix_apply, ha, map_smul, Module.Basis.repr_self, Finsupp.smul_single,
      smul_eq_mul, mul_one]
    by_cases h : i = j
    · rw [h, Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
    · rw [Matrix.diagonal_apply_ne _ h, Finsupp.single_eq_of_ne h]
  have h3 : Associated (∏ i, a i) (ϖ ^ n) := h2 ▸ h1.symm.trans hd
  have ha0 : ∀ i, a i ≠ 0 := fun i => Submodule.smithNormalFormCoeffs_ne_zero b h i
  choose k hk using fun i => IsDiscreteValuationRing.associated_pow_irreducible (ha0 i) hϖ
  have h4 : Associated (∏ i, a i) (ϖ ^ ∑ i, k i) := by
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Associated.prod _ _ _ fun i _ => hk i
  have h5 : ∑ i, k i = n := by
    have h6 := h4.symm.trans h3
    exact le_antisymm ((pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 h6.dvd)
      ((pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 h6.symm.dvd)
  have hp : (Ideal.span {ϖ}).IsPrime := hϖ.maximalIdeal_eq ▸ inferInstance
  rw [Nat.card_congr (Submodule.quotientEquivPiSpan N b h).toEquiv, Nat.card_pi, ← h5,
    ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hq := cardQuot_pow_of_prime (P := Ideal.span {ϖ})
    (fun h => hϖ.ne_zero (Ideal.span_singleton_eq_bot.1 h)) (i := k i)
  rw [Ideal.span_singleton_pow, Submodule.cardQuot_apply, Submodule.cardQuot_apply] at hq
  rw [← hq, ← Ideal.span_singleton_eq_span_singleton.2 (hk i)]

theorem det_blocks {E : Type} [CommRing E] {r : ℕ} (Z Z' : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hZ : IsUnit Z.det) (T T' : E) :
    (Matrix.fromBlocks Z (Matrix.single (Fin.last r) (Fin.last r) T)
      (Matrix.single (Fin.last r) (Fin.last r) T') Z').det =
    Z.det * Z'.det - T * T' * ((Z.submatrix Fin.castSucc Fin.castSucc).det *
      (Z'.submatrix Fin.castSucc Fin.castSucc).det) := by
  let := Z.invertibleOfIsUnitDet hZ
  have hadj : ∀ A : Matrix (Fin (r + 1)) (Fin (r + 1)) E, A.adjugate (Fin.last r) (Fin.last r) =
      (A.submatrix Fin.castSucc Fin.castSucc).det := fun A => by
    simp [Matrix.adjugate_fin_succ_eq_det_submatrix, ← two_mul]
  have hupd : ∀ c : E, (Z' - Matrix.single (Fin.last r) (Fin.last r) c).det =
      Z'.det - c * (Z'.submatrix Fin.castSucc Fin.castSucc).det := fun c => by
    have : Z' - Matrix.single (Fin.last r) (Fin.last r) c =
        Z'.updateRow (Fin.last r) (Z' (Fin.last r) + (-c) • Pi.single (Fin.last r) 1) := by
      ext i j
      by_cases hi : i = Fin.last r
      · subst hi
        by_cases hj : j = Fin.last r
        · subst hj; simp [sub_eq_add_neg]
        · simp [hj, Matrix.single_apply, Ne.symm hj]
      · simp [hi, Matrix.single_apply, Ne.symm hi]
    rw [this, Matrix.det_updateRow_add, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self,
      ← Matrix.adjugate_apply, hadj]
    ring
  rw [Matrix.det_fromBlocks₁₁, Matrix.single_mul_mul_single, hupd, Matrix.invOf_eq_nonsing_inv,
    Matrix.inv_def, Matrix.smul_apply, hadj, smul_eq_mul]
  have := Ring.mul_inverse_cancel _ hZ
  linear_combination (-(T * T' * ((Z.submatrix Fin.castSucc Fin.castSucc).det *
      (Z'.submatrix Fin.castSucc Fin.castSucc).det))) * this

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem card_coker [IsNonarchimedeanLocalField F] [CharZero F] (L : LocE F E) {ϖ : 𝒪[F]}
    (hϖ : Irreducible ϖ) {ι : Type} [Fintype ι] [DecidableEq ι] (N : Matrix ι ι L.O) (a : ℕ)
    (u : (𝒪[F])ˣ) (hN : ((N.det : L.O) : E) = algebraMap F E ((ϖ : F) ^ a * ((u : 𝒪[F]) : F))) :
    Nat.card ((ι → L.O) ⧸ LinearMap.range N.vecMulLinear) = resQ ϖ ^ (2 * a) := by
  obtain ⟨ω, hω, e, he, hωe⟩ := GlobalTheory.UnramOrder.exists_sub_cj_mul_eq_one L
  have hint : ∀ a : 𝒪[F], algebraMap F E a ∈ L.O := fun a =>
    (GlobalTheory.UnramOrder.algebraMap_mem_iff L a).2 a.2
  let i : 𝒪[F] →+* L.O := (algebraMap 𝒪[F] E).codRestrict L.O hint
  let : Algebra 𝒪[F] L.O := i.toAlgebra
  have hal : ∀ a : 𝒪[F], ((algebraMap 𝒪[F] L.O a : L.O) : E) = algebraMap F E a := fun _ => rfl
  let c : L.O →+* L.O := (L.cj : E →+* E).restrict L.O L.O fun x hx => GlobalTheory.UnramOrder.cj_mem L hx
  have hcv : ∀ x : L.O, ((c x : L.O) : E) = L.cj x := fun _ => rfl
  have hc : ∀ x, c (c x) = x := fun x => Subtype.ext (L.cj_cj x)
  have hbase : ∀ r, c (algebraMap 𝒪[F] L.O r) = algebraMap 𝒪[F] L.O r := fun r =>
    Subtype.ext (by rw [hcv, hal, AlgEquiv.commutes])
  have hfix : ∀ x, c x = x → x ∈ (algebraMap 𝒪[F] L.O).range := fun x hx => by
    obtain ⟨a, ha⟩ := GlobalTheory.UnramOrder.exists_int_of_fixed L x.2 (congrArg Subtype.val hx)
    exact ⟨a, Subtype.ext ha.symm⟩
  have hinj : Function.Injective (algebraMap 𝒪[F] L.O) := fun a b h =>
    Subtype.ext (GlobalTheory.UnramOrder.algebraMap_inj L (congrArg Subtype.val h))
  have hu : IsUnit ((⟨ω, hω⟩ : L.O) - c ⟨ω, hω⟩) :=
    IsUnit.of_mul_eq_one ⟨e, he⟩ (Subtype.ext hωe)
  have hli : LinearIndependent 𝒪[F] ![(1 : L.O), ⟨ω, hω⟩] := by
    rw [LinearIndependent.pair_iff]
    intro a b h
    rw [Algebra.smul_def, Algebra.smul_def, mul_one] at h
    have h' := congrArg c h
    rw [map_add, map_mul, hbase, hbase, map_zero] at h'
    have hb : algebraMap 𝒪[F] L.O b = 0 :=
      hu.mul_left_eq_zero.1 (by linear_combination h - h')
    have ha : algebraMap 𝒪[F] L.O a = 0 := by rw [hb] at h; simpa using h
    exact ⟨hinj (by simpa using ha), hinj (by simpa using hb)⟩
  have hsp : ⊤ ≤ Submodule.span 𝒪[F] (Set.range ![(1 : L.O), ⟨ω, hω⟩]) := by
    intro x _
    obtain ⟨a, b, h⟩ := GlobalTheory.UnramOrder.exists_eq_add_mul c hc hbase hfix hu x
    rw [Submodule.mem_span_range_iff_exists_fun]
    exact ⟨![a, b], by simp [h, Algebra.smul_def]⟩
  let B := Module.Basis.mk hli hsp
  have : Module.Free 𝒪[F] L.O := Module.Free.of_basis B
  have : Module.Finite 𝒪[F] L.O := Module.Finite.of_basis B
  have hdet : N.det = algebraMap 𝒪[F] L.O (ϖ ^ a * u) := Subtype.ext (by rw [hN, hal]; simp)
  have key := card_coker_dvr hϖ (N.vecMulLinear.restrictScalars 𝒪[F]) (2 * a) (by
    have h1 : LinearMap.det N.vecMulLinear = N.det := by
      rw [← Matrix.det_transpose, ← LinearMap.det_toLin']
      congr 1
      refine LinearMap.ext fun x => ?_
      simp [Matrix.mulVec_transpose]
    rw [LinearMap.det_restrictScalars, h1, hdet, Algebra.norm_algebraMap_of_basis B,
      Fintype.card_fin, mul_pow, ← pow_mul, mul_comm a 2]
    exact associated_mul_unit_left _ _ (u.isUnit.pow 2))
  rw [resQ, ← key]
  rfl

theorem count [IsNonarchimedeanLocalField F] [CharZero F] (L : LocE F E) {ϖ : 𝒪[F]}
    (hϖ : Irreducible ϖ) {ι : Type} [Fintype ι] [DecidableEq ι] {V : Type} [AddCommGroup V]
    [Module E V] (g : ι → V) (Φ : V →ₗ[E] (ι → E)) (a : ℕ) (u : (𝒪[F])ˣ)
    (hN : (Matrix.of fun i j => Φ (g i) j).det = algebraMap F E ((ϖ : F) ^ a * ((u : 𝒪[F]) : F)))
    (s : Set (Submodule L.O V))
    (hs : ∀ P ∈ s, (∀ i, g i ∈ P) ∧ (∀ x ∈ P, x ∈ Submodule.span E (Set.range g)) ∧
      ∀ x ∈ P, ∀ j, Φ x j ∈ L.O) :
    s.encard ≤ (resQ ϖ ^ (2 * a * Fintype.card ι) : ℕ) := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨P0, hP0⟩
  · simp
  let N : Matrix ι ι L.O := fun i j => ⟨Φ (g i) j, (hs P0 hP0).2.2 _ ((hs P0 hP0).1 i) j⟩
  have hcard := card_coker L hϖ N a u (by
    rw [← hN]; exact RingHom.map_det L.O.subtype N)
  have hq : 2 ≤ resQ ϖ := (GlobalTheory.UnramOrder.order_facts L ϖ hϖ).2.2.2.2.2.2.1
  have hfin : Finite ((ι → L.O) ⧸ LinearMap.range N.vecMulLinear) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  have hsub := (GlobalTheory.SubmoduleCount.card_submodule_and_hom_le L
    ((ι → L.O) ⧸ LinearMap.range N.vecMulLinear) (Fintype.card ι)
    (fun i => (LinearMap.range N.vecMulLinear).mkQ (Pi.single ((Fintype.equivFin ι).symm i) 1)) (by
      have h1 : (Set.range fun i => (LinearMap.range N.vecMulLinear).mkQ
          (Pi.single ((Fintype.equivFin ι).symm i) 1)) =
          (LinearMap.range N.vecMulLinear).mkQ '' Set.range (Pi.basisFun L.O ι) := by
        rw [← Set.range_comp, ← (Fintype.equivFin ι).symm.surjective.range_comp]
        congr 1; funext i; simp
      rw [h1, ← Submodule.map_span, Module.Basis.span_eq, Submodule.map_top,
        Submodule.range_mkQ])).1
  rw [hcard, ← pow_mul] at hsub
  have hunit : IsUnit (Matrix.of fun i j => Φ (g i) j).det := by
    rw [hN]
    refine (IsUnit.mk0 _ ?_).map _
    exact mul_ne_zero (pow_ne_zero _ fun h => hϖ.ne_zero (Subtype.ext h))
      fun h => u.ne_zero (Subtype.ext h)
  have hΦ : ∀ c : ι → E, Φ (∑ i, c i • g i) = Matrix.vecMul c (Matrix.of fun i j => Φ (g i) j) :=
    fun c => by
    funext j
    simp [Matrix.vecMul, dotProduct]
  have hker : ∀ x ∈ Submodule.span E (Set.range g), Φ x = 0 → x = 0 := fun x hx h0 => by
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hx
    rw [hΦ] at h0
    have : c = 0 := Matrix.vecMul_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 hunit)
      (by simpa using h0)
    simp [this]
  let Q : Submodule L.O V → Submodule L.O (ι → L.O) := fun P =>
    (P.map (Φ.restrictScalars L.O)).comap (LinearMap.compLeft (Algebra.linearMap L.O E) ι)
  have hQ : ∀ P z, z ∈ Q P ↔ ∃ x ∈ P, Φ x = fun j => (z j : E) := fun P z => Iff.rfl
  have hle : ∀ P ∈ s, LinearMap.range N.vecMulLinear ≤ Q P := by
    rintro P hP _ ⟨c, rfl⟩
    refine (hQ _ _).2 ⟨∑ i, c i • g i, P.sum_mem fun i _ => P.smul_mem _ ((hs P hP).1 i), ?_⟩
    have := hΦ fun i => c i
    refine Eq.trans this ?_
    funext j
    exact (RingHom.map_vecMul L.O.subtype N c j).symm
  have hmono : ∀ P ∈ s, ∀ P' ∈ s, Q P ≤ Q P' → P ≤ P' := fun P hP P' hP' h x hx => by
    obtain ⟨y, hy, hxy⟩ := (hQ P' fun j => ⟨Φ x j, (hs P hP).2.2 x hx j⟩).1
      (h ((hQ _ _).2 ⟨x, hx, rfl⟩))
    have := hker (x - y) (Submodule.sub_mem _ ((hs P hP).2.1 x hx) ((hs P' hP').2.1 y hy))
      (by rw [map_sub, hxy]; exact sub_self _)
    rwa [sub_eq_zero.1 this]
  have hinj : Set.InjOn (fun P => (Q P).map (LinearMap.range N.vecMulLinear).mkQ) s := by
    intro P hP P' hP' h
    have h2 := congrArg (Submodule.comap (LinearMap.range N.vecMulLinear).mkQ) h
    simp only [Submodule.comap_map_mkQ, sup_eq_right.2 (hle P hP), sup_eq_right.2 (hle P' hP')] at h2
    exact le_antisymm (hmono P hP P' hP' h2.le) (hmono P' hP' P hP h2.ge)
  rw [← hinj.encard_image]
  refine (Set.encard_le_encard (Set.subset_univ _)).trans ?_
  rw [Set.encard_univ, ENat.card_eq_coe_natCard]
  exact_mod_cast hsub

theorem hf_comb (L : LocE F E) {n : ℕ} {H : Matrix (Fin n) (Fin n) E} (h : IsHerm L H)
    {ι : Type} [Fintype ι] (B B' : Matrix ι ι E) (v w : ι → Fin n → E) :
    (Matrix.of fun i j => hf L H (∑ k, B k i • v k) (∑ k, B' k j • w k)) =
      B.transpose * (Matrix.of fun i j => hf L H (v i) (w j)) * B'.map L.cj := by
  have key : ∀ (α : ι → E) (g : ι → Fin n → E) (y : Fin n → E),
      hf L H (∑ i, α i • g i) y = ∑ i, α i * hf L H (g i) y := fun α g y => by
    change GlobalTheory.FrameBasic.hfL L H y _ = _
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul]; rfl
  ext i j
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  rw [GlobalTheory.FrameBasic.hf_conj L h, key, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul, ← GlobalTheory.FrameBasic.hf_conj L h, key, Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ => by ring

theorem det_base [IsNonarchimedeanLocalField F] [CharZero F] (L : LocE F E) {r k : ℕ}
    (S : Frames L r k) :
    (Matrix.of fun i j => hf L S.Hm (Sum.elim S.f' S.f i) (Sum.elim S.f S.f' j)).det = S.G := by
  have hU : IsUnit S.Zh.det := (GlobalTheory.FrameBasic.main L r k S).2.2.2.1
  have h1 : (Matrix.of fun i j => hf L S.Hm (Sum.elim S.f' S.f i) (Sum.elim S.f S.f' j)) =
      Matrix.fromBlocks S.Zh.transpose
        (Matrix.single (Fin.last r) (Fin.last r) (-algebraMap F E S.T'))
        (Matrix.single (Fin.last r) (Fin.last r) (-algebraMap F E S.T)) (S.Zh.map L.cj) := by
    ext (i | i) (j | j)
    · rfl
    · simp [S.gram', Matrix.single_apply, eq_comm]
    · simp [S.gram, Matrix.single_apply, eq_comm]
    · exact GlobalTheory.FrameBasic.hf_conj L S.herm.1 _ _
  have hD1 : S.D (Fin.last (r + 1)) = S.Zh.det := rfl
  have hD0 : S.D (Fin.last r).castSucc = (S.Zh.submatrix Fin.castSucc Fin.castSucc).det := rfl
  have hdet : ∀ {m : ℕ} (A : Matrix (Fin m) (Fin m) E), (A.map L.cj).det = L.cj A.det := fun A =>
    (AlgEquiv.map_det L.cj A).symm
  rw [h1, det_blocks _ _ (by rwa [Matrix.det_transpose]), Frames.G, hD1, hD0,
    ← Matrix.transpose_submatrix, Matrix.submatrix_map, hdet, hdet, Matrix.det_transpose,
    Matrix.det_transpose, map_mul]
  ring

theorem exists_det_one [IsNonarchimedeanLocalField F] [CharZero F] (L : LocE F E) {r k : ℕ}
    (S : Frames L r k) {C : Set S.FrP} (hC : S.IsCls C) {p : S.FrP} (hp : p ∈ C) :
    ∃ U U' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, U.det = 1 ∧ U'.det = 1 ∧
      (∀ j, p.1 j = ∑ i, U i j • S.f i) ∧ ∀ j, p.2 j = ∑ i, U' i j • S.f' i := by
  obtain ⟨n, hn, n', hn', rfl⟩ := hC
  obtain ⟨A, A', -, -, h0, h1, -, hA, hA'⟩ := hp
  obtain ⟨s, ⟨hs0, hs1⟩, hs⟩ := (GlobalTheory.HL.FrameOnto.unipotent_onto L r k S).1 n hn
  obtain ⟨s', ⟨hs0', hs1'⟩, hs'⟩ := (GlobalTheory.HL.FrameOnto.unipotent_onto L r k S).2.1 n' hn'
  have hd : ∀ B : Matrix (Fin (r + 1)) (Fin (r + 1)) E, (∀ i j, j < i → B i j = 0) →
      (∀ i, B i i = 1) → B.det = 1 := fun B b0 b1 => by
    rw [Matrix.det_of_upperTriangular (fun i j h => b0 i j h)]
    simp [b1]
  refine ⟨s * A, s' * A', ?_, ?_, fun j => ?_, fun j => ?_⟩
  · rw [Matrix.det_mul, hd s hs0 hs1, hd A (fun i j h => (h0 i j h).1) (fun i => (h1 i).1), one_mul]
  · rw [Matrix.det_mul, hd s' hs0' hs1', hd A' (fun i j h => (h0 i j h).2) (fun i => (h1 i).2),
      one_mul]
  · simp only [hA, hs, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  · simp only [hA', hs', Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
    rw [Finset.sum_comm]
    simp only [mul_comm]

theorem encard_overlattices_le : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ C, S.IsCls C → ∀ p ∈ C, 0 ≤ S.a → ({Mh : Submodule L.O S.V | S.Mof p.1 p.2 ≤ Mh ∧ (∀ x ∈ Mh, x ∈ S.ME) ∧ ∀ x ∈ Mh, ∀ y ∈ Mh, S.h x y ∈ L.O}.encard : ℝ≥0∞) ≤ (S.q : ℝ≥0∞) ^ (2 * S.a.toNat * (2 * r + 2)) := by
  intro F _ _ _ _ _ E _ _ _ L r k S C hC p hp ha
  obtain ⟨U, U', hU, hU', h1, h2⟩ := exists_det_one L S hC hp
  obtain ⟨-, -, ⟨c, hc0, hc⟩, -, -, hth, -, -⟩ := GlobalTheory.FrameBasic.main L r k S
  obtain ⟨u, hu⟩ := (GlobalTheory.UnramVal.vE_valuation L S.ϖ S.ϖ_irr).2.2.2 c hc0
  have hϖ0 : (S.ϖ : F) ≠ 0 := fun h => S.ϖ_irr.ne_zero (Subtype.ext h)
  set t : E := algebraMap F E S.th⁻¹ with ht
  let g : Fin (r + 1) ⊕ Fin (r + 1) → S.V := Sum.elim (fun b => t • (p.2 b - p.1 b)) p.1
  let g' : Fin (r + 1) ⊕ Fin (r + 1) → S.V := Sum.elim p.1 (fun b => t • (p.2 b - p.1 b))
  let B : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) E :=
    Matrix.fromBlocks (t • U') 0 (-(t • U)) U
  let B' : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) E :=
    Matrix.fromBlocks U (-(t • U)) 0 (t • U')
  have hg : ∀ i, g i = ∑ l, B l i • Sum.elim S.f' S.f l := by
    rintro (i | i)
    · simp [g, B, h1, h2, smul_sub, Finset.smul_sum, smul_smul, sub_eq_add_neg, add_comm]
    · simp [g, B, h1]
  have hg' : ∀ i, g' i = ∑ l, B' l i • Sum.elim S.f S.f' l := by
    rintro (i | i)
    · simp [g', B', h1]
    · simp [g', B', h1, h2, smul_sub, Finset.smul_sum, smul_smul, sub_eq_add_neg, add_comm]
  have hB : B.det = t ^ (r + 1) := by
    simp [B, Matrix.det_fromBlocks_zero₁₂, hU, hU']
  have hB' : B'.det = t ^ (r + 1) := by
    simp [B', Matrix.det_fromBlocks_zero₂₁, hU, hU']
  have hBu : IsUnit B.det := by
    rw [hB]; exact ((IsUnit.mk0 _ (inv_ne_zero hth)).map _).pow _
  have hME : S.ME ≤ Submodule.span E (Set.range g) := by
    have hv : ∀ l, Sum.elim S.f' S.f l ∈ Submodule.span E (Set.range g) := fun l => by
      refine (Submodule.mem_span_range_iff_exists_fun E).2 ⟨fun i => B⁻¹ i l, ?_⟩
      simp only [hg, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_smul, mul_comm (B⁻¹ _ _), ← Matrix.mul_apply,
        Matrix.mul_nonsing_inv B hBu, Matrix.one_apply, ite_smul, one_smul, zero_smul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
    refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨i, -, rfl⟩; exact hv (Sum.inr i)
    · rintro _ ⟨i, -, rfl⟩; exact hv (Sum.inl i)
  let Φ : S.V →ₗ[E] (Fin (r + 1) ⊕ Fin (r + 1) → E) :=
    LinearMap.pi fun j => GlobalTheory.FrameBasic.hfL L S.Hm (g' j)
  have hdet : (Matrix.of fun i j => Φ (g i) j).det =
      algebraMap F E ((S.ϖ : F) ^ S.a.toNat * ((u : 𝒪[F]) : F)) := by
    have e : (Matrix.of fun i j => Φ (g i) j) = Matrix.of fun i j => hf L S.Hm
        (∑ l, B l i • Sum.elim S.f' S.f l) (∑ l, B' l j • Sum.elim S.f S.f' l) := by
      ext i j
      rw [Matrix.of_apply, Matrix.of_apply, ← hg, ← hg']; rfl
    have e2 : (B'.map L.cj).det = L.cj B'.det := (AlgEquiv.map_det L.cj B').symm
    rw [e, hf_comb L S.herm.1, Matrix.det_mul, Matrix.det_mul, det_base, Matrix.det_transpose, e2,
      hB, hB', ht, map_pow, AlgEquiv.commutes, hc, ← map_pow, ← map_mul, ← map_mul]
    congr 1
    have hθ : S.th = (S.ϖ : F) ^ S.vth := by
      unfold Frames.th Frames.vth
      split_ifs <;> simp
    have hv : vE L S.ϖ (algebraMap F E c) = S.a + 2 * (r + 1) * S.vth := by
      rw [Frames.a, hc]; ring
    rw [← zpow_natCast (S.ϖ : F) S.a.toNat, Int.toNat_of_nonneg ha]
    rw [hv, zpow_add₀ hϖ0, mul_comm _ S.vth, zpow_mul, ← hθ] at hu
    have hn : (2 * (r + 1) : ℤ) = ((2 * (r + 1) : ℕ) : ℤ) := by push_cast; ring
    rw [hn, zpow_natCast] at hu
    have h3 : S.th⁻¹ ^ (r + 1) * S.th ^ (r + 1) = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hth, one_pow]
    rw [hu, two_mul, pow_add S.th (r + 1)]
    linear_combination ((S.ϖ : F) ^ S.a * ((u : 𝒪[F]) : F)) *
      (S.th⁻¹ ^ (r + 1) * S.th ^ (r + 1) + 1) * h3
  have hgM : ∀ i, g i ∈ S.Mof p.1 p.2 := by
    rintro (i | i)
    · exact Submodule.subset_span (Or.inr ⟨i, rfl⟩)
    · exact Submodule.subset_span (Or.inl ⟨i, rfl⟩)
  have hgM' : ∀ i, g' i ∈ S.Mof p.1 p.2 := by
    rintro (i | i)
    · exact Submodule.subset_span (Or.inl ⟨i, rfl⟩)
    · exact Submodule.subset_span (Or.inr ⟨i, rfl⟩)
  have key := count L S.ϖ_irr g Φ S.a.toNat u hdet
    {Mh : Submodule L.O S.V | S.Mof p.1 p.2 ≤ Mh ∧ (∀ x ∈ Mh, x ∈ S.ME) ∧
      ∀ x ∈ Mh, ∀ y ∈ Mh, S.h x y ∈ L.O}
    (fun P hP => ⟨fun i => hP.1 (hgM i), fun x hx => hME (hP.2.1 x hx),
      fun x hx j => hP.2.2 x hx _ (hP.1 (hgM' j))⟩)
  have hcard : Fintype.card (Fin (r + 1) ⊕ Fin (r + 1)) = 2 * r + 2 := by
    simp only [Fintype.card_sum, Fintype.card_fin]; ring
  rw [hcard] at key
  refine (ENat.toENNReal_le.2 key).trans_eq ?_
  rw [ENat.toENNReal_coe, Nat.cast_pow]
  rfl

end GlobalTheory.FrameOver
