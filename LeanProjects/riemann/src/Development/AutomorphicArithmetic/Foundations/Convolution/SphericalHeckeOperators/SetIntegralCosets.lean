import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.SymSum
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.DcoShape
import GroundTheory.AutomorphicForms.WhittakerGroups

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa UpperTheory.ConvolutionTheory.H

private theorem sum_fiber {A : Type*} [Group A] (P R : Subgroup A) (h : P ≤ R)
    [Fintype (A ⧸ P)] [Fintype (A ⧸ R)] [Fintype (R ⧸ P.subgroupOf R)] (f : A → ℂ)
    (hf : ∀ m, ∀ b ∈ R, f (m * b) = f m) :
    ∑ q : A ⧸ P, f q.out = (Fintype.card (R ⧸ P.subgroupOf R) : ℂ) * ∑ q : A ⧸ R, f q.out := by
  classical
  let e := Subgroup.quotientEquivProdOfLE h
  have aux : ∀ q : A ⧸ P, (e q).1 = ((q.out : A) : A ⧸ R) := by
    intro q
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  have inv : ∀ a b : A, (a : A ⧸ R) = (b : A ⧸ R) → f a = f b := by
    intro a b hab
    have := hf a _ (QuotientGroup.eq.1 hab)
    rw [← this]
    simp
  have key : ∀ p : (A ⧸ R) × (R ⧸ P.subgroupOf R), f (e.symm p).out = f p.1.out := by
    intro p
    apply inv
    rw [← aux, Equiv.apply_symm_apply, QuotientGroup.out_eq']
  rw [← e.symm.sum_comp, Fintype.sum_prod_type_right]
  simp only [key, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.mul_sum]

private theorem sum_vanish {A : Type*} [Group A] (L R : Subgroup A) [Fintype (A ⧸ L)] [Fintype (A ⧸ R)]
    (φ : A → ℂ) (hL : ∀ b ∈ L, ∀ m, φ (b * m) = φ m) (hR : ∀ m, ∀ b ∈ R, φ (m * b) = φ m)
    (h : ∑ q : A ⧸ R, φ q.out = 0) : ∑ q : A ⧸ L, φ (q.out)⁻¹ = 0 := by
  classical
  haveI : L.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  haveI : R.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  let P : Subgroup A := (L ⊓ R).normalCore
  haveI : P.Normal := Subgroup.normalCore_normal _
  haveI : P.FiniteIndex := inferInstance
  have hPL : P ≤ L := (Subgroup.normalCore_le _).trans inf_le_left
  have hPR : P ≤ R := (Subgroup.normalCore_le _).trans inf_le_right
  letI : Fintype (A ⧸ P) := Fintype.ofFinite _
  letI : Fintype (L ⧸ P.subgroupOf L) := Fintype.ofFinite _
  letI : Fintype (R ⧸ P.subgroupOf R) := Fintype.ofFinite _
  have h1 := sum_fiber P R hPR φ hR
  have h2 := sum_fiber P L hPL (fun m => φ m⁻¹) (fun m b hb => by
    rw [mul_inv_rev]; exact hL _ (L.inv_mem hb) _)
  have h3 : ∑ q : A ⧸ P, φ q.out = ∑ q : A ⧸ P, φ (q.out)⁻¹ := by
    rw [← Equiv.sum_comp (Equiv.inv (A ⧸ P)) (fun q : A ⧸ P => φ q.out)]
    refine Finset.sum_congr rfl fun q _ => ?_
    have e : (((q.out)⁻¹ : A) : A ⧸ P) = (((Equiv.inv (A ⧸ P)) q).out : A) := by
      rw [QuotientGroup.out_eq', QuotientGroup.mk_inv, QuotientGroup.out_eq']
      rfl
    have := hR ((q.out)⁻¹) _ (hPR (QuotientGroup.eq.1 e))
    rw [← this]
    simp
  rw [h, mul_zero, h3, h2] at h1
  have hc : (Fintype.card (L ⧸ P.subgroupOf L) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  exact (mul_eq_zero.1 h1).resolve_left hc

private theorem setIntegral_cosets {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [μ.IsMulLeftInvariant] (A I J : Subgroup G) (t : G)
    (hJ : ∀ x, x ∈ J ↔ t⁻¹ * x * t ∈ I) (hI : MeasurableSet (I : Set G)) (hfin : μ (I : Set G) ≠ ⊤)
    [Fintype (A ⧸ J.subgroupOf A)] (f : G → ℂ) (hf : ∀ g, ∀ y ∈ I, f (g * y) = f g) :
    ∫ g in {g | ∃ x ∈ A, ∃ y ∈ I, g = x * t * y}, f g ∂μ =
      (μ.real (I : Set G) : ℂ) * ∑ q : A ⧸ J.subgroupOf A, f ((q.out : G) * t) := by
  classical
  let S : A ⧸ J.subgroupOf A → Set G := fun q => (fun g => ((q.out : G) * t)⁻¹ * g) ⁻¹' (I : Set G)
  have hU : {g | ∃ x ∈ A, ∃ y ∈ I, g = x * t * y} = ⋃ q, S q := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, S, Set.mem_preimage, SetLike.mem_coe]
    constructor
    · rintro ⟨x, hx, y, hy, rfl⟩
      refine ⟨((⟨x, hx⟩ : A) : A ⧸ J.subgroupOf A), ?_⟩
      have h := QuotientGroup.eq.1 (QuotientGroup.out_eq' ((⟨x, hx⟩ : A) : A ⧸ J.subgroupOf A))
      rw [Subgroup.mem_subgroupOf, hJ] at h
      have := I.mul_mem h hy
      simpa [mul_assoc] using this
    · rintro ⟨q, hq⟩
      exact ⟨q.out, q.out.2, _, hq, by group⟩
  have hd : Pairwise (Function.onFun Disjoint S) := by
    intro p q hpq
    refine Set.disjoint_left.2 fun g hp hq => hpq ?_
    rw [← QuotientGroup.out_eq' p, ← QuotientGroup.out_eq' q, QuotientGroup.eq,
      Subgroup.mem_subgroupOf, hJ]
    have := I.mul_mem hp (I.inv_mem hq)
    simpa [mul_assoc] using this
  have hm : ∀ q, MeasurableSet (S q) := fun q => measurable_const_mul _ hI
  have hμ : ∀ q, μ (S q) = μ (I : Set G) := fun q => measure_preimage_mul μ _ _
  have hc : ∀ q, ∀ g ∈ S q, f g = f ((q.out : G) * t) := by
    intro q g hg
    have h2 : ((q.out : G) * t) * (((q.out : G) * t)⁻¹ * g) = g := mul_inv_cancel_left _ _
    have := hf ((q.out : G) * t) (((q.out : G) * t)⁻¹ * g) hg
    rwa [h2] at this
  have hint : ∀ q, IntegrableOn f (S q) μ := fun q =>
    (integrableOn_const (C := f ((q.out : G) * t)) (by rw [hμ]; exact hfin)).congr_fun
      (fun g hg => (hc q g hg).symm) (hm q)
  rw [hU, integral_iUnion_fintype hm hd hint, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [setIntegral_congr_fun (hm q) (hc q), setIntegral_const]
  simp [Measure.real, hμ]

private theorem isOpen_cosets {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (A I : Subgroup G) (hI : IsOpen (I : Set G)) (t : G) :
    IsOpen {g | ∃ x ∈ A, ∃ y ∈ I, g = x * t * y} := by
  have : {g | ∃ x ∈ A, ∃ y ∈ I, g = x * t * y} = ⋃ x ∈ A, (fun g => (x * t)⁻¹ * g) ⁻¹' (I : Set G) := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe, exists_prop]
    constructor
    · rintro ⟨x, hx, y, hy, rfl⟩
      exact ⟨x, hx, by simpa [mul_assoc] using hy⟩
    · rintro ⟨x, hx, h⟩
      exact ⟨x, hx, _, h, by group⟩
  rw [this]
  exact isOpen_biUnion fun x _ => hI.preimage (by fun_prop)

private theorem cosets_eq {G : Type*} [Group G] (C I : Subgroup G) {s g : G}
    (h : ∃ u ∈ C, ∃ y ∈ I, s = u * g * y) :
    {p | ∃ u ∈ C, ∃ y ∈ I, p = u * s * y} = {p | ∃ u ∈ C, ∃ y ∈ I, p = u * g * y} := by
  obtain ⟨u, hu, y, hy, rfl⟩ := h
  ext p
  constructor
  · rintro ⟨v, hv, z, hz, rfl⟩
    exact ⟨v * u, C.mul_mem hv hu, y * z, I.mul_mem hy hz, by group⟩
  · rintro ⟨v, hv, z, hz, rfl⟩
    exact ⟨v * u⁻¹, C.mul_mem hv (C.inv_mem hu), y⁻¹ * z, I.mul_mem (I.inv_mem hy) hz, by group⟩

private theorem vanish_of_cover {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) (N C I : Subgroup G) (hCN : C ≤ N)
    (hI : IsOpen (I : Set G)) (T : G → ℂ) (S : Finset G)
    (hS : ∀ g, T g ≠ 0 → ∃ s ∈ S, ∃ y ∈ I, g = s * y)
    (hC : ∀ s ∈ S, ∀ s' ∈ S, (∃ u ∈ N, ∃ y ∈ I, s' = u * s * y) → ∃ u ∈ C, ∃ y ∈ I, s' = u * s * y)
    (h0 : ∀ g₀, ∫ g in {g | ∃ u ∈ N, ∃ y ∈ I, g = u * g₀ * y}, T g ∂μ = 0) (g : G) :
    ∫ p in {p | ∃ u ∈ C, ∃ y ∈ I, p = u * g * y}, T p ∂μ = 0 := by
  by_cases h : ∃ p ∈ {p | ∃ u ∈ C, ∃ y ∈ I, p = u * g * y}, T p ≠ 0
  · obtain ⟨p, ⟨c, hc, y, hy, rfl⟩, hp⟩ := h
    obtain ⟨s, hs, y', hy', hsy⟩ := hS _ hp
    have hmem : ∃ u ∈ C, ∃ y ∈ I, s = u * g * y :=
      ⟨c, hc, y * y'⁻¹, I.mul_mem hy (I.inv_mem hy'), by
        rw [← mul_assoc, ← mul_inv_eq_iff_eq_mul.2 hsy]⟩
    rw [← cosets_eq C I hmem, ← h0 s]
    refine (setIntegral_eq_of_subset_of_forall_diff_eq_zero
      (isOpen_cosets N I hI s).measurableSet ?_ ?_).symm
    · rintro p ⟨u, hu, y, hy, rfl⟩
      exact ⟨u, hCN hu, y, hy, rfl⟩
    · rintro p ⟨⟨u, hu, y, hy, rfl⟩, hn⟩
      by_contra hT
      obtain ⟨s', hs', z, hz, hsz⟩ := hS _ hT
      obtain ⟨v, hv, x, hx, hvx⟩ := hC s hs s' hs' ⟨u, hu, y * z⁻¹, I.mul_mem hy (I.inv_mem hz), by
        rw [← mul_assoc, ← mul_inv_eq_iff_eq_mul.2 hsz]⟩
      exact hn ⟨v, hv, x * z, I.mul_mem hx hz, by rw [hsz, hvx]; group⟩
  · push_neg at h
    exact setIntegral_eq_zero_of_forall_eq_zero h

private theorem exists_cover {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (I : Subgroup G) (hI : IsOpen (I : Set G)) (T : G → ℂ) (hT : HasCompactSupport T) :
    ∃ S : Finset G, ∀ g, T g ≠ 0 → ∃ s ∈ S, ∃ y ∈ I, g = s * y := by
  obtain ⟨S, -, hS⟩ := hT.isCompact.elim_nhds_subcover (fun x => (fun g => x⁻¹ * g) ⁻¹' (I : Set G))
    (fun x _ => (hI.preimage (by fun_prop)).mem_nhds (by simp [I.one_mem]))
  refine ⟨S, fun g hg => ?_⟩
  have := hS (subset_tsupport T hg)
  simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe, exists_prop] at this
  obtain ⟨s, hs, h⟩ := this
  exact ⟨s, hs, _, h, by group⟩

private theorem exists_depth (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (x : F) : ∃ k : ℕ, ∀ e : ℤ, (k : ℤ) ≤ e →
      ValuativeRel.valuation F ((GLnLocal.uniformizer F : F) ^ e * x) ≤ 1 := by
  by_cases hx : x = 0
  · exact ⟨0, fun e _ => by simp [hx]⟩
  obtain ⟨z, u, rfl⟩ := exists_zpow_mul_unit F hx
  refine ⟨(-z).toNat, fun e he => ?_⟩
  have h0 : ((0 : ℕ) : ℤ) ≤ e + z := by push_cast; omega
  rw [← mul_assoc, ← zpow_add₀ (GLnLocal.uniformizer_ne_zero F)]
  have h1 := Parabolic.valuation_zpow_mul_le_pow_mul (F := F) (x := ((u : (ValuativeRel.valuation F).integer) : F)) h0
  rw [pow_zero, one_mul] at h1
  exact h1.trans ((Valuation.mem_integer_iff _ _).1 (u : (ValuativeRel.valuation F).integer).2)

private theorem exists_deep (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (n : ℕ) {ι : Type*} [Finite ι] (u : ι → GL (Fin n) F) (hu : ∀ i, u i ∈ unipotent F n) :
    ∃ a : Fin n → ℤ, Antitone a ∧ ∀ i, torusPow F n a * u i * (torusPow F n a)⁻¹ ∈ unipotent F n ⊓ integralGL F n := by
  choose k hk using fun p : ι × Fin n × Fin n =>
    exists_depth F ((u p.1 : Matrix (Fin n) (Fin n) F) p.2.1 p.2.2)
  obtain ⟨K, hK⟩ := Finite.exists_le k
  refine ⟨fun i => (K : ℤ) * ((n : ℤ) - ((i : ℕ) : ℤ)), ?_, fun i => ?_⟩
  · intro i j hij
    have h : ((i : ℕ) : ℤ) ≤ ((j : ℕ) : ℤ) := by exact_mod_cast hij
    exact mul_le_mul_of_nonneg_left (by omega) (by positivity)
  · set a : Fin n → ℤ := fun i => (K : ℤ) * ((n : ℤ) - ((i : ℕ) : ℤ)) with ha
    have hN : torusPow F n a * u i * (torusPow F n a)⁻¹ ∈ unipotent F n :=
      diagGL_mul_mul_inv_mem_unipotent F n (hu i) _
    have he : ∀ r s, ((torusPow F n a * u i * (torusPow F n a)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) r s =
        (GLnLocal.uniformizer F : F) ^ (a r - a s) * (u i : Matrix (Fin n) (Fin n) F) r s := by
      intro r s
      rw [← torusPow_neg, Units.val_mul, Units.val_mul, coe_torusPow, coe_torusPow, Matrix.mul_diagonal,
        Matrix.diagonal_mul, sub_eq_add_neg, zpow_add₀ (GLnLocal.uniformizer_ne_zero F), Pi.neg_apply]
      ring
    refine (mem_unipotent_inf_integralGL_iff F n).2 ⟨hN, fun r s => ?_⟩
    rcases lt_trichotomy r s with h | h | h
    · rw [he]
      refine (Valuation.mem_integer_iff _ _).2 (hk (i, r, s) _ ?_)
      have h1 : ((r : ℕ) : ℤ) + 1 ≤ ((s : ℕ) : ℤ) := by exact_mod_cast h
      have h2 : (k (i, r, s) : ℤ) ≤ K := by exact_mod_cast hK _
      have h3 : (K : ℤ) * 1 ≤ (K : ℤ) * (((s : ℕ) : ℤ) - ((r : ℕ) : ℤ)) :=
        mul_le_mul_of_nonneg_left (by omega) (by positivity)
      simp only [ha]
      nlinarith
    · subst h
      rw [hN.2 r]
      exact one_mem _
    · rw [hN.1 h]
      exact zero_mem _

theorem UpperTheory.ConvolutionTheory.H.jacq :
    ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ)
      [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] (T : GL (Fin n) F → ℂ), T ∈ locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ → BiI F T →
      (∀ g₀ : GL (Fin n) F, ∫ g in {g | ∃ u ∈ unipotent F n, ∃ y ∈ iwahori F n, g = u * g₀ * y}, T g ∂μ = 0) →
      ∃ a : Fin n → ℤ, Antitone a ∧ groupConv μ (uFn F a) T = 0 := by
  intro F _ _ _ _ n _ _ μ _ T hT hBi h0
  have hIo := isOpen_iwahori F n
  have hIc := isCompact_iwahori F n
  have hfin : μ (iwahori F n : Set (GL (Fin n) F)) ≠ ⊤ := hIc.measure_lt_top.ne
  obtain ⟨S, hS⟩ := exists_cover (iwahori F n) hIo T hT.2
  let ι := {p : S × S // ∃ u ∈ unipotent F n, ∃ y ∈ iwahori F n, (p.2 : GL (Fin n) F) = u * p.1 * y}
  choose u hu y hy huy using fun p : ι => p.2
  obtain ⟨a, ha, hdeep⟩ := exists_deep F n u hu
  refine ⟨a, ha, ?_⟩
  set w := torusPow F n a with hw
  let A : Subgroup (GL (Fin n) F) := unipotent F n ⊓ integralGL F n
  let C : Subgroup (GL (Fin n) F) := A.comap (MulAut.conj w).toMonoidHom
  have hCmem : ∀ m, m ∈ C ↔ w * m * w⁻¹ ∈ A := fun m => by simp [C]
  have hCN : C ≤ unipotent F n := by
    intro m hm
    have h1 := ((hCmem m).1 hm).1
    have h2 := diagGL_mul_mul_inv_mem_unipotent F n h1 (fun i => uniformizerUnit F ^ (-a) i)
    change torusPow F n (-a) * _ * (torusPow F n (-a))⁻¹ ∈ _ at h2
    rw [torusPow_neg, ← hw] at h2
    simpa [mul_assoc] using h2
  have hC : ∀ s ∈ S, ∀ s' ∈ S, (∃ u ∈ unipotent F n, ∃ y ∈ iwahori F n, s' = u * s * y) →
      ∃ u ∈ C, ∃ y ∈ iwahori F n, s' = u * s * y := by
    intro s hs s' hs' h
    let p : ι := ⟨(⟨s, hs⟩, ⟨s', hs'⟩), h⟩
    exact ⟨u p, (hCmem _).2 (hdeep p), y p, hy p, huy p⟩
  have hvan := vanish_of_cover μ (unipotent F n) C (iwahori F n) hCN hIo T S hS hC h0
  have hAc : IsCompact (A : Set (GL (Fin n) F)) :=
    (isCompact_integralGL F n).inter_left (Whittaker.isClosed_unipotent F n)
  haveI : CompactSpace A := isCompact_iff_compactSpace.1 hAc
  have hopen : ∀ t : GL (Fin n) F,
      IsOpen (((iwahori F n).comap (MulAut.conj t⁻¹).toMonoidHom : Subgroup (GL (Fin n) F)) : Set (GL (Fin n) F)) := by
    intro t
    have : (((iwahori F n).comap (MulAut.conj t⁻¹).toMonoidHom : Subgroup (GL (Fin n) F)) : Set (GL (Fin n) F)) =
        (fun x => t⁻¹ * x * t) ⁻¹' (iwahori F n : Set (GL (Fin n) F)) := by
      ext x; simp
    rw [this]
    exact hIo.preimage (by fun_prop)
  funext x
  let Jw : Subgroup (GL (Fin n) F) := (iwahori F n).comap (MulAut.conj w⁻¹).toMonoidHom
  let Jx : Subgroup (GL (Fin n) F) := (iwahori F n).comap (MulAut.conj x⁻¹).toMonoidHom
  have hJw : ∀ b, b ∈ Jw ↔ w⁻¹ * b * w ∈ iwahori F n := fun b => by simp [Jw]
  have hJx : ∀ b, b ∈ Jx ↔ x⁻¹ * b * x ∈ iwahori F n := fun b => by simp [Jx]
  haveI : Finite (A ⧸ Jw.subgroupOf A) :=
    Subgroup.quotient_finite_of_isOpen _ ((hopen w).preimage continuous_subtype_val)
  haveI : Finite (A ⧸ Jx.subgroupOf A) :=
    Subgroup.quotient_finite_of_isOpen _ ((hopen x).preimage continuous_subtype_val)
  letI : Fintype (A ⧸ Jw.subgroupOf A) := Fintype.ofFinite _
  letI : Fintype (A ⧸ Jx.subgroupOf A) := Fintype.ofFinite _
  have e1 := setIntegral_cosets μ A (iwahori F n) Jw w hJw hIo.measurableSet hfin (fun z => T (z⁻¹ * x))
    (fun g i hi => by
      have := (hBi (g⁻¹ * x) i⁻¹ ((iwahori F n).inv_mem hi)).1
      simpa [mul_assoc] using this)
  have e2 := setIntegral_cosets μ A (iwahori F n) Jx x hJx hIo.measurableSet hfin (fun z => T (w⁻¹ * z))
    (fun g i hi => by
      have := (hBi (w⁻¹ * g) i hi).2
      simpa [mul_assoc] using this)
  have hpre : (fun p => w⁻¹ * p) ⁻¹' {p | ∃ u ∈ C, ∃ y ∈ iwahori F n, p = u * (w⁻¹ * x) * y} =
      {g | ∃ v ∈ A, ∃ y ∈ iwahori F n, g = v * x * y} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    constructor
    · rintro ⟨v, hv, z, hz, h⟩
      refine ⟨_, (hCmem v).1 hv, z, hz, ?_⟩
      rw [inv_mul_eq_iff_eq_mul] at h
      rw [h]; group
    · rintro ⟨v, hv, z, hz, rfl⟩
      exact ⟨w⁻¹ * v * w, (hCmem _).2 (by simpa [mul_assoc] using hv), z, hz, by group⟩
  have e3 := (measurePreserving_mul_left μ w⁻¹).setIntegral_preimage_emb (measurableEmbedding_mulLeft w⁻¹) T
    {p | ∃ u ∈ C, ∃ y ∈ iwahori F n, p = u * (w⁻¹ * x) * y}
  rw [hpre, hvan (w⁻¹ * x), e2] at e3
  have hpos : (μ.real (iwahori F n : Set (GL (Fin n) F)) : ℂ) ≠ 0 := by
    have h1 : μ (iwahori F n : Set (GL (Fin n) F)) ≠ 0 := hIo.measure_ne_zero μ ⟨1, one_mem _⟩
    have : μ.real (iwahori F n : Set (GL (Fin n) F)) ≠ 0 := by
      simp [Measure.real, ENNReal.toReal_eq_zero_iff, h1, hfin]
    exact_mod_cast this
  have hsum := (mul_eq_zero.1 e3).resolve_left hpos
  have hfinal := sum_vanish (Jw.subgroupOf A) (Jx.subgroupOf A) (fun m : A => T (w⁻¹ * (m : GL (Fin n) F) * x))
    (fun b hb m => by
      rw [Subgroup.mem_subgroupOf, hJw] at hb
      have := (hBi (w⁻¹ * (m : GL (Fin n) F) * x) _ hb).1
      rw [← this]
      simp [mul_assoc])
    (fun m b hb => by
      rw [Subgroup.mem_subgroupOf, hJx] at hb
      have := (hBi (w⁻¹ * (m : GL (Fin n) F) * x) _ hb).2
      rw [← this]
      simp [mul_assoc])
    (by simpa [mul_assoc] using hsum)
  have hdco : dco F a = {g | ∃ v ∈ A, ∃ y ∈ iwahori F n, g = v * w * y} := by
    ext g
    exact (dcoShape F n a ha).1 g
  have hmeas : MeasurableSet (dco F a) := by
    rw [hdco]
    exact (isOpen_cosets A (iwahori F n) hIo w).measurableSet
  have hc : groupConv μ (uFn F a) T x = ∫ z in dco F a, T (z⁻¹ * x) ∂μ := by
    rw [← integral_indicator hmeas]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    by_cases hz : z ∈ dco F a <;> simp [uFn, hz]
  rw [hc, hdco, e1]
  have hfinal' : ∑ q : A ⧸ Jw.subgroupOf A, T ((((q.out : A) : GL (Fin n) F) * w)⁻¹ * x) = 0 := by
    simpa [mul_assoc] using hfinal
  rw [hfinal', mul_zero]
  rfl
