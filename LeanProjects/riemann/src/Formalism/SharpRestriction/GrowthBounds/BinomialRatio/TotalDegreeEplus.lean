import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.ExtendedStatementOfParts
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.KeptFin

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

section Val

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem toNat_addVal_mul {a b : O} (ha : a ≠ 0) (hb : b ≠ 0) :
    (IsDiscreteValuationRing.addVal O (a * b)).toNat =
      (IsDiscreteValuationRing.addVal O a).toNat + (IsDiscreteValuationRing.addVal O b).toNat := by
  have ha' : IsDiscreteValuationRing.addVal O a ≠ ⊤ := by
    rwa [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
  have hb' : IsDiscreteValuationRing.addVal O b ≠ ⊤ := by
    rwa [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
  rw [AddValuation.map_mul, ENat.toNat_add ha' hb']

private theorem vO_eq_addVal_div_ramE_of_ne_zero (p : ℕ) {z : O} (hz : z ≠ 0) :
    vO p z = ((((IsDiscreteValuationRing.addVal O z).toNat : ℚ) / (ramE p O : ℚ) : ℚ) : WithTop ℚ) := by
  have hz' : algebraMap O (KK O) z ≠ 0 := by
    intro h
    exact hz ((IsFractionRing.to_map_eq_zero_iff).mp h)
  have hspec := Classical.choose_spec (IsLocalization.surj (nonZeroDivisors O) (algebraMap O (KK O) z))
  simp only [vO, vK, ordW, if_neg hz']
  generalize Classical.choose (IsLocalization.surj (nonZeroDivisors O) (algebraMap O (KK O) z)) = ab at hspec ⊢
  rw [← map_mul] at hspec
  have hmul : z * (ab.2 : O) = ab.1 := IsFractionRing.injective O (KK O) hspec
  have hb : (ab.2 : O) ≠ 0 := nonZeroDivisors.coe_ne_zero ab.2
  rw [← hmul, toNat_addVal_mul hz hb]
  simp only [WithTop.map_coe]
  congr 1
  push_cast
  ring

theorem vK_alg_nonneg (p : ℕ) (o : O) : (0 : WithTop ℚ) ≤ vK p (algebraMap O (KK O) o) := by
  by_cases ho : o = 0
  · subst ho
    simp [vK, ordW]
  · have hv : vK p (algebraMap O (KK O) o) = vO p o := rfl
    rw [hv, vO_eq_addVal_div_ramE_of_ne_zero p ho, ← WithTop.coe_zero, WithTop.coe_le_coe]
    positivity

theorem smul_mem_bbSpec (p : ℕ) {σ : Type*} (sp : ℕ) (F : MvPolynomial σ (KK O)) (s : O)
    (h : ∀ μ ∈ F.support, IsLocalization.IsInteger O (s • F.coeff μ)) : s • F ∈ bbSpec O p σ sp := by
  classical
  have hF : s • F = ∑ μ ∈ F.support, monomial μ (s • F.coeff μ) := by
    conv_lhs => rw [← F.support_sum_monomial_coeff, Finset.smul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [MvPolynomial.smul_monomial]
  rw [hF]
  refine Submodule.sum_mem _ fun μ hμ => Submodule.subset_span ?_
  obtain ⟨o, ho⟩ := h μ hμ
  refine ⟨μ, s • F.coeff μ, ?_, rfl⟩
  rw [← ho]
  refine add_nonneg (vK_alg_nonneg p o) ?_
  have : (0 : ℚ) ≤ (padicValNat p (expFact μ) : ℚ) / 2 + (padicValNat p sp : ℚ) / 2 := by positivity
  exact_mod_cast this

end Val

theorem finrank_pi_supp {K β V : Type*} [Field K] [AddCommGroup V] [Module K V] (M : β → Submodule K V)
    (F : Finset β) (h : ∀ b, b ∉ F → M b = ⊥) (hf : ∀ b ∈ F, Module.Finite K (M b)) :
    Module.finrank K (Submodule.pi Set.univ M) = ∑ b ∈ F, Module.finrank K (M b) := by
  classical
  have hz : ∀ (x : V) b, b ∉ F → x ∈ M b → x = 0 := fun x b hb hx => by
    rw [h b hb] at hx
    exact (Submodule.mem_bot K).mp hx
  let e : (Submodule.pi Set.univ M) ≃ₗ[K] ((b : F) → M b) :=
    { toFun := fun x b => ⟨(x : β → V) b, x.2 b (Set.mem_univ _)⟩
      invFun := fun y => ⟨fun b => if hb : b ∈ F then (y ⟨b, hb⟩ : V) else 0, fun b _ => by
        by_cases hb : b ∈ F
        · simp only [dif_pos hb]
          exact (y ⟨b, hb⟩).2
        · simp only [dif_neg hb]
          exact Submodule.zero_mem _⟩
      map_add' := fun x y => by
        funext b
        rfl
      map_smul' := fun c x => by
        funext b
        rfl
      left_inv := fun x => by
        apply Subtype.ext
        funext b
        by_cases hb : b ∈ F
        · simp [hb]
        · simp only [dif_neg hb]
          exact (hz _ b hb (x.2 b (Set.mem_univ _))).symm
      right_inv := fun y => by
        funext b
        apply Subtype.ext
        simp [b.2] }
  haveI : ∀ b : F, Module.Finite K (M b) := fun b => hf b b.2
  rw [e.finrank_eq, Module.finrank_pi_fintype]
  exact Finset.sum_coe_sort F (fun b => Module.finrank K (M b))

theorem finrank_lattice {O E : Type} [CommRing O] [IsDomain O] [AddCommGroup E] [Module O E] [Module (KK O) E]
    [IsScalarTower O (KK O) E] (V : Submodule (KK O) E) (L : Submodule O E) (hLV : ∀ x ∈ L, x ∈ V)
    (habs : ∀ v ∈ V, ∃ s : O, s ≠ 0 ∧ s • v ∈ L) : Module.finrank O L = Module.finrank (KK O) V := by
  let f : L →ₗ[O] V :=
    { toFun := fun x => ⟨x.1, hLV x.1 x.2⟩
      map_add' := fun x y => rfl
      map_smul' := fun c x => rfl }
  have : IsLocalizedModule (nonZeroDivisors O) f :=
    { map_units := by
        intro x
        rw [Module.End.isUnit_iff]
        have hx : algebraMap O (KK O) (x : O) ≠ 0 := by
          intro h
          exact nonZeroDivisors.coe_ne_zero x ((map_eq_zero_iff _ (IsFractionRing.injective O (KK O))).1 h)
        constructor
        · intro v v' hv
          have hv' : (x : O) • v = (x : O) • v' := hv
          rw [← algebraMap_smul (KK O) (x : O) v, ← algebraMap_smul (KK O) (x : O) v'] at hv'
          exact smul_right_injective V hx hv'
        · intro v
          refine ⟨(algebraMap O (KK O) (x : O))⁻¹ • v, ?_⟩
          show (x : O) • ((algebraMap O (KK O) (x : O))⁻¹ • v) = v
          rw [← algebraMap_smul (KK O) (x : O), smul_smul, mul_inv_cancel₀ hx, one_smul]
      surj := by
        intro y
        obtain ⟨s, hs, hm⟩ := habs y.1 y.2
        exact ⟨(⟨s • y.1, hm⟩, ⟨s, mem_nonZeroDivisors_of_ne_zero hs⟩), rfl⟩
      exists_of_eq := by
        intro x₁ x₂ h
        refine ⟨1, ?_⟩
        have : x₁ = x₂ := Subtype.ext (congrArg (fun z : V => z.1) h)
        rw [this] }
  rw [← IsLocalizedModule.finrank_eq (nonZeroDivisors O) f le_rfl]
  exact (IsFractionRing.finrank_right_eq O (KK O) V).symm

section Deg

variable {O : Type} [CommRing O] [IsDomain O] {N r : ℕ}

theorem totalDegree_Ehat (D : BlockData N) (i : Fin D.T.t) : (D.Ehat O (r := r) i).totalDegree ≤ 2 := by
  unfold BlockData.Ehat
  refine (totalDegree_add _ _).trans (max_le ?_ ?_)
  · refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_X, totalDegree_X]
  · refine totalDegree_finsetSum_le fun c _ => ?_
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_X, totalDegree_X]

theorem totalDegree_Eplus (D : BlockData N) : (D.Eplus O (r := r)).totalDegree ≤ 2 := by
  unfold BlockData.Eplus
  refine (totalDegree_add _ _).trans (max_le ?_ ?_)
  · refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_X, totalDegree_X]
  · refine totalDegree_finsetSum_le fun c _ => ?_
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_X, totalDegree_X]

theorem totalDegree_chPol {K : Type*} [CommSemiring K] (LL : ChainLetters N) (y : MvPolynomial (Fin N × Fin r) K)
    (hy : y ∈ chPol K r LL) : y.totalDegree ≤ ∑ a, LL.deg a := by
  unfold chPol Pol at hy
  rw [MvPolynomial.mem_restrictSupport_iff] at hy
  unfold totalDegree
  refine Finset.sup_le fun m hm => ?_
  have h := hy (Finset.mem_coe.2 hm)
  have h' : ∀ i, multideg m i = LL.deg i := h
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_prod_type]
  exact le_of_eq (Finset.sum_congr rfl fun i _ => h' i)

theorem totalDegree_xi (t b : ℕ) (g : MvPolynomial (BVar N r t) (KK O)) (hg : g ∈ XiPolZ O N r t b) :
    g.totalDegree ≤ b := by
  classical
  have hg1 : g ∈ MvPolynomial.restrictSupport (KK O)
      {m | (∀ v ∈ m.support, ∃ c, v = xiVar N r t c) ∧ ∑ c, m (xiVar N r t c) = b} := hg.1
  rw [MvPolynomial.mem_restrictSupport_iff] at hg1
  unfold totalDegree
  refine Finset.sup_le fun m hm => ?_
  obtain ⟨h1, h2⟩ := hg1 (Finset.mem_coe.2 hm)
  rw [← h2]
  have hinj : Function.Injective (xiVar N r t) := by
    intro c c' h
    unfold xiVar at h
    exact (Prod.mk.inj (Sum.inl.inj h)).2
  rw [← Finset.sum_image (f := fun v => m v) (s := Finset.univ) (g := xiVar N r t) (fun _ _ _ _ h => hinj h)]
  unfold Finsupp.sum
  refine Finset.sum_le_sum_of_subset ?_
  intro v hv
  obtain ⟨c, rfl⟩ := h1 v hv
  exact Finset.mem_image_of_mem _ (Finset.mem_univ c)

def degBound (D : BlockData N) : ℕ :=
  (∑ i, D.LL.deg (D.letterAt (D.T.pos i)) * 2) + D.B * 2 + (∑ i, D.T.z i) + D.zPlus + (∑ a, D.LL.deg a) + D.B

theorem gens_totalDegree [NeZero r] (D : BlockData N) (j : Fin D.T.t → ℕ) (jp : ℕ) (hl : D.LevelOK j jp)
    (x : MvPolynomial (BVar N r D.T.t) (KK O)) (hx : x ∈ D.gens O (r := r) j jp) : x.totalDegree ≤ degBound D := by
  obtain ⟨y, hy, g, hg, rfl⟩ := hx
  have hy1 : y.totalDegree ≤ ∑ a, D.LL.deg a := by
    have h1 : y ∈ chPol (KK O) r (D.lettersAt j jp) := hy.1.1
    refine (totalDegree_chPol _ y h1).trans (Finset.sum_le_sum fun a _ => ?_)
    show D.LL.deg a - _ - _ ≤ D.LL.deg a
    omega
  have hg1 : g.totalDegree ≤ D.B := (totalDegree_xi _ _ g hg).trans (Nat.sub_le _ _)
  have hE : (∏ i, D.Ehat O (r := r) i ^ j i).totalDegree ≤ ∑ i, D.LL.deg (D.letterAt (D.T.pos i)) * 2 := by
    refine (totalDegree_finsetProd _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (totalDegree_pow _ _).trans ?_
    exact Nat.mul_le_mul (hl.1 i).1 (totalDegree_Ehat D i)
  have hP : (D.Eplus O (r := r) ^ jp).totalDegree ≤ D.B * 2 := by
    refine (totalDegree_pow _ _).trans ?_
    exact Nat.mul_le_mul (le_trans hl.2 (min_le_right _ _)) (totalDegree_Eplus D)
  have hZ : (∏ i, (X (scalZ N r D.T.t (Fin.castSucc i)) : MvPolynomial (BVar N r D.T.t) (KK O)) ^ D.T.z i).totalDegree ≤
      ∑ i, D.T.z i := by
    refine (totalDegree_finsetProd _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (totalDegree_pow _ _).trans ?_
    rw [totalDegree_X, mul_one]
  have hX : ((X (scalZ N r D.T.t (Fin.last D.T.t)) : MvPolynomial (BVar N r D.T.t) (KK O)) ^ D.zPlus).totalDegree ≤
      D.zPlus := by
    refine (totalDegree_pow _ _).trans ?_
    rw [totalDegree_X, mul_one]
  have hr : (rename (chainEmb N r D.T.t) y).totalDegree ≤ ∑ a, D.LL.deg a := (totalDegree_rename_le _ _).trans hy1
  unfold degBound
  refine (totalDegree_mul _ _).trans (Nat.add_le_add ?_ hg1)
  refine (totalDegree_mul _ _).trans (Nat.add_le_add ?_ hr)
  refine (totalDegree_mul _ _).trans (Nat.add_le_add ?_ hX)
  refine (totalDegree_mul _ _).trans (Nat.add_le_add ?_ hZ)
  exact (totalDegree_mul _ _).trans (Nat.add_le_add hE hP)

theorem spanSSZ_le [NeZero r] (D : BlockData N) :
    Submodule.span (KK O) ((D.SSZ O (r := r) : Submodule O (MvPolynomial (BVar N r D.T.t) (KK O))) :
      Set (MvPolynomial (BVar N r D.T.t) (KK O))) ≤ restrictTotalDegree (BVar N r D.T.t) (KK O) (degBound D) := by
  rw [Submodule.span_le]
  have h : D.SSZ O (r := r) ≤ (restrictTotalDegree (BVar N r D.T.t) (KK O) (degBound D)).restrictScalars O := by
    unfold BlockData.SSZ
    rw [Submodule.span_le]
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨j, jp, hl, hx⟩ := hx
    show x ∈ restrictTotalDegree (BVar N r D.T.t) (KK O) (degBound D)
    rw [mem_restrictTotalDegree]
    exact gens_totalDegree D j jp hl x hx
  exact h

theorem spanSSZ_finite [NeZero r] (D : BlockData N) :
    Module.Finite (KK O) (Submodule.span (KK O)
      ((D.SSZ O (r := r) : Submodule O (MvPolynomial (BVar N r D.T.t) (KK O))) :
        Set (MvPolynomial (BVar N r D.T.t) (KK O)))) :=
  Submodule.finiteDimensional_of_le (spanSSZ_le D)

end Deg

section Seg

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {s : ℕ}

def Vb (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p r : ℕ) [NeZero r] (S : SegData s)
    (aTop : Fin s → ℕ) (aPlus : ℕ) (m : ℝ) (b : SegBlock s r) :
    Submodule (KK O) (MvPolynomial (BVar (2 * s + 1) r S.t) (KK O)) :=
  let L : Submodule O (MvPolynomial (BVar (2 * s + 1) r S.t) (KK O)) :=
    (blockData p S aTop aPlus m b).SSZ O (r := r)
  Submodule.span (KK O) (L : Set (MvPolynomial (BVar (2 * s + 1) r S.t) (KK O)))

open Classical in

theorem finrank_segLat (p r : ℕ) [NeZero r] (S : SegData s) (aTop : Fin s → ℕ) (aPlus : ℕ) (m : ℝ)
    (hfin : {b : SegBlock s r | Kept p r S aTop b}.Finite) :
    Module.finrank O (segLat O p r S aTop aPlus m) = segRank O p r S aTop aPlus m := by
  set F : Finset (SegBlock s r) := hfin.toFinset with hF
  have hmemF : ∀ b, b ∈ F ↔ Kept p r S aTop b := fun b => by rw [hF, Set.Finite.mem_toFinset]; rfl
  let M : SegBlock s r → Submodule (KK O) (MvPolynomial (BVar (2 * s + 1) r S.t) (KK O)) :=
    fun b => if Kept p r S aTop b then Vb O p r S aTop aPlus m b else ⊥
  have hM1 : ∀ b, Kept p r S aTop b → M b = Vb O p r S aTop aPlus m b := fun b hb => if_pos hb
  have hM0 : ∀ b, ¬ Kept p r S aTop b → M b = ⊥ := fun b hb => if_neg hb
  have h1 : Module.finrank O (segLat O p r S aTop aPlus m) =
      Module.finrank (KK O) (Submodule.pi Set.univ M) := by
    apply finrank_lattice
    · intro x hx b _
      have hxb := hx b trivial
      show x b ∈ M b
      by_cases hb : Kept p r S aTop b
      · rw [hM1 b hb]
        simp only [if_pos hb] at hxb
        exact hxb.1
      · rw [hM0 b hb]
        simp only [if_neg hb] at hxb
        exact hxb
    · intro v hv
      obtain ⟨sd, hsd⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors O)
        (F.biUnion fun b => (v b).support.image fun μ => (v b).coeff μ)
      refine ⟨sd, nonZeroDivisors.coe_ne_zero sd, ?_⟩
      intro b _
      have hvb : v b ∈ M b := hv b trivial
      show ((sd : O) • v) b ∈ (if Kept p r S aTop b then blockLat O p r S aTop aPlus m b else ⊥ : Submodule O _)
      by_cases hb : Kept p r S aTop b
      · rw [hM1 b hb] at hvb
        rw [if_pos hb]
        refine ⟨?_, ?_⟩
        · exact ((Vb O p r S aTop aPlus m b).restrictScalars O).smul_mem (sd : O) hvb
        · refine smul_mem_bbSpec p _ (v b) (sd : O) fun μ hμ => hsd _ ?_
          rw [Finset.mem_biUnion]
          exact ⟨b, (hmemF b).2 hb, Finset.mem_image_of_mem _ hμ⟩
      · rw [hM0 b hb, Submodule.mem_bot] at hvb
        rw [if_neg hb, Submodule.mem_bot]
        show (sd : O) • v b = 0
        rw [hvb, smul_zero]
  rw [h1, finrank_pi_supp M F (fun b hb => hM0 b (fun h => hb ((hmemF b).2 h)))
    (fun b hb => by
      rw [hM1 b ((hmemF b).1 hb)]
      exact spanSSZ_finite (O := O) (r := r) (blockData p S aTop aPlus m b))]
  unfold segRank
  rw [finsum_eq_sum_of_support_subset (s := F)]
  · refine Finset.sum_congr rfl fun b hb => ?_
    rw [hM1 b ((hmemF b).1 hb), if_pos ((hmemF b).1 hb)]
    rfl
  · intro b hb
    rw [Function.mem_support] at hb
    rw [Finset.mem_coe, hmemF]
    by_contra h
    exact hb (if_neg h)

end Seg

theorem rkAt_all (C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc : ℝ) : RkAt C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc := by
  intro X _ W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ jO w _ _ _ j
  exact finrank_segLat _ _ _ _ _ _ (kf_kept_finite _ _ _ _)

theorem restRk : RestRk := by
  unfold RestRk
  exact TransportedAlt.mono (fun C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc _ => rkAt_all C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc) thr_std

end Formalism.MainNotions.ColumnSystems.Pf
