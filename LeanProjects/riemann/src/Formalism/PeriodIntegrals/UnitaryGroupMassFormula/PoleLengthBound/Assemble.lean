import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.LeOrdASmulOsK
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.FiltOk

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PI.PoleLengthCount

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

theorem colIdx_sum {N : ℕ} (col : Fin N) (α : Fin (WeightFamilies.dimY D j) → ℕ) :
    ((colIdx D j col α).sum fun _ n => n) = ∑ i, α i := by
  classical
  unfold colIdx
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
  simp [Fintype.sum_prod_type, Fin.sum_univ_succ]

theorem mon_sum {d k : ℕ} (α : Mon d k) : ∑ i, α.1 i = k := Finset.Nat.mem_antidiagonalTuple.1 α.2

theorem colIdx_mon {N : ℕ} (col : Fin N) {k : ℕ} (α : Mon (WeightFamilies.dimY D j) k) :
    ((colIdx D j col α.1).sum fun _ n => n) = k := by
  rw [colIdx_sum, mon_sum]

theorem exists_coef {G : GlobalFamilyData X ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)} (Q : LocalPointData G la) (hC : Q.InCurve)
    (u : Fin G.N → OsK X la G.w)
    (hs : ∑ col, algebraMap (Op X la G.N) (OsK X la G.w) (Tv X la G.N ((0 : Fin (WeightFamilies.dimY D j + 1)), col)) * u col = 1)
    (ho : ∀ (ζ : PtsG G la) col, 0 ≤ ord (unifO X la G.N) ζ (u col)) (k : ℕ) :
    ∃ a : Fin G.N → OsK X la G.w, (∀ col (ζ : PtsG G la), 0 ≤ ord (unifO X la G.N) ζ (a col)) ∧
      ∑ col, a col * u col ^ k = 1 := by
  have : ∀ ζ : PtsG G la, IsDVRAt ζ := isDVRAt_of_curve Q hC
  have hU := isUnif_of_curve Q hC
  have hu : ∀ col, u col ∈ As (Op X la G.N) (OsK X la G.w) := fun col => (mem_As_iff hU _).2 fun ζ => ho ζ col
  let u' : Fin G.N → ↥(As (Op X la G.N) (OsK X la G.w)) := fun col => ⟨u col, hu col⟩
  have h1 : Ideal.span (Set.range u') = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have e : (1 : ↥(As (Op X la G.N) (OsK X la G.w))) =
        ∑ col, algebraMap (Op X la G.N) ↥(As (Op X la G.N) (OsK X la G.w))
          (Tv X la G.N ((0 : Fin (WeightFamilies.dimY D j + 1)), col)) * u' col := by
      apply Subtype.ext
      simp only [u', OneMemClass.coe_one, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul,
        Subalgebra.coe_algebraMap]
      exact hs.symm
    rw [e]
    exact Ideal.sum_mem _ fun col _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨col, rfl⟩)
  have h2 := Ideal.span_pow_eq_top _ h1 k
  rw [← Set.range_comp] at h2
  have h3 : (1 : ↥(As (Op X la G.N) (OsK X la G.w))) ∈
      Ideal.span (Set.range ((fun x => x ^ k) ∘ u')) := by rw [h2]; trivial
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 h3
  refine ⟨fun col => (c col : OsK X la G.w), fun col ζ => ord_nonneg ζ hU (c col).2, ?_⟩
  have := congrArg Subtype.val hc
  simpa [u'] using this

section

variable (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO))

def psiRaw (a : Fin G.N → OsK X la G.w) (k : ℕ) (x : ↥(HK X la G.w wF)) : Vk G la k :=
  fun α => ∑ col, a col • rD G la (colIdx D j col α.1) x

theorem psiRaw_add (a : Fin G.N → OsK X la G.w) (k : ℕ) (x y : ↥(HK X la G.w wF)) :
    psiRaw G la a k (x + y) = psiRaw G la a k x + psiRaw G la a k y := by
  funext α
  simp only [psiRaw, Pi.add_apply, rD_add, smul_add, Finset.sum_add_distrib]

theorem psiRaw_smul (a : Fin G.N → OsK X la G.w) (k : ℕ) (r : Op X la G.N) (x : ↥(HK X la G.w wF))
    (hx : x ∈ Jid X la G.w ^ k • (⊤ : Submodule ↥(Frac0 X la G.w) ↥(HK X la G.w wF))) :
    psiRaw G la a k (algebraMap (Op X la G.N) (Kp X la G.N) r • x) = r • psiRaw G la a k x := by
  funext α
  simp only [psiRaw, Pi.smul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun col _ => ?_
  rw [restricted_derivative_linear G la k _ r x hx (le_of_eq (colIdx_mon col α))]
  exact smul_comm _ _ _

theorem psiRaw_congr (a : Fin G.N → OsK X la G.w) {k T : ℕ} (hk : k < a0 D j T) {x x' : ↥(HK X la G.w wF)}
    (h : toWK X la G.w wF (a0 D j T) x = toWK X la G.w wF (a0 D j T) x') : psiRaw G la a k x = psiRaw G la a k x' := by
  have hd : x - x' ∈ Jid X la G.w ^ a0 D j T • (⊤ : Submodule ↥(Frac0 X la G.w) ↥(HK X la G.w wF)) := by
    rw [← toWK_eq_zero_iff, map_sub, h, sub_self]
  have hd' : x - x' ∈ Jid X la G.w ^ (k + 1) • (⊤ : Submodule ↥(Frac0 X la G.w) ↥(HK X la G.w wF)) :=
    Submodule.smul_mono_left (Ideal.pow_le_pow_right hk) hd
  funext α
  unfold psiRaw
  refine Finset.sum_congr rfl fun col _ => ?_
  have e : x = x' + (x - x') := by abel
  rw [e, rD_add, vanishingOnQuadric G la (k + 1) _ _ hd' (by rw [colIdx_mon col α]; omega), add_zero]

theorem exists_of_mem_Fk {T k : ℕ} {z : WK X la G.w wF (a0 D j T)} (hz : z ∈ Fk G la T k) :
    ∃ x : ↥(HK X la G.w wF), x ∈ Jid X la G.w ^ k • (⊤ : Submodule ↥(Frac0 X la G.w) ↥(HK X la G.w wF)) ∧
      toWK X la G.w wF (a0 D j T) x = z := by
  unfold Fk at hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, hx, rfl⟩ := hz
    exact ⟨x, hx, rfl⟩
  | zero => exact ⟨0, Submodule.zero_mem _, map_zero _⟩
  | add z1 z2 _ _ h1 h2 =>
    obtain ⟨x1, hx1, rfl⟩ := h1
    obtain ⟨x2, hx2, rfl⟩ := h2
    exact ⟨x1 + x2, Submodule.add_mem _ hx1 hx2, map_add _ _ _⟩
  | smul r z _ h =>
    obtain ⟨x, hx, rfl⟩ := h
    refine ⟨algebraMap (Op X la G.N) (Kp X la G.N) r • x, Submodule.smul_of_tower_mem _ _ hx, ?_⟩
    rw [LinearMap.map_smul_of_tower]
    rfl

def pre {T k : ℕ} {z : WK X la G.w wF (a0 D j T)} (hz : z ∈ Fk G la T k) : ↥(HK X la G.w wF) :=
  Classical.choose (exists_of_mem_Fk G la hz)

theorem pre_mem {T k : ℕ} {z : WK X la G.w wF (a0 D j T)} (hz : z ∈ Fk G la T k) :
    pre G la hz ∈ Jid X la G.w ^ k • (⊤ : Submodule ↥(Frac0 X la G.w) ↥(HK X la G.w wF)) :=
  (Classical.choose_spec (exists_of_mem_Fk G la hz)).1

theorem pre_eq {T k : ℕ} {z : WK X la G.w wF (a0 D j T)} (hz : z ∈ Fk G la T k) :
    toWK X la G.w wF (a0 D j T) (pre G la hz) = z :=
  (Classical.choose_spec (exists_of_mem_Fk G la hz)).2

def psiL (a : Fin G.N → OsK X la G.w) (T k : ℕ) (hk : k < a0 D j T) :
    ↥(Fk G la T k) →ₗ[Op X la G.N] Vk G la k where
  toFun z := psiRaw G la a k (pre G la z.2)
  map_add' z1 z2 := by
    rw [← psiRaw_add]
    apply psiRaw_congr G la a hk
    rw [map_add, pre_eq, pre_eq, pre_eq]
    rfl
  map_smul' r z := by
    rw [RingHom.id_apply, ← psiRaw_smul G la a k r _ (pre_mem G la z.2)]
    apply psiRaw_congr G la a hk
    rw [LinearMap.map_smul_of_tower, pre_eq, pre_eq]
    rfl

def psiF (a : ℕ → Fin G.N → OsK X la G.w) (T : ℕ) : ∀ k, ↥(Fk G la T k) →ₗ[Op X la G.N] Vk G la k :=
  fun k => if hk : k < a0 D j T then psiL G la (a k) T k hk else 0

theorem psiF_lt (a : ℕ → Fin G.N → OsK X la G.w) {T k : ℕ} (hk : k < a0 D j T) (z : ↥(Fk G la T k))
    (x : ↥(HK X la G.w wF)) (hx : toWK X la G.w wF (a0 D j T) x = z) :
    psiF G la a T k z = psiRaw G la (a k) k x := by
  unfold psiF
  rw [dif_pos hk]
  exact psiRaw_congr G la (a k) hk ((pre_eq G la z.2).trans hx.symm)

theorem psiF_ge (a : ℕ → Fin G.N → OsK X la G.w) {T k : ℕ} (hk : ¬ k < a0 D j T) (z : ↥(Fk G la T k)) :
    psiF G la a T k z = 0 := by
  unfold psiF
  rw [dif_neg hk]
  rfl

theorem taylorRead (hE5 : ColDeriv G la) (u : Fin G.N → OsK X la G.w) (hu : uSpec G la u) (k : ℕ)
    (a : Fin G.N → OsK X la G.w) (ha : ∑ col, a col * u col ^ k = 1) (cf : Mon (WeightFamilies.dimY D j) k → ↥(HK X la G.w wF))
    (r : ↥(HK X la G.w wF))
    (hr : r ∈ Jid X la G.w ^ (k + 1) • (⊤ : Submodule ↥(Frac0 X la G.w) ↥(HK X la G.w wF)))
    (α' : Mon (WeightFamilies.dimY D j) k) :
    psiRaw G la a k (∑ α, yPow X la G.w α.1 • cf α + r) α' = toA0K X la G.w wF (cf α') := by
  have h1 : ∀ col, rD G la (colIdx D j col α'.1) (∑ α, yPow X la G.w α.1 • cf α + r) =
      u col ^ k • toA0K X la G.w wF (cf α') := by
    intro col
    rw [rD_add, rD_sum, vanishingOnQuadric G la (k + 1) _ r hr (by rw [colIdx_mon col α']; omega), add_zero]
    simp only [hE5 u hu k _ α' col]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
  unfold psiRaw
  simp only [h1, smul_smul]
  rw [← Finset.sum_smul, ha, one_smul]

end

theorem ordV_shift (t : WithTop ℤ) (c m : ℤ) (h : ((-m : ℤ) : WithTop ℤ) ≤ t + (c : WithTop ℤ)) :
    0 ≤ t + ((c + m : ℤ) : WithTop ℤ) := by
  induction t using WithTop.recTopCoe with
  | top => simp
  | coe n =>
    rw [← WithTop.coe_add] at h ⊢
    have := WithTop.coe_le_coe.1 h
    exact_mod_cast (show (0 : ℤ) ≤ n + (c + m) by omega)

theorem pole_length_assemble : Assemble := by
  intro D B P j X ka wL wF G la Q S CRm T e c hOk hw hL _ _ hE3 hE4 hE5 _ hE7
  have hC := hOk.2.1
  have : ∀ ζ : PtsG G la, IsDVRAt ζ := isDVRAt_of_curve Q hC
  have hU := isUnif_of_curve Q hC
  obtain ⟨u, hu, hs, ho⟩ := hE3
  choose a ha1 ha2 using exists_coef Q hC u hs ho
  refine ⟨psiF G la a T, ?_, ?_, ?_⟩
  · intro k z hz0
    by_cases hk : k < a0 D j T
    · obtain ⟨x, hx, hxz⟩ := exists_of_mem_Fk G la z.2
      rw [psiF_lt G la a hk z x hxz] at hz0
      obtain ⟨cf, r, hr, hxe⟩ := hE4 k x hx
      have hc : ∀ α, toA0K X la G.w wF (cf α) = 0 := fun α => by
        rw [← taylorRead G la hE5 u hu k (a k) (ha2 k) cf r hr α, ← hxe, hz0]
        rfl
      have hx' : x ∈ Jid X la G.w ^ (k + 1) • (⊤ : Submodule ↥(Frac0 X la G.w) ↥(HK X la G.w wF)) := by
        rw [hxe]
        refine Submodule.add_mem _ (Submodule.sum_mem _ fun α _ => ?_) hr
        have h1 : yPow X la G.w α.1 ∈ Jid X la G.w ^ k := by
          have := prod_sfr_mem X la G.w α.1
          rwa [mon_sum] at this
        have h2 : cf α ∈ Jid X la G.w • (⊤ : Submodule ↥(Frac0 X la G.w) ↥(HK X la G.w wF)) :=
          (reduction_eq_zero_iff_mem_ideal_smul X la G.w wF _).1 (hc α)
        rw [pow_succ, Submodule.mul_smul]
        exact Submodule.smul_mem_smul h1 h2
      rw [← hxz]
      exact Submodule.subset_span ⟨x, hx', rfl⟩
    · have h0 : (z : WK X la G.w wF (a0 D j T)) ∈ Fk G la T (a0 D j T) :=
        (image_filtration_decreasing G la T).1 (by omega) z.2
      rw [(image_filtration_decreasing G la T).2.2, Submodule.mem_bot] at h0
      rw [h0]
      exact Submodule.zero_mem _
  · intro k hk
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨x, -, hxz⟩ := exists_of_mem_Fk G la z.2
    have hg := good_of_mem_AAp hC (m := Q.mm S T e) (by omega) hz x hxz
    rw [psiF_lt G la a hk z x hxz]
    unfold Pk
    rw [Submodule.mem_pi]
    intro α _
    rw [mem_ballO_iff _ hU hC.2.2]
    intro ζ
    have key : ((-(Q.mm S T e ζ : ℤ) : ℤ) : WithTop ℤ) ≤ Q.ordA ζ (psiRaw G la (a k) k x α) :=
      le_ordA_sum Q hC ζ _ _ _ fun col _ => le_ordA_smul_OsK Q hC ζ _ (ha1 k col ζ) _ _
        (hg _ (by rw [colIdx_mon col α]; omega) ζ)
    exact ordV_shift _ _ _ key
  · intro k hk b hb
    unfold Qk at hb
    rw [Submodule.mem_pi] at hb
    choose x hx1 hx2 using fun α => hL (b α) (hb α (Set.mem_univ _))
    set Xs : ↥(HK X la G.w wF) := ∑ α, yPow X la G.w α.1 • x α with hXs
    have hX : Xs ∈ Jid X la G.w ^ k • (⊤ : Submodule ↥(Frac0 X la G.w) ↥(HK X la G.w wF)) := by
      refine Submodule.sum_mem _ fun α _ => Submodule.smul_mem_smul ?_ Submodule.mem_top
      have := prod_sfr_mem X la G.w α.1
      rwa [mon_sum] at this
    have hXA : toWK X la G.w wF (a0 D j T) Xs ∈ Q.AA T := by
      rw [hXs, map_sum]
      exact Submodule.sum_mem _ fun α _ => hE7 (x α) α.1 (hx2 α)
    refine ⟨⟨_, Submodule.subset_span ⟨Xs, hX, rfl⟩⟩, hXA, ?_⟩
    rw [psiF_lt G la a hk _ Xs rfl]
    funext α'
    have := taylorRead G la hE5 u hu k (a k) (ha2 k) x 0 (Submodule.zero_mem _) α'
    rw [add_zero] at this
    rw [this, hx1]

end PI.PoleLengthCount
