import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.GradedSeries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfSumSmul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanIsLinesOfGraded
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffEqOfApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AntitoneFiltrationExistsAdaptedLinearIndepSet
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComponentWachLetterBasisFiltration
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachWeierstrassTestAndDensity
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLevelExpansionAtRootOfUnity
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ISupIndepDdRE
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqOfExhaustive
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyClosedOfDictClosed

noncomputable section

namespace GlobalTheory.LevelCompare

open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.DeltaInvariantLattices TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries GlobalTheory.WachTie GlobalTheory.SenLines

section Series

variable {L M M' M'' : Type} [Field L] [AddCommGroup M] [Module L M] [AddCommGroup M'] [Module L M']
  [AddCommGroup M''] [Module L M'']

theorem isLaurent_serMul (f : L⟦X⟧) {u : ℤ → M} (hu : IsLaurent u) : IsLaurent (serMul f u) := by
  have := Laur.isLaurent_co (f • (Laur.mk u hu : Laur L M))
  rwa [Laur.co_smul] at this

theorem serMul_mul (f g : L⟦X⟧) {u : ℤ → M} (hu : IsLaurent u) :
    serMul (f * g) u = serMul f (serMul g u) := by
  have := congrArg Laur.co (mul_smul f g (Laur.mk u hu : Laur L M))
  rwa [Laur.co_smul, Laur.co_smul, Laur.co_smul] at this

theorem add_serMul (f g : L⟦X⟧) {u : ℤ → M} (hu : IsLaurent u) :
    serMul (f + g) u = serMul f u + serMul g u := by
  have := congrArg Laur.co (add_smul f g (Laur.mk u hu : Laur L M))
  rwa [map_add, Laur.co_smul, Laur.co_smul, Laur.co_smul] at this

theorem serMul_add (f : L⟦X⟧) {u w : ℤ → M} (hu : IsLaurent u) (hw : IsLaurent w) :
    serMul f (u + w) = serMul f u + serMul f w := by
  have := congrArg Laur.co (smul_add f (Laur.mk u hu : Laur L M) (Laur.mk w hw))
  rwa [map_add, Laur.co_smul, Laur.co_smul, Laur.co_smul, map_add] at this

theorem isLaurent_add {u w : ℤ → M} (hu : IsLaurent u) (hw : IsLaurent w) : IsLaurent (u + w) := by
  obtain ⟨m, hm⟩ := hu
  obtain ⟨m', hm'⟩ := hw
  exact ⟨min m m', fun k hk => by rw [Pi.add_apply, hm k (by omega), hm' k (by omega), add_zero]⟩

theorem serMul_zero (f : L⟦X⟧) : serMul f (0 : ℤ → M) = 0 := by
  funext k
  simp [serMul]

theorem serMul_C (c : L) (u : ℤ → M) : serMul (C c) u = c • u := by
  funext k
  unfold serMul
  rw [finsum_eq_single _ 0 fun j hj => by rw [coeff_C, if_neg hj, zero_smul]]
  simp

theorem serMul_X_pow (m : ℕ) (u : ℤ → M) (k : ℤ) : serMul ((X : L⟦X⟧) ^ m) u k = u (k - m) := by
  unfold serMul
  rw [finsum_eq_single _ m fun j hj => by rw [coeff_X_pow, if_neg hj, zero_smul]]
  simp

theorem serMul_low (f : L⟦X⟧) {u : ℤ → M} {m : ℤ} (hu : ∀ k < m, u k = 0) :
    serMul f u m = constantCoeff f • u m := by
  have := (Laur.co_smul_low f (Laur.mk u ⟨m, hu⟩ : Laur L M) m hu).2
  rwa [Laur.co_smul] at this

theorem serMul_apply_mem (f : L⟦X⟧) (u : ℤ → M) (k : ℤ) (P : Submodule L M) (h : ∀ j ≤ k, u j ∈ P) :
    serMul f u k ∈ P :=
  finsum_induction (· ∈ P) P.zero_mem (fun _ _ => P.add_mem) fun j => P.smul_mem _ (h _ (by omega))

theorem subset_serSpan {S : Set (ℤ → M)} {u : ℤ → M} (hu : u ∈ S) (hl : IsLaurent u) : u ∈ serSpan L S :=
  Submodule.subset_span ⟨1, u, hu, hl, (serMul_one u).symm⟩

theorem serSpan_le {S : Set (ℤ → M)} {P : Submodule L (ℤ → M)}
    (h : ∀ f : L⟦X⟧, ∀ u ∈ S, IsLaurent u → serMul f u ∈ P) : serSpan L S ≤ P := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, u, hu, hl, rfl⟩
  exact h f u hu hl

theorem serSpan_closed {S : Set (ℤ → M)} {y : ℤ → M} (hy : y ∈ serSpan L S) :
    IsLaurent y ∧ ∀ f : L⟦X⟧, serMul f y ∈ serSpan L S := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨g, u, hu, hl, rfl⟩ := hy
    exact ⟨isLaurent_serMul g hl, fun f => Submodule.subset_span ⟨f * g, u, hu, hl, (serMul_mul f g hl).symm⟩⟩
  | zero => exact ⟨⟨0, fun _ _ => rfl⟩, fun f => by rw [serMul_zero]; exact zero_mem _⟩
  | add y z _ _ hy hz =>
    exact ⟨isLaurent_add hy.1 hz.1, fun f => by rw [serMul_add f hy.1 hz.1]; exact add_mem (hy.2 f) (hz.2 f)⟩
  | smul c y _ hy =>
    rw [← serMul_C]
    exact ⟨isLaurent_serMul _ hy.1, fun f => by rw [← serMul_mul _ _ hy.1]; exact hy.2 _⟩

theorem serSpan_serSpan (S : Set (ℤ → M)) : serSpan L (serSpan L S : Set (ℤ → M)) = serSpan L S :=
  le_antisymm (serSpan_le fun f _ hu _ => (serSpan_closed hu).2 f)
    fun _ hu => subset_serSpan hu (serSpan_closed hu).1

theorem serMul_mem_shiftSer (f : L⟦X⟧) {a : ℤ} {F : Submodule L M} {u : ℤ → M} (hu : u ∈ shiftSer a F) :
    serMul f u ∈ shiftSer a F :=
  ⟨fun k hk => serMul_apply_mem f u k ⊥ fun j hj => hu.1 j (by omega),
    fun k => serMul_apply_mem f u k F fun j _ => hu.2 j⟩

theorem coeff_mem_of_graded {A : ℤ → Submodule L M} (hA : Antitone A) {y : ℤ → M} (hy : y ∈ gradedSer A)
    (k : ℤ) : y k ∈ A (-k) := by
  refine Submodule.iSup_induction _ (motive := fun y => y k ∈ A (-k)) hy ?_ (zero_mem _) fun _ _ => add_mem
  rintro a y ⟨h0, h1⟩
  by_cases hk : k < -a
  · rw [h0 k hk]; exact zero_mem _
  · exact hA (by omega) (h1 k)

theorem single_mem_shiftSer {F : Submodule L M} (k : ℤ) {d : M} (hd : d ∈ F) :
    (Pi.single k d : ℤ → M) ∈ shiftSer (-k) F := by
  refine ⟨fun j hj => Pi.single_eq_of_ne (by omega) _, fun j => ?_⟩
  by_cases h : j = k
  · subst h; simpa using hd
  · simp [Pi.single_eq_of_ne h]

open GlobalTheory.SenLines.Coords in

theorem spanIsLines_of_graded_onto {N : Type} (E : N → ℤ → M) {r : ℕ} (u : Fin r → ℤ) (d : Fin r → M)
    (hd : LinearIndependent L d) (A : ℤ → Submodule L M)
    (hA : ∀ a, A a = Submodule.span L (d '' {k | a ≤ u k})) (h1 : ∀ x k, E x k ∈ A (-k))
    (h2 : ∀ k, ∀ w ∈ A (-k), ∃ x : N, (∀ j < k, E x j ∈ A (-j + 1)) ∧ E x k - w ∈ A (-k + 1)) :
    SpanIsLines E u d L := by
  classical
  have hex : ∀ x (m : ℤ), ∃ c : Fin r → L, (∀ k, u k < -m → c k = 0) ∧ E x m = ∑ k, c k • d k := fun x m =>
    SplitFil.exists_coef u d (-m) _ (hA _ ▸ h1 x m)
  choose c hc hyc using hex
  let e : N → Fin r → L⟦X⟧ := fun x k => PowerSeries.mk fun j => c x ((j : ℤ) - u k) k
  have he : ∀ x, E x = lines u d (e x) := fun x => by
    funext m
    rw [lines_apply, hyc]
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold zc
    split_ifs with h
    · rw [coeff_mk, Int.toNat_of_nonneg h, add_sub_cancel_right]
    · rw [hc x m k (by omega)]
  have hz : ∀ (a : ℤ) (v : Fin r → L), ∑ k, v k • d k ∈ A a → ∀ k, u k < a → v k = 0 := fun a v hv k hk => by
    obtain ⟨c', hc', h⟩ := SplitFil.exists_coef u d a _ (hA _ ▸ hv)
    have := Fintype.linearIndependent_iff.1 hd (fun k => v k - c' k)
      (by simp only [sub_smul, Finset.sum_sub_distrib, h, sub_self]) k
    rw [sub_eq_zero.1 this, hc' k hk]
  choose x hx hx' using fun s => h2 (-u s) (d s) (by
    rw [hA]; exact Submodule.subset_span ⟨s, by simp, rfl⟩)
  let Mx : Matrix (Fin r) (Fin r) L⟦X⟧ := Matrix.of fun k s => e (x s) k
  have hM0 : ∀ k s, constantCoeff (Mx k s) = c (x s) (-u k) k := fun k s => by
    simp [Mx, e, ← coeff_zero_eq_constantCoeff_apply]
  have hlt : ∀ k s, u s < u k → constantCoeff (Mx k s) = 0 := fun k s h => by
    have h3 := hx s (-u k) (by omega)
    rw [hyc] at h3
    rw [hM0]
    exact hz _ _ h3 k (by omega)
  have heq : ∀ k s, u s = u k → constantCoeff (Mx k s) = if k = s then 1 else 0 := fun k s h => by
    have h3 := hx' s
    have h4 : d s = ∑ k, (if k = s then (1 : L) else 0) • d k := by simp
    rw [hyc, h4, ← Finset.sum_sub_distrib] at h3
    simp only [← sub_smul] at h3
    rw [hM0, ← h]
    exact sub_eq_zero.1 (hz _ _ h3 k (by omega))
  have hdet : IsUnit Mx.det := by
    rw [isUnit_iff_constantCoeff, RingHom.map_det, isUnit_iff_ne_zero, Ne, ← Matrix.exists_mulVec_eq_zero_iff]
    rintro ⟨v, hv, h0⟩
    obtain ⟨k, hk, hmax⟩ := Finset.exists_max_image (Finset.univ.filter fun k => v k ≠ 0) u (by
      obtain ⟨k, hk⟩ := Function.ne_iff.1 hv
      exact ⟨k, by simpa using hk⟩)
    have h3 := congrFun h0 k
    rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single k] at h3
    · change constantCoeff (Mx k k) * v k = 0 at h3
      rw [heq k k rfl, if_pos rfl, one_mul] at h3
      exact (Finset.mem_filter.1 hk).2 h3
    · intro s _ hs
      change constantCoeff (Mx k s) * v s = 0
      by_cases hvs : v s = 0
      · rw [hvs, mul_zero]
      rcases (hmax s (by simpa using hvs)).lt_or_eq with h | h
      · rw [hlt k s h, zero_mul]
      · rw [heq k s h, if_neg (Ne.symm hs), zero_mul]
    · simp
  intro y
  constructor
  · rintro ⟨s, z, f, rfl⟩
    refine ⟨∑ j, f j • e (z j), ?_⟩
    change _ = lines u d _
    rw [lines_sum]
    simp only [he, serAct_lines]
  · rintro ⟨c', rfl⟩
    obtain ⟨f, hf⟩ := Matrix.mulVec_surjective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det Mx).2 hdet) c'
    refine ⟨r, x, f, ?_⟩
    change lines u d _ = _
    simp only [he, serAct_lines]
    rw [← lines_sum, ← hf]
    congr 1
    funext k
    simp only [Matrix.mulVec, dotProduct, Mx, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun s _ => by ring

theorem serSpan_eq_graded (A : ℤ → Submodule L M) (hA : Antitone A) (hfd : FiniteDimensional L ↥(⨆ a, A a))
    (hsep : ∀ x, (∀ a, x ∈ A a) → x = 0) (S : Set (ℤ → M)) (h1 : ∀ y ∈ S, ∀ k, y k ∈ A (-k))
    (h2 : ∀ k, ∀ w ∈ A (-k), ∃ y ∈ serSpan L S, (∀ j < k, y j ∈ A (-j + 1)) ∧ y k - w ∈ A (-k + 1)) :
    serSpan L S = gradedSer A := by
  obtain ⟨m, d, u, hd, hsp⟩ := GlobalTheory.filtration_adapted_basis A hA hfd hsep
  have h3 : serSpan L S ≤ Submodule.pi Set.univ fun k => A (-k) := serSpan_le fun f y hy _ k _ =>
    serMul_apply_mem f y k _ fun j hj => hA (by omega) (h1 y hy j)
  have h4 := spanIsLines_of_graded_onto (N := ↥(serSpan L S)) Subtype.val u d hd A hsp
    (fun x k => h3 x.2 k trivial) fun k w hw => by
      obtain ⟨y, hy, h⟩ := h2 k w hw
      exact ⟨⟨y, hy⟩, h⟩
  rw [← serSpan_serSpan, ← Subtype.range_coe (s := (serSpan L S : Set (ℤ → M))),
    SplitFil.gradedSer_eq_range u d A hsp]
  ext y
  refine (SplitFil.mem_serSpan_iff _ (fun x => (serSpan_closed x.2).1) y).trans ((h4 y).trans ?_)
  exact ⟨fun ⟨c, hc⟩ => ⟨c, hc.symm⟩, fun ⟨c, hc⟩ => ⟨c, hc.symm⟩⟩

theorem serSpan_eq_std_iff (D : Submodule L M) [FiniteDimensional L D] (S : Set (ℤ → M))
    (hS : ∀ y ∈ S, IsLaurent y) :
    serSpan L S = shiftSer 0 D ↔ (∀ y ∈ S, y ∈ shiftSer 0 D) ∧ Submodule.span L ((fun y => y 0) '' S) = D := by
  constructor
  · intro h
    have h1 : ∀ y ∈ S, y ∈ shiftSer 0 D := fun y hy => h ▸ subset_serSpan hy (hS y hy)
    refine ⟨h1, le_antisymm (Submodule.span_le.2 ?_) fun d hd => ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact (h1 y hy).2 0
    · have h2 : serSpan L S ≤ (Submodule.span L ((fun y => y 0) '' S)).comap (LinearMap.proj (0 : ℤ)) :=
        serSpan_le fun f y hy _ => by
          change serMul f y 0 ∈ Submodule.span L ((fun y => y 0) '' S)
          rw [serMul_low f (m := 0) (h1 y hy).1]
          exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, hy, rfl⟩)
      simpa using h2 (h.ge (single_mem_shiftSer 0 hd))
  · rintro ⟨h1, h2⟩
    have hle : serSpan L S ≤ shiftSer 0 D := serSpan_le fun f y hy _ => serMul_mem_shiftSer f (h1 y hy)
    let A : ℤ → Submodule L M := fun a => if a ≤ 0 then D else ⊥
    have hAD : ∀ a, A a ≤ D := fun a => by
      simp only [A]; split_ifs
      · exact le_rfl
      · exact bot_le
    have e : serSpan L S = gradedSer A := by
      refine serSpan_eq_graded A (fun a b hab => ?_) (Submodule.finiteDimensional_of_le (iSup_le hAD))
        (fun x hx => by simpa [A] using hx 1) S (fun y hy k => ?_) fun k w hw => ?_
      · by_cases hb : b ≤ 0
        · simp [A, hb, hab.trans hb]
        · simp [A, hb]
      · by_cases hk : -k ≤ 0
        · simpa only [A, if_pos hk] using (h1 y hy).2 k
        · rw [(h1 y hy).1 k (by omega)]; exact zero_mem _
      · rcases lt_trichotomy k 0 with hk | rfl | hk
        · have : w = 0 := by simpa only [A, if_neg (show ¬ -k ≤ 0 by omega), Submodule.mem_bot] using hw
          exact ⟨0, zero_mem _, fun _ _ => zero_mem _, by simp [this]⟩
        · have h3 : D ≤ (serSpan L S).map (LinearMap.proj (0 : ℤ)) := by
            rw [← h2, Submodule.span_le]
            rintro _ ⟨y, hy, rfl⟩
            exact ⟨y, subset_serSpan hy (hS y hy), rfl⟩
          obtain ⟨y, hy, rfl⟩ := h3 (hAD _ hw)
          exact ⟨y, hy, fun j hj => by rw [(hle hy).1 j (by omega)]; exact zero_mem _, by simp⟩
        · refine ⟨0, zero_mem _, fun _ _ => zero_mem _, ?_⟩
          simpa only [A, if_pos (show -k + 1 ≤ 0 by omega), Pi.zero_apply, zero_sub, neg_mem_iff] using hAD _ hw
    refine le_antisymm hle (le_trans ?_ e.ge)
    exact le_iSup_of_le (f := fun a => shiftSer a (A a)) 0 (by simp [A])

theorem exists_div {w : L⟦X⟧} (hw : IsUnit w) (k : ℕ) {z : ℤ → M} (hz : IsLaurent z) :
    ∃ u, IsLaurent u ∧ serMul ((X * w) ^ k) u = z := by
  obtain ⟨w', hw'⟩ := hw.exists_right_inv
  have h1 : IsLaurent fun j => z (j + k) := by
    obtain ⟨m, hm⟩ := hz
    exact ⟨m - k, fun j hj => hm _ (by omega)⟩
  refine ⟨_, isLaurent_serMul (w' ^ k) h1, ?_⟩
  rw [← serMul_mul _ _ h1, ← mul_pow, mul_assoc, hw', mul_one]
  funext j
  simp [serMul_X_pow]

theorem div_mem_iff {w : L⟦X⟧} (hw : IsUnit w) (k : ℕ) {u : ℤ → M} (hu : IsLaurent u) (D : Submodule L M) :
    u ∈ shiftSer 0 D ↔ serMul ((X * w) ^ k) u ∈ shiftSer (-(k : ℤ)) D := by
  obtain ⟨w', hw'⟩ := hw.exists_right_inv
  constructor
  · intro h
    have h1 := serMul_mem_shiftSer (w ^ k) h
    rw [mul_pow, serMul_mul _ _ hu]
    exact ⟨fun j hj => by rw [serMul_X_pow]; exact h1.1 _ (by omega), fun j => by rw [serMul_X_pow]; exact h1.2 _⟩
  · intro h
    have h1 := serMul_mem_shiftSer (w' ^ k) h
    rw [← serMul_mul _ _ hu, ← mul_pow, mul_left_comm, mul_comm w', hw', mul_one] at h1
    refine ⟨fun j hj => ?_, fun j => ?_⟩
    · have := h1.1 (j + k) (by omega)
      rwa [serMul_X_pow, add_sub_cancel_right] at this
    · have := h1.2 (j + k)
      rwa [serMul_X_pow, add_sub_cancel_right] at this

theorem div_coeff (w : L⟦X⟧) (k : ℕ) {u : ℤ → M} (hu : ∀ j < (0 : ℤ), u j = 0) :
    serMul ((X * w) ^ k) u k = constantCoeff w ^ k • u 0 := by
  rw [mul_pow, serMul_mul _ _ ⟨0, hu⟩, serMul_X_pow, sub_self, serMul_low _ hu, map_pow]

def twist (c : L) (g : M →ₗ[L] M') : (ℤ → M) →ₗ[L] (ℤ → M') :=
  LinearMap.pi fun k => (c ^ k • g).comp (LinearMap.proj k)

theorem twist_apply (c : L) (g : M →ₗ[L] M') (u : ℤ → M) (k : ℤ) : twist c g u k = c ^ k • g (u k) := rfl

theorem twist_comp (c c' : L) (g : M' →ₗ[L] M'') (g' : M →ₗ[L] M') :
    (twist c g).comp (twist c' g') = twist (c * c') (g.comp g') := by
  refine LinearMap.ext fun u => funext fun k => ?_
  simp [twist_apply, mul_zpow, mul_smul]

theorem isLaurent_twist (c : L) (g : M →ₗ[L] M') {u : ℤ → M} (hu : IsLaurent u) : IsLaurent (twist c g u) := by
  obtain ⟨m, hm⟩ := hu
  exact ⟨m, fun k hk => by simp [twist_apply, hm k hk]⟩

theorem twist_serMul {c : L} (hc : c ≠ 0) (g : M →ₗ[L] M') (f : L⟦X⟧) {u : ℤ → M} (hu : IsLaurent u) :
    twist c g (serMul f u) = serMul (rescale c f) (twist c g u) := by
  have := congrArg Laur.co (Laur.tw_smul hc g f (Laur.mk u hu : Laur L M))
  rw [Laur.co_smul] at this
  refine Eq.trans (funext fun k => ?_) this
  rw [Laur.co_tw, Laur.co_smul]
  rfl

theorem map_serSpan {c : L} (hc : c ≠ 0) (g : M →ₗ[L] M') (S : Set (ℤ → M)) (hS : ∀ y ∈ S, IsLaurent y) :
    (serSpan L S).map (twist c g) = serSpan L (twist c g '' S) := by
  apply le_antisymm
  · refine Submodule.map_le_iff_le_comap.2 (serSpan_le fun f u hu hl => ?_)
    exact Submodule.subset_span ⟨_, _, ⟨u, hu, rfl⟩, isLaurent_twist c g hl, twist_serMul hc g f hl⟩
  · refine serSpan_le ?_
    rintro f _ ⟨u, hu, rfl⟩ -
    refine ⟨serMul (rescale c⁻¹ f) u, Submodule.subset_span ⟨_, u, hu, hS u hu, rfl⟩, ?_⟩
    rw [twist_serMul hc g _ (hS u hu), rescale_rescale, inv_mul_cancel₀ hc, rescale_one, RingHom.id_apply]

theorem map_shiftSer {c : L} (hc : c ≠ 0) (g : M →ₗ[L] M') (a : ℤ) (F : Submodule L M) :
    (shiftSer a F).map (twist c g) = shiftSer a (F.map g) := by
  apply le_antisymm
  · rintro _ ⟨u, hu, rfl⟩
    exact ⟨fun k hk => by simp [twist_apply, hu.1 k hk],
      fun k => Submodule.smul_mem _ _ (Submodule.mem_map_of_mem (hu.2 k))⟩
  · rintro y ⟨h0, h1⟩
    choose f hf hfy using h1
    refine ⟨fun k => if k < -a then 0 else (c ^ k)⁻¹ • f k, ⟨fun k hk => if_pos hk, fun k => ?_⟩, funext fun k => ?_⟩
    · dsimp only
      split_ifs
      · exact zero_mem _
      · exact F.smul_mem _ (hf k)
    · rw [twist_apply]
      split_ifs with hk
      · rw [map_zero, smul_zero, h0 k hk]
      · rw [map_smul, smul_inv_smul₀ (zpow_ne_zero k hc), hfy]

theorem map_gradedSer {c : L} (hc : c ≠ 0) (g : M →ₗ[L] M') (F : ℤ → Submodule L M) :
    (gradedSer F).map (twist c g) = gradedSer fun a => (F a).map g := by
  simp only [gradedSer, Submodule.map_iSup, map_shiftSer hc]

theorem twist_one_injective {g : M →ₗ[L] M'} (hg : Function.Injective g) : Function.Injective (twist 1 g) :=
  fun u w h => funext fun k => hg (by simpa [twist_apply] using congrFun h k)

end Series

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL)

theorem levN_smul (a : LetA O n) (x : ↥(W.N T)) :
    W.levN T i ζ (a • x) = serMul (W.lev i ζ a) (W.levN T i ζ x) :=
  funext (W.levN_smul T i ζ a x)

theorem levN_letE (x : ↥(W.N T)) : W.levN T i ζ ((letE i : LetA O n) • x) = W.levN T i ζ x := by
  rw [levN_smul, GlobalTheory.NL.LevPt.lev_letE, serMul_one]

theorem toDR_Dlet : toDR (PD := PD) T (Dlet W T i) = ιDi W T i := rfl

theorem toDR_FilLet (τ : K →ₐ[Qp] LL) (a : ℤ) :
    toDR (PD := PD) T (FilLet W T i τ a) = ιDi W T i ⊓ FilC (PD := PD) T τ a := by
  apply le_antisymm
  · rintro _ ⟨x, ⟨h1, h2⟩, rfl⟩
    exact ⟨⟨x, h1, rfl⟩, h2⟩
  · rintro _ ⟨⟨x, h1, rfl⟩, h2⟩
    exact ⟨x, ⟨h1, h2⟩, rfl⟩

theorem finite_ιDi (hT : IsCrys PD T.ρ) : FiniteDimensional LL ↥(ιDi W T i) :=
  haveI := GlobalTheory.NL.CompD.finite_DcrisL PD T.ρ hT (W.emb i)
  Module.Finite.map _ _

theorem low_iff [FiniteDimensional LL ↥(ιDi W T i)] :
    Nlev W T i ζ = shiftSer 0 (toDR (PD := PD) T (Dlet W T i)) ↔
      (∀ (x : ↥(W.N T)) (k : ℤ), W.levN T i ζ ((letE i : LetA O n) • x) k ∈ ιDi W T i ∧
        (k < 0 → W.levN T i ζ x k = 0)) ∧
      Submodule.span LL (Set.range fun x : ↥(W.N T) => W.levN T i ζ ((letE i : LetA O n) • x) 0) =
        ιDi W T i := by
  rw [toDR_Dlet, Nlev, serSpan_eq_std_iff _ _ (by rintro _ ⟨x, rfl⟩; exact W.levN_supp T i ζ x),
    ← Set.range_comp]
  simp only [levN_letE]
  refine and_congr_left' ⟨fun h x k => ⟨(h _ ⟨x, rfl⟩).2 k, (h _ ⟨x, rfl⟩).1 k⟩, ?_⟩
  rintro h _ ⟨x, rfl⟩
  exact ⟨fun k => (h x k).2, fun k => (h x k).1⟩

theorem pull_iff [FiniteDimensional LL ↥(ιDi W T i)] {w : LL⟦X⟧} (hw : IsUnit w) (hQ : W.lev i ζ W.Q = X * w) :
    phiNlev W T i ζ = shiftSer 0 (toDR (PD := PD) T (Dlet W T i)) ↔
      (∀ (x : ↥(W.N T)) (k : ℕ) (hk : W.Q ^ k • W.φD T x ∈ W.N T) (j : ℤ),
        W.levN T i ζ ⟨_, hk⟩ j ∈ ιDi W T i ∧ (j < k → W.levN T i ζ ⟨_, hk⟩ j = 0)) ∧
      Submodule.span LL {w | ∃ (x : ↥(W.N T)) (k : ℕ) (hk : W.Q ^ k • W.φD T x ∈ W.N T),
        w = W.levN T i ζ ⟨_, hk⟩ k} = ιDi W T i := by
  have hw0 : constantCoeff w ≠ 0 := (isUnit_iff_constantCoeff.1 hw).ne_zero
  have hex : ∀ (x : ↥(W.N T)) (k : ℕ) (hk : W.Q ^ k • W.φD T x ∈ W.N T),
      ∃ u ∈ {u | ∃ y ∈ W.N T, IsExpansion W T i ζ (W.φD T y) u},
        serMul ((X * w) ^ k) u = W.levN T i ζ ⟨_, hk⟩ := fun x k hk => by
    obtain ⟨u, hu, h⟩ := exists_div hw k (W.levN_supp T i ζ ⟨_, hk⟩)
    exact ⟨u, ⟨x, x.2, hu, k, hk, by rw [map_pow, hQ, h]⟩, h⟩
  rw [toDR_Dlet, phiNlev, serSpan_eq_std_iff _ _ (by rintro _ ⟨x, -, h⟩; exact h.1)]
  have h1 : (∀ y ∈ {u | ∃ y ∈ W.N T, IsExpansion W T i ζ (W.φD T y) u}, y ∈ shiftSer 0 (ιDi W T i)) ↔
      ∀ (x : ↥(W.N T)) (k : ℕ) (hk : W.Q ^ k • W.φD T x ∈ W.N T) (j : ℤ),
        W.levN T i ζ ⟨_, hk⟩ j ∈ ιDi W T i ∧ (j < k → W.levN T i ζ ⟨_, hk⟩ j = 0) := by
    constructor
    · intro h x k hk j
      obtain ⟨u, hu, e⟩ := hex x k hk
      have := (div_mem_iff hw k hu.choose_spec.2.1 _).1 (h u hu)
      rw [e] at this
      exact ⟨this.2 j, fun hj => this.1 j (by omega)⟩
    · rintro h u ⟨x, hx, hu, k, hk, e⟩
      rw [map_pow, hQ] at e
      rw [div_mem_iff hw k hu, e]
      exact ⟨fun j hj => (h ⟨x, hx⟩ k hk j).2 (by omega), fun j => (h ⟨x, hx⟩ k hk j).1⟩
  rw [← h1]
  refine and_congr_right fun h => Eq.congr_left (le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_))
  · rintro _ ⟨u, ⟨x, hx, hu, k, hk, e⟩, rfl⟩
    rw [map_pow, hQ] at e
    have e2 := congrFun e k
    rw [div_coeff w k (h u ⟨x, hx, hu, k, hk, by rw [map_pow, hQ, e]⟩).1] at e2
    rw [SetLike.mem_coe, ← Submodule.smul_mem_iff _ (pow_ne_zero k hw0), e2]
    exact Submodule.subset_span ⟨⟨x, hx⟩, k, hk, rfl⟩
  · rintro _ ⟨x, k, hk, rfl⟩
    obtain ⟨u, hu, e⟩ := hex x k hk
    rw [← e, div_coeff w k (h u hu).1]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨u, hu, rfl⟩)

theorem approx [IsDomain O] [IsFractionRing O LL]
    (hd : ∀ (f : LL⟦X⟧) (m : ℕ), ∃ (a : LetA O n) (c : LL), c ≠ 0 ∧ X ^ m ∣ c • W.lev i ζ a - f)
    (k : ℤ) {y : ℤ → T.V ⊗[Qp] BdR} (hy : y ∈ Nlev W T i ζ) :
    ∃ (x : ↥(W.N T)) (c : LL), c ≠ 0 ∧ ∀ j ≤ k, c • W.levN T i ζ x j = y j := by
  have hO : ∀ (o : O) (x : ↥(W.N T)),
      W.levN T i ζ (algebraMap O (LetA O n) o • x) = algebraMap O LL o • W.levN T i ζ x := fun o x => by
    rw [levN_smul, AlgHom.commutes, PowerSeries.algebraMap_apply, serMul_C]
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨f, _, ⟨x, rfl⟩, hl, rfl⟩ := hy
    obtain ⟨m, hm⟩ := W.levN_supp T i ζ x
    obtain ⟨a, c, hc, g, hg⟩ := hd f (k - m + 1).toNat
    refine ⟨a • x, c, hc, fun j hj => ?_⟩
    rw [levN_smul, ← Pi.smul_apply, SplitFil.smul_serMul _ _ hl, eq_add_of_sub_eq' hg, add_serMul _ _ hl,
      serMul_mul _ _ hl, Pi.add_apply, serMul_X_pow, add_eq_left]
    exact serMul_apply_mem g _ _ ⊥ fun j' hj' => hm _ (by omega)
  | zero => exact ⟨0, 1, one_ne_zero, fun j _ => by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨x, c, -, h⟩ := hy
    obtain ⟨x', c', -, h'⟩ := hz
    obtain ⟨b, hb'⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) ![c, c']
    obtain ⟨o, ho⟩ : ∃ o, algebraMap O LL o = algebraMap O LL b * c := by
      rw [← Algebra.smul_def]; exact hb' 0
    obtain ⟨o', ho'⟩ : ∃ o, algebraMap O LL o = algebraMap O LL b * c' := by
      rw [← Algebra.smul_def]; exact hb' 1
    have hb : algebraMap O LL b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
    refine ⟨algebraMap O (LetA O n) o • x + algebraMap O (LetA O n) o' • x', (algebraMap O LL b)⁻¹,
      inv_ne_zero hb, fun j hj => ?_⟩
    rw [map_add, hO, hO, Pi.add_apply, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, ho, ho', ← h j hj, ← h' j hj,
      mul_smul, mul_smul, ← smul_add, inv_smul_smul₀ hb]
  | smul e y _ hy =>
    obtain ⟨x, c, hc, h⟩ := hy
    by_cases he : e = 0
    · exact ⟨0, 1, one_ne_zero, fun j _ => by simp [he]⟩
    · exact ⟨x, e * c, mul_ne_zero he hc, fun j hj => by rw [mul_smul, h j hj, Pi.smul_apply]⟩

omit i ζ W in
theorem filC_antitone (τ : K →ₐ[Qp] LL) : Antitone (FilC (PD := PD) T τ) := fun _ _ hab =>
  sup_le_sup_right (inf_le_inf_left _ (GlobalTheory.Per.FilCount.filV_antitone PD hab)) _

theorem fil_iff [IsDomain O] [IsFractionRing O LL] [FiniteDimensional LL ↥(ιDi W T i)] (τ : K →ₐ[Qp] LL)
    (hd : ∀ (f : LL⟦X⟧) (m : ℕ), ∃ (a : LetA O n) (c : LL), c ≠ 0 ∧ X ^ m ∣ c • W.lev i ζ a - f)
    (hinj : ∀ d ∈ ιDi W T i, d ∈ GlobalTheory.NL.CompD.others PD T τ → d = 0)
    (hsurj : ∀ w ∈ DdRE PD T.ρ τ, ∃ d ∈ ιDi W T i, d - w ∈ GlobalTheory.NL.CompD.others PD T τ) :
    (Nlev W T i ζ = gradedSer fun a => toDR (PD := PD) T (FilLet W T i τ a)) ↔
      (∀ (x : ↥(W.N T)) (k : ℤ), W.levN T i ζ ((letE i : LetA O n) • x) k ∈
        ιDi W T i ⊓ FilC (PD := PD) T τ (-k)) ∧
      ∀ (k : ℤ), ∀ w ∈ FildR PD T.ρ τ (-k), ∃ (x : ↥(W.N T)) (c : LL), c ≠ 0 ∧
        (∀ j < k, c • W.levN T i ζ ((letE i : LetA O n) • x) j ∈ FilC (PD := PD) T τ (-j + 1)) ∧
        c • W.levN T i ζ ((letE i : LetA O n) • x) k - w ∈ FilC (PD := PD) T τ (-k + 1) := by
  simp only [levN_letE, toDR_FilLet]
  have hA : Antitone fun a => ιDi W T i ⊓ FilC (PD := PD) T τ a := fun a b hab =>
    inf_le_inf_left _ (filC_antitone T τ hab)
  constructor
  · intro h
    refine ⟨fun x k => coeff_mem_of_graded hA (h ▸ levN_mem_Nlev W T i ζ x) k, fun k w hw => ?_⟩
    obtain ⟨d, hD, hdw⟩ := hsurj w hw.1
    have h1 : d ∈ ιDi W T i ⊓ FilC (PD := PD) T τ (-k) :=
      ⟨hD, by rw [← add_sub_cancel w d]; exact Submodule.add_mem_sup hw hdw⟩
    obtain ⟨x, c, hc, e⟩ := approx W T i ζ hd k
      (h.ge (Submodule.mem_iSup_of_mem (-k) (single_mem_shiftSer k h1)))
    refine ⟨x, c, hc, fun j hj => ?_, ?_⟩
    · rw [e j hj.le, Pi.single_eq_of_ne hj.ne]; exact zero_mem _
    · rw [e k le_rfl, Pi.single_eq_same]; exact Submodule.mem_sup_right hdw
  · rintro ⟨h1, h2⟩
    refine serSpan_eq_graded _ hA (Submodule.finiteDimensional_of_le (iSup_le fun _ => inf_le_left))
      (fun x hx => ?_) _ (by rintro _ ⟨x, rfl⟩; exact h1 x) fun k d hd => ?_
    · obtain ⟨y, hy, z, hz, e⟩ := Submodule.mem_sup.1 (hx 0).2
      have h3 : y = 0 := GlobalTheory.Cmp.JumpDict.filV_sep PD (LL := LL) y fun a => by
        obtain ⟨y', hy', z', hz', e'⟩ := Submodule.mem_sup.1 (hx a).2
        have h4 : y - y' = z' - z := by rw [sub_eq_sub_iff_add_eq_add, e, add_comm, e']
        have h5 := (Submodule.disjoint_def.1 (GlobalTheory.Per.FilLetUnram.iSupIndep_DdRE PD T.ρ τ)) (y - y')
          (sub_mem hy.1 hy'.1) (h4 ▸ sub_mem hz' hz)
        rw [sub_eq_zero.1 h5]
        exact hy'.2
      rw [h3, zero_add] at e
      exact hinj x (hx 0).1 (e ▸ hz)
    · obtain ⟨w, hw, z, hz, e⟩ := Submodule.mem_sup.1 hd.2
      obtain ⟨x, c, -, h3, h4⟩ := h2 k w hw
      refine ⟨c • W.levN T i ζ x, Submodule.smul_mem _ _ (levN_mem_Nlev W T i ζ x),
        fun j hj => ⟨Submodule.smul_mem _ _ (h1 x j).1, h3 j hj⟩,
        sub_mem (Submodule.smul_mem _ _ (h1 x k).1) hd.1, ?_⟩
      rw [← e, ← sub_sub]
      exact sub_mem h4 (Submodule.mem_sup_right hz)

def CoeffAt (τ : K →ₐ[Qp] LL) : Prop :=
  ((∀ (x : ↥(W.N T)) (k : ℕ) (hk : W.Q ^ k • W.φD T x ∈ W.N T) (j : ℤ),
      W.levN T i ζ ⟨_, hk⟩ j ∈ ιDi W T i ∧ (j < k → W.levN T i ζ ⟨_, hk⟩ j = 0)) ∧
    Submodule.span LL {w | ∃ (x : ↥(W.N T)) (k : ℕ) (hk : W.Q ^ k • W.φD T x ∈ W.N T),
      w = W.levN T i ζ ⟨_, hk⟩ k} = ιDi W T i) ∧
  (∀ (x : ↥(W.N T)) (k : ℤ), W.levN T i ζ ((letE i : LetA O n) • x) k ∈
    ιDi W T i ⊓ FilC (PD := PD) T τ (-k)) ∧
  ∀ (k : ℤ), ∀ w ∈ FildR PD T.ρ τ (-k), ∃ (x : ↥(W.N T)) (c : LL), c ≠ 0 ∧
    (∀ j < k, c • W.levN T i ζ ((letE i : LetA O n) • x) j ∈ FilC (PD := PD) T τ (-j + 1)) ∧
    c • W.levN T i ζ ((letE i : LetA O n) • x) k - w ∈ FilC (PD := PD) T τ (-k + 1)

def SpanAt (τ : K →ₐ[Qp] LL) : Prop :=
  phiNlev W T i ζ = shiftSer 0 (toDR (PD := PD) T (Dlet W T i)) ∧
    Nlev W T i ζ = gradedSer fun a => toDR (PD := PD) T (FilLet W T i τ a)

theorem spanAt_iff [CharZero LL] [IsDomain O] [IsFractionRing O LL] (hT : IsCrys PD T.ρ) (τ : K →ₐ[Qp] LL)
    (hζ : IsPrimitiveRoot ζ (PD.p ^ W.s)) (hO : ∃ μ : O, algebraMap O LL μ = ζ)
    (ι : LL →ₐ[Qp] BdR) (hι : ∀ c, ι (τ c) = algebraMap K BdR c)
    (c1 : ∀ (r : ℕ) (d : Fin r → T.V ⊗[Qp] B) (b : Fin r → BdR), (∀ a, d a ∈ DcrisL PD T.ρ (W.emb i)) →
      LinearIndependent LL d →
      ∑ a, mulVR T (b a) (ιV PD (LL := LL) (V := T.V) (d a)) ∈ compKer T ι → ∀ a, b a = 0)
    (c3 : ∀ w ∈ DdRE PD T.ρ τ, ∃ d ∈ DcrisL PD T.ρ (W.emb i),
      ιV PD (LL := LL) (V := T.V) d - w ∈ GlobalTheory.NL.CompD.others PD T τ) :
    SpanAt W T i ζ τ ↔ CoeffAt W T i ζ τ := by
  haveI := finite_ιDi W T i hT
  obtain ⟨w, hw, hQ⟩ := ((GlobalTheory.NL.LevPt.lev_values W i ζ ⟨_, hζ⟩).2.2.1 hζ).1
  refine and_congr (pull_iff W T i ζ hw hQ) (fil_iff W T i ζ τ ?_ ?_ fun w hw => ?_)
  · obtain ⟨μ, rfl⟩ := hO
    exact GlobalTheory.NL.WDiv.lev_dense W i μ hζ
  · rintro _ ⟨d, hd, rfl⟩ ho
    by_cases h0 : d = 0
    · rw [h0, map_zero]
    have h1 := c1 1 (fun _ => d) (fun _ => 1) (fun _ => hd) (linearIndependent_unique_iff.2 h0) (by
      rw [Fin.sum_univ_one, show mulVR T (1 : BdR) (ιV PD (LL := LL) (V := T.V) d) = _ from
        GlobalTheory.NL.CompD.mu_one (LL := LL) _]
      exact GlobalTheory.NL.CompD.others_le_compKer PD T τ ι hι ho) 0
    exact absurd (by rw [← mul_one (PD.ι _), h1, mul_zero]; exact zero_mem _) PD.not_mem_filtration_two
  · obtain ⟨d, hd, e⟩ := c3 w hw
    exact ⟨_, ⟨d, hd, rfl⟩, e⟩

theorem low_guard_iff [CharZero LL] : (∃ j : ℕ, j < W.s ∧ IsPrimitiveRoot ζ (PD.p ^ j)) ↔
    (∃ m : ℕ, ζ ^ (PD.p ^ m) = 1) ∧ constantCoeff (W.lev i ζ W.X) = 0 := by
  have h1 := W.s_pos
  have key : ∀ m, ζ ^ PD.p ^ m = 1 → ∃ j ≤ m, IsPrimitiveRoot ζ (PD.p ^ j) := fun m hm => by
    obtain ⟨j, hj, e⟩ := (Nat.dvd_prime_pow PD.hp).1 (orderOf_dvd_of_pow_eq_one hm)
    exact ⟨j, hj, e ▸ IsPrimitiveRoot.orderOf ζ⟩
  have hX := fun hζ => (GlobalTheory.NL.LevPt.lev_values W i ζ hζ).2.2.2.1
  constructor
  · rintro ⟨j, hj, hζ⟩
    exact ⟨⟨j, hζ.pow_eq_one⟩, (hX ⟨j, hζ⟩).2 ((hζ.pow_eq_one_iff_dvd _).2 (pow_dvd_pow _ (by omega)))⟩
  · rintro ⟨⟨m, hm⟩, h0⟩
    obtain ⟨j, -, hj⟩ := key m hm
    obtain ⟨j', hj', hζ⟩ := key _ ((hX ⟨j, hj⟩).1 h0)
    exact ⟨j', by omega, hζ⟩

omit i ζ in

theorem coeffForm_iff_spans [CharZero LL] (hT : IsCrys PD T.ρ) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop)
    (hPt : ∀ i ζ τ, Pt i ζ τ → (SpanAt W T i ζ τ ↔ CoeffAt W T i ζ τ)) :
    p4 W Pt T ↔ ∀ i ζ, (∀ j : ℕ, j < W.s → IsPrimitiveRoot ζ (PD.p ^ j) →
      Nlev W T i ζ = shiftSer 0 (toDR (PD := PD) T (Dlet W T i))) ∧ ∀ τ, Pt i ζ τ → SpanAt W T i ζ τ := by
  have := fun i => finite_ιDi W T i hT
  constructor
  · rintro ⟨h1, h2⟩ i ζ
    refine ⟨fun j hj hζ => ?_, fun τ hτ => (hPt i ζ τ hτ).2 (h2 i ζ τ hτ)⟩
    obtain ⟨g1, g2⟩ := (low_guard_iff W i ζ).1 ⟨j, hj, hζ⟩
    exact (low_iff W T i ζ).2 (h1 i ζ g1 g2)
  · intro h
    refine ⟨fun i ζ g1 g2 => ?_, fun i ζ τ hτ => (hPt i ζ τ hτ).1 ((h i ζ).2 τ hτ)⟩
    obtain ⟨j, hj, hζ⟩ := (low_guard_iff W i ζ).2 ⟨g1, g2⟩
    exact (low_iff W T i ζ).1 ((h i ζ).1 j hj hζ)

omit W T i ζ [TopologicalSpace G] [TopologicalSpace LL] in
theorem ιV_inj {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] :
    Function.Injective (ιV PD (LL := LL) (V := V)) :=
  Module.Flat.lTensor_preserves_injective_linearMap (M := V) (PD.ι.toLinearMap.restrictScalars Qp) PD.ι_inj

variable {W} {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O] [Algebra Zl Ai]
    {RW : Type} [CommRing RW] [Algebra O RW]
    {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA} {ιdR : Ai →+* BdR} {p1 : Ai} {tS zS : BdR}
    (tie : CmpTie W E ιdR p1 tS zS)

def crisLev : Submodule LL (ℤ → T.V ⊗[Qp] B) := serSpan LL (Set.range (tie.levB T i ζ))

theorem levN_eq_twist (x : ↥(W.N T)) :
    W.levN T i ζ x = twist 1 (ιV PD (LL := LL) (V := T.V)) (tie.levB T i ζ x) :=
  funext fun k => by rw [twist_apply, one_zpow, one_smul, tie.levN_eq]

theorem Nlev_eq_map : Nlev W T i ζ = (crisLev T i ζ tie).map (twist 1 (ιV PD (LL := LL) (V := T.V))) := by
  rw [crisLev, map_serSpan one_ne_zero _ _ (by rintro _ ⟨x, rfl⟩; exact tie.levB_supp T i ζ x), ← Set.range_comp,
    Nlev]
  congr 2
  exact funext (levN_eq_twist T i ζ tie)

theorem levB_smul (a : LetA O n) (x : ↥(W.N T)) :
    tie.levB T i ζ (a • x) = serMul (W.lev i ζ a) (tie.levB T i ζ x) := by
  apply twist_one_injective (ιV_inj (PD := PD) (LL := LL) (V := T.V))
  rw [twist_serMul one_ne_zero _ _ (tie.levB_supp T i ζ x), rescale_one, RingHom.id_apply, ← levN_eq_twist,
    ← levN_eq_twist, levN_smul]

theorem crisLev_step [CharZero LL] (hT : IsCrys PD T.ρ) (hζ : ∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j))
    (hQ : IsUnit (W.lev i ζ W.Q)) :
    crisLev T i ζ tie =
      (crisLev T (i - 1) (ζ ^ PD.p) tie).map (twist (PD.p : LL) (φVB PD (LL := LL) (V := T.V))) := by
  obtain ⟨w, hw⟩ := hQ.exists_left_inv
  have hφ : ∀ (x : ↥(W.N T)) (m : ℕ) (hx : W.Q ^ m • W.φD T (x : W.DD T) ∈ W.N T),
      tie.levB T i ζ ⟨_, hx⟩ = serMul (W.lev i ζ (W.Q ^ m))
        (twist (PD.p : LL) (φVB PD (LL := LL) (V := T.V)) (tie.levB T (i - 1) (ζ ^ PD.p) x)) :=
    fun x m hx => funext (tie.levB_φ T hT i ζ hζ x m hx)
  have hinv : ∀ (m : ℕ) (u : ℤ → T.V ⊗[Qp] B), IsLaurent u →
      serMul (w ^ m) (serMul (W.lev i ζ (W.Q ^ m)) u) = u := fun m u hu => by
    rw [← serMul_mul _ _ hu, map_pow, ← mul_pow, hw, one_pow, serMul_one]
  rw [crisLev, crisLev, map_serSpan (Nat.cast_ne_zero.2 PD.hp.ne_zero) _ _
    (by rintro _ ⟨x, rfl⟩; exact tie.levB_supp T _ _ x)]
  set Λ := serSpan LL (twist (PD.p : LL) (φVB PD (LL := LL) (V := T.V)) ''
    Set.range (tie.levB T (i - 1) (ζ ^ PD.p))) with hΛ
  apply le_antisymm
  · have key : ∀ z ∈ Submodule.span (LetA O n) (W.φD T '' (W.N T : Set (W.DD T))),
        ∃ (m : ℕ) (hz : W.Q ^ m • z ∈ W.N T), tie.levB T i ζ ⟨_, hz⟩ ∈ Λ := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨x, hx, rfl⟩ := hz
        obtain ⟨m, hm⟩ := W.N_φ T x hx
        refine ⟨m, hm, ?_⟩
        rw [hφ ⟨x, hx⟩ m hm]
        exact Submodule.subset_span ⟨_, _, ⟨_, ⟨⟨x, hx⟩, rfl⟩, rfl⟩,
          isLaurent_twist _ _ (tie.levB_supp T _ _ _), rfl⟩
      | zero =>
        refine ⟨0, by simp, ?_⟩
        rw [show (⟨W.Q ^ 0 • (0 : W.DD T), _⟩ : ↥(W.N T)) = 0 from Subtype.ext (smul_zero _), map_zero]
        exact zero_mem _
      | add y z _ _ hy hz =>
        obtain ⟨m, hm, h⟩ := hy
        obtain ⟨m', hm', h'⟩ := hz
        have e : W.Q ^ (m + m') • (y + z) = ((W.Q ^ m' • (⟨_, hm⟩ : ↥(W.N T)) + W.Q ^ m • ⟨_, hm'⟩ : ↥(W.N T)) : W.DD T) := by
          simp only [Submodule.coe_add, Submodule.coe_smul, smul_smul, ← pow_add, smul_add, add_comm m' m]
        refine ⟨m + m', e ▸ Subtype.property _, ?_⟩
        rw [show (⟨W.Q ^ (m + m') • (y + z), _⟩ : ↥(W.N T)) = _ from Subtype.ext e, map_add, levB_smul, levB_smul]
        exact add_mem ((serSpan_closed h).2 _) ((serSpan_closed h').2 _)
      | smul a y _ hy =>
        obtain ⟨m, hm, h⟩ := hy
        have e : W.Q ^ m • (a • y) = ((a • (⟨_, hm⟩ : ↥(W.N T)) : ↥(W.N T)) : W.DD T) := smul_comm _ _ _
        refine ⟨m, e ▸ Subtype.property _, ?_⟩
        rw [show (⟨W.Q ^ m • (a • y), _⟩ : ↥(W.N T)) = _ from Subtype.ext e, levB_smul]
        exact (serSpan_closed h).2 _
    refine serSpan_le ?_
    rintro f _ ⟨y, rfl⟩ hl
    obtain ⟨k, hk⟩ := W.N_φinv T y y.2
    obtain ⟨m, hm, h⟩ := key _ hk
    rw [show (⟨W.Q ^ m • _, hm⟩ : ↥(W.N T)) = W.Q ^ (m + k) • y from Subtype.ext (by
      rw [Submodule.coe_smul, pow_add, mul_smul]; rfl), levB_smul] at h
    have h2 := (serSpan_closed h).2 (w ^ (m + k))
    rw [hinv _ _ hl] at h2
    exact (serSpan_closed h2).2 f
  · refine serSpan_le ?_
    rintro f _ ⟨_, ⟨x, rfl⟩, rfl⟩ hl
    obtain ⟨m, hm⟩ : ∃ m : ℕ, W.Q ^ m • W.φD T x ∈ W.N T := W.N_φ T x x.2
    have h := subset_serSpan (L := LL) (S := Set.range (tie.levB T i ζ)) ⟨⟨_, hm⟩, rfl⟩ (tie.levB_supp T _ _ _)
    rw [hφ x m hm] at h
    have h2 := (serSpan_closed h).2 (w ^ m)
    rw [hinv _ _ hl] at h2
    exact (serSpan_closed h2).2 f

theorem crisLev_iter [CharZero LL] (hT : IsCrys PD T.ρ) (j : ℕ) : ∀ (i : ZMod n) (ζ : LL),
    IsPrimitiveRoot ζ (PD.p ^ (W.s + j)) → crisLev T i ζ tie =
      (crisLev T (i - (j : ZMod n)) (ζ ^ PD.p ^ j) tie).map
        (twist ((PD.p : LL) ^ j) (φVB PD (LL := LL) (V := T.V) ^ j)) := by
  induction j with
  | zero =>
    intro i ζ _
    rw [show twist ((PD.p : LL) ^ 0) (φVB PD (LL := LL) (V := T.V) ^ 0) = LinearMap.id from
      LinearMap.ext fun u => funext fun k => by simp [twist_apply]]
    simp
  | succ j ih =>
    intro i ζ hζ
    have hQ : IsUnit (W.lev i ζ W.Q) := by
      rw [isUnit_iff_constantCoeff, isUnit_iff_ne_zero, Ne,
        (GlobalTheory.NL.LevPt.lev_values W i ζ ⟨_, hζ⟩).2.2.2.2.1]
      intro h
      have := Nat.pow_right_injective PD.hp.two_le (h.unique hζ)
      omega
    rw [crisLev_step T i ζ tie hT ⟨_, hζ⟩ hQ, ih (i - 1) (ζ ^ PD.p)
      (hζ.pow (pow_pos PD.hp.pos _) (by rw [← add_assoc, pow_succ'])), ← Submodule.map_comp, twist_comp,
      ← pow_mul, ← pow_succ', ← pow_succ', sub_sub, add_comm 1, Nat.cast_succ, pow_succ' (φVB PD)]
    rfl

theorem high [CharZero LL] (hT : IsCrys PD T.ρ) (j : ℕ) (hζ : IsPrimitiveRoot ζ (PD.p ^ (W.s + j))) :
    Nlev W T i ζ = serSpan LL (phiSer PD T j ''
      (serSpan LL (Set.range (tie.levB T (i - (j : ZMod n)) (ζ ^ (PD.p ^ j)))) : Set (ℤ → T.V ⊗[Qp] B))) ∧
    ∀ τ : K →ₐ[Qp] LL, (Nlev W T (i - (j : ZMod n)) (ζ ^ (PD.p ^ j)) =
        gradedSer fun a => toDR (PD := PD) T (FilLet W T (i - (j : ZMod n)) τ a)) →
      Nlev W T i ζ = gradedSer fun a => toDR (PD := PD) T
        ((FilLet W T (i - (j : ZMod n)) τ a).map (φVB PD (LL := LL) (V := T.V) ^ j)) := by
  have hp : (PD.p : LL) ^ j ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 PD.hp.ne_zero)
  have h1 := Nlev_eq_map T i ζ tie
  rw [crisLev_iter T tie hT j i ζ hζ, ← Submodule.map_comp, twist_comp, one_mul] at h1
  constructor
  · have e : phiSer PD T j = twist ((PD.p : LL) ^ j)
        ((ιV PD (LL := LL) (V := T.V)).comp (φVB PD (LL := LL) (V := T.V) ^ j)) :=
      funext fun u => funext fun k => map_smul _ _ _
    rw [e, ← map_serSpan hp _ _ (fun y hy => (serSpan_closed hy).1), serSpan_serSpan]
    exact h1
  · intro τ h
    have h2 : crisLev T (i - (j : ZMod n)) (ζ ^ PD.p ^ j) tie = gradedSer (FilLet W T (i - (j : ZMod n)) τ) := by
      apply Submodule.map_injective_of_injective (twist_one_injective (ιV_inj (PD := PD) (LL := LL) (V := T.V)))
      rw [← Nlev_eq_map, h, map_gradedSer one_ne_zero]
      rfl
    rw [h1, h2, map_gradedSer hp]
    simp only [Submodule.map_comp]
    rfl

end Generic

section Local

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (H : LocHW l P) {K : FinExt l} {s : ℕ}
  {LL : FinExt l} (h : Good K s LL) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL))
  (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (ζ : ↥LL.1)

theorem pt_iff (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) :
    GlobalTheory.NL.Pt H h i ζ τ ↔ ∃ τs, H.IsPt h i ζ τs ∧ resEmb h τs = τ := by
  refine exists_congr fun τs => and_congr_right' ⟨fun e => AlgHom.ext fun x => (e x _ rfl).symm, ?_⟩
  rintro rfl x y hxy
  exact congrArg τs (Subtype.ext hxy.symm)

set_option maxHeartbeats 1000000 in

theorem mid_iff (ht : LocTied l P AI) (hT : IsCrys (P.PD K) T.ρ) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1)
    (hpt : GlobalTheory.NL.Pt H h i ζ τ) : SpanAt (H.W K s LL h) T i ζ τ ↔ CoeffAt (H.W K s LL h) T i ζ τ := by
  have hl : l.Prime := Fact.out
  haveI : CharZero ↥LL.1 := algebraRat.charZero _
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) := (P.PD K).finK₀
  haveI : IsFractionRing ↥(OL LL) ↥LL.1 := integralClosure.isFractionRing_of_finite_extension ℚ_[l] ↥LL.1
  obtain ⟨hζ, hτ, ι, hι⟩ := GlobalTheory.NL.Points.pt_props H h i ζ τ hpt
  obtain ⟨c1, -, c3, -⟩ := GlobalTheory.NL.CompD.component_tied ht K LL T (GlobalTheory.NL.Points.card_emb h K.1 h.2.2.1)
    (GlobalTheory.NL.Points.card_emb h (K0 K) (GlobalTheory.NL.Points.unramifiedSubfield_le_cyclotomicExt K s)) hT τ ι hι.2.2 _ hτ
  exact spanAt_iff _ T i ζ hT τ (by rwa [P.PD_p, H.W_s])
    (GlobalTheory.NL.WDiv.root_integral LL (pow_pos hl.pos s) hζ.pow_eq_one) ι hι.2.2 c1 c3

def UpToLevel : Prop :=
  ∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (ζ : ↥LL.1),
    (∀ j : ℕ, j < s → IsPrimitiveRoot ζ (l ^ j) →
      Nlev (H.W K s LL h) T i ζ = shiftSer 0 (toDR (PD := P.PD K) T (Dlet (H.W K s LL h) T i))) ∧
    (∀ τ : ↥(Ks K s) →ₐ[ℚ_[l]] ↥LL.1, H.IsPt h i ζ τ → SpanAt (H.W K s LL h) T i ζ (resEmb h τ))

set_option maxHeartbeats 1000000 in

theorem upToLevel_iff (ht : LocTied l P AI) (hT : IsCrys (P.PD K) T.ρ) :
    p4 (H.W K s LL h) (GlobalTheory.NL.Pt H h) T ↔ UpToLevel H h T := by
  haveI : CharZero ↥LL.1 := algebraRat.charZero _
  refine (coeffForm_iff_spans _ T hT _ fun i ζ τ => mid_iff H h T i ζ ht hT τ).trans ?_
  rw [P.PD_p, H.W_s]
  refine forall₂_congr fun i ζ => and_congr_right' ⟨fun g τ hτ => g _ ((pt_iff H h i ζ _).2 ⟨τ, hτ, rfl⟩), ?_⟩
  intro g τ hτ
  obtain ⟨τs, h1, rfl⟩ := (pt_iff H h i ζ _).1 hτ
  exact g τs h1

set_option maxHeartbeats 1000000 in

theorem latticeAtLevels_iff_upToLevel {F : LocFon l P AI H} (C : LocCmpT l P AI H F) :
    LatticeAtLevels l P AI H F C ↔ ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL)
      (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys (P.PD K) T.ρ → UpToLevel H h T := by
  refine ⟨fun g K s LL h T hT i ζ => ⟨(g K s LL h T hT i ζ).1, (g K s LL h T hT i ζ).2.1⟩,
    fun g K s LL h T hT i ζ => ⟨(g K s LL h T hT i ζ).1, (g K s LL h T hT i ζ).2, fun j _ hζ => ?_⟩⟩
  haveI : CharZero ↥LL.1 := algebraRat.charZero _
  have h1 := high T i ζ (C.C K s LL h).tie hT j (by rwa [P.PD_p, H.W_s])
  have e : ζ ^ (P.PD K).p ^ j = ζ ^ l ^ j := by rw [P.PD_p]
  rw [e] at h1
  exact ⟨h1.1, fun τ hτ => h1.2 _ ((g K s LL h T hT _ _).2 τ hτ).2⟩

end Local

theorem coeffForm_iff_latticeAtLevels (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (C : CmpOf D.loc D.locA HW F) :
    P4 D HW F C ↔ ∀ (l : ℕ) [Fact l.Prime], LatticeAtLevels l (D.loc l) (D.locA l) (HW l) (F l) (C l) := by
  constructor
  · intro g l _
    exact (latticeAtLevels_iff_upToLevel (HW l) (C l)).2 fun K s LL h T hT =>
      (upToLevel_iff (HW l) h T (D.locT l) hT).1 (g l K s LL h T hT)
  · intro g l _ K s LL h T hT
    exact (upToLevel_iff (HW l) h T (D.locT l) hT).2
      ((latticeAtLevels_iff_upToLevel (HW l) (C l)).1 (g l) K s LL h T hT)

end GlobalTheory.LevelCompare
