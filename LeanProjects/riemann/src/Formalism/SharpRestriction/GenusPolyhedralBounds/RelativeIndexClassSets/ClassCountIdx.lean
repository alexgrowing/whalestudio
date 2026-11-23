import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGap
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ClassCountStmt

noncomputable section

namespace Formalism.MainNotions.Gaps.CC.Idx

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.UG.P Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.Gaps.LG
open scoped TensorProduct

section Defs

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

def adG (σ : E →ₐ[F] E) (J : Matrix n n E)
    (W : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL n (E ⊗[F] v.adicCompletion F))) :
    Subgroup (GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :=
  UPts σ J (FiniteAdeleRing (𝓞 F) F) ⊓ ⨅ v : HeightOneSpectrum (𝓞 F), (W v).comap (bc (prV (E := E) v))

def rowStab (A : Type) [CommRing A] (i0 : n) : Subgroup (GL n A) where
  carrier := {x | ∀ j, (x : Matrix n n A) i0 j = (1 : Matrix n n A) i0 j}
  one_mem' := fun _ => rfl
  mul_mem' := by
    intro a b ha hb j
    simp only [Set.mem_ofPred_eq] at ha hb
    rw [Units.val_mul, Matrix.mul_apply, Finset.sum_congr rfl (fun l _ => by rw [ha l])]
    simp [Matrix.one_apply, hb j]
  inv_mem' := by
    intro a ha j
    simp only [Set.mem_ofPred_eq] at ha
    have h : ((a : Matrix n n A) * ((a⁻¹ : GL n A) : Matrix n n A)) i0 j = (1 : Matrix n n A) i0 j := by
      rw [Units.mul_inv]
    rw [Matrix.mul_apply, Finset.sum_congr rfl (fun l _ => by rw [ha l])] at h
    simpa [Matrix.one_apply] using h

def congU (σ : E →ₐ[F] E) (J : Matrix n n E) (v : HeightOneSpectrum (𝓞 F)) (s : SplitCore σ v)
    (Hk : Subgroup (GL n (v.adicCompletionIntegers F ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)))) :
    Subgroup (GL n (E ⊗[F] v.adicCompletion F)) :=
  UPts σ J (v.adicCompletion F) ⊓
    (congPre (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))
      (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) Hk).comap
        (bc ((RingHom.fst _ _).comp s.φ.toRingHom))

end Defs

section SA

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

theorem inverse_in_adic_integers (c : 𝓞 F) (w : HeightOneSpectrum (𝓞 F)) [Decidable (Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) c) < 1)] :
    (if Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) c) < 1 then (0 : w.adicCompletion F)
      else (algebraMap (𝓞 F) (w.adicCompletion F) c)⁻¹) ∈ w.adicCompletionIntegers F := by
  split_ifs with h
  · exact zero_mem _
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀]
    have h1 : Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) c) = 1 :=
      le_antisymm ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (levelaf_int_mem_v w c)) (not_lt.1 h)
    rw [h1, inv_one]

open Classical in

def a_u (c : 𝓞 F) : FiniteAdeleRing (𝓞 F) F :=
  ⟨fun w => if Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) c) < 1 then (0 : w.adicCompletion F)
      else (algebraMap (𝓞 F) (w.adicCompletion F) c)⁻¹, Filter.Eventually.of_forall fun w => inverse_in_adic_integers c w⟩

theorem a_u_mem (c : 𝓞 F) : a_u c ∈ intAd F := fun w => inverse_in_adic_integers c w

theorem mem_S_of_loc (x : E ⊗[F] FiniteAdeleRing (𝓞 F) F) (h : ∀ w, prV (E := E) w x ∈ intV E w) :
    x ∈ tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F) := by
  classical
  obtain ⟨c, hc0, hc⟩ := loc_int_bound F E
  have hfin := levelaf_finite_places c hc0
  have key : x = ∑ v ∈ hfin.toFinset, afsplitIE v (prV (E := E) v x) +
      ((1 : E) ⊗ₜ[F] a_u c) * (levelafC E c * x) := by
    rw [← sub_eq_zero]
    apply afsplit_inj
    intro w
    rw [map_sub, map_add, map_sum, map_mul, map_mul, sub_eq_zero, afsplit_prV_tmul]
    unfold levelafC
    rw [afsplit_prV_tmul]
    by_cases hw : w ∈ hfin.toFinset
    · rw [Finset.sum_eq_single w (fun v _ hv => afsplit_prV_IE_ne v w (Ne.symm hv) _)
        (fun h => absurd hw h), afsplit_prV_IE]
      have h0 : (a_u c) w = 0 := if_pos (by simpa using hw)
      rw [h0, TensorProduct.tmul_zero, zero_mul, add_zero]
    · rw [Finset.sum_eq_zero (fun v hv => afsplit_prV_IE_ne v w (by rintro rfl; exact hw hv) _), zero_add]
      have h0 : (a_u c) w = (algebraMap (𝓞 F) (w.adicCompletion F) c)⁻¹ := if_neg (by simpa using hw)
      rw [h0, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
        show (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) c) w = algebraMap (𝓞 F) (w.adicCompletion F) c from rfl,
        inv_mul_cancel₀ (levelaf_algebraMap_ne_zero w c hc0), ← Algebra.TensorProduct.one_def, one_mul]
  rw [key]
  refine add_mem (Subring.sum_mem _ fun v _ => afsplit_IE_int v _ (h v)) (mul_mem ?_ (hc x h))
  exact Subring.subset_closure (Or.inr ⟨⟨a_u c, a_u_mem c⟩, rfl⟩)

theorem levelAf_eq_adG (σ : E →ₐ[F] E) (J : Matrix n n E) :
    levelAf σ J = adG σ J (fun v => levelV σ J v) := by
  ext g
  unfold adG
  rw [Subgroup.mem_inf, Subgroup.mem_iInf]
  constructor
  · intro hg
    have hU : g ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) := (Subgroup.mem_inf.mp hg).1
    obtain ⟨h1, h2⟩ := (afsplit_stab_iff _ _).mp (Subgroup.mem_inf.mp hg).2
    refine ⟨hU, fun v => Subgroup.mem_comap.2 ⟨afsplit_bc_mem σ J v g hU,
      (afsplit_stab_iff _ _).mpr ⟨fun i j => afsplit_prV_int v _ (h1 i j), fun i j => ?_⟩⟩⟩
    rw [← map_inv]
    exact afsplit_prV_int v _ (h2 i j)
  · rintro ⟨hU, hv⟩
    refine ⟨hU, (afsplit_stab_iff _ _).mpr
      ⟨fun i j => mem_S_of_loc _ fun w => ?_, fun i j => mem_S_of_loc _ fun w => ?_⟩⟩
    · exact ((afsplit_stab_iff _ _).mp (Subgroup.mem_inf.mp (Subgroup.mem_comap.1 (hv w))).2).1 i j
    · have h3 := ((afsplit_stab_iff _ _).mp (Subgroup.mem_inf.mp (Subgroup.mem_comap.1 (hv w))).2).2 i j
      rw [← map_inv] at h3
      exact h3

end SA

section SP

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

theorem p_mem_adG (σ : E →ₐ[F] E) (J : Matrix n n E)
    (W : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL n (E ⊗[F] v.adicCompletion F)))
    (x : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
    x ∈ adG σ J W ↔ x ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) ∧ ∀ v, bc (prV (E := E) v) x ∈ W v :=
  Subgroup.mem_inf.trans (and_congr Iff.rfl (Subgroup.mem_iInf.trans (forall_congr' fun _ => Subgroup.mem_comap)))

theorem p_mono (σ : E →ₐ[F] E) (J : Matrix n n E)
    (W W' : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL n (E ⊗[F] v.adicCompletion F)))
    (hle : ∀ v, W v ≤ W' v) : adG σ J W ≤ adG σ J W' := by
  intro x hx
  rw [p_mem_adG] at hx ⊢
  exact ⟨hx.1, fun v => hle v (hx.2 v)⟩

theorem p_lift (σ : E →ₐ[F] E) (J : Matrix n n E) (v : HeightOneSpectrum (𝓞 F))
    (h : GL n (E ⊗[F] v.adicCompletion F)) (hh : h ∈ UPts σ J (v.adicCompletion F)) :
    ∃ x ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F), bc (prV (E := E) v) x = h ∧
      ∀ w, w ≠ v → bc (prV (E := E) w) x = 1 := by
  refine ⟨afsplitU v h 1, afsplitU_mem v σ J h 1 hh (one_mem _), afsplit_right1 v h 1, fun w hw => ?_⟩
  apply Units.ext
  rw [afsplit_coe_bc_prV, afsplitU_coe, afsplitC_prV_ne v w hw, Units.val_one, Units.val_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem p_step (σ : E →ₐ[F] E) (J : Matrix n n E)
    (W W' : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL n (E ⊗[F] v.adicCompletion F)))
    (a : HeightOneSpectrum (𝓞 F)) (hU : W' a ≤ UPts σ J (a.adicCompletion F))
    (hW : ∀ v, v ≠ a → W v = W' v) (hle : W a ≤ W' a) :
    (adG σ J W).relIndex (adG σ J W') = (W a).relIndex (W' a) := by
  have h1 : adG σ J W = adG σ J W' ⊓ (W a).comap (bc (prV (E := E) a)) := by
    ext x
    rw [Subgroup.mem_inf, p_mem_adG, p_mem_adG, Subgroup.mem_comap]
    constructor
    · rintro ⟨hx, h⟩
      refine ⟨⟨hx, fun v => ?_⟩, h a⟩
      by_cases hv : v = a
      · subst hv; exact hle (h v)
      · rw [← hW v hv]; exact h v
    · rintro ⟨⟨hx, h⟩, ha⟩
      refine ⟨hx, fun v => ?_⟩
      by_cases hv : v = a
      · subst hv; exact ha
      · rw [hW v hv]; exact h v
  have h2 : (adG σ J W').map (bc (prV (E := E) a)) = W' a := by
    ext y
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ((p_mem_adG σ J W' x).1 hx).2 a
    · intro hy
      obtain ⟨x, hx, hxa, hxw⟩ := p_lift σ J a y (hU hy)
      refine ⟨x, (p_mem_adG σ J W' x).2 ⟨hx, fun v => ?_⟩, hxa⟩
      by_cases hv : v = a
      · subst hv; rw [hxa]; exact hy
      · rw [hxw v hv]; exact one_mem _
  rw [h1, Subgroup.inf_relIndex_left, Subgroup.relIndex_comap, h2]

open Classical in
theorem p_ind (σ : E →ₐ[F] E) (J : Matrix n n E)
    (W W' : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL n (E ⊗[F] v.adicCompletion F)))
    (hle : ∀ v, W v ≤ W' v) (hU : ∀ v, W' v ≤ UPts σ J (v.adicCompletion F))
    (s : Finset (HeightOneSpectrum (𝓞 F))) :
    (adG σ J W).relIndex (adG σ J (fun v => if v ∈ s then W' v else W v)) =
      ∏ v ∈ s, (W v).relIndex (W' v) := by
  induction s using Finset.induction_on with
  | empty =>
    have : (fun v : HeightOneSpectrum (𝓞 F) => if v ∈ (∅ : Finset (HeightOneSpectrum (𝓞 F))) then W' v else W v) = W := by
      funext v; simp
    rw [this, Subgroup.relIndex_self, Finset.prod_empty]
  | insert a s ha ih =>
    have hm1 : adG σ J W ≤ adG σ J (fun v => if v ∈ s then W' v else W v) := by
      refine p_mono σ J _ _ fun v => ?_
      show W v ≤ if v ∈ s then W' v else W v
      split_ifs
      · exact hle v
      · exact le_rfl
    have hm2 : adG σ J (fun v => if v ∈ s then W' v else W v) ≤
        adG σ J (fun v => if v ∈ insert a s then W' v else W v) := by
      refine p_mono σ J _ _ fun v => ?_
      show (if v ∈ s then W' v else W v) ≤ if v ∈ insert a s then W' v else W v
      by_cases hv : v ∈ s
      · rw [if_pos hv, if_pos (Finset.mem_insert_of_mem hv)]
      · rw [if_neg hv]
        split_ifs
        · exact hle v
        · exact le_rfl
    have hs := p_step σ J (fun v => if v ∈ s then W' v else W v)
      (fun v => if v ∈ insert a s then W' v else W v) a
      (by show (if a ∈ insert a s then W' a else W a) ≤ _
          rw [if_pos (Finset.mem_insert_self a s)]; exact hU a)
      (fun v hv => by
        show (if v ∈ s then W' v else W v) = if v ∈ insert a s then W' v else W v
        by_cases hvs : v ∈ s
        · rw [if_pos hvs, if_pos (Finset.mem_insert_of_mem hvs)]
        · rw [if_neg hvs, if_neg (fun h => (Finset.mem_insert.1 h).elim hv hvs)])
      (by show (if a ∈ s then W' a else W a) ≤ if a ∈ insert a s then W' a else W a
          rw [if_neg ha, if_pos (Finset.mem_insert_self a s)]; exact hle a)
    have hs' : (adG σ J (fun v => if v ∈ s then W' v else W v)).relIndex
        (adG σ J (fun v => if v ∈ insert a s then W' v else W v)) = (W a).relIndex (W' a) := by
      rw [hs]
      show (if a ∈ s then W' a else W a).relIndex (if a ∈ insert a s then W' a else W a) = _
      rw [if_neg ha, if_pos (Finset.mem_insert_self a s)]
    rw [← Subgroup.relIndex_mul_relIndex _ _ _ hm1 hm2, ih, hs', Finset.prod_insert ha, mul_comm]

theorem adG_relIndex (σ : E →ₐ[F] E) (J : Matrix n n E)
    (W W' : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL n (E ⊗[F] v.adicCompletion F)))
    (hle : ∀ v, W v ≤ W' v) (hU : ∀ v, W' v ≤ UPts σ J (v.adicCompletion F))
    (B : Finset (HeightOneSpectrum (𝓞 F))) (hB : ∀ v, v ∉ B → W v = W' v) :
    (adG σ J W).relIndex (adG σ J W') = ∏ v ∈ B, (W v).relIndex (W' v) := by
  classical
  have h := p_ind σ J W W' hle hU B
  have h' : (fun v : HeightOneSpectrum (𝓞 F) => if v ∈ B then W' v else W v) = W' := by
    funext v
    by_cases hv : v ∈ B
    · rw [if_pos hv]
    · rw [if_neg hv, hB v hv]
  rwa [h'] at h

end SP

section SL

theorem l_red_surj {O : Type} [CommRing O] [IsLocalRing O] {n : Type} [Fintype n] [DecidableEq n] :
    Function.Surjective (redGL (n := n) (IsLocalRing.maximalIdeal O)) := by
  intro y
  choose M hM using fun i j => Ideal.Quotient.mk_surjective (I := IsLocalRing.maximalIdeal O)
    ((y : Matrix n n (O ⧸ IsLocalRing.maximalIdeal O)) i j)
  have hmap : (Matrix.of M).map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)) =
      (y : Matrix n n (O ⧸ IsLocalRing.maximalIdeal O)) := by
    ext i j
    exact hM i j
  have hdet : IsUnit (Matrix.of M).det := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro hmem
    have h0 : Ideal.Quotient.mk (IsLocalRing.maximalIdeal O) (Matrix.of M).det = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 hmem
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hmap] at h0
    have hu : IsUnit (y : Matrix n n (O ⧸ IsLocalRing.maximalIdeal O)).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit
    rw [h0] at hu
    exact not_isUnit_zero hu
  refine ⟨Matrix.nonsingInvUnit (Matrix.of M) hdet, ?_⟩
  apply Units.ext
  exact hmap

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

theorem l_surj (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (s : SplitCore σ v)
    (h : GL n (v.adicCompletion F)) :
    ∃ g ∈ UPts σ (1 : Matrix n n E) (v.adicCompletion F), bc ((RingHom.fst _ _).comp s.φ.toRingHom) g = h := by
  obtain ⟨e, he⟩ := split_group_points F E n σ (1 : Matrix n n E) (v.adicCompletion F) s.φ s.sig
  obtain ⟨g', hg', hg'h⟩ := split_surjective (1 : Matrix n n (v.adicCompletion F)) (by simp) h
  have hJ : (1 : Matrix n n E).map ((s.φ : E ⊗[F] v.adicCompletion F →+* _).comp
      (inclE (F := F) (v.adicCompletion F))) = splitJ (1 : Matrix n n (v.adicCompletion F)) := by
    ext i j
    · by_cases hij : i = j
      · subst hij; simp [splitJ]
      · simp [splitJ, hij]
    · by_cases hij : i = j
      · subst hij; simp [splitJ]
      · simp [splitJ, hij, Ne.symm hij]
  rw [← hJ] at hg'
  refine ⟨(e.symm ⟨g', hg'⟩ : GL n _), (e.symm ⟨g', hg'⟩).2, ?_⟩
  have h1 : bc (s.φ : E ⊗[F] v.adicCompletion F →+* _) (e.symm ⟨g', hg'⟩ : GL n _) = g' := by
    rw [← he, e.apply_symm_apply]
  rw [← hg'h]
  exact congrArg (bc (RingHom.fst _ _)) h1

theorem l_levelV_iff (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (s : SplitCore σ v)
    (g : GL n (E ⊗[F] v.adicCompletion F)) (hg : g ∈ UPts σ (1 : Matrix n n E) (v.adicCompletion F)) :
    g ∈ levelV σ (1 : Matrix n n E) v ↔
      bc ((RingHom.fst _ _).comp s.φ.toRingHom) g ∈ GLint n (v.adicCompletionIntegers F).toSubring := by
  have hu : ∃ u ∈ GLint n (v.adicCompletionIntegers F).toSubring,
      (u : Matrix n n (v.adicCompletion F)) =
        fun i j => (s.φ (inclE (F := F) (v.adicCompletion F) ((1 : Matrix n n E) i j))).1 := by
    refine ⟨1, one_mem _, ?_⟩
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  exact level_subgroup_split F E n σ 1 v s.φ s.sig s.int hu g hg

theorem l_congPre_le (v : HeightOneSpectrum (𝓞 F))
    (Hk : Subgroup (GL n (v.adicCompletionIntegers F ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)))) :
    congPre (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))
      (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) Hk ≤
        GLint n (v.adicCompletionIntegers F).toSubring := by
  rintro x ⟨g, -, rfl⟩
  exact ⟨g, rfl⟩

theorem l_map_levelV (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (s : SplitCore σ v) :
    (levelV σ (1 : Matrix n n E) v).map (bc ((RingHom.fst _ _).comp s.φ.toRingHom)) =
      GLint n (v.adicCompletionIntegers F).toSubring := by
  ext h
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (l_levelV_iff σ v s g (Subgroup.mem_inf.1 hg).1).1 hg
  · intro hh
    obtain ⟨g, hg, rfl⟩ := l_surj σ v s h
    exact ⟨g, (l_levelV_iff σ v s g hg).2 hh, rfl⟩

theorem congU_le (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (s : SplitCore σ v)
    (Hk : Subgroup (GL n (v.adicCompletionIntegers F ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)))) :
    congU σ (1 : Matrix n n E) v s Hk ≤ levelV σ 1 v := by
  intro g hg
  obtain ⟨hU, hC⟩ := Subgroup.mem_inf.1 hg
  exact (l_levelV_iff σ v s g hU).2 (l_congPre_le v Hk hC)

theorem l_congPre_relIndex (v : HeightOneSpectrum (𝓞 F))
    (Hk : Subgroup (GL n (v.adicCompletionIntegers F ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)))) :
    (congPre (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))
      (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) Hk).relIndex
        (GLint n (v.adicCompletionIntegers F).toSubring) = Hk.index := by
  have hG : GLint n (v.adicCompletionIntegers F).toSubring =
      (⊤ : Subgroup (GL n (v.adicCompletionIntegers F))).map
        (bc (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))) := by
    rw [← MonoidHom.range_eq_map]
    rfl
  have hinj : Function.Injective (bc (n := n) (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))) :=
    bc_injective _ (FaithfulSMul.algebraMap_injective _ _)
  rw [hG]
  unfold congPre
  rw [Subgroup.relIndex_map_map_of_injective _ _ hinj, Subgroup.relIndex_top_right,
    Subgroup.index_comap_of_surjective _ l_red_surj]

theorem congU_relIndex (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (s : SplitCore σ v)
    (Hk : Subgroup (GL n (v.adicCompletionIntegers F ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)))) :
    (congU σ (1 : Matrix n n E) v s Hk).relIndex (levelV σ 1 v) = Hk.index := by
  have h1 : congU σ (1 : Matrix n n E) v s Hk ⊓ levelV σ 1 v =
      (congPre (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))
        (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) Hk).comap
          (bc ((RingHom.fst _ _).comp s.φ.toRingHom)) ⊓ levelV σ 1 v := by
    ext g
    simp only [Subgroup.mem_inf, congU]
    constructor
    · rintro ⟨⟨_, h⟩, hK⟩
      exact ⟨h, hK⟩
    · rintro ⟨h, hK⟩
      exact ⟨⟨(Subgroup.mem_inf.1 hK).1, h⟩, hK⟩
  rw [← Subgroup.inf_relIndex_right, h1, Subgroup.inf_relIndex_right, Subgroup.relIndex_comap,
    l_map_levelV, l_congPre_relIndex]

end SL

section K

theorem k_bc_surj {A B : Type} [CommRing A] [CommRing B] {n : Type} [Fintype n] [DecidableEq n] (e : A ≃+* B) :
    Function.Surjective (bc (n := n) (e : A →+* B)) := by
  intro y
  refine ⟨bc (e.symm : B →+* A) y, ?_⟩
  apply Units.ext
  ext i j
  show e (e.symm ((y : Matrix n n B) i j)) = _
  exact e.apply_symm_apply _

def k_uni (A : Type) [CommRing A] [Nontrivial A] (k g : ℕ) [Fact g.Prime] [CharP A g] : Subgroup (GL (Fin k) A) where
  carrier := {x | Formalism.MainNotions.StandardLattice.IsUnitri (x : Matrix (Fin k) (Fin k) A)}
  mul_mem' := fun {a b} ha hb => by
    show Formalism.MainNotions.StandardLattice.IsUnitri ((a * b : GL (Fin k) A) : Matrix (Fin k) (Fin k) A)
    rw [Units.val_mul]
    exact Formalism.MainNotions.Gaps.MI.isUnitri_mul ha hb
  one_mem' := by
    show Formalism.MainNotions.StandardLattice.IsUnitri ((1 : GL (Fin k) A) : Matrix (Fin k) (Fin k) A)
    rw [Units.val_one]
    exact Formalism.MainNotions.Gaps.MI.isUnitri_one
  inv_mem' := fun {a} ha => by
    show Formalism.MainNotions.StandardLattice.IsUnitri ((a⁻¹ : GL (Fin k) A) : Matrix (Fin k) (Fin k) A)
    have hg : g.Prime := Fact.out
    have hpos : 0 < g ^ k := pow_pos hg.pos k
    have hpow : a ^ (g ^ k) = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      exact Formalism.MainNotions.Gaps.MI.isUnitri_pow_char g ha
    have h1 : a ^ (g ^ k - 1) * a = 1 := by
      rw [← pow_succ, Nat.sub_add_cancel hpos]
      exact hpow
    have h2 : a⁻¹ = a ^ (g ^ k - 1) := (eq_inv_of_mul_eq_one_left h1).symm
    rw [h2, Units.val_pow_eq_pow_val]
    exact Formalism.MainNotions.Gaps.MI.isUnitri_pow ha _

theorem k_closure_eq (A : Type) [CommRing A] [Nontrivial A] (k g : ℕ) [Fact g.Prime] [CharP A g] :
    Subgroup.closure (upperUni k A) = k_uni A k g := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro y hy
    exact ⟨fun i j hij => (hy i j).1 hij, fun i => (hy i i).2⟩
  · intro y hy
    exact Subgroup.subset_closure fun i j => ⟨fun hij => hy.1 i j hij, hy.2 i⟩

theorem idx_upperUni (κ : Type) [CommRing κ] (g k : ℕ) (hg : g.Prime) (hc : Nat.card κ = g) :
    ((Subgroup.closure (upperUni k κ)).index : ℝ) = Formalism.MainNotions.StandardLattice.idxColLoc g k := by
  have : Fact g.Prime := ⟨hg⟩
  have : Finite κ := Nat.finite_of_card_ne_zero (by rw [hc]; exact hg.ne_zero)
  let _ : Fintype κ := Fintype.ofFinite κ
  let e : ZMod g ≃+* κ := ZMod.ringEquivOfPrime κ hg (by rw [← Nat.card_eq_fintype_card, hc])
  have : Nontrivial κ := e.symm.toEquiv.nontrivial
  have : CharP κ g := charP_of_injective_ringHom (f := (e : ZMod g →+* κ)) e.injective g
  rw [k_closure_eq κ k g]
  let E : GL (Fin k) κ ≃ GL (Fin k) (ZMod g) :=
    (Units.mapEquiv (RingEquiv.mapMatrix (m := Fin k) e.symm).toMulEquiv).toEquiv
  have hE : ∀ (a : GL (Fin k) κ) (i j : Fin k),
      ((E a : GL (Fin k) (ZMod g)) : Matrix (Fin k) (Fin k) (ZMod g)) i j = e.symm ((a : Matrix (Fin k) (Fin k) κ) i j) :=
    fun _ _ _ => rfl
  have h1 : Nat.card (GL (Fin k) κ) = Nat.card (GL (Fin k) (ZMod g)) := Nat.card_congr E
  have h2 : Nat.card (k_uni κ k g) =
      Nat.card {A : GL (Fin k) (ZMod g) // Formalism.MainNotions.StandardLattice.IsUnitri (A : Matrix (Fin k) (Fin k) (ZMod g))} := by
    refine Nat.card_congr (Equiv.subtypeEquiv E fun a => ?_)
    show Formalism.MainNotions.StandardLattice.IsUnitri (a : Matrix (Fin k) (Fin k) κ) ↔ _
    unfold Formalism.MainNotions.StandardLattice.IsUnitri
    simp only [hE, EmbeddingLike.map_eq_zero_iff, EmbeddingLike.map_eq_one_iff]
  have h3 := Subgroup.card_mul_index (k_uni κ k g)
  have h4 : (Nat.card (k_uni κ k g) : ℝ) ≠ 0 := by
    have : 0 < Nat.card (k_uni κ k g) := Nat.card_pos
    exact_mod_cast this.ne'
  unfold Formalism.MainNotions.StandardLattice.idxColLoc Formalism.MainNotions.StandardLattice.idxLoc
  rw [← h1, ← h2, eq_div_iff h4, ← h3]
  push_cast
  ring

theorem k_exists_row {K : Type} [Field K] {k : ℕ} (i0 : Fin k) (w : Fin k → K) (hw : w ≠ 0) :
    ∃ g : GL (Fin k) K, ∀ j, (g : Matrix (Fin k) (Fin k) K) i0 j = w j := by
  obtain ⟨j0, hj0⟩ := Function.ne_iff.1 hw
  let M : Matrix (Fin k) (Fin k) K := ((1 : Matrix (Fin k) (Fin k) K).updateRow j0 w).submatrix (Equiv.swap i0 j0) id
  have hdet : M.det ≠ 0 := by
    show (((1 : Matrix (Fin k) (Fin k) K).updateRow j0 w).submatrix (Equiv.swap i0 j0) id).det ≠ 0
    rw [Matrix.det_permute, ← Matrix.cramer_transpose_apply, Matrix.transpose_one, Matrix.cramer_one]
    refine mul_ne_zero ?_ hj0
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap i0 j0)) with h | h <;> rw [h] <;> simp
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet, fun j => ?_⟩
  show M i0 j = w j
  simp [M]

def k_V (K : Type) (k : ℕ) : Type := Fin k → K

@[instance_reducible] def k_act (K : Type) [Field K] (k : ℕ) : MulAction (GL (Fin k) K) (k_V K k) where
  smul := fun g w => (show Fin k → K from w) ᵥ* ((g⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K)
  one_smul := fun w => by
    show (show Fin k → K from w) ᵥ* (((1 : GL (Fin k) K)⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) = w
    rw [inv_one, Units.val_one]
    exact Matrix.vecMul_one (show Fin k → K from w)
  mul_smul := fun g h w => by
    show (show Fin k → K from w) ᵥ* (((g * h)⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) =
      ((show Fin k → K from w) ᵥ* ((h⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K)) ᵥ*
        ((g⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K)
    rw [Matrix.vecMul_vecMul, _root_.mul_inv_rev, Units.val_mul]

theorem k_idx_field (K : Type) [Field K] [Finite K] {k : ℕ} (i0 : Fin k) :
    (rowStab K i0).index = Nat.card K ^ k - 1 := by
  let act : MulAction (GL (Fin k) K) (k_V K k) := k_act K k
  let e0 : k_V K k := (Pi.single i0 1 : Fin k → K)
  have hsm : ∀ (g : GL (Fin k) K) (w : k_V K k),
      g • w = (show Fin k → K from w) ᵥ* ((g⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) :=
    fun _ _ => rfl
  have hrow : ∀ (g : GL (Fin k) K), (Pi.single i0 1 : Fin k → K) ᵥ* (g : Matrix (Fin k) (Fin k) K) =
      fun j => (g : Matrix (Fin k) (Fin k) K) i0 j := by
    intro g
    ext j
    simp [Matrix.vecMul, dotProduct, Pi.single_apply]
  have hone : (fun j => (1 : Matrix (Fin k) (Fin k) K) i0 j) = (Pi.single i0 1 : Fin k → K) := by
    ext j
    simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  have hs : rowStab K i0 = MulAction.stabilizer (GL (Fin k) K) e0 := by
    ext g
    rw [MulAction.mem_stabilizer_iff, ← inv_mem_iff, hsm]
    show _ ↔ (Pi.single i0 1 : Fin k → K) ᵥ* ((g⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) =
      (Pi.single i0 1 : Fin k → K)
    rw [hrow, ← hone]
    exact ⟨fun h => funext h, fun h j => congrFun h j⟩
  have ho : MulAction.orbit (GL (Fin k) K) e0 = (({0} : Set (Fin k → K))ᶜ : Set (Fin k → K)) := by
    ext w
    constructor
    · rintro ⟨g, rfl⟩ h0
      have h0' : (Pi.single i0 1 : Fin k → K) ᵥ* ((g⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) = 0 := h0
      have h1 := congrArg (fun u => u ᵥ* (g : Matrix (Fin k) (Fin k) K)) h0'
      simp only [Matrix.vecMul_vecMul, Units.inv_mul, Matrix.vecMul_one, Matrix.zero_vecMul] at h1
      have h2 := congrFun h1 i0
      simp at h2
    · intro hw
      obtain ⟨g, hg⟩ := k_exists_row i0 (show Fin k → K from w) hw
      refine ⟨g⁻¹, ?_⟩
      show g⁻¹ • e0 = w
      rw [hsm, inv_inv]
      show (Pi.single i0 1 : Fin k → K) ᵥ* (g : Matrix (Fin k) (Fin k) K) = w
      rw [hrow]
      exact funext hg
  rw [hs, MulAction.index_stabilizer, ho]
  show (({0} : Set (Fin k → K))ᶜ : Set (Fin k → K)).ncard = _
  rw [Set.ncard_compl, Set.ncard_singleton, Nat.card_fun]
  simp

theorem idx_rowStab (κ : Type) [CommRing κ] (T k : ℕ) (hT : T.Prime) (hc : Nat.card κ = T) (i0 : Fin k) :
    (rowStab κ i0).index = T ^ k - 1 := by
  have : Fact T.Prime := ⟨hT⟩
  have : Finite κ := Nat.finite_of_card_ne_zero (by rw [hc]; exact hT.ne_zero)
  let _ : Fintype κ := Fintype.ofFinite κ
  let e : ZMod T ≃+* κ := ZMod.ringEquivOfPrime κ hT (by rw [← Nat.card_eq_fintype_card, hc])
  have h : rowStab κ i0 = (rowStab (ZMod T) i0).comap (bc (n := Fin k) (e.symm : κ →+* ZMod T)) := by
    ext x
    rw [Subgroup.mem_comap]
    show (∀ j, (x : Matrix (Fin k) (Fin k) κ) i0 j = (1 : Matrix (Fin k) (Fin k) κ) i0 j) ↔
      ∀ j, e.symm ((x : Matrix (Fin k) (Fin k) κ) i0 j) = (1 : Matrix (Fin k) (Fin k) (ZMod T)) i0 j
    refine forall_congr' fun j => ?_
    by_cases hij : i0 = j
    · simp [Matrix.one_apply, hij]
    · simp [hij]
  rw [h, Subgroup.index_comap_of_surjective _ (k_bc_surj e.symm), k_idx_field, Nat.card_zmod]

end K

section TAbs

variable {A : Type} [CommRing A] (O : Subring A) {n : Type} [Fintype n] [DecidableEq n] (i0 : n) (p q qi : A)
  (Lb Ld : Submodule O (n → A))

theorem t_mulVec_single (M : Matrix n n A) (j : n) (x : A) (i : n) :
    (M *ᵥ (Pi.single j x : n → A)) i = M i j * x := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem t_row_id (g : Matrix n n A) (z : n → A) (hz : ∀ j, g i0 j - (1 : Matrix n n A) i0 j = p * z j) (y : n → A) :
    (g *ᵥ y) i0 = y i0 + p * ∑ j, z j * y j := by
  have h1 : ∀ j, g i0 j = (1 : Matrix n n A) i0 j + p * z j := fun j => by rw [← hz j]; ring
  have h2 : ∑ j, (1 : Matrix n n A) i0 j * y j = y i0 := by simp [Matrix.one_apply]
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_congr rfl (fun j _ => by rw [h1 j, add_mul]), Finset.sum_add_distrib, h2, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl (fun j _ => by ring)

variable (hp : p ∈ O) (hq : q ∈ O) (hqi : q * qi = 1)
  (mLb : ∀ y, y ∈ Lb ↔ (∃ c ∈ O, y i0 = p * c) ∧ ∀ i, i ≠ i0 → y i ∈ O)
  (mLd : ∀ y, y ∈ Ld ↔ q * y i0 ∈ O ∧ ∀ i, i ≠ i0 → y i ∈ O)

include hp hq hqi mLb mLd in
theorem t_abs_entries (g : GL n A) (hL : g ∈ stabGL Lb) (hD : g ∈ stabGL Ld) (i j : n) :
    (g : Matrix n n A) i j ∈ O := by
  by_cases hj : j = i0
  · subst hj
    have h1 : (Pi.single j qi : n → A) ∈ Ld := by
      rw [mLd]
      exact ⟨by rw [Pi.single_eq_same, hqi]; exact one_mem _,
        fun i hi => by rw [Pi.single_eq_of_ne hi]; exact zero_mem _⟩
    have h2 := (mLd _).1 ((hD _).1 h1)
    by_cases hi : i = j
    · subst hi
      have h3 := h2.1
      rw [t_mulVec_single] at h3
      have : q * ((g : Matrix n n A) i i * qi) = (g : Matrix n n A) i i := by
        rw [mul_left_comm, hqi, mul_one]
      rwa [this] at h3
    · have h3 := h2.2 i hi
      rw [t_mulVec_single] at h3
      have : (g : Matrix n n A) i j = q * ((g : Matrix n n A) i j * qi) := by
        rw [mul_left_comm, hqi, mul_one]
      rw [this]
      exact mul_mem hq h3
  · have h1 : (Pi.single j 1 : n → A) ∈ Lb := by
      rw [mLb]
      refine ⟨⟨0, zero_mem _, by rw [Pi.single_eq_of_ne (Ne.symm hj), mul_zero]⟩, fun i _ => ?_⟩
      by_cases hij : i = j
      · subst hij; rw [Pi.single_eq_same]; exact one_mem _
      · rw [Pi.single_eq_of_ne hij]; exact zero_mem _
    have h2 := (mLb _).1 ((hL _).1 h1)
    by_cases hi : i = i0
    · subst hi
      obtain ⟨c, hc, h3⟩ := h2.1
      rw [t_mulVec_single, mul_one] at h3
      rw [h3]
      exact mul_mem hp hc
    · have h3 := h2.2 i hi
      rwa [t_mulVec_single, mul_one] at h3

include hp mLb in
theorem t_abs_Lb (g : Matrix n n A) (hO : ∀ i j, g i j ∈ O)
    (hrow : ∀ j, ∃ z ∈ O, g i0 j - (1 : Matrix n n A) i0 j = p * z) (y : n → A) (hy : y ∈ Lb) :
    g *ᵥ y ∈ Lb := by
  obtain ⟨⟨c, hc, hc'⟩, hy'⟩ := (mLb y).1 hy
  have hyO : ∀ i, y i ∈ O := fun i => by
    by_cases h : i = i0
    · subst h; rw [hc']; exact mul_mem hp hc
    · exact hy' i h
  choose z hz hz' using hrow
  rw [mLb]
  refine ⟨⟨c + ∑ j, z j * y j, add_mem hc (sum_mem fun j _ => mul_mem (hz j) (hyO j)), ?_⟩, fun i _ => ?_⟩
  · rw [t_row_id i0 p g z hz' y, hc', mul_add]
  · exact sum_mem fun j _ => mul_mem (hO i j) (hyO j)

include hq mLd in
theorem t_abs_Ld (g : Matrix n n A) (hO : ∀ i j, g i j ∈ O)
    (hcol : ∀ i, i ≠ i0 → ∃ z ∈ O, g i i0 = q * z) (y : n → A) (hy : y ∈ Ld) : g *ᵥ y ∈ Ld := by
  obtain ⟨h0, hy'⟩ := (mLd y).1 hy
  have hqy : ∀ j, q * y j ∈ O := fun j => by
    by_cases h : j = i0
    · subst h; exact h0
    · exact mul_mem hq (hy' j h)
  rw [mLd]
  refine ⟨?_, fun i hi => ?_⟩
  · simp only [Matrix.mulVec, dotProduct]
    rw [Finset.mul_sum]
    refine sum_mem fun j _ => ?_
    rw [mul_left_comm]
    exact mul_mem (hO i0 j) (hqy j)
  · obtain ⟨z, hz, hz'⟩ := hcol i hi
    refine sum_mem fun j _ => ?_
    by_cases h : j = i0
    · subst h
      have h3 : g i j * y j = z * (q * y j) := by rw [hz']; ring
      show g i j * y j ∈ O
      rw [h3]
      exact mul_mem hz h0
    · exact mul_mem (hO i j) (hy' j h)

include hq mLb mLd in
theorem t_abs_diff (g : Matrix n n A) (hO : ∀ i j, g i j ∈ O)
    (hrow : ∀ j, ∃ z ∈ O, g i0 j - (1 : Matrix n n A) i0 j = p * z)
    (hcol : ∀ i, i ≠ i0 → ∃ z ∈ O, g i i0 = q * z) (y : n → A) (hy : y ∈ Ld) :
    ∃ b ∈ Ld, g *ᵥ y - y - p • b ∈ Lb := by
  have hgy := (mLd _).1 (t_abs_Ld O i0 q Ld hq mLd g hO hcol y hy)
  obtain ⟨h0, hy'⟩ := (mLd y).1 hy
  have hqy : ∀ j, q * y j ∈ O := fun j => by
    by_cases h : j = i0
    · subst h; exact h0
    · exact mul_mem hq (hy' j h)
  choose z hz hz' using hrow
  refine ⟨Pi.single i0 (∑ j, z j * y j), ?_, ?_⟩
  · rw [mLd]
    refine ⟨?_, fun i hi => by rw [Pi.single_eq_of_ne hi]; exact zero_mem _⟩
    rw [Pi.single_eq_same, Finset.mul_sum]
    refine sum_mem fun j _ => ?_
    rw [mul_left_comm]
    exact mul_mem (hz j) (hqy j)
  · rw [mLb]
    refine ⟨⟨0, zero_mem _, ?_⟩, fun i hi => ?_⟩
    · simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul]
      rw [t_row_id i0 p g z hz' y]
      ring
    · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [Pi.single_eq_of_ne hi, mul_zero, sub_zero]
      exact sub_mem (hgy.2 i hi) (hy' i hi)

include hq mLb mLd in
theorem t_abs_row (g : Matrix n n A) (j : n) (a b : n → A) (ha : a ∈ Lb) (hb : b ∈ Ld)
    (h : g *ᵥ (Pi.single j 1 : n → A) - Pi.single j 1 = a + p • b) :
    ∃ w, q * w ∈ O ∧ g i0 j - (1 : Matrix n n A) i0 j = p * w := by
  obtain ⟨c, hc, hc'⟩ := ((mLb a).1 ha).1
  have hb' := ((mLd b).1 hb).1
  refine ⟨c + b i0, by rw [mul_add]; exact add_mem (mul_mem hq hc) hb', ?_⟩
  have h1 := congrFun h i0
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1
  rw [t_mulVec_single, mul_one, hc'] at h1
  rw [mul_add, ← h1, Matrix.one_apply, Pi.single_apply]

end TAbs

section TConc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem t_rho_iff {σ : E →ₐ[F] E} {v : HeightOneSpectrum (𝓞 F)} (s : SplitCore σ v) (x : intV E v) :
    fm_rho s x = 0 ↔ Valued.v (s.φ x).1 < 1 := by
  show IsLocalRing.residue _ (fm_pr s x) = 0 ↔ _
  rw [IsLocalRing.residue_eq_zero_iff, Examples₂.adicInt_mem_max_iff, fm_pr_coe]

theorem t_dvd_iff {σ : E →ₐ[F] E} {v : HeightOneSpectrum (𝓞 F)} (s : SplitCore σ v) (p : intV E v)
    (h1 : Valued.v (s.φ p).1 = WithZero.exp (-1 : ℤ)) (h2 : Valued.v (s.φ p).2 = 1)
    (x : E ⊗[F] v.adicCompletion F) (hx : x ∈ intV E v) :
    Valued.v (s.φ x).1 < 1 ↔ ∃ z ∈ intV E v, x = (p : E ⊗[F] v.adicCompletion F) * z := by
  rw [← t_rho_iff s ⟨x, hx⟩, fm_rho_eq_zero s p h1 h2]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, z.2, congrArg Subtype.val hz⟩
  · rintro ⟨z, hz, h⟩
    exact ⟨⟨z, hz⟩, Subtype.ext h⟩

theorem t_tau_tau {σ : E →ₐ[F] E} {v : HeightOneSpectrum (𝓞 F)} (s : SplitCore σ v)
    (x : E ⊗[F] v.adicCompletion F) : sigR σ (v.adicCompletion F) (sigR σ (v.adicCompletion F) x) = x := by
  apply s.φ.injective
  rw [s.sig, s.sig]
  rfl

theorem t_tau_mem {σ : E →ₐ[F] E} {v : HeightOneSpectrum (𝓞 F)} (s : SplitCore σ v)
    (x : E ⊗[F] v.adicCompletion F) (hx : x ∈ intV E v) : sigR σ (v.adicCompletion F) x ∈ intV E v := by
  rw [s.int, s.sig]
  exact ⟨((s.int x).1 hx).2, ((s.int x).1 hx).1⟩

theorem t_unit_inv {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (τ : A →+* A) (g : GL n A)
    (hg : g ∈ UJ τ (1 : Matrix n n A)) (i j : n) : ((g⁻¹ : GL n A) : Matrix n n A) i j = τ ((g : Matrix n n A) j i) := by
  have h : cT τ (g : Matrix n n A) * 1 * (g : Matrix n n A) = 1 := hg
  rw [Matrix.mul_one] at h
  have h2 : ((g⁻¹ : GL n A) : Matrix n n A) = cT τ (g : Matrix n n A) := by
    calc ((g⁻¹ : GL n A) : Matrix n n A) = (cT τ (g : Matrix n n A) * (g : Matrix n n A)) * ((g⁻¹ : GL n A) : Matrix n n A) := by
          rw [h, Matrix.one_mul]
      _ = cT τ (g : Matrix n n A) := by rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rw [h2]
  rfl

variable {k : ℕ} (P : Par F E k)

theorem t_memLb (hk : 0 < k) (v : HeightOneSpectrum (𝓞 F)) (y : Fin k → E ⊗[F] v.adicCompletion F) :
    y ∈ P.LbV v ↔ (∃ c ∈ intV E v, y ⟨0, hk⟩ = inclE (F := F) (v.adicCompletion F) (P.pz : E) * c) ∧
      ∀ i, i ≠ (⟨0, hk⟩ : Fin k) → y i ∈ intV E v := by
  have hLb : P.LbV v = latS (F := F) (v.adicCompletion F) (intV E v)
      (LevGap.diagLat (LevGap.vecAt (⟨0, hk⟩ : Fin k) (P.pz : E))) := by
    unfold Par.LbV Par.Lb; rw [LevGap.LbOf_eq_latT hk]; rfl
  rw [hLb, fm_mem_latS]
  constructor
  · intro h
    refine ⟨?_, fun i hi => ?_⟩
    · obtain ⟨c, hc⟩ := h ⟨0, hk⟩
      exact ⟨c, c.2, by rw [hc, LevGap.vecAt_same]⟩
    · obtain ⟨c, hc⟩ := h i
      rw [hc, LevGap.vecAt_ne hi, map_one, one_mul]
      exact c.2
  · rintro ⟨⟨c, hc, hc'⟩, h⟩ i
    by_cases hi : i = ⟨0, hk⟩
    · subst hi
      exact ⟨⟨c, hc⟩, by rw [hc', LevGap.vecAt_same]⟩
    · exact ⟨⟨y i, h i hi⟩, by rw [LevGap.vecAt_ne hi, map_one, one_mul]⟩

theorem t_memLd (hk : 0 < k) (hJ : P.J = 1) (hz : (P.pz : E) ≠ 0) (v : HeightOneSpectrum (𝓞 F))
    (y : Fin k → E ⊗[F] v.adicCompletion F) :
    y ∈ P.LdV v ↔ inclE (F := F) (v.adicCompletion F) (P.σ (P.pz : E)) * y ⟨0, hk⟩ ∈ intV E v ∧
      ∀ i, i ≠ (⟨0, hk⟩ : Fin k) → y i ∈ intV E v := by
  have hzc : P.σ (P.pz : E) ≠ 0 := (map_ne_zero _).2 hz
  have hinv : inclE (F := F) (v.adicCompletion F) (P.σ (P.pz : E)) *
      inclE (F := F) (v.adicCompletion F) (P.σ (P.pz : E))⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hzc, map_one]
  have hLd : P.LdV v = latS (F := F) (v.adicCompletion F) (intV E v)
      (LevGap.diagLat (LevGap.vecAt (⟨0, hk⟩ : Fin k) (P.σ (P.pz : E))⁻¹)) := by
    unfold Par.LdV; rw [LevGap.Ld_eq hk P hJ hz]
  rw [hLd, fm_mem_latS]
  constructor
  · intro h
    refine ⟨?_, fun i hi => ?_⟩
    · obtain ⟨c, hc⟩ := h ⟨0, hk⟩
      rw [hc, LevGap.vecAt_same, ← mul_assoc, hinv, one_mul]
      exact c.2
    · obtain ⟨c, hc⟩ := h i
      rw [hc, LevGap.vecAt_ne hi, map_one, one_mul]
      exact c.2
  · rintro ⟨h0, h⟩ i
    by_cases hi : i = ⟨0, hk⟩
    · subst hi
      refine ⟨⟨_, h0⟩, ?_⟩
      rw [LevGap.vecAt_same, ← mul_assoc, mul_comm (inclE (F := F) (v.adicCompletion F) (P.σ (P.pz : E))⁻¹), hinv, one_mul]
    · exact ⟨⟨y i, h i hi⟩, by rw [LevGap.vecAt_ne hi, map_one, one_mul]⟩

theorem t_cong_iff (hJ : P.J = 1) (i0 : Fin k) (v : HeightOneSpectrum (𝓞 F)) (s : SplitCore P.σ v)
    (g : GL (Fin k) (E ⊗[F] v.adicCompletion F)) :
    g ∈ congU P.σ P.J v s (rowStab _ i0) ↔ g ∈ UPts P.σ P.J (v.adicCompletion F) ∧
      (∀ i j, (g : Matrix (Fin k) (Fin k) (E ⊗[F] v.adicCompletion F)) i j ∈ intV E v) ∧
      (∀ i j, ((g⁻¹ : GL (Fin k) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin k) (Fin k) (E ⊗[F] v.adicCompletion F)) i j ∈ intV E v) ∧
      ∀ j, Valued.v (s.φ ((g : Matrix (Fin k) (Fin k) (E ⊗[F] v.adicCompletion F)) i0 j -
        (1 : Matrix (Fin k) (Fin k) (E ⊗[F] v.adicCompletion F)) i0 j)).1 < 1 := by
  constructor
  · rintro ⟨hU, g0, hg0, hg0'⟩
    have hG : bc ((RingHom.fst _ _).comp s.φ.toRingHom) g ∈ GLint (Fin k) (v.adicCompletionIntegers F).toSubring :=
      ⟨g0, hg0'⟩
    have hu : ∃ u ∈ GLint (Fin k) (v.adicCompletionIntegers F).toSubring,
        (u : Matrix (Fin k) (Fin k) (v.adicCompletion F)) =
          fun i j => (s.φ (inclE (F := F) (v.adicCompletion F) (P.J i j))).1 := by
      refine ⟨1, one_mem _, ?_⟩
      ext i j
      rw [hJ]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    have h1 : g ∈ levelV P.σ P.J v :=
      (Formalism.UG.P.level_subgroup_split F E (Fin k) P.σ P.J v s.φ s.sig s.int hu g hU).2 hG
    obtain ⟨e1, e2⟩ := (afsplit_stab_iff _ _).mp (Subgroup.mem_inf.mp h1).2
    refine ⟨hU, e1, e2, fun j => ?_⟩
    have h3 : (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)))
        ((g0 : Matrix (Fin k) (Fin k) (v.adicCompletionIntegers F)) i0 j) =
        (1 : Matrix (Fin k) (Fin k) _) i0 j := hg0 j
    rw [← LevGap.map_one_apply (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F))) i0 j,
      Ideal.Quotient.eq, Examples₂.adicInt_mem_max_iff] at h3
    have h4 : (s.φ ((g : Matrix (Fin k) (Fin k) (E ⊗[F] v.adicCompletion F)) i0 j)).1 =
        (((g0 : Matrix (Fin k) (Fin k) (v.adicCompletionIntegers F)) i0 j : v.adicCompletionIntegers F) :
          v.adicCompletion F) :=
      (congrArg (fun u : GL (Fin k) (v.adicCompletion F) => (u : Matrix (Fin k) (Fin k) (v.adicCompletion F)) i0 j) hg0').symm
    have h5 : (s.φ ((1 : Matrix (Fin k) (Fin k) (E ⊗[F] v.adicCompletion F)) i0 j)).1 =
        (((1 : Matrix (Fin k) (Fin k) (v.adicCompletionIntegers F)) i0 j : v.adicCompletionIntegers F) :
          v.adicCompletion F) :=
      (LevGap.map_one_apply ((RingHom.fst _ _).comp s.φ.toRingHom) i0 j).trans
        (LevGap.map_one_apply (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) i0 j).symm
    rw [map_sub, Prod.fst_sub, h4, h5]
    exact h3
  · rintro ⟨hU, e1, e2, hrow⟩
    have r1 : (g : Matrix (Fin k) (Fin k) (E ⊗[F] v.adicCompletion F)) ∈
        (RingHom.mapMatrix (m := Fin k) (intV E v).subtype).range :=
      ⟨Matrix.of fun i j => ⟨_, e1 i j⟩, by ext i j; rfl⟩
    have r2 : ((g⁻¹ : GL (Fin k) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin k) (Fin k) (E ⊗[F] v.adicCompletion F)) ∈
        (RingHom.mapMatrix (m := Fin k) (intV E v).subtype).range :=
      ⟨Matrix.of fun i j => ⟨_, e2 i j⟩, by ext i j; rfl⟩
    obtain ⟨G, hG⟩ := levelaf_mem_range_of_integral (intV E v) g r1 r2
    refine ⟨hU, bc (fm_pr s) G, ?_, ?_⟩
    · intro j
      show (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)))
        (fm_pr s ((G : Matrix (Fin k) (Fin k) (intV E v)) i0 j)) = (1 : Matrix (Fin k) (Fin k) _) i0 j
      rw [← LevGap.map_one_apply (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F))) i0 j,
        ← LevGap.map_one_apply (fm_pr s) i0 j, Ideal.Quotient.eq, ← map_sub, Examples₂.adicInt_mem_max_iff, fm_pr_coe]
      have h := hrow j
      rw [← hG, ← LevGap.map_one_apply (intV E v).subtype i0 j] at h
      exact h
    · rw [← hG]
      rfl

end TConc

section TMain

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem t_col {k : ℕ} (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (s : SplitCore σ v) (i0 : Fin k)
    (p : E ⊗[F] v.adicCompletion F)
    (g : GL (Fin k) (E ⊗[F] v.adicCompletion F))
    (hU : g ∈ UJ (sigR σ (v.adicCompletion F)) (1 : Matrix (Fin k) (Fin k) (E ⊗[F] v.adicCompletion F)))
    (hrow : ∀ j, ∃ z ∈ intV E v, ((g⁻¹ : GL (Fin k) (E ⊗[F] v.adicCompletion F)) :
      Matrix (Fin k) (Fin k) (E ⊗[F] v.adicCompletion F)) i0 j -
        (1 : Matrix (Fin k) (Fin k) (E ⊗[F] v.adicCompletion F)) i0 j = p * z) :
    ∀ i, i ≠ i0 → ∃ z ∈ intV E v, (g : Matrix (Fin k) (Fin k) (E ⊗[F] v.adicCompletion F)) i i0 =
      sigR σ (v.adicCompletion F) p * z := by
  intro i hi
  obtain ⟨z, hz, h⟩ := hrow i
  rw [Matrix.one_apply_ne (Ne.symm hi), sub_zero, t_unit_inv _ g hU] at h
  refine ⟨sigR σ (v.adicCompletion F) z, t_tau_mem s z hz, ?_⟩
  rw [← map_mul, ← h, t_tau_tau s]

theorem Uloc_T_eq {k : ℕ} (P : Par F E k) (hk : 0 < k) (hJ : P.J = 1) (pzc : 𝓞 E) (hc : (pzc : E) = P.σ (P.pz : E))
    (hz : (P.pz : E) ≠ 0) (v : HeightOneSpectrum (𝓞 F)) (s : SplitCore P.σ v)
    (h1 : Valued.v (s.φ ((P.pz : E) ⊗ₜ[F] (1 : v.adicCompletion F))).1 = WithZero.exp (-1 : ℤ))
    (h2 : Valued.v (s.φ ((P.pz : E) ⊗ₜ[F] (1 : v.adicCompletion F))).2 = 1) :
    levelVL P.σ P.J v P.Lb ⊓ stabFun _ (P.fT v) = congU P.σ P.J v s (rowStab _ (⟨0, hk⟩ : Fin k)) := by
  classical
  let i0 : Fin k := ⟨0, hk⟩
  let ι : E →+* E ⊗[F] v.adicCompletion F := inclE (F := F) (E := E) (v.adicCompletion F)
  have hzc : P.σ (P.pz : E) ≠ 0 := (map_ne_zero _).2 hz
  have hqi : ι (P.σ (P.pz : E)) * ι (P.σ (P.pz : E))⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hzc, map_one]
  have hp : ι (P.pz : E) ∈ intV E v := fm_incl_mem v P.pz
  have hq : ι (P.σ (P.pz : E)) ∈ intV E v := by rw [← hc]; exact fm_incl_mem v pzc
  have mLb := t_memLb P hk v
  have mLd := t_memLd P hk hJ hz v
  have hJ' : P.J.map (inclE (F := F) (v.adicCompletion F)) = 1 := by
    rw [hJ]; exact Matrix.map_one _ (map_zero _) (map_one _)
  have hUJ : ∀ g, g ∈ UPts P.σ P.J (v.adicCompletion F) →
      g ∈ UJ (sigR P.σ (v.adicCompletion F)) (1 : Matrix (Fin k) (Fin k) (E ⊗[F] v.adicCompletion F)) := by
    intro g hg
    unfold UPts at hg
    rwa [hJ'] at hg
  have hsw : s.φ (ι (P.σ (P.pz : E))) = ((s.φ (ι (P.pz : E))).2, (s.φ (ι (P.pz : E))).1) :=
    s.sig ((P.pz : E) ⊗ₜ[F] (1 : v.adicCompletion F))
  have htp : sigR P.σ (v.adicCompletion F) (ι (P.pz : E)) = ι (P.σ (P.pz : E)) := rfl
  have hdvd := t_dvd_iff s (P.pzV v) h1 h2
  ext g
  rw [t_cong_iff P hJ i0 v s g]
  constructor
  · rintro ⟨⟨hU, hL⟩, hD, hf⟩
    have e1 := t_abs_entries (intV E v) i0 _ _ _ (P.LbV v) (P.LdV v) hp hq hqi mLb mLd g hL hD
    have e2 := t_abs_entries (intV E v) i0 _ _ _ (P.LbV v) (P.LdV v) hp hq hqi mLb mLd g⁻¹
      (inv_mem hL) (inv_mem hD)
    refine ⟨hU, e1, e2, fun j => ?_⟩
    have hej : (Pi.single j 1 : Fin k → E ⊗[F] v.adicCompletion F) ∈ P.LdV v := by
      rw [mLd]
      refine ⟨?_, fun i _ => ?_⟩
      · by_cases hj : i0 = j
        · rw [← hj, Pi.single_eq_same, mul_one]; exact hq
        · rw [Pi.single_eq_of_ne hj, mul_zero]; exact zero_mem _
      · by_cases hj : i = j
        · rw [← hj, Pi.single_eq_same]; exact one_mem _
        · rw [Pi.single_eq_of_ne hj]; exact zero_mem _
    have h3 := hf ⟨_, hej⟩
    have h4 := (Submodule.Quotient.eq (P.fKer v)).1 h3
    obtain ⟨a, ha, _, ⟨b, rfl⟩, hab⟩ := Submodule.mem_sup.1 h4
    obtain ⟨w, hw, hw'⟩ := t_abs_row (intV E v) i0 (ι (P.pz : E)) _ (P.LbV v) (P.LdV v) hq mLb mLd
      (g : Matrix (Fin k) (Fin k) (E ⊗[F] v.adicCompletion F)) j a.1 b.1 ha b.2 (congrArg Subtype.val hab).symm
    rw [hw', map_mul, Prod.fst_mul, map_mul]
    have h5 : Valued.v (s.φ w).1 ≤ 1 := by
      have h6 := ((s.int _).1 hw).1
      rw [map_mul, Prod.fst_mul, hsw, HeightOneSpectrum.mem_adicCompletionIntegers, map_mul] at h6
      change Valued.v (s.φ ((P.pz : E) ⊗ₜ[F] (1 : v.adicCompletion F))).2 * _ ≤ 1 at h6
      rwa [h2, one_mul] at h6
    change Valued.v (s.φ ((P.pz : E) ⊗ₜ[F] (1 : v.adicCompletion F))).1 * _ < 1
    rw [h1]
    calc WithZero.exp (-1 : ℤ) * Valued.v (s.φ w).1 ≤ WithZero.exp (-1 : ℤ) * 1 := by gcongr
      _ < 1 := by rw [mul_one, Examples₂.wz_lt_one_iff]
  · intro hg
    have hgc : g ∈ congU P.σ P.J v s (rowStab _ i0) := (t_cong_iff P hJ i0 v s g).2 hg
    obtain ⟨hU, e1, e2, hr⟩ := hg
    obtain ⟨hU', -, -, hr'⟩ := (t_cong_iff P hJ i0 v s g⁻¹).1 (inv_mem hgc)
    have one_mem' : ∀ j, (1 : Matrix (Fin k) (Fin k) (E ⊗[F] v.adicCompletion F)) i0 j ∈ intV E v :=
      fun j => afsplit_one_mem _ i0 j
    have hrow : ∀ j, ∃ z ∈ intV E v, (g : Matrix (Fin k) (Fin k) (E ⊗[F] v.adicCompletion F)) i0 j -
        (1 : Matrix (Fin k) (Fin k) (E ⊗[F] v.adicCompletion F)) i0 j = ι (P.pz : E) * z :=
      fun j => (hdvd _ (sub_mem (e1 i0 j) (one_mem' j))).1 (hr j)
    have hrow' : ∀ j, ∃ z ∈ intV E v, ((g⁻¹ : GL (Fin k) (E ⊗[F] v.adicCompletion F)) :
        Matrix (Fin k) (Fin k) (E ⊗[F] v.adicCompletion F)) i0 j -
        (1 : Matrix (Fin k) (Fin k) (E ⊗[F] v.adicCompletion F)) i0 j = ι (P.pz : E) * z :=
      fun j => (hdvd _ (sub_mem (e2 i0 j) (one_mem' j))).1 (hr' j)
    have hcol := t_col P.σ v s i0 (ι (P.pz : E)) g (hUJ g hU) hrow'
    have hcol' := t_col P.σ v s i0 (ι (P.pz : E)) g⁻¹ (hUJ _ hU') (by rw [inv_inv]; exact hrow)
    rw [htp] at hcol hcol'
    have hL : g ∈ stabGL (P.LbV v) := LevGap.mem_stabGL_of _ g
      (t_abs_Lb (intV E v) i0 _ (P.LbV v) hp mLb _ e1 hrow)
      (t_abs_Lb (intV E v) i0 _ (P.LbV v) hp mLb _ e2 hrow')
    have hD : g ∈ stabGL (P.LdV v) := LevGap.mem_stabGL_of _ g
      (t_abs_Ld (intV E v) i0 _ (P.LdV v) hq mLd _ e1 hcol)
      (t_abs_Ld (intV E v) i0 _ (P.LdV v) hq mLd _ e2 hcol')
    refine ⟨⟨hU, hL⟩, hD, fun x => ?_⟩
    obtain ⟨b, hb, hab⟩ := t_abs_diff (intV E v) i0 (ι (P.pz : E)) _ (P.LbV v) (P.LdV v) hq mLb mLd
      (g : Matrix (Fin k) (Fin k) (E ⊗[F] v.adicCompletion F)) e1 hrow hcol x.1 x.2
    refine (Submodule.Quotient.eq (P.fKer v)).2 ?_
    refine Submodule.mem_sup.2 ⟨_ - P.pzV v • (⟨b, hb⟩ : P.LdV v), ?_, P.pzV v • (⟨b, hb⟩ : P.LdV v), ⟨⟨b, hb⟩, rfl⟩,
      sub_add_cancel _ _⟩
    exact hab

end TMain

section Asm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem m_stdLat_eq (k : ℕ) :
    Formalism.MainNotions.StandardLattice.stdLat E k = Formalism.UG.stdLat (n := Fin k) (A := E) (𝓞 E) := by
  have h := Formalism.MainNotions.Gaps.LevGap.diagLat_eq_span (E := E) (n := Fin k) (fun _ => (1 : E))
  unfold Formalism.MainNotions.StandardLattice.stdLat
  rw [← h]
  ext x
  rw [Formalism.MainNotions.Gaps.LevGap.mem_diagLat, mem_stdLat_iff']
  refine forall_congr' fun i => ⟨?_, ?_⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, by rw [hc, one_mul]⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, by rw [one_mul]; exact hc.symm⟩

theorem m_finite_places (p : ℕ) (hp : p ≠ 0) : {v : HeightOneSpectrum (𝓞 F) | (p : 𝓞 F) ∈ v.asIdeal}.Finite := by
  have h0 : Ideal.span {(p : 𝓞 F)} ≠ 0 := by
    intro h
    rw [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] at h
    exact hp (by exact_mod_cast h)
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  exact (Ideal.dvd_span_singleton).2 hv

theorem Kstd_eq {k : ℕ} (σ : E →ₐ[F] E) (J : Matrix (Fin k) (Fin k) E) :
    levelAfL σ J (Formalism.MainNotions.StandardLattice.stdLat E k) = adG σ J (fun v => levelV σ J v) := by
  rw [m_stdLat_eq, level_subgroup_finite_adelic_standard, levelAf_eq_adG]

variable {k : ℕ} (P : Par F E k)

theorem m_U_eq (S : P.Splits) : P.U S = adG P.σ P.J (P.Uloc S) := rfl

theorem m_levelVL_Lb (pzc : 𝓞 E) (hpz : (P.pz : E) * (pzc : E) = (P.T : E))
    (v : HeightOneSpectrum (𝓞 F)) (hTv : (P.T : 𝓞 F) ∉ v.asIdeal) :
    levelVL P.σ P.J v P.Lb = levelV P.σ P.J v := by
  rw [← level_subgroup_local_standard F E (Fin k) P.σ P.J v]
  unfold levelVL Par.Lb
  rw [iw_latS_eq (F := F) k P.pz pzc P.T hpz v hTv]

theorem m_iwPre_eq (v : HeightOneSpectrum (𝓞 F)) (s : SplitCore P.σ v) :
    P.iwPre v s.φ = congU P.σ P.J v s (Subgroup.closure (upperUni k _)) := rfl

theorem m_orient (hpz : (P.pz : E) * P.σ (P.pz : E) = (P.T : E)) (v : HeightOneSpectrum (𝓞 F))
    (s : SplitCore P.σ v) (hval : Valued.v ((P.T : ℕ) : v.adicCompletion F) = WithZero.exp (-1 : ℤ)) :
    ∃ s' : SplitCore P.σ v,
      Valued.v (s'.φ ((P.pz : E) ⊗ₜ[F] (1 : v.adicCompletion F))).1 = WithZero.exp (-1 : ℤ) ∧
      Valued.v (s'.φ ((P.pz : E) ⊗ₜ[F] (1 : v.adicCompletion F))).2 = 1 := by
  have hsw : s.φ ((P.σ (P.pz : E)) ⊗ₜ[F] (1 : v.adicCompletion F)) =
      ((s.φ ((P.pz : E) ⊗ₜ[F] (1 : v.adicCompletion F))).2, (s.φ ((P.pz : E) ⊗ₜ[F] (1 : v.adicCompletion F))).1) :=
    s.sig ((P.pz : E) ⊗ₜ[F] (1 : v.adicCompletion F))
  have e1 : ((P.T : ℕ) : E) ⊗ₜ[F] (1 : v.adicCompletion F) = ((P.T : ℕ) : E ⊗[F] v.adicCompletion F) :=
    map_natCast (inclE (F := F) (E := E) (v.adicCompletion F)) P.T
  have e2 : (1 : E) ⊗ₜ[F] ((P.T : ℕ) : v.adicCompletion F) = ((P.T : ℕ) : E ⊗[F] v.adicCompletion F) :=
    map_natCast (Algebra.TensorProduct.includeRight : v.adicCompletion F →ₐ[F] E ⊗[F] v.adicCompletion F) P.T
  have hprod : (s.φ ((P.pz : E) ⊗ₜ[F] (1 : v.adicCompletion F))).1 *
      (s.φ ((P.pz : E) ⊗ₜ[F] (1 : v.adicCompletion F))).2 = ((P.T : ℕ) : v.adicCompletion F) := by
    have h0 : ((P.pz : E) ⊗ₜ[F] (1 : v.adicCompletion F)) * ((P.σ (P.pz : E)) ⊗ₜ[F] (1 : v.adicCompletion F)) =
        (1 : E) ⊗ₜ[F] ((P.T : ℕ) : v.adicCompletion F) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, hpz, mul_one, e1, e2]
    have h := congrArg s.φ h0
    rw [map_mul, hsw, s.alg] at h
    exact congrArg Prod.fst h
  have hint := (s.int _).1 (P.pzV v).2
  have hv1 : Valued.v (s.φ ((P.pz : E) ⊗ₜ[F] (1 : v.adicCompletion F))).1 ≤ 1 := hint.1
  have hv2 : Valued.v (s.φ ((P.pz : E) ⊗ₜ[F] (1 : v.adicCompletion F))).2 ≤ 1 := hint.2
  have hvp := congrArg Valued.v hprod
  rw [map_mul, hval] at hvp
  by_cases h : Valued.v (s.φ ((P.pz : E) ⊗ₜ[F] (1 : v.adicCompletion F))).1 = 1
  · rw [h, one_mul] at hvp
    exact ⟨fm_swap s, hvp, h⟩
  · have h1 := (Examples₂.wz_lt_one_iff _).1 (lt_of_le_of_ne hv1 h)
    have h2 : Valued.v (s.φ ((P.pz : E) ⊗ₜ[F] (1 : v.adicCompletion F))).2 = 1 := by
      by_contra h2
      have h2' := (Examples₂.wz_lt_one_iff _).1 (lt_of_le_of_ne hv2 h2)
      have : WithZero.exp (-1 : ℤ) ≤ WithZero.exp (-1 : ℤ) * WithZero.exp (-1 : ℤ) := by
        calc WithZero.exp (-1 : ℤ) = _ := hvp.symm
          _ ≤ _ := mul_le_mul' h1 h2'
      rw [← WithZero.exp_add, WithZero.exp_le_exp] at this
      omega
    rw [h2, mul_one] at hvp
    exact ⟨s, hvp, h2⟩

structure IdxHyp (f : ℕ) : Prop where
  k_pos : 0 < k
  J_one : P.J = 1
  norm : (P.pz : E) * P.σ (P.pz : E) = (P.T : E)
  T_prime : P.T.Prime
  g_prime : ∀ i, (P.gp i).Prime
  T_g : ∀ i, P.T ≠ P.gp i
  g_ne : P.gp 0 ≠ P.gp 1
  core_alt : ∀ v : HeightOneSpectrum (𝓞 F), (P.T : 𝓞 F) ∈ v.asIdeal → Nonempty (SplitCore P.σ v)
  valuation_at_places_over_T : ∀ v : HeightOneSpectrum (𝓞 F), (P.T : 𝓞 F) ∈ v.asIdeal →
    Valued.v ((P.T : ℕ) : v.adicCompletion F) = WithZero.exp (-1 : ℤ)
  card_alt : ∀ v : HeightOneSpectrum (𝓞 F), (P.T : 𝓞 F) ∈ v.asIdeal → Nat.card (𝓞 F ⧸ v.asIdeal) = P.T
  card_g : ∀ i, ∀ v : HeightOneSpectrum (𝓞 F), (P.gp i : 𝓞 F) ∈ v.asIdeal → Nat.card (𝓞 F ⧸ v.asIdeal) = P.gp i
  num_places_over_T : {v : HeightOneSpectrum (𝓞 F) | (P.T : 𝓞 F) ∈ v.asIdeal}.ncard = f
  num_g : ∀ i, {v : HeightOneSpectrum (𝓞 F) | (P.gp i : 𝓞 F) ∈ v.asIdeal}.ncard = f

variable {P} {f : ℕ}

theorem m_card_res (v : HeightOneSpectrum (𝓞 F)) :
    Nat.card (v.adicCompletionIntegers F ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) =
      Nat.card (𝓞 F ⧸ v.asIdeal) := fm_card_residue v

theorem IdxHyp.coprime_level_prime (h : IdxHyp P f) (i : Fin 2) : Nat.Coprime P.T (P.gp i) :=
  (Nat.coprime_primes h.T_prime (h.g_prime i)).2 (h.T_g i)

theorem IdxHyp.cop_g (h : IdxHyp P f) : Nat.Coprime (P.gp 0) (P.gp 1) :=
  (Nat.coprime_primes (h.g_prime 0) (h.g_prime 1)).2 h.g_ne

theorem IdxHyp.exists_pzc (_h : IdxHyp P f) : ∃ pzc : 𝓞 E, (pzc : E) = P.σ (P.pz : E) :=
  Formalism.MainNotions.Gaps.LevGap.map_int_mem (P.σ : E →+* E) P.pz

theorem IdxHyp.UlocAlt (h : IdxHyp P f) (S : P.Splits) (v : HeightOneSpectrum (𝓞 F)) (hv : (P.T : 𝓞 F) ∈ v.asIdeal) :
    ∃ s : SplitCore P.σ v, P.Uloc S v = congU P.σ P.J v s (rowStab _ (⟨0, h.k_pos⟩ : Fin k)) := by
  obtain ⟨s0⟩ := h.core_alt v hv
  obtain ⟨s, h1, h2⟩ := m_orient P h.norm v s0 (h.valuation_at_places_over_T v hv)
  obtain ⟨pzc, hc⟩ := h.exists_pzc
  have hz : (P.pz : E) ≠ 0 := by
    intro h0
    have := h.norm
    rw [h0, zero_mul] at this
    exact h.T_prime.ne_zero (by exact_mod_cast this.symm)
  exact ⟨s, by rw [Par.UlocAlt P S v hv]; exact Uloc_T_eq P h.k_pos h.J_one pzc hc hz v s h1 h2⟩

theorem IdxHyp.Uloc_g (h : IdxHyp P f) (S : P.Splits) (i : Fin 2) (v : HeightOneSpectrum (𝓞 F))
    (hv : (P.gp i : 𝓞 F) ∈ v.asIdeal) :
    P.Uloc S v = congU P.σ P.J v (S i v hv).core (Subgroup.closure (upperUni k _)) := by
  rw [Par.Uloc_g P S h.coprime_level_prime h.cop_g i v hv]; rfl

theorem IdxHyp.Uloc_hyp (h : IdxHyp P f) (S : P.Splits) (v : HeightOneSpectrum (𝓞 F))
    (hT : (P.T : 𝓞 F) ∉ v.asIdeal) (h0 : (P.gp 0 : 𝓞 F) ∉ v.asIdeal) (h1 : (P.gp 1 : 𝓞 F) ∉ v.asIdeal) :
    P.Uloc S v = levelV P.σ P.J v := by
  obtain ⟨pzc, hc⟩ := h.exists_pzc
  rw [Par.Uloc_hyp P S v h0 h1 hT]
  exact m_levelVL_Lb P pzc (by rw [hc]; exact h.norm) v hT

theorem IdxHyp.Uloc_le (h : IdxHyp P f) (S : P.Splits) (v : HeightOneSpectrum (𝓞 F)) :
    P.Uloc S v ≤ levelV P.σ P.J v := by
  by_cases hT : (P.T : 𝓞 F) ∈ v.asIdeal
  · obtain ⟨s, hs⟩ := h.UlocAlt S v hT
    rw [hs, h.J_one]; exact congU_le _ _ _ _
  by_cases h0 : (P.gp 0 : 𝓞 F) ∈ v.asIdeal
  · rw [h.Uloc_g S 0 v h0, h.J_one]; exact congU_le _ _ _ _
  by_cases h1 : (P.gp 1 : 𝓞 F) ∈ v.asIdeal
  · rw [h.Uloc_g S 1 v h1, h.J_one]; exact congU_le _ _ _ _
  exact (h.Uloc_hyp S v hT h0 h1).le

theorem IdxHyp.U_le (h : IdxHyp P f) (S : P.Splits) :
    P.U S ≤ levelAfL P.σ P.J (Formalism.MainNotions.StandardLattice.stdLat E k) := by
  rw [Kstd_eq, m_U_eq]
  exact inf_le_inf_left _ (iInf_mono fun v => Subgroup.comap_mono (h.Uloc_le S v))

theorem IdxHyp.relIndex_alt (h : IdxHyp P f) (S : P.Splits) (v : HeightOneSpectrum (𝓞 F))
    (hv : (P.T : 𝓞 F) ∈ v.asIdeal) : (P.Uloc S v).relIndex (levelV P.σ P.J v) = P.T ^ k - 1 := by
  obtain ⟨s, hs⟩ := h.UlocAlt S v hv
  rw [hs, h.J_one, congU_relIndex]
  exact idx_rowStab _ P.T k h.T_prime ((m_card_res v).trans (h.card_alt v hv)) _

theorem IdxHyp.relIndex_g (h : IdxHyp P f) (S : P.Splits) (i : Fin 2) (v : HeightOneSpectrum (𝓞 F))
    (hv : (P.gp i : 𝓞 F) ∈ v.asIdeal) :
    ((P.Uloc S v).relIndex (levelV P.σ P.J v) : ℝ) = Formalism.MainNotions.StandardLattice.idxColLoc (P.gp i) k := by
  rw [h.Uloc_g S i v hv, h.J_one, congU_relIndex]
  exact idx_upperUni _ (P.gp i) k (h.g_prime i) ((m_card_res v).trans (h.card_g i v hv))

theorem IdxHyp.relIndex_g_ne (h : IdxHyp P f) (S : P.Splits) (i : Fin 2) (v : HeightOneSpectrum (𝓞 F))
    (hv : (P.gp i : 𝓞 F) ∈ v.asIdeal) : (P.Uloc S v).relIndex (levelV P.σ P.J v) ≠ 0 := by
  rw [h.Uloc_g S i v hv, h.J_one, congU_relIndex]
  have : Finite (v.adicCompletionIntegers F ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) :=
    Nat.finite_of_card_ne_zero (by rw [m_card_res v, h.card_g i v hv]; exact (h.g_prime i).ne_zero)
  exact Subgroup.index_ne_zero_of_finite

theorem IdxHyp.relIndex (h : IdxHyp P f) (S : P.Splits) :
    ((P.U S).relIndex (levelAfL P.σ P.J (Formalism.MainNotions.StandardLattice.stdLat E k)) : ℝ) =
      Formalism.MainNotions.StandardLattice.idxColLoc (P.gp 0) k ^ f * Formalism.MainNotions.StandardLattice.idxColLoc (P.gp 1) k ^ f * ((P.T : ℝ) ^ k - 1) ^ f := by
  classical
  have fT := m_finite_places (F := F) P.T h.T_prime.ne_zero
  have f0 := m_finite_places (F := F) (P.gp 0) (h.g_prime 0).ne_zero
  have f1 := m_finite_places (F := F) (P.gp 1) (h.g_prime 1).ne_zero
  have d01 : Disjoint f0.toFinset f1.toFinset := by
    rw [Finset.disjoint_left]
    intro v h0 h1
    exact asm_not_both h.cop_g v (f0.mem_toFinset.1 h0) (f1.mem_toFinset.1 h1)
  have dT : Disjoint (f0.toFinset ∪ f1.toFinset) fT.toFinset := by
    rw [Finset.disjoint_left]
    intro v h0 hT
    rcases Finset.mem_union.1 h0 with h0 | h0
    · exact asm_not_both (h.coprime_level_prime 0) v (fT.mem_toFinset.1 hT) (f0.mem_toFinset.1 h0)
    · exact asm_not_both (h.coprime_level_prime 1) v (fT.mem_toFinset.1 hT) (f1.mem_toFinset.1 h0)
  rw [Kstd_eq, m_U_eq, adG_relIndex P.σ P.J (P.Uloc S) (fun v => levelV P.σ P.J v) (h.Uloc_le S)
    (fun v => inf_le_left) ((f0.toFinset ∪ f1.toFinset) ∪ fT.toFinset) ?_]
  · rw [Finset.prod_union dT, Finset.prod_union d01]
    push_cast
    rw [Finset.prod_congr rfl (fun v hv => h.relIndex_g S 0 v (f0.mem_toFinset.1 hv)),
      Finset.prod_congr rfl (fun v hv => h.relIndex_g S 1 v (f1.mem_toFinset.1 hv)),
      Finset.prod_congr rfl (fun v hv => congrArg (Nat.cast : ℕ → ℝ) (h.relIndex_alt S v (fT.mem_toFinset.1 hv))),
      Finset.prod_const, Finset.prod_const, Finset.prod_const, ← Set.ncard_eq_toFinset_card _ f0,
      ← Set.ncard_eq_toFinset_card _ f1, ← Set.ncard_eq_toFinset_card _ fT, h.num_g 0, h.num_g 1, h.num_places_over_T,
      Nat.cast_sub (Nat.one_le_pow _ _ h.T_prime.pos)]
    push_cast
    rfl
  · intro v hv
    simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_or] at hv
    exact h.Uloc_hyp S v hv.2 hv.1.1 hv.1.2

theorem IdxHyp.relIndex_ne_zero (h : IdxHyp P f) (S : P.Splits) :
    (P.U S).relIndex (levelAfL P.σ P.J (Formalism.MainNotions.StandardLattice.stdLat E k)) ≠ 0 := by
  classical
  have fT := m_finite_places (F := F) P.T h.T_prime.ne_zero
  have f0 := m_finite_places (F := F) (P.gp 0) (h.g_prime 0).ne_zero
  have f1 := m_finite_places (F := F) (P.gp 1) (h.g_prime 1).ne_zero
  rw [Kstd_eq, m_U_eq, adG_relIndex P.σ P.J (P.Uloc S) (fun v => levelV P.σ P.J v) (h.Uloc_le S)
    (fun v => inf_le_left) ((f0.toFinset ∪ f1.toFinset) ∪ fT.toFinset) ?_]
  · refine Finset.prod_ne_zero_iff.2 fun v hv => ?_
    simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hv
    rcases hv with (hv | hv) | hv
    · exact h.relIndex_g_ne S 0 v hv
    · exact h.relIndex_g_ne S 1 v hv
    · rw [h.relIndex_alt S v hv]
      have := Nat.one_lt_pow h.k_pos.ne' h.T_prime.one_lt
      omega
  · intro v hv
    simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_or] at hv
    exact h.Uloc_hyp S v hv.2 hv.1.1 hv.1.2

theorem IdxHyp.relIndex_GA (h : IdxHyp P f) (S : P.Splits) :
    (((P.U S).subgroupOf P.GA).relIndex ((levelAfL P.σ P.J (Formalism.MainNotions.StandardLattice.stdLat E k)).subgroupOf P.GA) : ℝ) =
      Formalism.MainNotions.StandardLattice.idxColLoc (P.gp 0) k ^ f * Formalism.MainNotions.StandardLattice.idxColLoc (P.gp 1) k ^ f * ((P.T : ℝ) ^ k - 1) ^ f := by
  rw [Subgroup.relIndex_subgroupOf (show levelAfL P.σ P.J (Formalism.MainNotions.StandardLattice.stdLat E k) ≤ P.GA from inf_le_left)]
  exact h.relIndex S

theorem IdxHyp.relIndex_GA_ne_zero (h : IdxHyp P f) (S : P.Splits) :
    ((P.U S).subgroupOf P.GA).relIndex ((levelAfL P.σ P.J (Formalism.MainNotions.StandardLattice.stdLat E k)).subgroupOf P.GA) ≠ 0 := by
  rw [Subgroup.relIndex_subgroupOf (show levelAfL P.σ P.J (Formalism.MainNotions.StandardLattice.stdLat E k) ≤ P.GA from inf_le_left)]
  exact h.relIndex_ne_zero S

theorem IdxHyp.idxOK (h : IdxHyp P f) : IdxOK P f := fun S => ⟨h.U_le S, h.relIndex S⟩

end Asm

section Host

variable {R : Ranks} (H : Host R)

theorem idxHyp_host (T : ℕ) (pz : 𝓞 H.E) (piG : Fin 2 → 𝓞 H.E) (h : LevHyp H T pz piG) :
    IdxHyp (hostPar H T pz piG) R.f := by
  have hs := Formalism.MainNotions.Gaps.LevGap.T_split_of_levHyp H T pz piG h
  exact
  { k_pos := Formalism.MainNotions.Gaps.LevGap.k_pos R
    J_one := rfl
    norm := h.pz_norm
    T_prime := h.T_prime
    g_prime := H.g_prime
    T_g := Formalism.MainNotions.Gaps.LevGap.factTNeG H T pz piG h
    g_ne := H.g_ne
    core_alt := fun v hv => host_core H T h.T_prime hs v hv
    valuation_at_places_over_T := fun v hv => hs_val H T h.T_prime hs v hv
    card_alt := fun v hv => hs_card H T h.T_prime hs v hv
    card_g := fun i v hv => hs_card H (H.g i) (H.g_prime i) (h.g_split i) v hv
    num_places_over_T := (Formalism.MainNotions.Gaps.LevGap.split_F H T h.T_prime hs).trans (Formalism.MainNotions.Gaps.LevGap.finrank_F H)
    num_g := fun i => (Formalism.MainNotions.Gaps.LevGap.split_F H (H.g i) (H.g_prime i) (h.g_split i)).trans
      (Formalism.MainNotions.Gaps.LevGap.finrank_F H) }

theorem host_U_le (T : ℕ) (pz : 𝓞 H.E) (piG : Fin 2 → 𝓞 H.E) (h : LevHyp H T pz piG)
    (S : (hostPar H T pz piG).Splits) :
    (hostPar H T pz piG).U S ≤ levelAfL (Examples₂.conjF H) 1 (Formalism.MainNotions.StandardLattice.stdLat H.E R.k) :=
  (idxHyp_host H T pz piG h).U_le S

theorem host_relIndex (T : ℕ) (pz : 𝓞 H.E) (piG : Fin 2 → 𝓞 H.E) (h : LevHyp H T pz piG)
    (S : (hostPar H T pz piG).Splits) :
    (((hostPar H T pz piG).U S).relIndex (levelAfL (Examples₂.conjF H) 1 (Formalism.MainNotions.StandardLattice.stdLat H.E R.k)) : ℝ) =
      Formalism.MainNotions.StandardLattice.idxColLoc (H.g 0) R.k ^ R.f * Formalism.MainNotions.StandardLattice.idxColLoc (H.g 1) R.k ^ R.f * ((T : ℝ) ^ R.k - 1) ^ R.f :=
  (idxHyp_host H T pz piG h).relIndex S

theorem host_relIndex_ne_zero (T : ℕ) (pz : 𝓞 H.E) (piG : Fin 2 → 𝓞 H.E) (h : LevHyp H T pz piG)
    (S : (hostPar H T pz piG).Splits) :
    ((hostPar H T pz piG).U S).relIndex (levelAfL (Examples₂.conjF H) 1 (Formalism.MainNotions.StandardLattice.stdLat H.E R.k)) ≠ 0 :=
  (idxHyp_host H T pz piG h).relIndex_ne_zero S

theorem idxOK_host (T : ℕ) (pz : 𝓞 H.E) (piG : Fin 2 → 𝓞 H.E) (h : LevHyp H T pz piG) :
    IdxOK (hostPar H T pz piG) R.f :=
  fun S => ⟨host_U_le H T pz piG h S, host_relIndex H T pz piG h S⟩

theorem host_relIndex_Kstd_ne_zero (T : ℕ) (pz : 𝓞 H.E) (piG : Fin 2 → 𝓞 H.E) (h : LevHyp H T pz piG)
    (S : (hostPar H T pz piG).Splits) :
    ((hostPar H T pz piG).U S).relIndex (Kstd (hostPar H T pz piG).σ (hostPar H T pz piG).J) ≠ 0 :=
  host_relIndex_ne_zero H T pz piG h S

end Host

end Formalism.MainNotions.Gaps.CC.Idx

end
