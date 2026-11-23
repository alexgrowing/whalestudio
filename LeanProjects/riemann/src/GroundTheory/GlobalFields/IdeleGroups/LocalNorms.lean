import Mathlib
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.CompletionsOverBasisRepr
import GroundTheory.GlobalFields.IdeleGroups.Restricted
import GroundTheory.GlobalFields.Adele.BaseChange.FiniteMap

namespace GroundTheory.Global

open IsDedekindDomain NumberField Filter
open AdeleBaseChange SemiLocal
open scoped NumberField.AdeleRing NumberField.LiesOver

noncomputable section

namespace IdeleNorm

variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L]
  [Algebra K L]

def finiteLocalNorm (v : HeightOneSpectrum (𝓞 K)) :
    ((w : PlacesOver L v) → (w.1.adicCompletion L)ˣ) →* (v.adicCompletion K)ˣ where
  toFun y := ∏ w, Units.map (Algebra.norm (v.adicCompletion K) :
    w.1.adicCompletion L →* v.adicCompletion K) (y w)
  map_one' := by simp
  map_mul' y z := by simp only [Pi.mul_apply, map_mul, Finset.prod_mul_distrib]

variable {L} in

theorem coe_finiteLocalNorm (v : HeightOneSpectrum (𝓞 K))
    (y : (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ) :
    ((finiteLocalNorm L v y : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
      ∏ w, Algebra.norm (v.adicCompletion K) (y w : w.1.adicCompletion L) := by
  simp [finiteLocalNorm, Units.coe_prod]

def integerUnitsOver (v : HeightOneSpectrum (𝓞 K)) :
    Subgroup ((w : PlacesOver L v) → (w.1.adicCompletion L)ˣ) :=
  Subgroup.pi Set.univ fun w ↦ (Submonoid.ofClass (w.1.adicCompletionIntegers L)).units

omit [NumberField K] in
variable {L} in

theorem mem_integerUnitsOver {v : HeightOneSpectrum (𝓞 K)}
    {y : (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ} :
    y ∈ integerUnitsOver L v ↔
      ∀ w, y w ∈ (Submonoid.ofClass (w.1.adicCompletionIntegers L)).units := by
  simp [integerUnitsOver, Subgroup.mem_pi]

open scoped Classical in

def infiniteLocalNorm (v : InfinitePlace K) :
    ((w : v.placesOver L) → ((w : InfinitePlace L).Completion)ˣ) →* (v.Completion)ˣ where
  toFun y := ∏ w : v.placesOver L, Units.map (Algebra.norm v.Completion :
    (w : InfinitePlace L).Completion →* v.Completion) (y w)
  map_one' := by simp
  map_mul' y z := by simp only [Pi.mul_apply, map_mul, Finset.prod_mul_distrib]

omit [NumberField K] in
open scoped Classical in
variable {L} in

theorem coe_infiniteLocalNorm (v : InfinitePlace K)
    (y : (w : v.placesOver L) → ((w : InfinitePlace L).Completion)ˣ) :
    ((infiniteLocalNorm L v y : (v.Completion)ˣ) : v.Completion) =
      ∏ w : v.placesOver L, Algebra.norm v.Completion (y w : (w : InfinitePlace L).Completion) := by
  simp [infiniteLocalNorm, Units.coe_prod]

variable {L}

theorem finiteProj_ideleNorm (y : IdeleGroup L) (v : HeightOneSpectrum (𝓞 K)) :
    IdeleGroup.finiteProj v (ideleNorm K L y) =
      finiteLocalNorm L v (fun w ↦ IdeleGroup.finiteProj w.1 y) := by
  ext
  rw [IdeleGroup.coe_finiteProj, coe_finiteLocalNorm, ideleNorm_snd]
  simp only [IdeleGroup.coe_finiteProj]

theorem infiniteProj_ideleNorm (y : IdeleGroup L) (v : InfinitePlace K) :
    IdeleGroup.infiniteProj v (ideleNorm K L y) =
      infiniteLocalNorm L v (fun w ↦ IdeleGroup.infiniteProj (w : InfinitePlace L) y) := by
  classical
  apply Units.ext
  rw [IdeleGroup.coe_infiniteProj, coe_infiniteLocalNorm, ideleNorm_fst]
  simp only [IdeleGroup.coe_infiniteProj]

theorem eventually_finiteProj_mem (y : IdeleGroup L) :
    ∀ᶠ w in cofinite,
      IdeleGroup.finiteProj w y ∈ (Submonoid.ofClass (w.adicCompletionIntegers L)).units := by
  refine (IdeleGroup.prodRestrictedEquiv L y).2.2.mono fun w hw ↦ ?_
  have e : IdeleGroup.finiteProj w y = (IdeleGroup.prodRestrictedEquiv L y).2 w :=
    Units.ext (by simp)
  rw [e]
  exact hw

omit [NumberField K] [NumberField L] in
variable (K) in

theorem eventually_forall_placesOver {P : HeightOneSpectrum (𝓞 L) → Prop}
    (h : ∀ᶠ w in cofinite, P w) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in cofinite, ∀ w : PlacesOver L v, P w.1 := by
  rw [eventually_cofinite] at h ⊢
  refine (h.image (below K)).subset fun v hv ↦ ?_
  simp only [Set.mem_ofPred_eq, not_forall] at hv
  obtain ⟨w, hw⟩ := hv
  exact ⟨w.1, hw, (below_eq_iff w.1 v).2 w.2⟩

omit [NumberField K] in

theorem placesOver_congr (yf : ∀ v : HeightOneSpectrum (𝓞 K),
      (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ)
    {v v' : HeightOneSpectrum (𝓞 K)} (h : v' = v) (w : HeightOneSpectrum (𝓞 L))
    (hw : w.asIdeal.LiesOver v.asIdeal) (hw' : w.asIdeal.LiesOver v'.asIdeal) :
    yf v' ⟨w, hw'⟩ = yf v ⟨w, hw⟩ := by
  subst h
  rfl

omit [NumberField K] [NumberField L] in

theorem infinitePlacesOver_congr (yi : ∀ v : InfinitePlace K,
      (w : v.placesOver L) → ((w : InfinitePlace L).Completion)ˣ)
    {v v' : InfinitePlace K} (h : v' = v) (w : InfinitePlace L)
    (hw : w ∈ v.placesOver L) (hw' : w ∈ v'.placesOver L) :
    yi v' ⟨w, hw'⟩ = yi v ⟨w, hw⟩ := by
  subst h
  rfl

def glue (yf : ∀ v : HeightOneSpectrum (𝓞 K), (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ)
    (hyf : ∀ᶠ v in cofinite, yf v ∈ integerUnitsOver L v)
    (yi : ∀ v : InfinitePlace K, (w : v.placesOver L) → ((w : InfinitePlace L).Completion)ˣ) :
    IdeleGroup L :=
  (IdeleGroup.prodRestrictedEquiv L).symm
    (MulEquiv.piUnits.symm fun w : InfinitePlace L ↦
        yi (w.comap (algebraMap K L)) ⟨w, (inferInstance : w.LiesOver (w.comap (algebraMap K L)))⟩,
      ⟨fun w ↦ yf (below K w) ⟨w, inferInstance⟩,
        ((tendsto_below (K := K) (L := L)).eventually hyf).mono fun w hw ↦
          mem_integerUnitsOver.1 hw ⟨w, inferInstance⟩⟩)

theorem glue_snd (yf : ∀ v : HeightOneSpectrum (𝓞 K),
      (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ)
    (hyf : ∀ᶠ v in cofinite, yf v ∈ integerUnitsOver L v)
    (yi : ∀ v : InfinitePlace K, (w : v.placesOver L) → ((w : InfinitePlace L).Completion)ˣ)
    (v : HeightOneSpectrum (𝓞 K)) (w : PlacesOver L v) :
    ((glue yf hyf yi : 𝔸[L]).2 w.1) = (yf v w : w.1.adicCompletion L) := by
  rw [← IdeleGroup.prodRestrictedEquiv_apply_snd, glue, ContinuousMulEquiv.apply_symm_apply]
  exact congrArg Units.val (placesOver_congr yf ((below_eq_iff w.1 v).2 w.2) w.1 w.2 _)

theorem glue_fst (yf : ∀ v : HeightOneSpectrum (𝓞 K),
      (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ)
    (hyf : ∀ᶠ v in cofinite, yf v ∈ integerUnitsOver L v)
    (yi : ∀ v : InfinitePlace K, (w : v.placesOver L) → ((w : InfinitePlace L).Completion)ˣ)
    (v : InfinitePlace K) (w : v.placesOver L) :
    ((glue yf hyf yi : 𝔸[L]).1 w) = (yi v w : (w : InfinitePlace L).Completion) := by
  rw [← IdeleGroup.prodRestrictedEquiv_apply_fst, glue, ContinuousMulEquiv.apply_symm_apply]
  have := infinitePlacesOver_congr yi (InfinitePlace.LiesOver.comap_eq (w : InfinitePlace L) v)
    (w : InfinitePlace L) w.2
    (inferInstance : (w : InfinitePlace L).LiesOver ((w : InfinitePlace L).comap (algebraMap K L)))
  exact congrArg Units.val this

theorem ideleNorm_glue (yf : ∀ v : HeightOneSpectrum (𝓞 K),
      (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ)
    (hyf : ∀ᶠ v in cofinite, yf v ∈ integerUnitsOver L v)
    (yi : ∀ v : InfinitePlace K, (w : v.placesOver L) → ((w : InfinitePlace L).Completion)ˣ)
    {x : IdeleGroup K} (hf : ∀ v, finiteLocalNorm L v (yf v) = IdeleGroup.finiteProj v x)
    (hi : ∀ v, infiniteLocalNorm L v (yi v) = IdeleGroup.infiniteProj v x) :
    ideleNorm K L (glue yf hyf yi) = x := by
  classical
  apply Units.ext
  refine Prod.ext (funext fun v ↦ ?_) (FiniteAdeleRing.ext (K := K) fun v ↦ ?_)
  · rw [ideleNorm_fst, ← IdeleGroup.coe_infiniteProj, ← hi v, coe_infiniteLocalNorm]
    exact Finset.prod_congr rfl fun w _ ↦ by rw [glue_fst]
  · rw [ideleNorm_snd, ← IdeleGroup.coe_finiteProj, ← hf v, coe_finiteLocalNorm]
    exact Finset.prod_congr rfl fun w _ ↦ by rw [glue_snd]

theorem mem_range_ideleNorm (x : IdeleGroup K)
    (hfin : ∀ v, IdeleGroup.finiteProj v x ∈ (finiteLocalNorm L v).range)
    (hinf : ∀ v, IdeleGroup.infiniteProj v x ∈ (infiniteLocalNorm L v).range)
    (hint : ∀ᶠ v in cofinite,
      IdeleGroup.finiteProj v x ∈ (integerUnitsOver L v).map (finiteLocalNorm L v)) :
    x ∈ (ideleNorm K L).range := by
  classical
  let yf : ∀ v : HeightOneSpectrum (𝓞 K), (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ :=
    fun v ↦ if h : IdeleGroup.finiteProj v x ∈ (integerUnitsOver L v).map (finiteLocalNorm L v)
      then (Subgroup.mem_map.1 h).choose else (MonoidHom.mem_range.1 (hfin v)).choose
  have hyf_int : ∀ᶠ v in cofinite, yf v ∈ integerUnitsOver L v := hint.mono fun v h ↦ by
    simp only [yf, dif_pos h]
    exact (Subgroup.mem_map.1 h).choose_spec.1
  have hyf : ∀ v, finiteLocalNorm L v (yf v) = IdeleGroup.finiteProj v x := by
    intro v
    by_cases h : IdeleGroup.finiteProj v x ∈ (integerUnitsOver L v).map (finiteLocalNorm L v)
    · simp only [yf, dif_pos h]
      exact (Subgroup.mem_map.1 h).choose_spec.2
    · simp only [yf, dif_neg h]
      exact (MonoidHom.mem_range.1 (hfin v)).choose_spec
  exact ⟨glue yf hyf_int (fun v ↦ (MonoidHom.mem_range.1 (hinf v)).choose),
    ideleNorm_glue _ _ _ hyf fun v ↦ (MonoidHom.mem_range.1 (hinf v)).choose_spec⟩

theorem mem_range_ideleNorm_iff (x : IdeleGroup K) :
    x ∈ (ideleNorm K L).range ↔
      (∀ v, IdeleGroup.finiteProj v x ∈ (finiteLocalNorm L v).range) ∧
      (∀ v, IdeleGroup.infiniteProj v x ∈ (infiniteLocalNorm L v).range) ∧
      ∀ᶠ v in cofinite,
        IdeleGroup.finiteProj v x ∈ (integerUnitsOver L v).map (finiteLocalNorm L v) := by
  refine ⟨?_, fun ⟨h1, h2, h3⟩ ↦ mem_range_ideleNorm x h1 h2 h3⟩
  rintro ⟨y, rfl⟩
  refine ⟨fun v ↦ ⟨_, (finiteProj_ideleNorm y v).symm⟩,
    fun v ↦ ⟨_, (infiniteProj_ideleNorm y v).symm⟩, ?_⟩
  refine (eventually_forall_placesOver K (eventually_finiteProj_mem y)).mono fun v hv ↦ ?_
  exact ⟨_, mem_integerUnitsOver.2 hv, (finiteProj_ideleNorm y v).symm⟩

end IdeleNorm

end

end GroundTheory.Global
