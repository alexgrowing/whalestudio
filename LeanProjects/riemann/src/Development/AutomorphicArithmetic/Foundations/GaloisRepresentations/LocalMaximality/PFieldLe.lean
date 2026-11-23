import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KahlerFormsOverSubalgebraClosurePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLaurentConstantTermFormFunctionFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTopDegreeCoefficientFormAndEqOnTopFormsStatement
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 GlobalTheory.W1.Lef UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma lft_uni' {ι κ : Type} [LinearOrder ι] [LinearOrder κ] (I : Finset ι) (J : Finset κ) :
    lft (uni I J) = I := by
  ext a
  simp [lft, uni]

private lemma rgt_uni' {ι κ : Type} [LinearOrder ι] [LinearOrder κ] (I : Finset ι) (J : Finset κ) :
    rgt (uni I J) = J := by
  ext a
  simp [rgt, uni]

private lemma card_uni' {ι κ : Type} [LinearOrder ι] [LinearOrder κ] (I : Finset ι) (J : Finset κ) :
    (uni I J).card = I.card + J.card := by
  simp [uni]

private lemma omB_mono' {L : Type} [Field L] [Algebra ℂ L] {B B' : Subalgebra ℂ L} (h : B ≤ B') (q : ℕ) :
    omB ℂ L B q ≤ omB ℂ L B' q := by
  refine Submodule.span_mono ?_
  rintro y ⟨b, hb, v, hv, rfl⟩
  exact ⟨b, h hb, v, fun j => h (hv j), rfl⟩

private lemma lft_mono' {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {s t : Finset (ι ⊕ₗ κ)} (h : s ⊆ t) :
    lft s ⊆ lft t := by
  intro a ha
  simp only [lft, Finset.mem_toLeft, Finset.mem_map] at ha ⊢
  obtain ⟨u, hu, e⟩ := ha
  exact ⟨u, h hu, e⟩

private lemma rgt_mono' {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {s t : Finset (ι ⊕ₗ κ)} (h : s ⊆ t) :
    rgt s ⊆ rgt t := by
  intro a ha
  simp only [rgt, Finset.mem_toRight, Finset.mem_map] at ha ⊢
  obtain ⟨u, hu, e⟩ := ha
  exact ⟨u, h hu, e⟩

private lemma card_split' {ι : Type} [LinearOrder ι] (u : Finset ι) {j : ι} (hj : j ∈ u) :
    (u.filter (· ≤ j)).card + (u.filter (j ≤ ·)).card = u.card + 1 := by
  have h1 := Finset.card_filter_add_card_filter_not (s := u) (fun i => i ≤ j)
  have h2 : u.filter (j ≤ ·) = insert j (u.filter (fun i => ¬ i ≤ j)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_insert, not_le]
    constructor
    · rintro ⟨hi, hji⟩
      rcases hji.eq_or_lt with h | h
      · exact Or.inl h.symm
      · exact Or.inr ⟨hi, h⟩
    · rintro (rfl | ⟨hi, h⟩)
      · exact ⟨hj, le_rfl⟩
      · exact ⟨hi, h.le⟩
  rw [h2, Finset.card_insert_of_notMem (by simp)]
  omega

private lemma cechC_iff' {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E] {A : Finset ι → Submodule ℂ E}
    {n : ℤ} {c : Finset ι → E} :
    c ∈ cechC A n ↔ ∀ s, c s ∈ (if s.Nonempty ∧ (s.card : ℤ) = n + 1 then A s else ⊥ : Submodule ℂ E) :=
  ⟨fun h s => h s trivial, fun h s _ => h s⟩

private lemma cupE_mem' {ι E E' E'' : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']
    [AddCommGroup E''] [Module ℂ E''] (μ : E →ₗ[ℂ] E' →ₗ[ℂ] E'')
    (A : Finset ι → Submodule ℂ E) (B : Finset ι → Submodule ℂ E') (H : Finset ι → Submodule ℂ E'') (q p n : ℤ)
    (hn : q + p = n)
    (hH : ∀ s t u : Finset ι, s.Nonempty → t.Nonempty → s ⊆ u → t ⊆ u → ∀ y ∈ A s, ∀ y' ∈ B t, μ y y' ∈ H u)
    (a : Finset ι → E) (b : Finset ι → E') (ha : a ∈ cechC A q) (hb : b ∈ cechC B p) : cupE μ a b ∈ cechC H n := by
  refine cechC_iff'.2 fun u => ?_
  have key : ∀ j ∈ u, (u.filter (· ≤ j)).Nonempty ∧ ((u.filter (· ≤ j)).card : ℤ) = q + 1 →
      (u.filter (j ≤ ·)).Nonempty ∧ ((u.filter (j ≤ ·)).card : ℤ) = p + 1 →
      (u.Nonempty ∧ (u.card : ℤ) = n + 1) := by
    intro j hj c1 c2
    have := card_split' u hj
    exact ⟨⟨j, hj⟩, by omega⟩
  have zero : ∀ j ∈ u, ¬ ((u.filter (· ≤ j)).Nonempty ∧ ((u.filter (· ≤ j)).card : ℤ) = q + 1 ∧
      (u.filter (j ≤ ·)).Nonempty ∧ ((u.filter (j ≤ ·)).card : ℤ) = p + 1) →
      μ (a (u.filter (· ≤ j))) (b (u.filter (j ≤ ·))) = 0 := by
    intro j _ hc
    have h1 := cechC_iff'.1 ha (u.filter (· ≤ j))
    have h2 := cechC_iff'.1 hb (u.filter (j ≤ ·))
    by_cases c1 : (u.filter (· ≤ j)).Nonempty ∧ ((u.filter (· ≤ j)).card : ℤ) = q + 1
    · have c2 : ¬ ((u.filter (j ≤ ·)).Nonempty ∧ ((u.filter (j ≤ ·)).card : ℤ) = p + 1) :=
        fun c2 => hc ⟨c1.1, c1.2, c2.1, c2.2⟩
      rw [if_neg c2, Submodule.mem_bot] at h2
      rw [h2, map_zero]
    · rw [if_neg c1, Submodule.mem_bot] at h1
      rw [h1, map_zero, LinearMap.zero_apply]
  by_cases hu : u.Nonempty ∧ (u.card : ℤ) = n + 1
  · rw [if_pos hu]
    refine Submodule.sum_mem _ fun j hj => ?_
    by_cases c : (u.filter (· ≤ j)).Nonempty ∧ ((u.filter (· ≤ j)).card : ℤ) = q + 1 ∧
        (u.filter (j ≤ ·)).Nonempty ∧ ((u.filter (j ≤ ·)).card : ℤ) = p + 1
    · have h1 := cechC_iff'.1 ha (u.filter (· ≤ j))
      have h2 := cechC_iff'.1 hb (u.filter (j ≤ ·))
      rw [if_pos ⟨c.1, c.2.1⟩] at h1
      rw [if_pos c.2.2] at h2
      exact hH _ _ _ c.1 c.2.2.1 (Finset.filter_subset _ _) (Finset.filter_subset _ _) _ h1 _ h2
    · rw [zero j hj c]
      exact Submodule.zero_mem _
  · rw [if_neg hu, Submodule.mem_bot]
    refine Finset.sum_eq_zero fun j hj => zero j hj fun c => hu (key j hj ⟨c.1, c.2.1⟩ c.2.2)

private lemma alt_trace' (hTL : TrLin) {M : Type} [AddCommGroup M] [Module ℂ M] (C : Cx ℂ M)
    (u : ∀ p : ℕ, C.H p →ₗ[ℂ] C.H p) (d m : ℕ) (p : Fin m → ℕ) (f g : Fin m → M) (φ : Fin m → M →ₗ[ℂ] ℂ)
    (hpd : ∀ k, p k ≤ d) (hf : ∀ k, f k ∈ C.Z (p k)) (hg : ∀ k, g k ∈ C.Z (p k))
    (hφ : ∀ k, ∀ y ∈ C.B (p k), φ k y = 0)
    (hid : ∀ q : ℕ, ∀ α ∈ C.Z q, α - ∑ k ∈ Finset.univ.filter (fun k => p k = q), φ k α • f k ∈ C.B q)
    (hu : ∀ k, u (p k) (Submodule.Quotient.mk ⟨f k, hf k⟩) = Submodule.Quotient.mk ⟨g k, hg k⟩) :
    ∑ q ∈ Finset.range (d + 1), (-1 : ℂ) ^ q * LinearMap.trace ℂ _ (u q) = ∑ k, (-1 : ℂ) ^ p k * φ k (g k) := by
  have key : ∀ q : ℕ, LinearMap.trace ℂ _ (u q) = ∑ k ∈ Finset.univ.filter (fun k => p k = q), φ k (g k) := by
    intro q
    let φ' : {k // p k = q} → C.H q →ₗ[ℂ] ℂ := fun k =>
      Submodule.liftQ _ ((φ k.1).comp (C.Z q).subtype) (by
        intro y hy
        have h1 : (y : M) ∈ C.B q := hy
        have h2 := hφ k.1 y.1 (by rw [k.2]; exact h1)
        simpa using h2)
    have hfq : ∀ k : {k // p k = q}, f k.1 ∈ C.Z q := fun k => by
      have := hf k.1
      rwa [k.2] at this
    let v : {k // p k = q} → C.H q := fun k => Submodule.Quotient.mk ⟨f k.1, hfq k⟩
    have hdec : ∀ y, y = ∑ k, φ' k y • v k := by
      intro y
      induction y using Submodule.Quotient.induction_on with
      | H α =>
        have e : ∑ k, φ' k (Submodule.Quotient.mk α) • v k =
            ((C.B q).submoduleOf (C.Z q)).mkQ (∑ k : {k // p k = q}, φ k.1 α.1 • (⟨f k.1, hfq k⟩ : C.Z q)) := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [map_smul]
          rfl
        rw [e, Submodule.mkQ_apply, Submodule.Quotient.eq]
        show ((α - ∑ k : {k // p k = q}, φ k.1 α.1 • (⟨f k.1, hfq k⟩ : C.Z q) : C.Z q) : M) ∈ C.B q
        have h := hid q α.1 α.2
        rw [Finset.sum_subtype (Finset.univ.filter fun k => p k = q) (p := fun k => p k = q) (by simp)] at h
        simpa using h
    rw [(hTL (C.H q) {k // p k = q} φ' v hdec).2 (u q),
      Finset.sum_subtype (Finset.univ.filter fun k => p k = q) (p := fun k => p k = q) (by simp)]
    refine Finset.sum_congr rfl ?_
    rintro ⟨k, rfl⟩ -
    show φ' ⟨k, rfl⟩ (u (p k) (Submodule.Quotient.mk ⟨f k, hf k⟩)) = φ k (g k)
    rw [hu k]
    rfl
  calc ∑ q ∈ Finset.range (d + 1), (-1 : ℂ) ^ q * LinearMap.trace ℂ _ (u q)
      = ∑ q ∈ Finset.range (d + 1), ∑ k ∈ Finset.univ.filter (fun k => p k = q), (-1 : ℂ) ^ p k * φ k (g k) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [key, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [(Finset.mem_filter.1 hk).2]
    _ = ∑ k, (-1 : ℂ) ^ p k * φ k (g k) :=
        Finset.sum_fiberwise_of_maps_to (fun k _ => Finset.mem_range.2 (Nat.lt_succ_of_le (hpd k))) _

private lemma edge_id' {ι κ E : Type} [LinearOrder ι] [LinearOrder κ] [AddCommGroup E] {n : Type} [Fintype n]
    (ε : n → ℤ) (C : n → Finset ι → E) (l : Finset ι → E) (G : Finset (ι ⊕ₗ κ) → E) (J : n → Finset (ι ⊕ₗ κ) → E) :
    edge1 (∑ k, ε k • C k - l) =
      (G - edge1 l) - (G - ∑ k, J k) - ∑ k, (J k - ε k • edge1 (C k)) := by
  funext s
  simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, edge1, Finset.sum_sub_distrib]
  by_cases hs : (rgt s).card = 1
  · simp only [hs, if_true]
    abel
  · simp [hs]

section Forms
variable {K L : Type} [Field K] [Field L] [Algebra ℂ K] [Algebra ℂ L] [Algebra K L] [IsScalarTower ℂ K L]

private lemma mapDR_ιMulti' (q : ℕ) (v : Fin q → K) :
    mapDR ℂ K L (ExteriorAlgebra.ιMulti K q fun j => D ℂ K (v j)) =
      ExteriorAlgebra.ιMulti L q fun j => D ℂ L (algebraMap K L (v j)) := by
  induction q with
  | zero => rw [ExteriorAlgebra.ιMulti_zero_apply, ExteriorAlgebra.ιMulti_zero_apply, map_one]
  | succ q ih =>
    rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_succ_apply, map_mul]
    have ht : Matrix.vecTail (fun j => D ℂ K (v j)) = fun j => D ℂ K (v j.succ) := rfl
    have ht' : Matrix.vecTail (fun j => D ℂ L (algebraMap K L (v j))) =
        fun j => D ℂ L (algebraMap K L (v j.succ)) := rfl
    rw [ht, ht', ih (fun j => v j.succ)]
    congr 1
    simp only [mapDR, ExteriorAlgebra.lift_ι_apply]
    simp [map1, KaehlerDifferential.map_D]

private lemma mapL_mem' (B : Subalgebra ℂ K) (B' : Subalgebra ℂ L) (h : ∀ y ∈ B, algebraMap K L y ∈ B') (n : ℕ) :
    ∀ y ∈ omB ℂ K B n, mapL K L y ∈ omB ℂ L B' n := by
  have hle : omB ℂ K B n ≤ (omB ℂ L B' n).comap (mapL K L) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, hb, v, hv, rfl⟩
    refine Submodule.subset_span ⟨algebraMap K L b, h b hb, fun j => algebraMap K L (v j), fun j => h _ (hv j), ?_⟩
    show mapDR ℂ K L (b • _) = _
    rw [map_smul, mapDR_ιMulti', algebraMap_smul]
  exact fun y hy => hle hy

private lemma mapC_Z' {ι : Type} [LinearOrder ι] (B : Finset ι → Subalgebra ℂ K) (B' : Finset ι → Subalgebra ℂ L)
    (h : ∀ I, ∀ y ∈ B I, algebraMap K L y ∈ B' I) (q : ℕ) (n : ℤ) (c : Finset ι → DR ℂ K)
    (hc : c ∈ (omCx B q).Z n) : (fun I => mapDR ℂ K L (c I)) ∈ (omCx B' q).Z n := by
  obtain ⟨hC, hD⟩ := Submodule.mem_inf.1 hc
  refine Submodule.mem_inf.2 ⟨cechC_iff'.2 fun s => ?_, ?_⟩
  · have h1 := cechC_iff'.1 hC s
    by_cases hs : s.Nonempty ∧ (s.card : ℤ) = n + 1
    · rw [if_pos hs] at h1 ⊢
      exact mapL_mem' _ _ (h s) q _ h1
    · rw [if_neg hs, Submodule.mem_bot] at h1 ⊢
      rw [h1, map_zero]
  · have hD' : GlobalTheory.DI.delta c = 0 := hD
    show GlobalTheory.DI.delta (fun I => mapDR ℂ K L (c I)) = 0
    funext t
    have := congrFun hD' t
    simp only [GlobalTheory.DI.delta, Pi.zero_apply] at this ⊢
    have h2 := congrArg (mapL K L) this
    simpa only [map_sum, map_zsmul, map_zero, mapL_apply] using h2

end Forms

theorem UpperTheory.Gal.productCup_of_system.fieldLe_of :
    ZFam → ZEx → ZId → PrB → YMain → GMap → LCupRel → EdgeB → TrTop → ResidueOfTraceIsFiberSum → TrLin → SysBasic → RYBasic → OmLoc → FieldLe := by
  intro hZF hZEx hZId hPrB hYM hGM hLC hEB hTT hRT hTL hSB hRY hOL
  intro F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 Fx A hY a ha u hu
  have h0 : Y0 x j2 := hY.toY0
  have hcZ := h0.covZ
  have hcY := h0.covY
  obtain ⟨τ, hτ⟩ := (GlobalTheory.T.exists_topDegreeCoefficientForm_and_eq_on_top_forms ℂ F K d (xv x) hcZ).1
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.exists_laurentConstantTermForm_functionField ℂ F d (xv x) hcZ.pd
  obtain ⟨m, n, z, hz⟩ := hZF F K d x hcZ
  obtain ⟨c, hc, hD⟩ := hZEx F K d x hcZ τ hτ a ha (Fin m) n z hz
  obtain ⟨h, hh1, hh2, hh3⟩ := hYM F K K' d x j2 Fx A hY τ hτ a ha (Fin m) n z hz c hc hD
  have hc0 : resK inlE c ∈ ((sysZ K x a).cx n11 (sysZ K x a).mu).Z (d + 2) :=
    (hSB d _ _ (sysZ K x a) _ (app n11 n) (app (sysZ K x a).mu z) (d + 2)).2.2.2.2.2 (Mi d) inlE c hc
  obtain ⟨M, p, e, f, hpef, hjoin, hid⟩ := hZId F K d x hcZ τ hτ ρ hρ a ha _ hc0 hD
  choose bt hbt hbtJ hbtC hbtu using fun k => hu (p k) (f k) (hpef k).2.2
  obtain ⟨hRI, -, hRmono, hRmap, -⟩ := hRY F K K' d x j2 h0
  have hgm := (hGM F K K' d x j2 h0 a ha).2.2.2.1 (d + 2) _ hjoin
  have hda : d - a + a = d := Nat.sub_add_cancel ha
  have hrRY : ∀ I J, rB ℂ K' (xv x) I ≤ RY (xv x) j2 I J := fun I J => by
    have := hRmono I I ∅ J subset_rfl (Finset.empty_subset _)
    rwa [hRI] at this
  have hrm : ∀ s w, s ⊆ w → rB ℂ K' (xv x) s ≤ rB ℂ K' (xv x) w := fun s w h => by
    have := hRmono s w ∅ ∅ h subset_rfl
    rwa [hRI, hRI] at this
  let μ : DR ℂ K' →ₗ[ℂ] DR ℂ K' →ₗ[ℂ] DR ℂ K' := LinearMap.mul ℂ (DR ℂ K')
  let aa : Fin M → Finset (Fin (d + 1)) → DR ℂ K' := fun k I => mapDR ℂ K K' (e k I)
  let bb : Fin M → Finset (Fin (d + 1)) → DR ℂ K' := fun k I => bt k (uni I ∅)
  have hmulm : ∀ (B : Subalgebra ℂ K') (p q : ℕ), ∀ y ∈ omB ℂ K' B p, ∀ y' ∈ omB ℂ K' B q, y * y' ∈ omB ℂ K' B (p + q) :=
    fun B p q => (GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties ℂ K' B p q).1
  have haa : ∀ k, aa k ∈ (omCx (rB ℂ K' (xv x)) (d - a)).Z ((d : ℤ) - p k) := fun k =>
    mapC_Z' _ _ (fun I y hy => (hRmap I y hy).1) (d - a) _ _ (hpef k).2.1
  have hbb : ∀ k, bb k ∈ cechC (fun I => omB ℂ K' (rB ℂ K' (xv x) I) a) (p k) := by
    intro k
    refine cechC_iff'.2 fun I => ?_
    have h1 := cechC_iff'.1 (Submodule.mem_inf.1 (hbt k)).1 (uni I ∅)
    have hcard : (uni I (∅ : Finset (Fin (d + 1)))).card = I.card := by simp [card_uni']
    by_cases hI : I.Nonempty ∧ (I.card : ℤ) = p k + 1
    · have c : (uni I (∅ : Finset (Fin (d + 1)))).Nonempty ∧
          ((uni I (∅ : Finset (Fin (d + 1)))).card : ℤ) = p k + 1 :=
        ⟨Finset.card_pos.1 (by rw [hcard]; exact Finset.card_pos.2 hI.1), by rw [hcard]; exact hI.2⟩
      rw [if_pos c, lft_uni', rgt_uni', hRI] at h1
      rw [if_pos hI]
      exact h1
    · have c : ¬ ((uni I (∅ : Finset (Fin (d + 1)))).Nonempty ∧
          ((uni I (∅ : Finset (Fin (d + 1)))).card : ℤ) = p k + 1) := fun c =>
        hI ⟨Finset.card_pos.1 (by rw [← hcard]; exact Finset.card_pos.2 c.1), by rw [← hcard]; exact c.2⟩
      rw [if_neg c] at h1
      rw [if_neg hI]
      exact h1
  have hcond : ∀ (I J I' : Finset (Fin (d + 1))) (s : Finset (Two d)), J.Nonempty → I'.Nonempty → s.Nonempty → I' ⊆ I →
      s ⊆ uni I J → ∀ y ∈ omB ℂ K' (rB ℂ K' (xv x) I') (d - a), ∀ y' ∈ omB ℂ K' (RY (xv x) j2 (lft s) (rgt s)) a,
      μ y y' ∈ omB ℂ K' (RY (xv x) j2 I J) d := by
    intro I J I' s _ _ _ hI hs y hy y' hy'
    have e1 : y ∈ omB ℂ K' (RY (xv x) j2 I J) (d - a) :=
      omB_mono' ((hrm _ _ hI).trans (hrRY I J)) _ hy
    have e2 : y' ∈ omB ℂ K' (RY (xv x) j2 I J) a :=
      omB_mono' (hRmono _ _ _ _ (by simpa only [lft_uni'] using lft_mono' hs)
        (by simpa only [rgt_uni'] using rgt_mono' hs)) _ hy'
    have := hmulm _ _ _ y e1 y' e2
    rwa [hda] at this
  have hlc : ∀ k, join μ (aa k) (fun J => bt k (uni ∅ J)) - ((-1 : ℤ) ^ p k) • edge1 (cupE μ (aa k) (bb k)) ∈
      (sysY x j2 d).mix.B (d + 2) ∧ deltaL ℂ _ _ (cupE μ (aa k) (bb k)) = 0 := by
    intro k
    have hq : ((d - p k : ℕ) : ℤ) = (d : ℤ) - p k := Nat.cast_sub (hpef k).1
    have := hLC (Fin (d + 1)) (DR ℂ K') (DR ℂ K') (DR ℂ K') μ (fun I => omB ℂ K' (rB ℂ K' (xv x) I) (d - a))
      (fun s => omB ℂ K' (RY (xv x) j2 (lft s) (rgt s)) a) (fun I J => omB ℂ K' (RY (xv x) j2 I J) d) (d - p k) (p k)
      hcond (aa k) (by rw [hq]; exact haa k) (bt k) (hbt k)
    rw [show (((d - p k : ℕ) : ℤ) + p k + 2) = (d : ℤ) + 2 by rw [hq]; ring] at this
    exact this
  have hcupZ : ∀ k, cupE μ (aa k) (bb k) ∈ (omCx (rB ℂ K' (xv x)) d).Z d := by
    intro k
    refine Submodule.mem_inf.2 ⟨cupE_mem' μ (fun I => omB ℂ K' (rB ℂ K' (xv x) I) (d - a))
      (fun I => omB ℂ K' (rB ℂ K' (xv x) I) a) _ ((d : ℤ) - p k) (p k) d (by ring) ?_ (aa k) (bb k)
      (Submodule.mem_inf.1 (haa k)).1 (hbb k), (hlc k).2⟩
    intro s t w _ _ hsw htw y hy y' hy'
    have := hmulm _ _ _ y (omB_mono' (hrm _ _ hsw) _ hy) y' (omB_mono' (hrm _ _ htw) _ hy')
    rwa [hda] at this
  have htop : top (resK inlE c) = top c := by
    funext b
    simp only [top, resK, lft_uni', rgt_uni', Finset.map_empty]
  have hgj : ∀ k, (fun s => gY j2 (join (TensorProduct.mk ℂ _ _) (e k) (f k) s)) =
      join μ (aa k) (fun J => bt k (uni ∅ J)) := by
    intro k
    funext s
    simp only [join, aa, hbtJ]
    simp [gY, μ]
  let Λ : Finset (Fin (d + 1)) → DR ℂ K' := ∑ k, ((-1 : ℤ) ^ p k) • cupE μ (aa k) (bb k)
  have hΛZ : Λ ∈ (omCx (rB ℂ K' (xv x)) d).Z d := Submodule.sum_mem _ fun k _ => zsmul_mem (hcupZ k) _
  have hy := sub_mem hΛZ hh2
  have hedge : edge1 (Λ - locCoch ℂ K' (xv x) h) ∈ (sysY x j2 d).mix.B (d + 2) := by
    have hP : (fun s => gY j2 ((top (resK inlE c) - ∑ k, join (TensorProduct.mk ℂ _ _) (e k) (f k)) s)) =
        (fun s => gY j2 (top c s)) - ∑ k, join μ (aa k) (fun J => bt k (uni ∅ J)) := by
      funext s
      rw [htop, Pi.sub_apply, Pi.sub_apply, Finset.sum_apply, Finset.sum_apply, map_sub, map_sum]
      congr 1
      exact Finset.sum_congr rfl fun k _ => congrFun (hgj k) s
    rw [hP] at hgm
    rw [edge_id' (fun k => (-1 : ℤ) ^ p k) (fun k => cupE μ (aa k) (bb k)) _ (fun s => gY j2 (top c s))
      (fun k => join μ (aa k) (fun J => bt k (uni ∅ J)))]
    exact sub_mem (sub_mem hh1 hgm) (Submodule.sum_mem _ fun k _ => (hlc k).1)
  have hB := hEB F K K' d x j2 h0 _ hy hedge
  obtain ⟨hT1, hT2, hT3⟩ := hTT F K K' d x j2 h0 τ hτ ρ hρ
  have hz0 := hT3 _ hB
  have hl : locCoch ℂ K' (xv x) h Finset.univ = (h : K') • vol0 ℂ K' (xv x) := by simp [locCoch]
  have hΛv : trF ℂ τ ρ (trDR ℂ K K' (Λ Finset.univ)) = ∑ e ∈ Fx, locTerm (A e) a := by
    rw [Pi.sub_apply, map_sub, map_sub, sub_eq_zero, hl, hT2] at hz0
    rw [hz0, hRT F K' d x hcY h0.red ρ hρ h, hh3]
  have hterm : ∀ k, trF ℂ τ ρ (trDR ℂ K K' (cupE μ (aa k) (bb k) Finset.univ)) =
      pr K τ ρ (e k) (trC (k := ℂ) (K := K) (L := K') (bb k)) := by
    intro k
    simp only [cupE, map_sum, cupPair, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [μ, aa, LinearMap.mul_apply', hT1]
    simp [trC]
  rw [alt_trace' hTL (omCx (rB ℂ K (xv x)) a) u d M p f (fun k => trC (k := ℂ) (K := K) (L := K') (bb k))
    (fun k => pr K τ ρ (e k)) (fun k => (hpef k).1) (fun k => (hpef k).2.2) hbtC
    (fun k y hy => hPrB F K d x hcZ τ hτ ρ hρ a (p k) ha (hpef k).1 (e k) (hpef k).2.1 y hy) hid hbtu, ← hΛv]
  simp only [Λ, Finset.sum_apply, Pi.smul_apply, map_sum, map_zsmul, hterm]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp
