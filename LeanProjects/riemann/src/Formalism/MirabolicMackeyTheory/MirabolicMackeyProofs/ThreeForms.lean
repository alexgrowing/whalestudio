import Formalism.MirabolicMackeyTheory.StatementL
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.IdxRules
import Formalism.HermitianLattices.HermitianLatticesProofs.LocBasic
import Formalism.HermitianLattices.HermitianLatticesProofs.IndexBasic
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ImageLcv
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.IdxChange
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic

open Module NumberField IsDedekindDomain Formalism.HermitianLatticesTheory

noncomputable section

namespace Formalism.EigenvalueLevelCeiling

open Formalism.DivisionValues

namespace ThreeFormsAlt

section Len

variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]

def qlen (X Y : Submodule R W) : ℕ∞ := Module.length R (↥X ⧸ Y.comap X.subtype)

theorem qlen_congr (X : Submodule R W) {Y Y' : Submodule R W} (h : ∀ x ∈ X, x ∈ Y ↔ x ∈ Y') :
    qlen X Y = qlen X Y' := by
  have : Y.comap X.subtype = Y'.comap X.subtype := by
    ext ⟨x, hx⟩
    exact h x hx
  unfold qlen
  rw [this]

theorem qlen_inf_self (X Y : Submodule R W) : qlen X (X ⊓ Y) = qlen X Y :=
  qlen_congr X (fun _ hx => ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩)

theorem qlen_eq_zero {X Y : Submodule R W} (h : X ≤ Y) : qlen X Y = 0 := by
  have : Y.comap X.subtype = ⊤ := by
    ext ⟨x, hx⟩
    simp [h hx]
  unfold qlen
  rw [this]
  simp

theorem qlen_mono_left {X' X : Submodule R W} (h : X' ≤ X) (Y : Submodule R W) :
    qlen X' Y ≤ qlen X Y := by
  unfold qlen
  let f : (↥X' ⧸ Y.comap X'.subtype) →ₗ[R] (↥X ⧸ Y.comap X.subtype) :=
    Submodule.mapQ _ _ (Submodule.inclusion h) (by
      intro x hx
      simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_inclusion] at hx ⊢
      exact hx)
  refine Module.length_le_of_injective f ?_
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro y hy
  induction y using Submodule.Quotient.induction_on with
  | H x =>
    rw [LinearMap.mem_ker] at hy
    dsimp only [f] at hy
    rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hy
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    exact hy

theorem qlen_le_of_sup {X' X Y : Submodule R W} (h : X' ≤ X) (hs : X ≤ X' ⊔ (X ⊓ Y)) :
    qlen X Y ≤ qlen X' Y := by
  unfold qlen
  let f : (↥X' ⧸ Y.comap X'.subtype) →ₗ[R] (↥X ⧸ Y.comap X.subtype) :=
    Submodule.mapQ _ _ (Submodule.inclusion h) (by
      intro x hx
      simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_inclusion] at hx ⊢
      exact hx)
  refine Module.length_le_of_surjective f ?_
  intro z
  induction z using Submodule.Quotient.induction_on with
  | H x =>
    obtain ⟨x, hx⟩ := x
    obtain ⟨u, hu, t, ht, rfl⟩ := Submodule.mem_sup.mp (hs hx)
    refine ⟨Submodule.Quotient.mk ⟨u, hu⟩, ?_⟩
    dsimp only [f]
    rw [Submodule.mapQ_apply, Submodule.Quotient.eq]
    simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub,
      Submodule.coe_inclusion]
    have : u - (u + t) = -t := by abel
    rw [this]
    exact Y.neg_mem ht.2

theorem qlen_anti_right (X : Submodule R W) {Y Y' : Submodule R W} (h : Y ≤ Y') :
    qlen X Y' ≤ qlen X Y := by
  unfold qlen
  let g : (↥X ⧸ Y.comap X.subtype) →ₗ[R] (↥X ⧸ Y'.comap X.subtype) :=
    Submodule.mapQ _ _ LinearMap.id (fun x hx => h hx)
  refine Module.length_le_of_surjective g ?_
  intro z
  induction z using Submodule.Quotient.induction_on with
  | H x => exact ⟨Submodule.Quotient.mk x, rfl⟩

theorem qlen_add {N M P : Submodule R W} (hNM : N ≤ M) (hMP : M ≤ P) :
    qlen P N = qlen M N + qlen P M :=
  indexBasic_len_add N M P hNM hMP

theorem qlen_map (f : W ≃ₗ[R] W) (X Y : Submodule R W) :
    qlen (X.map (f : W →ₗ[R] W)) (Y.map (f : W →ₗ[R] W)) = qlen X Y :=
  imageLcv_len_map f X Y

theorem lidx_of_le (p : Ideal R) [p.IsPrime] {X Y : Submodule R W} (h : Y ≤ X) :
    lidx p X Y = ((qlen (localization₂ p X) (localization₂ p Y)).toNat : ℤ) := by
  unfold lidx
  rw [inf_eq_right.mpr h, indexBasic_locLen_self]
  simp [locLen, qlen]

end Len

section Sc

variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {Z : Type} [AddCommGroup Z] [Module K Z] [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z]

def scE (a : K) (ha : a ≠ 0) : Z ≃ₗ[𝓞 K] Z :=
  (LinearEquiv.smulOfNeZero K Z a ha).restrictScalars (𝓞 K)

theorem sc_eq_map (a : K) (ha : a ≠ 0) (X : Submodule (𝓞 K) Z) :
    sc a X = X.map ((scE a ha : Z ≃ₗ[𝓞 K] Z) : Z →ₗ[𝓞 K] Z) := by
  ext x
  simp [sc, scE]

theorem mem_sc_inv {a : K} (ha : a ≠ 0) (X : Submodule (𝓞 K) Z) (x : Z) :
    x ∈ sc a⁻¹ X ↔ a • x ∈ X := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [smul_smul, ha] using hy
  · intro h
    exact ⟨a • x, h, by simp [smul_smul, ha]⟩

theorem sc_sc_inv {a : K} (ha : a ≠ 0) (X : Submodule (𝓞 K) Z) : sc a (sc a⁻¹ X) = X := by
  ext x
  have := mem_sc_inv (inv_ne_zero ha) (sc a⁻¹ X) x
  rw [inv_inv] at this
  rw [this, mem_sc_inv ha, smul_smul, mul_inv_cancel₀ ha, one_smul]

theorem localization_sc (p : Ideal (𝓞 K)) [p.IsPrime] {a : K} (ha : a ≠ 0) (X : Submodule (𝓞 K) Z) :
    localization₂ p (sc a X) = sc a (localization₂ p X) := by
  rw [sc_eq_map a ha, sc_eq_map a ha, localization_map']

theorem localization_inf (p : Ideal (𝓞 K)) [p.IsPrime] (X Y : Submodule (𝓞 K) Z) :
    localization₂ p (X ⊓ Y) = localization₂ p X ⊓ localization₂ p Y :=
  locBasic_locS_inf _ X Y

theorem algebraMap_ne_zero_of_notMem (p : Ideal (𝓞 K)) {s : 𝓞 K} (hs : s ∉ p) :
    algebraMap (𝓞 K) K s ≠ 0 := by
  intro h
  have : s = 0 := (FaithfulSMul.algebraMap_injective (𝓞 K) K) (by rw [h, map_zero])
  exact hs (this ▸ p.zero_mem)

theorem localization_sup_eq_localization_dnN (p : Ideal (𝓞 K)) [p.IsPrime] (X Y : Submodule (𝓞 K) Z) :
    localization₂ p (X ⊔ Y) = localization₂ p X ⊔ localization₂ p Y :=
  locBasic_locS_sup (K := K) _ (fun _ hs => algebraMap_ne_zero_of_notMem p hs) X Y

theorem cut_mono (W : Submodule K Z) {X Y : Submodule (𝓞 K) Z} (h : X ≤ Y) : cut W X ≤ cut W Y :=
  inf_le_inf_right _ h

theorem localization_cut (p : Ideal (𝓞 K)) [p.IsPrime] (W : Submodule K Z) (X : Submodule (𝓞 K) Z) :
    localization₂ p (cut W X) = cut W (localization₂ p X) := by
  unfold cut
  rw [localization_inf]
  congr 1
  apply le_antisymm
  · rintro x ⟨s, hs, hx⟩
    have hs0 := algebraMap_ne_zero_of_notMem p hs
    have hx' : (algebraMap (𝓞 K) K s) • x ∈ W := by
      rw [algebraMap_smul]
      exact hx
    have := W.smul_mem (algebraMap (𝓞 K) K s)⁻¹ hx'
    rwa [smul_smul, inv_mul_cancel₀ hs0, one_smul] at this
  · exact locBasic_le_locS _ _

end Sc

section Core

variable {O K Z : Type*} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [ValuationRing O]
  [Field K] [Algebra O K] [IsFractionRing O K] [AddCommGroup Z] [Module K Z] [Module O Z]
  [IsScalarTower O K Z]

theorem split_of_snf (N NB : Submodule O Z) (a : O) (ha : a ≠ 0)
    {ι : Type*} [Fintype ι] {n : ℕ} (snf : Basis.SmithNormalForm (NB.comap N.subtype) ι n) :
    ∃ W : Submodule K Z,
      (∀ x ∈ N, ∃ y ∈ N, ∃ t ∈ N, y ∈ W ∧ a • t ∈ NB ∧ x = y + t) ∧
      (∀ x ∈ W, a • x ∈ N → a • x ∈ NB → x ∈ N) := by
  classical
  let v : ι → Z := fun j => (snf.bM j : Z)
  have hvN : ∀ j, v j ∈ N := fun j => (snf.bM j).2
  have hliA : LinearIndependent O v := snf.bM.linearIndependent.map' N.subtype N.ker_subtype
  have hli : LinearIndependent K v := (LinearIndependent.iff_fractionRing O K).mp hliA
  let good : ι → Prop := fun j => ∃ i, snf.f i = j ∧ snf.a i ∣ a
  have hexp : ∀ (x : Z) (hx : x ∈ N), x = ∑ j, (snf.bM.repr ⟨x, hx⟩ j) • v j := by
    intro x hx
    have := congrArg (N.subtype) (snf.bM.sum_repr ⟨x, hx⟩)
    rw [map_sum] at this
    simpa using this.symm
  have haK : algebraMap O K a ≠ 0 := by
    rw [Ne, FaithfulSMul.algebraMap_eq_zero_iff]
    exact ha
  refine ⟨Submodule.span K (v '' {j | ¬ good j}), ?_, ?_⟩
  · intro x hxN
    refine ⟨∑ j with ¬ good j, (snf.bM.repr ⟨x, hxN⟩ j) • v j, ?_,
      ∑ j with ¬ ¬ good j, (snf.bM.repr ⟨x, hxN⟩ j) • v j, ?_, ?_, ?_, ?_⟩
    · exact Submodule.sum_mem _ (fun j _ => N.smul_mem _ (hvN j))
    · exact Submodule.sum_mem _ (fun j _ => N.smul_mem _ (hvN j))
    · refine Submodule.sum_mem _ (fun j hj => ?_)
      have hj' : ¬ good j := (Finset.mem_filter.mp hj).2
      rw [← algebraMap_smul K]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj', rfl⟩)
    · rw [Finset.smul_sum]
      refine Submodule.sum_mem _ (fun j hj => ?_)
      have hj' : good j := not_not.mp (Finset.mem_filter.mp hj).2
      obtain ⟨i, rfl, d, hd⟩ := hj'
      have h1 : (((snf.bN i : ↥(NB.comap N.subtype)) : N) : Z) ∈ NB := (snf.bN i).2
      rw [snf.snf i, Submodule.coe_smul] at h1
      have h2 : a • ((snf.bM.repr ⟨x, hxN⟩ (snf.f i)) • v (snf.f i)) =
          ((snf.bM.repr ⟨x, hxN⟩ (snf.f i)) * d) • (snf.a i • (snf.bM (snf.f i) : Z)) := by
        rw [smul_smul, smul_smul]
        congr 1
        rw [hd]
        ring
      rw [h2]
      exact NB.smul_mem _ h1
    · rw [Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => ¬ good j)]
      exact hexp x hxN
  · intro x hxW haxN hxC
    obtain ⟨l, hl, hlx⟩ := (Finsupp.mem_span_image_iff_linearCombination K).mp hxW
    rw [Finsupp.mem_supported'] at hl
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (fun i => zero_smul K (v i))]
      at hlx
    let m : ↥(NB.comap N.subtype) := ⟨⟨a • x, haxN⟩, hxC⟩
    have hsum : ∑ j, (algebraMap O K a * l j - algebraMap O K (snf.bM.repr (m : N) j)) • v j
        = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, mul_smul, algebraMap_smul]
      rw [← Finset.smul_sum, hlx, sub_eq_zero]
      exact hexp (a • x) haxN
    have hco : ∀ j, algebraMap O K a * l j = algebraMap O K (snf.bM.repr (m : N) j) := fun j =>
      sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hli _ hsum j)
    have hint : ∀ j, ∃ s : O, l j = algebraMap O K s := by
      intro j
      by_cases hg : good j
      · exact ⟨0, by rw [hl j (by simpa using hg), map_zero]⟩
      by_cases hr : ∃ i, snf.f i = j
      · obtain ⟨i, rfl⟩ := hr
        have hnd : ¬ snf.a i ∣ a := fun h => hg ⟨i, rfl, h⟩
        obtain ⟨u, hu⟩ := (ValuationRing.dvd_total (snf.a i) a).resolve_left hnd
        have hzi : snf.bM.repr (m : N) (snf.f i) = snf.a i * snf.bN.repr m i := by
          have := snf.repr_apply_embedding_eq_repr_smul m (i := i)
          rw [map_smul, Finsupp.smul_apply, smul_eq_mul] at this
          exact this
        refine ⟨u * snf.bN.repr m i, ?_⟩
        have h4 := hco (snf.f i)
        rw [hzi, hu, map_mul, map_mul, mul_assoc] at h4
        rw [mul_left_cancel₀ haK h4, map_mul]
      · have h0 : snf.bM.repr (m : N) j = 0 :=
          snf.repr_eq_zero_of_notMem_range m (by simpa using hr)
        have h4 := hco j
        rw [h0, map_zero] at h4
        exact ⟨0, by rw [(mul_eq_zero.mp h4).resolve_left haK, map_zero]⟩
    choose s hs using hint
    rw [← hlx]
    refine Submodule.sum_mem _ (fun j _ => ?_)
    rw [hs j, algebraMap_smul]
    exact N.smul_mem (s j) (hvN j)

theorem split_core (N NB : Submodule O Z) (hfg : N.FG) (hle : NB ≤ N) (a : O) (ha : a ≠ 0) :
    ∃ W : Submodule K Z,
      (∀ x ∈ N, ∃ y ∈ N, ∃ t ∈ N, y ∈ W ∧ a • t ∈ NB ∧ x = y + t) ∧
      (∀ x ∈ W, a • x ∈ NB → x ∈ N) := by
  have hfin : Module.Finite O N := Module.Finite.iff_fg.mpr hfg
  have htfZ : Module.IsTorsionFree O Z := Module.IsTorsionFree.trans_faithfulSMul O K Z
  have htf : Module.IsTorsionFree O N := inferInstance
  obtain ⟨n, snf⟩ := Submodule.smithNormalForm (Module.Free.chooseBasis O N) (NB.comap N.subtype)
  obtain ⟨W, h1, h2⟩ := split_of_snf (K := K) N NB a ha snf
  exact ⟨W, h1, fun x hx hax => h2 x hx (hle hax) hax⟩

end Core

section Split

variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {Z : Type} [AddCommGroup Z] [Module K Z] [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z]

abbrev OO (w : HeightOneSpectrum (𝓞 K)) : Subalgebra (𝓞 K) K :=
  Localization.subalgebra.ofField K w.asIdeal.primeCompl w.asIdeal.primeCompl_le_nonZeroDivisors

theorem mem_OO (w : HeightOneSpectrum (𝓞 K)) (x : K) :
    x ∈ OO w ↔ ∃ (a s : 𝓞 K) (_ : s ∈ w.asIdeal.primeCompl),
      x = algebraMap (𝓞 K) K a * (algebraMap (𝓞 K) K s)⁻¹ :=
  Iff.rfl

theorem isDVR_OO (w : HeightOneSpectrum (𝓞 K)) : IsDiscreteValuationRing (OO w) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) w.ne_bot (OO w)

theorem mem_localization_iff_mem_span (w : HeightOneSpectrum (𝓞 K)) (M : Submodule (𝓞 K) Z) (x : Z) :
    x ∈ localization₂ w.asIdeal M ↔ x ∈ Submodule.span (OO w) (M : Set Z) := by
  constructor
  · rintro ⟨s, hs, hsx⟩
    have hs0 := algebraMap_ne_zero_of_notMem w.asIdeal hs
    have hu : (algebraMap (𝓞 K) K s)⁻¹ ∈ OO w := (mem_OO w _).mpr ⟨1, s, hs, by simp⟩
    have hx : x = (⟨_, hu⟩ : OO w) • (s • x) := by
      rw [Subalgebra.smul_def, ← algebraMap_smul K s x, smul_smul]
      simp [hs0]
    rw [hx]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hsx)
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact locBasic_le_locS _ M hy
    | zero => exact Submodule.zero_mem _
    | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
    | smul a y _ hy =>
      obtain ⟨s, hs, hsy⟩ := hy
      obtain ⟨r, t, ht, hat⟩ := (mem_OO w a).mp a.2
      refine ⟨t * s, mul_mem ht hs, ?_⟩
      have ht0 := algebraMap_ne_zero_of_notMem w.asIdeal ht
      have he : (t * s) • (a • y) = r • (s • y) := by
        rw [Subalgebra.smul_def, hat, ← algebraMap_smul K (t * s), ← algebraMap_smul K r,
          ← algebraMap_smul K s, smul_smul, smul_smul]
        congr 1
        rw [map_mul]
        field_simp
      rw [he]
      exact M.smul_mem r hsy

theorem mem_OO_of_vw_nonneg (w : HeightOneSpectrum (𝓞 K)) {a : K} (ha : a ≠ 0)
    (h : 0 ≤ vw w a) : a ∈ OO w := by
  have := isDVR_OO w
  rcases ValuationRing.isInteger_or_isInteger (OO w) a with ⟨c, hc⟩ | ⟨c, hc⟩
  · rw [← hc]
    exact c.2
  · obtain ⟨r, s, hs, hrs⟩ := (mem_OO w _).mp c.2
    have hc' : a⁻¹ = algebraMap (𝓞 K) K r * (algebraMap (𝓞 K) K s)⁻¹ := by
      rw [← hrs, ← hc]
      rfl
    have hs0 := algebraMap_ne_zero_of_notMem w.asIdeal hs
    have hr0 : algebraMap (𝓞 K) K r ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hc'
      exact inv_ne_zero ha hc'
    by_cases hr : r ∈ w.asIdeal
    · exfalso
      have hr0' : r ≠ 0 := fun h0 => hr0 (by rw [h0, map_zero])
      have h1 := idxChange_cnt_mem (K := K) w hr0' hr
      have h2 := idxChange_cnt_unit (K := K) w hs
      have h3 : algebraMap (𝓞 K) K s = a * algebraMap (𝓞 K) K r := by
        have : a * a⁻¹ = 1 := mul_inv_cancel₀ ha
        rw [hc'] at this
        field_simp at this
        exact this.symm
      rw [h3, idxChange_cnt_mul w ha hr0] at h2
      unfold vw at h
      omega
    · refine (mem_OO w _).mpr ⟨s, r, hr, ?_⟩
      rw [← inv_inv a, hc']
      field_simp

theorem exists_split (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) Z) (hA : A.FG)
    (hBA : B ≤ A) {a : K} (ha : a ≠ 0) (hav : a ∈ OO w) :
    ∃ W : Submodule K Z,
      localization₂ w.asIdeal A ≤
        cut W (localization₂ w.asIdeal A) ⊔ (localization₂ w.asIdeal A ⊓ sc a⁻¹ (localization₂ w.asIdeal B)) ∧
      cut W (sc a⁻¹ (localization₂ w.asIdeal B)) ≤ localization₂ w.asIdeal A := by
  have hdvr := isDVR_OO w
  have htow : IsScalarTower (𝓞 K) (OO w) Z :=
    ⟨fun r c z => by rw [Subalgebra.smul_def, Subalgebra.smul_def, Subalgebra.coe_smul, smul_assoc]⟩
  have hfg : (Submodule.span (OO w) (A : Set Z)).FG := by
    obtain ⟨s, hs⟩ := hA
    exact ⟨s, by rw [← hs, Submodule.span_span_of_tower]⟩
  have ha0 : (⟨a, hav⟩ : OO w) ≠ 0 := fun h => ha (congrArg Subtype.val h)
  obtain ⟨W, h1, h2⟩ := split_core (K := K) (Submodule.span (OO w) (A : Set Z))
    (Submodule.span (OO w) (B : Set Z)) hfg (Submodule.span_mono hBA) ⟨a, hav⟩ ha0
  refine ⟨W, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, t, ht, hyW, hat, rfl⟩ := h1 x ((mem_localization_iff_mem_span w A x).mp hx)
    exact Submodule.add_mem_sup ⟨(mem_localization_iff_mem_span w A y).mpr hy, hyW⟩
      ⟨(mem_localization_iff_mem_span w A t).mpr ht,
        (mem_sc_inv ha _ _).mpr ((mem_localization_iff_mem_span w B _).mpr hat)⟩
  · rintro x ⟨hxC, hxW⟩
    exact (mem_localization_iff_mem_span w A x).mpr
      (h2 x hxW ((mem_localization_iff_mem_span w B _).mp ((mem_sc_inv ha _ _).mp hxC)))

theorem le_sc_inv (w : HeightOneSpectrum (𝓞 K)) (L : Submodule (𝓞 K) Z) {a : K} (ha : a ≠ 0)
    (hav : a ∈ OO w) : localization₂ w.asIdeal L ≤ sc a⁻¹ (localization₂ w.asIdeal L) := by
  intro x hx
  rw [mem_sc_inv ha, mem_localization_iff_mem_span]
  exact Submodule.smul_mem _ (⟨a, hav⟩ : OO w) ((mem_localization_iff_mem_span w L x).mp hx)

theorem sc_inv_cut (W : Submodule K Z) (X : Submodule (𝓞 K) Z) {a : K} (ha : a ≠ 0) :
    sc a⁻¹ (cut W X) = cut W (sc a⁻¹ X) := by
  ext x
  rw [mem_sc_inv ha]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(mem_sc_inv ha _ _).mpr h1, ?_⟩
    have := W.smul_mem a⁻¹ h2
    rwa [smul_smul, inv_mul_cancel₀ ha, one_smul] at this
  · rintro ⟨h1, h2⟩
    exact ⟨(mem_sc_inv ha _ _).mp h1, W.smul_mem a h2⟩

theorem isLatIn_cut (W : Submodule K Z) (B : Submodule (𝓞 K) Z) (hB : IsLatIn ⊤ B) :
    IsLatIn W (cut W B) := by
  constructor
  · have : IsNoetherian (𝓞 K) B := isNoetherian_of_fg_of_noetherian B hB.1
    exact isNoetherian_submodule.mp this _ inf_le_left
  · apply le_antisymm
    · exact Submodule.span_le.mpr (fun x hx => hx.2)
    · intro x hx
      have htop := indexBasic_locS_top (K := K) B hB.2
      have hx' : x ∈ locS (nonZeroDivisors (𝓞 K)) B := by rw [htop]; exact Submodule.mem_top
      obtain ⟨d, hd, hdx⟩ := hx'
      have hd0 : algebraMap (𝓞 K) K d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
      have hmem : d • x ∈ cut W B := by
        refine ⟨hdx, ?_⟩
        change d • x ∈ W
        rw [← algebraMap_smul K d x]
        exact W.smul_mem _ hx
      have := Submodule.smul_mem (Submodule.span K ((cut W B : Submodule (𝓞 K) Z) : Set Z))
        (algebraMap (𝓞 K) K d)⁻¹ (Submodule.subset_span hmem)
      rwa [← algebraMap_smul K d x, smul_smul, inv_mul_cancel₀ hd0, one_smul] at this

theorem qlen_ne_top (p : Ideal (𝓞 K)) [p.IsPrime] (X Y : Submodule (𝓞 K) Z) (hX : X.FG)
    (hY : Submodule.span K (Y : Set Z) = ⊤) : qlen (localization₂ p X) (localization₂ p Y) ≠ ⊤ := by
  obtain ⟨d, hd, hdY⟩ := indexBasic_denom (nonZeroDivisors (𝓞 K)) X Y hX
    (by rw [indexBasic_locS_top (K := K) Y hY]; exact le_top)
  exact Module.length_ne_top_iff.mpr (indexBasic_finLen p X Y hX hd hdY)

theorem qlen_scale [FiniteDimensional K Z] (hS : IdxScaleIn) (w : HeightOneSpectrum (𝓞 K))
    (W : Submodule K Z) (L : Submodule (𝓞 K) Z) (hL : IsLatIn W L) {a : K} (ha : a ≠ 0) (E : ℕ)
    (hE : vw w a = (E : ℤ)) :
    qlen (sc a⁻¹ (localization₂ w.asIdeal L)) (localization₂ w.asIdeal L) = ((E * finrank K W : ℕ) : ℕ∞) := by
  have hav : a ∈ OO w := mem_OO_of_vw_nonneg w ha (by rw [hE]; exact Int.natCast_nonneg E)
  have hloc := le_sc_inv w L ha hav
  have hfin : qlen (sc a⁻¹ (localization₂ w.asIdeal L)) (localization₂ w.asIdeal L) ≠ ⊤ := by
    obtain ⟨r, s, hs, hrs⟩ := IsFractionRing.div_surjective (A := 𝓞 K) a
    have hs0 : algebraMap (𝓞 K) K s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
    have hr0 : algebraMap (𝓞 K) K r ≠ 0 := by
      intro h0
      rw [h0, zero_div] at hrs
      exact ha hrs.symm
    have hr : r ∈ nonZeroDivisors (𝓞 K) :=
      mem_nonZeroDivisors_of_ne_zero (fun h0 => hr0 (by rw [h0, map_zero]))
    rw [← localization_sc _ (inv_ne_zero ha)]
    refine Module.length_ne_top_iff.mpr
      (indexBasic_finLen w.asIdeal (sc a⁻¹ L) L (hL.1.map _) hr ?_)
    intro x hx
    have hx' := (mem_sc_inv ha L x).mp hx
    have : r • x = s • (a • x) := by
      rw [← algebraMap_smul K r, ← algebraMap_smul K s, smul_smul, ← hrs]
      congr 1
      field_simp
    rw [this]
    exact L.smul_mem s hx'
  have h := (hS K Z w W L L hL hL a⁻¹ (inv_ne_zero ha)).2
  have hinv : vw w a⁻¹ = - vw w a := (valuation_basic_properties K w).2.2.2.2.2.1 a
  have h0 : lix w L L = 0 := by
    unfold lix
    rw [lidx_of_le _ le_rfl, qlen_eq_zero le_rfl]
    rfl
  have h1 : lix w L (sc a⁻¹ L) =
      - ((qlen (sc a⁻¹ (localization₂ w.asIdeal L)) (localization₂ w.asIdeal L)).toNat : ℤ) := by
    unfold lix lidx locLen
    rw [localization_inf, localization_sc _ (inv_ne_zero ha), inf_eq_left.mpr hloc]
    change ((qlen (localization₂ w.asIdeal L) (localization₂ w.asIdeal L)).toNat : ℤ) -
      ((qlen (sc a⁻¹ (localization₂ w.asIdeal L)) (localization₂ w.asIdeal L)).toNat : ℤ) = _
    rw [qlen_eq_zero le_rfl]
    simp
  rw [h1, h0, hinv, hE] at h
  have h2 : (qlen (sc a⁻¹ (localization₂ w.asIdeal L)) (localization₂ w.asIdeal L)).toNat = E * finrank K W := by
    have : ((qlen (sc a⁻¹ (localization₂ w.asIdeal L)) (localization₂ w.asIdeal L)).toNat : ℤ) =
        (E : ℤ) * (finrank K W : ℤ) := by linarith
    exact_mod_cast this
  rw [← h2, ENat.natCast_toNat hfin]

end Split

section Ram

open IsLocalRing

theorem isLocalHom_of_map_eq_pow (O O' : Type) [CommRing O] [IsLocalRing O] [CommRing O']
    [IsLocalRing O'] [Algebra O O'] (e : ℕ) (he : e ≠ 0)
    (h : Ideal.map (algebraMap O O') (maximalIdeal O) = maximalIdeal O' ^ e) :
    IsLocalHom (algebraMap O O') := by
  constructor
  intro a ha
  by_contra hna
  have hm : a ∈ maximalIdeal O := hna
  have h1 : algebraMap O O' a ∈ maximalIdeal O' ^ e := h ▸ Ideal.mem_map_of_mem _ hm
  exact (mem_maximalIdeal _).mp (Ideal.pow_le_self he h1) ha

theorem exists_pow_smul_eq_zero (O : Type) [CommRing O] [IsLocalRing O] (ϖ : O)
    (hϖ : ϖ ∈ maximalIdeal O) (M : Type) [AddCommGroup M] [Module O M] (h : IsFiniteLength O M) :
    ∃ n : ℕ, ∀ x : M, ϖ ^ n • x = 0 := by
  induction h with
  | of_subsingleton => exact ⟨0, fun x => Subsingleton.elim _ _⟩
  | @of_simple_quotient M _ _ N hs _ ih =>
    obtain ⟨n, hn⟩ := ih
    obtain ⟨m, hm, ⟨f⟩⟩ := isSimpleModule_iff_quot_maximal.mp hs
    have hmm : m = maximalIdeal O := IsLocalRing.eq_maximalIdeal hm
    subst hmm
    have hk : ∀ x : M, ϖ • x ∈ N := by
      intro x
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
      apply f.injective
      rw [map_smul, map_zero]
      obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (f (Submodule.Quotient.mk x))
      rw [← hy, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
        Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mul_mem_right _ _ hϖ
    refine ⟨n + 1, fun x => ?_⟩
    have := hn ⟨ϖ • x, hk x⟩
    rw [pow_succ, mul_smul]
    simpa using congrArg Subtype.val this

end Ram

end ThreeFormsAlt

open ThreeFormsAlt in
theorem three_forms_sum : ThreeFormsSum := by
  intro K _ _ _ Z _ _ _ _ _ w A B _ _ _ a ha _
  unfold lix
  rw [lidx_of_le _ (le_sup_right : B ≤ sc a A ⊔ B),
    lidx_of_le _ (inf_le_left : A ⊓ sc a⁻¹ B ≤ A), localization_sup_eq_localization_dnN, localization_sc _ ha, localization_inf,
    localization_sc _ (inv_ne_zero ha)]
  set A' := localization₂ w.asIdeal A
  set B' := localization₂ w.asIdeal B
  have h1 : qlen (sc a A' ⊔ B') B' = qlen (sc a A') B' :=
    le_antisymm (qlen_le_of_sup le_sup_left (sup_le_sup_left (le_inf le_sup_right le_rfl) _))
      (qlen_mono_left le_sup_left _)
  have h2 : qlen (sc a A') B' = qlen A' (sc a⁻¹ B') := by
    conv_lhs => rw [← sc_sc_inv ha B']
    rw [sc_eq_map a ha, sc_eq_map a ha, qlen_map]
  have h3 : qlen A' (A' ⊓ sc a⁻¹ B') = qlen A' (sc a⁻¹ B') :=
    qlen_congr A' (fun x hx => ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩)
  rw [h1, h2, h3]

open ThreeFormsAlt in
theorem threeForms_of (hS : IdxScaleIn) : ThreeForms := by
  intro K _ _ _ Z _ _ _ _ _ w A B hA hB hBA a E r ha hE
  have hav : a ∈ OO w := mem_OO_of_vw_nonneg w ha (by rw [hE]; exact Int.natCast_nonneg E)
  have hR : lix w A (A ⊓ sc a⁻¹ B) =
      ((qlen (localization₂ w.asIdeal A) (sc a⁻¹ (localization₂ w.asIdeal B))).toNat : ℤ) := by
    unfold lix
    rw [lidx_of_le _ (inf_le_left : A ⊓ sc a⁻¹ B ≤ A), localization_inf, localization_sc _ (inv_ne_zero ha),
      qlen_inf_self]
  have hL : ∀ W : Submodule K Z, lix w (cut W A) (cut W B) =
      ((qlen (cut W (localization₂ w.asIdeal A)) (cut W (localization₂ w.asIdeal B))).toNat : ℤ) := by
    intro W
    unfold lix
    rw [lidx_of_le _ (cut_mono W hBA), localization_cut, localization_cut]
  have hSc : ∀ W : Submodule K Z,
      qlen (cut W (sc a⁻¹ (localization₂ w.asIdeal B))) (cut W (localization₂ w.asIdeal B)) =
        ((E * finrank K W : ℕ) : ℕ∞) := by
    intro W
    rw [← sc_inv_cut W _ ha, ← localization_cut]
    exact qlen_scale hS w W (cut W B) (isLatIn_cut W B hB) ha E hE
  have hfin : qlen (localization₂ w.asIdeal A) (localization₂ w.asIdeal B) ≠ ⊤ :=
    qlen_ne_top w.asIdeal A B hA.1 hB.2
  have hBA' : localization₂ w.asIdeal B ≤ localization₂ w.asIdeal A := locBasic_locS_mono _ hBA
  have hBC' : localization₂ w.asIdeal B ≤ sc a⁻¹ (localization₂ w.asIdeal B) := le_sc_inv w B ha hav
  have hsplit := exists_split w A B hA.1 hBA ha hav
  rw [hR]
  simp only [hL]
  generalize localization₂ w.asIdeal A = A' at *
  generalize localization₂ w.asIdeal B = B' at *
  generalize hC : sc a⁻¹ B' = C' at *
  have hfinC : qlen A' C' ≠ ⊤ := ne_top_of_le_ne_top hfin (qlen_anti_right A' hBC')
  have hcongr : ∀ (W : Submodule K Z) (Y : Submodule (𝓞 K) Z),
      qlen (cut W A') (cut W Y) = qlen (cut W A') Y := fun W Y =>
    qlen_congr _ (fun x hx => ⟨fun h => h.1, fun h => ⟨h, hx.2⟩⟩)
  have hfinW : ∀ W : Submodule K Z, qlen (cut W A') (cut W B') ≠ ⊤ := fun W =>
    ne_top_of_le_ne_top hfin (by rw [hcongr]; exact qlen_mono_left inf_le_left _)
  obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.mp hfinC
  constructor
  · intro h
    obtain ⟨W, h1, h2⟩ := hsplit
    obtain ⟨x, hx⟩ := ENat.ne_top_iff_exists.mp (hfinW W)
    have hadd : qlen (cut W A') (cut W B') =
        qlen (cut W C') (cut W B') + qlen (cut W A') (cut W C') :=
      qlen_add (cut_mono W hBC') (le_inf h2 inf_le_right)
    have hge : qlen A' C' ≤ qlen (cut W A') (cut W C') := by
      rw [hcongr]
      exact qlen_le_of_sup inf_le_left h1
    have hW := h W
    rw [hSc W] at hadd
    rw [← hx] at hadd hW
    rw [← hc] at hge ⊢
    have h3 : ((E * finrank K W : ℕ) : ℕ∞) + (c : ℕ∞) ≤ (x : ℕ∞) := by
      rw [hadd]
      exact add_le_add_right hge _
    have h4 : E * finrank K W + c ≤ x := by exact_mod_cast h3
    have h5 : ((E * finrank K W + c : ℕ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast h4
    push_cast at h5
    simp only [ENat.toNat_natCast, Int.cast_natCast] at hW ⊢
    linarith
  · intro h W
    obtain ⟨x, hx⟩ := ENat.ne_top_iff_exists.mp (hfinW W)
    have hadd : qlen (cut W A') (cut W B') =
        qlen (cut W (A' ⊓ C')) (cut W B') + qlen (cut W A') (cut W (A' ⊓ C')) :=
      qlen_add (cut_mono W (le_inf hBA' hBC')) (cut_mono W inf_le_left)
    have hle1 : qlen (cut W (A' ⊓ C')) (cut W B') ≤ qlen (cut W C') (cut W B') :=
      qlen_mono_left (cut_mono W inf_le_right) _
    have hle2 : qlen (cut W A') (cut W (A' ⊓ C')) ≤ qlen A' C' := by
      have h6 : qlen (cut W A') (A' ⊓ C') = qlen (cut W A') C' :=
        qlen_congr (cut W A') (fun x hx => ⟨fun h => h.2, fun h => ⟨hx.1, h⟩⟩)
      rw [hcongr, h6]
      exact qlen_mono_left inf_le_left _
    rw [hSc W] at hle1
    rw [← hx] at hadd ⊢
    rw [← hc] at hle2 h
    have h3 : (x : ℕ∞) ≤ ((E * finrank K W : ℕ) : ℕ∞) + (c : ℕ∞) := by
      rw [hadd]
      exact add_le_add hle1 hle2
    have h4 : x ≤ E * finrank K W + c := by exact_mod_cast h3
    have h5 : (x : ℝ) ≤ ((E * finrank K W + c : ℕ) : ℝ) := by exact_mod_cast h4
    push_cast at h5
    simp only [ENat.toNat_natCast, Int.cast_natCast] at h ⊢
    linarith

theorem three_forms : ThreeForms := threeForms_of index_scale_inclusion

open IsLocalRing in
theorem length_ramified : LengthRamified := by
  intro O O' _ _ _ _ _ _ _ _ e hmap M _ _ hM
  by_cases he : e = 0
  · subst he
    rw [pow_zero, Ideal.one_eq_top] at hmap
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    have hu : IsUnit (algebraMap O O' ϖ) := by
      rw [hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton,
        Ideal.span_singleton_eq_top] at hmap
      exact hmap
    obtain ⟨n, hn⟩ := ThreeFormsAlt.exists_pow_smul_eq_zero O ϖ
      (by rw [hϖ.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self ϖ) M
      (Module.length_ne_top_iff.mp hM)
    have hsub : Subsingleton (TensorProduct O O' M) := by
      refine ⟨fun x y => ?_⟩
      have h0 : ∀ z : TensorProduct O O' M, z = 0 := by
        intro z
        induction z using TensorProduct.induction_on with
        | zero => rfl
        | tmul a m =>
          obtain ⟨u, hu'⟩ := hu.pow n
          have : a = ϖ ^ n • (a * (u⁻¹ : O'ˣ)) := by
            rw [Algebra.smul_def, map_pow, ← hu', mul_comm a, Units.mul_inv_cancel_left]
          rw [this, TensorProduct.smul_tmul, hn, TensorProduct.tmul_zero]
        | add a b ha hb => rw [ha, hb, add_zero]
      rw [h0 x, h0 y]
    rw [Module.length_eq_zero]
    simp
  · have := ThreeFormsAlt.isLocalHom_of_map_eq_pow O O' e he hmap
    rw [IsLocalRing.length_baseChange O O' M, hmap,
      IsDiscreteValuationRing.length_quotient_pow_maximalIdeal, mul_comm]

end Formalism.EigenvalueLevelCeiling
