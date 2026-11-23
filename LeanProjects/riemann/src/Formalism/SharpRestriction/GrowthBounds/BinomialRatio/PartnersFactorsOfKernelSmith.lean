import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.ExtendedStatementOfParts
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.FactorsOfPerturb
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.KeptFin
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.TotalDegreeEplus
import Formalism.SharpRestriction.GrowthBounds.RootWeights.ExponentFactorialAddSingleOne

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory

section Gen

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

def SmithData {r s t : ℕ} (form : SegVs O r s t → SegVs O r s t → KK O) (L : Submodule O (SegVs O r s t)) (n : ℕ)
    (al be : Fin n → SegVs O r s t) (β : Fin n → SegBlock s r) : Prop :=
  (∀ i, al i ∈ L ∧ be i ∈ L) ∧ (∀ i b, b ≠ β i → al i b = 0 ∧ be i b = 0) ∧
    (∀ i l, i ≠ l → form (al i) (be l) = 0) ∧ LinearIndependent O al ∧
    Submodule.span O (Set.range al) = L ∧ Submodule.span O (Set.range be) = L

theorem vK_zero (p : ℕ) : vK p (0 : KK O) = ⊤ := by
  unfold vK ordW
  simp

theorem vLE_ne_zero {p : ℕ} {κ : KK O} {D : ℝ} (h : vLE p κ D) : κ ≠ 0 := by
  intro hκ
  subst hκ
  obtain ⟨q, hq, -⟩ := h
  rw [vK_zero] at hq
  exact WithTop.top_ne_coe hq

theorem scale_to_O {p : ℕ} {w : O} (hw : Irreducible w) (h2 : w ^ 2 = (p : O)) {κ : KK O} {D : ℝ} (hD : 0 ≤ D)
    (h : vLE p κ D) : ∃ c z : O, z ≠ 0 ∧ vLEO p z D ∧ algebraMap O (KK O) c * κ = algebraMap O (KK O) z := by
  have hκ := vLE_ne_zero h
  rcases ValuationRing.isInteger_or_isInteger O κ with ⟨z, hz⟩ | ⟨c, hc⟩
  · refine ⟨1, z, ?_, ?_, by rw [map_one, one_mul, hz]⟩
    · rintro rfl
      exact hκ (by rw [← hz, map_zero])
    · unfold vLEO vO
      rw [hz]
      exact h
  · refine ⟨c, 1, one_ne_zero, ?_, by rw [hc, map_one, inv_mul_cancel₀ hκ]⟩
    rw [vLEO_iff hw h2 one_ne_zero, dvr_order_unit_eq_zero isUnit_one]
    simpa using hD

theorem segForm_smul_right (p r : ℕ) {s : ℕ} (S : SegData s) (c : O) (f g : SegVs O r s S.t) :
    segForm O p r S f (c • g) = algebraMap O (KK O) c * segForm O p r S f g := by
  unfold segForm
  by_cases hc : algebraMap O (KK O) c = 0
  · rw [hc, zero_mul]
    have : ∀ b, ((specConst p S b : ℕ) : KK O) * fock (f b) ((c • g) b) = 0 := fun b => by
      rw [Pi.smul_apply, ← algebraMap_smul (KK O) c (g b), hc, zero_smul]
      unfold fock
      simp
    rw [finsum_congr this, finsum_zero]
  · have := AddMonoidHom.map_finsum_of_injective (AddMonoidHom.mulLeft (algebraMap O (KK O) c))
      (mul_right_injective₀ hc) (fun b => ((specConst p S b : ℕ) : KK O) * fock (f b) (g b))
    simp only [AddMonoidHom.coe_mulLeft] at this
    rw [this]
    refine finsum_congr fun b => ?_
    rw [Pi.smul_apply, ← algebraMap_smul (KK O) c (g b), fock_form_smul_right, smul_eq_mul]
    ring

open Classical in

theorem blockDiag_of_smith {p : ℕ} {w : O} (hw : Irreducible w) (h2 : w ^ 2 = (p : O)) {r s : ℕ} (S : SegData s)
    (L : Submodule O (SegVs O r s S.t)) {n : ℕ} {al be : Fin n → SegVs O r s S.t} {β : Fin n → SegBlock s r}
    (hS : SmithData (segForm O p r S) L n al be β) {D : ℝ} (hD : 0 ≤ D) (g : ℕ)
    (hg : g ≤ (Finset.univ.filter fun i => vLE p (segForm O p r S (al i) (be i)) D).card) :
    BlockDiag p (segForm O p r S) L g D := by
  obtain ⟨hmem, hsupp, horth, -, -, -⟩ := hS
  set good := Finset.univ.filter fun i => vLE p (segForm O p r S (al i) (be i)) D with hgood
  let e : Fin g → Fin n := fun i => ((good.equivFin).symm (Fin.castLE hg i)).1
  have he : Function.Injective e := fun a b hab => by
    have h1 := Subtype.ext hab
    have h3 := (good.equivFin).symm.injective h1
    exact Fin.castLE_injective hg h3
  have hegood : ∀ i, vLE p (segForm O p r S (al (e i)) (be (e i))) D := fun i =>
    (Finset.mem_filter.1 ((good.equivFin).symm (Fin.castLE hg i)).2).2
  choose c z hz0 hzD hcz using fun i => scale_to_O hw h2 hD (hegood i)
  refine ⟨fun i => al (e i), fun i => c i • be (e i), fun i => β (e i), z,
    fun i => ⟨(hmem _).1, L.smul_mem _ (hmem _).2⟩, fun i b hb => ⟨(hsupp _ b hb).1, ?_⟩, fun i => ⟨hz0 i, hzD i⟩, ?_⟩
  · show c i • be (e i) b = 0
    rw [(hsupp _ b hb).2, smul_zero]
  · intro i l
    show segForm O p r S (al (e i)) (c l • be (e l)) = _
    rw [segForm_smul_right]
    by_cases hil : i = l
    · subst hil
      rw [if_pos rfl, hcz]
    · rw [if_neg hil, horth _ _ (fun h => hil (he h)), mul_zero]

end Gen

def SmithAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (jO : W →+* O) (w : O),
    UnramifiedQuadraticSetting X.p X.n' W Qq O Kf ι σ jO w → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ j : Fin (numSeg X.TT), ∃ (n : ℕ) (al be : Fin n → SegVs O X.m (segS X.TT j) (X.seg C0 CE1 CE2 j).t)
      (β : Fin n → SegBlock (segS X.TT j) X.m),
      SmithData (segForm O X.p X.m (X.seg C0 CE1 CE2 j)) (Lj O C0 CE1 CE2 Cm X j) n al be β

open Classical in

def CountSmithAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (jO : W →+* O) (w : O),
    UnramifiedQuadraticSetting X.p X.n' W Qq O Kf ι σ jO w → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (Dj : ℝ) (L₁ : Submodule O (SegVs O X.m (segS X.TT j) (X.seg C0 CE1 CE2 j).t)), 0 ≤ Dj →
      GoodSub X.p (segForm O X.p X.m (X.seg C0 CE1 CE2 j)) (Lj O C0 CE1 CE2 Cm X j) L₁ Dj →
      ∀ (n : ℕ) (al be : Fin n → SegVs O X.m (segS X.TT j) (X.seg C0 CE1 CE2 j).t)
        (β : Fin n → SegBlock (segS X.TT j) X.m),
        SmithData (segForm O X.p X.m (X.seg C0 CE1 CE2 j)) (Lj O C0 CE1 CE2 Cm X j) n al be β →
        Module.finrank O L₁ ≤
          (Finset.univ.filter fun i => vLE X.p (segForm O X.p X.m (X.seg C0 CE1 CE2 j) (al i) (be i)) Dj).card

theorem partners_factors_at_of_smith {C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc : ℝ} (hSm : SmithAt C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc)
    (hCn : CountSmithAt C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc) : PartnersToFactorsAt C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc := by
  intro X _ W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ jO w hS hH hc j Dj L₁ hD hG
  obtain ⟨n, al, be, β, hd⟩ := hSm X W Qq O Kf ι σ jO w hS hH hc j
  exact blockDiag_of_smith hS.2.1 hS.1.w_sq _ _ hd hD _
    (hCn X W Qq O Kf ι σ jO w hS hH hc j Dj L₁ hD hG n al be β hd)

def RestSmith : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc => SmithAt C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc
def RestCountSmith : Prop :=
  TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc => CountSmithAt C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc

theorem partners_factors_of_smith_count (hSm : RestSmith) (hCn : RestCountSmith) : PartnersToFactors :=
  TransportedAlt.mono (fun _ _ _ _ _ _ _ _ _ _ h => partners_factors_at_of_smith h.1 h.2) (TransportedAlt.and hSm hCn)

section Rank

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem rank_le_of_ker {V : Type} [AddCommGroup V] [Module O V] {n : ℕ} (al : Fin n → V) (hli : LinearIndependent O al)
    (L L₁ : Submodule O V) (hspan : Submodule.span O (Set.range al) = L) (hle : L₁ ≤ L) (good : Finset (Fin n))
    (hker : ∀ a : Fin n → O, (∑ i, a i • al i) ∈ L₁ → (∀ i ∈ good, a i = 0) → a = 0) :
    Module.finrank O L₁ ≤ good.card := by
  classical
  have hle' : L₁ ≤ Submodule.span O (Set.range al) := hle.trans hspan.ge
  let π : L₁ →ₗ[O] (good → O) := LinearMap.pi fun i =>
    (Finsupp.lapply (i : Fin n)).comp (hli.repr.comp (Submodule.inclusion hle'))
  have hπ : Function.Injective π := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hrep := hli.linearCombination_repr (Submodule.inclusion hle' x)
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (fun i => zero_smul O (al i))] at hrep
    have hz : (fun i => hli.repr (Submodule.inclusion hle' x) i) = 0 := by
      refine hker _ ?_ (fun i hi => congr_fun hx ⟨i, hi⟩)
      show (∑ i, hli.repr (Submodule.inclusion hle' x) i • al i) ∈ L₁
      rw [hrep, Submodule.coe_inclusion]
      exact x.2
    have hz' : ∀ i, hli.repr (Submodule.inclusion hle' x) i = 0 := fun i => congr_fun hz i
    apply Subtype.ext
    rw [Submodule.coe_zero, ← Submodule.coe_inclusion hle' x, ← hrep]
    simp [hz']
  calc Module.finrank O L₁ ≤ Module.finrank O (good → O) := LinearMap.finrank_le_finrank_of_injective hπ
    _ = good.card := by simp

end Rank

open Classical in

def KerSmithAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (jO : W →+* O) (w : O),
    UnramifiedQuadraticSetting X.p X.n' W Qq O Kf ι σ jO w → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (Dj : ℝ) (L₁ : Submodule O (SegVs O X.m (segS X.TT j) (X.seg C0 CE1 CE2 j).t)), 0 ≤ Dj →
      GoodSub X.p (segForm O X.p X.m (X.seg C0 CE1 CE2 j)) (Lj O C0 CE1 CE2 Cm X j) L₁ Dj →
      ∀ (n : ℕ) (al be : Fin n → SegVs O X.m (segS X.TT j) (X.seg C0 CE1 CE2 j).t)
        (β : Fin n → SegBlock (segS X.TT j) X.m),
        SmithData (segForm O X.p X.m (X.seg C0 CE1 CE2 j)) (Lj O C0 CE1 CE2 Cm X j) n al be β →
        ∀ a : Fin n → O, (∑ i, a i • al i) ∈ L₁ →
          (∀ i, vLE X.p (segForm O X.p X.m (X.seg C0 CE1 CE2 j) (al i) (be i)) Dj → a i = 0) → a = 0

open Classical in
theorem countSmithAt_of {C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc : ℝ}
    (h : KerSmithAt C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc) : CountSmithAt C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc := by
  intro X _ W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ jO w hS hH hC j Dj L₁ hD hG n al be β hSm
  exact rank_le_of_ker al hSm.2.2.2.1 _ L₁ hSm.2.2.2.2.1 hG.1.1 _
    (fun a ha h0 => h X W Qq O Kf ι σ jO w hS hH hC j Dj L₁ hD hG n al be β hSm a ha
      (fun i hi => h0 i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)))

def RestKerSmith : Prop :=
  TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc => KerSmithAt C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc

theorem partners_factors_of_kernel_smith (hSm : RestSmith) (hK : RestKerSmith) : PartnersToFactors :=
  partners_factors_of_smith_count hSm (TransportedAlt.mono (fun _ _ _ _ _ _ _ _ _ _ h => countSmithAt_of h) hK)

section Ker

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem bad_zero (p : ℕ) (D : ℝ) : ¬ vLE p (0 : KK O) D := fun h => vLE_ne_zero h rfl

theorem bad_add {p : ℕ} {D : ℝ} {x y : KK O} (hx : ¬ vLE p x D) (hy : ¬ vLE p y D) : ¬ vLE p (x + y) D := by
  rintro ⟨q, hq, hqD⟩
  have h := valuation_add_ge_min p x y
  rw [hq] at h
  rcases min_le_iff.1 h with h1 | h1
  · obtain ⟨q', hq', hle⟩ := WithTop.le_coe_iff.1 h1
    exact hx ⟨q', hq', le_trans (by exact_mod_cast hle) hqD⟩
  · obtain ⟨q', hq', hle⟩ := WithTop.le_coe_iff.1 h1
    exact hy ⟨q', hq', le_trans (by exact_mod_cast hle) hqD⟩

theorem bad_mul {p : ℕ} {D : ℝ} (o : O) {x : KK O} (hx : ¬ vLE p x D) : ¬ vLE p (algebraMap O (KK O) o * x) D := by
  rintro ⟨q, hq, hqD⟩
  rw [valuation_mul_alt] at hq
  have h0 := vK_alg_nonneg p o
  have h1 : vK p x ≤ (q : WithTop ℚ) := by
    rw [← hq]
    exact le_add_of_nonneg_left h0
  obtain ⟨q', hq', hle⟩ := WithTop.le_coe_iff.1 h1
  exact hx ⟨q', hq', le_trans (by exact_mod_cast hle) hqD⟩

theorem bad_sum {p : ℕ} {D : ℝ} {ι : Type} (s : Finset ι) (f : ι → KK O) (h : ∀ i ∈ s, ¬ vLE p (f i) D) :
    ¬ vLE p (∑ i ∈ s, f i) D := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simpa using bad_zero (O := O) p D
  · intro i s hi ih h
    rw [Finset.sum_insert hi]
    exact bad_add (h i (Finset.mem_insert_self i s)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

open Classical in

theorem prim_div {w : O} (hw : Irreducible w) {n : ℕ} (a : Fin n → O) (ha : a ≠ 0) :
    ∃ (k : ℕ) (a' : Fin n → O), (∀ i, a i = w ^ k * a' i) ∧ ∃ i0, IsUnit (a' i0) := by
  obtain ⟨j, hj⟩ : ∃ j, a j ≠ 0 := by
    by_contra hne
    push_neg at hne
    exact ha (funext hne)
  let S := Finset.univ.filter fun i => a i ≠ 0
  have hS : S.Nonempty := ⟨j, by simp [S, hj]⟩
  obtain ⟨i0, hi0S, hmin⟩ := S.exists_min_image (fun i => dvrOrderNat (a i)) hS
  have hi0 : a i0 ≠ 0 := (Finset.mem_filter.mp hi0S).2
  have hex : ∀ i, ∃ b : O, a i = w ^ dvrOrderNat (a i0) * b ∧ (i = i0 → IsUnit b) := by
    intro i
    by_cases hi : a i = 0
    · refine ⟨0, by rw [hi, mul_zero], fun h => ?_⟩
      subst h
      exact absurd hi hi0
    · obtain ⟨u, hu⟩ := eq_unit_pow hw hi
      have hle : dvrOrderNat (a i0) ≤ dvrOrderNat (a i) := hmin i (by simp [S, hi])
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
      refine ⟨(u : O) * w ^ d, ?_, fun h => ?_⟩
      · conv_lhs => rw [hu, hd]
        rw [pow_add]
        ring
      · subst h
        have hd0 : d = 0 := by omega
        rw [hd0, pow_zero, mul_one]
        exact u.isUnit
  choose a' ha' using hex
  exact ⟨dvrOrderNat (a i0), a', fun i => (ha' i).1, i0, (ha' i0).2 rfl⟩

theorem ker_core {p : ℕ} {w : O} (hw : Irreducible w) {V : Type} [AddCommGroup V] [Module O V]
    (form : V → V → KK O) (L L₁ : Submodule O V) {n : ℕ} (al be : Fin n → V) (hli : LinearIndependent O al)
    (hA : Submodule.span O (Set.range al) = L) (hB : Submodule.span O (Set.range be) = L)
    (hbil : ∀ a η : Fin n → O, form (∑ i, a i • al i) (∑ i, η i • be i) =
      ∑ i, algebraMap O (KK O) (a i * η i) * form (al i) (be i))
    {D : ℝ} (hG : GoodSub p form L L₁ D) (a : Fin n → O) (ha : (∑ i, a i • al i) ∈ L₁)
    (h0 : ∀ i, vLE p (form (al i) (be i)) D → a i = 0) : a = 0 := by
  by_contra hne
  obtain ⟨k, a', ha', i0, hu⟩ := prim_div hw a hne
  have hwk : w ^ k ≠ 0 := pow_ne_zero _ hw.ne_zero
  have hL : (∑ i, a' i • al i) ∈ L := by
    rw [← hA]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hsm : w ^ k • (∑ i, a' i • al i) = ∑ i, a i • al i := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_smul, ← ha']
  have h1 : (∑ i, a' i • al i) ∈ L₁ := hG.1.2 _ _ hwk hL (by rw [hsm]; exact ha)
  have hprim : PrimIn L₁ (∑ i, a' i • al i) := by
    refine ⟨h1, fun c x hx hcx => ?_⟩
    have hxL : x ∈ Submodule.span O (Set.range al) := by rw [hA]; exact hG.1.1 hx
    obtain ⟨ξ, hξ⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 hxL
    have hz : ∑ i, (a' i - c * ξ i) • al i = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, mul_smul]
      rw [← Finset.smul_sum, hξ, ← hcx, sub_self]
    have := Fintype.linearIndependent_iff.1 hli _ hz i0
    have h2 : a' i0 = c * ξ i0 := sub_eq_zero.1 this
    rw [h2] at hu
    exact isUnit_of_mul_isUnit_left hu
  obtain ⟨y, hyL, hy⟩ := hG.2 _ hprim
  have hyS : y ∈ Submodule.span O (Set.range be) := by rw [hB]; exact hyL
  obtain ⟨η, hη⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 hyS
  rw [← hη, hbil] at hy
  refine bad_sum _ _ (fun i _ => ?_) hy
  by_cases hi : vLE p (form (al i) (be i)) D
  · have : a' i = 0 := by
      have h3 := h0 i hi
      rw [ha'] at h3
      exact (mul_eq_zero.1 h3).resolve_left hwk
    rw [this, zero_mul, map_zero, zero_mul]
    exact bad_zero p D
  · exact bad_mul _ hi

end Ker

def BilinAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (jO : W →+* O) (w : O),
    UnramifiedQuadraticSetting X.p X.n' W Qq O Kf ι σ jO w → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (n : ℕ) (al be : Fin n → SegVs O X.m (segS X.TT j) (X.seg C0 CE1 CE2 j).t)
        (β : Fin n → SegBlock (segS X.TT j) X.m),
        SmithData (segForm O X.p X.m (X.seg C0 CE1 CE2 j)) (Lj O C0 CE1 CE2 Cm X j) n al be β →
        ∀ a η : Fin n → O, segForm O X.p X.m (X.seg C0 CE1 CE2 j) (∑ i, a i • al i) (∑ i, η i • be i) =
          ∑ i, algebraMap O (KK O) (a i * η i) * segForm O X.p X.m (X.seg C0 CE1 CE2 j) (al i) (be i)

theorem kerSmithAt_of {C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc : ℝ}
    (h : BilinAt C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc) : KerSmithAt C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc := by
  intro X _ W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ jO w hS hH hC j Dj L₁ hD hG n al be β hSm a ha h0
  exact ker_core hS.2.1 _ _ L₁ al be hSm.2.2.2.1 hSm.2.2.2.2.1 hSm.2.2.2.2.2
    (h X W Qq O Kf ι σ jO w hS hH hC j n al be β hSm) hG a ha h0

section Bilin

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem fock_zero_left {σ : Type} (G : MvPolynomial σ (KK O)) : fock (0 : MvPolynomial σ (KK O)) G = 0 := by
  unfold fock
  simp

theorem segForm_eq_sum (p r : ℕ) {s : ℕ} (S : SegData s) (T : Finset (SegBlock s r)) (f g : SegVs O r s S.t)
    (hT : ∀ b, b ∉ T → f b = 0) :
    segForm O p r S f g = ∑ b ∈ T, ((specConst p S b : ℕ) : KK O) * fock (f b) (g b) := by
  unfold segForm
  apply finsum_eq_sum_of_support_subset
  intro b hb
  by_contra hn
  apply hb
  show ((specConst p S b : ℕ) : KK O) * fock (f b) (g b) = 0
  rw [hT b (by simpa using hn), fock_zero_left, mul_zero]

theorem fock_bilin {σ : Type} {n : ℕ} (F G : Fin n → MvPolynomial σ (KK O)) (a η : Fin n → O) :
    fock (∑ i, a i • F i) (∑ l, η l • G l) = ∑ i, ∑ l, algebraMap O (KK O) (a i * η l) * fock (F i) (G l) := by
  rw [← fockBilinear_apply, map_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← algebraMap_smul (KK O) (a i) (F i), ← algebraMap_smul (KK O) (η l) (G l), map_smul, map_smul,
    LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, fockBilinear_apply, map_mul]
  ring

theorem segForm_bilin (p r : ℕ) {s : ℕ} (S : SegData s) (T : Finset (SegBlock s r)) {n : ℕ}
    (al be : Fin n → SegVs O r s S.t) (hT : ∀ i b, b ∉ T → al i b = 0) (a η : Fin n → O) :
    segForm O p r S (∑ i, a i • al i) (∑ i, η i • be i) =
      ∑ i, ∑ l, algebraMap O (KK O) (a i * η l) * segForm O p r S (al i) (be l) := by
  have h0 : ∀ b, b ∉ T → (∑ i, a i • al i) b = 0 := fun b hb => by
    rw [Finset.sum_apply]
    exact Finset.sum_eq_zero fun i _ => by rw [Pi.smul_apply, hT i b hb, smul_zero]
  rw [segForm_eq_sum p r S T _ _ h0]
  have e1 : ∀ i l, segForm O p r S (al i) (be l) =
      ∑ b ∈ T, ((specConst p S b : ℕ) : KK O) * fock (al i b) (be l b) := fun i l =>
    segForm_eq_sum p r S T _ _ (hT i)
  simp only [e1]
  have key : ∀ b, fock ((∑ i, a i • al i) b) ((∑ i, η i • be i) b) =
      ∑ i, ∑ l, algebraMap O (KK O) (a i * η l) * fock (al i b) (be l b) := fun b => by
    rw [Finset.sum_apply, Finset.sum_apply]
    simp only [Pi.smul_apply]
    exact fock_bilin (fun i => al i b) (fun l => be l b) a η
  calc ∑ b ∈ T, ((specConst p S b : ℕ) : KK O) * fock ((∑ i, a i • al i) b) ((∑ i, η i • be i) b)
      = ∑ b ∈ T, ∑ i, ∑ l, algebraMap O (KK O) (a i * η l) *
          (((specConst p S b : ℕ) : KK O) * fock (al i b) (be l b)) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [key b, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by ring
    _ = ∑ i, ∑ b ∈ T, ∑ l, algebraMap O (KK O) (a i * η l) *
          (((specConst p S b : ℕ) : KK O) * fock (al i b) (be l b)) := Finset.sum_comm
    _ = ∑ i, ∑ l, ∑ b ∈ T, algebraMap O (KK O) (a i * η l) *
          (((specConst p S b : ℕ) : KK O) * fock (al i b) (be l b)) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = _ := by simp only [Finset.mul_sum]

end Bilin

theorem bilinAt_all (C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc : ℝ) : BilinAt C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc := by
  intro X _ W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ jO w hS hH hC j n al be β hSm a η
  classical
  have hT : ∀ i b, b ∉ Finset.univ.image β → al i b = 0 := by
    intro i b hb
    refine (hSm.2.1 i b fun hbi => hb ?_).1
    rw [hbi]
    exact Finset.mem_image_of_mem β (Finset.mem_univ i)
  rw [segForm_bilin X.p X.m (X.seg C0 CE1 CE2 j) (Finset.univ.image β) al be hT a η]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · intro l _ hl
    rw [hSm.2.2.1 i l (Ne.symm hl), mul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem partners_factors_of_smith_bases (hSm : RestSmith) : PartnersToFactors :=
  partners_factors_of_kernel_smith hSm (TransportedAlt.of_all fun C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc =>
    kerSmithAt_of (bilinAt_all C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc))

end Formalism.MainNotions.ColumnSystems.Pf
