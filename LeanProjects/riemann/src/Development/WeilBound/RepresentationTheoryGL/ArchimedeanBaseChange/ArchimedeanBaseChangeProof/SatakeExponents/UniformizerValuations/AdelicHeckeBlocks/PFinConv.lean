import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelRep
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralPointsOpenCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyNrmLTwConj

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open PositivityTheory.Rg.BcN.F2 (mconv)
open scoped Classical

namespace PositivityTheory.Rg.BcB.F

attribute [local instance] borelG borelF borelH

namespace FinConv

theorem rStab_left {H : Type} [Group H] (u : H → ℂ) (k : H) : rStab (fun z => u (k * z)) = rStab u := by
  ext s
  change (∀ x, u (k * (x * s)) = u (k * x)) ↔ ∀ x, u (x * s) = u x
  constructor
  · intro h x; simpa [mul_assoc] using h (k⁻¹ * x)
  · intro h x; simpa [mul_assoc] using h (k * x)

theorem hint_left {H : Type} [Group H] (K : Subgroup H) (u : H → ℂ) (k : H) :
    hint K (fun z => u (k * z)) = hint K u := by
  unfold hint
  rw [rStab_left]
  congr 1
  rw [← finsum_comp_equiv (MulAction.toPerm k : Equiv.Perm (H ⧸ (rStab u ⊓ K))) (f := fun q => u q.out)]
  refine finsum_congr fun q => ?_
  induction q using QuotientGroup.induction_on with
  | H g =>
    obtain ⟨h₁, e₁⟩ := QuotientGroup.mk_out_eq_mul (rStab u ⊓ K) g
    obtain ⟨h₂, e₂⟩ := QuotientGroup.mk_out_eq_mul (rStab u ⊓ K) (k * g)
    have hk : (MulAction.toPerm k : Equiv.Perm (H ⧸ (rStab u ⊓ K))) (QuotientGroup.mk g) = QuotientGroup.mk (k * g) := rfl
    simp only [hk, e₁, e₂]
    rw [← mul_assoc, (Subgroup.mem_inf.1 h₁.2).1, (Subgroup.mem_inf.1 h₂.2).1]

theorem hint_zero {H : Type} [Group H] (K : Subgroup H) : hint K (fun _ : H => (0 : ℂ)) = 0 := by
  simp [hint]

theorem exists_of_hint_ne {H : Type} [Group H] (K : Subgroup H) (u : H → ℂ) (h : hint K u ≠ 0) : ∃ z, u z ≠ 0 := by
  by_contra hc
  push Not at hc
  exact h (by rw [show u = fun _ => 0 from funext hc, hint_zero])

theorem hint_ind {H : Type} [Group H] (K : Subgroup H) : hint K ((K : Set H).indicator 1) = 1 := by
  have hR : rStab ((K : Set H).indicator 1) ⊓ K = K := by
    refine inf_eq_right.2 fun k hk x => ?_
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem (K.mul_mem hx hk), Set.indicator_of_mem hx]; rfl
    · rw [Set.indicator_of_notMem (fun h => hx (by simpa using K.mul_mem h (K.inv_mem hk))), Set.indicator_of_notMem hx]
  unfold hint
  rw [hR, Subgroup.relIndex_self]
  simp only [Nat.cast_one, inv_one, one_mul]
  rw [finsum_eq_single _ (QuotientGroup.mk 1 : H ⧸ K)]
  · obtain ⟨h, e⟩ := QuotientGroup.mk_out_eq_mul K (1 : H)
    rw [e, Set.indicator_of_mem (by simpa using h.2)]; rfl
  · intro q hq
    refine Set.indicator_of_notMem (fun hm => hq ?_) _
    rw [← QuotientGroup.out_eq' q]
    exact QuotientGroup.eq.2 (by simpa using K.inv_mem hm)

def cv {H : Type} [Group H] (K : Subgroup H) (u₁ u₂ : H → ℂ) (m : H) : ℂ := hint K fun z => u₁ z * u₂ (z⁻¹ * m)

theorem cv_hecke {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (K L₁ L₂ : Subgroup H) (u₁ u₂ : H → ℂ)
    (h₁ : IsHecke L₁ u₁) (h₂ : IsHecke L₂ u₂) : IsHecke (L₁ ⊓ L₂) (cv K u₁ u₂) := by
  refine ⟨?_, fun k hk m => ⟨?_, ?_⟩⟩
  · change IsCompact (closure (Function.support (cv K u₁ u₂)))
    refine IsCompact.closure_of_subset (h₁.1.mul h₂.1) fun m hm => ?_
    obtain ⟨z, hz⟩ := exists_of_hint_ne K (fun z => u₁ z * u₂ (z⁻¹ * m)) hm
    exact Set.mem_mul.2 ⟨z, subset_tsupport _ (left_ne_zero_of_mul hz), z⁻¹ * m,
      subset_tsupport _ (right_ne_zero_of_mul hz), mul_inv_cancel_left z m⟩
  · unfold cv
    calc hint K (fun z => u₁ z * u₂ (z⁻¹ * (k * m)))
        = hint K (fun z => (fun z => u₁ (k * z) * u₂ (z⁻¹ * m)) (k⁻¹ * z)) := by
          congr 1; funext z; simp [mul_assoc]
      _ = hint K (fun z => u₁ (k * z) * u₂ (z⁻¹ * m)) := hint_left K (fun z => u₁ (k * z) * u₂ (z⁻¹ * m)) k⁻¹
      _ = _ := by congr 1; funext z; rw [(h₁.2 k (Subgroup.mem_inf.1 hk).1 z).1]
  · unfold cv; congr 1; funext z; rw [← mul_assoc, (h₂.2 k (Subgroup.mem_inf.1 hk).2 _).2]

theorem cv_ind {H : Type} [Group H] (K : Subgroup H) :
    cv K ((K : Set H).indicator 1) ((K : Set H).indicator 1) = (K : Set H).indicator 1 := by
  funext m
  unfold cv
  by_cases hm : m ∈ K
  · rw [Set.indicator_of_mem hm, Pi.one_apply]
    have e : (fun z => (K : Set H).indicator 1 z * (K : Set H).indicator (1 : H → ℂ) (z⁻¹ * m)) =
        (K : Set H).indicator 1 := by
      funext z
      by_cases hz : z ∈ K
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem (K.mul_mem (K.inv_mem hz) hm)]; simp
      · rw [Set.indicator_of_notMem hz]; simp
    rw [e, hint_ind]
  · rw [Set.indicator_of_notMem hm]
    have e : (fun z => (K : Set H).indicator 1 z * (K : Set H).indicator (1 : H → ℂ) (z⁻¹ * m)) = fun _ => 0 := by
      funext z
      by_cases hz : z ∈ K
      · rw [Set.indicator_of_notMem (fun h : z⁻¹ * m ∈ K => hm (by simpa using K.mul_mem hz h))]; simp
      · rw [Set.indicator_of_notMem hz]; simp
    rw [e, hint_zero]

theorem hecke_mono {H : Type} [Group H] [TopologicalSpace H] {L L' : Subgroup H} {f : H → ℂ} (h : IsHecke L f) (hl : L' ≤ L) : IsHecke L' f :=
  ⟨h.1, fun k hk => h.2 k (hl hk)⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem level_inf {H : Type} [Group H] [TopologicalSpace H] (θ : H →* H) (K K₁ K₂ : Subgroup H)
    (h₁ : IsLevel θ K K₁) (h₂ : IsLevel θ K K₂) : IsLevel θ K (K₁ ⊓ K₂) :=
  ⟨h₁.1.inter h₂.1, le_trans inf_le_left h₁.2.1, fun k hk =>
    Subgroup.mem_inf.2 ⟨h₁.2.2 k (Subgroup.mem_inf.1 hk).1, h₂.2.2 k (Subgroup.mem_inf.1 hk).2⟩⟩

theorem levelFam_inf {H : Pl E → Type} [∀ w, Group (H w)] [∀ w, TopologicalSpace (H w)] (θ : ∀ w, H w →* H w)
    (K K₁ K₂ : ∀ w : Pl E, Subgroup (H w)) (h₁ : IsLevelFam θ K K₁) (h₂ : IsLevelFam θ K K₂) :
    IsLevelFam θ K (fun w => K₁ w ⊓ K₂ w) :=
  ⟨fun w => level_inf _ _ _ _ (h₁.1 w) (h₂.1 w), by
    filter_upwards [h₁.2, h₂.2] with w e₁ e₂
    rw [e₁, e₂, inf_idem]⟩

theorem isTestFunction_mulConvolution {φ φ' : ∀ w : Pl E, GLw a w × GLw b w → ℂ} (h : IsTestP φ) (h' : IsTestP φ') :
    IsTestP (fun w => mconv (φ w) (φ' w)) := by
  obtain ⟨K₁, K₂, hK₁, hK₂, hT⟩ := h
  obtain ⟨K₁', K₂', hK₁', hK₂', hT'⟩ := h'
  refine ⟨fun w => K₁ w ⊓ K₁' w, fun w => K₂ w ⊓ K₂' w, levelFam_inf _ _ _ _ hK₁ hK₁', levelFam_inf _ _ _ _ hK₂ hK₂',
    fun w => ?_, ?_⟩
  · exact hecke_mono (cv_hecke (K2 a b w) _ _ _ _ (hT.1 w) (hT'.1 w))
      (le_inf (Subgroup.prod_mono inf_le_left inf_le_left) (Subgroup.prod_mono inf_le_right inf_le_right))
  · filter_upwards [hT.2, hT'.2] with w e e'
    show cv (K2 a b w) (φ w) (φ' w) = _
    rw [e, e', cv_ind]

theorem placeTest {φ : ∀ w : Pl E, GLw a w × GLw b w → ℂ} (h : IsTestP φ) :
    ∃ L : ∀ w : Pl E, Subgroup (GLw a w × GLw b w),
      (∀ w, IsOpen (L w : Set (GLw a w × GLw b w)) ∧ L w ≤ K2 a b w ∧ IsHecke (L w) (φ w)) ∧
      ∀ᶠ w in cofinite, L w = K2 a b w ∧ φ w = (K2 a b w : Set (GLw a w × GLw b w)).indicator 1 := by
  obtain ⟨K₁, K₂, hK₁, hK₂, hT⟩ := h
  refine ⟨fun w => (K₁ w).prod (K₂ w), fun w => ⟨?_, Subgroup.prod_mono (hK₁.1 w).2.1 (hK₂.1 w).2.1, hT.1 w⟩, ?_⟩
  · rw [Subgroup.coe_prod]; exact (hK₁.1 w).1.prod (hK₂.1 w).1
  · filter_upwards [hK₁.2, hK₂.2, hT.2] with w e₁ e₂ e₃
    exact ⟨by rw [e₁, e₂], e₃⟩

def sf {S : Set (Pl E)} (φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ) : ∀ i : Slot S, GLw a i.pl × GLw b i.pl → ℂ
  | .inl w => φ₁ w.1
  | .inr w => φ₂ w.1

def slL {S : Set (Pl E)} (L₁ L₂ : ∀ w : Pl E, Subgroup (GLw a w × GLw b w)) :
    ∀ i : Slot S, Subgroup (GLw a i.pl × GLw b i.pl)
  | .inl w => L₁ w.1
  | .inr w => L₂ w.1

theorem ev_position {S : Set (Pl E)} (Q : Pl E → Prop) (hQ : ∀ᶠ w in cofinite, Q w) {P : Slot S → Prop}
    (h : ∀ i, Q i.pl → P i) : ∀ᶠ i in cofinite, P i := by
  rw [Filter.eventually_cofinite] at hQ ⊢
  refine (((hQ.preimage Subtype.val_injective.injOn).image (Sum.inl : {w // w ∈ S} → Slot S)).union
    ((hQ.preimage Subtype.val_injective.injOn).image
      (Sum.inr : {w // w ∈ S ∧ IsSplitAt w} → Slot S))).subset ?_
  intro i hi
  cases i with
  | inl w => exact Or.inl ⟨w, fun hq => hi (h _ hq), rfl⟩
  | inr w => exact Or.inr ⟨w, fun hq => hi (h _ hq), rfl⟩

theorem positionTest {S : Set (Pl E)} {φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ} (h₁ : IsTestP φ₁) (h₂ : IsTestP φ₂) :
    ∃ L : ∀ i : Slot S, Subgroup (GLw a i.pl × GLw b i.pl),
      (∀ i, IsOpen (L i : Set (GLw a i.pl × GLw b i.pl)) ∧ L i ≤ K2 a b i.pl ∧ IsHecke (L i) (sf φ₁ φ₂ i)) ∧
      ∀ᶠ i in cofinite, L i = K2 a b i.pl ∧ sf φ₁ φ₂ i = (K2 a b i.pl : Set (GLw a i.pl × GLw b i.pl)).indicator 1 := by
  obtain ⟨L₁, hL₁, e₁⟩ := placeTest h₁
  obtain ⟨L₂, hL₂, e₂⟩ := placeTest h₂
  refine ⟨slL L₁ L₂, fun i => ?_, ev_position _ (e₁.and e₂) fun i hi => ?_⟩
  · cases i with
    | inl w => exact hL₁ w.1
    | inr w => exact hL₂ w.1
  · cases i with
    | inl w => exact hi.1
    | inr w => exact hi.2

theorem finprod_sum_elim {α β : Type} (g : α ⊕ β → ℂ) (hfin : (Function.mulSupport g).Finite) :
    ∏ᶠ i, g i = (∏ᶠ x, g (Sum.inl x)) * ∏ᶠ y, g (Sum.inr y) := by
  conv_lhs => rw [← finprod_mem_univ, ← Set.range_inl_union_range_inr]
  rw [finprod_mem_union' Set.isCompl_range_inl_range_inr.disjoint (hfin.subset Set.inter_subset_right)
    (hfin.subset Set.inter_subset_right), finprod_mem_range Sum.inl_injective, finprod_mem_range Sum.inr_injective]

theorem reindex (S : Set (Pl E)) (A B : Pl E → ℂ)
    (hfin : (Function.mulSupport (Sum.elim (fun w : {w // w ∈ S} => A w.1)
      (fun w : {w // w ∈ S ∧ IsSplitAt w} => B w.1))).Finite) :
    ∏ᶠ w ∈ S, (A w * if IsSplitAt w then B w else 1) =
      ∏ᶠ i, Sum.elim (fun w : {w // w ∈ S} => A w.1) (fun w : {w // w ∈ S ∧ IsSplitAt w} => B w.1) i := by
  have hA : (S ∩ Function.mulSupport A).Finite := by
    refine ((hfin.preimage Sum.inl_injective.injOn).image Subtype.val).subset ?_
    rintro w ⟨hw, hA⟩
    exact ⟨⟨w, hw⟩, hA, rfl⟩
  have hB : (S ∩ Function.mulSupport fun w => if IsSplitAt w then B w else 1).Finite := by
    refine ((hfin.preimage Sum.inr_injective.injOn).image Subtype.val).subset ?_
    rintro w ⟨hw, hB⟩
    rw [Function.mem_mulSupport] at hB
    by_cases hs : IsSplitAt w
    · rw [if_pos hs] at hB
      exact ⟨⟨w, hw, hs⟩, hB, rfl⟩
    · rw [if_neg hs] at hB
      exact absurd rfl hB
  rw [finprod_mem_mul_distrib' hA hB, finprod_sum_elim _ hfin]
  have e₂ : ∏ᶠ w ∈ S, (if IsSplitAt w then B w else 1) = ∏ᶠ w ∈ {w | w ∈ S ∧ IsSplitAt w}, B w := by
    refine finprod_congr fun w => ?_
    by_cases hS : w ∈ S <;> by_cases hs : IsSplitAt w <;> simp [hS, hs]
  rw [e₂, ← finprod_set_coe_eq_finprod_mem S, ← finprod_set_coe_eq_finprod_mem]
  rfl

theorem fin_one {S : Set (Pl E)} (hev : ∀ x : Gf E a b, ∀ᶠ i : Slot S in cofinite, i.cp a b x ∈ K2 a b i.pl)
    {φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ}
    (hind : ∀ᶠ i : Slot S in cofinite, sf φ₁ φ₂ i = (K2 a b i.pl : Set (GLw a i.pl × GLw b i.pl)).indicator 1)
    (y : Gf E a b) : (Function.mulSupport fun i : Slot S => sf φ₁ φ₂ i (i.cp a b y)).Finite :=
  Filter.eventually_cofinite.1 ((hind.and (hev y)).mono fun i hi => by
    show sf φ₁ φ₂ i (Slot.cp a b i y) = 1
    rw [hi.1, Set.indicator_of_mem hi.2]; rfl)

theorem finFn_eq {S : Set (Pl E)} (hev : ∀ x : Gf E a b, ∀ᶠ i : Slot S in cofinite, i.cp a b x ∈ K2 a b i.pl)
    {φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ}
    (hind : ∀ᶠ i : Slot S in cofinite, sf φ₁ φ₂ i = (K2 a b i.pl : Set (GLw a i.pl × GLw b i.pl)).indicator 1)
    (y : Gf E a b) : finFn S φ₁ φ₂ y = ∏ᶠ i : Slot S, sf φ₁ φ₂ i (i.cp a b y) := by
  have key : (fun i : Slot S => sf φ₁ φ₂ i (i.cp a b y)) = Sum.elim (fun w : {w // w ∈ S} => φ₁ w.1 (atW w.1 y))
      (fun w : {w // w ∈ S ∧ IsSplitAt w} => φ₂ w.1 (atW w.1 (thP E a b y))) := by
    funext i; cases i <;> rfl
  have hf := fin_one hev hind y
  rw [key] at hf
  unfold finFn
  rw [reindex S (fun w => φ₁ w (atW w y)) (fun w => φ₂ w (atW w (thP E a b y))) hf, ← key]

def pc {S : Set (Pl E)} (hmul : ∀ (i : Slot S) (x y : Gf E a b), i.cp a b (x * y) = i.cp a b x * i.cp a b y)
    (i : Slot S) : Gf E a b →* GLw a i.pl × GLw b i.pl := MonoidHom.mk' (i.cp a b) (hmul i)

def levelSub {S : Set (Pl E)} (hmul : ∀ (i : Slot S) (x y : Gf E a b), i.cp a b (x * y) = i.cp a b x * i.cp a b y)
    (L : ∀ i : Slot S, Subgroup (GLw a i.pl × GLw b i.pl)) : Subgroup (Gf E a b) :=
  ⨅ i, (L i).comap (pc hmul i)

theorem mem_levelSub {S : Set (Pl E)} (hmul : ∀ (i : Slot S) (x y : Gf E a b), i.cp a b (x * y) = i.cp a b x * i.cp a b y)
    (L : ∀ i : Slot S, Subgroup (GLw a i.pl × GLw b i.pl)) (x : Gf E a b) :
    x ∈ levelSub hmul L ↔ ∀ i, i.cp a b x ∈ L i := Subgroup.mem_iInf

theorem isOpen_maximal_pair : IsOpen (((Kf E a).prod (Kf E b) : Subgroup (Gf E a b)) : Set (Gf E a b)) := by
  rw [Subgroup.coe_prod]; exact (GlobalTheory.T.finite_kernel_compact_open E a).1.prod (GlobalTheory.T.finite_kernel_compact_open E b).1

theorem isCompact_maximal_pair : IsCompact (((Kf E a).prod (Kf E b) : Subgroup (Gf E a b)) : Set (Gf E a b)) := by
  rw [Subgroup.coe_prod]; exact (GlobalTheory.T.finite_kernel_compact_open E a).2.prod (GlobalTheory.T.finite_kernel_compact_open E b).2

theorem isOpen_levelSub {S : Set (Pl E)}
    (hmul : ∀ (i : Slot S) (x y : Gf E a b), i.cp a b (x * y) = i.cp a b x * i.cp a b y)
    (hcont : ∀ i : Slot S, Continuous (i.cp a b))
    (hK : ∀ x, x ∈ (Kf E a).prod (Kf E b) ↔ ∀ i : Slot S, i.cp a b x ∈ K2 a b i.pl)
    (L : ∀ i : Slot S, Subgroup (GLw a i.pl × GLw b i.pl))
    (hL : ∀ i, IsOpen (L i : Set (GLw a i.pl × GLw b i.pl)) ∧ L i ≤ K2 a b i.pl)
    (hLe : ∀ᶠ i in cofinite, L i = K2 a b i.pl) : IsOpen (levelSub hmul L : Set (Gf E a b)) := by
  have hT := Filter.eventually_cofinite.1 hLe
  have e : (levelSub hmul L : Set (Gf E a b)) = (((Kf E a).prod (Kf E b) : Subgroup (Gf E a b)) : Set (Gf E a b)) ∩
      ⋂ i ∈ {i | ¬ L i = K2 a b i.pl}, (i.cp a b) ⁻¹' (L i : Set (GLw a i.pl × GLw b i.pl)) := by
    ext x
    simp only [SetLike.mem_coe, mem_levelSub, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, hK,
      Set.mem_setOf_eq]
    constructor
    · intro h; exact ⟨fun i => (hL i).2 (h i), fun i _ => h i⟩
    · rintro ⟨h₁, h₂⟩ i
      by_cases hi : L i = K2 a b i.pl
      · rw [hi]; exact h₁ i
      · exact h₂ i hi
  rw [e]
  exact isOpen_maximal_pair.inter (hT.isOpen_biInter fun i _ => (hL i).1.preimage (hcont i))

def cset {S : Set (Pl E)} (φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ) (i : Slot S) : Set (GLw a i.pl × GLw b i.pl) :=
  if sf φ₁ φ₂ i = (K2 a b i.pl : Set (GLw a i.pl × GLw b i.pl)).indicator 1 then (K2 a b i.pl : Set _)
  else tsupport (sf φ₁ φ₂ i)

theorem vol_ne (B : Block E) : B.vol ≠ 0 := by
  haveI := B.hν
  unfold Block.vol
  have hpos := (isOpen_maximal_pair (E := E) (a := B.a) (b := B.b)).measure_pos B.ν ⟨1, Subgroup.one_mem _⟩
  have hfin := (isCompact_maximal_pair (E := E) (a := B.a) (b := B.b)).measure_lt_top (μ := B.ν)
  exact Complex.ofReal_ne_zero.2 (ENNReal.toReal_pos hpos.ne' hfin.ne).ne'

theorem finFn_hcs {S : Set (Pl E)} (hev : ∀ x : Gf E a b, ∀ᶠ i : Slot S in cofinite, i.cp a b x ∈ K2 a b i.pl)
    (hcpt : ∀ C : ∀ i : Slot S, Set (GLw a i.pl × GLw b i.pl), (∀ i, IsCompact (C i)) →
      (∀ᶠ i in cofinite, C i = K2 a b i.pl) → IsCompact {x : Gf E a b | ∀ i : Slot S, i.cp a b x ∈ C i})
    {φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ} (h₁ : IsTestP φ₁) (h₂ : IsTestP φ₂) :
    HasCompactSupport (finFn S φ₁ φ₂) := by
  obtain ⟨L, hL, hLe⟩ := positionTest (S := S) h₁ h₂
  have hind := hLe.mono fun i hi => hi.2
  have hC : ∀ i : Slot S, IsCompact (cset φ₁ φ₂ i) := fun i => by
    unfold cset
    by_cases h : sf φ₁ φ₂ i = (K2 a b i.pl : Set (GLw a i.pl × GLw b i.pl)).indicator 1
    · rw [if_pos h]; exact (GlobalTheory.BCT.StTw2Add.isOpen_isCompact_KK a b i.pl).2
    · rw [if_neg h]; exact (hL i).2.2.1
  have hCe : ∀ᶠ i in cofinite, cset φ₁ φ₂ i = K2 a b i.pl := hLe.mono fun i hi => if_pos hi.2
  change IsCompact (closure (Function.support (finFn S φ₁ φ₂)))
  refine IsCompact.closure_of_subset (hcpt _ hC hCe) fun x hx i => ?_
  rw [Function.mem_support, finFn_eq hev hind] at hx
  have hne : sf φ₁ φ₂ i (i.cp a b x) ≠ 0 := fun h0 => hx (finprod_eq_zero _ i h0 (fin_one hev hind x))
  unfold cset
  by_cases h : sf φ₁ φ₂ i = (K2 a b i.pl : Set (GLw a i.pl × GLw b i.pl)).indicator 1
  · rw [if_pos h]
    by_contra hn
    rw [h, Set.indicator_of_notMem hn] at hne
    exact hne rfl
  · rw [if_neg h]; exact subset_tsupport _ hne

theorem finFn_inv {S : Set (Pl E)}
    (hmul : ∀ (i : Slot S) (x y : Gf E a b), i.cp a b (x * y) = i.cp a b x * i.cp a b y)
    (hev : ∀ x : Gf E a b, ∀ᶠ i : Slot S in cofinite, i.cp a b x ∈ K2 a b i.pl)
    {φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ} (L : ∀ i : Slot S, Subgroup (GLw a i.pl × GLw b i.pl))
    (hH : ∀ i, IsHecke (L i) (sf φ₁ φ₂ i))
    (hind : ∀ᶠ i : Slot S in cofinite, sf φ₁ φ₂ i = (K2 a b i.pl : Set (GLw a i.pl × GLw b i.pl)).indicator 1) :
    ∀ u ∈ levelSub hmul L, ∀ h, finFn S φ₁ φ₂ (u * h) = finFn S φ₁ φ₂ h ∧ finFn S φ₁ φ₂ (h * u) = finFn S φ₁ φ₂ h := by
  intro u hu h
  have hu' := (mem_levelSub hmul L u).1 hu
  simp only [finFn_eq hev hind, hmul]
  exact ⟨finprod_congr fun i => ((hH i).2 _ (hu' i) _).1, finprod_congr fun i => ((hH i).2 _ (hu' i) _).2⟩

theorem conv_eq (h1 : IntHint) (h2 : HintProd) (B : Block E) {S : Set (Pl E)}
    (hmul : ∀ (i : Slot S) (x y : Gf E B.a B.b), i.cp B.a B.b (x * y) = i.cp B.a B.b x * i.cp B.a B.b y)
    (hcont : ∀ i : Slot S, Continuous (i.cp B.a B.b))
    (hinj : ∀ x y : Gf E B.a B.b, (∀ i : Slot S, i.cp B.a B.b x = i.cp B.a B.b y) → x = y)
    (hsurj : ∀ y : ∀ i : Slot S, GLw B.a i.pl × GLw B.b i.pl, (∀ᶠ i in cofinite, y i ∈ K2 B.a B.b i.pl) →
      ∃ x, ∀ i : Slot S, i.cp B.a B.b x = y i)
    (hev : ∀ x : Gf E B.a B.b, ∀ᶠ i : Slot S in cofinite, i.cp B.a B.b x ∈ K2 B.a B.b i.pl)
    (hK : ∀ x, x ∈ (Kf E B.a).prod (Kf E B.b) ↔ ∀ i : Slot S, i.cp B.a B.b x ∈ K2 B.a B.b i.pl)
    (hcpt : ∀ C : ∀ i : Slot S, Set (GLw B.a i.pl × GLw B.b i.pl), (∀ i, IsCompact (C i)) →
      (∀ᶠ i in cofinite, C i = K2 B.a B.b i.pl) → IsCompact {x : Gf E B.a B.b | ∀ i : Slot S, i.cp B.a B.b x ∈ C i})
    {φ₁ φ₂ φ₁' φ₂' : ∀ w : Pl E, LF B.a B.b w} (h₁ : IsTestP φ₁) (h₂ : IsTestP φ₂) (h₁' : IsTestP φ₁')
    (h₂' : IsTestP φ₂') (g : Hf E B.a B.b) :
    ∫ h, finFn S φ₁ φ₂ h * finFn S φ₁' φ₂' (h⁻¹ * g) ∂B.ν =
      B.vol * finFn S (fun w => mconv (φ₁ w) (φ₁' w)) (fun w => mconv (φ₂ w) (φ₂' w)) g := by
  haveI := B.hν
  haveI : BorelSpace (Hf E B.a B.b) := ⟨rfl⟩
  obtain ⟨L, hL, hLe⟩ := positionTest (S := S) h₁ h₂
  obtain ⟨L', hL', hLe'⟩ := positionTest (S := S) h₁' h₂'
  obtain ⟨L'', _, hLe''⟩ := positionTest (S := S) (isTestFunction_mulConvolution h₁ h₁') (isTestFunction_mulConvolution h₂ h₂')
  have hind := hLe.mono fun i hi => hi.2
  have hind' := hLe'.mono fun i hi => hi.2
  have hind'' := hLe''.mono fun i hi => hi.2
  have hU : IsOpen ((levelSub hmul L ⊓ levelSub hmul L' : Subgroup (Gf E B.a B.b)) : Set (Gf E B.a B.b)) :=
    (isOpen_levelSub hmul hcont hK L (fun i => ⟨(hL i).1, (hL i).2.1⟩) (hLe.mono fun i hi => hi.1)).inter
      (isOpen_levelSub hmul hcont hK L' (fun i => ⟨(hL' i).1, (hL' i).2.1⟩) (hLe'.mono fun i hi => hi.1))
  have hF := finFn_inv hmul hev L (fun i => (hL i).2.2) hind
  have hF' := finFn_inv hmul hev L' (fun i => (hL' i).2.2) hind'
  rw [h1 (Hf E B.a B.b) B.ν ((Kf E B.a).prod (Kf E B.b)) (levelSub hmul L ⊓ levelSub hmul L')
    (fun h => finFn S φ₁ φ₂ h * finFn S φ₁' φ₂' (h⁻¹ * g)) isOpen_maximal_pair isCompact_maximal_pair hU
    ((finFn_hcs hev hcpt h₁ h₂).mul_right) (fun u hu x => by
      rw [(hF u (Subgroup.mem_inf.1 hu).1 x).2, _root_.mul_inv_rev, mul_assoc,
        (hF' u⁻¹ (inv_mem (Subgroup.mem_inf.1 hu).2) _).1]) B.hν']
  refine congrArg₂ (· * ·) rfl ?_
  have hp := h2 (Slot S) (Hf E B.a B.b) (fun i => GLw B.a i.pl × GLw B.b i.pl) (pc hmul) ((Kf E B.a).prod (Kf E B.b))
    (fun i => K2 B.a B.b i.pl) (fun i => L i ⊓ L' i)
    (fun i m => sf φ₁ φ₂ i m * sf φ₁' φ₂' i (m⁻¹ * i.cp B.a B.b g)) hinj hsurj hev hK (fun i =>
      ⟨(GlobalTheory.BCT.StTw2Add.isOpen_isCompact_KK B.a B.b i.pl).2, (GlobalTheory.BCT.StTw2Add.isOpen_isCompact_KK B.a B.b i.pl).1,
        (hL i).1.inter (hL' i).1,
        HasCompactSupport.mul_right (f' := fun m => sf φ₁' φ₂' i (m⁻¹ * i.cp B.a B.b g)) (hL i).2.2.1,
        fun u hu x => by
          show sf φ₁ φ₂ i (x * u) * sf φ₁' φ₂' i ((x * u)⁻¹ * i.cp B.a B.b g) =
            sf φ₁ φ₂ i x * sf φ₁' φ₂' i (x⁻¹ * i.cp B.a B.b g)
          rw [((hL i).2.2.2 u (Subgroup.mem_inf.1 hu).1 x).2, _root_.mul_inv_rev, mul_assoc,
            ((hL' i).2.2.2 u⁻¹ (inv_mem (Subgroup.mem_inf.1 hu).2) _).1]⟩) (by
      filter_upwards [hind, hind', hev g] with i e e' hg
      funext m
      show sf φ₁ φ₂ i m * sf φ₁' φ₂' i (m⁻¹ * i.cp B.a B.b g) = _
      rw [e, e']
      by_cases hm : m ∈ K2 B.a B.b i.pl
      · rw [Set.indicator_of_mem hm, Set.indicator_of_mem (mul_mem (inv_mem hm) hg)]; simp
      · rw [Set.indicator_of_notMem hm]; simp)
  have e1 : (fun h => finFn S φ₁ φ₂ h * finFn S φ₁' φ₂' (h⁻¹ * g)) = fun x =>
      ∏ᶠ i : Slot S, sf φ₁ φ₂ i (pc hmul i x) * sf φ₁' φ₂' i ((pc hmul i x)⁻¹ * i.cp B.a B.b g) := by
    funext x
    rw [finFn_eq hev hind, finFn_eq hev hind', ← finprod_mul_distrib (fin_one hev hind x) (fin_one hev hind' _)]
    refine finprod_congr fun i => ?_
    have hc : i.cp B.a B.b (x⁻¹ * g) = (i.cp B.a B.b x)⁻¹ * i.cp B.a B.b g := by
      rw [show i.cp B.a B.b (x⁻¹ * g) = pc hmul i (x⁻¹ * g) from rfl, map_mul, map_inv]; rfl
    rw [hc]; rfl
  have e2 : finFn S (fun w => mconv (φ₁ w) (φ₁' w)) (fun w => mconv (φ₂ w) (φ₂' w)) g =
      ∏ᶠ i : Slot S, hint (K2 B.a B.b i.pl) (fun m => sf φ₁ φ₂ i m * sf φ₁' φ₂' i (m⁻¹ * i.cp B.a B.b g)) := by
    rw [finFn_eq hev hind'']
    exact finprod_congr fun i => by cases i <;> rfl
  rw [e1, hp, e2]

end FinConv

theorem finConv (h1 : IntHint) (h2 : HintProd) (h3 : Slots) : FinConv := by
  intro E _ _ _ B S hS
  obtain ⟨hmul, hcont, hinj, hsurj, hev, hK, hcpt⟩ := h3 E B.a B.b S hS
  refine ⟨FinConv.vol_ne B, fun φ₁ φ₂ h₁ h₂ => ⟨FinConv.finFn_hcs hev hcpt h₁ h₂, ?_, fun φ₁' φ₂' h₁' h₂' =>
    ⟨FinConv.isTestFunction_mulConvolution h₁ h₁', FinConv.isTestFunction_mulConvolution h₂ h₂', fun g =>
      FinConv.conv_eq h1 h2 B hmul hcont hinj hsurj hev hK hcpt h₁ h₂ h₁' h₂' g⟩⟩⟩
  obtain ⟨L, hL, hLe⟩ := FinConv.positionTest (S := S) h₁ h₂
  exact ⟨FinConv.levelSub hmul L,
    FinConv.isOpen_levelSub hmul hcont hK L (fun i => ⟨(hL i).1, (hL i).2.1⟩) (hLe.mono fun i hi => hi.1),
    FinConv.finFn_inv hmul hev L (fun i => (hL i).2.2) (hLe.mono fun i hi => hi.2)⟩

end PositivityTheory.Rg.BcB.F
