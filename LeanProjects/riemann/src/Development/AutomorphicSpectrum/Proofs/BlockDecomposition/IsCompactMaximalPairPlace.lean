import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.FmTools
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinsumOutOfLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelFamInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThLInvolutive
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.FA
open scoped Classical

attribute [local instance] borelG borelF borelH

namespace GlobalTheory.CompanionTheory.FmPowP

section Generic

variable {H : Type} [Group H]

theorem hint_ind_left (K U : Subgroup H) (hUK : U ≤ K) (hi : U.relIndex K ≠ 0) (f : H → ℂ)
    (hl : ∀ u ∈ U, ∀ g, f (u * g) = f g) (m : H) :
    hint K (fun z => (U : Set H).indicator (fun _ => ((U.relIndex K : ℕ) : ℂ)) z * f (z⁻¹ * m)) = f m := by
  have hC : ((U.relIndex K : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hi
  rw [GlobalTheory.CompanionTheory.HintLevel.hint_eq_level H K U _ hUK (fun k hk x => ?_) hi]
  · rw [finsum_eq_single _ ((1 : H) : H ⧸ U)]
    · have hmem : (((1 : H) : H ⧸ U).out : H) ∈ U := by
        have := QuotientGroup.out_eq' ((1 : H) : H ⧸ U)
        simpa using (QuotientGroup.eq.1 this)
      rw [Set.indicator_of_mem (by exact hmem), hl _ (inv_mem hmem)]
      field_simp
    · intro q hq
      have hnot : (q.out : H) ∉ U := fun h => hq (by
        rw [← QuotientGroup.out_eq' q]
        exact QuotientGroup.eq.2 (by simpa using inv_mem h))
      rw [Set.indicator_of_notMem (by exact hnot), zero_mul]
  · have h1 : (x * k ∈ (U : Set H)) ↔ x ∈ (U : Set H) := Subgroup.mul_mem_cancel_right U hk
    have h2 : (x * k)⁻¹ * m = k⁻¹ * (x⁻¹ * m) := by group
    rw [h2, hl _ (inv_mem hk)]
    by_cases hx : x ∈ (U : Set H)
    · rw [Set.indicator_of_mem (h1.2 hx), Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem (fun h => hx (h1.1 h)), Set.indicator_of_notMem hx]

theorem hint_ind_right (K U : Subgroup H) (hUK : U ≤ K) (hi : U.relIndex K ≠ 0) (f : H → ℂ)
    (hr : ∀ u ∈ U, ∀ g, f (g * u) = f g) (m : H) :
    hint K (fun z => f z * (U : Set H).indicator (fun _ => ((U.relIndex K : ℕ) : ℂ)) (z⁻¹ * m)) = f m := by
  have hC : ((U.relIndex K : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hi
  rw [GlobalTheory.CompanionTheory.HintLevel.hint_eq_level H K U _ hUK (fun k hk x => ?_) hi]
  · rw [finsum_eq_single _ ((m : H) : H ⧸ U)]
    · obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U m
      have hmem : ((((m : H) : H ⧸ U).out : H))⁻¹ * m ∈ U := by
        rw [hu]; simp
      rw [Set.indicator_of_mem (by exact hmem), hu, hr _ u.2]
      field_simp
    · intro q hq
      have hnot : ((q.out : H))⁻¹ * m ∉ U := fun h => hq (by
        rw [← QuotientGroup.out_eq' q]
        exact QuotientGroup.eq.2 h)
      rw [Set.indicator_of_notMem (by exact hnot), mul_zero]
  · have h2 : (x * k)⁻¹ * m = k⁻¹ * (x⁻¹ * m) := by group
    have h1 : (k⁻¹ * (x⁻¹ * m) ∈ (U : Set H)) ↔ x⁻¹ * m ∈ (U : Set H) :=
      Subgroup.mul_mem_cancel_left U (inv_mem hk)
    rw [hr _ hk, h2]
    by_cases hx : x⁻¹ * m ∈ (U : Set H)
    · rw [Set.indicator_of_mem (h1.2 hx), Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem (fun h => hx (h1.1 h)), Set.indicator_of_notMem hx]

theorem relIndex_ne_of_open [TopologicalSpace H] [IsTopologicalGroup H] {K U : Subgroup H}
    (hU : IsOpen (U : Set H)) (hK : IsCompact (K : Set H)) : U.relIndex K ≠ 0 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have ho : IsOpen ((U.subgroupOf K : Subgroup K) : Set K) := hU.preimage continuous_subtype_val
  haveI : Finite (K ⧸ U.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ ho
  exact Subgroup.index_ne_zero_of_finite

end Generic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem isCompact_maximal_pair_place (w : Pl E) : IsCompact ((K2 a b w : Subgroup _) : Set (GLw a w × GLw b w)) := by
  have h1 := (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).2
  have h2 := (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).2
  simpa [Subgroup.coe_prod] using h1.prod h2

theorem mconv_idem_left {w : Pl E} {U : Subgroup (GLw a w × GLw b w)} (hU : IsOpen (U : Set (GLw a w × GLw b w)))
    (hUK : U ≤ K2 a b w) (f : LF a b w) (hl : ∀ u ∈ U, ∀ g, f (u * g) = f g) :
    PositivityTheory.Rg.BcN.F2.mconv (idem U) f = f := by
  funext m
  exact hint_ind_left _ U hUK (relIndex_ne_of_open hU (isCompact_maximal_pair_place w)) f hl m

theorem mconv_idem_right {w : Pl E} {U : Subgroup (GLw a w × GLw b w)} (hU : IsOpen (U : Set (GLw a w × GLw b w)))
    (hUK : U ≤ K2 a b w) (f : LF a b w) (hr : ∀ u ∈ U, ∀ g, f (g * u) = f g) :
    PositivityTheory.Rg.BcN.F2.mconv f (idem U) = f := by
  funext m
  exact hint_ind_right _ U hUK (relIndex_ne_of_open hU (isCompact_maximal_pair_place w)) f hr m

theorem mconv_zero_left {w : Pl E} (f : LF a b w) : PositivityTheory.Rg.BcN.F2.mconv (0 : LF a b w) f = 0 := by
  funext m
  simpa [PositivityTheory.Rg.BcN.F2.mconv] using GlobalTheory.CompanionTheory.FamClP.hint_zero (K2 a b w)

theorem mconv_zero_right {w : Pl E} (f : LF a b w) : PositivityTheory.Rg.BcN.F2.mconv f (0 : LF a b w) = 0 := by
  funext m
  simpa [PositivityTheory.Rg.BcN.F2.mconv] using GlobalTheory.CompanionTheory.FamClP.hint_zero (K2 a b w)

theorem idem_left {w : Pl E} (U : Subgroup (GLw a w × GLw b w)) (u) (hu : u ∈ U) (g) : idem U (u * g) = idem U g := by
  have h1 : (u * g ∈ (U : Set (GLw a w × GLw b w))) ↔ g ∈ (U : Set (GLw a w × GLw b w)) :=
    Subgroup.mul_mem_cancel_left U hu
  unfold idem
  by_cases hx : g ∈ (U : Set (GLw a w × GLw b w))
  · rw [Set.indicator_of_mem (h1.2 hx), Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem (fun h => hx (h1.1 h)), Set.indicator_of_notMem hx]

theorem idem_right {w : Pl E} (U : Subgroup (GLw a w × GLw b w)) (u) (hu : u ∈ U) (g) : idem U (g * u) = idem U g := by
  have h1 : (g * u ∈ (U : Set (GLw a w × GLw b w))) ↔ g ∈ (U : Set (GLw a w × GLw b w)) :=
    Subgroup.mul_mem_cancel_right U hu
  unfold idem
  by_cases hx : g ∈ (U : Set (GLw a w × GLw b w))
  · rw [Set.indicator_of_mem (h1.2 hx), Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem (fun h => hx (h1.1 h)), Set.indicator_of_notMem hx]

theorem continuous_thL (n : ℕ) (w : Pl E) : Continuous (thL n w) := by
  unfold thL
  split_ifs with h
  · exact continuous_id
  · refine GlobalTheory.ThetaPull.continuous_thetaGL _ ?_
    unfold cj
    split_ifs with h'
    · exact h'.choose_spec.1
    · exact continuous_id

theorem exists_level_one (n : ℕ) (w : Pl E) {A : Subgroup (GLw n w)} (hA : IsOpen (A : Set (GLw n w)))
    (hAK : A ≤ GlobalTheory.LFun.KGL w n) :
    ∃ V : Subgroup (GLw n w), IsLevel (thL n w) (GlobalTheory.LFun.KGL w n) V ∧ V ≤ A := by
  refine ⟨A ⊓ A.comap (thL n w), ⟨?_, inf_le_left.trans hAK, fun k hk => ⟨hk.2, ?_⟩⟩, inf_le_left⟩
  · rw [Subgroup.coe_inf]
    exact hA.inter (hA.preimage (continuous_thL n w))
  · show thL n w (thL n w k) ∈ A
    rw [GlobalTheory.BCT.TwistInvol.thL_involutive E n w k]
    exact hk.1

theorem exists_level {w : Pl E} {U : Subgroup (GLw a w × GLw b w)} (hU : IsOpen (U : Set (GLw a w × GLw b w)))
    (hUK : U ≤ K2 a b w) :
    ∃ (V₁ : Subgroup (GLw a w)) (V₂ : Subgroup (GLw b w)), IsLevel (thL a w) (GlobalTheory.LFun.KGL w a) V₁ ∧
      IsLevel (thL b w) (GlobalTheory.LFun.KGL w b) V₂ ∧ V₁.prod V₂ ≤ U := by
  obtain ⟨V₁, h₁, l₁⟩ := exists_level_one a w (A := U.comap (MonoidHom.inl (GLw a w) (GLw b w)))
    (hU.preimage (f := fun x => (x, (1 : GLw b w))) (continuous_id.prodMk continuous_const)) (fun x hx => (hUK hx).1)
  obtain ⟨V₂, h₂, l₂⟩ := exists_level_one b w (A := U.comap (MonoidHom.inr (GLw a w) (GLw b w)))
    (hU.preimage (f := fun x => ((1 : GLw a w), x)) (continuous_const.prodMk continuous_id)) (fun x hx => (hUK hx).2)
  refine ⟨V₁, V₂, h₁, h₂, fun x hx => ?_⟩
  have : x = (x.1, 1) * (1, x.2) := by simp
  rw [this]
  exact mul_mem (l₁ hx.1) (l₂ hx.2)

theorem isHecke_idem {w : Pl E} {U V : Subgroup (GLw a w × GLw b w)} (hU : IsOpen (U : Set (GLw a w × GLw b w)))
    (hUK : U ≤ K2 a b w) (hVU : V ≤ U) : IsHecke V (idem U) := by
  have hc : IsCompact (U : Set (GLw a w × GLw b w)) :=
    (isCompact_maximal_pair_place w).of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hU) hUK
  refine ⟨HasCompactSupport.intro' hc (Subgroup.isClosed_of_isOpen _ hU) fun y hy => ?_,
    fun k hk x => ⟨idem_left U k (hVU hk) x, idem_right U k (hVU hk) x⟩⟩
  exact Set.indicator_of_notMem hy _

section Sel

variable {κ : Pl E → Type} [∀ w, Fintype (κ w)]

def sel (U : ∀ w : Pl E, Subgroup (GLw a w × GLw b w)) (L : LM κ a b) (Q : Finset (Pl E)) : LM κ a b :=
  ⟨fun w x y => if w ∈ Q then L.m w x y else if x = y then idem (U w) else 0, L.s, L.t⟩

theorem sel_ok {U : ∀ w : Pl E, Subgroup (GLw a w × GLw b w)} {L : LM κ a b} {P : Finset (Pl E)} (hU : IsLev U)
    (hok : L.Ok P) (Q : Finset (Pl E)) : (sel U L Q).Ok P := by
  refine ⟨fun x y => ?_, hok.2⟩
  obtain ⟨K₁, K₂, h₁, h₂, hT⟩ := hok.1 x y
  choose V₁ V₂ hV₁ hV₂ hV using fun w => exists_level (hU.1 w).1 (hU.1 w).2
  have hev : ∀ᶠ w in cofinite, w ∉ P := P.finite_toSet.compl_mem_cofinite
  have hent : ∀ w, ¬ (w ∈ P ∧ w ∉ Q) → (sel U L Q).ent P x y w = L.ent P x y w := by
    intro w hw
    unfold LM.ent
    split_ifs with hP
    · have : w ∈ Q := by_contra fun h => hw ⟨hP, h⟩
      simp [sel, this]
    · rfl
  refine ⟨fun w => if w ∈ P ∧ w ∉ Q then V₁ w else K₁ w, fun w => if w ∈ P ∧ w ∉ Q then V₂ w else K₂ w,
    ⟨fun w => ?_, ?_⟩, ⟨fun w => ?_, ?_⟩, fun w => ?_, ?_⟩
  · dsimp only
    split_ifs
    · exact hV₁ w
    · exact h₁.1 w
  · filter_upwards [hev, h₁.2] with w hw hk
    rw [if_neg fun h => hw h.1, hk]
  · dsimp only
    split_ifs
    · exact hV₂ w
    · exact h₂.1 w
  · filter_upwards [hev, h₂.2] with w hw hk
    rw [if_neg fun h => hw h.1, hk]
  · dsimp only
    by_cases hw : w ∈ P ∧ w ∉ Q
    · rw [if_pos hw, if_pos hw]
      have : (sel U L Q).ent P x y w = if x ⟨w, hw.1⟩ = y ⟨w, hw.1⟩ then idem (U w) else 0 := by
        unfold LM.ent
        rw [dif_pos hw.1]
        simp [sel, hw.2]
      rw [this]
      split_ifs
      · exact isHecke_idem (hU.1 w).1 (hU.1 w).2 (hV w)
      · exact ⟨HasCompactSupport.zero, fun _ _ _ => ⟨rfl, rfl⟩⟩
    · rw [if_neg hw, if_neg hw, hent w hw]
      exact hT.1 w
  · filter_upwards [hev, hT.2] with w hw hk
    rw [hent w fun h => hw h.1, hk]

end Sel

section Alg

variable {κ : Pl E → Type} [∀ w, Fintype (κ w)]

theorem sum_mconv_right {k : Type} [Fintype k] {w : Pl E} (f : k → LF a b w) (g : LF a b w) (y : k) :
    ∑ z, PositivityTheory.Rg.BcN.F2.mconv (f z) (if z = y then g else 0) = PositivityTheory.Rg.BcN.F2.mconv (f y) g := by
  rw [Finset.sum_eq_single y]
  · simp
  · intro z _ hz
    rw [if_neg hz, mconv_zero_right]
  · simp

theorem sum_mconv_left {k : Type} [Fintype k] {w : Pl E} (f : k → LF a b w) (g : LF a b w) (x : k) :
    ∑ z, PositivityTheory.Rg.BcN.F2.mconv (if x = z then g else 0) (f z) = PositivityTheory.Rg.BcN.F2.mconv g (f x) := by
  rw [Finset.sum_eq_single x]
  · simp
  · intro z _ hz
    rw [if_neg (Ne.symm hz), mconv_zero_left]
  · simp

theorem mconv_idem_idem {w : Pl E} {U : Subgroup (GLw a w × GLw b w)} (hU : IsOpen (U : Set (GLw a w × GLw b w)))
    (hUK : U ≤ K2 a b w) : PositivityTheory.Rg.BcN.F2.mconv (idem U) (idem U) = idem U :=
  mconv_idem_left hU hUK _ (idem_left U)

theorem sel_mul_ent {U : ∀ w : Pl E, Subgroup (GLw a w × GLw b w)} {L : LM κ a b} {P : Finset (Pl E)} (hU : IsLev U)
    (hs : ∀ w, L.s w = idem (U w))
    (hinv : ∀ w ∈ P, ∀ x y, ∀ u ∈ U w, ∀ g, L.m w x y (u * g) = L.m w x y g ∧ L.m w x y (g * u) = L.m w x y g)
    {Q₁ Q₂ : Finset (Pl E)} (hQ₁ : Q₁ ⊆ P) (hQ₂ : Q₂ ⊆ P) (hd : Disjoint Q₁ Q₂) (x y : ∀ w : P, κ w) :
    ((sel U L Q₁).mul (sel U L Q₂)).ent P x y = (sel U L (Q₁ ∪ Q₂)).ent P x y := by
  funext w
  unfold LM.ent
  split_ifs with hw
  · show ∑ z, PositivityTheory.Rg.BcN.F2.mconv ((sel U L Q₁).m w _ z) ((sel U L Q₂).m w z _) = (sel U L (Q₁ ∪ Q₂)).m w _ _
    simp only [sel]
    by_cases h₁ : w ∈ Q₁
    · have h₂ : w ∉ Q₂ := Finset.disjoint_left.1 hd h₁
      simp only [h₁, h₂, if_true, if_false, Finset.mem_union, true_or]
      rw [sum_mconv_right]
      exact mconv_idem_right (hU.1 w).1 (hU.1 w).2 _ fun u hu g => (hinv w hw _ _ u hu g).2
    · by_cases h₂ : w ∈ Q₂
      · simp only [h₁, h₂, if_true, if_false, Finset.mem_union, or_true]
        rw [sum_mconv_left]
        exact mconv_idem_left (hU.1 w).1 (hU.1 w).2 _ fun u hu g => (hinv w hw _ _ u hu g).1
      · simp only [h₁, h₂, if_false, Finset.mem_union, or_self]
        rw [sum_mconv_left (fun z => if z = _ then idem (U w) else 0)]
        split_ifs with hxy
        · exact mconv_idem_idem (hU.1 w).1 (hU.1 w).2
        · exact mconv_zero_right _
  · show PositivityTheory.Rg.BcN.F2.mconv (L.s w) (L.s w) = L.s w
    rw [hs w]
    exact mconv_idem_idem (hU.1 w).1 (hU.1 w).2

end Alg

section Lev

theorem hasLev_zero : HasLev (0 : H E a b → ℂ) :=
  ⟨⊤, isOpen_univ, fun _ _ _ => rfl⟩

theorem hasLev_add {G G' : H E a b → ℂ} (h : HasLev G) (h' : HasLev G') : HasLev (G + G') := by
  obtain ⟨U, hU, hG⟩ := h
  obtain ⟨U', hU', hG'⟩ := h'
  refine ⟨U ⊓ U', by rw [Subgroup.coe_inf]; exact hU.inter hU', fun u hu x => ?_⟩
  simp [hG u hu.1 x, hG' u hu.2 x]

theorem ofLev_zero (S : Set (Pl E)) (U₁ U₂ : ∀ w : Pl E, Subgroup (GLw a w × GLw b w)) :
    OfLev S U₁ U₂ (0 : H E a b → ℂ) :=
  ⟨hasLev_zero, fun _ _ => ⟨zero_mem _, fun _ => zero_mem _⟩⟩

theorem ofLev_add {S : Set (Pl E)} {U₁ U₂ : ∀ w : Pl E, Subgroup (GLw a w × GLw b w)} {G G' : H E a b → ℂ}
    (h : OfLev S U₁ U₂ G) (h' : OfLev S U₁ U₂ G') : OfLev S U₁ U₂ (G + G') :=
  ⟨hasLev_add h.1 h'.1, fun w hw => ⟨add_mem (h.2 w hw).1 (h'.2 w hw).1,
    fun hs => add_mem ((h.2 w hw).2 hs) ((h'.2 w hw).2 hs)⟩⟩

theorem ofLev_sum {ι : Type} (s : Finset ι) {S : Set (Pl E)} {U₁ U₂ : ∀ w : Pl E, Subgroup (GLw a w × GLw b w)}
    {G : ι → H E a b → ℂ} (h : ∀ i ∈ s, OfLev S U₁ U₂ (G i)) : OfLev S U₁ U₂ (∑ i ∈ s, G i) := by
  induction s using Finset.induction_on with
  | empty => simpa using ofLev_zero S U₁ U₂
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact ofLev_add (h i (Finset.mem_insert_self _ _)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem common_level {ι : Type} [Finite ι] {G : ι → H E a b → ℂ} (h : ∀ i, HasLev (G i)) :
    ∃ U : Subgroup (Hf E a b), IsOpen (U : Set (Hf E a b)) ∧ ∀ i, ∀ u ∈ U, ∀ x, G i (x * finH u) = G i x := by
  choose V hV hG using h
  refine ⟨⨅ i, V i, ?_, fun i u hu x => hG i u ((Subgroup.mem_iInf.1 hu) i) x⟩
  rw [Subgroup.coe_iInf]
  exact isOpen_iInter_of_finite hV

end Lev

theorem iter_fac {X : Type} (C : X → Prop) (T T' O : X → X) (hO : ∀ x, C x → C (O x)) (hT' : ∀ x, C x → C (T' x))
    (hfac : ∀ x, C x → T x = O (T' x)) (hcomm : ∀ x, C x → T' (O x) = O (T' x)) (m : ℕ) (x : X) (hx : C x) :
    T^[m] x = T'^[m] (O^[m] x) := by
  have hit : ∀ (f : X → X), (∀ x, C x → C (f x)) → ∀ k x, C x → C (f^[k] x) := by
    intro f hf k
    induction k with
    | zero => exact fun x hx => hx
    | succ k ih => exact fun x hx => by rw [Function.iterate_succ_apply']; exact hf _ (ih x hx)
  have hc : ∀ k y, C y → T'^[k] (O y) = O (T'^[k] y) := by
    intro k
    induction k with
    | zero => exact fun _ _ => rfl
    | succ k ih =>
      intro y hy
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih y hy, hcomm _ (hit T' hT' k y hy)]
  induction m with
  | zero => rfl
  | succ m ih =>
    have hy := hit O hO m x hx
    rw [Function.iterate_succ_apply', ih, hfac _ (hit T' hT' m _ hy), Function.iterate_succ_apply' O,
      hc (m + 1) _ hy, Function.iterate_succ_apply']

section Act

theorem ofLev_actS (hAct : ActAlg) (hId : ActIdem) {S : Set (Pl E)} (hS : IsSection S)
    {U₁ U₂ : ∀ w : Pl E, Subgroup (GLw a w × GLw b w)} (hU₁ : IsLev U₁) (hU₂ : IsLev U₂)
    {ι₁ ι₂ φ₁ φ₂ : ∀ w : Pl E, LF a b w} (hι₁ : IsTestP ι₁) (hι₂ : IsTestP ι₂) (hφ₁ : IsTestP φ₁) (hφ₂ : IsTestP φ₂)
    (h₁ : ∀ w, ι₁ w = idem (U₁ w)) (h₂ : ∀ w, ι₂ w = idem (U₂ w)) {v : Pl E} (hv : v ∈ S)
    (hbi : ∀ u ∈ U₁ v, ∀ g, φ₁ v (u * g) = φ₁ v g) {G : H E a b → ℂ} (hG : OfLev S U₁ U₂ G) :
    OfLev S U₁ U₂ (actP v (φ₁ v) G) := by
  have A := fun (i j : Slot S) => hAct E a b S hS φ₁ φ₂ ι₁ ι₂ hφ₁ hφ₂ hι₁ hι₂ G G hG.1 hG.1 i j
  have hL : HasLev (actP v (φ₁ v) G) := (A (Sum.inl ⟨v, hv⟩) (Sum.inl ⟨v, hv⟩)).1
  refine ⟨hL, fun u hu => ⟨?_, fun hsp => ?_⟩⟩
  · refine (hId E a b u (U₁ u) _ (hU₁.1 u).1 (hU₁.1 u).2 hL).1.1 ?_
    by_cases huv : u = v
    · subst huv
      have B' : actP u (PositivityTheory.Rg.BcN.F2.mconv (ι₁ u) (φ₁ u)) G = actP u (ι₁ u) (actP u (φ₁ u) G) :=
        (hAct E a b S hS ι₁ ι₂ φ₁ φ₂ hι₁ hι₂ hφ₁ hφ₂ G G hG.1 hG.1 (Sum.inl ⟨u, hv⟩) (Sum.inl ⟨u, hv⟩)).2.2.2
      rw [h₁ u, mconv_idem_left (hU₁.1 u).1 (hU₁.1 u).2 _ hbi] at B'
      exact B'.symm
    · have hj : (Sum.inl ⟨v, hv⟩ : Slot S) ≠ Sum.inl ⟨u, hu⟩ := fun h =>
        huv (congrArg Subtype.val (Sum.inl.inj h)).symm
      have C' : actP v (φ₁ v) (actP u (ι₁ u) G) = actP u (ι₁ u) (actP v (φ₁ v) G) := (A _ _).2.2.1 hj
      have hGu : actP u (idem (U₁ u)) G = G :=
        (hId E a b u (U₁ u) G (hU₁.1 u).1 (hU₁.1 u).2 hG.1).1.2 (hG.2 u hu).1
      rw [h₁ u, hGu] at C'
      exact C'.symm
  · refine (hId E a b u (U₂ u) _ (hU₂.1 u).1 (hU₂.1 u).2 hL).2.1 ?_
    have hj : (Sum.inl ⟨v, hv⟩ : Slot S) ≠ Sum.inr ⟨u, hu, hsp⟩ := by simp
    have C' : actP v (φ₁ v) (actT u (ι₂ u) G) = actT u (ι₂ u) (actP v (φ₁ v) G) := (A _ _).2.2.1 hj
    have hGu : actT u (idem (U₂ u)) G = G :=
      (hId E a b u (U₂ u) G (hU₂.1 u).1 (hU₂.1 u).2 hG.1).2.2 ((hG.2 u hu).2 hsp)
    rw [h₂ u, hGu] at C'
    exact C'.symm

theorem actS_sum (hAct : ActAlg) {S : Set (Pl E)} (hS : IsSection S) {φ₁ φ₂ : ∀ w : Pl E, LF a b w}
    (hφ₁ : IsTestP φ₁) (hφ₂ : IsTestP φ₂) (i : Slot S) {ι : Type} (s : Finset ι) {G : ι → H E a b → ℂ}
    (hG : ∀ j ∈ s, HasLev (G j)) : actS φ₁ φ₂ i (∑ j ∈ s, G j) = ∑ j ∈ s, actS φ₁ φ₂ i (G j) := by
  have hadd := fun (X Y : H E a b → ℂ) (hX : HasLev X) (hY : HasLev Y) =>
    ((hAct E a b S hS φ₁ φ₂ φ₁ φ₂ hφ₁ hφ₂ hφ₁ hφ₂ X Y hX hY i i).2.1 1)
  simp only [one_smul] at hadd
  induction s using Finset.induction_on with
  | empty =>
    have h0 := hadd 0 0 hasLev_zero hasLev_zero
    simpa using h0
  | insert j s hj ih =>
    have hs : HasLev (∑ j ∈ s, G j) := by
      have : ∀ t : Finset ι, (∀ j ∈ t, HasLev (G j)) → HasLev (∑ j ∈ t, G j) := by
        intro t
        induction t using Finset.induction_on with
        | empty => intro _; simpa using hasLev_zero
        | insert k t hk ih' =>
          intro h
          rw [Finset.sum_insert hk]
          exact hasLev_add (h k (Finset.mem_insert_self _ _)) (ih' fun l hl => h l (Finset.mem_insert_of_mem hl))
      exact this s fun l hl => hG l (Finset.mem_insert_of_mem hl)
    rw [Finset.sum_insert hj, Finset.sum_insert hj, hadd _ _ (hG j (Finset.mem_insert_self _ _)) hs,
      ih fun l hl => hG l (Finset.mem_insert_of_mem hl)]

theorem localAction_zero_left (w : Pl E) (G : H E a b → ℂ) : actP w (0 : LF a b w) G = 0 := by
  funext z
  simpa [actP] using GlobalTheory.CompanionTheory.FamClP.hint_zero (K2 a b w)

end Act

section Main

variable {κ : Pl E → Type} [∀ w, Fintype (κ w)] {S : Set (Pl E)} {P : Finset (Pl E)} {B : Block E}
  {e : B.κ ≃ ∀ w : P, κ w} {U₁ U₂ : ∀ w : Pl E, Subgroup (GLw B.a w × GLw B.b w)} {L : LM κ B.a B.b}

theorem sel_self (v : Pl E) : (sel U₁ L {v}).m v = L.m v := by
  funext x y
  simp [sel]

theorem ent_at (Q : Finset (Pl E)) (v : P) (X Y : ∀ w : P, κ w) :
    (sel U₁ L Q).ent P X Y v.1 = (sel U₁ L Q).m v.1 (X v) (Y v) := by
  unfold LM.ent
  rw [dif_pos v.2]

theorem test_alt (hU₁ : IsLev U₁) (hok : L.Ok P) (hs : ∀ w, L.s w = idem (U₁ w)) (X : ∀ w : P, κ w) : IsTestP L.s := by
  have h := (sel_ok hU₁ hok ∅).1 X X
  have e' : (sel U₁ L ∅).ent P X X = L.s := by
    funext w
    unfold LM.ent
    split_ifs
    · simp [sel, hs w]
    · rfl
  rwa [e'] at h

theorem exists_fam (hU₁ : IsLev U₁) (hok : L.Ok P) (X : ∀ w : P, κ w) (v : P) (r s : κ v.1) :
    ∃ φ : ∀ w : Pl E, LF B.a B.b w, IsTestP φ ∧ φ v.1 = L.m v.1 r s := by
  refine ⟨(sel U₁ L {v.1}).ent P (Function.update X v r) (Function.update X v s), (sel_ok hU₁ hok _).1 _ _, ?_⟩
  rw [ent_at, sel_self, Function.update_self, Function.update_self]

variable (hAlg : FmAlg) (hAt : FmAtP) (hCM : Tail.ConvMul) (hAct : ActAlg) (hId : ActIdem) (hS : IsSection S)
  (hP : (↑P : Set (Pl E)) ⊆ S) (hU₁ : IsLev U₁) (hU₂ : IsLev U₂) (hok : L.Ok P) (hs : ∀ w, L.s w = idem (U₁ w))
  (ht : ∀ w, L.t w = idem (U₂ w))
  (hinv : ∀ w ∈ P, ∀ x y, ∀ u ∈ U₁ w, ∀ g, L.m w x y (u * g) = L.m w x y g ∧ L.m w x y (g * u) = L.m w x y g)

include hAt hId hS hP hU₁ hU₂ hok hs ht in
theorem fm_one (v : P) (Q : Finset (Pl E)) (hQ : ∀ u ∈ Q, u = v.1) (G : Unit × B.κ → H E B.a B.b → ℂ)
    (hG : ∀ i, OfLev S U₁ U₂ (G i)) (p : Unit) (x : B.κ) :
    convF B.ν (fm S P B e (sel U₁ L Q)) G (p, x) =
      ∑ y : κ v.1, actP v.1 ((sel U₁ L Q).m v.1 (e x v) y) (G (p, e.symm (Function.update (e x) v y))) := by
  refine hAt E κ S P B e hS hP Unit (sel U₁ L Q) v G (sel_ok hU₁ hok Q) (fun i => (hG i).1) ⟨?_, ?_⟩ p x
  · intro w hw hne r s hrs
    have hwv : w ≠ v.1 := fun h => hne (hP hw) (by subst h; rfl)
    have hwQ : w ∉ Q := fun h => hwv (hQ w h)
    simp [sel, hwQ, hrs]
  · rintro (⟨u, hu⟩ | ⟨u, hu, hsp⟩) hi p' x' y' hxy
    · have huv : u ≠ v.1 := fun h => hi (by subst h; rfl)
      have huQ : u ∉ Q := fun h => huv (hQ u h)
      have hent : (sel U₁ L Q).ent P (e x') (e y') u = idem (U₁ u) := by
        unfold LM.ent
        split_ifs with huP
        · have hne : ∀ h : u ∈ S, (Sum.inl ⟨v.1, hP v.2⟩ : Slot S) ≠ Sum.inl ⟨u, h⟩ := fun h hc =>
            huv (congrArg Subtype.val (Sum.inl.inj hc)).symm
          simp [sel, huQ, hxy ⟨u, huP⟩ hne]
        · exact hs u
      show actP u ((sel U₁ L Q).ent P (e x') (e y') u) _ = _
      rw [hent]
      exact (hId E B.a B.b u (U₁ u) _ (hU₁.1 u).1 (hU₁.1 u).2 (hG _).1).1.2 ((hG _).2 u hu).1
    · show actT u (L.t u) _ = _
      rw [ht u]
      exact (hId E B.a B.b u (U₂ u) _ (hU₂.1 u).1 (hU₂.1 u).2 (hG _).1).2.2 (((hG _).2 u hu).2 hsp)

include hAt hId hS hP hU₁ hU₂ hok hs ht in
theorem fm_self (v : P) (G : Unit × B.κ → H E B.a B.b → ℂ) (hG : ∀ i, OfLev S U₁ U₂ (G i)) (p : Unit)
    (X : ∀ w : P, κ w) :
    convF B.ν (fm S P B e (sel U₁ L {v.1})) G (p, e.symm X) =
      ∑ y : κ v.1, actP v.1 (L.m v.1 (X v) y) (G (p, e.symm (Function.update X v y))) := by
  rw [fm_one hAt hId hS hP hU₁ hU₂ hok hs ht v {v.1} (fun u hu => Finset.mem_singleton.1 hu) G hG p,
    Equiv.apply_symm_apply, sel_self]

include hAt hId hS hP hU₁ hU₂ hok hs ht in
theorem sel_empty (v : P) (G : Unit × B.κ → H E B.a B.b → ℂ) (hG : ∀ i, OfLev S U₁ U₂ (G i)) :
    convF B.ν (fm S P B e (sel U₁ L ∅)) G = G := by
  funext ⟨p, x⟩
  rw [fm_one hAt hId hS hP hU₁ hU₂ hok hs ht v ∅ (by simp) G hG p, Finset.sum_eq_single (e x v)]
  · simp only [sel, Finset.notMem_empty, if_false, if_true, Function.update_eq_self, Equiv.symm_apply_apply]
    exact (hId E B.a B.b v.1 (U₁ v.1) _ (hU₁.1 v.1).1 (hU₁.1 v.1).2 (hG _).1).1.2 ((hG _).2 v.1 (hP v.2)).1
  · intro y _ hy
    simp only [sel, Finset.notMem_empty, if_false]
    rw [if_neg (Ne.symm hy), localAction_zero_left]
  · simp

include hAct hAt hId hS hP hU₁ hU₂ hok hs ht hinv in
theorem one_ofLev (v : P) (G : Unit × B.κ → H E B.a B.b → ℂ) (hG : ∀ i, OfLev S U₁ U₂ (G i)) (i : Unit × B.κ) :
    OfLev S U₁ U₂ (convF B.ν (fm S P B e (sel U₁ L {v.1})) G i) := by
  obtain ⟨p, x⟩ := i
  have hx := fm_self (e := e) hAt hId hS hP hU₁ hU₂ hok hs ht v G hG p (e x)
  rw [Equiv.symm_apply_apply] at hx
  rw [hx]
  refine ofLev_sum _ fun y _ => ?_
  obtain ⟨φ, hφ, hφv⟩ := exists_fam hU₁ hok (e x) v (e x v) y
  rw [← hφv]
  refine ofLev_actS hAct hId hS hU₁ hU₂ (test_alt hU₁ hok hs (e x)) hok.2 hφ hok.2 hs ht (hP v.2) ?_ (hG _)
  intro u hu g
  rw [hφv]
  exact (hinv v.1 v.2 _ _ u hu g).1

include hAct hAt hId hS hP hU₁ hU₂ hok hs ht hinv in
theorem one_comm (u v : P) (huv : u ≠ v) (G : Unit × B.κ → H E B.a B.b → ℂ) (hG : ∀ i, OfLev S U₁ U₂ (G i)) :
    convF B.ν (fm S P B e (sel U₁ L {u.1})) (convF B.ν (fm S P B e (sel U₁ L {v.1})) G) =
      convF B.ν (fm S P B e (sel U₁ L {v.1})) (convF B.ν (fm S P B e (sel U₁ L {u.1})) G) := by
  have hO := fun (t : P) => one_ofLev (e := e) hAt hAct hId hS hP hU₁ hU₂ hok hs ht hinv t G hG
  have hF := fun (t : P) (H' : Unit × B.κ → H E B.a B.b → ℂ) (hH : ∀ i, OfLev S U₁ U₂ (H' i)) (p : Unit) (X) =>
    fm_self (e := e) hAt hId hS hP hU₁ hU₂ hok hs ht t H' hH p X
  funext ⟨p, x⟩
  have expand : ∀ (s t : P), s ≠ t → convF B.ν (fm S P B e (sel U₁ L {s.1})) (convF B.ν (fm S P B e (sel U₁ L {t.1})) G) (p, x) =
      ∑ y : κ s.1, ∑ z : κ t.1, actP s.1 (L.m s.1 (e x s) y) (actP t.1 (L.m t.1 (e x t) z)
        (G (p, e.symm (Function.update (Function.update (e x) s y) t z)))) := by
    intro s t hst
    have h1 := hF s _ (hO t) p (e x)
    rw [Equiv.symm_apply_apply] at h1
    rw [h1]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hF t G hG p, Function.update_of_ne (Ne.symm hst)]
    obtain ⟨φ, hφ, hφv⟩ := exists_fam hU₁ hok (e x) s (e x s) y
    obtain ⟨ψ, hψ, hψv⟩ := exists_fam hU₁ hok (e x) t (e x t) (e x t)
    rw [← hφv]
    refine actS_sum hAct hS hφ hok.2 (Sum.inl ⟨s.1, hP s.2⟩) _ fun z _ => ?_
    obtain ⟨χ, hχ, hχv⟩ := exists_fam hU₁ hok (e x) t (e x t) z
    rw [← hχv]
    have hz := (hG (p, e.symm (Function.update (Function.update (e x) s y) t z))).1
    exact (hAct E B.a B.b S hS χ L.t χ L.t hχ hok.2 hχ hok.2 _ _ hz hz
      (Sum.inl ⟨t.1, hP t.2⟩) (Sum.inl ⟨t.1, hP t.2⟩)).1
  rw [expand u v huv, expand v u (Ne.symm huv), Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun y _ => ?_
  obtain ⟨φ, hφ, hφv⟩ := exists_fam hU₁ hok (e x) u (e x u) y
  obtain ⟨ψ, hψ, hψv⟩ := exists_fam hU₁ hok (e x) v (e x v) z
  rw [Function.update_comm huv, ← hφv, ← hψv]
  have hne : (Sum.inl ⟨u.1, hP u.2⟩ : Slot S) ≠ Sum.inl ⟨v.1, hP v.2⟩ := by
    intro h
    have h2 := Sum.inl_injective h
    exact huv (Subtype.ext (Subtype.mk.inj h2))
  have hz := (hG (p, e.symm (Function.update (Function.update (e x) v z) u y))).1
  exact (hAct E B.a B.b S hS φ L.t ψ L.t hφ hok.2 hψ hok.2 _ _ hz hz _ _).2.2.1 hne

include hAlg hCM hok hS hP hU₁ hU₂ hs ht hinv in
theorem step {Q₁ Q₂ : Finset (Pl E)} (hQ₁ : Q₁ ⊆ P) (hQ₂ : Q₂ ⊆ P) (hd : Disjoint Q₁ Q₂)
    (G : Unit × B.κ → H E B.a B.b → ℂ) (hG : ∀ i, OfLev S U₁ U₂ (G i)) :
    convF B.ν (fm S P B e (sel U₁ L (Q₁ ∪ Q₂))) G =
      convF B.ν (fm S P B e (sel U₁ L Q₁)) (convF B.ν (fm S P B e (sel U₁ L Q₂)) G) := by
  have o₁ := sel_ok hU₁ hok Q₁
  have o₂ := sel_ok hU₁ hok Q₂
  obtain ⟨f₁, -, hm, -, -⟩ := hAlg E κ S P B e hS hP (sel U₁ L Q₁) (sel U₁ L Q₂) o₁ o₂
  obtain ⟨f₂, -⟩ := hAlg E κ S P B e hS hP (sel U₁ L Q₂) (sel U₁ L Q₁) o₂ o₁
  have ht' : ((sel U₁ L Q₁).mul (sel U₁ L Q₂)).t = (sel U₁ L (Q₁ ∪ Q₂)).t := by
    funext w
    show PositivityTheory.Rg.BcN.F2.mconv (L.t w) (L.t w) = L.t w
    rw [ht w]
    exact mconv_idem_idem (hU₂.1 w).1 (hU₂.1 w).2
  have hf : fm S P B e ((sel U₁ L Q₁).mul (sel U₁ L Q₂)) = fm S P B e (sel U₁ L (Q₁ ∪ Q₂)) := by
    funext x y h
    unfold fm
    rw [sel_mul_ent hU₁ hs hinv hQ₁ hQ₂ hd, ht']
  obtain ⟨U, hUo, hUl⟩ := common_level fun i => (hG i).1
  rw [← hf, ← hm]
  exact (hCM E B Unit _ _ U G f₁ f₂ hUo hUl).1

include hAlg hAt hCM hAct hId hS hP hU₁ hU₂ hok hs ht hinv in
theorem claim (v₀ : P) (Q : Finset (Pl E)) (hQ : Q ⊆ P) :
    (∀ G : Unit × B.κ → H E B.a B.b → ℂ, (∀ i, OfLev S U₁ U₂ (G i)) →
      ∀ i, OfLev S U₁ U₂ (convF B.ν (fm S P B e (sel U₁ L Q)) G i)) ∧
    ∀ v : P, v.1 ∉ Q → ∀ G : Unit × B.κ → H E B.a B.b → ℂ, (∀ i, OfLev S U₁ U₂ (G i)) →
      convF B.ν (fm S P B e (sel U₁ L Q)) (convF B.ν (fm S P B e (sel U₁ L {v.1})) G) =
        convF B.ν (fm S P B e (sel U₁ L {v.1})) (convF B.ν (fm S P B e (sel U₁ L Q)) G) := by
  have hO := fun (t : P) G hG => one_ofLev (e := e) hAt hAct hId hS hP hU₁ hU₂ hok hs ht hinv t G hG
  have hE := fun G hG => sel_empty (e := e) hAt hId hS hP hU₁ hU₂ hok hs ht v₀ G hG
  induction Q using Finset.induction_on with
  | empty =>
    refine ⟨fun G hG => by rw [hE G hG]; exact hG, fun v _ G hG => ?_⟩
    rw [hE G hG, hE _ (hO v G hG)]
  | insert u Q hu ih =>
    have huP : u ∈ P := hQ (Finset.mem_insert_self _ _)
    have hQP : Q ⊆ P := fun x hx => hQ (Finset.mem_insert_of_mem hx)
    obtain ⟨c₁, c₂⟩ := ih hQP
    have hst : ∀ G : Unit × B.κ → H E B.a B.b → ℂ, (∀ i, OfLev S U₁ U₂ (G i)) →
        convF B.ν (fm S P B e (sel U₁ L (insert u Q))) G =
          convF B.ν (fm S P B e (sel U₁ L {u})) (convF B.ν (fm S P B e (sel U₁ L Q)) G) := by
      intro G hG
      rw [Finset.insert_eq]
      exact step hAlg hCM hS hP hU₁ hU₂ hok hs ht hinv (Finset.singleton_subset_iff.2 huP) hQP
        (Finset.disjoint_singleton_left.2 hu) G hG
    refine ⟨fun G hG => ?_, fun v hv G hG => ?_⟩
    · rw [hst G hG]
      exact hO ⟨u, huP⟩ _ (c₁ G hG)
    · have hvu : v.1 ≠ u := fun h => hv (h ▸ Finset.mem_insert_self _ _)
      have hvQ : v.1 ∉ Q := fun h => hv (Finset.mem_insert_of_mem h)
      rw [hst _ (hO v G hG), hst G hG, c₂ v hvQ G hG]
      exact one_comm hAt hAct hId hS hP hU₁ hU₂ hok hs ht hinv ⟨u, huP⟩ v
        (fun h => hvu (congrArg Subtype.val h).symm) _ (c₁ G hG)

include hAlg hAt hCM hAct hId hS hP hU₁ hU₂ hok hs ht hinv in
theorem main_unit (G : Unit × B.κ → H E B.a B.b → ℂ) (hG : ∀ i, OfLev S U₁ U₂ (G i)) (m : ℕ)
    (h : (convF B.ν (fm S P B e L))^[m] G ≠ 0) (w₀ : P) :
    ∃ x : ∀ w : P, κ w,
      (locM w₀.1 (L.m w₀.1))^[m] (fun y => G ((), e.symm (Function.update x w₀ y))) ≠ 0 := by
  set O := convF B.ν (fm S P B e (sel U₁ L {w₀.1})) with hOdef
  set T' := convF B.ν (fm S P B e (sel U₁ L (P.erase w₀.1))) with hT'def
  have hfL : fm S P B e L = fm S P B e (sel U₁ L ({w₀.1} ∪ P.erase w₀.1)) := by
    have hU : ({w₀.1} ∪ P.erase w₀.1 : Finset (Pl E)) = P := by
      rw [← Finset.insert_eq, Finset.insert_erase w₀.2]
    rw [hU]
    funext x y h
    unfold fm
    have : L.ent P (e x) (e y) = (sel U₁ L P).ent P (e x) (e y) := by
      funext w
      unfold LM.ent
      split_ifs with hw
      · simp [sel, hw]
      · rfl
    rw [this]
    rfl
  have hC := claim (e := e) hAlg hAt hCM hAct hId hS hP hU₁ hU₂ hok hs ht hinv w₀ (P.erase w₀.1) (Finset.erase_subset _ _)
  have hO := one_ofLev (e := e) hAt hAct hId hS hP hU₁ hU₂ hok hs ht hinv w₀
  have hit := iter_fac (fun G : Unit × B.κ → H E B.a B.b → ℂ => ∀ i, OfLev S U₁ U₂ (G i))
    (convF B.ν (fm S P B e L)) T' O (fun G hG => hO G hG) (fun G hG => hC.1 G hG)
    (fun G hG => by
      rw [hfL]
      exact step hAlg hCM hS hP hU₁ hU₂ hok hs ht hinv (Finset.singleton_subset_iff.2 w₀.2)
        (Finset.erase_subset _ _) (Finset.disjoint_singleton_left.2 (Finset.notMem_erase _ _)) G hG)
    (fun G hG => hC.2 w₀ (Finset.notMem_erase _ _) G hG) m G hG
  have hOit : ∀ k, ∀ G' : Unit × B.κ → H E B.a B.b → ℂ, (∀ i, OfLev S U₁ U₂ (G' i)) → ∀ i, OfLev S U₁ U₂ (O^[k] G' i) := by
    intro k
    induction k with
    | zero => exact fun _ h => h
    | succ k ih => exact fun G' h => by rw [Function.iterate_succ_apply']; exact hO _ (ih G' h)
  have hsl : ∀ k (x : ∀ w : P, κ w), (fun y => O^[k] G ((), e.symm (Function.update x w₀ y))) =
      (locM w₀.1 (L.m w₀.1))^[k] (fun y => G ((), e.symm (Function.update x w₀ y))) := by
    intro k x
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
      funext y
      rw [hOdef, fm_self (e := e) hAt hId hS hP hU₁ hU₂ hok hs ht w₀ _ (hOit k G hG) (), Function.update_self]
      simp only [Function.update_idem]
      rfl
  by_contra hcon
  push_neg at hcon
  have hz : O^[m] G = 0 := by
    funext ⟨p, z⟩
    have h1 := congrFun (hsl m (e z)) (e z w₀)
    rw [hcon (e z)] at h1
    simpa using h1
  have hT0 : ∀ k, T'^[k] (0 : Unit × B.κ → H E B.a B.b → ℂ) = 0 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      funext i z
      simp [hT'def, convF]
  exact h (by rw [hit, hz, hT0])

end Main

theorem fmPowOf : PositivityTheory.Rg.BcB.F.FA.FmPowOf := by
  intro hAlg hAt hCM hAct hId E _ _ _ κ _ S P B e hS hP U₁ U₂ L A F m hU₁ hU₂ hok hs ht hinv hF hT w₀
  have hne : ∃ i, (convF B.ν (fm S P B e L))^[m] F i ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hT (funext hc)
  obtain ⟨⟨p, x⟩, hx⟩ := hne
  let sl : (A × B.κ → H E B.a B.b → ℂ) → (Unit × B.κ → H E B.a B.b → ℂ) := fun F' i => F' (p, i.2)
  have hsl : ∀ k (F' : A × B.κ → H E B.a B.b → ℂ),
      sl ((convF B.ν (fm S P B e L))^[k] F') = (convF B.ν (fm S P B e L))^[k] (sl F') := by
    intro k F'
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
      rfl
  have hne' : (convF B.ν (fm S P B e L))^[m] (sl F) ≠ 0 := by
    rw [← hsl]
    intro h0
    exact hx (congrFun h0 ((), x))
  obtain ⟨y, hy⟩ := main_unit hAlg hAt hCM hAct hId hS hP hU₁ hU₂ hok hs ht hinv (sl F) (fun i => hF _) m hne' w₀
  exact ⟨p, y, hy⟩

end GlobalTheory.CompanionTheory.FmPowP

end
