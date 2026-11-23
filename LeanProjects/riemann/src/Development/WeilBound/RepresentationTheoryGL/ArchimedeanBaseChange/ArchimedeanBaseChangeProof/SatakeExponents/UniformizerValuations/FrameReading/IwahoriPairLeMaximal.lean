import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameBoundSpaces.FrameBound
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.MconvZeroRight
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryLevelSubgroupProperties
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralPointsOpenCompactStatement

noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open PositivityTheory.Rg.BcB.F.Tail (I2)
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Rd.LevOC

open PositivityTheory.Rg.BcB.F

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem maximal_pair_isCompact (a b : ℕ) (w : Pl E) : IsCompact (K2 a b w : Set (GLw a w × GLw b w)) := by
  rw [K2, Subgroup.coe_prod]
  exact (GlobalTheory.CompanionTheory.IwLevels.isCompact_KGL w a).prod (GlobalTheory.CompanionTheory.IwLevels.isCompact_KGL w b)

theorem KGL_open (w : Pl E) (m : ℕ) : IsOpen (GlobalTheory.LFun.KGL w m : Set (GLw m w)) := by
  rw [GlobalTheory.CompanionTheory.IwLevels.KGL_eq_KO]
  exact GlobalTheory.SplitFlip.isOpen_KO

theorem maximal_pair_isOpen (a b : ℕ) (w : Pl E) : IsOpen (K2 a b w : Set (GLw a w × GLw b w)) := by
  rw [K2, Subgroup.coe_prod]
  exact (KGL_open w a).prod (KGL_open w b)

theorem iwahori_pair_isOpen (a b : ℕ) (w : Pl E) : IsOpen (I2 a b w : Set (GLw a w × GLw b w)) := by
  rw [I2, Subgroup.coe_prod]
  exact (GlobalTheory.SmGL.IwahoriOnto.isOpen_iwahori (w.adicCompletion E) (Fin a)).prod
    (GlobalTheory.SmGL.IwahoriOnto.isOpen_iwahori (w.adicCompletion E) (Fin b))

theorem I2_le_K2 (a b : ℕ) (w : Pl E) : I2 a b w ≤ K2 a b w :=
  Subgroup.prod_mono (GlobalTheory.CompanionTheory.IwLevels.iwGL_le_KGL w a) (GlobalTheory.CompanionTheory.IwLevels.iwGL_le_KGL w b)

theorem compact_of_le {a b : ℕ} {w : Pl E} (L : Subgroup (GLw a w × GLw b w)) (ho : IsOpen (L : Set (GLw a w × GLw b w)))
    (hle : L ≤ K2 a b w) : IsCompact (L : Set (GLw a w × GLw b w)) :=
  (maximal_pair_isCompact a b w).of_isClosed_subset (Subgroup.isClosed_of_isOpen L ho) hle

theorem L_open_le (d : LocData E n) (hd : d.Ok) (a : ℕ) (ha : a ≤ n) (w : Pl E) (hw : w ∈ d.S₀ ∪ d.Bad) :
    IsOpen (d.L a w : Set (GLw a w × GLw (n - a) w)) ∧ d.L a w ≤ K2 a (n - a) w := by
  obtain ⟨L₁, L₂, h, ⟨h1o, h1le, -⟩, ⟨h2o, h2le, -⟩⟩ := hd.L a ha w hw
  rw [h, Subgroup.coe_prod]
  exact ⟨h1o.prod h2o, Subgroup.prod_mono h1le h2le⟩

theorem locLev_oc (d : LocData E n) (hd : d.Ok) (a : ℕ) (ha : a ≤ n) (w : Pl E) :
    IsOpen (d.lev a w : Set (GLw a w × GLw (n - a) w)) ∧ IsCompact (d.lev a w : Set (GLw a w × GLw (n - a) w)) ∧
      d.lev a w ≤ K2 a (n - a) w := by
  have h : IsOpen (d.lev a w : Set (GLw a w × GLw (n - a) w)) ∧ d.lev a w ≤ K2 a (n - a) w := by
    unfold LocData.lev
    split_ifs with h1 h2
    · exact ⟨iwahori_pair_isOpen a (n - a) w, I2_le_K2 a (n - a) w⟩
    · exact L_open_le d hd a ha w h2
    · exact ⟨maximal_pair_isOpen a (n - a) w, le_rfl⟩
  exact ⟨h.1, compact_of_le _ h.1 h.2, h.2⟩

theorem locLev₂_oc (d : LocData E n) (hd : d.Ok) (a : ℕ) (ha : a ≤ n) (w : Pl E) :
    IsOpen (d.lev₂ a w : Set (GLw a w × GLw (n - a) w)) ∧ IsCompact (d.lev₂ a w : Set (GLw a w × GLw (n - a) w)) ∧
      d.lev₂ a w ≤ K2 a (n - a) w := by
  have h : IsOpen (d.lev₂ a w : Set (GLw a w × GLw (n - a) w)) ∧ d.lev₂ a w ≤ K2 a (n - a) w := by
    unfold LocData.lev₂
    split_ifs with h2
    · exact L_open_le d hd a ha w h2
    · exact ⟨maximal_pair_isOpen a (n - a) w, le_rfl⟩
  exact ⟨h.1, compact_of_le _ h.1 h.2, h.2⟩

def gSet (Sec : Set (Pl E)) (d : LocData E n) (a : ℕ) : Set (Hf E a (n - a)) :=
  {h | ∀ w ∈ Sec, atW w h ∈ d.lev a w ∧ (IsSplitAt w → atW w (thP E a (n - a) h) ∈ d.lev₂ a w)}

def g₁ (Sec : Set (Pl E)) (d : LocData E n) (a : ℕ) : Subgroup (GL (Fin a) (Af E)) :=
  Subgroup.closure {g | (g, 1) ∈ gSet Sec d a}

def g₂ (Sec : Set (Pl E)) (d : LocData E n) (a : ℕ) : Subgroup (GL (Fin (n - a)) (Af E)) :=
  Subgroup.closure {g | (1, g) ∈ gSet Sec d a}

def C (d : LocData E n) (a : ℕ) {S : Set (Pl E)} : ∀ i : Slot S, Set (GLw a i.pl × GLw (n - a) i.pl)
  | .inl w => (d.lev a w.1 : Set (GLw a w.1 × GLw (n - a) w.1))
  | .inr w => (d.lev₂ a w.1 : Set (GLw a w.1 × GLw (n - a) w.1))

theorem C_open_le (d : LocData E n) (hd : d.Ok) (a : ℕ) (ha : a ≤ n) {S : Set (Pl E)} (i : Slot S) :
    IsOpen (C d a i) ∧ C d a i ⊆ (K2 a (n - a) i.pl : Set (GLw a i.pl × GLw (n - a) i.pl)) := by
  rcases i with w | w
  · exact ⟨(locLev_oc d hd a ha w.1).1, (locLev_oc d hd a ha w.1).2.2⟩
  · exact ⟨(locLev₂_oc d hd a ha w.1).1, (locLev₂_oc d hd a ha w.1).2.2⟩

theorem position_cof {S : Set (Pl E)} {P : Pl E → Prop} (h : ∀ᶠ w in cofinite, P w) :
    ∀ᶠ i : Slot S in cofinite, P i.pl := by
  rw [Filter.eventually_cofinite] at h ⊢
  have h1 : {w : {w // w ∈ S} | ¬ P w.1}.Finite := h.preimage Subtype.val_injective.injOn
  have h2 : {w : {w // w ∈ S ∧ IsSplitAt w} | ¬ P w.1}.Finite := h.preimage Subtype.val_injective.injOn
  refine ((h1.image Sum.inl).union (h2.image Sum.inr)).subset ?_
  rintro (w | w) hw
  · exact Or.inl ⟨w, hw, rfl⟩
  · exact Or.inr ⟨w, hw, rfl⟩

theorem C_cof (d : LocData E n) (a : ℕ) {S : Set (Pl E)} :
    ∀ᶠ i : Slot S in cofinite, C d a i = (K2 a (n - a) i.pl : Set (GLw a i.pl × GLw (n - a) i.pl)) := by
  filter_upwards [position_cof (S := S) (Rd.levCof d a)] with i hi
  rcases i with w | w
  · show ((d.lev a w.1 : Subgroup _) : Set (GLw a w.1 × GLw (n - a) w.1)) = (K2 a (n - a) w.1 : Set _)
    have h' : d.lev a w.1 = K2 a (n - a) w.1 := hi.1
    rw [h']
  · show ((d.lev₂ a w.1 : Subgroup _) : Set (GLw a w.1 × GLw (n - a) w.1)) = (K2 a (n - a) w.1 : Set _)
    have h' : d.lev₂ a w.1 = K2 a (n - a) w.1 := hi.2
    rw [h']

theorem gSet_eq (S : Set (Pl E)) (d : LocData E n) (a : ℕ) :
    gSet S d a = {x : Hf E a (n - a) | ∀ i : Slot S, i.cp a (n - a) x ∈ C d a i} := by
  ext x
  constructor
  · intro hx i
    rcases i with w | w
    · exact (hx w.1 w.2).1
    · exact (hx w.1 w.2.1).2 w.2.2
  · intro hx w hw
    exact ⟨hx (.inl ⟨w, hw⟩), fun hs => hx (.inr ⟨w, hw, hs⟩)⟩

def levSub (S : Set (Pl E)) (d : LocData E n) (a : ℕ) : Subgroup (Hf E a (n - a)) where
  carrier := gSet S d a
  one_mem' := by
    simp only [gSet, Set.mem_ofPred_eq, map_one]
    intro w _
    have e1 : atW w (1 : Hf E a (n - a)) = 1 := by simp [atW]
    rw [e1]
    exact ⟨one_mem _, fun _ => one_mem _⟩
  mul_mem' := by
    intro x y hx hy
    simp only [gSet, Set.mem_ofPred_eq] at hx hy ⊢
    intro w hw
    have e : ∀ z z' : Hf E a (n - a), atW w (z * z') = atW w z * atW w z' := fun z z' => by simp [atW]
    simp only [map_mul, e]
    exact ⟨mul_mem (hx w hw).1 (hy w hw).1, fun hs => mul_mem ((hx w hw).2 hs) ((hy w hw).2 hs)⟩
  inv_mem' := by
    intro x hx
    simp only [gSet, Set.mem_ofPred_eq] at hx ⊢
    intro w hw
    have e : ∀ z : Hf E a (n - a), atW w z⁻¹ = (atW w z)⁻¹ := fun z => by simp [atW]
    simp only [map_inv, e]
    exact ⟨inv_mem (hx w hw).1, fun hs => inv_mem ((hx w hw).2 hs)⟩

theorem gSet_sub (hSl : Slots) {Sec : Set (Pl E)} (hS : IsSection Sec) (d : LocData E n) (hd : d.Ok) (a : ℕ)
    (ha : a ≤ n) : gSet Sec d a ⊆ (((Kf E a).prod (Kf E (n - a)) : Subgroup (Hf E a (n - a))) : Set (Hf E a (n - a))) := by
  intro x hx
  rw [gSet_eq] at hx
  exact ((hSl E a (n - a) Sec hS).2.2.2.2.2.1 x).2 fun i => (C_open_le d hd a ha i).2 (hx i)

theorem gSet_open (hSl : Slots) {Sec : Set (Pl E)} (hS : IsSection Sec) (d : LocData E n) (hd : d.Ok) (a : ℕ)
    (ha : a ≤ n) : IsOpen (gSet Sec d a) := by
  have hSl' := hSl E a (n - a) Sec hS
  obtain ⟨hKo1, -⟩ := GlobalTheory.T.finite_kernel_compact_open E a
  obtain ⟨hKo2, -⟩ := GlobalTheory.T.finite_kernel_compact_open E (n - a)
  set U : Set (Hf E a (n - a)) := (((Kf E a).prod (Kf E (n - a)) : Subgroup (Hf E a (n - a))) : Set (Hf E a (n - a)))
    with hU
  have hUo : IsOpen U := by
    rw [hU, Subgroup.coe_prod]
    exact hKo1.prod hKo2
  have hF := (Filter.eventually_cofinite.1 (C_cof d a (S := Sec)))
  set V : Set (Hf E a (n - a)) := U ∩ ⋂ i ∈ {i : Slot Sec | ¬ C d a i = (K2 a (n - a) i.pl : Set _)},
    (i.cp a (n - a)) ⁻¹' C d a i with hV
  have hVo : IsOpen V :=
    hUo.inter (hF.isOpen_biInter fun i _ => (C_open_le d hd a ha i).1.preimage (hSl'.2.1 i))
  have h1V : (1 : Hf E a (n - a)) ∈ V := by
    refine ⟨one_mem _, Set.mem_iInter₂.2 fun i _ => ?_⟩
    have h1 : (1 : Hf E a (n - a)) ∈ gSet Sec d a := (levSub Sec d a).one_mem
    rw [gSet_eq] at h1
    exact h1 i
  have hVsub : V ⊆ gSet Sec d a := by
    intro x hx
    rw [gSet_eq]
    intro i
    by_cases hi : C d a i = (K2 a (n - a) i.pl : Set _)
    · rw [hi]
      exact (hSl'.2.2.2.2.2.1 x).1 hx.1 i
    · exact Set.mem_iInter₂.1 hx.2 i hi
  exact Subgroup.isOpen_of_mem_nhds (levSub Sec d a) (g := 1) (Filter.mem_of_superset (hVo.mem_nhds h1V) hVsub)

theorem g₁_coe (Sec : Set (Pl E)) (d : LocData E n) (a : ℕ) :
    (g₁ Sec d a : Set (GL (Fin a) (Af E))) = (fun g => ((g, 1) : Hf E a (n - a))) ⁻¹' gSet Sec d a := by
  rw [g₁, show {g | ((g, 1) : Hf E a (n - a)) ∈ gSet Sec d a} =
    (((levSub Sec d a).comap (MonoidHom.inl _ _) : Subgroup _) : Set _) from rfl, Subgroup.closure_eq]
  rfl

theorem g₂_coe (Sec : Set (Pl E)) (d : LocData E n) (a : ℕ) :
    (g₂ Sec d a : Set (GL (Fin (n - a)) (Af E))) = (fun g => ((1, g) : Hf E a (n - a))) ⁻¹' gSet Sec d a := by
  rw [g₂, show {g | ((1, g) : Hf E a (n - a)) ∈ gSet Sec d a} =
    (((levSub Sec d a).comap (MonoidHom.inr _ _) : Subgroup _) : Set _) from rfl, Subgroup.closure_eq]
  rfl

theorem g₁_oc (hSl : Slots) {Sec : Set (Pl E)} (hS : IsSection Sec) (d : LocData E n) (hd : d.Ok) (a : ℕ)
    (ha : a ≤ n) : IsOpen (g₁ Sec d a : Set (GL (Fin a) (Af E))) ∧ IsCompact (g₁ Sec d a : Set (GL (Fin a) (Af E))) := by
  have ho : IsOpen (g₁ Sec d a : Set (GL (Fin a) (Af E))) := by
    rw [g₁_coe]
    exact (gSet_open hSl hS d hd a ha).preimage (continuous_id.prodMk continuous_const)
  refine ⟨ho, (GlobalTheory.T.finite_kernel_compact_open E a).2.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ ho) ?_⟩
  intro g hg
  rw [g₁_coe] at hg
  exact (Subgroup.mem_prod.1 (gSet_sub hSl hS d hd a ha hg)).1

theorem g₂_oc (hSl : Slots) {Sec : Set (Pl E)} (hS : IsSection Sec) (d : LocData E n) (hd : d.Ok) (a : ℕ)
    (ha : a ≤ n) : IsOpen (g₂ Sec d a : Set (GL (Fin (n - a)) (Af E))) ∧
      IsCompact (g₂ Sec d a : Set (GL (Fin (n - a)) (Af E))) := by
  have ho : IsOpen (g₂ Sec d a : Set (GL (Fin (n - a)) (Af E))) := by
    rw [g₂_coe]
    exact (gSet_open hSl hS d hd a ha).preimage (continuous_const.prodMk continuous_id)
  refine ⟨ho, (GlobalTheory.T.finite_kernel_compact_open E (n - a)).2.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ ho) ?_⟩
  intro g hg
  rw [g₂_coe] at hg
  exact (Subgroup.mem_prod.1 (gSet_sub hSl hS d hd a ha hg)).2

theorem gSet_oc (hSl : Slots) {Sec : Set (Pl E)} (hS : IsSection Sec) (d : LocData E n) (hd : d.Ok) (a : ℕ)
    (ha : a ≤ n) : IsOpen (gSet Sec d a) ∧ IsCompact (gSet Sec d a) := by
  have ho := gSet_open hSl hS d hd a ha
  refine ⟨ho, ?_⟩
  have hc : IsCompact (((Kf E a).prod (Kf E (n - a)) : Subgroup (Hf E a (n - a))) : Set (Hf E a (n - a))) := by
    rw [Subgroup.coe_prod]
    exact (GlobalTheory.T.finite_kernel_compact_open E a).2.prod (GlobalTheory.T.finite_kernel_compact_open E (n - a)).2
  exact hc.of_isClosed_subset (Subgroup.isClosed_of_isOpen (levSub Sec d a) ho) (gSet_sub hSl hS d hd a ha)

end PositivityTheory.Rg.BcB.F.Rd.LevOC

end
