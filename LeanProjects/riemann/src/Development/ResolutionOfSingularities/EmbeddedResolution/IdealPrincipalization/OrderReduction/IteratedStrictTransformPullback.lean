import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransformOffCenter
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictTransformFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DimensionRecursion
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.SequenceOfBlowupsPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MapToEarlierScheme
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.CenterInvariant
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.BoundaryRelabeling
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.LevelwiseIso
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

private theorem comap_eqToHom_of_eq {F : ℕ → Scheme.{u}} (K : ∀ i : ℕ, (F i).IdealSheafData)
    {a b : ℕ} (h : a = b) : (K b).comap (eqToHom (congrArg F h)) = K a := by
  subst h
  exact AlgebraicGeometry.Scheme.IdealSheafData.comap_id _

private theorem smooth_of_isPullback_of_smooth_right {A B C D : Scheme.{u}} {f : A ⟶ B} {g : A ⟶ C}
    {h : B ⟶ D} {k : C ⟶ D} (sq : IsPullback f g h k) [AlgebraicGeometry.Smooth k] :
    AlgebraicGeometry.Smooth f :=
  MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Smooth) sq.flip inferInstance

private theorem isPullback_of_unique {P A C B : Scheme.{u}} (e : P ⟶ A) [IsIso e]
    (ψ : A ⟶ C) (h : C ⟶ B) (φ : A ⟶ B) (hψ : ψ ≫ h = φ)
    (huniq : ∀ (T : Scheme.{u}) (v : T ⟶ A) (u : T ⟶ C), u ≫ h = v ≫ φ → u = v ≫ ψ) :
    IsPullback (e ≫ ψ) e h φ := by
  have w : (e ≫ ψ) ≫ h = e ≫ φ := by rw [Category.assoc, hψ]
  refine IsPullback.of_isLimit' ⟨w⟩
    (Limits.PullbackCone.IsLimit.mk w (fun s => s.snd ≫ inv e) ?_ ?_ ?_)
  · intro s
    have h1 := huniq s.pt s.snd s.fst s.condition
    simp only [Category.assoc, IsIso.inv_hom_id_assoc]
    exact h1.symm
  · intro s
    simp
  · intro s m _ hm2
    rw [← hm2]
    simp

private theorem exists_lift_of_centers_comap_eq_top {A B : Scheme.{u}} (φ : A ⟶ B) (c : SequenceOfBlowups B)
    (hinv : ∀ i : ℕ, i < c.length → ∀ ψ : A ⟶ c.schemeAt i,
      ψ ≫ c.projectionToBase i = φ → (c.center i).comap ψ = ⊤) :
    ∀ i : ℕ, i ≤ c.length → ∃ ψ : A ⟶ c.schemeAt i, ψ ≫ c.projectionToBase i = φ ∧
      ∀ (T : Scheme.{u}) (v : T ⟶ A) (u : T ⟶ c.schemeAt i), u ≫ c.projectionToBase i = v ≫ φ →
        u = v ≫ ψ := by
  intro i
  induction i with
  | zero =>
    intro _
    have : IsIso (c.projectionToBase 0) := by
      rw [SequenceOfBlowups.projectionToBase_zero]
      infer_instance
    refine ⟨φ ≫ CategoryTheory.inv (c.projectionToBase 0), by simp, ?_⟩
    intro T v u h
    rw [← Category.assoc, ← h]
    simp
  | succ m ih =>
    intro hm
    obtain ⟨ψ, hψ, hu⟩ := ih (Nat.le_of_lt hm)
    have hmlt : m < c.length := hm
    have htop : (c.center m).comap ψ = ⊤ := hinv m hmlt ψ hψ
    have hbl : Blowup.IsBlowupAlongIdealSheaf (c.transitionMapSucc m) (c.center m) := c.isBlowupAlongIdealSheaf_blowupMorphism m hmlt
    have hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor ((c.center m).comap ψ) := by
      rw [htop]
      exact Blowup.isLocallyGeneratedByNonZeroDivisor_top _
    have h2 : c.transitionMapSucc m ≫ c.projectionToBase m = c.projectionToBase (m + 1) := by
      rw [SequenceOfBlowups.blowupMorphism_eq_transitionMap]
      exact c.transitionMap_comp_projectionToBase _
    refine ⟨hbl.lift ψ hcart, ?_, ?_⟩
    · have h1 : hbl.lift ψ hcart ≫ c.transitionMapSucc m = ψ := hbl.lift_comp ψ hcart
      rw [← h2, ← Category.assoc, h1, hψ]
    · intro T v u h
      have hdown : u ≫ c.transitionMapSucc m = v ≫ ψ := by
        refine hu T v (u ≫ c.transitionMapSucc m) ?_
        rw [Category.assoc, h2]
        exact h
      have hcart2 : Blowup.IsLocallyGeneratedByNonZeroDivisor ((c.center m).comap (v ≫ ψ)) := by
        rw [Scheme.IdealSheafData.comap_comp, htop]
        exact Blowup.isLocallyGeneratedByNonZeroDivisor_comap_top v
      refine hbl.hom_ext_of_comp_eq hcart2 hdown ?_
      rw [Category.assoc, hbl.lift_comp ψ hcart]

private theorem eq_comap_mapToEarlierScheme_succ_of_index_ne {X X' : Scheme.{u}} {φ : X' ⟶ X} {t' : SequenceOfBlowups X'}
    {t : SequenceOfBlowups X} (c : SequenceOfBlowupsPullback φ t' t)
    (K : ∀ i : ℕ, (t.schemeAt i).IdealSheafData)
    (hN : ∀ i : ℕ, i ≤ t.length → AlgebraicGeometry.IsNoetherian (t.schemeAt i))
    (hrec : ∀ i : ℕ, i < t.length → K (i + 1) = Blowup.strictTransform (t.transitionMapSucc i) (t.center i) (K i))
    (j : ℕ) (hj : j ≤ t'.length) (i : ℕ) (hi : i < c.idx j)
    (hmiss : ∀ j' : ℕ, j' < t'.length → c.idx j' ≠ i)
    (L : (t'.schemeAt j).IdealSheafData)
    (h : L = (K i).comap (c.mapToEarlierScheme j hj i (le_of_lt hi))) :
    L = (K (i + 1)).comap (c.mapToEarlierScheme j hj (i + 1) hi) := by
  have hilt : i < t.length := lt_of_lt_of_le hi (c.index_le_length j hj)
  have : AlgebraicGeometry.IsNoetherian (t.schemeAt (i + 1)) := hN (i + 1) hilt
  have hcenter : ((t.center i).comap (t.transitionMapSucc i)).comap (c.mapToEarlierScheme j hj (i + 1) hi) = ⊤ := by
    rw [← Scheme.IdealSheafData.comap_comp, ← c.mapToEarlierScheme_eq_comp_blowupMorphism j hj i hi]
    exact c.comap_center_mapToEarlierScheme_eq_top_of_unmatched j hj i hi hmiss
  rw [h, hrec i hilt,
    FunctorialResolution.EmbeddedResolution.strictTransform_comap_of_comap_center_eq_top (t.transitionMapSucc i) (t.center i) (K i)
      (c.mapToEarlierScheme j hj (i + 1) hi) hcenter,
    ← Scheme.IdealSheafData.comap_comp, ← c.mapToEarlierScheme_eq_comp_blowupMorphism j hj i hi]

private theorem eq_comap_mapToEarlierScheme_of_le_of_index_ne {X X' : Scheme.{u}} {φ : X' ⟶ X} {t' : SequenceOfBlowups X'}
    {t : SequenceOfBlowups X} (c : SequenceOfBlowupsPullback φ t' t)
    (K : ∀ i : ℕ, (t.schemeAt i).IdealSheafData)
    (hN : ∀ i : ℕ, i ≤ t.length → AlgebraicGeometry.IsNoetherian (t.schemeAt i))
    (hrec : ∀ i : ℕ, i < t.length → K (i + 1) = Blowup.strictTransform (t.transitionMapSucc i) (t.center i) (K i))
    (j : ℕ) (hj : j ≤ t'.length) (L : (t'.schemeAt j).IdealSheafData) (i₀ : ℕ) (hi₀ : i₀ ≤ c.idx j)
    (hmiss : ∀ i : ℕ, i₀ ≤ i → i < c.idx j → ∀ j' : ℕ, j' < t'.length → c.idx j' ≠ i)
    (h : L = (K i₀).comap (c.mapToEarlierScheme j hj i₀ hi₀)) :
    ∀ i : ℕ, i₀ ≤ i → ∀ hi : i ≤ c.idx j, L = (K i).comap (c.mapToEarlierScheme j hj i hi) := by
  intro i hii
  induction i, hii using Nat.le_induction with
  | base => intro _; exact h
  | succ p hp ih =>
    intro hi
    have hplt : p < c.idx j := hi
    exact eq_comap_mapToEarlierScheme_succ_of_index_ne c K hN hrec j hj p hplt (hmiss p hp hplt) L (ih (le_of_lt hplt))

private theorem iteratedStrictTransform_succ_eq_comap_map {X X' : Scheme.{u}} {φ : X' ⟶ X} {t' : SequenceOfBlowups X'}
    {t : SequenceOfBlowups X} (c : SequenceOfBlowupsPullback φ t' t) [AlgebraicGeometry.Flat φ]
    (K : ∀ i : ℕ, (t.schemeAt i).IdealSheafData) (K' : ∀ j : ℕ, (t'.schemeAt j).IdealSheafData)
    (hN : ∀ i : ℕ, i ≤ t.length → AlgebraicGeometry.IsNoetherian (t.schemeAt i))
    (hN' : ∀ j : ℕ, j ≤ t'.length → AlgebraicGeometry.IsNoetherian (t'.schemeAt j))
    (hrec : ∀ i : ℕ, i < t.length → K (i + 1) = Blowup.strictTransform (t.transitionMapSucc i) (t.center i) (K i))
    (hrec' : ∀ j : ℕ, j < t'.length →
      K' (j + 1) = Blowup.strictTransform (t'.transitionMapSucc j) (t'.center j) (K' j))
    (j : ℕ) (hj : j < t'.length)
    (h : K' j = (K (c.idx j)).comap (c.map j (le_of_lt hj))) :
    K' (j + 1) = (K (c.idx (j + 1))).comap (c.map (j + 1) hj) := by
  have hidxlt : c.idx j < t.length := c.idx_lt j hj
  have : AlgebraicGeometry.IsNoetherian (t.schemeAt (c.idx j + 1)) := hN (c.idx j + 1) hidxlt
  have : AlgebraicGeometry.IsNoetherian (t'.schemeAt (j + 1)) := hN' (j + 1) hj
  have : AlgebraicGeometry.Flat (c.map j (le_of_lt hj)) := c.flat_map j (le_of_lt hj)
  have hsq := c.isPullback_blowupMorphism j hj
  have key := FunctorialResolution.EmbeddedResolution.comap_strictTransform_of_flat_of_isLocallyNoetherian
    (t.transitionMapSucc (c.idx j)) (c.map j (le_of_lt hj)) (t'.transitionMapSucc j)
    (c.mapToEarlierScheme (j + 1) hj (c.idx j + 1) (c.idx_strictMono j hj)) hsq
    (t.center (c.idx j)) (K (c.idx j)) (t.isBlowupAlongIdealSheaf_blowupMorphism (c.idx j) hidxlt)
  have e1 : K (c.idx j + 1)
      = Blowup.strictTransform (t.transitionMapSucc (c.idx j)) (t.center (c.idx j)) (K (c.idx j)) :=
    hrec (c.idx j) hidxlt
  have e2 : K' (j + 1)
      = (K (c.idx j + 1)).comap (c.mapToEarlierScheme (j + 1) hj (c.idx j + 1) (c.idx_strictMono j hj)) := by
    rw [hrec' j hj, e1, key, h, c.center_comap j hj]
  have hmiss : ∀ i : ℕ, c.idx j + 1 ≤ i → i < c.idx (j + 1) →
      ∀ j' : ℕ, j' < t'.length → c.idx j' ≠ i :=
    fun i h1 h2 => c.index_ne_of_index_lt_of_lt_index_succ j hj i h1 h2
  have hfin := eq_comap_mapToEarlierScheme_of_le_of_index_ne c K hN hrec (j + 1) hj (K' (j + 1)) (c.idx j + 1)
    (c.idx_strictMono j hj) hmiss e2 (c.idx (j + 1)) (c.idx_strictMono j hj) le_rfl
  rw [c.mapToEarlierScheme_index (j + 1) hj] at hfin
  exact hfin

private theorem iteratedStrictTransform_eq_comap_lastMap_of_sequence {X X' : Scheme.{u}} {φ : X' ⟶ X} {t' : SequenceOfBlowups X'}
    {t : SequenceOfBlowups X} (c : SequenceOfBlowupsPullback φ t' t) [AlgebraicGeometry.Flat φ]
    (K : ∀ i : ℕ, (t.schemeAt i).IdealSheafData) (K' : ∀ j : ℕ, (t'.schemeAt j).IdealSheafData)
    (hN : ∀ i : ℕ, i ≤ t.length → AlgebraicGeometry.IsNoetherian (t.schemeAt i))
    (hN' : ∀ j : ℕ, j ≤ t'.length → AlgebraicGeometry.IsNoetherian (t'.schemeAt j))
    (hzero : K' 0 = (K 0).comap (c.mapToEarlierScheme 0 (Nat.zero_le _) 0 (Nat.zero_le _)))
    (hrec : ∀ i : ℕ, i < t.length → K (i + 1) = Blowup.strictTransform (t.transitionMapSucc i) (t.center i) (K i))
    (hrec' : ∀ j : ℕ, j < t'.length →
      K' (j + 1) = Blowup.strictTransform (t'.transitionMapSucc j) (t'.center j) (K' j)) :
    K' t'.length = (K t.length).comap c.lastMap := by
  have main : ∀ (j : ℕ) (hj : j ≤ t'.length), K' j = (K (c.idx j)).comap (c.map j hj) := by
    intro j
    induction j with
    | zero =>
      intro hj
      have hmiss : ∀ i : ℕ, 0 ≤ i → i < c.idx 0 → ∀ j' : ℕ, j' < t'.length → c.idx j' ≠ i :=
        fun i _ h2 => c.index_ne_of_lt_index_zero i h2
      have hfin := eq_comap_mapToEarlierScheme_of_le_of_index_ne c K hN hrec 0 hj (K' 0) 0 (Nat.zero_le _) hmiss hzero
        (c.idx 0) (Nat.zero_le _) le_rfl
      rw [c.mapToEarlierScheme_index 0 hj] at hfin
      exact hfin
    | succ m ih =>
      intro hj
      exact iteratedStrictTransform_succ_eq_comap_map c K K' hN hN' hrec hrec' m hj (ih (Nat.le_of_lt hj))
  have hend := main t'.length le_rfl
  have hLastMap : c.lastMap = c.map t'.length le_rfl ≫ eqToHom (congrArg t.schemeAt c.idx_length) := rfl
  rw [hend, hLastMap, Scheme.IdealSheafData.comap_comp, comap_eqToHom_of_eq]
  exact c.idx_length

namespace SequenceOfBlowupsPullback

section

variable {X X' : Scheme.{u}} {φ : X' ⟶ X}

theorem smooth_lastMap {s' : SequenceOfBlowups X'} {s : SequenceOfBlowups X} (c : SequenceOfBlowupsPullback φ s' s)
    [AlgebraicGeometry.Smooth φ] : AlgebraicGeometry.Smooth c.lastMap :=
  smooth_of_isPullback_of_smooth_right c.isPullback_lastMap

end

section

variable {k k' : Type u} [Field k] [Field k']
variable {X Y : Scheme.{u}}
variable {p : X ⟶ Spec (CommRingCat.of k)} {q : Y ⟶ Spec (CommRingCat.of k')}
variable {g : Y ⟶ X}
variable {I : X.IdealSheafData} {I' : Y.IdealSheafData} {m : ℕ}
variable {E : List X.IdealSheafData} {E' : List Y.IdealSheafData}

theorem iteratedStrictTransform_eq_comap_lastMap {s : MarkedBlowupSequenceData p I m E} {s' : MarkedBlowupSequenceData q I' m E'}
    (d : SequenceOfBlowupsPullback g s'.toMarkedSequenceOfBlowups.toSequenceOfBlowups s.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    [AlgebraicGeometry.Flat g]
    (K : ∀ i : ℕ, (s.obj i).IdealSheafData) (K' : ∀ j : ℕ, (s'.obj j).IdealSheafData)
    (hN : ∀ i : ℕ, i ≤ s.length → AlgebraicGeometry.IsNoetherian (s.obj i))
    (hN' : ∀ j : ℕ, j ≤ s'.length → AlgebraicGeometry.IsNoetherian (s'.obj j))
    (hzero : K' 0 = (K 0).comap (d.mapToEarlierScheme 0 (Nat.zero_le _) 0 (Nat.zero_le _)))
    (hrec : ∀ i : ℕ, i < s.length →
      K (i + 1) = Blowup.strictTransform (s.map i) (s.center i) (K i))
    (hrec' : ∀ j : ℕ, j < s'.length →
      K' (j + 1) = Blowup.strictTransform (s'.map j) (s'.center j) (K' j)) :
    K' s'.length = (K s.length).comap d.lastMap := by
  refine iteratedStrictTransform_eq_comap_lastMap_of_sequence d K K' ?_ ?_ hzero ?_ ?_
  · intro i hi
    exact hN i hi
  · intro j hj
    exact hN' j hj
  · intro i hi
    rw [MarkedBlowupSequenceData.toMarkedSequence_blowupMorphism, MarkedBlowupSequenceData.toMarkedSequence_center]
    exact hrec i hi
  · intro j hj
    rw [MarkedBlowupSequenceData.toMarkedSequence_blowupMorphism, MarkedBlowupSequenceData.toMarkedSequence_center]
    exact hrec' j hj

end

end SequenceOfBlowupsPullback

theorem isPullback_of_length_zero_of_comap_center_eq_top {A B : Scheme.{u}} (φ : A ⟶ B)
    (n : SequenceOfBlowups A) (c : SequenceOfBlowups B) (hn : n.length = 0)
    (hinv : ∀ i : ℕ, i < c.length → ∀ ψ : A ⟶ c.schemeAt i,
      ψ ≫ c.projectionToBase i = φ → (c.center i).comap ψ = ⊤) :
    IsPullbackBlowupSequence φ n c := by
  obtain ⟨ψ, hψ, huniq⟩ := exists_lift_of_centers_comap_eq_top φ c hinv c.length le_rfl
  have hlt : ∀ j : ℕ, ¬ j < n.length := by
    intro j hj
    rw [hn] at hj
    exact Nat.not_lt_zero j hj
  refine SequenceOfBlowupsPullback.isPullbackSequenceOfBlowups
    { idx := fun _ => c.length
      map := fun j _ => n.projectionToBase j ≫ ψ
      idx_length := rfl
      idx_lt := fun j hj => absurd hj (hlt j)
      idx_strictMono := fun j hj => absurd hj (hlt j)
      isPullback := ?_
      step := fun j hj => absurd hj (hlt j)
      center_comap := fun j hj => absurd hj (hlt j)
      center_ne_top := fun j hj => absurd hj (hlt j)
      omitted := ?_ }
  · intro j hj
    have hj0 : j = 0 := by
      rw [hn] at hj
      omega
    subst hj0
    have : IsIso (n.projectionToBase 0) := by
      rw [SequenceOfBlowups.projectionToBase_zero]
      infer_instance
    exact isPullback_of_unique (n.projectionToBase 0) ψ (c.projectionToBase c.length) φ hψ huniq
  · intro i hi _ z hz x' hcon
    obtain ⟨ψi, hψi, huniqi⟩ := exists_lift_of_centers_comap_eq_top φ c hinv i (le_of_lt hi)
    have htop : (c.center i).comap ψi = ⊤ := hinv i hi ψi hψi
    obtain ⟨w, hw1, hw2⟩ :=
      AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback
        (f := c.projectionToBase i) (g := φ) (x := z) (y := x') hcon.symm
    have hfac : Limits.pullback.fst (c.projectionToBase i) φ
        = Limits.pullback.snd (c.projectionToBase i) φ ≫ ψi :=
      huniqi _ (Limits.pullback.snd (c.projectionToBase i) φ) (Limits.pullback.fst (c.projectionToBase i) φ)
        Limits.pullback.condition
    have hza : ψi.base ((Limits.pullback.snd (c.projectionToBase i) φ).base w) = z := by
      rw [← hw1]
      show (Limits.pullback.snd (c.projectionToBase i) φ ≫ ψi).base w
        = (Limits.pullback.fst (c.projectionToBase i) φ).base w
      rw [hfac]
    have key : (1 : ℕ∞) ≤ orderAt ((c.center i).comap ψi)
        ((Limits.pullback.snd (c.projectionToBase i) φ).base w) := by
      refine le_trans ?_ (orderAt_le_orderAt_comap ψi (c.center i) _)
      show (1 : ℕ∞) ≤ orderAt (c.center i) (ψi.base _)
      rw [hza]
      exact (one_le_orderAt_iff_mem_support _ _).2 hz
    rw [htop, orderAt_top] at key
    simp at key

end FunctorialResolution.EmbeddedResolution
