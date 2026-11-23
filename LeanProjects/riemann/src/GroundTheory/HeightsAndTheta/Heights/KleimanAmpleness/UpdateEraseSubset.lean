import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsMoreMore
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.KerAltSucc
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisFurther
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCechDSq
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

noncomputable section

section Cells

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, LinearOrder (ι k)] {Ω : Type} [Field Ω] [Algebra S Ω] {y : (Σ k, ι k) → Ω} {n : ℕ}

theorem cellD_apply_of_not (s : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n → Ω) (I : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι (n + 1))
    (hI : ¬ CellMeets y I.1) : cellD S y n s I = 0 := by
  simp only [cellD, LinearMap.pi_apply, if_neg hI, LinearMap.zero_apply]

open Classical in
theorem cellD_apply_of (s : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n → Ω) (I : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι (n + 1))
    (hI : CellMeets y I.1) :
    cellD S y n s I = ∑ k, ∑ i ∈ I.1 k,
      if h : (∀ l, (Function.update I.1 k ((I.1 k).erase i) l).Nonempty) ∧
          ∑ l, ((Function.update I.1 k ((I.1 k).erase i) l).card - 1) = n then
        ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.faceSign I.1 k i • s ⟨Function.update I.1 k ((I.1 k).erase i), h⟩
      else 0 := by
  simp only [cellD, LinearMap.pi_apply, if_pos hI, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> rfl

omit [Fintype K] in
theorem update_erase_subset (I : ∀ k, Finset (ι k)) (k : K) (i : ι k) (l : K) :
    Function.update I k ((I k).erase i) l ⊆ I l := by
  rcases eq_or_ne l k with rfl | h
  · rw [Function.update_self]; exact Finset.erase_subset _ _
  · rw [Function.update_of_ne h]

omit [Fintype K] [LinearOrder K] [∀ k, LinearOrder (ι k)] in
theorem cellMeets_of_subset {I I' : ∀ k, Finset (ι k)} (h : ∀ k, I k ⊆ I' k) (hI' : CellMeets y I') :
    CellMeets y I :=
  fun k i hi => hI' k i (h k hi)

omit [LinearOrder K] [∀ k, LinearOrder (ι k)] in
theorem mem_cellCOf {G : (∀ k, Finset (ι k)) → Submodule S Ω} {s : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n → Ω} :
    s ∈ cellCOf S G n ↔ ∀ c, s c ∈ G c.1 := by
  simp [cellCOf, Submodule.mem_pi]

theorem cellD_mem (G : (∀ k, Finset (ι k)) → Submodule S Ω)
    (hG : ∀ I I' : ∀ k, Finset (ι k), (∀ k, (I k).Nonempty) → (∀ k, (I' k).Nonempty) → (∀ k, I k ⊆ I' k) →
      CellMeets y I' → G I ≤ G I')
    {s : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n → Ω} (hs : s ∈ cellCOf S G n) : cellD S y n s ∈ cellCOf S G (n + 1) := by
  rw [mem_cellCOf] at hs ⊢
  intro I
  by_cases hI : CellMeets y I.1
  · rw [cellD_apply_of s I hI]
    refine Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun i _ => ?_
    split_ifs with h
    · exact zsmul_mem (hG _ _ h.1 I.2.1 (update_erase_subset I.1 k i) hI (hs ⟨_, h⟩)) _
    · exact Submodule.zero_mem _
  · rw [cellD_apply_of_not s I hI]
    exact Submodule.zero_mem _

theorem sum_faceSign_pair (I : ∀ k, Finset (ι k)) (k₁ : K) (h2 : (I k₁).card = 2)
    (h1 : ∀ l, l ≠ k₁ → (I l).card = 1) : ∑ i ∈ I k₁, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.faceSign I k₁ i = 0 := by
  have hoff : ∑ l ∈ Finset.univ.filter (· < k₁), ((I l).card - 1) = 0 :=
    Finset.sum_eq_zero fun l hl => by rw [h1 l (ne_of_lt (Finset.mem_filter.1 hl).2), Nat.sub_self]
  simp_rw [ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.faceSign, hoff, add_zero]
  obtain ⟨a, b, hab, hI⟩ := Finset.card_eq_two.mp h2
  rw [hI, Finset.sum_pair hab]
  rcases hab.lt_or_gt with h | h
  · have e1 : ({a, b} : Finset (ι k₁)).filter (· < a) = ∅ := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
      rintro (rfl | rfl) hz
      · exact lt_irrefl _ hz
      · exact lt_asymm h hz
    have e2 : ({a, b} : Finset (ι k₁)).filter (· < b) = {a} := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl, hz⟩
        · rfl
        · exact absurd hz (lt_irrefl _)
      · rintro rfl
        exact ⟨Or.inl rfl, h⟩
    simp [e1, e2]
  · have e1 : ({a, b} : Finset (ι k₁)).filter (· < b) = ∅ := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
      rintro (rfl | rfl) hz
      · exact lt_asymm h hz
      · exact lt_irrefl _ hz
    have e2 : ({a, b} : Finset (ι k₁)).filter (· < a) = {b} := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl, hz⟩
        · exact absurd hz (lt_irrefl _)
        · rfl
      · rintro rfl
        exact ⟨Or.inr rfl, h⟩
    simp [e1, e2]

theorem cellD_const (z : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι 0 → Ω) (a : Ω)
    (hz : ∀ c : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι 0, CellMeets y c.1 → z c = a) : cellD S y 0 z = 0 := by
  funext I
  by_cases hI : CellMeets y I.1
  · rw [cellD_apply_of z I hI, Pi.zero_apply]
    have hsum : ∑ k, ((I.1 k).card - 1) = 1 := I.2.2
    have hpos : ∀ k, 1 ≤ (I.1 k).card := fun k => (I.2.1 k).card_pos
    obtain ⟨k₁, hk₁⟩ : ∃ k₁, (I.1 k₁).card - 1 ≠ 0 := by
      by_contra h
      push Not at h
      rw [Finset.sum_eq_zero (fun k _ => h k)] at hsum
      omega
    have hsplit := Finset.add_sum_erase Finset.univ (fun k => (I.1 k).card - 1) (Finset.mem_univ k₁)
    rw [hsum] at hsplit
    have h2 : (I.1 k₁).card = 2 := by have := hpos k₁; omega
    have hrest : ∑ l ∈ Finset.univ.erase k₁, ((I.1 l).card - 1) = 0 := by omega
    have h1 : ∀ l, l ≠ k₁ → (I.1 l).card = 1 := fun l hl => by
      have := (Finset.sum_eq_zero_iff.mp hrest) l (Finset.mem_erase.mpr ⟨hl, Finset.mem_univ _⟩)
      have := hpos l
      omega
    rw [Finset.sum_eq_single k₁]
    · refine (Finset.sum_congr rfl (g := fun i => ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.faceSign I.1 k₁ i • a) fun i hi => ?_).trans
        (by rw [← Finset.sum_smul, sum_faceSign_pair I.1 k₁ h2 h1, zero_smul])
      split_ifs with h
      · rw [hz ⟨_, h⟩ (cellMeets_of_subset (update_erase_subset I.1 k₁ i) hI)]
      · exfalso
        apply h
        have hc : ((I.1 k₁).erase i).card = 1 := by rw [Finset.card_erase_of_mem hi, h2]
        refine ⟨fun l => ?_, Finset.sum_eq_zero fun l _ => ?_⟩
        · rcases eq_or_ne l k₁ with rfl | hl
          · rw [Function.update_self]; exact Finset.card_pos.mp (by omega)
          · rw [Function.update_of_ne hl]; exact I.2.1 l
        · rcases eq_or_ne l k₁ with rfl | hl
          · rw [Function.update_self, hc, Nat.sub_self]
          · rw [Function.update_of_ne hl, h1 l hl, Nat.sub_self]
    · intro k _ hk
      refine Finset.sum_eq_zero fun i hi => ?_
      split_ifs with h
      · exfalso
        have hne := h.1 k
        rw [Function.update_self] at hne
        have hc : ((I.1 k).erase i).card = 0 := by rw [Finset.card_erase_of_mem hi, h1 k hk]
        rw [Finset.card_eq_zero] at hc
        rw [hc] at hne
        exact Finset.not_nonempty_empty hne
      · rfl
    · intro h; exact absurd (Finset.mem_univ k₁) h
  · rw [cellD_apply_of_not z I hI]
    rfl

end Cells

section Double

variable {F : Type} [Field F] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, LinearOrder (ι k)]
  {Ω : Type} [Field Ω] [Algebra F Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

variable (K ι Ω x) in

abbrev DoubleCech.Amb (q p : ℕ) : Type :=
  Kleiman.Cech.Cochain (fun _ : Kleiman.Chart x => ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι q → Ω) p

variable (F K ι Ω x) in

def DoubleCech.vert (q p : ℕ) : DoubleCech.Amb K ι Ω x q p →ₗ[F] DoubleCech.Amb K ι Ω x q (p + 1) :=
  Kleiman.Cech.d (fun _ : Kleiman.Chart x => ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι q → Ω) (fun _ _ _ => LinearMap.id) p

variable (F) in

def DoubleCech.horiz (y : (Σ k, ι k) → Ω) (q p : ℕ) :
    DoubleCech.Amb K ι Ω x q p →ₗ[F] DoubleCech.Amb K ι Ω x (q + 1) p :=
  Kleiman.Cech.mapC (G := fun _ : Kleiman.Chart x => ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι q → Ω)
    (G' := fun _ : Kleiman.Chart x => ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι (q + 1) → Ω) (fun _ => cellD F y q) p

def DoubleCech.dsub (M : Kleiman.Chart x → (∀ k, Finset (ι k)) → Submodule F Ω) (q p : ℕ) :
    Submodule F (DoubleCech.Amb K ι Ω x q p) :=
  Kleiman.Cech.Cdeg (fun _ : Kleiman.Chart x => ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι q → Ω) (fun J => cellCOf F (M J) q) p

omit [LinearOrder K] [∀ k, LinearOrder (ι k)] in
theorem DoubleCech.mem_dsub' {M : Kleiman.Chart x → (∀ k, Finset (ι k)) → Submodule F Ω} {q p : ℕ}
    {s : DoubleCech.Amb K ι Ω x q p} : s ∈ DoubleCech.dsub M q p ↔ ∀ J, s J ∈ cellCOf F (M J.1) q := by
  simp [DoubleCech.dsub, Kleiman.Cech.Cdeg, Submodule.mem_pi]

omit [LinearOrder K] [∀ k, LinearOrder (ι k)] in
theorem DoubleCech.mem_dsub {M : Kleiman.Chart x → (∀ k, Finset (ι k)) → Submodule F Ω} {q p : ℕ}
    {s : DoubleCech.Amb K ι Ω x q p} : s ∈ DoubleCech.dsub M q p ↔ ∀ J c, s J c ∈ M J.1 c.1 := by
  simp only [DoubleCech.mem_dsub', mem_cellCOf]

omit [LinearOrder K] [∀ k, LinearOrder (ι k)] in
theorem DoubleCech.vert_apply {q p : ℕ} (s : DoubleCech.Amb K ι Ω x q p) (J : Kleiman.Cech.Idx (Kleiman.support x) (p + 1))
    (c : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι q) :
    DoubleCech.vert F K ι Ω x q p s J c =
      ∑ j : J.1.1, Kleiman.Cech.sgn J.1.1 j • s (Kleiman.Cech.face J j) c := by
  unfold DoubleCech.vert
  rw [Kleiman.Cech.d_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, LinearMap.id_apply]

omit [LinearOrder K] [∀ k, LinearOrder (ι k)] in

theorem DoubleCech.d_eval {q p : ℕ} (s : DoubleCech.Amb K ι Ω x q p) (c : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι q) :
    Kleiman.Cech.d (fun _ : Kleiman.Chart x => Ω) (omegaRes F x) p (fun J => s J c) =
      fun J => DoubleCech.vert F K ι Ω x q p s J c := by
  funext J
  rw [Kleiman.Cech.d_apply, DoubleCech.vert_apply]
  rfl

def DoubleCech.vD (M : Kleiman.Chart x → (∀ k, Finset (ι k)) → Submodule F Ω)
    (hMJ : ∀ (J J' : Kleiman.Chart x) I, J.1 ⊆ J'.1 → M J I ≤ M J' I) (q p : ℕ) :
    ↥(DoubleCech.dsub M q p) →ₗ[F] ↥(DoubleCech.dsub M q (p + 1)) :=
  (DoubleCech.vert F K ι Ω x q p).restrict fun s hs => by
    rw [DoubleCech.mem_dsub] at hs ⊢
    intro J c
    rw [DoubleCech.vert_apply]
    exact Submodule.sum_mem _ fun j _ => zsmul_mem (hMJ _ _ _ (Kleiman.Cech.face_subset J j) (hs _ c)) _

def DoubleCech.hD (y : (Σ k, ι k) → Ω) (M : Kleiman.Chart x → (∀ k, Finset (ι k)) → Submodule F Ω)
    (hMI : ∀ J (I I' : ∀ k, Finset (ι k)), (∀ k, I k ⊆ I' k) → CellMeets y I' → M J I ≤ M J I') (q p : ℕ) :
    ↥(DoubleCech.dsub M q p) →ₗ[F] ↥(DoubleCech.dsub M (q + 1) p) :=
  (DoubleCech.horiz F y q p).restrict fun s hs => by
    rw [DoubleCech.mem_dsub'] at hs ⊢
    exact fun J => cellD_mem (M J.1) (fun I I' _ _ h h' => hMI J.1 I I' h h') (hs J)

open Classical in

def DoubleCech.aug (y : (Σ k, ι k) → Ω) (T : Kleiman.SubSystem F x Ω)
    (M : Kleiman.Chart x → (∀ k, Finset (ι k)) → Submodule F Ω)
    (hrow : ∀ J, CellAugExact F y (M J) ((T.sub J).restrictScalars F)) (p : ℕ) :
    Kleiman.Cech.Cochain (fun J => ↥(T.sub J)) p →ₗ[F] ↥(DoubleCech.dsub M 0 p) where
  toFun t := ⟨fun J c => if CellMeets y c.1 then (t J : Ω) else 0, by
    rw [DoubleCech.mem_dsub]
    intro J c
    split_ifs with h
    · exact (hrow J.1).1 c.1 c.2.1 h (t J).2
    · exact Submodule.zero_mem _⟩
  map_add' t t' := Subtype.ext (funext fun J => funext fun c => by by_cases h : CellMeets y c.1 <;> simp [h])
  map_smul' r t := Subtype.ext (funext fun J => funext fun c => by by_cases h : CellMeets y c.1 <;> simp [h])

def DoubleCech.colAug (y : (Σ k, ι k) → Ω) (B : (∀ k, Finset (ι k)) → Submodule F Ω)
    (M : Kleiman.Chart x → (∀ k, Finset (ι k)) → Submodule F Ω) (hB : ∀ I, ¬ CellMeets y I → B I = ⊥)
    (hcol0 : ∀ I : ∀ k, Finset (ι k), (∀ k, (I k).Nonempty) → CellMeets y I → ∀ J, B I ≤ M J I) (q : ℕ) :
    ↥(cellCOf F B q) →ₗ[F] ↥(DoubleCech.dsub M q 0) where
  toFun b := ⟨fun _ c => (b : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι q → Ω) c, by
    rw [DoubleCech.mem_dsub]
    intro J c
    by_cases h : CellMeets y c.1
    · exact hcol0 c.1 c.2.1 h J.1 (mem_cellCOf.1 b.2 c)
    · have hb := mem_cellCOf.1 b.2 c
      rw [hB c.1 h, Submodule.mem_bot] at hb
      rw [hb]
      exact Submodule.zero_mem _⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def DoubleCech.dC (y : (Σ k, ι k) → Ω) (B : (∀ k, Finset (ι k)) → Submodule F Ω)
    (hBm : ∀ I I' : ∀ k, Finset (ι k), (∀ k, (I k).Nonempty) → (∀ k, (I' k).Nonempty) → (∀ k, I k ⊆ I' k) →
      CellMeets y I' → B I ≤ B I') (q : ℕ) :
    ↥(cellCOf F B q) →ₗ[F] ↥(cellCOf F B (q + 1)) :=
  (cellD F y q).restrict fun _ hs => cellD_mem B hBm hs

end Double

section Hyps

variable {F : Type} [Field F] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, LinearOrder (ι k)]
  {Ω : Type} [Field Ω] [Algebra F Ω] {N : ℕ} {x : Fin (N + 1) → Ω} {y : (Σ k, ι k) → Ω}
  {M : Kleiman.Chart x → (∀ k, Finset (ι k)) → Submodule F Ω}

theorem DoubleCech.comm (hMJ : ∀ (J J' : Kleiman.Chart x) I, J.1 ⊆ J'.1 → M J I ≤ M J' I)
    (hMI : ∀ J (I I' : ∀ k, Finset (ι k)), (∀ k, I k ⊆ I' k) → CellMeets y I' → M J I ≤ M J I') (p q : ℕ) :
    (DoubleCech.vD M hMJ (q + 1) p).comp (DoubleCech.hD y M hMI q p) =
      (DoubleCech.hD y M hMI q (p + 1)).comp (DoubleCech.vD M hMJ q p) :=
  LinearMap.ext fun s => Subtype.ext (Kleiman.Cech.mapC_d
    (ρ := fun _ _ _ => (LinearMap.id : (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι q → Ω) →ₗ[F] _))
    (ρ' := fun _ _ _ => (LinearMap.id : (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι (q + 1) → Ω) →ₗ[F] _))
    (fun _ => cellD F y q) (fun _ _ _ _ => rfl) p s.1).symm

theorem DoubleCech.aug_chain (hMJ : ∀ (J J' : Kleiman.Chart x) I, J.1 ⊆ J'.1 → M J I ≤ M J' I)
    (T : Kleiman.SubSystem F x Ω) (hrow : ∀ J, CellAugExact F y (M J) ((T.sub J).restrictScalars F)) (p : ℕ) :
    (DoubleCech.aug y T M hrow (p + 1)).comp (Kleiman.Cech.d (fun J => ↥(T.sub J)) T.res p) =
      (DoubleCech.vD M hMJ 0 p).comp (DoubleCech.aug y T M hrow p) := by
  classical
  refine LinearMap.ext fun t => Subtype.ext (funext fun J => funext fun c => ?_)
  change (if CellMeets y c.1 then ((Kleiman.Cech.d (fun J => ↥(T.sub J)) T.res p t J : ↥(T.sub J.1)) : Ω) else 0) =
    DoubleCech.vert F K ι Ω x 0 p (fun J c => if CellMeets y c.1 then (t J : Ω) else 0) J c
  rw [DoubleCech.vert_apply, Kleiman.Cech.d_apply]
  by_cases h : CellMeets y c.1
  · simp only [h, if_true, Submodule.coe_sum]
    rfl
  · simp [h]

theorem DoubleCech.col_chain (hMJ : ∀ (J J' : Kleiman.Chart x) I, J.1 ⊆ J'.1 → M J I ≤ M J' I)
    (hMI : ∀ J (I I' : ∀ k, Finset (ι k)), (∀ k, I k ⊆ I' k) → CellMeets y I' → M J I ≤ M J I')
    {B : (∀ k, Finset (ι k)) → Submodule F Ω} (hB : ∀ I, ¬ CellMeets y I → B I = ⊥)
    (hcol0 : ∀ I : ∀ k, Finset (ι k), (∀ k, (I k).Nonempty) → CellMeets y I → ∀ J, B I ≤ M J I)
    (hBm : ∀ I I' : ∀ k, Finset (ι k), (∀ k, (I k).Nonempty) → (∀ k, (I' k).Nonempty) → (∀ k, I k ⊆ I' k) →
      CellMeets y I' → B I ≤ B I') (q : ℕ) :
    (DoubleCech.colAug y B M hB hcol0 (q + 1)).comp (DoubleCech.dC y B hBm q) =
      (DoubleCech.hD y M hMI q 0).comp (DoubleCech.colAug y B M hB hcol0 q) :=
  LinearMap.ext fun _ => rfl

theorem DoubleCech.aug_inj (T : Kleiman.SubSystem F x Ω) (hrow : ∀ J, CellAugExact F y (M J) ((T.sub J).restrictScalars F))
    (c₀ : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι 0) (hc₀ : CellMeets y c₀.1) (p : ℕ) :
    LinearMap.ker (DoubleCech.aug y T M hrow p) = ⊥ := by
  classical
  refine LinearMap.ker_eq_bot'.2 fun t ht => funext fun J => Subtype.ext ?_
  have h := congrFun (congrFun (congrArg Subtype.val ht) J) c₀
  change (if CellMeets y c₀.1 then (t J : Ω) else 0) = 0 at h
  rw [if_pos hc₀] at h
  exact h

theorem DoubleCech.row_zero (hMI : ∀ J (I I' : ∀ k, Finset (ι k)), (∀ k, I k ⊆ I' k) → CellMeets y I' → M J I ≤ M J I')
    (hM : ∀ J I, ¬ CellMeets y I → M J I = ⊥)
    (T : Kleiman.SubSystem F x Ω) (hrow : ∀ J, CellAugExact F y (M J) ((T.sub J).restrictScalars F)) (p : ℕ) :
    LinearMap.ker (DoubleCech.hD y M hMI 0 p) = LinearMap.range (DoubleCech.aug y T M hrow p) := by
  classical
  refine le_antisymm (fun s hs => ?_) ?_
  · have hs' : ∀ J, cellD F y 0 (s.1 J) = 0 := fun J => congrFun (congrArg Subtype.val (LinearMap.mem_ker.1 hs)) J
    have hmem : ∀ J, s.1 J ∈ cellCOf F (M J.1) 0 := DoubleCech.mem_dsub'.1 s.2
    choose a ha hac using fun J => (hrow J.1).2.1 (s.1 J) (hmem J) (hs' J)
    refine ⟨fun J => ⟨a J, ha J⟩, Subtype.ext (funext fun J => funext fun c => ?_)⟩
    change (if CellMeets y c.1 then a J else 0) = s.1 J c
    split_ifs with h
    · exact (hac J c h).symm
    · have h0 := mem_cellCOf.1 (hmem J) c
      rw [hM J.1 c.1 h, Submodule.mem_bot] at h0
      exact h0.symm
  · rintro _ ⟨t, rfl⟩
    rw [LinearMap.mem_ker]
    exact Subtype.ext (funext fun J => cellD_const _ (t J : Ω) fun c hc => if_pos hc)

theorem DoubleCech.row_succ [∀ k, Fintype (ι k)] (hSq : CellDSq.Statement)
    (hMI : ∀ J (I I' : ∀ k, Finset (ι k)), (∀ k, I k ⊆ I' k) → CellMeets y I' → M J I ≤ M J I')
    (T : Kleiman.SubSystem F x Ω) (hrow : ∀ J, CellAugExact F y (M J) ((T.sub J).restrictScalars F)) (p q : ℕ) :
    LinearMap.ker (DoubleCech.hD y M hMI (q + 1) p) = LinearMap.range (DoubleCech.hD y M hMI q p) := by
  refine le_antisymm (fun s hs => ?_) ?_
  · have hs' : ∀ J, cellD F y (q + 1) (s.1 J) = 0 := fun J =>
      congrFun (congrArg Subtype.val (LinearMap.mem_ker.1 hs)) J
    have hmem : ∀ J, s.1 J ∈ cellCOf F (M J.1) (q + 1) := DoubleCech.mem_dsub'.1 s.2
    choose t ht htd using fun J => (hrow J.1).2.2 q (s.1 J) (hmem J) (hs' J)
    exact ⟨⟨t, DoubleCech.mem_dsub'.2 ht⟩, Subtype.ext (funext fun J => htd J)⟩
  · rintro _ ⟨t, rfl⟩
    rw [LinearMap.mem_ker]
    exact Subtype.ext (funext fun J => hSq F K ι Ω y q (t.1 J))

omit [LinearOrder K] [∀ k, LinearOrder (ι k)] in
theorem DoubleCech.col_inj {B : (∀ k, Finset (ι k)) → Submodule F Ω} (hB : ∀ I, ¬ CellMeets y I → B I = ⊥)
    (hcol0 : ∀ I : ∀ k, Finset (ι k), (∀ k, (I k).Nonempty) → CellMeets y I → ∀ J, B I ≤ M J I)
    (J₀ : Kleiman.Cech.Idx (Kleiman.support x) 0) (q : ℕ) :
    LinearMap.ker (DoubleCech.colAug y B M hB hcol0 q) = ⊥ :=
  LinearMap.ker_eq_bot'.2 fun _ hb => Subtype.ext (funext fun c => congrFun (congrFun (congrArg Subtype.val hb) J₀) c)

theorem DoubleCech.col_zero (hMJ : ∀ (J J' : Kleiman.Chart x) I, J.1 ⊆ J'.1 → M J I ≤ M J' I)
    (hM : ∀ J I, ¬ CellMeets y I → M J I = ⊥)
    {B : (∀ k, Finset (ι k)) → Submodule F Ω} (hB : ∀ I, ¬ CellMeets y I → B I = ⊥)
    (hcol : ∀ I : ∀ k, Finset (ι k), (∀ k, (I k).Nonempty) → CellMeets y I → CechAugExact F (fun J => M J I) (B I))
    (q : ℕ) :
    LinearMap.ker (DoubleCech.vD M hMJ q 0) =
      LinearMap.range (DoubleCech.colAug y B M hB (fun I hI hm => (hcol I hI hm).1) q) := by
  classical
  refine le_antisymm (fun s hs => ?_) ?_
  · have hex : ∀ c : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι q, ∃ b ∈ B c.1, ∀ J, s.1 J c = b := by
      intro c
      by_cases h : CellMeets y c.1
      · refine (hcol c.1 c.2.1 h).2.1 (fun J => s.1 J c) ?_ ?_
        · rw [Kleiman.Cech.Cdeg, Submodule.mem_pi]
          exact fun J _ => DoubleCech.mem_dsub.1 s.2 J c
        · rw [DoubleCech.d_eval]
          funext J
          exact congrFun (congrFun (congrArg Subtype.val (LinearMap.mem_ker.1 hs)) J) c
      · refine ⟨0, Submodule.zero_mem _, fun J => ?_⟩
        have h0 := DoubleCech.mem_dsub.1 s.2 J c
        rw [hM J.1 c.1 h, Submodule.mem_bot] at h0
        exact h0
    choose b hb hbs using hex
    exact ⟨⟨b, mem_cellCOf.2 hb⟩, Subtype.ext (funext fun J => funext fun c => (hbs c J).symm)⟩
  · rintro _ ⟨b, rfl⟩
    rw [LinearMap.mem_ker]
    exact Subtype.ext (Kleiman.Cech.d_zero_of_compat
      (ρ := fun _ _ _ => (LinearMap.id : (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι q → Ω) →ₗ[F] _))
      (fun _ => (b : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι q → Ω)) (fun _ _ _ => rfl))

omit [LinearOrder K] [∀ k, LinearOrder (ι k)] in
theorem DoubleCech.col_succ (hMJ : ∀ (J J' : Kleiman.Chart x) I, J.1 ⊆ J'.1 → M J I ≤ M J' I)
    (hM : ∀ J I, ¬ CellMeets y I → M J I = ⊥) {B : (∀ k, Finset (ι k)) → Submodule F Ω}
    (hcol : ∀ I : ∀ k, Finset (ι k), (∀ k, (I k).Nonempty) → CellMeets y I → CechAugExact F (fun J => M J I) (B I))
    (p q : ℕ) :
    LinearMap.ker (DoubleCech.vD M hMJ q (p + 1)) = LinearMap.range (DoubleCech.vD M hMJ q p) := by
  classical
  refine le_antisymm (fun s hs => ?_) ?_
  · have hex : ∀ c : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι q,
        ∃ t ∈ Kleiman.Cech.Cdeg (fun _ : Kleiman.Chart x => Ω) (fun J => M J c.1) p,
          Kleiman.Cech.d (fun _ : Kleiman.Chart x => Ω) (omegaRes F x) p t = fun J => s.1 J c := by
      intro c
      by_cases h : CellMeets y c.1
      · refine (hcol c.1 c.2.1 h).2.2 p (fun J => s.1 J c) ?_ ?_
        · rw [Kleiman.Cech.Cdeg, Submodule.mem_pi]
          exact fun J _ => DoubleCech.mem_dsub.1 s.2 J c
        · rw [DoubleCech.d_eval]
          funext J
          exact congrFun (congrFun (congrArg Subtype.val (LinearMap.mem_ker.1 hs)) J) c
      · refine ⟨0, Submodule.zero_mem _, ?_⟩
        rw [map_zero]
        funext J
        have h0 := DoubleCech.mem_dsub.1 s.2 J c
        rw [hM J.1 c.1 h, Submodule.mem_bot] at h0
        exact h0.symm
    choose t ht htd using hex
    have htm : ∀ c J, t c J ∈ M J.1 c.1 := fun c J => by
      have := ht c
      rw [Kleiman.Cech.Cdeg, Submodule.mem_pi] at this
      exact this J (Set.mem_univ _)
    refine ⟨⟨fun J c => t c J, DoubleCech.mem_dsub.2 fun J c => htm c J⟩, Subtype.ext (funext fun J => funext fun c => ?_)⟩
    have e := congrFun (DoubleCech.d_eval (F := F) (fun J c => t c J) c) J
    exact e.symm.trans (congrFun (htd c) J)
  · rintro _ ⟨t, rfl⟩
    rw [LinearMap.mem_ker]
    exact Subtype.ext (Kleiman.CechDSq.proof (N + 1) (Kleiman.support x) F
      (fun _ : Kleiman.Chart x => ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι q → Ω) (fun _ _ _ => LinearMap.id)
      (fun _ _ _ _ _ => LinearMap.id_comp _) p t.1)

omit [Fintype K] [LinearOrder K] [∀ k, LinearOrder (ι k)] in

theorem DoubleCech.B_mono {B : (∀ k, Finset (ι k)) → Submodule F Ω}
    (hMI : ∀ J (I I' : ∀ k, Finset (ι k)), (∀ k, I k ⊆ I' k) → CellMeets y I' → M J I ≤ M J I')
    (hcol : ∀ I : ∀ k, Finset (ι k), (∀ k, (I k).Nonempty) → CellMeets y I → CechAugExact F (fun J => M J I) (B I))
    (J₀ : Kleiman.Cech.Idx (Kleiman.support x) 0) :
    ∀ I I' : ∀ k, Finset (ι k), (∀ k, (I k).Nonempty) → (∀ k, (I' k).Nonempty) → (∀ k, I k ⊆ I' k) →
      CellMeets y I' → B I ≤ B I' := by
  intro I I' hne hne' hsub hm' m hm
  have hmI : CellMeets y I := cellMeets_of_subset hsub hm'
  have hall : ∀ J, m ∈ M J I' := fun J => hMI J I I' hsub hm' ((hcol I hne hmI).1 J hm)
  obtain ⟨b, hb, hbJ⟩ := (hcol I' hne' hm').2.1 (fun _ => m)
    (by rw [Kleiman.Cech.Cdeg, Submodule.mem_pi]; exact fun J _ => hall J.1)
    (Kleiman.Cech.d_zero_of_compat (fun _ => m) (fun _ _ _ => rfl))
  rw [hbJ J₀]
  exact hb

end Hyps

section Ends

variable {F : Type} [Field F] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, LinearOrder (ι k)]
  {Ω : Type} [Field Ω] [Algebra F Ω] {N : ℕ} {x : Fin (N + 1) → Ω} {y : (Σ k, ι k) → Ω}

theorem DoubleCech.T_equiv (T : Kleiman.SubSystem F x Ω) (n : ℕ) :
    Nonempty (T.H n ≃ₗ[F] Staircase.H (fun p => Kleiman.Cech.d (fun J => ↥(T.sub J)) T.res p) n) := by
  cases n <;> exact ⟨LinearEquiv.refl F _⟩

theorem DoubleCech.B_equiv {B : (∀ k, Finset (ι k)) → Submodule F Ω}
    (hBm : ∀ I I' : ∀ k, Finset (ι k), (∀ k, (I k).Nonempty) → (∀ k, (I' k).Nonempty) → (∀ k, I k ⊆ I' k) →
      CellMeets y I' → B I ≤ B I') (n : ℕ) :
    Nonempty (Staircase.H (fun q => DoubleCech.dC y B hBm q) n ≃ₗ[F] cellHOf F y B n) := by
  let e0 : ↥(LinearMap.ker (DoubleCech.dC y B hBm n)) ≃ₗ[F] ↥(cellZOf F y B n) :=
    { toFun := fun z => ⟨z.1.1, z.1.2, congrArg Subtype.val (LinearMap.mem_ker.1 z.2)⟩
      invFun := fun z => ⟨⟨z.1, z.2.1⟩, LinearMap.mem_ker.2 (Subtype.ext z.2.2)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  refine ⟨Submodule.Quotient.equiv _ _ e0 ?_⟩
  cases n with
  | zero =>
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hw0 : (w : ↥(cellCOf F B 0)) = 0 := (Submodule.mem_bot F).1 hw
      show ((e0 w : ↥(cellZOf F y B 0)) : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι 0 → Ω) ∈ (⊥ : Submodule F _)
      rw [Submodule.mem_bot]
      exact congrArg Subtype.val hw0
    · intro hz
      refine ⟨e0.symm z, ?_, e0.apply_symm_apply z⟩
      show ((e0.symm z : ↥(LinearMap.ker (DoubleCech.dC y B hBm 0))) : ↥(cellCOf F B 0)) ∈ (⊥ : Submodule F _)
      rw [Submodule.mem_bot]
      exact Subtype.ext ((Submodule.mem_bot F).1 hz)
  | succ n =>
    ext z
    constructor
    · rintro ⟨w, ⟨t, ht⟩, rfl⟩
      exact ⟨t.1, t.2, congrArg Subtype.val ht⟩
    · rintro ⟨t, htm, htz⟩
      refine ⟨e0.symm z, ⟨⟨t, htm⟩, Subtype.ext htz⟩, e0.apply_symm_apply z⟩

end Ends

theorem DoubleCech.proof (hS : Staircase.Statement) (hSq : CellDSq.Statement) : DoubleCech.Statement := by
  intro F _ K _ _ ι _ _ Ω _ _ y N x T B M hy hx hB hM hMJ hMI hcol hrow n
  classical
  obtain ⟨j, hj⟩ := hx
  let J₀ : Kleiman.Cech.Idx (Kleiman.support x) 0 :=
    ⟨⟨{j}, Finset.singleton_nonempty j, Finset.singleton_subset_iff.2 ((Kleiman.mem_support x).2 hj)⟩,
      Finset.card_singleton j⟩
  choose i hi using hy
  let c₀ : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι 0 := ⟨fun k => {i k}, fun k => Finset.singleton_nonempty _, by simp⟩
  have hc₀ : CellMeets y c₀.1 := fun k i' hi' => by
    rw [Finset.mem_singleton.1 hi']
    exact hi k
  have hcol0 : ∀ I : ∀ k, Finset (ι k), (∀ k, (I k).Nonempty) → CellMeets y I → ∀ J, B I ≤ M J I :=
    fun I hI hm => (hcol I hI hm).1
  have hBm := DoubleCech.B_mono hMI hcol J₀
  obtain ⟨e⟩ := hS F (fun p q => ↥(DoubleCech.dsub M q p)) (fun p q => DoubleCech.vD M hMJ q p)
    (fun p q => DoubleCech.hD y M hMI q p) (fun p => Kleiman.Cech.Cochain (fun J => ↥(T.sub J)) p)
    (fun p => Kleiman.Cech.d (fun J => ↥(T.sub J)) T.res p) (fun p => DoubleCech.aug y T M hrow p)
    (fun q => ↥(cellCOf F B q)) (fun q => DoubleCech.dC y B hBm q) (fun q => DoubleCech.colAug y B M hB hcol0 q)
    (DoubleCech.comm hMJ hMI) (DoubleCech.aug_chain hMJ T hrow) (DoubleCech.col_chain hMJ hMI hB hcol0 hBm)
    (DoubleCech.aug_inj T hrow c₀ hc₀) (DoubleCech.row_zero hMI hM T hrow) (DoubleCech.row_succ hSq hMI T hrow)
    (DoubleCech.col_inj hB hcol0 J₀) (DoubleCech.col_zero hMJ hM hB hcol) (DoubleCech.col_succ hMJ hM hcol) n
  obtain ⟨eT⟩ := DoubleCech.T_equiv T n
  obtain ⟨eB⟩ := DoubleCech.B_equiv hBm n
  exact ⟨eT.trans (e.trans eB)⟩

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
