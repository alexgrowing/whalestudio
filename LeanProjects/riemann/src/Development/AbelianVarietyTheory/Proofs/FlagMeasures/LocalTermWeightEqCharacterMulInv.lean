import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HL.TermPhase

section Tri

variable {E V : Type} [CommRing E] [AddCommGroup V] [Module E V] {r : ℕ}

def lowSpan (E : Type) [CommRing E] [Module E V] (f : Fin (r + 1) → V) (b : ℕ) : Submodule E V := Submodule.span E (f '' {c | (c : ℕ) < b})

theorem lowSpan_mono (f : Fin (r + 1) → V) {b b' : ℕ} (h : b ≤ b') :
    lowSpan E f b ≤ lowSpan E f b' :=
  Submodule.span_mono (Set.image_mono fun _ hc => lt_of_lt_of_le hc h)

abbrev IsTriW (f : Fin (r + 1) → V) (g : V ≃ₗ[E] V) : Prop := ∀ b : Fin (r + 1), g (f b) - f b ∈ lowSpan E f b

theorem map_lowSpan {f : Fin (r + 1) → V} {g : V ≃ₗ[E] V} (hg : IsTriW f g) (b : ℕ) :
    ∀ x ∈ lowSpan E f b, g x ∈ lowSpan E f b := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨c, hc, rfl⟩ := hy
    have h1 : f c ∈ lowSpan E f b := Submodule.subset_span ⟨c, hc, rfl⟩
    have h2 : g (f c) - f c ∈ lowSpan E f b := lowSpan_mono f (le_of_lt hc) (hg c)
    have := add_mem h2 h1
    simpa using this
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

theorem exists_pre_lowSpan {f : Fin (r + 1) → V} {g : V ≃ₗ[E] V} (hg : IsTriW f g) :
    ∀ b : ℕ, ∀ x ∈ lowSpan E f b, ∃ y ∈ lowSpan E f b, g y = x := by
  intro b
  induction b with
  | zero =>
    intro x hx
    have h0 : lowSpan E f 0 = ⊥ := by simp [lowSpan]
    rw [h0, Submodule.mem_bot] at hx
    exact ⟨0, zero_mem _, by simp [hx]⟩
  | succ b ih =>
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨c, hc, rfl⟩ := hy
      have hc' : (c : ℕ) < b ∨ (c : ℕ) = b := by
        have : (c : ℕ) < b + 1 := hc
        omega
      rcases hc' with hlt | heq
      · obtain ⟨w, hw, hgw⟩ := ih (f c) (Submodule.subset_span ⟨c, hlt, rfl⟩)
        exact ⟨w, lowSpan_mono f (Nat.le_succ b) hw, hgw⟩
      · obtain ⟨w, hw, hgw⟩ := ih (g (f c) - f c) (by rw [← heq]; exact hg c)
        refine ⟨f c - w, sub_mem (Submodule.subset_span ⟨c, hc, rfl⟩) (lowSpan_mono f (Nat.le_succ b) hw), ?_⟩
        rw [map_sub, hgw]; abel
    | zero => exact ⟨0, zero_mem _, map_zero g⟩
    | add x x' _ _ hx hx' =>
      obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨y', hy', rfl⟩ := hx'
      exact ⟨y + y', add_mem hy hy', map_add g y y'⟩
    | smul a x _ hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨a • y, Submodule.smul_mem _ a hy, map_smul g a y⟩

def triSub (f : Fin (r + 1) → V) : Subgroup (V ≃ₗ[E] V) where
  carrier := {g | IsTriW f g}
  one_mem' := by
    rw [Set.mem_setOf_eq]; intro b
    show f b - f b ∈ lowSpan E f b
    simp
  mul_mem' := by
    intro g g' hg hg'
    rw [Set.mem_setOf_eq] at hg hg' ⊢
    intro b
    show g (g' (f b)) - f b ∈ lowSpan E f b
    have : g (g' (f b)) - f b = g (g' (f b) - f b) + (g (f b) - f b) := by rw [map_sub]; abel
    rw [this]
    exact add_mem (map_lowSpan hg b _ (hg' b)) (hg b)
  inv_mem' := by
    intro g hg
    rw [Set.mem_setOf_eq] at hg ⊢
    intro b
    show g.symm (f b) - f b ∈ lowSpan E f b
    obtain ⟨y, hy, hgy⟩ := exists_pre_lowSpan hg b (f b - g (f b)) (by
      have := neg_mem (hg b)
      simpa using this)
    have : g.symm (f b) - f b = g.symm (f b - g (f b)) := by
      rw [map_sub, LinearEquiv.symm_apply_apply]
    rw [this, ← hgy, LinearEquiv.symm_apply_apply]
    exact hy

end Tri

theorem hf_add_left' {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] (L : Loc.LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (x x' y : Fin n → E) :
    hf L Hm (x + x') y = hf L Hm x y + hf L Hm x' y := by
  simp [hf, add_mul, Finset.sum_add_distrib]

theorem hf_smul_left' {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] (L : Loc.LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (a : E) (x y : Fin n → E) :
    hf L Hm (a • x) y = a * hf L Hm x y := by
  simp [hf, Finset.mul_sum, mul_assoc]

theorem hf_zero_left' {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] (L : Loc.LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (y : Fin n → E) :
    hf L Hm 0 y = 0 := by
  simp [hf]

section Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] {r : ℕ}

theorem nset_sub {H : Loc.HermSp M V} (Fr : LocNG.FrameD H r) :
    Fr.NSet ⊆ ((triSub (E := E) Fr.f : Subgroup (V ≃ₗ[E] V)) : Set (V ≃ₗ[E] V)) := by
  rintro g ⟨-, hF, hP⟩ b
  induction b using Fin.lastCases with
  | last =>
    have hz : Fr.f (Fin.last r) ∈ H.perp (H.X Fr.f) := by
      show ∀ x ∈ H.X Fr.f, H.h (Fr.f (Fin.last r)) x = 0
      intro x hx
      have h0 : H.h x (Fr.f (Fin.last r)) = 0 := by
        induction hx using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨a, rfl⟩ := hy
          exact Fr.h_iso _ _ (Or.inl (Fin.castSucc_lt_last a).ne)
        | zero => exact H.h_zero_left _
        | add x y _ _ hx hy => rw [H.h_add_left, hx, hy, add_zero]
        | smul a x _ hx => rw [H.h_smul_left, hx, mul_zero]
      rw [H.h_herm x, h0, map_zero]
    have h1 := hP _ hz
    have h2 : H.X Fr.f ≤ lowSpan E Fr.f (Fin.last r : ℕ) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨a, rfl⟩
      exact Submodule.subset_span ⟨a.castSucc, by simp, rfl⟩
    exact h2 h1
  | cast a =>
    have hv : Fr.f a.castSucc ∈ Fr.Fj (a.val + 1) := Submodule.subset_span ⟨a, by simp, rfl⟩
    have h1 := hF (a.val + 1) (by have := a.isLt; omega) _ hv
    simp only [Nat.add_sub_cancel] at h1
    have h2 : Fr.Fj a.val ≤ lowSpan E Fr.f (a.castSucc : ℕ) := by
      refine Submodule.span_mono ?_
      rintro _ ⟨a', ha', rfl⟩
      exact ⟨a'.castSucc, by simpa using ha', rfl⟩
    exact h2 h1

theorem mem_span_of_mem_N {H : Loc.HermSp M V} (Fr : LocNG.FrameD H r) {n : V ≃ₗ[E] V} (hn : n ∈ Fr.N)
    (b : Fin (r + 1)) : n (Fr.f b) ∈ Submodule.span E (Set.range Fr.f) := by
  have hT : IsTriW Fr.f n := (Subgroup.closure_le (triSub (E := E) Fr.f)).mpr (nset_sub Fr) hn
  have h1 : lowSpan E Fr.f b ≤ Submodule.span E (Set.range Fr.f) :=
    Submodule.span_mono (Set.image_subset_range _ _)
  have := add_mem (h1 (hT b)) (Submodule.subset_span ⟨b, rfl⟩ : Fr.f b ∈ Submodule.span E (Set.range Fr.f))
  simpa using this

theorem coef_eq {H : Loc.HermSp M V} (Fr : LocNG.FrameD H r) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (e : V ≃ₗ[E] (Fin n → E)) (g : Fin (r + 1) → Fin n → E) (gs : Fin r → Fin n → E)
    (hg : ∀ a, g a = e (Fr.f a)) (hd : ∀ a j, hf M.L Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)
    (j : Fin r) (x : V) (hx : x ∈ Submodule.span E (Set.range Fr.f)) :
    H.h x (Fr.es j) = hf M.L Hm (e x) (gs j) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    rw [← hg a, hd a j]
    induction a using Fin.lastCases with
    | last =>
      have h0 : H.h (Fr.f (Fin.last r)) (Fr.es j) = 0 := by
        rw [H.h_herm (Fr.es j) (Fr.f (Fin.last r)), Fr.h_sz j, map_zero]
      rw [h0, if_neg (Fin.castSucc_lt_last j).ne']
    | cast i =>
      rw [Fr.h_es i j]
      simp [Fin.castSucc_inj]
  | zero => rw [H.h_zero_left, map_zero, hf_zero_left']
  | add x y _ _ hx hy => rw [H.h_add_left, map_add, hf_add_left', hx, hy]
  | smul a x _ hx => rw [H.h_smul_left, map_smul, hf_smul_left', hx]

end Loc

theorem om_eq_psi_mul_inv : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E) {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (r k : ℕ) (P : LocNG.FPair H r) (S : Frames M.L r k) (c : WCoord P S) (d : LocNG.Datum P) (t : Loc.Term V M r), LocNG.IsTermOver P d t → ∀ m m' : S.GLV, (∀ b, c.e (t.f b) = m (S.f b)) → (∀ b, c.e (t.f' b) = m' (S.f' b)) → LocNG.om P t = S.psi m * (S.psi' m')⁻¹ := by
  intro F _ _ _ E _ _ _ _ M V _ _ H r k P S c d t hT m m' hm hm'
  obtain ⟨-, -, ⟨n, hn, hfn, -⟩, ⟨n', hn', hfn', -⟩, -⟩ := hT
  have hth : LocNG.theta M = S.th := by
    unfold LocNG.theta Frames.th
    cases hs : M.split with
    | none => simp [c.gg_none hs]
    | some g =>
      obtain ⟨h1, h2⟩ := c.gg_some g hs
      simp [h1, h2]
  have h1 : (∑ a : Fin r, H.h (t.f a.succ) (P.A.es a)) = ∑ j, S.h (m (S.f j.succ)) (S.es j) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hm]
    refine coef_eq P.A S.Hm c.e S.f S.es c.f_eq (fun a j => S.dual a j) j _ ?_
    rw [hfn]; exact mem_span_of_mem_N P.A hn _
  have h2 : (∑ a : Fin r, H.h (t.f' a.succ) (P.B.es a)) = ∑ j, S.h (m' (S.f' j.succ)) (S.es' j) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hm']
    refine coef_eq P.B S.Hm c.e S.f' S.es' c.f'_eq (fun a j => S.dual' a j) j _ ?_
    rw [hfn']; exact mem_span_of_mem_N P.B hn' _
  simp only [LocNG.om, LocNG.FrameD.psiOf, LocNG.FrameD.coefSum, Frames.psi, Frames.psi', Frames.psiOf,
    Frames.coef, hth, h1, h2]

end GlobalTheory.HL.TermPhase
