import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalIsometryExtendsLocalIsometry
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameAdaptedIsometryOfFixingBothFrames
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ActFrame
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RatIota
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PullGraph

section Abs

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {r : ℕ}

theorem mem_perp (H : HermSp M V) {S : Submodule E V} {v : V} : v ∈ H.perp S ↔ ∀ x ∈ S, H.h v x = 0 := Iff.rfl

theorem h_smul_right (H : HermSp M V) (c : E) (x y : V) : H.h x (c • y) = M.L.cj c * H.h x y := by
  rw [H.h_herm (c • y) x, H.h_smul_left, map_mul, ← H.h_herm]

theorem mem_smulLat (H : HermSp M V) (c : E) (Λ : Submodule M.L.O V) {x : V} :
    x ∈ H.smulLat c Λ ↔ ∃ v ∈ Λ, x = c • v := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨v, hv, rfl⟩ := hx; exact ⟨v, hv, rfl⟩
    | zero => exact ⟨0, Λ.zero_mem, (smul_zero c).symm⟩
    | add x y _ _ ihx ihy =>
      obtain ⟨v, hv, rfl⟩ := ihx
      obtain ⟨w, hw, rfl⟩ := ihy
      exact ⟨v + w, Λ.add_mem hv hw, (smul_add c v w).symm⟩
    | smul o x _ ih =>
      obtain ⟨v, hv, rfl⟩ := ih
      refine ⟨o • v, Λ.smul_mem o hv, ?_⟩
      show ((o : E)) • (c • v) = c • ((o : E) • v)
      rw [smul_smul, smul_smul, mul_comm]
  · rintro ⟨v, hv, rfl⟩
    exact Submodule.subset_span ⟨v, hv, rfl⟩

def Fam (H : HermSp M V) (Λ : Submodule M.L.O V) (f f' : Fin (r + 1) → V) (a b : V) : Prop :=
  ∃ y' ∈ Λ, ∃ y ∈ Λ, y' ∈ H.perp (H.X f') ∧ y ∈ H.perp (H.X f) ∧ y' - a ∈ H.X f' ∧ y - b ∈ H.X f ∧
    ∃ v ∈ Λ, y' - y = algebraMap F E (LocNG.theta M) • v

variable {H : HermSp M V} {Λ : Submodule M.L.O V} {f f' : Fin (r + 1) → V}

theorem fam_congr {a b a' b' : V} (h : Fam H Λ f f' a b) (ha : a - a' ∈ H.X f') (hb : b - b' ∈ H.X f) :
    Fam H Λ f f' a' b' := by
  obtain ⟨y', hy', y, hy, hP', hP, h1, h2, hv⟩ := h
  refine ⟨y', hy', y, hy, hP', hP, ?_, ?_, hv⟩
  · have e : y' - a' = (y' - a) + (a - a') := by abel
    rw [e]; exact add_mem h1 ha
  · have e : y - b' = (y - b) + (b - b') := by abel
    rw [e]; exact add_mem h2 hb

theorem fam_iff {a b : V} : Fam H Λ f f' a b ↔ ∃ x' ∈ Λ, ∃ x ∈ Λ, x' ∈ H.perp (H.X f') ∧ x ∈ H.perp (H.X f) ∧
    a - x' ∈ H.X f' ∧ b - x ∈ H.X f ∧ Fam H Λ f f' x' x := by
  constructor
  · intro h
    obtain ⟨y', hy', y, hy, hP', hP, h1, h2, hv⟩ := h
    refine ⟨y', hy', y, hy, hP', hP, ?_, ?_, y', hy', y, hy, hP', hP, by simp, by simp, hv⟩
    · have := neg_mem h1; simpa using this
    · have := neg_mem h2; simpa using this
  · rintro ⟨x', -, x, -, -, -, ha, hb, h⟩
    refine fam_congr h ?_ ?_
    · have := neg_mem ha; simpa using this
    · have := neg_mem hb; simpa using this

theorem fam_pt (iso : H.X f ≤ H.perp (H.X f)) (iso' : H.X f' ≤ H.perp (H.X f')) {x' x : V} (hx' : x' ∈ Λ) (hx : x ∈ Λ)
    (hP' : x' ∈ H.perp (H.X f')) (hP : x ∈ H.perp (H.X f)) :
    Fam H Λ f f' x' x ↔ Cong H Λ f f' (x - x') := by
  constructor
  · rintro ⟨y', hy', y, hy, -, -, h1, h2, v, hv, e⟩
    refine ⟨-(algebraMap F E (LocNG.theta M) • v), (mem_smulLat H _ Λ).2 ⟨-v, Λ.neg_mem hv, by rw [smul_neg]⟩,
      x - y, Λ.sub_mem hx hy, y' - x', Λ.sub_mem hy' hx', ?_, h1, ?_⟩
    · have := neg_mem h2; simpa using this
    · rw [← e]; abel
  · rintro ⟨s, hs, b₀, hb₀, c₀, hc₀, hb₀X, hc₀X, e⟩
    obtain ⟨w, hw, rfl⟩ := (mem_smulLat H _ Λ).1 hs
    refine ⟨x' + c₀, Λ.add_mem hx' hc₀, x - b₀, Λ.sub_mem hx hb₀, add_mem hP' (iso' hc₀X),
      sub_mem hP (iso hb₀X), by simpa using hc₀X, by simpa using neg_mem hb₀X, -w, Λ.neg_mem hw, ?_⟩
    have e2 : algebraMap F E (LocNG.theta M) • w = x - x' - b₀ - c₀ := by rw [e]; abel
    rw [smul_neg, e2]; abel

theorem famL_iff {f₀ f₁ : Fin (r + 1) → V} (gβ gn : V ≃ₗ[E] V)
    (hΛ : ∀ v, gβ v ∈ Λ ↔ v ∈ Λ)
    (hX : ∀ v, gβ v ∈ H.X f₁ ↔ v ∈ H.X f₀)
    (hP : ∀ v, gβ v ∈ H.perp (H.X f₁) ↔ v ∈ H.perp (H.X f₀))
    (hnX : ∀ z, gn z ∈ H.X f₀ ↔ z ∈ H.X f₁)
    (hm : ∀ x ∈ H.perp (H.X f₀), gn (gβ x) - x ∈ H.X f₀)
    (hnA : ∀ z, gn z ∈ H.X f ↔ z ∈ H.X f)
    (hnP : ∀ y ∈ H.perp (H.X f), gn y - y ∈ H.X f) {a b : V} :
    Fam H Λ f f₁ (gn.symm a) (gn.symm b) ↔ ∃ x' ∈ Λ, ∃ x ∈ Λ, x' ∈ H.perp (H.X f₀) ∧ x ∈ H.perp (H.X f) ∧
      a - x' ∈ H.X f₀ ∧ b - x ∈ H.X f ∧ Fam H Λ f f₁ (gβ x') x := by
  constructor
  · rintro ⟨y', hy', y, hy, hyP1, hyP, h1, h2, hv⟩
    have hx'Λ : gβ.symm y' ∈ Λ := (hΛ _).1 (by simpa using hy')
    have hx'P : gβ.symm y' ∈ H.perp (H.X f₀) := (hP _).1 (by simpa using hyP1)
    refine ⟨gβ.symm y', hx'Λ, y, hy, hx'P, hyP, ?_, ?_, ?_⟩
    · have k1 := (hnX _).2 h1
      rw [map_sub, LinearEquiv.apply_symm_apply] at k1
      have k2 := hm _ hx'P
      rw [LinearEquiv.apply_symm_apply] at k2
      have e : a - gβ.symm y' = (gn y' - gβ.symm y') - (gn y' - a) := by abel
      rw [e]; exact sub_mem k2 k1
    · have k1 := (hnA _).2 h2
      rw [map_sub, LinearEquiv.apply_symm_apply] at k1
      have k2 := hnP y hyP
      have e : b - y = (gn y - y) - (gn y - b) := by abel
      rw [e]; exact sub_mem k2 k1
    · rw [LinearEquiv.apply_symm_apply]
      exact ⟨y', hy', y, hy, hyP1, hyP, by simp, by simp, hv⟩
  · rintro ⟨x', hx', x, hx, hx'P, hxP, ha, hb, y', hy', y, hy, hyP1, hyP, h1, h2, hv⟩
    refine ⟨y', hy', y, hy, hyP1, hyP, ?_, ?_, hv⟩
    · rw [← hnX, map_sub, LinearEquiv.apply_symm_apply]
      have k1 := (hnX _).2 h1
      rw [map_sub] at k1
      have k2 := hm _ hx'P
      have e : gn y' - a = (gn y' - gn (gβ x')) + (gn (gβ x') - x') - (a - x') := by abel
      rw [e]; exact sub_mem (add_mem k1 k2) ha
    · rw [← hnA, map_sub, LinearEquiv.apply_symm_apply]
      have k2 := hnP y hyP
      have e : gn y - b = (gn y - y) + (y - x) - (b - x) := by abel
      rw [e]; exact sub_mem (add_mem k2 h2) hb

theorem main_abs {f₀ f₁ : Fin (r + 1) → V} (gβ gn : V ≃ₗ[E] V)
    (hΛ : ∀ v, gβ v ∈ Λ ↔ v ∈ Λ)
    (hX : ∀ v, gβ v ∈ H.X f₁ ↔ v ∈ H.X f₀)
    (hP : ∀ v, gβ v ∈ H.perp (H.X f₁) ↔ v ∈ H.perp (H.X f₀))
    (hnX : ∀ z, gn z ∈ H.X f₀ ↔ z ∈ H.X f₁)
    (hm : ∀ x ∈ H.perp (H.X f₀), gn (gβ x) - x ∈ H.X f₀)
    (hnA : ∀ z, gn z ∈ H.X f ↔ z ∈ H.X f)
    (hnP : ∀ y ∈ H.perp (H.X f), gn y - y ∈ H.X f)
    (isoA : H.X f ≤ H.perp (H.X f)) (iso0 : H.X f₀ ≤ H.perp (H.X f₀)) :
    (∀ a b, Fam H Λ f f₁ (gn.symm a) (gn.symm b) ↔ Fam H Λ f f₀ a b) ↔
      ∀ x' ∈ Λ, ∀ x ∈ Λ, x' ∈ H.perp (H.X f₀) → x ∈ H.perp (H.X f) →
        (Cong H Λ f f₀ (x - x') ↔ Cong H Λ f f₁ (x - gβ x')) := by
  have iso1 : H.X f₁ ≤ H.perp (H.X f₁) := by
    intro z hz
    have h1 : gβ.symm z ∈ H.X f₀ := (hX _).1 (by simpa using hz)
    have h2 := (hP _).2 (iso0 h1)
    simpa using h2
  have Lpt : ∀ x' ∈ Λ, ∀ x ∈ Λ, x' ∈ H.perp (H.X f₀) → x ∈ H.perp (H.X f) →
      (Fam H Λ f f₁ (gn.symm x') (gn.symm x) ↔ Fam H Λ f f₁ (gβ x') x) := by
    intro x' hx' x hx hx'P hxP
    rw [famL_iff gβ gn hΛ hX hP hnX hm hnA hnP]
    constructor
    · rintro ⟨x₁, -, x₂, -, -, -, h1, h2, h⟩
      refine fam_congr h ?_ ?_
      · rw [← map_sub]; refine (hX _).2 ?_
        have := neg_mem h1; simpa using this
      · have := neg_mem h2; simpa using this
    · intro h
      exact ⟨x', hx', x, hx, hx'P, hxP, by simp, by simp, h⟩
  constructor
  · intro h x' hx' x hx hx'P hxP
    rw [← fam_pt isoA iso0 hx' hx hx'P hxP, ← fam_pt isoA iso1 ((hΛ _).2 hx') hx ((hP _).2 hx'P) hxP,
      ← Lpt x' hx' x hx hx'P hxP, h]
  · intro h a b
    rw [famL_iff gβ gn hΛ hX hP hnX hm hnA hnP, fam_iff]
    constructor
    · rintro ⟨x', hx', x, hx, hx'P, hxP, ha, hb, k⟩
      refine ⟨x', hx', x, hx, hx'P, hxP, ha, hb, ?_⟩
      rw [fam_pt isoA iso1 ((hΛ _).2 hx') hx ((hP _).2 hx'P) hxP, ← h x' hx' x hx hx'P hxP] at k
      exact (fam_pt isoA iso0 hx' hx hx'P hxP).2 k
    · rintro ⟨x', hx', x, hx, hx'P, hxP, ha, hb, k⟩
      refine ⟨x', hx', x, hx, hx'P, hxP, ha, hb, ?_⟩
      rw [fam_pt isoA iso0 hx' hx hx'P hxP, h x' hx' x hx hx'P hxP] at k
      exact (fam_pt isoA iso1 ((hΛ _).2 hx') hx ((hP _).2 hx'P) hxP).2 k

end Abs

end GlobalTheory.PullGraph

namespace GlobalTheory.PullGraph

section Gen

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {r : ℕ} {H : HermSp M V}

theorem nu_keepX {f : Fin (r + 1) → V} {g : V ≃ₗ[E] V} (hg : g ∈ NU H f) {z : V} (hz : z ∈ H.X f) :
    g z ∈ H.X f := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a, rfl⟩ := hz
    have h1 := hg.2.1 a
    have h2 : Submodule.span E ((fun b : Fin r => f b.castSucc) '' {b | b < a}) ≤ H.X f :=
      Submodule.span_mono (Set.image_subset_range _ _)
    have e : g (f a.castSucc) = (g (f a.castSucc) - f a.castSucc) + f a.castSucc := by abel
    rw [e]; exact add_mem (h2 h1) (Submodule.subset_span ⟨a, rfl⟩)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem nu_X_iff {f : Fin (r + 1) → V} {g : V ≃ₗ[E] V} (hg : g ∈ NU H f) (hg' : g.symm ∈ NU H f) (z : V) :
    g z ∈ H.X f ↔ z ∈ H.X f :=
  ⟨fun h => by simpa using nu_keepX hg' h, nu_keepX hg⟩

theorem perp_iff_of_map {g : V ≃ₗ[E] V} (hu : IsUnitary H g) {S S' : Submodule E V} (hS : ∀ v, g v ∈ S' ↔ v ∈ S)
    (v : V) : g v ∈ H.perp S' ↔ v ∈ H.perp S := by
  rw [mem_perp, mem_perp]
  constructor
  · intro hv x hx
    rw [← hu]; exact hv _ ((hS x).2 hx)
  · intro hv y hy
    have := hv _ ((hS (g.symm y)).1 (by simpa using hy))
    rw [← hu v (g.symm y), LinearEquiv.apply_symm_apply] at this
    exact this

theorem X_iff_of_map {g : V ≃ₗ[E] V} {f f' : Fin (r + 1) → V} (h : ∀ a, g (f a) = f' a) (v : V) :
    g v ∈ H.X f' ↔ v ∈ H.X f := by
  have hm : (H.X f).map (g : V →ₗ[E] V) = H.X f' := by
    simp only [HermSp.X]
    rw [Submodule.map_span, ← Set.range_comp]
    congr 1
    ext x
    simp [h]
  rw [← hm, Submodule.mem_map_equiv]
  simp

theorem X_le_perp_of (f : Fin (r + 1) → V) (h0 : ∀ a b : Fin r, H.h (f a.castSucc) (f b.castSucc) = 0) :
    H.X f ≤ H.perp (H.X f) := by
  have s1 : ∀ x ∈ H.X f, ∀ b : Fin r, H.h x (f b.castSucc) = 0 := by
    intro x hx b
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨a, rfl⟩ := hx; exact h0 a b
    | zero => exact H.h_zero_left _
    | add x y _ _ hx hy => rw [H.h_add_left, hx, hy, add_zero]
    | smul c x _ hx => rw [H.h_smul_left, hx, mul_zero]
  intro y hy
  rw [mem_perp]
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨b, rfl⟩ := hx; exact s1 y hy b
  | zero => rw [H.h_herm 0 y, H.h_zero_left, map_zero]
  | add x x' _ _ hx hx' =>
    rw [H.h_herm (x + x') y, H.h_add_left, map_add, ← H.h_herm, ← H.h_herm, hx, hx', add_zero]
  | smul c x _ hx => rw [h_smul_right, hx, mul_zero]

end Gen

section Glob

variable {D : D7}

theorem scaled_iso (Z : LocDat D) (p : PlF D) {T : D.host.E} (F : LFlag (VS D) D.R.rS T) :
    (locH Z p).X (scaled Z p (frame F)) ≤ (locH Z p).perp ((locH Z p).X (scaled Z p (frame F))) := by
  refine X_le_perp_of _ fun a b => ?_
  simp only [scaled, GlobalTheory.LocExt.frame_castSucc]
  rw [(locH Z p).h_smul_left, h_smul_right]
  show _ * (_ * LocFacts₂ Z.M p _ _) = 0
  rw [baseChangeAt_form Z.M p (Z.hcj p)]
  simp [brS, F.fl.e_iso]

theorem ext_trans {p : PlF D} {a b : (VS D).V ≃ₗ[D.host.E] (VS D).V} {ga gb : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p}
    (ha : Ext p a ga) (hb : Ext p b gb) : Ext p (a * b) (gb.trans ga) := fun x => by
  show ga (gb (baseChange₂ D p x)) = baseChange₂ D p (a (b x))
  rw [hb, ha]

theorem ext_symm {p : PlF D} {a : (VS D).V ≃ₗ[D.host.E] (VS D).V} {g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p}
    (h : Ext p a g) : Ext p a⁻¹ g.symm := fun x => by
  rw [LinearEquiv.symm_apply_eq, h]
  show baseChange₂ D p x = baseChange₂ D p (a (a.symm x))
  rw [LinearEquiv.apply_symm_apply]

theorem nu_of_ext (Z : LocDat D) (p : PlF D) {T : D.host.E} {F : LFlag (VS D) D.R.rS T}
    {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} {g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p} (hN : γ ∈ NRat F) (h : Ext p γ g) :
    g ∈ NU (locH Z p) (scaled Z p (frame F)) := by
  rw [GlobalTheory.LocExt.locEquiv_unique p γ g h]
  exact GlobalTheory.LocExt.locEquiv_NU Z p γ F hN

end Glob

end GlobalTheory.PullGraph

namespace GlobalTheory.PullGraph

variable {D : D7}

theorem pulled_iff_local (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (Z : LocDat D) (t₀ t : TauC Y u u')
    (n m : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hl : t.lam = t₀.lam) (hl' : t.lam' = t₀.lam')
    (hn : n ∈ NRat (lf D (X.Fu u))) (hm : m ∈ NRat (lf D (X.Fu u'))) (ht : t.lin = n⁻¹ * t₀.lin * m)
    (p : PlF D) (gn : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (hgn : Ext p n gn) :
    (∀ a b, Fam (locH Z p) (lattice₂ D Z.M p t₀.lam) (scaled Z p (frame (lf D (X.Fu u)))) (scaled Z p (frame t.frame))
        (gn.symm a) (gn.symm b) ↔
      Fam (locH Z p) (lattice₂ D Z.M p t₀.lam) (scaled Z p (frame (lf D (X.Fu u)))) (scaled Z p (frame t₀.frame)) a b) ↔
    (∀ gβ, Ext p (t.lin * t₀.lin⁻¹) gβ → ∀ x' ∈ lattice₂ D Z.M p t₀.lam, ∀ x ∈ lattice₂ D Z.M p t₀.lam,
      x' ∈ (locH Z p).perp ((locH Z p).X (scaled Z p (frame t₀.frame))) →
      x ∈ (locH Z p).perp ((locH Z p).X (scaled Z p (frame (lf D (X.Fu u))))) →
      (Cong (locH Z p) (lattice₂ D Z.M p t₀.lam) (scaled Z p (frame (lf D (X.Fu u)))) (scaled Z p (frame t₀.frame)) (x - x') ↔
        Cong (locH Z p) (lattice₂ D Z.M p t₀.lam) (scaled Z p (frame (lf D (X.Fu u)))) (scaled Z p (frame t.frame))
          (x - gβ x'))) := by
  have hi0 : t₀.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t₀.rep.2.2.1
  have hi1 : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  have hβ : t.lin * t₀.lin⁻¹ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT :=
    (Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem hi1 ((Formalism.HermitianLatticesTheory.isom (VS D).hT).inv_mem hi0)
  have hβΛ : Formalism.HermitianLatticesTheory.gmap (t.lin * t₀.lin⁻¹) t₀.lam = t₀.lam := by
    have hg0 : Formalism.HermitianLatticesTheory.gmap t₀.lin t₀.lam' = t₀.lam := t₀.rep.2.2.2.1
    have hg1 : Formalism.HermitianLatticesTheory.gmap t.lin t.lam' = t.lam := t.rep.2.2.2.1
    calc Formalism.HermitianLatticesTheory.gmap (t.lin * t₀.lin⁻¹) t₀.lam
        = Formalism.HermitianLatticesTheory.gmap t.lin (Formalism.HermitianLatticesTheory.gmap t₀.lin⁻¹ (Formalism.HermitianLatticesTheory.gmap t₀.lin t₀.lam')) := by
          rw [Formalism.L2.SG.Pf.gmap_mul_sat, hg0]
      _ = t₀.lam := by rw [Formalism.L2.SG.Pf.gmap_inv_gmap, ← hl', hg1, hl]
  have hfr : ∀ a, (t.lin * t₀.lin⁻¹) (frame t₀.frame a) = frame t.frame a := by
    intro a
    show (t.lin * t₀.lin⁻¹) (frame (mapLF t₀.lin (lf D (X.Fu u'))) a) = frame (mapLF t.lin (lf D (X.Fu u'))) a
    rw [Formalism.L2.SG.Pf.Act.frame_mapLF hi0, Formalism.L2.SG.Pf.Act.frame_mapLF hi1]
    show t.lin (t₀.lin.symm (t₀.lin _)) = _
    rw [LinearEquiv.symm_apply_apply]
  have hm0 : n * (t.lin * t₀.lin⁻¹) ∈ NRat t₀.frame := by
    have e : n * (t.lin * t₀.lin⁻¹) = t₀.lin * m * t₀.lin⁻¹ := by rw [ht]; group
    rw [e]
    exact GlobalTheory.StabCnt.nrat_conj (GlobalTheory.StabCnt.adapt_mapLF hi0) hm
  have hgβ : Ext p (t.lin * t₀.lin⁻¹) (GlobalTheory.LocExt.locEquiv p (t.lin * t₀.lin⁻¹)) := GlobalTheory.LocExt.locEquiv_ext p _
  have huβ := GlobalTheory.LocExt.locEquiv_unitary Z p _ hβ
  have hgf : ∀ a, GlobalTheory.LocExt.locEquiv p (t.lin * t₀.lin⁻¹) (scaled Z p (frame t₀.frame) a) =
      scaled Z p (frame t.frame) a := by
    intro a
    simp only [scaled, map_smul, hgβ _, hfr]
  have hXβ := X_iff_of_map (H := locH Z p) hgf
  have hPβ := perp_iff_of_map huβ hXβ
  have hΛ : ∀ v, GlobalTheory.LocExt.locEquiv p (t.lin * t₀.lin⁻¹) v ∈ lattice₂ D Z.M p t₀.lam ↔ v ∈ lattice₂ D Z.M p t₀.lam := by
    have himg := GlobalTheory.LocExt.locEquiv_img Z p (t.lin * t₀.lin⁻¹) t₀.lam
    rw [hβΛ] at himg
    intro v
    constructor
    · intro hv
      rw [← himg] at hv
      obtain ⟨w, hw, e⟩ := Submodule.mem_map.1 hv
      have : w = v := (GlobalTheory.LocExt.locEquiv p (t.lin * t₀.lin⁻¹)).injective e
      rwa [← this]
    · intro hv
      rw [← himg]
      exact Submodule.mem_map_of_mem hv
  have hg0 := ext_trans hgn hgβ
  have hNU0 := nu_of_ext Z p hm0 hg0
  have hNU0' := nu_of_ext Z p (GlobalTheory.StabCnt.nrat_inv hm0) (ext_symm hg0)
  have hnN := nu_of_ext Z p hn hgn
  have hnN' := nu_of_ext Z p (GlobalTheory.StabCnt.nrat_inv hn) (ext_symm hgn)
  have hnX : ∀ z, gn z ∈ (locH Z p).X (scaled Z p (frame t₀.frame)) ↔ z ∈ (locH Z p).X (scaled Z p (frame t.frame)) := by
    intro z
    have e : gn z = ((GlobalTheory.LocExt.locEquiv p (t.lin * t₀.lin⁻¹)).trans gn)
        ((GlobalTheory.LocExt.locEquiv p (t.lin * t₀.lin⁻¹)).symm z) := by simp
    rw [e, nu_X_iff hNU0 hNU0', ← hXβ, LinearEquiv.apply_symm_apply]
  have hmm : ∀ x ∈ (locH Z p).perp ((locH Z p).X (scaled Z p (frame t₀.frame))),
      gn (GlobalTheory.LocExt.locEquiv p (t.lin * t₀.lin⁻¹) x) - x ∈ (locH Z p).X (scaled Z p (frame t₀.frame)) :=
    fun x hx => hNU0.2.2 x hx
  have key := main_abs (GlobalTheory.LocExt.locEquiv p (t.lin * t₀.lin⁻¹)) gn hΛ hXβ hPβ hnX hmm (nu_X_iff hnN hnN') hnN.2.2
    (scaled_iso Z p _) (scaled_iso Z p _)
  constructor
  · intro h gβ hgβ'
    rw [GlobalTheory.LocExt.locEquiv_unique p _ gβ hgβ']
    exact key.1 h
  · intro h
    exact key.2 (h _ hgβ)

theorem pulled_graph_iff : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (t₀ t : TauC Y u u') (n m : (VS D).V ≃ₗ[D.host.E] (VS D).V), t.lam = t₀.lam → t.lam' = t₀.lam' → n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m → ∀ (p : PlF D) (gn : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p), Ext p n gn → ((∀ a b : Vp D p, (∃ y' ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam, ∃ y ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam, y' ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).perp ((locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame t.frame))) ∧ y ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).perp ((locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame (lf D (X.Fu u))))) ∧ y' - gn.symm a ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame t.frame)) ∧ y - gn.symm b ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame (lf D (X.Fu u)))) ∧ ∃ v ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam, y' - y = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (LocNG.theta ((⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p)) • v) ↔ (∃ y' ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam, ∃ y ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam, y' ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).perp ((locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame t₀.frame))) ∧ y ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).perp ((locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame (lf D (X.Fu u))))) ∧ y' - a ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame t₀.frame)) ∧ y - b ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame (lf D (X.Fu u)))) ∧ ∃ v ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam, y' - y = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (LocNG.theta ((⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p)) • v)) ↔ (∀ gβ, Ext p (t.lin * t₀.lin⁻¹) gβ → ∀ x' ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam, ∀ x ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam, x' ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).perp ((locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame t₀.frame))) → x ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).perp ((locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame (lf D (X.Fu u))))) → (Cong (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) (lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam) (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame (lf D (X.Fu u)))) (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame t₀.frame)) (x - x') ↔ Cong (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) (lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam) (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame (lf D (X.Fu u)))) (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame t.frame)) (x - gβ x')))) := by
  intro D X Y u u' t₀ t n m hl hl' hnm p gn hgn
  exact pulled_iff_local X Y u u' _ t₀ t n m hl hl' hnm.1 hnm.2.1 hnm.2.2 p gn hgn

end GlobalTheory.PullGraph
