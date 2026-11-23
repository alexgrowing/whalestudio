import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL.NmlCoset

variable {D : D7} {T : D.host.E} (F : LFlag (VS D) D.R.rS T)

theorem mem_orth_iff (U : Submodule D.host.E (VS D).V) (y : (VS D).V) :
    y ∈ orth (VS D) U ↔ ∀ x ∈ U, (VS D).hT x y = 0 := by
  unfold orth
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]

theorem X_iso : ∀ x ∈ Xsp F, ∀ y ∈ Xsp F, (VS D).hT x y = 0 := by
  intro x hx y hy
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨b, rfl⟩ := hy; exact F.fl.e_iso a b
    | zero => simp
    | add y y' _ _ h1 h2 => simp [map_add, h1, h2]
    | smul c y _ h => simp [map_smul, h]
  | zero => simp
  | add x x' _ _ h1 h2 => simp [map_add, h1, h2]
  | smul c x _ h => simp [h]

theorem X_le_orth : Xsp F ≤ orth (VS D) (Xsp F) := by
  intro y hy
  rw [mem_orth_iff]
  intro x hx
  exact X_iso F x hx y hy

theorem Xa_mono (j : ℕ) : Xflag F j ≤ Xflag F (j + 1) := by
  apply Submodule.span_mono
  apply Set.image_mono
  intro i hi
  simp only [Set.mem_setOf_eq] at hi ⊢
  omega

instance Xa_fd (j : ℕ) : FiniteDimensional D.host.E (Xflag F j) :=
  FiniteDimensional.span_of_finite _ (Set.Finite.image _ (Set.toFinite _))

theorem maps_Xa {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ NRat F) (j : ℕ) :
    ∀ x ∈ Xflag F (j + 1), n x ∈ Xflag F (j + 1) := by
  intro x hx
  have h := hn.2.1 j x hx
  have : n x = (n x - x) + x := by abel
  rw [this]
  exact (Xflag F (j + 1)).add_mem (Xa_mono F j h) hx

theorem maps_X {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ NRat F) :
    ∀ x ∈ Xsp F, n x ∈ Xsp F := by
  intro x hx
  have h := hn.2.2 x (X_le_orth F hx)
  have : n x = (n x - x) + x := by abel
  rw [this]
  exact (Xsp F).add_mem h hx

theorem maps_orth {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ NRat F) :
    ∀ x ∈ orth (VS D) (Xsp F), n x ∈ orth (VS D) (Xsp F) := by
  intro x hx
  have h := hn.2.2 x hx
  have : n x = (n x - x) + x := by abel
  rw [this]
  exact (orth (VS D) (Xsp F)).add_mem (X_le_orth F h) hx

theorem symm_mem_Xa {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ NRat F) (j : ℕ) :
    ∀ x ∈ Xflag F (j + 1), n.symm x ∈ Xflag F (j + 1) := by
  intro x hx
  have hle : (Xflag F (j + 1)).map (n : (VS D).V →ₗ[D.host.E] (VS D).V) ≤ Xflag F (j + 1) := by
    rintro _ ⟨y, hy, rfl⟩
    exact maps_Xa F hn j y hy
  have heq := Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq n _)
  rw [← heq] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  have : n.symm x = y := by rw [← hyx]; simp
  rw [this]; exact hy

theorem one_mem : (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ NRat F := by
  refine ⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).one_mem, ?_, ?_⟩
  · intro j x _; simp
  · intro x _; simp

theorem mul_mem {n m : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ NRat F) (hm : m ∈ NRat F) :
    n * m ∈ NRat F := by
  refine ⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem hn.1 hm.1, ?_, ?_⟩
  · intro j x hx
    show n (m x) - x ∈ Xflag F j
    have e : n (m x) - x = (n (m x) - m x) + (m x - x) := by abel
    rw [e]
    exact (Xflag F j).add_mem (hn.2.1 j (m x) (maps_Xa F hm j x hx)) (hm.2.1 j x hx)
  · intro x hx
    show n (m x) - x ∈ Xsp F
    have e : n (m x) - x = (n (m x) - m x) + (m x - x) := by abel
    rw [e]
    exact (Xsp F).add_mem (hn.2.2 (m x) (maps_orth F hm x hx)) (hm.2.2 x hx)

theorem inv_mem {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ NRat F) : n⁻¹ ∈ NRat F := by
  refine ⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).inv_mem hn.1, ?_, ?_⟩
  · intro j x hx
    show n.symm x - x ∈ Xflag F j
    have hy := symm_mem_Xa F hn j x hx
    have h := hn.2.1 j (n.symm x) hy
    rw [LinearEquiv.apply_symm_apply] at h
    have e : n.symm x - x = -(x - n.symm x) := by abel
    rw [e]; exact (Xflag F j).neg_mem h
  · intro x hx
    show n.symm x - x ∈ Xsp F
    have hy : n.symm x ∈ orth (VS D) (Xsp F) := by
      rw [mem_orth_iff] at hx ⊢
      intro v hv
      have hi := hn.1 v (n.symm x)
      rw [LinearEquiv.apply_symm_apply] at hi
      rw [← hi]
      exact hx _ (maps_X F hn v hv)
    have h := hn.2.2 (n.symm x) hy
    rw [LinearEquiv.apply_symm_apply] at h
    have e : n.symm x - x = -(x - n.symm x) := by abel
    rw [e]; exact (Xsp F).neg_mem h

end GlobalTheory.HL.NmlCoset

namespace GlobalTheory.HL

open GlobalTheory.HL.NmlCoset in

theorem nmlOf_eq_iff_lin : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    Formalism.MainNotions.S.Cnt.Stand D u u' → ∀ t₀ t : TauC Y u u', nmlOf Y u u' t = nmlOf Y u u' t₀ ↔
      ∃ n m : ((VS D).V ≃ₗ[D.host.E] (VS D).V), n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧
        t.lin = n⁻¹ * t₀.lin * m := by
  intro D X Y u u' _ t₀ t
  constructor
  · intro h
    have ht : t.lin ∈ nmlOf Y u u' t := ⟨1, one_mem _, 1, one_mem _, by simp⟩
    rw [h] at ht
    obtain ⟨n, hn, n', hn', e⟩ := ht
    exact ⟨n⁻¹, n', inv_mem _ hn, hn', by simpa using e⟩
  · rintro ⟨n, m, hn, hm, e⟩
    ext δ
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      refine ⟨a * n⁻¹, mul_mem _ ha (inv_mem _ hn), m * b, mul_mem _ hm hb, ?_⟩
      rw [e]; simp only [mul_assoc]
    · rintro ⟨a, ha, b, hb, rfl⟩
      refine ⟨a * n, mul_mem _ ha hn, m⁻¹ * b, mul_mem _ (inv_mem _ hm) hb, ?_⟩
      rw [e]; group

end GlobalTheory.HL
