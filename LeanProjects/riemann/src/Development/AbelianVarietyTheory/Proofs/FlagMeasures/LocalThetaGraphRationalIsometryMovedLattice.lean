import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalIsometryExtendsLocalIsometry
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GraphTr

theorem span_tri_le {K W : Type*} [Semiring K] [AddCommMonoid W] [Module K W] {n r : ℕ}
    (f g : Fin n → W) (A : Matrix (Fin n) (Fin n) K) (hA : ∀ a b, b < a → A a b = 0)
    (hg : ∀ b, g b = ∑ a, A a b • f a) :
    Submodule.span K (g '' {i | (i : ℕ) < r}) ≤ Submodule.span K (f '' {i | (i : ℕ) < r}) := by
  rw [Submodule.span_le]
  rintro _ ⟨b, hb, rfl⟩
  rw [hg b]
  refine Submodule.sum_mem _ fun a _ => ?_
  by_cases hab : b < a
  · rw [hA a b hab, zero_smul]; exact Submodule.zero_mem _
  · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, ?_, rfl⟩)
    show (a : ℕ) < r
    exact lt_of_le_of_lt (Fin.le_iff_val_le_val.1 (not_lt.1 hab)) hb

theorem inv_rel {K W : Type*} [CommRing K] [AddCommGroup W] [Module K W] {n : ℕ}
    (f g : Fin n → W) (A : Matrix (Fin n) (Fin n) K) (hA : IsUnit A.det)
    (hg : ∀ b, g b = ∑ a, A a b • f a) : ∀ b, f b = ∑ a, A⁻¹ a b • g a := by
  intro b
  simp_rw [hg, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  have h : ∀ c, ∑ a, A⁻¹ a b * A c a = (A * A⁻¹) c b := fun c => by
    rw [Matrix.mul_apply]; exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  simp_rw [h, Matrix.mul_nonsing_inv _ hA, Matrix.one_apply, ite_smul, one_smul, zero_smul]
  simp

theorem range_castSucc {W : Type*} {r : ℕ} (f : Fin (r + 1) → W) :
    Set.range (fun a : Fin r => f a.castSucc) = f '' {i | (i : ℕ) < r} := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩; exact ⟨a.castSucc, by simp, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨⟨i, hi⟩, congrArg f (Fin.ext rfl)⟩

theorem span_units {K W ι : Type*} [CommRing K] [AddCommGroup W] [Module K W] (u : ι → K)
    (hu : ∀ a, IsUnit (u a)) (v : ι → W) (S : Set ι) :
    Submodule.span K ((fun a => u a • v a) '' S) = Submodule.span K (v '' S) := by
  apply le_antisymm
  · rw [Submodule.span_le]; rintro _ ⟨a, ha, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, ha, rfl⟩)
  · rw [Submodule.span_le]; rintro _ ⟨a, ha, rfl⟩
    obtain ⟨w, hw⟩ := hu a
    have h : u a • v a ∈ Submodule.span K ((fun a => u a • v a) '' S) := Submodule.subset_span ⟨a, ha, rfl⟩
    have h2 := Submodule.smul_mem _ ((w⁻¹ : Kˣ) : K) h
    rwa [smul_smul, ← hw, Units.inv_mul, one_smul] at h2

end GlobalTheory.GraphTr

namespace GlobalTheory.GraphTr

variable {D : D7}

theorem frFac_isUnit (Z : LocDat D) (p : PlF D) (a : Fin (D.R.rS + 1)) : IsUnit (frFac Z.δ p a) := by
  unfold frFac
  have hδ : IsUnit (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p)) :=
    (Ne.isUnit (Z.agree p).2.1).map _
  have hg : ∀ i, D.host.g i ≠ 0 := fun i => (D.host.g_prime i).ne_zero
  have hgp : gpart p ≠ 0 := by
    unfold gpart; split_ifs <;> simp [hg]
  have hgS : (Formalism.MainNotions.S.Lat.gS D : ℚ) ≠ 0 := by
    unfold Formalism.MainNotions.S.Lat.gS; push_cast
    exact mul_ne_zero (by exact_mod_cast hg 0) (by exact_mod_cast hg 1)
  have hu : ((uP p : ℚ) : D.host.E) ≠ 0 := by
    rw [Rat.cast_ne_zero]; unfold uP; exact div_ne_zero (by exact_mod_cast hgp) hgS
  have hι : IsUnit ((D.s.atP p).ιE ((uP p : ℚ) : D.host.E)) := (Ne.isUnit hu).map _
  obtain ⟨w, hw⟩ := (hδ.mul hι).pow (D.R.rS - a.val)
  rw [← hw, Ring.inverse_unit]
  exact Units.isUnit _

theorem span_bc (p : PlF D) (s : Set (VS D).V) :
    Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (Submodule.span D.host.E s : Set (VS D).V)) =
      Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' s) := by
  apply le_antisymm
  · rw [Submodule.span_le]; rintro _ ⟨x, hx, rfl⟩; exact GlobalTheory.LocExt.baseChange_mem_span p hx
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

theorem X_eq (Z : LocDat D) (p : PlF D) (f : Fin (D.R.rS + 1) → (VS D).V) :
    (locH Z p).X (scaled Z p f) = Submodule.span (D.s.atP p).Ep
      (baseChange₂ D p '' (Submodule.span D.host.E (f '' {i | (i : ℕ) < D.R.rS}) : Set (VS D).V)) := by
  rw [span_bc, Set.image_image]
  unfold Formalism.MainNotions.S.Loc.HermSp.X
  rw [range_castSucc]
  exact span_units (fun a => frFac Z.δ p a) (frFac_isUnit Z p) (fun a => baseChange₂ D p (f a)) _

theorem rat_span_eq (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (f f0 : Fin (D.R.rS + 1) → (VS D).V)
    (U : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) (hU : IsUpUni U)
    (hσ : ∀ b, σ (f b) = ∑ a, U a b • f0 a) (r : ℕ) :
    (Submodule.span D.host.E (f '' {i | (i : ℕ) < r})).map (σ : (VS D).V →ₗ[D.host.E] (VS D).V) =
      Submodule.span D.host.E (f0 '' {i | (i : ℕ) < r}) := by
  rw [Submodule.map_span, Set.image_image]
  have hA : ∀ a b, b < a → U a b = 0 := fun a b h => (hU a b).1 h
  have hd : ∀ i, U i i = 1 := fun i => (hU i i).2 rfl
  have hdet : IsUnit U.det := by
    rw [Matrix.det_of_upperTriangular (by intro i j h; exact (hU i j).1 h)]
    simp [hd]
  apply le_antisymm
  · exact span_tri_le f0 (fun b => σ (f b)) U hA hσ
  · exact span_tri_le (fun b => σ (f b)) f0 U⁻¹ (inv_unitri U hA hd).1
      (inv_rel f0 (fun b => σ (f b)) U hdet hσ)

theorem map_X (Z : LocDat D) (p : PlF D) (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (gσ : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (hE : Ext p σ gσ) (f f0 : Fin (D.R.rS + 1) → (VS D).V)
    (U : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) (hU : IsUpUni U)
    (hσ : ∀ b, σ (f b) = ∑ a, U a b • f0 a) :
    ((locH Z p).X (scaled Z p f)).map (gσ : Vp D p →ₗ[(D.s.atP p).Ep] Vp D p) =
      (locH Z p).X (scaled Z p f0) := by
  rw [X_eq, X_eq, Submodule.map_span, Set.image_image, ← rat_span_eq σ f f0 U hU hσ, Submodule.map_coe,
    Set.image_image]
  congr 1
  apply Set.image_congr
  intro x _
  exact hE x

end GlobalTheory.GraphTr

namespace GlobalTheory.GraphTr

variable {D : D7}

section Coord

variable {Z : LocDat D} {T T' : D.host.E} {F0 : LFlag (VS D) D.R.rS T} {F0' : LFlag (VS D) D.R.rS T'}
  {FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS} {G : GFrames (placesOf Z) D.R.rS D.R.k}

theorem framesX (c : GCoord Z F0 F0' FP G) (p : PlF D) (hA : (FP p).A.f = scaled Z p (frame F0)) :
    (G.S p).X = ((locH Z p).X (scaled Z p (frame F0))).map
      (c.c p).e.toLinearMap := by
  unfold Frames.X Frames.spanTo Formalism.MainNotions.S.Loc.HermSp.X
  rw [range_castSucc, Submodule.map_span, Set.image_image]
  congr 1
  apply Set.image_congr
  intro a _
  rw [(c.c p).f_eq a, hA]
  rfl

theorem framesX' (c : GCoord Z F0 F0' FP G) (p : PlF D) (hB : (FP p).B.f = scaled Z p (frame F0')) :
    (G.S p).X' = ((locH Z p).X (scaled Z p (frame F0'))).map
      (c.c p).e.toLinearMap := by
  unfold Frames.X' Frames.spanTo Formalism.MainNotions.S.Loc.HermSp.X
  rw [range_castSucc, Submodule.map_span, Set.image_image]
  congr 1
  apply Set.image_congr
  intro a _
  rw [(c.c p).f'_eq a, hB]
  rfl

theorem lat_eq (c : GCoord Z F0 F0' FP G) (p : PlF D) (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (gσ : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (hE : Ext p σ gσ) (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    (placesOf Z).lat p (c.lat σ Λ) = (c.c p).lat (LocNG.img (M := Z.M p) gσ (lattice₂ D Z.M p Λ)) := by
  have hs : (placesOf Z).bc p '' ((c.lat σ Λ : Submodule (𝓞 D.host.E) G.V) : Set G.V) =
      ((fun y => (c.c p).e (gσ (baseChange₂ D p y))) '' (Λ : Set (VS D).V)) := by
    ext z
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      refine ⟨y, hy, ?_⟩
      show (c.c p).e (gσ (baseChange₂ D p y)) = (placesOf Z).bc p (c.e (σ y))
      rw [hE y]; exact c.compat p (σ y)
    · rintro ⟨y, hy, rfl⟩
      refine ⟨c.e (σ y), ⟨y, hy, rfl⟩, ?_⟩
      show (placesOf Z).bc p (c.e (σ y)) = (c.c p).e (gσ (baseChange₂ D p y))
      rw [hE y]; exact (c.compat p (σ y)).symm
  unfold WCoord.lat LocNG.img lattice₂ Places.lat
  rw [Submodule.map_span, Submodule.map_span, Set.image_image, Set.image_image, hs]
  rfl

theorem th_eq (c : GCoord Z F0 F0' FP G) (p : PlF D) : (G.S p).th = LocNG.theta (Z.M p) := by
  unfold Frames.th LocNG.theta
  rcases h : (Z.M p).split with _ | g
  · simp [(c.c p).gg_none h]; rfl
  · obtain ⟨h1, h2⟩ := (c.c p).gg_some g h
    simp [h1, h2]

end Coord

end GlobalTheory.GraphTr

namespace GlobalTheory.GraphTr

section Gen

open Formalism.MainNotions.S.Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}
  {P : LocNG.FPair H r} {S : Frames M.L r k}

theorem mem_map_eg (c : WCoord P S) (g : V ≃ₗ[E] V) (W : Submodule E V) (y : V) :
    c.e (g y) ∈ (W.map (g : V →ₗ[E] V)).map (c.e : V →ₗ[E] S.V) ↔ y ∈ W := by
  constructor
  · rintro ⟨x, ⟨z, hz, rfl⟩, hx⟩
    have : z = y := g.injective (c.e.injective hx)
    exact this ▸ hz
  · intro hy; exact ⟨g y, ⟨y, hy, rfl⟩, rfl⟩

theorem mem_lat_eg (c : WCoord P S) (g : V ≃ₗ[E] V) (Λ0 : Submodule M.L.O V) (y : V) :
    c.e (g y) ∈ c.lat (LocNG.img g Λ0) ↔ y ∈ Λ0 := by
  constructor
  · rintro ⟨x, ⟨z, hz, rfl⟩, hx⟩
    have : z = y := g.injective (c.e.injective hx)
    exact this ▸ hz
  · intro hy; exact ⟨g y, ⟨y, hy, rfl⟩, rfl⟩

theorem h_eg (c : WCoord P S) (g : V ≃ₗ[E] V) (hg : LocNG.IsUnitary H g) (x y : V) :
    hf M.L S.Hm (c.e (g x)) (c.e (g y)) = H.h x y := by
  have h := c.h_eq (g x) (g y)
  rw [hg] at h
  exact h

theorem mem_perp_eg (c : WCoord P S) (g : V ≃ₗ[E] V) (hg : LocNG.IsUnitary H g) (W : Submodule E V) (y : V) :
    c.e (g y) ∈ perp M.L S.Hm ((W.map (g : V →ₗ[E] V)).map (c.e : V →ₗ[E] S.V)) ↔ y ∈ H.perp W := by
  constructor
  · intro h x hx
    have h1 := h (c.e (g x)) ⟨g x, ⟨x, hx, rfl⟩, rfl⟩
    rwa [h_eg c g hg] at h1
  · rintro h _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    show hf M.L S.Hm (c.e (g y)) (c.e (g x)) = 0
    rw [h_eg c g hg]
    exact h x hx

theorem graphOf_coord (c : WCoord P S) (g : V ≃ₗ[E] V) (hg : LocNG.IsUnitary H g) (Λ0 : Submodule M.L.O V)
    (X1 X2 : Submodule E V) (hX1 : S.X = (X1.map (g : V →ₗ[E] V)).map (c.e : V →ₗ[E] S.V))
    (hX2 : S.X' = (X2.map (g : V →ₗ[E] V)).map (c.e : V →ₗ[E] S.V)) (θ : F) (hθ : S.th = θ)
    (q : S.V × S.V) :
    q ∈ S.graphOf (c.lat (LocNG.img g Λ0)) ↔ ∃ y' ∈ Λ0, ∃ y ∈ Λ0, y' ∈ H.perp X2 ∧ y ∈ H.perp X1 ∧
      y' - g.symm (c.e.symm q.1) ∈ X2 ∧ y - g.symm (c.e.symm q.2) ∈ X1 ∧
      ∃ v ∈ Λ0, y' - y = algebraMap F E θ • v := by
  have hs : ∀ Y : S.V, Y = c.e (g (g.symm (c.e.symm Y))) := fun Y => by simp
  have hsub : ∀ (y : V) (Y : S.V), c.e (g y) - Y = c.e (g (y - g.symm (c.e.symm Y))) := fun y Y => by
    rw [map_sub, map_sub, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  constructor
  · rintro ⟨Y', hY', Y, hY, h1, h2, h3, h4, w, hw, h5⟩
    obtain ⟨y', rfl⟩ : ∃ y', Y' = c.e (g y') := ⟨_, hs Y'⟩
    obtain ⟨y, rfl⟩ : ∃ y, Y = c.e (g y) := ⟨_, hs Y⟩
    obtain ⟨v, rfl⟩ : ∃ v, w = c.e (g v) := ⟨_, hs w⟩
    refine ⟨y', (mem_lat_eg c g Λ0 y').1 hY', y, (mem_lat_eg c g Λ0 y).1 hY, ?_, ?_, ?_, ?_, v,
      (mem_lat_eg c g Λ0 v).1 hw, ?_⟩
    · rw [hX2] at h1; exact (mem_perp_eg c g hg X2 y').1 h1
    · rw [hX1] at h2; exact (mem_perp_eg c g hg X1 y).1 h2
    · rw [hX2, hsub] at h3; exact (mem_map_eg c g X2 _).1 h3
    · rw [hX1, hsub] at h4; exact (mem_map_eg c g X1 _).1 h4
    · rw [hθ, ← map_sub, ← map_sub, ← map_smul, ← map_smul] at h5
      exact g.injective (c.e.injective h5)
  · rintro ⟨y', hy', y, hy, h1, h2, h3, h4, v, hv, h5⟩
    refine ⟨c.e (g y'), (mem_lat_eg c g Λ0 y').2 hy', c.e (g y), (mem_lat_eg c g Λ0 y).2 hy, ?_, ?_, ?_, ?_,
      c.e (g v), (mem_lat_eg c g Λ0 v).2 hv, ?_⟩
    · rw [hX2]; exact (mem_perp_eg c g hg X2 y').2 h1
    · rw [hX1]; exact (mem_perp_eg c g hg X1 y).2 h2
    · rw [hX2, hsub]; exact (mem_map_eg c g X2 _).2 h3
    · rw [hX1, hsub]; exact (mem_map_eg c g X1 _).2 h4
    · rw [hθ, ← map_sub, ← map_sub, h5, map_smul, map_smul]

end Gen

end GlobalTheory.GraphTr

theorem GlobalTheory.HL.graph_moved_local : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (p : PlF D) (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (gσ : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (F₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (U₁ U₂ : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) F₂ σ U₁ U₂ → Ext p σ gσ → ∀ (Λ : Submodule (𝓞 D.host.E) (VS D).V) (q : (G.S p).V × (G.S p).V), (q ∈ (G.datOf (c.lat σ Λ) p).2.2 ↔ ∃ y' ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p Λ, ∃ y ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p Λ, y' ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).perp ((locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame F₂))) ∧ y ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).perp ((locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame (lf D (X.Fu u))))) ∧ y' - gσ.symm ((c.c p).e.symm q.1) ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame F₂)) ∧ y - gσ.symm ((c.c p).e.symm q.2) ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame (lf D (X.Fu u)))) ∧ ∃ v ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p Λ, y' - y = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (LocNG.theta ((⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p)) • v) := by
  intro D X Y u u' _ _ w F00 F'0 FP _ _ hFP G c p σ gσ F₂ U₁ U₂ hM hE Λ q
  obtain ⟨g0, _, hu0, huniq, -⟩ := GlobalTheory.LocExt.ext_isometry D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p σ hM.1
  have hu : LocNG.IsUnitary (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) gσ := (huniq gσ hE) ▸ hu0
  have hlat := GlobalTheory.GraphTr.lat_eq c p σ gσ hE Λ
  have hX1 := GlobalTheory.GraphTr.map_X (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p σ gσ hE (frame (lf D (X.Fu u))) (frame F00) U₁
    hM.2.1 hM.2.2.2.1
  have hX2 := GlobalTheory.GraphTr.map_X (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p σ gσ hE (frame F₂) (frame F'0) U₂
    hM.2.2.1 hM.2.2.2.2
  have hF1 := GlobalTheory.GraphTr.framesX c p (hFP p).1.1
  have hF2 := GlobalTheory.GraphTr.framesX' c p (hFP p).1.2.1
  rw [← hX1] at hF1
  rw [← hX2] at hF2
  show q ∈ (G.S p).graphOf ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).lat p (c.lat σ Λ)) ↔ _
  rw [hlat]
  exact GlobalTheory.GraphTr.graphOf_coord (c.c p) gσ hu _ _ _ hF1 hF2 _ (GlobalTheory.GraphTr.th_eq c p) q
