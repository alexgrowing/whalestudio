import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalDiscriminantIsUnit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalFramePairsDifferIsometryUnitriangularStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalIsometryExtendsLocalIsometryStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnsignedLocalTermRowLatticeIsTerm
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsDatumOfTwoCongruentFramesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitRepsOver

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver

namespace GlobalTheory.LocOver.GlobOver

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Mat

theorem uni_mul {K : Type} [CommRing K] {n : ℕ} {A B : Matrix (Fin n) (Fin n) K} (hA : Uni A) (hB : Uni B) :
    Uni (A * B) := by
  obtain ⟨hA0, hA1⟩ := hA
  obtain ⟨hB0, hB1⟩ := hB
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rcases lt_or_ge c a with h | h
    · rw [hA0 a c h, zero_mul]
    · rw [hB0 c b (lt_of_lt_of_le hab h), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [hA1, hB1, one_mul]
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with h | h
      · rw [hA0 a c h, zero_mul]
      · rw [hB0 c a h, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ a) h

theorem tri_trans {K W : Type} [CommRing K] [AddCommGroup W] [Module K W] {n : ℕ} {f g h : Fin n → W}
    (h1 : Tri K f g) (h2 : Tri K g h) : Tri K f h := by
  obtain ⟨A, hA, hAc⟩ := h1
  obtain ⟨B, hB, hBc⟩ := h2
  have hAc' : ∀ b, g b = ∑ a, A a b • f a := hAc
  have hBc' : ∀ b, h b = ∑ a, B a b • g a := hBc
  refine ⟨A * B, uni_mul hA hB, fun b => ?_⟩
  rw [hBc' b]
  simp only [hAc', Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by rw [mul_comm]

theorem tri_map {K W W' : Type} [CommRing K] [AddCommGroup W] [Module K W] [AddCommGroup W'] [Module K W'] {n : ℕ}
    (φ : W →ₗ[K] W') {f g : Fin n → W} (h : Tri K f g) : Tri K (fun a => φ (f a)) (fun a => φ (g a)) := by
  obtain ⟨A, hA, hc⟩ := h
  have hc' : ∀ b, g b = ∑ a, A a b • f a := hc
  exact ⟨A, hA, fun b => by simp only [hc' b, map_sum, map_smul]⟩

end Mat

section Loc

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

theorem mem_img (g : V ≃ₗ[E] V) (Λ : Submodule M.L.O V) (x : V) :
    x ∈ img g Λ ↔ ∃ y ∈ Λ, g y = x := by
  unfold img
  exact Submodule.mem_map

theorem span_map_le (g : V ≃ₗ[E] V) (S : Set V) :
    ∀ v ∈ Submodule.span M.L.O S, g v ∈ Submodule.span M.L.O ((fun x => g x) '' S) := by
  intro v hv
  have h := Submodule.mem_map_of_mem (f := (g : V →ₗ[E] V).restrictScalars M.L.O) hv
  rw [← Submodule.span_image] at h
  exact h

theorem img_selfDual (H : HermSp M V) {g : V ≃ₗ[E] V} (hg : IsUnitary H g)
    {Λ : Submodule M.L.O V} (hΛ : H.IsSelfDual Λ) : H.IsSelfDual (img g Λ) := by
  obtain ⟨hfg, hsp, hdual⟩ := hΛ
  have hg' : ∀ x y, H.h (g x) (g y) = H.h x y := hg
  have hset : ((img g Λ : Submodule M.L.O V) : Set V) = (g : V →ₗ[E] V) '' (Λ : Set V) := by
    ext x
    simp only [SetLike.mem_coe, mem_img, Set.mem_image, LinearEquiv.coe_coe]
  refine ⟨hfg.map _, ?_, fun x => ?_⟩
  · rw [hset, Submodule.span_image, hsp, Submodule.map_top]
    exact LinearEquiv.range g
  · have hx : x ∈ img g Λ ↔ g.symm x ∈ Λ := by
      rw [mem_img]
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
      · intro h
        exact ⟨_, h, by simp⟩
    rw [hx, hdual (g.symm x)]
    constructor
    · intro h y hy
      obtain ⟨z, hz, rfl⟩ := (mem_img g Λ y).1 hy
      have := h z hz
      rw [← hg' (g.symm x) z, LinearEquiv.apply_symm_apply] at this
      exact this
    · intro h z hz
      rw [← hg' (g.symm x) z, LinearEquiv.apply_symm_apply]
      exact h (g z) ((mem_img g Λ (g z)).2 ⟨z, hz, rfl⟩)

theorem img_frame (H : HermSp M V) {g : V ≃ₗ[E] V} (hg : IsUnitary H g)
    {Λ : Submodule M.L.O V} {r : ℕ} {f : Fin (r + 1) → V} {T : F} (hf : H.IsFrame Λ r f T) :
    H.IsFrame (img g Λ) r (fun b => g (f b)) T := by
  have hg' : ∀ x y, H.h (g x) (g y) = H.h x y := hg
  obtain ⟨⟨hmem, hli, hsp⟩, hiso, hzz, hT⟩ := hf
  refine ⟨⟨fun a => (mem_img g Λ _).2 ⟨f a, hmem a, rfl⟩, hli.map' _ g.ker, ?_⟩, ?_, ?_, hT⟩
  · intro x hx hxs
    obtain ⟨y, hy, rfl⟩ := (mem_img g Λ x).1 hx
    have hr : Set.range (fun b => g (f b)) = (g : V →ₗ[E] V) '' Set.range f :=
      Set.range_comp (⇑(g : V →ₗ[E] V)) f
    have hys : y ∈ Submodule.span E (Set.range f) := by
      rw [hr, Submodule.span_image, Submodule.mem_map] at hxs
      obtain ⟨z, hz, hzy⟩ := hxs
      rwa [← g.injective hzy]
    have h2 := span_map_le (M := M) g (Set.range f) y (hsp y hy hys)
    have hr' : Set.range (fun b => g (f b)) = (fun x => g x) '' Set.range f :=
      Set.range_comp (fun x => g x) f
    rw [hr']
    exact h2
  · intro a b hab
    rw [hg']
    exact hiso a b hab
  · rw [hg']
    exact hzz

theorem smulLat_map (H : HermSp M V) (g : V ≃ₗ[E] V) (c : E) (Λ : Submodule M.L.O V) {x : V}
    (hx : x ∈ H.smulLat c Λ) : g x ∈ H.smulLat c (img g Λ) := by
  unfold HermSp.smulLat at hx ⊢
  refine Submodule.span_mono ?_ (span_map_le (M := M) g _ x hx)
  rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
  exact ⟨g v, (mem_img g Λ (g v)).2 ⟨v, hv, rfl⟩, by simp only [map_smul]⟩

private lemma Zhat_comp_unitary (H : HermSp M V) {g : V ≃ₗ[E] V} (hg : IsUnitary H g) {r : ℕ}
    (f f' : Fin (r + 1) → V) :
    H.Zhat (fun b => g (f b)) (fun b => g (f' b)) = H.Zhat f f' := by
  have hg' : ∀ x y, H.h (g x) (g y) = H.h x y := hg
  ext a b
  simp only [HermSp.Zhat, Matrix.of_apply, hg']

private lemma Dl_comp_unitary (H : HermSp M V) {g : V ≃ₗ[E] V} (hg : IsUnitary H g) {r : ℕ}
    (f f' : Fin (r + 1) → V) (l : ℕ) :
    H.Dl (fun b => g (f b)) (fun b => g (f' b)) l = H.Dl f f' l := by
  simp only [HermSp.Dl, Zhat_comp_unitary H hg]

theorem isTerm_move (H : HermSp M V) {g : V ≃ₗ[E] V} (hg : IsUnitary H g) {r : ℕ} {t : Term V M r}
    (ht : H.IsTerm t) : H.IsTerm (move g t) := by
  obtain ⟨hsd, hfr, hfr', hD, hG, hsp⟩ := ht
  refine ⟨img_selfDual H hg hsd, img_frame H hg hfr, img_frame H hg hfr', ?_, ?_, ?_⟩
  · show IsUnit (H.Dl (fun b => g (t.f b)) (fun b => g (t.f' b)) (r + 1))
    rw [Dl_comp_unitary H hg]
    exact hD
  · show H.Gdet (fun b => g (t.f b)) (fun b => g (t.f' b)) t.T t.T' ≠ 0
    simpa only [HermSp.Gdet, Dl_comp_unitary H hg] using hG
  · intro q hq
    obtain ⟨h1, h2, h3⟩ := hsp q hq
    refine ⟨h1, h2, fun b => ?_⟩
    show g (t.f' b) - g (t.f b) ∈ H.smulLat _ (img g t.abelian₂)
    rw [← map_sub]
    exact smulLat_map H g _ t.abelian₂ (h3 b)

end Loc

section Glob

theorem over_local : ∀ (D : D7) (Z : LocDat D), ∀ (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V), IsRowLat D F0 Λ → ∀ F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E), PD D Λ (lf D F0) u' F' → Gval (lf D F0) F' ≠ 0 → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)), IsInCell (ZhatOM (ZhatL (lf D F0) F')) w → ZhatOM (ZhatL F00 F'0) = ptMat w → ∀ (p : PlF D) (P : LocNG.FPair (locH Z p) D.R.rS), AtBase Z p F00 F'0 (Tu D u) (Tu D u') P → ∃ d, Over P d (locU Z p Λ (lf D F0) F' (Tu D u) (Tu D u')) := by
  intro D Z u u' F0 Λ hrow F' hPD hG w F00 F'0 hcell hpt p P hAt
  have hT : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (Formalism.L2.SG.GramJoint.Tu_pos D u).ne'
  have hT' : ((Tu D u' : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (Formalism.L2.SG.GramJoint.Tu_pos D u').ne'
  obtain ⟨-, γ, hγ, hA, hA'⟩ := GlobalTheory.T.rationalFramePairs_differ_isometry_unitriangular D (lf D F0) F00 F' F'0 w hT hT' hG hcell hpt
  obtain ⟨g, hext, hgU, -, -, -⟩ := GlobalTheory.T.rational_isometry_extends_local_isometry D Z p γ hγ
  obtain ⟨ht0, htri0⟩ := locU_isTerm D Z u u' F0 Λ hrow F' hPD hG p
  have hOK : (Z.M p).OK := (Z.agree p).1
  obtain ⟨A, hAu, hAc⟩ := hA
  obtain ⟨A', hA'u, hA'c⟩ := hA'
  obtain ⟨Ap, hAp, -⟩ := tri_scaled D Z _ _ A hAu hAc
  obtain ⟨Ap', hAp', -⟩ := tri_scaled D Z _ _ A' hA'u hA'c
  have hext' : ∀ x, g (baseChange₂ D p x) = baseChange₂ D p (γ x) := hext
  have hmove : ∀ f : Fin (D.R.rS + 1) → (VS D).V,
      (fun a => g (scaled Z p f a)) = scaled Z p (fun a => γ (f a)) := by
    intro f
    funext a
    simp only [scaled, map_smul, hext']
  set t := locU Z p Λ (lf D F0) F' (Tu D u) (Tu D u') with ht_def
  have hf : Tri (D.s.atP p).Ep P.A.f (move g t).f := by
    rw [hAt.1]
    have h1 : (move g t).f = fun a => g (scaled Z p (frame (lf D F0)) a) := rfl
    rw [h1, hmove (frame (lf D F0))]
    exact ⟨Ap p, hAp p⟩
  have hf' : Tri (D.s.atP p).Ep P.B.f (move g t).f' := by
    rw [hAt.2.1]
    have h1 : Tri (D.s.atP p).Ep (fun a => g (scaled Z p (frame F') a)) (fun a => g (t.f' a)) :=
      tri_map (g : Vp D p →ₗ[(D.s.atP p).Ep] Vp D p) htri0
    rw [hmove (frame F')] at h1
    exact tri_trans ⟨Ap' p, hAp' p⟩ h1
  obtain ⟨d, hd⟩ := GlobalTheory.T.exists_datum_of_two_congruent_frames (Z.M p) hOK (locH Z p) D.R.rS P (move g t)
    (isTerm_move (locH Z p) hgU ht0) hAt.2.2.1.symm hAt.2.2.2.symm hf hf'
  refine ⟨d, ?_⟩
  unfold Over
  exact ⟨g, hgU, d, (orbit_reps_over (Z.M p) hOK (locH Z p) D.R.rS P).1.refl d, hd⟩

end Glob

end GlobalTheory.LocOver.GlobOver
