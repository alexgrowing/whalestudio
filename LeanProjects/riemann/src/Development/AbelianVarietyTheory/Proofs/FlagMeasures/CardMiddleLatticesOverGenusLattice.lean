import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NcardGluedMiddleLatticesEqPowPrimeSubOneStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SplitRowLatticeMiddleIffGluedLatticeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFrameFixingIsometrySplitRowLatticeStatement

noncomputable section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LoopC.GluingNum

variable (D : D7)

abbrev jz (z : (VS D).V) : ((D.sp.X 0).V × D.host.E) →ₗ[𝓞 D.host.E] (VS D).V :=
  ((D.sp.iXY 0).coprod (LinearMap.toSpanSingleton D.host.E (VS D).V z)).restrictScalars (𝓞 D.host.E)

theorem jz_apply (z : (VS D).V) (p : (D.sp.X 0).V × D.host.E) :
    jz D z p = D.sp.iXY 0 p.1 + p.2 • z := rfl

theorem mem_Wb (v : (hS D).V) : v ∈ Wb D ↔
    (∀ a, (hS D).hT (D.sp.hypE a) v = 0) ∧ ∀ a, (hS D).hT (D.sp.hypF a) v = 0 := by
  unfold Wb
  rw [Formalism.MainNotions.mem_orth_iff]
  constructor
  · intro h
    exact ⟨fun a => h _ (Submodule.subset_span (Or.inl ⟨a, rfl⟩)),
      fun a => h _ (Submodule.subset_span (Or.inr ⟨a, rfl⟩))⟩
  · rintro ⟨h1, h2⟩ x hx
    have : Submodule.span D.host.E (Set.range D.sp.hypE ∪ Set.range D.sp.hypF) ≤
        LinearMap.ker ((hS D).hT.flip v) := by
      refine Submodule.span_le.2 ?_
      rintro _ (⟨a, rfl⟩ | ⟨a, rfl⟩)
      · exact h1 a
      · exact h2 a
    exact this hx

theorem eq_zero_of_mem_X {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (he : F0.e = D.sp.hypE)
    {x : (hS D).V} (hx : x ∈ F0.X) (hw : x ∈ Wb D) : x = 0 := by
  unfold FlagG.X at hx
  rw [he] at hx
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hx
  have h2 := ((mem_Wb D _).1 hw).2
  have hc : ∀ b, c b = 0 := by
    intro b
    have h := Formalism.MainNotions.hT_swap_zero (h2 b)
    simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, D.sp.hyp_ef,
      smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true] at h
    simpa using h
  simp [hc]

theorem iXY_mem_Wb (w : (D.sp.X 0).V) : D.sp.iXY 0 w ∈ Wb D :=
  (mem_Wb D _).2 ⟨fun a => Formalism.MainNotions.hT_swap_zero (D.sp.hyp_orthX a w).1,
    fun a => Formalism.MainNotions.hT_swap_zero (D.sp.hyp_orthX a w).2⟩

theorem zmOf_mem_Wb (u : D.what₂.Word) : D.zmOf u ∈ Wb D :=
  Submodule.smul_mem _ _ ((mem_Wb D _).2 ⟨fun a => Formalism.MainNotions.hT_swap_zero (D.sp.hyp_orthz a).1,
    fun a => Formalism.MainNotions.hT_swap_zero (D.sp.hyp_orthz a).2⟩)

theorem jz_mem_Wb (u : D.what₂.Word) (p : (D.sp.X 0).V × D.host.E) : jz D (D.zmOf u) p ∈ Wb D := by
  rw [jz_apply]
  exact (Wb D).add_mem (iXY_mem_Wb D _) ((Wb D).smul_mem _ (zmOf_mem_Wb D u))

theorem exists_jz (u : D.what₂.Word) (F0 : Fb D u) (hT : Tu D u ≠ 0) (he : F0.e = D.sp.hypE)
    (hz : F0.z = D.zmOf u) {v : (hS D).V} (hv : v ∈ Wb D) : ∃ p, jz D (D.zmOf u) p = v := by
  have hW := (Formalism.MainNotions.WHyp_Wsp D u hT (lf D F0) he hz).1
  have hT' : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hT
  set c : D.host.E := -((hS D).hT F0.z v) / ((Tu D u : ℕ) : D.host.E) with hc
  have hvz : v - c • D.zmOf u ∈ Wb D := (Wb D).sub_mem hv ((Wb D).smul_mem _ (zmOf_mem_Wb D u))
  have h1 : v - c • D.zmOf u ∈ orth (hS D) (Xplus (lf D F0)) := by
    rw [Formalism.MainNotions.mem_orth_iff]
    refine Formalism.MainNotions.hT_zero_of_mem_Xplus F0 (fun a => ?_) ?_
    · rw [he]; exact ((mem_Wb D _).1 hvz).1 a
    · rw [← hz, map_sub, map_smul, F0.z_norm, smul_eq_mul, hc]
      field_simp
      ring
  rw [← hW] at h1
  obtain ⟨_, ⟨w, rfl⟩, x, hx, hs⟩ := Submodule.mem_sup.1 h1
  have hx0 : x = 0 := by
    refine eq_zero_of_mem_X D F0 he hx ?_
    have : x = (v - c • D.zmOf u) - D.sp.iXY 0 w := by rw [← hs]; abel
    rw [this]
    exact (Wb D).sub_mem hvz (iXY_mem_Wb D w)
  refine ⟨(w, c), ?_⟩
  rw [hx0, add_zero] at hs
  rw [jz_apply, hs]
  simp

theorem comap_sup_X (u : D.what₂.Word) (F0 : Fb D u) (he : F0.e = D.sp.hypE)
    (L : LatV D) (hL : L ≤ toO (hS D) (Wb D)) :
    (L ⊔ toO (hS D) F0.X).comap (jz D (D.zmOf u)) = L.comap (jz D (D.zmOf u)) := by
  apply le_antisymm _ (Submodule.comap_mono le_sup_left)
  intro p hp
  obtain ⟨l, hl, x, hx, hs⟩ := Submodule.mem_sup.1 hp
  have hx0 : x = 0 := by
    refine eq_zero_of_mem_X D F0 he hx ?_
    have : x = jz D (D.zmOf u) p - l := by rw [← hs]; abel
    rw [this]
    exact (Wb D).sub_mem (jz_mem_Wb D u p) (hL hl)
  rw [hx0, add_zero] at hs
  change jz D (D.zmOf u) p ∈ L
  rw [← hs]; exact hl

theorem mem_Lsub {T : D.host.E} (F : Fg D T) (Λ : LatV D) (v : (hS D).V) :
    v ∈ Lsub Λ F ↔ v ∈ orth (hS D) (Xsp F) ∧
      ∃ l ∈ Λ, l ∈ orth (hS D) (Xsp F) ∧ v - l ∈ Xsp F := by
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨l, hl, x, hx, hs⟩ := Submodule.mem_sup.1 h1
    refine ⟨h2, l, hl.1, hl.2, ?_⟩
    rw [← hs]; simpa using hx
  · rintro ⟨h2, l, hl, hl', hx⟩
    refine ⟨Submodule.mem_sup.2 ⟨l, ⟨hl, hl'⟩, v - l, hx, by abel⟩, h2⟩

theorem Lsub_gmap {T : D.host.E} (F : Fg D T) (Λ : LatV D) (n : (hS D).V ≃ₗ[D.host.E] (hS D).V)
    (hn : FixFr D F n) : Lsub (Formalism.HermitianLatticesTheory.gmap n Λ) F = Lsub Λ F := by
  obtain ⟨h1, h2, h3⟩ := hn
  have key : ∀ l, n l ∈ orth (hS D) (Xsp F) ↔ l ∈ orth (hS D) (Xsp F) := by
    intro l
    have he : ∀ a, (hS D).hT (F.fl.e a) (n l) = (hS D).hT (F.fl.e a) l := by
      intro a
      have := h2 a.castSucc
      simp only [frame, FlagG.fvec, Fin.snoc_castSucc] at this
      conv_lhs => rw [← this]
      exact h1 _ _
    rw [Formalism.MainNotions.mem_orth_iff, Formalism.MainNotions.mem_orth_iff]
    constructor
    · intro h
      exact Formalism.MainNotions.hT_zero_of_mem_X F.fl (fun a => by
        rw [← he]; exact h _ (Submodule.subset_span ⟨a, rfl⟩))
    · intro h
      exact Formalism.MainNotions.hT_zero_of_mem_X F.fl (fun a => by
        rw [he]; exact h _ (Submodule.subset_span ⟨a, rfl⟩))
  ext v
  rw [mem_Lsub, mem_Lsub]
  refine and_congr_right (fun _ => ⟨?_, ?_⟩)
  · rintro ⟨_, ⟨l, hl, rfl⟩, hl', hx⟩
    have hl2 : l ∈ orth (hS D) (Xsp F) := (key l).1 hl'
    refine ⟨l, hl, hl2, ?_⟩
    have := (Xsp F).add_mem hx (h3 l hl2)
    convert this using 1
    change v - l = v - n l + (n l - l)
    abel
  · rintro ⟨l, hl, hl', hx⟩
    refine ⟨n l, ⟨l, hl, rfl⟩, (key l).2 hl', ?_⟩
    have := (Xsp F).sub_mem hx (h3 l hl')
    convert this using 1
    abel

theorem le_Wb_of_mem (u : D.what₂.Word) {M : LatW D} {L : LatV D} (hL : L ∈ glueSet D u M) :
    L ≤ toO (hS D) (Wb D) := by
  intro x hx
  change x ∈ Wb D
  rw [← hL.2.1]
  exact Submodule.subset_span hx

theorem comap_jz_inl (z : (VS D).V) (L : LatV D) :
    (L.comap (jz D z)).comap ((LinearMap.inl D.host.E (D.sp.X 0).V D.host.E).restrictScalars (𝓞 D.host.E)) =
      L.comap ((D.sp.iXY 0).restrictScalars (𝓞 D.host.E)) := by
  ext w
  change jz D z (w, 0) ∈ L ↔ D.sp.iXY 0 w ∈ L
  rw [jz_apply]
  simp

theorem gluingNum : ∀ (D : D7) (u : D.what₂.Word), (Tu D u).Prime → 3 ≤ Tu D u → SplitsCompletely (E := D.host.E) (Tu D u) → ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u → ∀ Λ : LatV D, IsRowLat D F0 Λ → ∀ M ∈ Formalism.HermitianLatticesTheory.genus (D.sp.X 0).hT (L0X D Λ (lf D F0)), {𝓛 : Submodule (𝓞 D.host.E) ((D.sp.X 0).V × D.host.E) | (∃ Λ', IsRowLat D F0 Λ' ∧ (Lsub Λ' (lf D F0)).comap (((D.sp.iXY 0).coprod (LinearMap.toSpanSingleton D.host.E (VS D).V F0.z)).restrictScalars (𝓞 D.host.E)) = 𝓛) ∧ 𝓛.comap ((LinearMap.inl D.host.E (D.sp.X 0).V D.host.E).restrictScalars (𝓞 D.host.E)) = M}.ncard = (Tu D u - 1) ^ D.R.f := by
  intro D u hp h3 hs F0 he hz Λ hΛ M hM
  have hB : IsBase D u F0 := ⟨he, hz⟩
  have h1 : 1 ≤ Tu D u := by omega
  rw [← (GlobalTheory.T.ncard_gluedMiddleLattices_eq_pow_prime_sub_one D u F0 Λ hp h3 hs hB hΛ M hM).2]
  have hinj : Set.InjOn (fun L : LatV D => L.comap (jz D (D.zmOf u))) (glueSet D u M) := by
    have aux : ∀ L₁ ∈ glueSet D u M, ∀ L₂ : LatV D,
        L₁.comap (jz D (D.zmOf u)) = L₂.comap (jz D (D.zmOf u)) → L₁ ≤ L₂ := by
      intro L₁ h₁ L₂ h x hx
      obtain ⟨p, rfl⟩ := exists_jz D u F0 hp.ne_zero he hz (le_Wb_of_mem D u h₁ hx)
      have : p ∈ L₁.comap (jz D (D.zmOf u)) := hx
      rw [h] at this
      exact this
    intro L₁ h₁ L₂ h₂ h
    exact le_antisymm (aux L₁ h₁ L₂ h) (aux L₂ h₂ L₁ h.symm)
  rw [← hinj.ncard_image]
  congr 1
  ext 𝓛
  rw [hz]
  constructor
  · rintro ⟨⟨Λ', hΛ', rfl⟩, hc⟩
    obtain ⟨n, hn, hsp, hrow⟩ := GlobalTheory.T.exists_frameFixing_isometry_split_rowLattice D u F0 Λ' hB hΛ' h1
    obtain ⟨hg, hL⟩ := (GlobalTheory.T.splitRowLattice_middle_iff_gluedLattice D u F0 _ h1 hB hrow).1 hsp
    have e : (Lsub Λ' (lf D F0)).comap (jz D (D.zmOf u)) =
        (Formalism.HermitianLatticesTheory.gmap n Λ' ⊓ toO (hS D) (Wb D)).comap (jz D (D.zmOf u)) := by
      rw [← Lsub_gmap D (lf D F0) Λ' n hn, hL, comap_sup_X D u F0 he _ inf_le_right]
    refine ⟨Formalism.HermitianLatticesTheory.gmap n Λ' ⊓ toO (hS D) (Wb D),
      ⟨hg.1, hg.2.1, hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2.1, ?_⟩, e.symm⟩
    rw [← comap_jz_inl D (D.zmOf u), ← e]
    exact hc
  · rintro ⟨L, hL, rfl⟩
    obtain ⟨hrow, hsp, hW⟩ := (GlobalTheory.T.splitRowLattice_middle_iff_gluedLattice D u F0 Λ h1 hB hΛ).2 M L hL
    have hL' := ((GlobalTheory.T.splitRowLattice_middle_iff_gluedLattice D u F0 _ h1 hB hrow).1 hsp).2
    refine ⟨⟨_, hrow, ?_⟩, ?_⟩
    · rw [hL', hW]
      exact comap_sup_X D u F0 he L (le_Wb_of_mem D u hL)
    · exact (comap_jz_inl D (D.zmOf u) L).trans hL.2.2.2.2.2

end GlobalTheory.LoopC.GluingNum

end
