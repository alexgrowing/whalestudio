import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemPerpSpan
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.DatumOf

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem mem_smul_iff (g : S.GLV) (P : Submodule L.O S.V) (x : S.V) :
    x ∈ g • P ↔ ∃ b ∈ P, g b = x := by
  simp only [Submodule.mem_smul_pointwise_iff_exists, LinearEquiv.smul_def]

theorem inner_le_of_unip (Y : Submodule E S.V) (n : S.GLV) (hn : n ∈ unipOn (perp L S.Hm Y) Y)
    (Λ : Submodule L.O S.V) :
    ((n • Λ) ⊓ (perp L S.Hm Y).restrictScalars L.O) ⊔ Y.restrictScalars L.O ≤
      (Λ ⊓ (perp L S.Hm Y).restrictScalars L.O) ⊔ Y.restrictScalars L.O := by
  refine sup_le ?_ le_sup_right
  rintro z ⟨hz1, hz2⟩
  obtain ⟨y, hy, rfl⟩ := (mem_smul_iff S n Λ z).1 hz1
  have hyP : y ∈ perp L S.Hm Y := (hn.1 y).1 hz2
  have e : n y = y + (n y - y) := by abel
  rw [e]
  exact Submodule.add_mem_sup ⟨hy, hyP⟩ (hn.2 y hyP)

theorem inner_eq_of_unip (Y : Submodule E S.V) (n : S.GLV) (hn : n ∈ unipOn (perp L S.Hm Y) Y)
    (Λ : Submodule L.O S.V) :
    ((n • Λ) ⊓ (perp L S.Hm Y).restrictScalars L.O) ⊔ Y.restrictScalars L.O =
      (Λ ⊓ (perp L S.Hm Y).restrictScalars L.O) ⊔ Y.restrictScalars L.O := by
  refine le_antisymm (inner_le_of_unip S Y n hn Λ) ?_
  have h1 := inner_le_of_unip S Y n⁻¹ (inv_mem hn) (n • Λ)
  rwa [inv_smul_smul] at h1

theorem complementGroup_fixes_frameSpan {g : S.GLV} (hg : g ∈ S.H0) {x : S.V} (hx : x ∈ S.ME) : g x = x :=
  sub_eq_zero.1 ((Submodule.mem_bot E).1 (hg.2.2 x hx))

theorem X_le : S.X ≤ S.ME := by
  refine le_trans (Submodule.span_mono (Set.image_mono fun i hi => ?_)) le_sup_left
  simp only [Set.mem_setOf_eq] at hi ⊢
  omega

theorem X'_le : S.X' ≤ S.ME := by
  refine le_trans (Submodule.span_mono (Set.image_mono fun i hi => ?_)) le_sup_right
  simp only [Set.mem_setOf_eq] at hi ⊢
  omega

theorem hermitianOrthogonalComplement_mapsTo_of_mem_stabilizer (Y : Submodule E S.V) (hY : Y ≤ S.ME) {g : S.GLV} (hg : g ∈ S.H0) {y : S.V}
    (hy : y ∈ perp L S.Hm Y) : g y ∈ perp L S.Hm Y := by
  intro w hw
  have e := hg.1 y w
  rw [complementGroup_fixes_frameSpan S hg (hY hw)] at e
  rw [e]
  exact hy w hw

theorem inTh_smul (g : S.GLV) (Λ : Submodule L.O S.V) {v : S.V} (hv : S.InTh Λ v) :
    S.InTh (g • Λ) (g v) := by
  obtain ⟨y, hy, rfl⟩ := hv
  exact ⟨g y, (mem_smul_iff S g Λ _).2 ⟨y, hy, rfl⟩, map_smul g _ y⟩

theorem smul_inner_lattice_le_of_mem_hermitianStabilizer (Y : Submodule E S.V) (hY : Y ≤ S.ME) {g : S.GLV} (hg : g ∈ S.H0)
    (Λ : Submodule L.O S.V) :
    g • ((Λ ⊓ (perp L S.Hm Y).restrictScalars L.O) ⊔ Y.restrictScalars L.O) ≤
      ((g • Λ) ⊓ (perp L S.Hm Y).restrictScalars L.O) ⊔ Y.restrictScalars L.O := by
  intro z hz
  obtain ⟨b, hb, rfl⟩ := (mem_smul_iff S g _ z).1 hz
  obtain ⟨y, ⟨hy1, hy2⟩, x, hx, rfl⟩ := Submodule.mem_sup.1 hb
  rw [map_add, complementGroup_fixes_frameSpan S hg (hY hx)]
  exact Submodule.add_mem_sup ⟨(mem_smul_iff S g Λ _).2 ⟨y, hy1, rfl⟩, hermitianOrthogonalComplement_mapsTo_of_mem_stabilizer S Y hY hg hy2⟩ hx

theorem smul_inner_lattice_eq_of_mem_hermitianStabilizer (Y : Submodule E S.V) (hY : Y ≤ S.ME) {g : S.GLV} (hg : g ∈ S.H0)
    (Λ : Submodule L.O S.V) :
    ((g • Λ) ⊓ (perp L S.Hm Y).restrictScalars L.O) ⊔ Y.restrictScalars L.O =
      g • ((Λ ⊓ (perp L S.Hm Y).restrictScalars L.O) ⊔ Y.restrictScalars L.O) := by
  refine le_antisymm ?_ (smul_inner_lattice_le_of_mem_hermitianStabilizer S Y hY hg Λ)
  have h1 := smul_inner_lattice_le_of_mem_hermitianStabilizer S Y hY (inv_mem hg) (g • Λ)
  rw [inv_smul_smul] at h1
  intro z hz
  have h2 := Submodule.smul_mem_pointwise_smul _ g _ (h1 (Submodule.smul_mem_pointwise_smul z g⁻¹ _ hz))
  rwa [smul_inv_smul] at h2

theorem smul_graphOf_subset_of_mem_hermitianStabilizer {g : S.GLV} (hg : g ∈ S.H0) (Λ : Submodule L.O S.V) :
    g • S.graphOf Λ ⊆ S.graphOf (g • Λ) := by
  rintro _ ⟨p, ⟨y', hy', y, hy, h1, h2, h3, h4, h5⟩, rfl⟩
  refine ⟨g y', (mem_smul_iff S g Λ _).2 ⟨y', hy', rfl⟩, g y, (mem_smul_iff S g Λ _).2 ⟨y, hy, rfl⟩,
    hermitianOrthogonalComplement_mapsTo_of_mem_stabilizer S _ (X'_le S) hg h1, hermitianOrthogonalComplement_mapsTo_of_mem_stabilizer S _ (X_le S) hg h2, ?_, ?_, ?_⟩
  · show g y' - g p.1 ∈ S.X'
    rw [← map_sub, complementGroup_fixes_frameSpan S hg (X'_le S h3)]
    exact h3
  · show g y - g p.2 ∈ S.X
    rw [← map_sub, complementGroup_fixes_frameSpan S hg (X_le S h4)]
    exact h4
  · rw [← map_sub]
    exact inTh_smul S g Λ h5

theorem graphOf_smul_eq_of_mem_hermitianStabilizer {g : S.GLV} (hg : g ∈ S.H0) (Λ : Submodule L.O S.V) :
    S.graphOf (g • Λ) = g • S.graphOf Λ := by
  refine subset_antisymm ?_ (smul_graphOf_subset_of_mem_hermitianStabilizer S hg Λ)
  intro p hp
  have h1 := smul_graphOf_subset_of_mem_hermitianStabilizer S (inv_mem hg) (g • Λ) ⟨p, hp, rfl⟩
  rw [inv_smul_smul] at h1
  exact ⟨g⁻¹ • p, h1, smul_inv_smul g p⟩

theorem datOf_smul_eq_of_mem_hermitianStabilizer {g : S.GLV} (hg : g ∈ S.H0) (Λ : Submodule L.O S.V) :
    S.datOf (g • Λ) = g • S.datOf Λ :=
  Prod.ext (smul_inner_lattice_eq_of_mem_hermitianStabilizer S S.X (X_le S) hg Λ)
    (Prod.ext (smul_inner_lattice_eq_of_mem_hermitianStabilizer S S.X' (X'_le S) hg Λ) (graphOf_smul_eq_of_mem_hermitianStabilizer S hg Λ))

theorem std_inner [IsNonarchimedeanLocalField F] [CharZero F] (g : Fin (r + 1) → S.V) (gs : Fin r → S.V)
    (hgs : (g = S.f ∧ gs = S.es) ∨ (g = S.f' ∧ gs = S.es')) (A : Submodule L.O S.V) (hA : S.IsInner g gs A) :
    (S.stdLat g gs A ⊓ (perp L S.Hm (S.spanTo g r)).restrictScalars L.O) ⊔
      (S.spanTo g r).restrictScalars L.O = A := by
  have h3 := (StdLat.stdLat_spec L r k S g gs hgs A hA).2.2
  apply le_antisymm
  · refine sup_le ?_ ?_
    · rintro y ⟨hy1, hy2⟩
      exact (h3 y).2 ⟨y, hy1, hy2, by simp⟩
    · intro x hx
      exact hA.1 x hx
  · intro x hx
    obtain ⟨y, hy, hyp, hyx⟩ := (h3 x).1 hx
    have e : x = y - (y - x) := by abel
    rw [e]
    exact Submodule.sub_mem_sup ⟨hy, hyp⟩ hyx

theorem datOf_term [IsNonarchimedeanLocalField F] [CharZero F] {d : S.Datum} {Λ : Submodule L.O S.V}
    (h : S.IsTerm d Λ) : d = S.datOf Λ := by
  obtain ⟨⟨n, n'⟩, hA, hA', hn, hn', hΛ, hΛ', -, hg⟩ := h
  refine Prod.ext ?_ (Prod.ext ?_ hg)
  · show d.1 = (Λ ⊓ (perp L S.Hm S.X).restrictScalars L.O) ⊔ S.X.restrictScalars L.O
    rw [hΛ, inner_eq_of_unip S S.X n hn.2]
    exact (std_inner S S.f S.es (Or.inl ⟨rfl, rfl⟩) _ hA).symm
  · show d.2.1 = (Λ ⊓ (perp L S.Hm S.X').restrictScalars L.O) ⊔ S.X'.restrictScalars L.O
    rw [hΛ', inner_eq_of_unip S S.X' n' hn'.2]
    exact (std_inner S S.f' S.es' (Or.inr ⟨rfl, rfl⟩) _ hA').symm

theorem exists_unitri (g : Fin (r + 1) → S.V) (φ : S.GLV) (h : ∀ b : Fin (r + 1), φ (g b) - g b ∈ S.spanTo g b) :
    ∃ s : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) ∧
      ∀ j, φ (g j) = ∑ i, s i j • g i := by
  choose c hc0 hc using fun b : Fin (r + 1) => StdLat.exists_coef g {i | (i : ℕ) < b} (h b)
  refine ⟨fun i j => c j i + if i = j then 1 else 0, ⟨fun i j hij => ?_, fun i => ?_⟩, fun j => ?_⟩
  · have hne : i ≠ j := (ne_of_lt hij).symm
    have h0 : c j i = 0 := hc0 j i fun hi => by
      have := Fin.lt_def.1 hij
      simp only [Set.mem_setOf_eq] at hi
      omega
    simp [h0, hne]
  · have h0 : c i i = 0 := hc0 i i fun hi => lt_irrefl (i : ℕ) hi
    simp [h0]
  · have e1 : ∑ i, (c j i + if i = j then (1 : E) else 0) • g i = ∑ i, c j i • g i + g j := by
      simp [add_smul, Finset.sum_add_distrib, ite_smul]
    rw [e1, ← hc j]
    abel

theorem mem_hermitianStabilizer_of_preserves_both_flags [IsNonarchimedeanLocalField F] [CharZero F] (φ : S.GLV) (hφ : φ ∈ isomG L S.Hm)
    (h1 : ∀ b : Fin (r + 1), φ (S.f b) - S.f b ∈ S.spanTo S.f b)
    (h2 : ∀ b : Fin (r + 1), φ (S.f' b) - S.f' b ∈ S.spanTo S.f' b) :
    ∃ s ∈ S.St, ∃ h ∈ S.H0, φ = s * h := by
  have := L.free
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)
  have : IsArtinianRing E := IsArtinianRing.of_finite F E
  obtain ⟨s, hs, hsφ⟩ := exists_unitri S S.f φ h1
  obtain ⟨s', hs', hsφ'⟩ := exists_unitri S S.f' φ h2
  have hz : cT L s * S.Zh * s' = S.Zh := by
    ext a b
    rw [← FrameStab.pair_eq S s s' a b, ← hsφ, ← hsφ']
    exact hφ _ _
  obtain ⟨h, hh, hf, hf'⟩ := ((FrameStab.stab_eq L r k S).2 s s' hs hs').1 hz
  have k1 : ∀ (g : Fin (r + 1) → S.V) (m : ℕ), (∀ i, φ (g i) = h (g i)) → ∀ v ∈ S.spanTo g m, φ v = h v := by
    intro g m hg v hv
    have hle : S.spanTo g m ≤ LinearMap.eqLocus (φ : S.V →ₗ[E] S.V) (h : S.V →ₗ[E] S.V) := by
      rw [Frames.spanTo, Submodule.span_le]
      rintro _ ⟨i, -, rfl⟩
      exact hg i
    exact hle hv
  have hfix : ∀ v ∈ S.ME, φ v = h v := by
    intro v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add, map_add, k1 S.f _ (fun i => by rw [hsφ, hf]) a ha,
      k1 S.f' _ (fun i => by rw [hsφ', hf']) b hb]
  have hiso : h ∈ isomG L S.Hm := hh.1.1.1
  refine ⟨h, hh, h⁻¹ * φ, Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hiso) hφ, ?_⟩, (mul_inv_cancel_left h φ).symm⟩
  refine FrameStab.mem_unipOn' bot_le _ fun v hv => ?_
  show h.symm (φ v) - v ∈ (⊥ : Submodule E S.V)
  rw [hfix v hv, LinearEquiv.symm_apply_apply, sub_self]
  exact zero_mem _

end

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), (∀ d Λ, S.IsTerm d Λ → d = S.datOf Λ) ∧ (∀ h ∈ S.H0, ∀ Λ, S.datOf (h • Λ) = h • S.datOf Λ) ∧ (∀ n ∈ S.N, ∀ Λ, (S.datOf (n • Λ)).1 = (S.datOf Λ).1) ∧ (∀ n ∈ S.N', ∀ Λ, (S.datOf (n • Λ)).2.1 = (S.datOf Λ).2.1) ∧ ∀ φ ∈ isomG L S.Hm, (∀ b : Fin (r + 1), φ (S.f b) - S.f b ∈ S.spanTo S.f b) → (∀ b : Fin (r + 1), φ (S.f' b) - S.f' b ∈ S.spanTo S.f' b) → ∃ s ∈ S.St, ∃ h ∈ S.H0, φ = s * h := by
  intro F _ _ _ _ _ E _ _ _ L r k S
  exact ⟨fun d Λ h => datOf_term S h, fun g hg Λ => datOf_smul_eq_of_mem_hermitianStabilizer S hg Λ,
    fun n hn Λ => inner_eq_of_unip S S.X n hn.2 Λ, fun n hn Λ => inner_eq_of_unip S S.X' n hn.2 Λ,
    fun φ hφ h1 h2 => mem_hermitianStabilizer_of_preserves_both_flags S φ hφ h1 h2⟩

end GlobalTheory.HL.DatumOf
