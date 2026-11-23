import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.XLeSpanRight
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ExistsOfMemSmulLat
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumATools
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalModelPeriodLattices

noncomputable section

open ValuativeRel Matrix

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section RG1

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}

theorem hR_add (x y z : V) : H.h x (y + z) = H.h x y + H.h x z := by
  rw [H.h_herm (y + z) x, H.h_add_left, map_add, ← H.h_herm y x, ← H.h_herm z x]

theorem hR_smul (c : E) (x y : V) : H.h x (c • y) = M.L.cj c * H.h x y := by
  rw [H.h_herm (c • y) x, H.h_smul_left, map_mul, ← H.h_herm y x]

theorem hR_zero (x : V) : H.h x 0 = 0 := by
  have h0 : H.h 0 x = 0 := by
    have h1 := H.h_smul_left 0 0 x
    rwa [zero_smul, zero_mul] at h1
  rw [H.h_herm 0 x, h0, map_zero]

theorem hR_sub (x y z : V) : H.h x (y - z) = H.h x y - H.h x z := by
  rw [sub_eq_add_neg, ← neg_one_smul E z, hR_add, hR_smul, map_neg, map_one]
  ring

theorem q_ne (g : SplitG M.L) : (g.q : F) ≠ 0 := fun h => g.q_irr.ne_zero (Subtype.ext h)

theorem q_mem_O (g : SplitG M.L) : algebraMap F E (g.q : F) ∈ M.L.O := by
  rw [M.L.O_def]
  have h1 : algebraMap F E (g.q : F) = algebraMap 𝒪[F] E g.q := (IsScalarTower.algebraMap_apply 𝒪[F] F E g.q).symm
  rw [h1]
  exact isIntegral_algebraMap

theorem cj_q (g : SplitG M.L) : M.L.cj (algebraMap F E (g.q : F)) = algebraMap F E (g.q : F) :=
  M.L.cj.commutes _

theorem gramMM_unit_of_term (t : Term V M r) (hT : H.IsTerm t) : IsUnit (H.gram (H.MMfam t)).det := by
  have hF : Formalism.MainNotions.ThinScalesBound.FrameK H t.f t.T := ⟨hT.2.1.2.1, hT.2.1.2.2.1⟩
  have hF' : Formalism.MainNotions.ThinScalesBound.FrameK H t.f' t.T' := ⟨hT.2.2.1.2.1, hT.2.2.1.2.2.1⟩
  have hD : IsUnit (H.Dl t.f t.f' (r + 1)) := hT.2.2.2.1
  have hG : IsUnit (H.Gdet t.f t.f' t.T t.T') := isUnit_Gdet H _ _ _ _ hT.2.2.2.2.1
  obtain ⟨s, hs, hdet⟩ := gram_det H t.f t.f' t.T t.T' hF hF' hD
  have hgu : IsUnit (H.gram (Sum.elim t.f t.f')).det := by
    have hsu : IsUnit s := ⟨⟨s, s, hs, hs⟩, rfl⟩
    have : (H.gram (Sum.elim t.f t.f')).det = H.Gdet t.f t.f' t.T t.T' * s := by
      rw [← hdet, mul_assoc, hs, mul_one]
    rw [this]
    exact hG.mul hsu
  rcases hsplit : M.split with _ | g
  · have hMM : H.MMfam t = Sum.elim t.f t.f' := by
      unfold HermSp.MMfam
      rw [hsplit]
    rw [hMM]
    exact hgu
  · set qi : E := algebraMap F E ((g.q : F)⁻¹)
    have hqi : IsUnit qi := ((Units.mk0 (g.q : F) (q_ne g))⁻¹.isUnit).map (algebraMap F E)
    have hMM : H.MMfam t = Sum.elim t.f (fun a => qi • (t.f' a - t.f a)) := by
      unfold HermSp.MMfam
      rw [hsplit]
    let A : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) E :=
      fromBlocks 1 (-(qi • (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E))) 0 (qi • 1)
    have hw : Sum.elim t.f (fun a => qi • (t.f' a - t.f a)) = fun j => ∑ i, A i j • Sum.elim t.f t.f' i := by
      funext j
      rcases j with a | a
      · simp [A, Fintype.sum_sum_type, Matrix.one_apply]
      · simp [A, Fintype.sum_sum_type, Matrix.one_apply, sub_eq_add_neg, add_comm]
    rw [hMM, hw, gram_recomb, det_mul, det_mul, det_transpose]
    have hA : A.det = qi ^ (r + 1) := by
      simp [A, det_fromBlocks_zero₂₁]
    have hAm : (A.map M.L.cj).det = M.L.cj A.det := by
      rw [show A.map M.L.cj = (M.L.cj.toRingEquiv.toRingHom).mapMatrix A from rfl, ← RingHom.map_det]
      rfl
    rw [hAm, hA]
    exact ((hqi.pow _).map M.L.cj).mul hgu |>.mul (hqi.pow _)

theorem exists_dual {ι : Type} [Fintype ι] [DecidableEq ι] (v : ι → V) (hG : IsUnit (H.gram v).det)
    (d : ι → E) : ∃ u ∈ Submodule.span E (Set.range v), ∀ i, H.h u (v i) = d i := by
  have hsum : ∀ (s : Finset ι) (c : ι → E) (y : V), H.h (∑ j ∈ s, c j • v j) y = ∑ j ∈ s, c j * H.h (v j) y := by
    intro s c y
    induction s using Finset.induction_on with
    | empty => simp [H.h_zero_left]
    | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, H.h_add_left, H.h_smul_left, ih]
  refine ⟨∑ j, ((H.gram v)⁻¹ *ᵥ d) j • v j, Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩), fun i => ?_⟩
  rw [hsum]
  have h1 : (H.gram v *ᵥ ((H.gram v)⁻¹ *ᵥ d)) i = d i := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hG, Matrix.one_mulVec]
  rw [← h1]
  simp only [Matrix.mulVec, dotProduct, Formalism.MainNotions.S.Loc.HermSp.gram, Matrix.of_apply]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem mem_MMsharp_of (t : Term V M r) {u : V} (hu : u ∈ Submodule.span E (Set.range (H.MMfam t)))
    (hd : ∀ i, H.h u (H.MMfam t i) ∈ M.L.O) : u ∈ MMsharp H t := by
  have hcj : ∀ c ∈ M.L.O, M.L.cj c ∈ M.L.O := by
    intro c hc
    rw [M.L.O_def] at hc ⊢
    exact hc.map ((M.L.cj : E →ₐ[F] E).restrictScalars 𝒪[F])
  refine ⟨hu, fun m hm => ?_⟩
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact hd i
  | zero =>
    rw [hR_zero]
    exact M.L.O.zero_mem
  | add a b _ _ ha hb =>
    rw [hR_add]
    exact M.L.O.add_mem ha hb
  | smul c x _ hx =>
    rw [Subring.smul_def, hR_smul]
    exact M.L.O.mul_mem (hcj c c.2) hx

theorem MMfam_G (g : SplitG M.L) (hs : M.split = some g) (t : Term V M r) :
    H.MMfam t = Sum.elim t.f (fun a => algebraMap F E ((g.q : F)⁻¹) • (t.f' a - t.f a)) := by
  simp only [Formalism.MainNotions.S.Loc.HermSp.MMfam, hs]

theorem f'_eq_G (g : SplitG M.L) (hs : M.split = some g) (t : Term V M r) (a : Fin (r + 1)) :
    t.f' a = t.f a + algebraMap F E (g.q : F) • H.MMfam t (Sum.inr a) := by
  rw [MMfam_G H g hs t, Sum.elim_inr, smul_smul, ← map_mul, mul_inv_cancel₀ (q_ne g), map_one, one_smul,
    add_sub_cancel]

theorem smul_mem_lat (g : SplitG M.L) (abelian₂ : Submodule M.L.O V) {x : V} (hx : x ∈ abelian₂) :
    algebraMap F E (g.q : F) • x ∈ abelian₂ := by
  have h1 := abelian₂.smul_mem (⟨algebraMap F E (g.q : F), q_mem_O g⟩ : M.L.O) hx
  exact h1

theorem iota_fst_of (hM : M.OK) (g : SplitG M.L) (hs : M.split = some g) (t : Term V M r) (hg : H.IsGeneric t)
    (hU : IsCompl (Submodule.span E (Set.range (Sum.elim t.f t.f'))) (H.W0 t.f t.f')) {x : V} (hx : x ∈ t.abelian₂)
    (hxp : x ∈ H.perp (H.X t.f)) :
    ∃ x' ∈ t.abelian₂, x' ∈ H.perp (H.X t.f') ∧ x - x' ∈ H.smulLat (algebraMap F E (g.q : F)) t.abelian₂ := by
  set c : E := algebraMap F E (g.q : F)
  have hGu := gramMM_unit_of_term H t hg.1
  let d : Fin (r + 1) ⊕ Fin (r + 1) → E := Sum.elim (fun a => H.h x (H.MMfam t (Sum.inr a))) 0
  obtain ⟨u, huS, hud⟩ := exists_dual H (H.MMfam t) hGu d
  have huM : u ∈ MMsharp H t := by
    refine mem_MMsharp_of H t huS fun i => ?_
    rw [hud]
    rcases i with a | a
    · exact (hg.1.1.2.2 x).1 hx _ (hg.2.1 (Sum.inr a))
    · exact M.L.O.zero_mem
  obtain ⟨w, hw⟩ := surj_MMsharp M hM H t hg hU ⟨u, huM⟩
  refine ⟨x - c • ((u : V) + w), t.abelian₂.sub_mem hx (smul_mem_lat g t.abelian₂ hw), ?_, ?_⟩
  · refine mem_perpX_of H fun j => ?_
    have hxf : H.h x (t.f j.castSucc) = 0 := hxp _ (Submodule.subset_span ⟨j, rfl⟩)
    have hyM : H.MMfam t (Sum.inr j.castSucc) ∈ Submodule.span E (Set.range (H.MMfam t)) :=
      Submodule.subset_span ⟨_, rfl⟩
    have hfM : t.f j.castSucc ∈ Submodule.span E (Set.range (H.MMfam t)) := by
      rw [MMfam_G H g hs]
      exact Submodule.subset_span ⟨Sum.inl j.castSucc, rfl⟩
    have hwf : H.h (w : V) (t.f j.castSucc) = 0 := hermitian_W0_span_zero H t w.2 hfM
    have hwy : H.h (w : V) (H.MMfam t (Sum.inr j.castSucc)) = 0 := hermitian_W0_span_zero H t w.2 hyM
    have hu1 : H.h u (t.f j.castSucc) = H.h x (H.MMfam t (Sum.inr j.castSucc)) := by
      have := hud (Sum.inl j.castSucc)
      simp only [d, Sum.elim_inl] at this
      rw [← this, MMfam_G H g hs, Sum.elim_inl]
    have hu2 : H.h u (H.MMfam t (Sum.inr j.castSucc)) = 0 := hud (Sum.inr j.castSucc)
    rw [f'_eq_G H g hs t, h_sub_left, H.h_smul_left, hR_add, hR_add, hR_smul, hR_smul, H.h_add_left,
      H.h_add_left, hxf, hwf, hwy, hu1, hu2, cj_q]
    ring
  · rw [sub_sub_cancel]
    exact Submodule.subset_span ⟨_, hw, rfl⟩

theorem iota_snd_of (hM : M.OK) (g : SplitG M.L) (hs : M.split = some g) (t : Term V M r) (hg : H.IsGeneric t)
    (hU : IsCompl (Submodule.span E (Set.range (Sum.elim t.f t.f'))) (H.W0 t.f t.f')) {x' : V} (hx : x' ∈ t.abelian₂)
    (hxp : x' ∈ H.perp (H.X t.f')) :
    ∃ x ∈ t.abelian₂, x ∈ H.perp (H.X t.f) ∧ x - x' ∈ H.smulLat (algebraMap F E (g.q : F)) t.abelian₂ := by
  set c : E := algebraMap F E (g.q : F)
  have hGu := gramMM_unit_of_term H t hg.1
  let d : Fin (r + 1) ⊕ Fin (r + 1) → E := Sum.elim (fun a => H.h x' (H.MMfam t (Sum.inr a))) 0
  obtain ⟨u, huS, hud⟩ := exists_dual H (H.MMfam t) hGu d
  have huM : u ∈ MMsharp H t := by
    refine mem_MMsharp_of H t huS fun i => ?_
    rw [hud]
    rcases i with a | a
    · exact (hg.1.1.2.2 x').1 hx _ (hg.2.1 (Sum.inr a))
    · exact M.L.O.zero_mem
  obtain ⟨w, hw⟩ := surj_MMsharp M hM H t hg hU ⟨u, huM⟩
  refine ⟨x' + c • ((u : V) + w), t.abelian₂.add_mem hx (smul_mem_lat g t.abelian₂ hw), ?_, ?_⟩
  · refine mem_perpX_of H fun j => ?_
    have hxf : H.h x' (t.f' j.castSucc) = 0 := hxp _ (Submodule.subset_span ⟨j, rfl⟩)
    have hyM : H.MMfam t (Sum.inr j.castSucc) ∈ Submodule.span E (Set.range (H.MMfam t)) :=
      Submodule.subset_span ⟨_, rfl⟩
    have hfM : t.f j.castSucc ∈ Submodule.span E (Set.range (H.MMfam t)) := by
      rw [MMfam_G H g hs]
      exact Submodule.subset_span ⟨Sum.inl j.castSucc, rfl⟩
    have hwf : H.h (w : V) (t.f j.castSucc) = 0 := hermitian_W0_span_zero H t w.2 hfM
    have hu1 : H.h u (t.f j.castSucc) = H.h x' (H.MMfam t (Sum.inr j.castSucc)) := by
      have := hud (Sum.inl j.castSucc)
      simp only [d, Sum.elim_inl] at this
      rw [← this, MMfam_G H g hs, Sum.elim_inl]
    have hxf2 : H.h x' (t.f j.castSucc) = - (c * H.h x' (H.MMfam t (Sum.inr j.castSucc))) := by
      have e := f'_eq_G H g hs t j.castSucc
      have : t.f j.castSucc = t.f' j.castSucc - c • H.MMfam t (Sum.inr j.castSucc) := by rw [e]; abel
      rw [this, hR_sub, hR_smul, hxf, cj_q]
      ring
    rw [H.h_add_left, H.h_smul_left, H.h_add_left, hxf2, hwf, hu1]
    ring
  · rw [add_sub_cancel_left]
    exact Submodule.subset_span ⟨_, hw, rfl⟩

theorem Lset_eq_snd (hM : M.OK) (g : SplitG M.L) (hs : M.split = some g) (t : Term V M r) (hg : H.IsGeneric t)
    (hU : IsCompl (Submodule.span E (Set.range (Sum.elim t.f t.f'))) (H.W0 t.f t.f')) :
    H.Lset t.abelian₂ t.f = Prod.snd '' H.iotaGraph g t := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨x', hx', hx'p, hd⟩ := iota_fst_of H hM g hs t hg hU hx x.2
    exact ⟨_, ⟨⟨x', hx'p⟩, x, hx', hx, hd, rfl⟩, rfl⟩
  · rintro _ ⟨_, ⟨x', x, -, hx, -, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩

theorem Lset_eq_fst (hM : M.OK) (g : SplitG M.L) (hs : M.split = some g) (t : Term V M r) (hg : H.IsGeneric t)
    (hU : IsCompl (Submodule.span E (Set.range (Sum.elim t.f t.f'))) (H.W0 t.f t.f')) :
    H.Lset t.abelian₂ t.f' = Prod.fst '' H.iotaGraph g t := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x', hx', rfl⟩
    obtain ⟨x, hx, hxp, hd⟩ := iota_snd_of H hM g hs t hg hU hx' x'.2
    exact ⟨_, ⟨x', ⟨x, hxp⟩, hx', hx, hd, rfl⟩, rfl⟩
  · rintro _ ⟨_, ⟨x', x, hx', -, -, rfl⟩, rfl⟩
    exact ⟨x', hx', rfl⟩

end RG1

end Formalism.L2.SG.LsDatumA
