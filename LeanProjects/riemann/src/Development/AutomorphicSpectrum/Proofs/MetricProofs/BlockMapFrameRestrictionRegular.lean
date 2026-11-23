import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.UpVApply
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.PFl.Fwd

open GlobalTheory.CompanionTheory.Ar.PB.CPts GlobalTheory.CompanionTheory.Ar.PB.ValRing

section Lift

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

theorem val_lift_of {Ω Φ : Type} [Field Ω] [Field Φ] (φ : Ω →+* Φ) {κ : K → K'} {v : (Σ k, ι k) → Σ k, ι' k}
    (hb : IsBlockMap κ v) {x : (Σ k, ι k) → Ω} {y : (Σ k, ι' k) → Φ} (hy : y ∘ v = φ ∘ x)
    {z : (Σ k, ι' k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) {s : Ω} (hs : RegAt x (mCoordIdeal (z ∘ v)) s) :
    IsValueAt y (φ s) z (valAt x s (z ∘ v)) := by
  have hzb := comp_mem_mcPts hb φ hy hz
  obtain ⟨d, g, h, hg, hh, hn, heq⟩ := hs
  have hg' := isMultiHomog_rename_block hb hg
  have hh' := isMultiHomog_rename_block hb hh
  have hn' : rename v h ∉ mCoordIdeal z := rename_notMem hb hn
  have heq' : aeval y (rename v g) = φ s * aeval y (rename v h) := by
    rw [aeval_rename, aeval_rename, hy, aeval_comp_ringHom, aeval_comp_ringHom, heq, map_mul]
  have v1 : IsValueAt x s (z ∘ v) _ :=
    ⟨d, g, h, hg, hh, aeval_ne_zero_of_notMem hzb hh hn, heq, eval_ne_zero_of_notMem hh hn, rfl⟩
  have v2 : IsValueAt y (φ s) z _ :=
    ⟨_, _, _, hg', hh', aeval_ne_zero_of_notMem hz hh' hn', heq', eval_ne_zero_of_notMem hh' hn', rfl⟩
  rw [valAt_eq hzb v1]
  rw [eval_rename_block, eval_rename_block] at v2
  exact v2

end Lift

section Flag

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}
  {Kk : Type} [Fintype Kk] {ιk : Kk → Type} [∀ k, Fintype (ιk k)]

theorem exists_section (M : FlagModel y Ψ N j) {κ : Kk → K} {v : (Σ k, ιk k) → Σ k, ι k} (hb : IsBlockMap κ v)
    (hr : ∀ k, (∀ p, M.blk p ≠ some k) → k ∈ Set.range κ) :
    ∃ (κ' : NonPluckerBlocks M.blk → Kk) (v' : (Σ k, baseIdx ι M.blk k) → Σ k, ιk k), IsBlockMap κ' v' ∧
      ∀ q, v (v' q) = ⟨q.1.1, q.2⟩ := by
  choose κ' hκ' using fun k : NonPluckerBlocks M.blk => hr k.1 k.2
  have hq : ∀ q : Σ k, baseIdx ι M.blk k, ∃ p, v p = ⟨q.1.1, q.2⟩ := fun q =>
    hb.2.2.2 ⟨q.1.1, q.2⟩ ⟨κ' q.1, hκ' q.1⟩
  choose v' hv' using hq
  refine ⟨κ', v', ⟨fun a b h => Subtype.ext (by rw [← hκ' a, ← hκ' b, h]), fun a b h => ?_, fun q => ?_, ?_⟩, hv'⟩
  · have h' := congrArg v h
    rw [hv', hv'] at h'
    exact (blockMap_base M).2.1 h'
  · refine hb.1 ?_
    rw [hκ', ← hb.2.2.1, hv']
  · rintro ⟨k, i⟩ ⟨⟨kb, hkb⟩, rfl⟩
    rcases hvq : v ⟨κ' ⟨kb, hkb⟩, i⟩ with ⟨k₂, i₂⟩
    have hk₂ : k₂ = kb := by
      have h1 := hb.2.2.1 ⟨κ' ⟨kb, hkb⟩, i⟩
      rw [hvq] at h1
      exact h1.trans (hκ' ⟨kb, hkb⟩)
    subst hk₂
    refine ⟨⟨⟨k₂, hkb⟩, i₂⟩, hb.2.1 ?_⟩
    rw [hv', hvq]

theorem exists_pre {κ : Kk → K} {v : (Σ k, ιk k) → Σ k, ι k} (hb : IsBlockMap κ v) (k₁ : Kk) (m : ι (κ k₁)) :
    ∃ i : ιk k₁, v ⟨k₁, i⟩ = ⟨κ k₁, m⟩ := by
  obtain ⟨⟨k₂, i⟩, hp⟩ := hb.2.2.2 ⟨κ k₁, m⟩ ⟨k₁, rfl⟩
  have hk : k₂ = k₁ := hb.1 (by simpa [hp] using (hb.2.2.1 ⟨k₂, i⟩).symm)
  subst hk
  exact ⟨i, hp⟩

theorem ratio_up {κ : Kk → K} {v : (Σ k, ιk k) → Σ k, ι k} (hb : IsBlockMap κ v) {z : (Σ k, ιk k) → ℂ} {k₁ : Kk}
    {m c : ι (κ k₁)} (hy : y ⟨κ k₁, c⟩ ≠ 0) (hz : upV v z ⟨κ k₁, c⟩ ≠ 0) :
    IsValueAt (y ∘ v) (y ⟨κ k₁, m⟩ / y ⟨κ k₁, c⟩) z (upV v z ⟨κ k₁, m⟩ / upV v z ⟨κ k₁, c⟩) := by
  obtain ⟨im, hm⟩ := exists_pre hb k₁ m
  obtain ⟨ic, hc⟩ := exists_pre hb k₁ c
  rw [← hc] at hy hz ⊢
  rw [← hm]
  rw [upV_apply hb.2.1] at hz ⊢
  rw [upV_apply hb.2.1]
  exact isValueAt_ratio (y := y ∘ v) hy hz

theorem exists_coord {κ : Kk → K} {v : (Σ k, ιk k) → Σ k, ι k} (hb : IsBlockMap κ v) {z : (Σ k, ιk k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal (y ∘ v))) (k₁ : Kk) :
    ∃ c : ι (κ k₁), upV v z ⟨κ k₁, c⟩ ≠ 0 ∧ y ⟨κ k₁, c⟩ ≠ 0 := by
  obtain ⟨c₁, hc₁⟩ := hz.1 k₁
  have hy : (y ∘ v) ⟨k₁, c₁⟩ ≠ 0 := coord_ne hz hc₁
  have hex : ∃ c : ι (κ k₁), v ⟨k₁, c₁⟩ = ⟨κ k₁, c⟩ := by
    rcases hq : v ⟨k₁, c₁⟩ with ⟨kq, c⟩
    have h1 : kq = κ k₁ := by
      have h2 := hb.2.2.1 ⟨k₁, c₁⟩
      rw [hq] at h2
      exact h2
    subst h1
    exact ⟨c, rfl⟩
  obtain ⟨c, hc⟩ := hex
  refine ⟨c, ?_, ?_⟩
  · rw [← hc, upV_apply hb.2.1]
    exact hc₁
  · rw [← hc]
    exact hy

theorem flag_fwd_kept (M : FlagModel y Ψ N j) (keep : Ψ × Fin N → Prop) {κ : Kk → K} {v : (Σ k, ιk k) → Σ k, ι k}
    (hb : IsBlockMap κ v)
    (hrange : ∀ k, k ∈ Set.range κ ↔ ((∀ p, M.blk p ≠ some k) ∨ ∃ p, keep p ∧ M.blk p = some k))
    {F : FrameData ι Ψ N M.Ω M.blk} (hF : M.IsFrame F) {z : (Σ k, ιk k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal (y ∘ v))) (hG : M.GoodAt F (mCoordIdeal (pBase M v z))) :
    ∃ H : Ψ → Matrix (Fin N) (Fin N) ℂ, (∀ τ, IsBlockDiag j (H τ) ∧ (H τ).det ≠ 0) ∧
      ∀ p k, keep p → M.blk p = some k → ∃ α : ℂ, α ≠ 0 ∧ ∀ m : ι k,
        upV v z ⟨k, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) (pBase M v z) * minorIJ (H p.1) I (stepCols N j p.2) := by
  obtain ⟨κ', v', hb', hv'⟩ := exists_section M hb fun k h => (hrange k).2 (Or.inl h)
  let am := algebraMap M.Ω Φ
  have hx : (y ∘ v) ∘ v' = am ∘ M.x := funext fun q => by
    show y (v (v' q)) = am (M.x q)
    rw [hv']
    exact M.y_base q
  have hpb : pBase M v z = z ∘ v' := funext fun q => by
    show upV v z ⟨q.1.1, q.2⟩ = z (v' q)
    rw [← hv' q, upV_apply hb.2.1]
  rw [hpb] at hG ⊢
  have hzb : z ∘ v' ∈ mcPts (mCoordIdeal M.x) := comp_mem_mcPts hb' am hx hz
  let O := regRing (y ∘ v) z
  let val : O →+* ℂ := regVal hz
  obtain ⟨V, hOV, hpl⟩ := GlobalTheory.T.valuation_ring_extension_specialization Φ O val (regVal_local hz)
  have hO : ∀ {s}, RegAt M.x (mCoordIdeal (z ∘ v')) s → am s ∈ O := fun hs => ⟨_, val_lift_of am hb' hx hz hs⟩
  let Ag : Ψ → Matrix (Fin N) (Fin N) Φ := fun τ => (F.T τ)⁻¹.map am * M.g τ
  have hinvD : ∀ τ, ((F.T τ)⁻¹.map am).det ≠ 0 := fun τ => by
    have : ((F.T τ)⁻¹.map am).det = am ((F.T τ)⁻¹.det) := (RingHom.map_det am _).symm
    rw [this]
    refine (map_ne_zero am).2 fun h0 => ?_
    have h1 := Matrix.det_nonsing_inv_mul_det (F.T τ) (hF.1 τ).2.isUnit
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  have hAgB : ∀ τ, IsBlockDiag j (Ag τ) := fun τ =>
    (((hF.1 τ).1.inv (hF.1 τ).2.isUnit).map am).mul (M.g_block τ)
  have hAgD : ∀ τ, (Ag τ).det ≠ 0 := fun τ => by
    rw [Matrix.det_mul]
    exact mul_ne_zero (hinvD τ) (M.isUnit_det_g τ).ne_zero
  choose b hbB hbT hbd hbV hbdet hbinv using fun τ => GlobalTheory.T.block_diag_valuation_normalization Φ V N j (Ag τ) (hAgB τ) (hAgD τ)
  let H : Ψ → Matrix (Fin N) (Fin N) Φ := fun τ => Ag τ * b τ
  have hHB : ∀ τ, IsBlockDiag j (H τ) := fun τ => (hAgB τ).mul (hbB τ)
  let wf : ∀ (p : Ψ × Fin N) (k : K), ι k → Φ := fun p k m =>
    ∑ I, am (F.u ⟨k, m⟩ I) * minorIJ (H p.1) I (stepCols N j p.2)
  have data : ∀ p, ∃ wc : Φ, wc ∈ V ∧ wc ≠ 0 ∧ wc⁻¹ ∈ V ∧ ∀ k, keep p → M.blk p = some k →
      ∃ c : ι k, upV v z ⟨k, c⟩ ≠ 0 ∧
        ∀ m, ∃ r, IsValueAt (y ∘ v) r z (upV v z ⟨k, m⟩ / upV v z ⟨k, c⟩) ∧ wf p k m = r * wc := by
    intro p
    by_cases hkp : keep p
    swap
    · exact ⟨1, V.one_mem, one_ne_zero, by simpa using V.one_mem, fun k h => absurd h hkp⟩
    cases hp : M.blk p with
    | none => exact ⟨1, V.one_mem, one_ne_zero, by simpa using V.one_mem, fun k _ hk => by cases hk⟩
    | some k =>
      obtain ⟨k₁, rfl⟩ := (hrange k).2 (Or.inr ⟨p, hkp, hp⟩)
      obtain ⟨c, hzc, hyc⟩ := exists_coord hb hz k₁
      have hdet : am (detFac j p.2 (F.T p.1)) ≠ 0 :=
        (map_ne_zero am).2 (detFac_ne_zero M.j_le p.2 (hF.1 p.1).1 (hF.1 p.1).2)
      have hE : am (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b p k') ≠ 0 := (map_ne_zero am).2 (Finset.prod_ne_zero_iff.2 fun k' _ =>
        zpow_ne_zero _ (M.x_chart_ne (mCoordIdeal_le hzb) hG k'))
      have hB : (∏ c ∈ stepCols N j p.2, b p.1 c c) ≠ 0 := Finset.prod_ne_zero_iff.2 fun c _ => hbd p.1 c
      have rel : ∀ m, am (detFac j p.2 (F.T p.1)) * (∏ c ∈ stepCols N j p.2, b p.1 c c) * y ⟨κ k₁, m⟩ =
          am (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b p k') * wf p (κ k₁) m := fun m =>
        frame_gen M hF (RingHom.id Φ) hp m (hHB p.1) (hbB p.1) (hbT p.1) (by
          show (F.T p.1).map am * ((F.T p.1)⁻¹.map am * M.g p.1 * b p.1) = (M.g p.1).map (RingHom.id Φ) * b p.1
          rw [Matrix.mul_assoc ((F.T p.1)⁻¹.map am), map_mul_inv_map am (hF.1 p.1).2]
          rfl)
      obtain ⟨e, he, hw⟩ : ∃ e : Φ, e ≠ 0 ∧ ∀ m, wf p (κ k₁) m = e * y ⟨κ k₁, m⟩ :=
        ⟨am (detFac j p.2 (F.T p.1)) * (∏ c ∈ stepCols N j p.2, b p.1 c c) / am (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b p k'),
          div_ne_zero (mul_ne_zero hdet hB) hE, fun m => by
            rw [div_mul_eq_mul_div, rel m, mul_div_cancel_left₀ _ hE]⟩
      obtain ⟨m₀, hm₀, hm₀i⟩ := GlobalTheory.T.step_rows_inverse_nonzero_entry Φ V N j p.2 (H p.1) (ι (κ k₁)) (fun m I => am (F.u ⟨κ k₁, m⟩ I))
        (fun I m => am (F.u' I ⟨κ k₁, m⟩)) M.j_le (hHB p.1) (hbV p.1) (hbdet p.1) (hbinv p.1)
        (fun I m => hOV _ (hO (hG.2.1 _ I).2)) (fun m I => hOV _ (hO (hG.2.1 _ I).1)) (fun I I' hI hI' => by
          have := congrArg am (hF.2.2.1 p (κ k₁) hp I I' hI hI')
          rw [map_sum] at this
          simp only [map_mul] at this
          rw [this]
          split_ifs <;> simp)
      have hwc : wf p (κ k₁) c ≠ 0 := by rw [hw]; exact mul_ne_zero he hyc
      have hr : ∀ m, wf p (κ k₁) m = y ⟨κ k₁, m⟩ / y ⟨κ k₁, c⟩ * wf p (κ k₁) c := fun m => by
        rw [hw, hw]
        field_simp
      refine ⟨wf p (κ k₁) c, ?_, hwc, ?_, fun k' _ hk' => ?_⟩
      · exact sum_mem fun I _ => V.mul_mem _ _ (hOV _ (hO (hG.2.1 _ I).1)) (minorIJ_mem V.toSubring (hbV p.1) I _)
      · have h1 : y ⟨κ k₁, m₀⟩ / y ⟨κ k₁, c⟩ ∈ O := ⟨_, ratio_up hb hyc hzc⟩
        have h2 : (wf p (κ k₁) c)⁻¹ = y ⟨κ k₁, m₀⟩ / y ⟨κ k₁, c⟩ * (wf p (κ k₁) m₀)⁻¹ := by
          have hm₀' : wf p (κ k₁) m₀ ≠ 0 := hm₀
          rw [hr m₀] at hm₀' ⊢
          have h3 := left_ne_zero_of_mul hm₀'
          rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ h3, one_mul]
        rw [h2]
        exact V.mul_mem _ _ (hOV _ h1) hm₀i
      · obtain rfl := Option.some.inj hk'
        exact ⟨c, hzc, fun m => ⟨_, ratio_up hb hyc hzc, hr m⟩⟩
  choose wc hwV hw0 hwinv hdat using data
  let T : Finset Φ := (Finset.univ.image fun t : Ψ × Fin N × Fin N => H t.1 t.2.1 t.2.2) ∪
    (Finset.univ.image fun τ => (H τ).det) ∪ (Finset.univ.image wc)
  have hT1 : ∀ τ a c, H τ a c ∈ T := fun τ a c => Finset.mem_union_left _ (Finset.mem_union_left _
    (Finset.mem_image.2 ⟨(τ, a, c), Finset.mem_univ _, rfl⟩))
  have hT2 : ∀ τ, (H τ).det ∈ T := fun τ => Finset.mem_union_left _ (Finset.mem_union_right _
    (Finset.mem_image.2 ⟨τ, Finset.mem_univ _, rfl⟩))
  have hT3 : ∀ p, wc p ∈ T := fun p => Finset.mem_union_right _ (Finset.mem_image.2 ⟨p, Finset.mem_univ _, rfl⟩)
  have hTV : ∀ t ∈ T, t ∈ V := fun t ht => by
    rcases Finset.mem_union.1 ht with ht | ht
    · rcases Finset.mem_union.1 ht with ht | ht
      · obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 ht
        exact hbV _ _ _
      · obtain ⟨τ, -, rfl⟩ := Finset.mem_image.1 ht
        exact det_mem V.toSubring (hbV τ)
    · obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 ht
      exact hwV p
  obtain ⟨R, hOR, ψ, hTR, hψ, hinv⟩ := hpl T hTV
  let HR : Ψ → Matrix (Fin N) (Fin N) R := fun τ => Matrix.of fun a c => ⟨H τ a c, hTR _ (hT1 τ a c)⟩
  have hHR : ∀ τ, (HR τ).map R.subtype = H τ := fun τ => by ext a c; rfl
  refine ⟨fun τ => (HR τ).map ψ, fun τ => ⟨?_, ?_⟩, fun p k hkp hp => ?_⟩
  · intro a c hac
    have h0 : HR τ a c = 0 := Subtype.ext (hHB τ a c hac)
    show ψ (HR τ a c) = 0
    rw [h0, map_zero]
  · have e1 : R.subtype (HR τ).det = (H τ).det := by rw [RingHom.map_det]; exact congrArg _ (hHR τ)
    have e2 : (HR τ).det * ⟨(H τ).det⁻¹, hinv _ (hT2 τ) (hbdet τ) (hbinv τ)⟩ = 1 := Subtype.ext (by
      show R.subtype (HR τ).det * (H τ).det⁻¹ = 1
      rw [e1, mul_inv_cancel₀ (hbdet τ)])
    have e3 := congrArg ψ e2
    rw [map_mul, map_one, RingHom.map_det] at e3
    exact left_ne_zero_of_mul_eq_one e3
  · obtain ⟨c, hzc, hm⟩ := hdat p k hkp hp
    let wR : R := ⟨wc p, hTR _ (hT3 p)⟩
    have hβ : ψ wR ≠ 0 := by
      have e2 : wR * ⟨(wc p)⁻¹, hinv _ (hT3 p) (hw0 p) (hwinv p)⟩ = 1 := Subtype.ext (mul_inv_cancel₀ (hw0 p))
      have e3 := congrArg ψ e2
      rw [map_mul, map_one] at e3
      exact left_ne_zero_of_mul_eq_one e3
    refine ⟨upV v z ⟨k, c⟩ / ψ wR, div_ne_zero hzc hβ, fun m => ?_⟩
    obtain ⟨r, hr, hw⟩ := hm m
    let uR : Finset (Fin N) → R := fun I => Subring.inclusion hOR ⟨am (F.u ⟨k, m⟩ I), hO (hG.2.1 _ I).1⟩
    let rR : R := Subring.inclusion hOR ⟨r, _, hr⟩
    have e1 : ∑ I, uR I * minorIJ (HR p.1) I (stepCols N j p.2) = rR * wR := Subtype.ext (by
      show R.subtype _ = r * wc p
      rw [map_sum]
      simp only [map_mul, ← minorIJ_map, hHR]
      exact hw)
    have e2 := congrArg ψ e1
    rw [map_sum] at e2
    simp only [map_mul, ← minorIJ_map] at e2
    have e3 : ∀ I, ψ (uR I) = valAt M.x (F.u ⟨k, m⟩ I) (z ∘ v') := fun I =>
      (hψ _).trans (regVal_eq hz _ (val_lift_of am hb' hx hz (hG.2.1 _ I).1))
    have e4 : ψ rR = upV v z ⟨k, m⟩ / upV v z ⟨k, c⟩ := (hψ _).trans (regVal_eq hz _ hr)
    simp only [e3] at e2
    rw [e4] at e2
    show upV v z ⟨k, m⟩ = _ * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) (z ∘ v') * minorIJ ((HR p.1).map ψ) I (stepCols N j p.2)
    rw [e2]
    field_simp

end Flag

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (keep : Ψ × Fin N → Prop) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)), IsBlockMap κ v → (∀ k, k ∈ Set.range κ ↔ ((∀ p, M.blk p ≠ some k) ∨ ∃ p, keep p ∧ M.blk p = some k)) → ∀ (F : FrameData ι Ψ N M.Ω M.blk) (z : (Σ k, ιk k) → ℂ), M.IsFrame F → z ∈ mcPts (mCoordIdeal (y ∘ v)) → M.GoodAt F (mCoordIdeal (pBase M v z)) → (∀ k, pBase M v z ⟨k, F.c k⟩ = 1) → ∃ H : Ψ → Matrix (Fin N) (Fin N) ℂ, (∀ τ, IsBlockDiag j (H τ) ∧ (H τ).det ≠ 0) ∧ ∀ p k, keep p → M.blk p = some k → ∃ α : ℂ, α ≠ 0 ∧ ∀ m : ι k, upV v z ⟨k, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) (pBase M v z) * minorIJ (H p.1) I (stepCols N j p.2) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M keep Kk _ ιk _ κ v hb hrange F z hF hz hG _
  exact flag_fwd_kept M keep hb hrange hF hz hG

end GlobalTheory.CompanionTheory.Ar.PB.PFl.Fwd
