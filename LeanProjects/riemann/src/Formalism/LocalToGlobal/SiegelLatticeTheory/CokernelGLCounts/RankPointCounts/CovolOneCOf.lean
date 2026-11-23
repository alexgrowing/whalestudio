import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ChartC

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.NGCut.SplitEmbedding

namespace Formalism.L2.SG.NGCut.StabilizerCovolume

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem covolOneC_of (hC : ChartC) (hL : LatC) : Formalism.L2.SG.Pf.VolPinAsm.CovolOneC := by
  intro D X Y u u' t hrel hG w hat F' L U hNR γw s s' μw hIs hs hs' hpt hHaar hmap c Φ hD
  obtain ⟨BX, hBm, hBd, hB0, hstm, hStm, hinj, hsurj, hmul, hconj⟩ :=
    hC D X Y u u' t hrel hG w hat γw s s' hIs hs hs' hpt
  have hΦR : ∀ β, c⁻¹ * Φ β * c ∈ Formalism.L2.SG.TermOp.Vanish.Rset t := hD.2.1
  obtain ⟨σ, h', I, Λ, k, τ, σι, hh', hφ, hΛ, hk, hk0, hs0, hτ, hset, hc0, hconst⟩ :=
    hL D X Y u u' t hrel hG w hat F' L U hNR γw s s' hIs hs hs' hpt c Φ hD
  have hTC := Formalism.MainNotions.InterlacingSignCuts.host_totallyComplex D
  have : IsEmpty {w : InfinitePlace D.host.E // w.IsReal} :=
    ⟨fun w => (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w.1)) w.2⟩
  set St := Formalism.L2.SG.RealObj.StInf X u u' γw with hStdef
  set sc := Formalism.L2.SG.RealObj.stCoord X u' w γw with hscdef
  let gβ : Formalism.L2.SG.Pf.VolPinAsm.StG w → X.B.I.Ginf := fun β => s⁻¹ * (c⁻¹ * Φ β * c) * s
  have hgSt : ∀ β, gβ β ∈ St := fun β => hconj _ (hΦR β)
  have hg_inv : ∀ β, gβ β⁻¹ = (gβ β)⁻¹ := by
    intro β; simp only [gβ, map_inv]; group
  have hg_mul : ∀ β (y : X.B.I.Ginf), s⁻¹ * (c⁻¹ * (Φ β * y) * c) * s = gβ β * (s⁻¹ * (c⁻¹ * y * c) * s) := by
    intro β y; simp only [gβ]; group
  let A : Formalism.L2.SG.RealObj.FreeE w → AddSubgroup (InfinitePlace X.B.I.F → ℂ) :=
    fun p => (Λ p).map (Formalism.L2.SG.NGCut.SplitEmbedding.embS (Formalism.L2.SG.Pf.VolPinAsm.phiV X) (σ p))
  have hΓ : ∀ x, (∀ p, (fun v => x v p) - τ p x ∈ A p) ↔
      ∃ β : Formalism.L2.SG.Pf.VolPinAsm.StG w, (β : Formalism.L2.SG.PairVal.GLR D) ∈ Formalism.L2.SG.PairVal.stabInt D u u' Y.δ Y.M w ∧
        x = sc (gβ β) := by
    intro x
    exact (hset x).symm
  have hBd' : ∀ p (x x' y y' : Formalism.L2.SG.RealObj.FreeE w → ℂ), (∀ q, h' q < h' p → x q = x' q ∧ y q = y' q) →
      BX p x y = BX p x' y' :=
    fun p x x' y y' hxy => hBd p x x' y y' fun q hq => hxy q (hh' p q hq)
  have hinv : ∀ γ, (∀ p, (fun v => γ v p) - τ p γ ∈ A p) → ∃ γ', (∀ p, (fun v => γ' v p) - τ p γ' ∈ A p) ∧
      ∀ x, lawX BX γ' (lawX BX γ x) = x ∧ lawX BX γ (lawX BX γ' x) = x := by
    intro γ hγ
    obtain ⟨β, hβ, rfl⟩ := (hΓ γ).1 hγ
    have hβi : ((β⁻¹ : Formalism.L2.SG.Pf.VolPinAsm.StG w) : Formalism.L2.SG.PairVal.GLR D) ∈
        Formalism.L2.SG.PairVal.stabInt D u u' Y.δ Y.M w := by
      rw [Subgroup.coe_inv]; exact Subgroup.inv_mem _ hβ
    refine ⟨sc (gβ β⁻¹), (hΓ _).2 ⟨β⁻¹, hβi, rfl⟩, fun x => ?_⟩
    obtain ⟨z, hz, rfl⟩ := hsurj x
    have h1 := hmul (gβ β) (hgSt β) z hz
    have h1' := hmul (gβ β⁻¹) (hgSt _) z hz
    constructor
    · have h2 := hmul (gβ β⁻¹) (hgSt _) (gβ β * z) h1.1
      rw [← h1.2, ← h2.2, hg_inv, inv_mul_cancel_left]
    · have h2 := hmul (gβ β) (hgSt β) (gβ β⁻¹ * z) h1'.1
      rw [← h1'.2, ← h2.2, hg_inv, mul_inv_cancel_left]

  have hfd : ∀ p, ∃ F : Set (InfinitePlace X.B.I.F → ℂ), MeasurableSet F ∧
      ∀ v, ∃! b : A p, (b : InfinitePlace X.B.I.F → ℂ) + v ∈ F := by
    intro p
    obtain ⟨F, hF, hFd⟩ := exists_fd D.host.E (InfinitePlace X.B.I.F) (Formalism.L2.SG.Pf.VolPinAsm.phiV X) σι hφ (I p) (Λ p)
      (hΛ p) (by rw [hk p]; exact hk0 p) (σ p) (hs0 p)
    refine ⟨F, hF, fun v => ?_⟩
    obtain ⟨a, ha, hau⟩ := hFd v
    refine ⟨⟨Formalism.L2.SG.NGCut.SplitEmbedding.embS (Formalism.L2.SG.Pf.VolPinAsm.phiV X) (σ p) a, AddSubgroup.mem_map_of_mem _ a.2⟩, ha, ?_⟩
    rintro ⟨y, hy⟩ hyF
    obtain ⟨a', ha', rfl⟩ := AddSubgroup.mem_map.1 hy
    have := hau ⟨a', ha'⟩ hyF
    apply Subtype.ext
    show Formalism.L2.SG.NGCut.SplitEmbedding.embS (Formalism.L2.SG.Pf.VolPinAsm.phiV X) (σ p) a' = Formalism.L2.SG.NGCut.SplitEmbedding.embS (Formalism.L2.SG.Pf.VolPinAsm.phiV X) (σ p) a
    rw [show a' = (a : D.host.E) from congrArg Subtype.val this]
  choose F hF hFd using hfd
  set K' : Set (InfinitePlace X.B.I.F → Formalism.L2.SG.RealObj.FreeE w → ℂ) := {y | ∀ p, (fun v => y v p) ∈ F p} with hK'def
  have hK'm : MeasurableSet K' := by
    rw [hK'def, Set.setOf_forall]
    exact MeasurableSet.iInter fun p =>
      (measurable_pi_lambda _ fun v => (measurable_pi_apply p).comp (measurable_pi_apply v)) (hF p)
  have hKd := box_fundX h' BX hBd' τ hτ A F hFd
  have hone := covol_one_eq_one D.host.E (InfinitePlace X.B.I.F) (Formalism.L2.SG.Pf.VolPinAsm.phiV X) σι hφ
    (Formalism.L2.SG.RealObj.FreeE w) h' BX hBm hBd' hB0 _ hc0 I Λ hΛ k hk hk0 σ hs0 hconst τ hτ hinv K' hK'm hKd

  have hQm : Measurable (fun y : X.B.I.Ginf => s⁻¹ * (c⁻¹ * y * c) * s) :=
    ((continuous_const.mul ((continuous_const.mul continuous_id).mul continuous_const)).mul continuous_const).measurable
  set KA := (fun y : X.B.I.Ginf => s⁻¹ * (c⁻¹ * y * c) * s) ⁻¹' (St ∩ sc ⁻¹' K') with hKAdef
  have hKAm : MeasurableSet KA := hQm (hStm.inter (hstm hK'm))
  refine ⟨KA, hKAm, fun y hy => ?_, ?_⟩
  · set z := s⁻¹ * (c⁻¹ * y * c) * s
    have hz : z ∈ St := hconj _ hy
    obtain ⟨γ, ⟨hγΓ, hγK⟩, hγu⟩ := hKd (sc z)
    obtain ⟨β, hβ, rfl⟩ := (hΓ γ).1 hγΓ
    refine ⟨Φ β, ⟨⟨β, (Subgroup.mem_subgroupOf).2 hβ, rfl⟩, ?_⟩, ?_⟩
    · show s⁻¹ * (c⁻¹ * (Φ β * y) * c) * s ∈ St ∩ sc ⁻¹' K'
      rw [hg_mul]
      have h1 := hmul (gβ β) (hgSt β) z hz
      exact ⟨h1.1, by show sc (gβ β * z) ∈ K'; rw [h1.2]; exact hγK⟩
    · rintro x' ⟨hx'm, hx'K⟩
      obtain ⟨β', hβ', rfl⟩ := Subgroup.mem_map.1 hx'm
      have hβ'' : (β' : Formalism.L2.SG.PairVal.GLR D) ∈ Formalism.L2.SG.PairVal.stabInt D u u' Y.δ Y.M w :=
        (Subgroup.mem_subgroupOf).1 hβ'
      have hK2 : s⁻¹ * (c⁻¹ * (Φ β' * y) * c) * s ∈ St ∩ sc ⁻¹' K' := hx'K
      rw [hg_mul] at hK2
      have h1 := hmul (gβ β') (hgSt β') z hz
      have hin : lawX BX (sc (gβ β')) (sc z) ∈ K' := by rw [← h1.2]; exact hK2.2
      have heq := hγu (sc (gβ β')) ⟨(hΓ _).2 ⟨β', hβ'', rfl⟩, hin⟩
      have hgg : gβ β' = gβ β := hinj (hgSt β') (hgSt β) heq
      have : Φ β' = Φ β := by
        have e : c⁻¹ * Φ β' * c = c⁻¹ * Φ β * c := by
          have := congrArg (fun g => s * g * s⁻¹) hgg
          simpa [gβ, mul_assoc] using this
        have := congrArg (fun g => c * g * c⁻¹) e
        simpa [mul_assoc] using this
      exact this
  · have hc1m : Measurable (fun y : X.B.I.Ginf => c * y * c⁻¹) :=
      ((continuous_const.mul continuous_id).mul continuous_const).measurable
    have hs1m : Measurable (fun y : X.B.I.Ginf => s * y * s⁻¹) :=
      ((continuous_const.mul continuous_id).mul continuous_const).measurable
    rw [Measure.map_apply hc1m hKAm, Measure.map_apply hs1m (hc1m hKAm)]
    have hset' : (fun y : X.B.I.Ginf => s * y * s⁻¹) ⁻¹' ((fun y : X.B.I.Ginf => c * y * c⁻¹) ⁻¹' KA) =
        St ∩ sc ⁻¹' K' := by
      ext y
      simp only [Set.mem_preimage, hKAdef]
      have e : s⁻¹ * (c⁻¹ * (c * (s * y * s⁻¹) * c⁻¹) * c) * s = y := by group
      rw [e]
    rw [hset', Set.inter_comm, measure_inter_conull hHaar.2.2.1, ← Measure.map_apply hstm hK'm, hmap]
    exact hone

end Formalism.L2.SG.NGCut.StabilizerCovolume
