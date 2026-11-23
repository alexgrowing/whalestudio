import Development.WeilBound.CoreStatements.VolumeEquality.BallVolDefs
import Development.WeilBound.CoreStatements.EqualVolumeCompactOpens.Master
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BallMobiusHolomorphicPotentialChangeStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BallMobiusMulStatement

noncomputable section

namespace SheetDecomposition

open NumberField Matrix MeasureTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.Dict
  GlobalTheory.CompanionTheory.Ar.Cusp.DictMeas PositivityTheory.EqVol

namespace Moeb

variable {Ψ : Type} [Fintype Ψ] {j j' n : ℕ}

theorem sgI_sq : sgI j j' * sgI j j' = 1 := by
  simp [sgI, fromBlocks_multiply]

theorem sgI_ct : (sgI j j')ᴴ = sgI j j' := by
  simp [sgI, fromBlocks_conjTranspose]

def sinv (u : Matrix (Sg j j') (Sg j j') ℂ) : Matrix (Sg j j') (Sg j j') ℂ := sgI j j' * uᴴ * sgI j j'

theorem sinv_mul {u : Matrix (Sg j j') (Sg j j') ℂ} (h : IsSgU u) : sinv u * u = 1 := by
  unfold IsSgU at h
  rw [sinv, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc uᴴ, h, sgI_sq]

theorem mul_sinv {u : Matrix (Sg j j') (Sg j j') ℂ} (h : IsSgU u) : u * sinv u = 1 :=
  mul_eq_one_comm.1 (sinv_mul h)

theorem sinv_su {u : Matrix (Sg j j') (Sg j j') ℂ} (h : IsSgU u) : IsSgU (sinv u) := by
  have h1 := mul_sinv h
  unfold IsSgU at h ⊢
  conv_lhs => rw [← h]
  have : (sinv u)ᴴ * (uᴴ * sgI j j' * u) * sinv u = (u * sinv u)ᴴ * sgI j j' * (u * sinv u) := by
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  rw [this, h1]
  simp

theorem moeb_one (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) : moebBall q (fun _ => 1) t = t := by
  funext k
  have : ∀ W : Matrix (Fin j') (Fin j) ℂ, moebW (1 : Matrix (Sg j j') (Sg j j') ℂ) W = W := fun W => by
    rw [moebW, ← fromBlocks_one, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂]
    simp
  simp [moebBall, ballPt, this, ballMat]

theorem moeb_maps (q : Ψ × Fin j × Fin j' ≃ Fin n) {u : Ψ → Matrix (Sg j j') (Sg j j') ℂ} (hu : ∀ τ, IsSgU (u τ))
    {t : Fin n → ℂ} (ht : t ∈ ballDom q) : moebBall q u t ∈ ballDom q :=
  (GlobalTheory.T.ball_mobius_holomorphic_potential_change Ψ j j' n q u hu).2.1 ht

theorem moeb_mul (q : Ψ × Fin j × Fin j' ≃ Fin n) {u v w : Ψ → Matrix (Sg j j') (Sg j j') ℂ} (hu : ∀ τ, IsSgU (u τ))
    (hv : ∀ τ, IsSgU (v τ)) (hw : ∀ τ, u τ * v τ = w τ) {t : Fin n → ℂ} (ht : t ∈ ballDom q) :
    moebBall q u (moebBall q v t) = moebBall q w t := by
  rw [← GlobalTheory.T.ball_mobius_mul Ψ j j' n q u v hu hv t ht, funext hw]

theorem moeb_inv (q : Ψ × Fin j × Fin j' ≃ Fin n) {u v : Ψ → Matrix (Sg j j') (Sg j j') ℂ} (hu : ∀ τ, IsSgU (u τ))
    (hv : ∀ τ, IsSgU (v τ)) (hw : ∀ τ, u τ * v τ = 1) {t : Fin n → ℂ} (ht : t ∈ ballDom q) :
    moebBall q u (moebBall q v t) = t :=
  (moeb_mul q hu hv hw ht).trans (moeb_one q t)

theorem moeb_injOn (q : Ψ × Fin j × Fin j' ≃ Fin n) {u : Ψ → Matrix (Sg j j') (Sg j j') ℂ} (hu : ∀ τ, IsSgU (u τ)) :
    Set.InjOn (moebBall q u) (ballDom q) := fun t ht t' ht' h => by
  rw [← moeb_inv q (fun τ => sinv_su (hu τ)) hu (fun τ => sinv_mul (hu τ)) ht, h,
    moeb_inv q (fun τ => sinv_su (hu τ)) hu (fun τ => sinv_mul (hu τ)) ht']

theorem moeb_meas (q : Ψ × Fin j × Fin j' ≃ Fin n) {u : Ψ → Matrix (Sg j j') (Sg j j') ℂ} (hu : ∀ τ, IsSgU (u τ))
    {S : Set (Fin n → ℂ)} (hS : MeasurableSet S) (hSD : S ⊆ ballDom q) :
    MeasurableSet (moebBall q u '' S) ∧ ballMeas q (moebBall q u '' S) = ballMeas q S := by
  obtain ⟨h1, h2, G, h3, h4⟩ := GlobalTheory.T.ball_mobius_holomorphic_potential_change Ψ j j' n q u hu
  exact ⟨hS.image_of_continuousOn_injOn (h1.continuousOn.mono hSD) ((moeb_injOn q hu).mono hSD),
    ballMeas_image q h1 h2 (moeb_injOn q hu) (fun t ht => ballDens_transform q h1 h3 h2 h4 ht) hS hSD⟩

def ren (q q' : Ψ × Fin j × Fin j' ≃ Fin n) : (Fin n → ℂ) ≃ᵐ (Fin n → ℂ) :=
  MeasurableEquiv.piCongrLeft (fun _ => ℂ) (q'.symm.trans q)

theorem ren_apply (q q' : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) (x : Ψ × Fin j × Fin j') :
    ren q q' t (q x) = t (q' x) := by
  have := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => ℂ) (q'.symm.trans q) t (q' x)
  simpa [ren] using this

theorem ballMat_ren (q q' : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) : ballMat q (ren q q' t) = ballMat q' t := by
  funext τ
  ext a b
  simp [ballMat, ren_apply]

theorem ren_mem (q q' : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) : ren q q' t ∈ ballDom q ↔ t ∈ ballDom q' := by
  simp only [ballDom, Set.mem_setOf_eq, ballMat_ren]

theorem moeb_ren (q q' : Ψ × Fin j × Fin j' ≃ Fin n) (u : Ψ → Matrix (Sg j j') (Sg j j') ℂ) (t : Fin n → ℂ) :
    moebBall q u (ren q q' t) = ren q q' (moebBall q' u t) := by
  funext k
  obtain ⟨x, rfl⟩ := q.surjective k
  rw [ren_apply]
  simp [moebBall, ballPt, ballMat_ren]

theorem ren_meas (q q' : Ψ × Fin j × Fin j' ≃ Fin n) {S : Set (Fin n → ℂ)} (hS : MeasurableSet S) (hSD : S ⊆ ballDom q') :
    ballMeas q (ren q q' '' S) = ballMeas q' S := by
  have hm : MeasurePreserving (ren q q') volume volume := volume_measurePreserving_piCongrLeft (fun _ => ℂ) _
  rw [ballMeas_apply q ((ren q q').measurableSet_image.2 hS) (by rintro _ ⟨t, ht, rfl⟩; exact (ren_mem q q' t).2 (hSD ht)),
    ballMeas_apply q' hS hSD, ← hm.setLIntegral_comp_emb (ren q q').measurableEmbedding]
  simp only [ballDens, ballPot, ballMat_ren]

theorem core (q : Ψ × Fin j × Fin j' ≃ Fin n) {G : Type} [Group G] [Countable G]
    (ρ : G → Ψ → Matrix (Sg j j') (Sg j j') ℂ) (U Γ Γ' : Subgroup G) (S S' : Set (Fin n → ℂ)) (h1 : ∀ τ, ρ 1 τ = 1)
    (hm : ∀ x y τ, ρ (x * y) τ = ρ x τ * ρ y τ) (hU : ∀ γ ∈ U, ∀ τ, IsSgU (ρ γ τ)) (hΓ : Γ ≤ U) (hΓ' : Γ' ≤ U)
    (hI : EqIdx Γ Γ') (hS : MFund q ρ Γ S) (hS' : MFund q ρ Γ' S') : ballMeas q S = ballMeas q S' := by
  have hD : MeasurableSet (ballDom q) := (BallInverse.isOpen_ballDom q).measurableSet
  have hemb : MeasurableEmbedding (Subtype.val : ballDom q → Fin n → ℂ) := MeasurableEmbedding.subtype_coe hD
  letI act : MulAction U (ballDom q) :=
    { smul := fun γ t => ⟨moebBall q (ρ γ) t, moeb_maps q (hU γ γ.2) t.2⟩
      one_smul := fun t => Subtype.ext (by
        show moebBall q (ρ 1) t = t
        rw [funext h1, moeb_one])
      mul_smul := fun a b t => Subtype.ext
        (moeb_mul q (hU a a.2) (hU b b.2) (fun τ => (hm a b τ).symm) t.2).symm }
  have sm : ∀ (γ : U) (t : ballDom q), ((γ • t : ballDom q) : Fin n → ℂ) = moebBall q (ρ γ) t := fun _ _ => rfl
  haveI : MeasurableConstSMul U (ballDom q) := ⟨fun γ =>
    (Continuous.subtype_mk (continuousOn_iff_continuous_restrict.1
      (GlobalTheory.T.ball_mobius_holomorphic_potential_change Ψ j j' n q (ρ γ) (hU γ γ.2)).1.continuousOn) _).measurable⟩
  let μ : Measure (ballDom q) := (ballMeas q).comap Subtype.val
  have hμ : ∀ s, μ s = ballMeas q (Subtype.val '' s) := fun s => hemb.comap_apply _ s
  haveI : SMulInvariantMeasure U (ballDom q) μ := ⟨fun γ s hs => by
    rw [hμ, hμ, ← (moeb_meas q (hU _ (γ⁻¹).2) (hemb.measurableSet_image.2 hs) (Subtype.coe_image_subset _ _)).2]
    congr 1
    ext t
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨_, ⟨γ • x, hx, rfl⟩, by rw [← sm, inv_smul_smul]⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨γ⁻¹ • x, by simpa using hx, rfl⟩⟩
  have fd : ∀ (Γ : Subgroup G) (S : Set (Fin n → ℂ)), Γ ≤ U → MFund q ρ Γ S →
      IsFundamentalDomain (Γ.subgroupOf U) (Subtype.val ⁻¹' S : Set (ballDom q)) μ ∧
        μ (Subtype.val ⁻¹' S) = ballMeas q S := fun Γ S hΓ ⟨a1, a2, a3, a4⟩ => by
    refine ⟨IsFundamentalDomain.mk' (hemb.measurable a1).nullMeasurableSet fun x => ?_, ?_⟩
    · obtain ⟨γ, hγ, h⟩ := a3 x x.2
      refine ⟨⟨⟨γ, hΓ hγ⟩, hγ⟩, h, fun g hg => ?_⟩
      have e : (g.1 * (⟨γ, hΓ hγ⟩ : U)⁻¹) • ((⟨γ, hΓ hγ⟩ : U) • x) = g.1 • x := by
        rw [← mul_smul, inv_mul_cancel_right]
      have := a4 _ h (g.1.1 * γ⁻¹) (Γ.mul_mem g.2 (Γ.inv_mem hγ)) (by
        have e' := congrArg Subtype.val e
        rw [sm, sm, sm] at e'
        exact e' ▸ hg)
      exact Subtype.ext (Subtype.ext (mul_inv_eq_one.1 this))
    · rw [hμ, Subtype.image_preimage_coe, Set.inter_eq_right.2 a2]
  obtain ⟨a₁, b₁⟩ := fd Γ S hΓ hS
  obtain ⟨a₂, b₂⟩ := fd Γ' S' hΓ' hS'
  rw [← b₁, ← b₂]
  exact fdEqual _ _ μ _ _ _ _
    (by rw [Subgroup.relIndex_subgroupOf hΓ, Subgroup.relIndex_subgroupOf hΓ']; exact hI.1)
    (by rw [Subgroup.relIndex_subgroupOf hΓ']; exact hI.2) a₁ a₂

end Moeb

open Moeb

theorem moebVol : MoebVol := by
  intro Ψ _ j j' n q q' G _ _ ρ ρ' w U Γ Γ' a S S' h1 hm hU hU' hw hc hΓ hΓ' hI hS ⟨b1, b2, b3, b4⟩
  have r1 : MeasurableSet (ren q q' '' S') := (ren q q').measurableSet_image.2 b1
  have r2 : ren q q' '' S' ⊆ ballDom q := by
    rintro _ ⟨t, ht, rfl⟩
    exact (ren_mem q q' t).2 (b2 ht)
  obtain ⟨m1, m2⟩ := moeb_meas q hw r1 r2
  have key : ∀ γ ∈ Γ', ∀ t ∈ ballDom q', moebBall q (ρ (a * γ * a⁻¹)) (moebBall q w (ren q q' t)) =
      moebBall q w (ren q q' (moebBall q' (ρ' γ) t)) := fun γ hγ t ht => by
    have ht' := (ren_mem q q' t).2 ht
    rw [← moeb_ren, moeb_mul q (hU (a * γ * a⁻¹) (hΓ' ⟨γ, hγ, rfl⟩)) hw (fun _ => rfl) ht',
      moeb_mul q hw (hU' γ hγ) (hc γ) ht']
  rw [← ren_meas q q' b1 b2, ← m2]
  refine core q ρ U Γ _ S _ h1 hm hU hΓ hΓ' hI hS ⟨m1, ?_, fun t ht => ?_, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    exact moeb_maps q hw (r2 ht)
  · have hi := fun τ => sinv_su (hw τ)
    obtain ⟨s, hs⟩ := (ren q q').surjective (moebBall q (fun τ => sinv (w τ)) t)
    have hs' : s ∈ ballDom q' := (ren_mem q q' s).1 (hs ▸ moeb_maps q hi ht)
    obtain ⟨γ, hγ, h⟩ := b3 s hs'
    refine ⟨a * γ * a⁻¹, ⟨γ, hγ, rfl⟩, _, ⟨_, h, rfl⟩, ?_⟩
    rw [← key γ hγ s hs', hs, moeb_inv q hw hi (fun τ => mul_sinv (hw τ)) ht]
  · rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩ _ ⟨γ, hγ, rfl⟩ ⟨_, ⟨s, hs, rfl⟩, e⟩
    replace e : moebBall q w (ren q q' s) = moebBall q (ρ (a * γ * a⁻¹)) (moebBall q w (ren q q' t)) := e
    rw [key γ hγ t (b2 ht)] at e
    have e2 := (ren q q').injective (moeb_injOn q hw ((ren_mem q q' _).2 (b2 hs))
      ((ren_mem q q' _).2 (moeb_maps q' (hU' γ hγ) (b2 ht))) e)
    obtain rfl := b4 t ht γ hγ (e2 ▸ hs)
    exact map_one _

end SheetDecomposition
