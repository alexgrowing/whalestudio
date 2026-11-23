import Development.WeilBound.ThetaLifts.SmallCones.ExpAlg
import Development.WeilBound.ThetaLifts.SmallCones.ExpSum

noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d n₁ d₁ m : ℕ} {B : Base F E} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}
  {M : Model σ X W} {M₁ : Model σ X₁ W₁} {ι : Matrix (Fin n) (Fin n₁) E} {ι' : Matrix (Fin d) (Fin d₁) E}
  {I : Set (Ten F E n d)} {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁} {u z : Fin m → Matrix (Fin n) (Fin d) E}

def rhoL (B : Base F E) (M : Model σ X W) (w : Ten F E n d) : Fn F n d →ₗ[ℂ] Fn F n d where
  toFun := M.co.rho B.ψ w
  map_add' := rho_add _ _ _
  map_smul' := rho_smul _ _ _

theorem slice_summable (hS : Slice) (hB : B.IsGood σ) (hM : M.IsGood B.ψ) (hM₁ : M₁.IsGood B.ψ) (he : IsEv B M M₁ ι ι' I e)
    (hD : Dual σ X W I u z) {l} (hl : l ∈ (adeleClass F).adm (Fin n₁ × Fin d₁)) {Φ} (hΦ : Φ ∈ schA F (Fin n × Fin d)) :
    Summable fun y : Fin m → F => l (e (rhoL B M (lin u fun j => algebraMap F (AF F) (y j)) Φ)) := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    obtain ⟨wt, P, h1, -, -, h2⟩ := slice_bound hS hB hM hM₁ he hD hl hg
    exact Summable.of_norm_bounded (h1.mul_left (P f)) fun y => h2 y f
  | zero => simpa using summable_zero
  | add Φ Ψ _ _ h1 h2 => simpa only [map_add] using h1.add h2
  | smul c Φ _ h => simpa only [map_smul, smul_eq_mul] using h.mul_left c

theorem slice_adm (hS : Slice) (hB : B.IsGood σ) (hM : M.IsGood B.ψ) (hM₁ : M₁.IsGood B.ψ) (he : IsEv B M M₁ ι ι' I e)
    (hD : Dual σ X W I u z) {l} (hl : l ∈ (adeleClass F).adm (Fin n₁ × Fin d₁)) :
    ∃ L ∈ (adeleClass F).adm (Fin n × Fin d), ∀ Φ ∈ schA F (Fin n × Fin d),
      HasSum (fun y : Fin m → F => l (e (M.co.rho B.ψ (lin u fun j => algebraMap F (AF F) (y j)) Φ))) (L Φ) := by
  let L₀ : schA F (Fin n × Fin d) →ₗ[ℂ] ℂ :=
    { toFun := fun Φ => ∑' y : Fin m → F, l (e (rhoL B M (lin u fun j => algebraMap F (AF F) (y j)) Φ.1))
      map_add' := fun Φ Ψ => by
        simp only [Submodule.coe_add, map_add]
        exact (slice_summable hS hB hM hM₁ he hD hl Φ.2).tsum_add (slice_summable hS hB hM hM₁ he hD hl Ψ.2)
      map_smul' := fun c Φ => by
        simp only [Submodule.coe_smul, map_smul, smul_eq_mul, RingHom.id_apply]
        exact tsum_mul_left }
  obtain ⟨L, hL⟩ := LinearMap.exists_extend L₀
  have hL' : ∀ Φ ∈ schA F (Fin n × Fin d),
      HasSum (fun y : Fin m → F => l (e (M.co.rho B.ψ (lin u fun j => algebraMap F (AF F) (y j)) Φ))) (L Φ) := fun Φ hΦ => by
    rw [show L Φ = L₀ ⟨Φ, hΦ⟩ from LinearMap.congr_fun hL ⟨Φ, hΦ⟩]
    exact (slice_summable hS hB hM hM₁ he hD hl hΦ).hasSum
  refine ⟨L, fun g hg => ?_, hL'⟩
  obtain ⟨wt, P, h1, h2, h3, h4⟩ := slice_bound hS hB hM hM₁ he hD hl hg
  let T : SInf F (Fin n × Fin d) →ₗ[ℂ] ℂ :=
    { toFun := fun f => L (pureA F f g)
      map_add' := fun f₁ f₂ => by
        rw [← map_add]; congr 1; funext x; simp [pureA, add_mul]
      map_smul' := fun c f => by
        rw [RingHom.id_apply, ← map_smul]; congr 1; funext x; simp [pureA, mul_assoc] }
  refine ⟨⟨T, continuous_of_continuousAt_zero T ?_⟩, fun f => rfl⟩
  rw [ContinuousAt, map_zero]
  refine squeeze_zero_norm (a := fun f => P f * ∑' y, wt y) (fun f => ?_) ?_
  · exact (hL' _ (Submodule.subset_span ⟨f, g, hg, rfl⟩)).norm_le_of_bounded (h1.hasSum.mul_left (P f)) fun y => h4 y f
  · simpa [h3] using (h2.tendsto 0).mul_const (∑' y, wt y)

theorem term_zero (h : IsStd B.ψ) (a : (Fin m → F) → Fn F n d → ℂ)
    (ha : ∀ y t, ∀ Φ ∈ schA F (Fin n × Fin d), a y (M.co.rho B.ψ (lin z t) Φ) =
      B.ψ (-((fun j => algebraMap F (AF F) (y j)) ⬝ᵥ t)) * a y Φ)
    (h0 : ∀ Φ ∈ schA F (Fin n × Fin d), HasSum (fun y => a y Φ) 0) (y) {Φ} (hΦ : Φ ∈ schA F (Fin n × Fin d)) : a y Φ = 0 := by
  refine fourier_uniq h (fun y => a y Φ) (h0 Φ hΦ).summable (fun t => ?_) y
  rw [← (h0 _ (rho_mem M h (lin z (-t)) hΦ)).tsum_eq]
  exact tsum_congr fun y => by rw [ha y _ Φ hΦ, dotProduct_neg, neg_neg, mul_comm]

theorem thetaExp_of (hS : Slice) : ThetaExp := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ M M₁ hB hM hM₁ ι ι' I e he m u z hP
  have h := hB.std
  obtain ⟨l, hl, hθ⟩ := (GlobalTheory.CompanionTheory.ThetaAdm.theta_adm F (Fin n₁ × Fin d₁)).2.1
  obtain ⟨L, hL, hs⟩ := slice_adm hS hB hM hM₁ he hP.toDual hl
  have hs' : ∀ Φ ∈ schA F (Fin n × Fin d), HasSum (fun y : Fin m → F =>
      thetaSum F (e (M.co.rho B.ψ (lin u fun j => algebraMap F (AF F) (y j)) Φ))) (L Φ) := fun Φ hΦ => by
    simpa only [hθ _ (he.maps _ (rho_mem M h _ hΦ))] using hs Φ hΦ
  have hu : ∀ a : Fin m → F, ∀ Φ ∈ schA F (Fin n × Fin d),
      L (M.co.rho B.ψ (lin u fun j => algebraMap F (AF F) (a j)) Φ) = L Φ := fun a Φ hΦ => by
    refine (hs' _ (rho_mem M h _ hΦ)).unique ?_
    have := (Equiv.addRight a).hasSum_iff.2 (hs' Φ hΦ)
    convert this using 2 with y
    rw [rho_rho_of _ _ _ _ (sy_lin_uu M hP _ _), ← lin_add]
    simp only [Function.comp_apply, Equiv.coe_addRight, Pi.add_apply, map_add]
    rfl
  have hz : ∀ b : Fin m → F, ∀ Φ ∈ schA F (Fin n × Fin d),
      L (M.co.rho B.ψ (lin z fun j => algebraMap F (AF F) (b j)) Φ) = L Φ := fun b Φ hΦ => by
    refine (hs' _ (rho_mem M h _ hΦ)).unique ?_
    convert hs' Φ hΦ using 2 with y
    rw [ev_rho_uz h he hP _ _ hΦ,
      show -((fun j => algebraMap F (AF F) (y j)) ⬝ᵥ fun j => algebraMap F (AF F) (b j)) = algebraMap F (AF F) (-(y ⬝ᵥ b)) by
        simp [dotProduct], h.2.1, one_smul]
  have hm : ∀ x₁ : Matrix (Fin n₁) (Fin d₁) E, ∀ Φ ∈ schA F (Fin n × Fin d),
      L (M.co.rho B.ψ (incM F ι * incM F x₁ * (incM F ι')ᵀ) Φ) = L Φ := fun x₁ Φ hΦ => by
    refine (hs' _ (rho_mem M h _ hΦ)).unique ?_
    convert hs' Φ hΦ using 2 with y
    obtain ⟨a, b, hab⟩ := hM₁.rat x₁
    rw [ev_rho_um h he hP _ _ hΦ, Darboux.rho, hab, theta_schr_rat h]
  obtain ⟨c, hc⟩ := thetaUniq_of F (Fin n × Fin d) B.ψ h L hL fun ξ η Φ hΦ => by
    obtain ⟨x, hx⟩ := rat_surj hB.cm.2.2.1 M.co.e hM.rat ξ η
    obtain ⟨a, b, x₁, hr⟩ := rho_rat (M := M) h hP x
    rw [← hx, ← Darboux.rho, hr, hu _ _ (rho_mem M h _ (rho_mem M h _ hΦ)), hz _ _ (rho_mem M h _ hΦ), hm _ _ hΦ]
  have hc0 : c ≠ 0 := by
    rintro rfl
    obtain ⟨Φ, hΦ, hne⟩ := ev_ne_zero hM hM₁ he
    refine hne (thetaInj_of F _ B.ψ h _ (he.maps Φ hΦ) fun w => ?_)
    obtain ⟨w, rfl⟩ := M₁.co.e.surjective w
    have := term_zero (M := M) (z := z) h
      (fun y Φ => thetaSum F (e (M.co.rho B.ψ (lin u fun j => algebraMap F (AF F) (y j)) Φ)))
      (fun y t Φ hΦ => by rw [ev_rho_uz h he hP _ _ hΦ, thetaSum_smul])
      (fun Φ hΦ => by simpa only [hc Φ hΦ, zero_mul] using hs' Φ hΦ) 0 (rho_mem M h (incM F ι * w * (incM F ι')ᵀ) hΦ)
    rwa [show (fun j => algebraMap F (AF F) ((0 : Fin m → F) j)) = 0 from funext fun j => map_zero _, lin_zero, rho_zero,
      he.Heisenberg₂ _ _ hΦ] at this
  refine ⟨c⁻¹, inv_ne_zero hc0, fun Φ hΦ => ?_⟩
  simpa only [hc Φ hΦ, inv_mul_cancel_left₀ hc0] using (hs' Φ hΦ).mul_left c⁻¹

theorem evUniq_of (hE : ThetaExp) : EvUniq := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ M M₁ hB hM hM₁ ι ι' I e e' he he' m u z hP
  have h := hB.std
  obtain ⟨C, hC, hs⟩ := hE F E σ B n d n₁ d₁ X W X₁ W₁ M M₁ hB hM hM₁ ι ι' I e he m u z hP
  obtain ⟨C', hC', hs'⟩ := hE F E σ B n d n₁ d₁ X W X₁ W₁ M M₁ hB hM hM₁ ι ι' I e' he' m u z hP
  refine ⟨C'⁻¹ * C, mul_ne_zero (inv_ne_zero hC') hC, fun Φ hΦ => ?_⟩
  have key : C • e Φ + (-C') • e' Φ = 0 := by
    refine thetaInj_of F _ B.ψ h _ (add_mem (Submodule.smul_mem _ _ (he.maps Φ hΦ)) (Submodule.smul_mem _ _ (he'.maps Φ hΦ)))
      fun w => ?_
    obtain ⟨w, rfl⟩ := M₁.co.e.surjective w
    have := term_zero (M := M) (z := z) h
      (fun y Φ => C * thetaSum F (e (M.co.rho B.ψ (lin u fun j => algebraMap F (AF F) (y j)) Φ)) -
        C' * thetaSum F (e' (M.co.rho B.ψ (lin u fun j => algebraMap F (AF F) (y j)) Φ)))
      (fun y t Φ hΦ => by rw [ev_rho_uz h he hP _ _ hΦ, ev_rho_uz h he' hP _ _ hΦ, thetaSum_smul, thetaSum_smul]; ring)
      (fun Φ hΦ => by simpa only [sub_self] using (hs Φ hΦ).sub (hs' Φ hΦ)) 0 (rho_mem M h (incM F ι * w * (incM F ι')ᵀ) hΦ)
    rw [show (fun j => algebraMap F (AF F) ((0 : Fin m → F) j)) = 0 from funext fun j => map_zero _, lin_zero, rho_zero,
      he.Heisenberg₂ _ _ hΦ, he'.Heisenberg₂ _ _ hΦ] at this
    rw [← Darboux.rho, rho_add, rho_smul, rho_smul,
      thetaSum_add F (Submodule.smul_mem _ _ (rho_mem M₁ h _ (he.maps Φ hΦ))) (Submodule.smul_mem _ _ (rho_mem M₁ h _ (he'.maps Φ hΦ))),
      thetaSum_smul, thetaSum_smul, ← this]
    ring
  rw [mul_smul, eq_neg_of_add_eq_zero_left key, neg_smul, neg_neg, smul_smul, inv_mul_cancel₀ hC', one_smul]

end PositivityTheory.ThKCT
