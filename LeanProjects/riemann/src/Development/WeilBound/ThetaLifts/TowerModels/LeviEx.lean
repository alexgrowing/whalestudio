import Development.WeilBound.ThetaLifts.TowerModels.PlaneHerm
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.PlaneRemovalConfiguration
import Development.WeilBound.ThetaLifts.ConeHypotheses.PolDense
import Development.WeilBound.ThetaLifts.TowerModels.LeviAd
import Development.WeilBound.ThetaLifts.TowerModels.ExistsRefl

noncomputable section

namespace PositivityTheory.ThKG.Tow

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace Levi

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {B : Base F E} {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H : Plane E d d₁} {i₀ i₁ r s : ℕ}

theorem exists_loc (hB : B.IsGood σ) (hW : W.IsSkew σ B r s) (hH : H.IsAdapted σ B W W₁ i₀ i₁) (w : InfinitePlace F)
    {g g' : Matrix (Fin d) (Fin d) ℂ} (h1 : g * g' = 1)
    (h2 : gᵀ * W.J.map (B.emb w).1 * g.map star = W.J.map (B.emb w).1) :
    ∃ (p p' : Matrix (Fin d) (Fin d) ℂ) (t : ℂ), t ≠ 0 ∧ p * p' = 1 ∧
      pᵀ * W.J.map (B.emb w).1 * p.map star = W.J.map (B.emb w).1 ∧
      (p *ᵥ fun i => (B.emb w).1 (H.x i)) = t • (fun i => (B.emb w).1 (H.x i)) ∧ Commute (p' * g) (W.θ w) := by
  set τ := (B.emb w).1 with hτ
  set M := Complex.I • W.J.map τ with hM
  have hiso : ∀ k : Matrix (Fin d) (Fin d) ℂ, kᵀ * M * k.map star = M ↔ kᵀ * W.J.map τ * k.map star = W.J.map τ := fun k => by
    rw [hM, Matrix.mul_smul, Matrix.smul_mul]
    exact (smul_right_injective _ Complex.I_ne_zero).eq_iff
  have hherm : ∀ i j, star (M j i) = M i j := fun i j => by
    have := hB.cm.2.2.2 τ (W.J j i)
    rw [hW.skew, map_neg] at this
    simp only [hM, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, star_mul', ← this]
    simp
  obtain ⟨c1, c2, c3⟩ := hW.cartan w
  set v : Fin d → ℂ := fun i => τ (H.x i) with hv
  have hv0 : v ≠ 0 := fun h => by
    have : H.x = 0 := funext fun i => τ.injective ((congrFun h i).trans (map_zero τ).symm)
    have e := hH.xy
    rw [this, form, zero_dotProduct] at e
    exact zero_ne_one e
  have hvv : hf M v v = 0 := by
    have e := congrArg τ hH.xx
    simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hB.cm.2.2.2, map_zero] at e
    rw [hf_apply, hM, Matrix.smul_mulVec, dotProduct_smul]
    exact smul_eq_zero_of_right _ e
  have hgv : g *ᵥ (g' *ᵥ v) = v := by rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  obtain ⟨κ, t, ht, k1, k2, k3⟩ := exists_move hherm c1 c2 c3 hv0 (v' := g' *ᵥ v)
    (fun h => hv0 (by rw [← hgv, h, Matrix.mulVec_zero]))
    hvv (by rw [← (hiso g).2 h2, ← hf_mulVec, hgv, hvv])
  have hκ : IsUnit κ.det := by
    have e := congrArg Matrix.det ((hiso κ).1 k1)
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at e
    refine IsUnit.mk0 _ fun h => det_ne_zero hW (τ.injective ?_)
    rw [h, zero_mul, zero_mul] at e
    rw [RingHom.map_det, map_zero]
    exact e.symm
  have h1' := mul_eq_one_comm.1 h1
  refine ⟨g * κ, κ⁻¹ * g', t, ht, ?_, (hiso _).1 (iso_of_hf fun x y => ?_), ?_, ?_⟩
  · rw [mul_assoc, ← mul_assoc κ, Matrix.mul_nonsing_inv _ hκ, one_mul, h1]
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hf_mulVec, (hiso g).2 h2, hf_mulVec, k1]
  · rw [← Matrix.mulVec_mulVec, k3, Matrix.mulVec_smul, hgv]
  · rw [mul_assoc, h1', mul_one]
    obtain ⟨u, rfl⟩ := (Matrix.isUnit_iff_isUnit_det κ).2 hκ
    rw [← Matrix.coe_units_inv]
    exact k2.units_inv_left

theorem exists_stab (hB : B.IsGood σ) (hW : W.IsSkew σ B r s) (hH : H.IsAdapted σ B W W₁ i₀ i₁) (x : UA σ W.J) :
    ∃ (p : UA σ W.J) (t : (AE F E)ˣ), mat p *ᵥ incV F H.x = t.1 • incV F H.x ∧ p⁻¹ * x ∈ PositivityTheory.ThKEnd.FinK σ B W := by
  have hσ := hB.cm
  have one : ∀ {S : Type} [CommRing S] (f : AE F E →+* S), (1 : Matrix (Fin d) (Fin d) (AE F E)).map f = 1 := fun f =>
    Matrix.map_one _ (map_zero _) (map_one _)
  choose p p' t ht h1 h2 h3 h4 using fun w => exists_loc hB hW hH w (g := (mat x).map (piInf (B.emb w)))
    (g' := (mat x⁻¹).map (piInf (B.emb w)))
    (by rw [← Matrix.map_mul, show mat x * mat x⁻¹ = 1 from x.1.mul_inv, one])
    (by
      rw [← iso_map_piInf (fun τ z => piInf_cA hσ τ z), show (mat x)ᵀ * incM F W.J * (mat x).map (cA σ) = incM F W.J from x.2]
      exact Matrix.ext fun i j => piInf_incl _ _)
  obtain ⟨q, q1, q2⟩ := exists_lift hσ B.emb W.J p p' h1 h2
  obtain ⟨a, a1, a2⟩ := exists_inf hσ B.emb t
  obtain ⟨b, b1, b2⟩ := exists_inf hσ B.emb fun w => (t w)⁻¹
  have hab : a * b = 1 := ad_ext hσ B.emb (fun w => by rw [map_mul, a1, b1, mul_inv_cancel₀ (ht w), map_one])
    fun v => by rw [map_mul, a2, b2, mul_one, map_one]
  refine ⟨q, ⟨a, b, hab, (mul_comm _ _).trans hab⟩, funext fun i => ad_ext hσ B.emb (fun w => ?_) fun v => ?_, fun w => ?_⟩
  · have e : piInf (B.emb w) ∘ incV F H.x = fun i => (B.emb w).1 (H.x i) := funext fun i => piInf_incl _ _
    rw [RingHom.map_mulVec, q1, e, h3, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, a1]
    exact congrArg _ (congrFun e i).symm
  · rw [RingHom.map_mulVec, q2, Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul, map_mul, a2, one_mul]
    rfl
  · have e : (mat q⁻¹).map (piInf (B.emb w)) = p' w := by
      have e1 : (mat q⁻¹).map (piInf (B.emb w)) * p w = 1 := by
        rw [← q1, ← Matrix.map_mul, show mat q⁻¹ * mat q = 1 from q.1.inv_mul, one]
      exact left_inv_eq_right_inv e1 (h1 w)
    rw [show mat (q⁻¹ * x) = mat q⁻¹ * mat x from rfl, Matrix.map_mul, e]
    exact h4 w

end Levi

open Levi

theorem leviEx : PositivityTheory.ThKG.LeviEx := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hB hW hH h₁ => exists_levi hB hW hH 1 h₁

theorem iwa : PositivityTheory.ThKEnd.Iwa := by
  intro F E _ _ _ _ _ σ B d d₁ W W₁ H i₀ i₁ r s hB hW hH
  have hd : IsUnit W₁.J.det := (isFr hB hW hH).isUnit_det (det_ne_zero hW).isUnit
  refine ⟨⟨hH.rank, hH.xx, hH.yy, hH.xy, hH.orth, hH.gram, hd.ne_zero⟩, fun x => ?_⟩
  obtain ⟨p, t, hp, hk⟩ := exists_stab hB hW hH x
  obtain ⟨g, α, hg, hα⟩ := (isFrA hB hW hH).stab t.mul_inv p.2 hp
  have hgu : IsUnit g.det := by
    have e := congrArg Matrix.det hg
    have hd' : IsUnit (incM F W₁.J).det := by
      have := hd.map (inclR (F := F) (AF F))
      rwa [RingHom.map_det] at this
    rw [← e, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hd'
    exact isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hd')
  obtain ⟨h₁, rfl⟩ := exists_UA (σ := σ) (Matrix.mul_nonsing_inv _ hgu) hg
  obtain ⟨m, hm⟩ := exists_levi hB hW hH t 1
  obtain ⟨l, hl⟩ := exists_levi hB hW hH 1 h₁
  refine ⟨p * (m * l)⁻¹, Subgroup.subset_closure ?_, t, m, h₁, l, _, hk, hm, hl, by group⟩
  obtain ⟨u, hu⟩ : ∃ u, u = p * (m * l)⁻¹ := ⟨_, rfl⟩
  have e : mat u * (mat m * mat l) = mat p := by
    rw [hu]; exact congrArg mat (inv_mul_cancel_right p (m * l))
  rw [← hu]
  constructor
  · have e1 : t.1 • (mat u *ᵥ incV F H.x) = t.1 • incV F H.x := by
      rw [← hp, ← e, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hl.1, Units.val_one, one_smul, hm.1, Matrix.mulVec_smul]
    exact (t.isUnit.smul_left_cancel).1 e1
  · intro z
    obtain ⟨y, rfl⟩ : ∃ y, z = mat h₁ *ᵥ y :=
      ⟨mat h₁⁻¹ *ᵥ z, by rw [Matrix.mulVec_mulVec, show mat h₁ * mat h₁⁻¹ = 1 from h₁.1.mul_inv, Matrix.one_mulVec]⟩
    refine ⟨α ⬝ᵥ y, ?_⟩
    have e2 : mat u * (incM F H.ι * mat h₁) = mat p * incM F H.ι := by
      rw [← e, Matrix.mul_assoc, Matrix.mul_assoc, hl.2.2, ← Matrix.mul_assoc (mat m), hm.2.2,
        show mat (1 : UA σ W₁.J) = 1 from rfl, Matrix.mul_one]
    rw [← hα, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, e2]
    rfl

end PositivityTheory.ThKG.Tow

end
