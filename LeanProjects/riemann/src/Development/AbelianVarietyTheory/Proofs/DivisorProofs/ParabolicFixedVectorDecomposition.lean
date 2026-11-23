import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviLiftOfAdaptedPlane
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicComplementNondegenerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicComplementHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedFiniteMapsRestriction
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.StabDecInf

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mul_inv_mem_unip_one {σ : E →ₐ[F] E} {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H' : Plane E d d₁}
    {h₁ : UA σ W₁.J} {m p : UA σ W.J} (hl : IsLevi H' 1 h₁ m)
    (hpx : mat p *ᵥ incV F H'.x = incV F H'.x)
    (hpι : ∀ z, ∃ a : AE F E, mat p *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ (mat h₁ *ᵥ z) + a • incV F H'.x) :
    p * m⁻¹ ∈ unip σ W H' := by
  have hmi : mat m⁻¹ * mat m = 1 := Units.inv_mul m.1
  have hhi : mat h₁ * mat h₁⁻¹ = 1 := Units.mul_inv h₁.1
  have hmul : mat (p * m⁻¹) = mat p * mat m⁻¹ := rfl
  have hx : mat m⁻¹ *ᵥ incV F H'.x = incV F H'.x := by
    have h0 := hl.1
    rw [Units.val_one, one_smul] at h0
    conv_lhs => rw [← h0]
    rw [Matrix.mulVec_mulVec, hmi, Matrix.one_mulVec]
  have hι : mat m⁻¹ * incM F H'.ι = incM F H'.ι * mat h₁⁻¹ := by
    calc mat m⁻¹ * incM F H'.ι = mat m⁻¹ * (incM F H'.ι * (mat h₁ * mat h₁⁻¹)) := by rw [hhi, Matrix.mul_one]
      _ = (mat m⁻¹ * mat m) * incM F H'.ι * mat h₁⁻¹ := by
          rw [← Matrix.mul_assoc (incM F H'.ι), ← hl.2.2]; simp only [Matrix.mul_assoc]
      _ = incM F H'.ι * mat h₁⁻¹ := by rw [hmi, Matrix.one_mul]
  refine Subgroup.subset_closure ⟨?_, fun z => ?_⟩
  · rw [hmul, ← Matrix.mulVec_mulVec, hx, hpx]
  · obtain ⟨a, ha⟩ := hpι (mat h₁⁻¹ *ᵥ z)
    refine ⟨a, ?_⟩
    rw [hmul, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec z (mat m⁻¹) (incM F H'.ι), hι, ← Matrix.mulVec_mulVec, ha,
      Matrix.mulVec_mulVec z (mat h₁), hhi, Matrix.one_mulVec]

theorem exists_levi_mat {σ : E →ₐ[F] E} {n n₁ : ℕ} {X : Spc F E n} {X₁ : Spc F E n₁} (H : Plane E n n₁)
    (π : Matrix (Fin n₁) (Fin n) E) (hπι : π * H.ι = 1) (hπx : π *ᵥ H.x = 0) (hπy : π *ᵥ H.y = 0)
    (hc : H.ιᵀ * X.J = X₁.J * π.map σ) (hd : X.J * H.ι.map σ = πᵀ * X₁.J) (g₀ : UA σ X₁.J) :
    ∃ m : UA σ X.J, IsLevi (W₁ := X₁) H 1 g₀ m ∧ mat m = 1 + incM F H.ι * ((mat g₀ - 1) * incM F π) := by
  let c : AE F E →+* AE F E := (cA σ).toRingHom
  have hPI : incM F π * incM F H.ι = 1 := by
    simp only [incM]; rw [← Matrix.map_mul, hπι, Matrix.map_one _ (map_zero _) (map_one _)]
  have hcM : (incM F H.ι)ᵀ * incM F X.J = incM F X₁.J * (incM F π).map c := by
    rw [show (incM F π).map c = (incM F π).map (cA σ) from rfl, GlobalTheory.LeviFrame.incM_map_cA]
    simp only [incM]; rw [← Matrix.transpose_map, ← Matrix.map_mul, hc, Matrix.map_mul]
  have hdM : incM F X.J * (incM F H.ι).map c = (incM F π)ᵀ * incM F X₁.J := by
    rw [show (incM F H.ι).map c = (incM F H.ι).map (cA σ) from rfl, GlobalTheory.LeviFrame.incM_map_cA]
    simp only [incM]; rw [← Matrix.transpose_map, ← Matrix.map_mul, hd, Matrix.map_mul]
  have hU : (mat g₀)ᵀ * incM F X₁.J * (mat g₀).map c = incM F X₁.J := g₀.2
  have hHK : mat g₀ * mat g₀⁻¹ = 1 := Units.mul_inv g₀.1
  have hKH : mat g₀⁻¹ * mat g₀ = 1 := Units.inv_mul g₀.1
  let g : GL (Fin n) (AE F E) :=
    ⟨1 + incM F H.ι * ((mat g₀ - 1) * incM F π), 1 + incM F H.ι * ((mat g₀⁻¹ - 1) * incM F π),
      GlobalTheory.LeviFrame.levi_inv_alg _ _ _ _ hPI hHK, GlobalTheory.LeviFrame.levi_inv_alg _ _ _ _ hPI hKH⟩
  have hg : g ∈ UG (cA σ) (incM F X.J) :=
    GlobalTheory.LeviFrame.levi_unit_alg c (incM F X.J) (incM F X₁.J) (incM F H.ι) (incM F π) (mat g₀) hPI hcM hdM hU
  refine ⟨⟨g, hg⟩, ⟨?_, ?_, ?_⟩, rfl⟩
  · show (1 + incM F H.ι * ((mat g₀ - 1) * incM F π)) *ᵥ incV F H.x = ((1 : (AE F E)ˣ) : AE F E) • incV F H.x
    rw [Units.val_one, one_smul, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, GlobalTheory.LeviFrame.incM_mulVec_incV, hπx,
      show incV F (0 : Fin n₁ → E) = 0 from funext fun _ => map_zero _,
      Matrix.mulVec_zero, Matrix.mulVec_zero, add_zero]
  · show (1 + incM F H.ι * ((mat g₀ - 1) * incM F π)) *ᵥ incV F H.y =
      cA σ (((1 : (AE F E)ˣ)⁻¹ : (AE F E)ˣ) : AE F E) • incV F H.y
    rw [inv_one, Units.val_one, map_one, one_smul, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, GlobalTheory.LeviFrame.incM_mulVec_incV, hπy,
      show incV F (0 : Fin n₁ → E) = 0 from funext fun _ => map_zero _,
      Matrix.mulVec_zero, Matrix.mulVec_zero, add_zero]
  · show (1 + incM F H.ι * ((mat g₀ - 1) * incM F π)) * incM F H.ι = incM F H.ι * mat g₀
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc, hPI, Matrix.mul_one, Matrix.mul_sub,
      Matrix.mul_one, add_sub_cancel]

theorem stab_decomp_at {R : Type} [Zero R] (ev : AF F → R) {σ : E →ₐ[F] E} {B : Base F E} {n n₁ : ℕ} {X : Spc F E n}
    {X₁ : Spc F E n₁} {H : Plane E n n₁} {r s i₀ i₁ : ℕ} (hB : B.IsGood σ) (hX : X.IsHerm σ B r s)
    (hdet : X₁.J.det ≠ 0) (hA : H.IsAdapted σ B X X₁ i₀ i₁) (p : UA σ X.J) (hp : p ∈ UAt σ X ev)
    (hpx : mat p *ᵥ incV F H.x = incV F H.x) :
    ∃ (u m : UA σ X.J) (g₀ : UA σ X₁.J), u ∈ unip σ X H ∧ u ∈ UAt σ X ev ∧
      IsLevi (W₁ := X₁) H 1 g₀ m ∧ m ∈ UAt σ X ev ∧ g₀ ∈ UAt σ X₁ ev ∧ p = u * m := by
  have hσ : ∀ z, σ (σ z) = z := GlobalTheory.PlaneFrame.conj_conj hB.cm
  have hspan := GlobalTheory.LeviSpan.span_adelic F E σ n n₁ X.J X₁.J H.x H.y H.ι hσ hX.herm hA.1 hA.xx hA.yy hA.xy hA.orth
    hA.gram hdet
  obtain ⟨g₀, hg₀⟩ := GlobalTheory.LeviCols.levi_cols F E σ n n₁ X.J X₁.J H.x H.y H.ι hσ hX.herm hA.xx hA.yy hA.xy hA.orth
    hA.gram hdet hspan p 1 (by rw [Units.val_one, one_smul]; exact hpx)
  obtain ⟨π, hπι, hπx, hπy, hc, hd⟩ := GlobalTheory.LeviFrameH.frame_facts σ B X X₁ H hB.cm hX hA
  obtain ⟨m, hl, hm⟩ := exists_levi_mat H π hπι hπx hπy hc hd g₀
  have hPI : incM F π * incM F H.ι = 1 := by
    simp only [incM]; rw [← Matrix.map_mul, hπι, Matrix.map_one _ (map_zero _) (map_one _)]
  have hPx : incM F π *ᵥ incV F H.x = 0 := by
    rw [GlobalTheory.LeviFrame.incM_mulVec_incV, hπx]
    exact funext fun _ => map_zero _
  have hg : mat g₀ - 1 = incM F π * ((mat p - 1) * incM F H.ι) := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, hPI]
    congr 1
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun w => ?_
    obtain ⟨a, ha⟩ := hg₀ w
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ha,
      Matrix.mulVec_add, Matrix.mulVec_smul, hPx, smul_zero, add_zero, Matrix.mulVec_mulVec (mat g₀ *ᵥ w), hPI,
      Matrix.one_mulVec]
  have hg₀at : g₀ ∈ UAt σ X₁ ev := fun u hu => by
    rw [hg, ← Matrix.mul_smul, ← Matrix.smul_mul, hp u hu, Matrix.zero_mul, Matrix.mul_zero]
  have hmat : m ∈ UAt σ X ev := fun u hu => by
    rw [hm, add_sub_cancel_left, ← Matrix.mul_smul, ← Matrix.smul_mul, hg₀at u hu, Matrix.zero_mul, Matrix.mul_zero]
  refine ⟨p * m⁻¹, m, g₀, mul_inv_mem_unip_one hl hpx hg₀, ?_, hl, hmat, hg₀at, by group⟩
  exact (UAtSub σ X ev).mul_mem hp ((UAtSub σ X ev).inv_mem hmat)

theorem stab_decomp_inf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    B.IsGood σ → G.IsGood B → G₁.IsGood B →
    ∀ p ∈ UAt σ G.V (evI F), mat p *ᵥ incV F H.x = incV F H.x →
      ∃ (n m : UA σ G.V.J) (g₀ : UA σ G₁.V.J), n ∈ unip σ G.V H ∧ n ∈ UAt σ G.V (evI F) ∧
        IsLevi (W₁ := G₁.V) H 1 g₀ m ∧ m ∈ UAt σ G.V (evI F) ∧ g₀ ∈ UAt σ G₁.V (evI F) ∧ p = n * m := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' hC hB hG hG₁ p hp hpx
  exact stab_decomp_at (evI F) hB hG.hV (GlobalTheory.FinUniq.det_ne_zero_herm hG₁.hV) hC.hH p hp hpx

end GlobalTheory.StabDecInf

end
