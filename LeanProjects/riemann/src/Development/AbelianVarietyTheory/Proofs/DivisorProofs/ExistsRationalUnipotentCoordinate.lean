import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAutSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNeZeroOfIsHypPl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalUnipotentCoordinateSurjective
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)
open GlobalTheory.ThK.UnipDom

noncomputable section

namespace GlobalTheory.ThK.IntV.HypRatPt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

local notation "fm" => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form

lemma exists_sol_hyp {σ : E →ₐ[F] E} {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁}
    {H' : Plane E d d₁} (hσ : ∀ e, σ (σ e) = e) (hH : IsHypPl σ W W₁ H') (α : Fin d₁ → E) :
    ∃ t : Fin d → E, (∀ k, (H'.ι *ᵥ Pi.single k 1) ⬝ᵥ (W.J *ᵥ t) = α k) ∧ H'.x ⬝ᵥ (W.J *ᵥ t) = 0 := by
  let vs : Fin d₁ ⊕ Fin 2 → Fin d → E := Sum.elim (fun k => H'.ι *ᵥ Pi.single k 1) ![H'.x, H'.y]
  let A : Matrix (Fin d₁ ⊕ Fin 2) (Fin d) E := Matrix.of fun r => vs r ᵥ* W.J
  have hA : ∀ r t, (A *ᵥ t) r = vs r ⬝ᵥ (W.J *ᵥ t) := by
    intro r t
    simp only [A, Matrix.mulVec, Matrix.of_apply, Matrix.dotProduct_mulVec]
  have hdet := GlobalTheory.ThK.HypPl.det_ne_zero_of_isHypPl hσ hH
  have hJu : IsUnit W.J := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet)
  have hinj : Function.Injective A.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro t ht
    have hr : ∀ r, vs r ⬝ᵥ (W.J *ᵥ t) = 0 := fun r => by
      rw [← hA]; rw [Matrix.mulVecLin_apply] at ht; rw [ht]; rfl
    set q := W.J *ᵥ t with hqdef
    have hι : q ᵥ* H'.ι = 0 := by
      ext k
      have := hr (Sum.inl k)
      simp only [vs, Sum.elim_inl, Matrix.mulVec_single_one] at this
      rw [dotProduct_comm] at this
      exact this
    have hx0 : H'.x ⬝ᵥ q = 0 := hr (Sum.inr 0)
    have hy0 : H'.y ⬝ᵥ q = 0 := hr (Sum.inr 1)
    have hall : ∀ z, z ⬝ᵥ q = 0 := by
      intro z
      obtain ⟨a, b, u, rfl⟩ := GlobalTheory.ThK.HypPl.span_of_isHypPl hσ hH z
      rw [add_dotProduct, add_dotProduct, smul_dotProduct, smul_dotProduct, hx0, hy0, dotProduct_comm (H'.ι *ᵥ u),
        Matrix.dotProduct_mulVec, hι]
      simp
    have hq : q = 0 := funext fun i => by simpa using hall (Pi.single i 1)
    exact (Matrix.mulVec_injective_iff_isUnit.2 hJu) (by rw [← hqdef, hq, Matrix.mulVec_zero])
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [hH.1])).1 hinj
  obtain ⟨t, ht⟩ := hsurj (Sum.elim α 0)
  refine ⟨t, fun k => ?_, ?_⟩
  · have := congrFun ht (Sum.inl k)
    rw [Matrix.mulVecLin_apply, hA] at this
    simpa [vs] using this
  · have := congrFun ht (Sum.inr 0)
    rw [Matrix.mulVecLin_apply, hA] at this
    simpa [vs] using this

open GlobalTheory.ThK.UnipDom.RatPt in

theorem exists_unip_rat_coA_hyp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n n₁ : ℕ} (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁), IsCMExt F E σ → GlobalTheory.ThK.IntV.IsHypPl σ Y Y₁ H → ∀ α : Fin n₁ → E, ∃ γ ∈ unip σ Y H, γ ∈ ratU σ Y.J ∧ coA σ Y.J H γ = fun j => inclR (F := F) (AF F) (α j) := by
  intro F E _ _ _ _ _ σ d d₁ W W₁ H' hcm hH α
  have hσ := GlobalTheory.ThK.HypPl.conj_conj hcm
  obtain ⟨t, ht, htx⟩ := exists_sol_hyp hσ hH α
  obtain ⟨-, hxx, -, hxy, horth, -, hJ, -⟩ := hH
  set w : Fin d → E := fun i => σ (t i) with hw
  have hσw : (fun i => σ (w i)) = t := funext fun i => hσ _
  have hfw : ∀ v, fm σ W.J v w = v ⬝ᵥ (W.J *ᵥ t) := fun v => by
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, hσw]
  have hxw : fm σ W.J H'.x w = 0 := by rw [hfw]; exact htx
  have hxw' : fm σ W.J H'.x (-w) = 0 := by rw [fm_neg_right, hxw, neg_zero]
  set M := eichM σ W.J H'.x w with hMdef
  set M' := eichM σ W.J H'.x (-w) with hM'def
  have hMM' : M * M' = 1 := by
    apply Matrix.ext_of_mulVec_single; intro i
    rw [← Matrix.mulVec_mulVec, hMdef, hM'def, eichM_mulVec, eichM_mulVec, Matrix.one_mulVec, eich_neg hσ hJ hxx hxw]
  have hM'M : M' * M = 1 := by
    apply Matrix.ext_of_mulVec_single; intro i
    have := eich_neg hσ hJ hxx hxw' (Pi.single i 1)
    rw [neg_neg] at this
    rw [← Matrix.mulVec_mulVec, hMdef, hM'def, eichM_mulVec, eichM_mulVec, Matrix.one_mulVec, this]
  let γE : GL (Fin d) E := ⟨M, M', hMM', hM'M⟩
  have hug : Mᵀ * W.J * M.map σ = W.J :=
    ug_of_form M (fun v u => by rw [hMdef, eichM_mulVec, eichM_mulVec, eich_form hσ hJ hxx hxw])
  let f : E →+* AE F E := inclR (F := F) (AF F)
  have hcA : ∀ e, cA σ (f e) = f (σ e) := fun e => by
    simp [f, cA, inclR]
  have hmv : ∀ (N : Matrix (Fin d) (Fin d) E) (v : Fin d → E), N.map f *ᵥ incV F v = incV F (N *ᵥ v) :=
    fun N v => funext fun i => (RingHom.map_mulVec f N v i).symm
  have hmem : Matrix.GeneralLinearGroup.map f γE ∈ UG (cA σ) (incM F W.J) := by
    show (M.map f)ᵀ * W.J.map f * (M.map f).map (cA σ) = W.J.map f
    rw [Matrix.map_map, show (⇑(cA σ) ∘ ⇑f) = ⇑f ∘ ⇑σ from funext hcA, ← Matrix.map_map, ← Matrix.transpose_map,
      ← Matrix.map_mul, ← Matrix.map_mul, hug]
  have hMx : M *ᵥ H'.x = H'.x := by
    rw [hMdef, eichM_mulVec]; simp [eich, hxw, hxx]
  have hMι : ∀ k, M *ᵥ (H'.ι *ᵥ Pi.single k 1) = H'.ι *ᵥ Pi.single k 1 + α k • H'.x := by
    intro k
    rw [hMdef, eichM_mulVec]
    have h1 : fm σ W.J (H'.ι *ᵥ Pi.single k 1) w = α k := by rw [hfw]; exact ht k
    have h2 : fm σ W.J (H'.ι *ᵥ Pi.single k 1) H'.x = 0 := (horth _).1
    simp only [eich, h1, h2, zero_smul, add_zero, mul_zero]
  have hMιm : M * H'.ι = H'.ι + Matrix.vecMulVec H'.x α := by
    apply Matrix.ext_of_mulVec_single; intro k
    rw [← Matrix.mulVec_mulVec, hMι, Matrix.add_mulVec, Matrix.vecMulVec_mulVec, dotProduct_single_one]
    ext i; simp [MulOpposite.smul_eq_mul_unop, mul_comm]
  refine ⟨⟨_, hmem⟩, Subgroup.subset_closure ⟨?_, ?_⟩, Subgroup.mem_subgroupOf.2 ⟨γE, rfl⟩, ?_⟩
  · show M.map f *ᵥ incV F H'.x = incV F H'.x
    rw [hmv, hMx]
  · intro z
    refine ⟨incV F α ⬝ᵥ z, ?_⟩
    show M.map f *ᵥ (H'.ι.map f *ᵥ z) = H'.ι.map f *ᵥ z + (incV F α ⬝ᵥ z) • incV F H'.x
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hMιm, Matrix.map_add _ (map_add f), Matrix.add_mulVec]
    congr 1
    have hvv : (Matrix.vecMulVec H'.x α).map f = Matrix.vecMulVec (incV F H'.x) (incV F α) := by
      ext i j; simp [Matrix.vecMulVec, incV, f]
    rw [hvv, Matrix.vecMulVec_mulVec]
    ext i; simp [MulOpposite.smul_eq_mul_unop, mul_comm]
  · funext j
    show fA σ W.J (M.map f *ᵥ (H'.ι.map f *ᵥ Pi.single j 1)) (incV F H'.y) = f (α j)
    have hcol : H'.ι.map f *ᵥ Pi.single j 1 = incV F (H'.ι *ᵥ Pi.single j 1) := by
      rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one]; rfl
    have hfA : ∀ v u : Fin d → E, fA σ W.J (incV F v) (incV F u) = f (fm σ W.J v u) := by
      intro v u
      simp only [fA, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form]
      rw [show (fun i => cA σ (incV F u i)) = incV F (fun i => σ (u i)) from funext fun i => hcA (u i)]
      rw [show incM F W.J = W.J.map f from rfl, hmv, RingHom.map_dotProduct]
      rfl
    rw [hcol, hmv, hMι, hfA, fm_add_left, fm_smul_left, (horth _).2, hxy]
    simp

end GlobalTheory.ThK.IntV.HypRatPt

end
