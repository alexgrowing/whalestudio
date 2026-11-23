import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoC
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.UnipDom

noncomputable section
namespace GlobalTheory.ThK.UnipDom.RatPt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

local notation "fm" => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form

section Form
variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

lemma fm_add_left (a b u : Fin n → E) : fm σ J (a + b) u = fm σ J a u + fm σ J b u := by
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, add_dotProduct]
lemma fm_smul_left (k : E) (a u : Fin n → E) : fm σ J (k • a) u = k * fm σ J a u := by
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, smul_dotProduct]
lemma fm_neg_left (a u : Fin n → E) : fm σ J (-a) u = - fm σ J a u := by
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, neg_dotProduct]
lemma fm_add_right (a u u' : Fin n → E) : fm σ J a (u + u') = fm σ J a u + fm σ J a u' := by
  have : (fun i => σ ((u + u') i)) = (fun i => σ (u i)) + (fun i => σ (u' i)) := by ext i; simp
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, this, Matrix.mulVec_add, dotProduct_add]
lemma fm_smul_right (k : E) (a u : Fin n → E) : fm σ J a (k • u) = σ k * fm σ J a u := by
  have : (fun i => σ ((k • u) i)) = σ k • (fun i => σ (u i)) := by ext i; simp
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, this, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
lemma fm_neg_right (a u : Fin n → E) : fm σ J a (-u) = - fm σ J a u := by
  have : (fun i => σ ((-u) i)) = -(fun i => σ (u i)) := by ext i; simp
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, this, Matrix.mulVec_neg, dotProduct_neg]

lemma fm_skew (hσ : ∀ e, σ (σ e) = e) (hJ : ∀ i j, σ (J j i) = -J i j) (a b : Fin n → E) :
    fm σ J b a = - σ (fm σ J a b) := by
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, Finset.mul_sum, map_neg]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hJ j i]
  ring

end Form
end GlobalTheory.ThK.UnipDom.RatPt

namespace GlobalTheory.ThK.UnipDom.RatPt
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
local notation "fm" => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form

section Eich
variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

def eich (x w v : Fin n → E) : Fin n → E :=
  v + fm σ J v w • x + fm σ J v x • w + (fm σ J w w / 2 * fm σ J v x) • x

variable {σ J}

lemma eich_form (hσ : ∀ e, σ (σ e) = e) (hJ : ∀ i j, σ (J j i) = -J i j) {x w : Fin n → E}
    (hxx : fm σ J x x = 0) (hxw : fm σ J x w = 0) (v u : Fin n → E) :
    fm σ J (eich σ J x w v) (eich σ J x w u) = fm σ J v u := by
  have hwx : fm σ J w x = 0 := by rw [fm_skew σ J hσ hJ, hxw, map_zero, neg_zero]
  have h1 : fm σ J x u = - σ (fm σ J u x) := fm_skew σ J hσ hJ u x
  have h2 : fm σ J w u = - σ (fm σ J u w) := fm_skew σ J hσ hJ u w
  have h3 : σ (fm σ J w w) = - fm σ J w w := by
    have := fm_skew σ J hσ hJ w w
    linear_combination this
  simp only [eich, fm_add_left, fm_smul_left, fm_add_right, fm_smul_right, hxx, hxw, hwx, h1, h2, map_mul, map_div₀,
    h3, map_ofNat]
  ring

lemma eich_neg (hσ : ∀ e, σ (σ e) = e) (hJ : ∀ i j, σ (J j i) = -J i j) {x w : Fin n → E}
    (hxx : fm σ J x x = 0) (hxw : fm σ J x w = 0) (v : Fin n → E) :
    eich σ J x w (eich σ J x (-w) v) = v := by
  have hwx : fm σ J w x = 0 := by rw [fm_skew σ J hσ hJ, hxw, map_zero, neg_zero]
  have e1 : fm σ J (eich σ J x (-w) v) x = fm σ J v x := by
    simp only [eich, fm_add_left, fm_smul_left, fm_neg_left, hxx, hwx]; ring
  have e2 : fm σ J (eich σ J x (-w) v) w = fm σ J v w - fm σ J v x * fm σ J w w := by
    simp only [eich, fm_add_left, fm_smul_left, fm_neg_left, fm_neg_right, hxw, fm_add_right]; ring
  have e3 : fm σ J (-w) (-w) = fm σ J w w := by rw [fm_neg_left, fm_neg_right, neg_neg]
  rw [eich, e1, e2]
  simp only [eich, e3, fm_neg_right]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  ring

end Eich
end GlobalTheory.ThK.UnipDom.RatPt

namespace GlobalTheory.ThK.UnipDom.RatPt
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
local notation "fm" => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form

section Mat
variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

def eichM (x w : Fin n → E) : Matrix (Fin n) (Fin n) E :=
  1 + Matrix.vecMulVec x (J *ᵥ fun i => σ (w i)) + Matrix.vecMulVec w (J *ᵥ fun i => σ (x i)) +
    (fm σ J w w / 2) • Matrix.vecMulVec x (J *ᵥ fun i => σ (x i))

lemma smul_mulVec' (c : E) (M : Matrix (Fin n) (Fin n) E) (v : Fin n → E) : (c • M) *ᵥ v = c • (M *ᵥ v) := by
  ext k; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

lemma eichM_mulVec (x w v : Fin n → E) : eichM σ J x w *ᵥ v = eich σ J x w v := by
  ext i
  simp only [eichM, eich, Matrix.add_mulVec, Matrix.one_mulVec, smul_mulVec', Matrix.vecMulVec_mulVec,
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, Pi.add_apply, Pi.smul_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
  rw [dotProduct_comm _ v, dotProduct_comm _ v]
  ring

variable {σ J}

lemma ug_of_form (G : Matrix (Fin n) (Fin n) E) (h : ∀ v u, fm σ J (G *ᵥ v) (G *ᵥ u) = fm σ J v u) :
    Gᵀ * J * G.map σ = J := by
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  have hr : (fun k => σ ((Pi.single j (1:E) : Fin n → E) k)) = Pi.single j 1 := by
    ext k; by_cases hk : k = j <;> simp [hk]
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, hr, single_one_dotProduct, Matrix.mulVec_single_one, Matrix.col_apply] at this
  rw [← this]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, dotProduct, Matrix.mulVec, Matrix.col_apply,
    Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

end Mat
end GlobalTheory.ThK.UnipDom.RatPt

namespace GlobalTheory.ThK.UnipDom.RatPt
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
local notation "fm" => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form

lemma invol_of_cm {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (e : E) : σ (σ e) = e := by
  have : 0 < Fintype.card (E →+* ℂ) := by rw [NumberField.Embeddings.card E ℂ]; exact Module.finrank_pos
  obtain ⟨τ⟩ := Fintype.card_pos_iff.mp this
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

lemma vecMul_eq_zero_of_skew {σ : E →ₐ[F] E} {B : Base F E} {n r s : ℕ} {X : Spc F E n} (hX : X.IsSkew σ B r s)
    (v : Fin n → E) (hv : v ᵥ* X.J = 0) : v = 0 := by
  by_contra hne
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h; push_neg at h; exact hne (funext h)
  have hmem : ∀ k : E, k • v ∈ X.L := by
    intro k
    rw [hX.dual]
    intro z _ o
    have : fm σ X.J (k • v) z = 0 := by
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, smul_dotProduct, Matrix.dotProduct_mulVec v, hv, zero_dotProduct, smul_zero]
    rw [this, mul_zero, map_zero]; exact isIntegral_zero
  haveI := hX.lat
  have hfg : X.L.FG := Submodule.IsLattice.fg (A := E)
  let π : (Fin n → E) →ₗ[𝓞 E] E := LinearMap.proj i
  have htop : X.L.map π = ⊤ := by
    rw [eq_top_iff]; intro e _
    refine ⟨(e / v i) • v, hmem _, ?_⟩
    simp [π, div_mul_cancel₀ _ hi]
  haveI : Module.Finite (𝓞 E) E := Module.finite_def.2 (htop ▸ hfg.map π)
  exact RingOfIntegers.not_isField E
    ((Algebra.IsIntegral.isField_iff_isField (IsFractionRing.injective (𝓞 E) E)).2 (Field.toIsField E))

lemma exists_sol {σ : E →ₐ[F] E} {B : Base F E} {d d₁ r s i₀ i₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁}
    {H' : Plane E d d₁} (hW : W.IsSkew σ B r s) (hH : H'.IsAdapted σ B W W₁ i₀ i₁) (α : Fin d₁ → E) :
    ∃ t : Fin d → E, (∀ k, (H'.ι *ᵥ Pi.single k 1) ⬝ᵥ (W.J *ᵥ t) = α k) ∧ H'.x ⬝ᵥ (W.J *ᵥ t) = 0 := by
  let vs : Fin d₁ ⊕ Fin 2 → Fin d → E := Sum.elim (fun k => H'.ι *ᵥ Pi.single k 1) ![H'.x, H'.y]
  let A : Matrix (Fin d₁ ⊕ Fin 2) (Fin d) E := Matrix.of fun r => vs r ᵥ* W.J
  have hA : ∀ r t, (A *ᵥ t) r = vs r ⬝ᵥ (W.J *ᵥ t) := by
    intro r t
    simp only [A, Matrix.mulVec, Matrix.of_apply, Matrix.dotProduct_mulVec]
  have hJu : IsUnit W.J := Matrix.vecMul_injective_iff_isUnit.1 (fun a b hab => by
      have := vecMul_eq_zero_of_skew hW (a - b) (by rw [Matrix.sub_vecMul]; exact sub_eq_zero.2 hab)
      exact sub_eq_zero.1 this)
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
    have hL : ∀ z ∈ W.L, z ⬝ᵥ q = 0 := by
      intro z hz
      obtain ⟨a, b, u, -, -, -, rfl⟩ := hH.split z hz
      rw [add_dotProduct, add_dotProduct, smul_dotProduct, smul_dotProduct, hx0, hy0, dotProduct_comm (H'.ι *ᵥ u),
        Matrix.dotProduct_mulVec, hι]
      simp
    have hall : ∀ z, z ⬝ᵥ q = 0 := by
      intro z
      have hz : z ∈ Submodule.span E (W.L : Set (Fin d → E)) := by
        haveI := hW.lat; rw [Submodule.IsLattice.span_eq_top]; trivial
      induction hz using Submodule.span_induction with
      | mem z hz => exact hL z hz
      | zero => simp
      | add a b _ _ ha hb => rw [add_dotProduct, ha, hb, add_zero]
      | smul c a _ ha => rw [smul_dotProduct, ha, smul_zero]
    have hq : q = 0 := funext fun i => by simpa using hall (Pi.single i 1)
    exact (Matrix.mulVec_injective_iff_isUnit.2 hJu) (by rw [← hqdef, hq, Matrix.mulVec_zero])
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [hH.rank])).1 hinj
  obtain ⟨t, ht⟩ := hsurj (Sum.elim α 0)
  refine ⟨t, fun k => ?_, ?_⟩
  · have := congrFun ht (Sum.inl k)
    rw [Matrix.mulVecLin_apply, hA] at this
    simpa [vs] using this
  · have := congrFun ht (Sum.inr 0)
    rw [Matrix.mulVecLin_apply, hA] at this
    simpa [vs] using this

end GlobalTheory.ThK.UnipDom.RatPt

namespace GlobalTheory.ThK.UnipDom.RatPt
local notation "fm" => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form

theorem exists_unip_rat_coA : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (d d₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (r s i₀ i₁ : ℕ), IsCMExt F E σ → W.IsSkew σ B r s → H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ α : Fin d₁ → E, ∃ γ ∈ unip σ W H', γ ∈ ratU σ W.J ∧ coA σ W.J H' γ = fun j => inclR (F := F) (AF F) (α j) := by
  intro F E _ _ _ _ _ σ B d d₁ W W₁ H' r s i₀ i₁ hcm hW hH α
  have hσ := invol_of_cm hcm
  have hJ := hW.skew
  obtain ⟨t, ht, htx⟩ := exists_sol hW hH α
  set w : Fin d → E := fun i => σ (t i) with hw
  have hσw : (fun i => σ (w i)) = t := funext fun i => hσ _
  have hfw : ∀ v, fm σ W.J v w = v ⬝ᵥ (W.J *ᵥ t) := fun v => by
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, hσw]
  have hxw : fm σ W.J H'.x w = 0 := by rw [hfw]; exact htx
  have hxx := hH.xx
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
    have h2 : fm σ W.J (H'.ι *ᵥ Pi.single k 1) H'.x = 0 := (hH.orth _).1
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
    rw [hcol, hmv, hMι, hfA, fm_add_left, fm_smul_left, (hH.orth _).2, hH.xy]
    simp

end GlobalTheory.ThK.UnipDom.RatPt
