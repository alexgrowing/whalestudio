import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulTransposeInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticIsotropicPlaneVanishesAdelic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormRestrictedPlane
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewDeterminantNeZeroFirstSpace

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.DblLagr

open GlobalTheory.MixedLagr (hat hat_add hat_smul hTens_vecMulVec)
open GlobalTheory.MixedLagrGram (hTens_eq_trace incM_map_cA)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_ratCoord {α β κ : Type} (e : Matrix α β (AE F E) ≃ₗ[AF F] (κ → AF F) × (κ → AF F))
    (h : ∀ x : Matrix α β E, ∃ w : (κ → F) × (κ → F), e (incM F x) = hat w) :
    ∃ f : Matrix α β E →ₗ[F] (κ → F) × (κ → F), Function.Injective f ∧ ∀ x, hat (f x) = e (incM F x) := by
  choose w hw using h
  have hA : Function.Injective (algebraMap F (AF F)) := AdeleRing.algebraMap_injective (𝓞 F) F
  have hg : ∀ x, hat (w x) = e (incM F x) := fun x => (hw x).symm
  have hinj : Function.Injective (hat : (κ → F) × (κ → F) → _) := by
    intro a b hab
    simp only [hat, Prod.mk.injEq] at hab
    exact Prod.ext (funext fun i => hA (congrFun hab.1 i)) (funext fun i => hA (congrFun hab.2 i))
  have hadd : ∀ x x' : Matrix α β E, incM F (x + x') = incM F x + incM F x' := by
    intro x x'
    ext i j
    simp [incM, Matrix.map_apply, map_add]
  have hsmul : ∀ (c : F) (x : Matrix α β E), incM F (c • x) = algebraMap F (AF F) c • incM F x := by
    intro c x
    ext i j
    simp only [incM, Matrix.map_apply, Matrix.smul_apply]
    show (Algebra.TensorProduct.includeRight : E →ₐ[F] AE F E) (c • x i j) =
      algebraMap F (AF F) c • (Algebra.TensorProduct.includeRight : E →ₐ[F] AE F E) (x i j)
    rw [map_smul, algebraMap_smul]
  have hI : Function.Injective (incM F : Matrix α β E → Matrix α β (AE F E)) :=
    Matrix.map_injective (Algebra.TensorProduct.includeRight_injective hA)
  refine ⟨{ toFun := w, map_add' := ?_, map_smul' := ?_ }, ?_, hg⟩
  · intro x x'
    apply hinj
    rw [hat_add, hg, hg, hg, hadd, map_add]
  · intro c x
    apply hinj
    rw [RingHom.id_apply, hat_smul, hg, hg, hsmul, LinearEquiv.map_smul]
  · intro x x' hx
    apply hI
    apply e.injective
    rw [← hg, ← hg]
    exact congrArg hat hx

theorem exists_first_zero {α β κ : Type} [Fintype α] [Fintype β] [Fintype κ]
    (e : Matrix α β (AE F E) ≃ₗ[AF F] (κ → AF F) × (κ → AF F)) (hE : Module.finrank F E = 2)
    (hκ : Fintype.card κ = Fintype.card α * Fintype.card β)
    (h : ∀ x : Matrix α β E, ∃ w : (κ → F) × (κ → F), e (incM F x) = hat w) :
    ∃ K : Submodule F (Matrix α β E), Module.finrank F K = Fintype.card κ ∧ ∀ z ∈ K, (e (incM F z)).1 = 0 := by
  obtain ⟨f, hf, hhat⟩ := exists_ratCoord e h
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  have hdom : Module.finrank F (Matrix α β E) = Fintype.card κ * 2 := by
    rw [Module.finrank_matrix, hE, hκ]
  have hcod : Module.finrank F ((κ → F) × (κ → F)) = Fintype.card κ * 2 := by
    rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card]; ring
  have hsurj : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (hdom.trans hcod.symm)).mp hf
  set g := (LinearMap.fst F (κ → F) (κ → F)).comp f with hg
  have gsurj : Function.Surjective g := by
    intro y
    obtain ⟨x, hx⟩ := hsurj (y, 0)
    exact ⟨x, by simp [hg, hx]⟩
  refine ⟨LinearMap.ker g, ?_, ?_⟩
  · have h1 := LinearMap.finrank_range_add_finrank_ker g
    rw [LinearMap.range_eq_top.mpr gsurj, finrank_top, Module.finrank_fintype_fun_eq_card, hdom] at h1
    omega
  · intro z hz
    rw [LinearMap.mem_ker] at hz
    rw [← hhat z]
    have hz' : (f z).1 = 0 := by simpa [hg] using hz
    funext i
    simp [hat, hz']

theorem rat_dbl {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W)
    (hM : ∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
      M.co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)))
    (d' : Darboux (symp (cA σ) (-1) (incM F W.J) (incM F X.J)) (Fin n × Fin d))
    (hd' : ∀ x : Matrix (Fin n) (Fin d) (AE F E), d'.e xᵀ = M.co.e x)
    (dd : Darboux (symp (cA σ) (-1) (incM F W.J) (dbl (incM F X.J))) ((Fin n × Fin d) ⊕ (Fin n × Fin d)))
    (hdd : IsDblCoord (cA σ) (-1) (incM F W.J) (incM F X.J) d' dd) (x : Matrix (Fin d) (Fin n ⊕ Fin n) E) :
    ∃ w, dd.e (incM F x) = hat w := by
  obtain ⟨y₁, z₁, h₁⟩ := hM (x.toCols₁)ᵀ
  obtain ⟨y₂, z₂, h₂⟩ := hM (x.toCols₂)ᵀ
  rw [← hd'] at h₁ h₂
  have e : incM F x = Matrix.fromCols (incM F (x.toCols₁)ᵀ)ᵀ (incM F (x.toCols₂)ᵀ)ᵀ := by
    ext i (j | j) <;> rfl
  refine ⟨(Sum.elim y₁ y₂, Sum.elim z₁ (-z₂)), ?_⟩
  rw [e, hdd, h₁, h₂]
  refine Prod.ext ?_ ?_
  · funext j
    rcases j with j | j <;> rfl
  · funext j
    rcases j with j | j
    · rfl
    · simp [hat]

section Forms

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A)
  {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]

theorem hTens_restrict_left (JA : Matrix α α A) (JB : Matrix β β A) (J₁ : Matrix γ γ A) (ι : Matrix α γ A)
    (h : ιᵀ * JA * ι.map c = J₁) (z z' : Matrix γ β A) :
    hTens c JA JB (ι * z) (ι * z') = hTens c J₁ JB z z' := by
  rw [hTens_eq_trace, hTens_eq_trace, ← h, Matrix.transpose_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]

theorem hTens_cross (JA : Matrix α α A) (JB : Matrix β β A) (ι : Matrix α γ A) (x : α → A)
    (h : ιᵀ *ᵥ (JA *ᵥ fun k => c (x k)) = 0) (z : Matrix γ β A) (y : β → A) :
    hTens c JA JB (ι * z) (Matrix.vecMulVec x y) = 0 := by
  have e : (Matrix.vecMulVec x y).map c = Matrix.vecMulVec (fun k => c (x k)) (fun k => c (y k)) := by
    ext i j; simp [Matrix.vecMulVec_apply]
  rw [hTens_eq_trace, e, Matrix.mul_vecMulVec, Matrix.transpose_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h]
  simp

end Forms

theorem isotropic {σ : E →ₐ[F] E} {B : Base F E} {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H' : Plane E d d₁} {i₀ i₁ : ℕ}
    (hH : H'.IsAdapted σ B W W₁ i₀ i₁) {β κ κ₁ : Type} [Fintype β] [DecidableEq β] [Fintype κ] [Fintype κ₁]
    (JB : Matrix β β (AE F E)) (dd : Darboux (symp (cA σ) (-1) (incM F W.J) JB) κ)
    (dd₁ : Darboux (symp (cA σ) (-1) (incM F W₁.J) JB) κ₁) (y y' : β → AE F E) (z z' : Matrix (Fin d₁) β (AE F E))
    (hz : (dd₁.e z).1 = 0) (hz' : (dd₁.e z').1 = 0) :
    (dd.e (Matrix.vecMulVec (incV F H'.x) y + incM F H'.ι * z)).1 ⬝ᵥ
        (dd.e (Matrix.vecMulVec (incV F H'.x) y' + incM F H'.ι * z')).2 =
      (dd.e (Matrix.vecMulVec (incV F H'.x) y' + incM F H'.ι * z')).1 ⬝ᵥ
        (dd.e (Matrix.vecMulVec (incV F H'.x) y + incM F H'.ι * z)).2 := by
  have hc : ∀ x : E, cA σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := fun x => rfl
  have hx : ∑ j, ∑ l, incV F H'.x j * incM F W.J j l * cA σ (incV F H'.x l) = 0 := by
    have h1 := congrArg (inclR (F := F) (AF F)) hH.xx
    rw [map_zero] at h1
    rw [← h1]
    simp only [form, incV, incM, Matrix.map_apply, hc, dotProduct, Matrix.mulVec, Finset.mul_sum, map_sum, map_mul, mul_assoc]
  have h0 : (incM F H'.ι)ᵀ *ᵥ (incM F W.J *ᵥ fun k => cA σ (incV F H'.x k)) = 0 := by
    funext m
    have e := (hH.orth (Pi.single m 1)).1
    rw [Matrix.mulVec_single_one] at e
    have := congrArg (inclR (F := F) (AF F)) e
    simpa [form, incM, incV, Matrix.mulVec, dotProduct, map_sum, map_mul, hc] using this
  have hA : (incM F H'.ι)ᵀ * incM F W.J * (incM F H'.ι).map (cA σ) = incM F W₁.J := by
    rw [incM_map_cA, ← hH.gram]
    simp only [incM, Matrix.map_mul, Matrix.transpose_map]
  have h1 := dd.form (Matrix.vecMulVec (incV F H'.x) y) (Matrix.vecMulVec (incV F H'.x) y')
  rw [symp, hTens_vecMulVec, hx, zero_mul, mul_zero, map_zero] at h1
  have h2 := dd.form (incM F H'.ι * z) (Matrix.vecMulVec (incV F H'.x) y')
  rw [symp, hTens_cross _ _ _ _ _ h0, mul_zero, map_zero] at h2
  have h3 := dd.form (incM F H'.ι * z') (Matrix.vecMulVec (incV F H'.x) y)
  rw [symp, hTens_cross _ _ _ _ _ h0, mul_zero, map_zero] at h3
  have h4 := dd.form (incM F H'.ι * z) (incM F H'.ι * z')
  have h5 := dd₁.form z z'
  rw [hz, hz', zero_dotProduct, zero_dotProduct, sub_zero, symp] at h5
  rw [symp, hTens_restrict_left _ _ _ _ _ hA, h5] at h4
  simp only [map_add, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
  linear_combination -h1 - h2 + h3 - h4

theorem eq_zero_of_sum {σ : E →ₐ[F] E} {B : Base F E} {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H' : Plane E d d₁}
    {i₀ i₁ : ℕ} (hH : H'.IsAdapted σ B W W₁ i₀ i₁) (hdet : W₁.J.det ≠ 0) {β : Type} [Fintype β]
    (y : β → E) (z : Matrix (Fin d₁) β E) (h : Matrix.vecMulVec H'.x y + H'.ι * z = 0) : y = 0 ∧ z = 0 := by
  have hcol : ∀ j, y j • H'.x + H'.ι *ᵥ (fun k => z k j) = 0 := by
    intro j
    funext i
    have := congrFun (congrFun h i) j
    simp only [Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.zero_apply] at this
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Pi.zero_apply]
    rw [← this, mul_comm]
  have hform : ∀ (a : E) (u v : Fin d → E), form σ W.J (a • u + v) H'.y = a * form σ W.J u H'.y + form σ W.J v H'.y := by
    intro a u v
    simp [form, add_dotProduct, smul_dotProduct]
  have hy : y = 0 := by
    funext j
    have : form σ W.J (y j • H'.x + H'.ι *ᵥ (fun k => z k j)) H'.y = form σ W.J 0 H'.y := by rw [hcol j]
    rw [hform, hH.xy, (hH.orth _).2] at this
    simpa [form] using this
  refine ⟨hy, ?_⟩
  have hv : Matrix.vecMulVec H'.x y = 0 := by
    ext i j; simp [hy, Matrix.vecMulVec_apply]
  rw [hv, zero_add] at h
  have h0 : zᵀ * W₁.J = 0 := by
    rw [← hH.gram, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.transpose_mul, h]
    simp
  have h1 := congrArg (· * W₁.J⁻¹) h0
  simp only [Matrix.zero_mul] at h1
  rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), Matrix.mul_one] at h1
  simpa using congrArg Matrix.transpose h1

theorem exists_ratLagr : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ →
      ∀ (d' : Darboux (symp (cA σ) (-1) (incM F W.J) (incM F X.J)) (Fin n × Fin d)),
        (∀ x : Matrix (Fin n) (Fin d) (AE F E), d'.e xᵀ = M.co.e x) →
      ∀ (d₁' : Darboux (symp (cA σ) (-1) (incM F W₁.J) (incM F X.J)) (Fin n × Fin d₁)),
        (∀ x : Matrix (Fin n) (Fin d₁) (AE F E), d₁'.e xᵀ = M₁.co.e x) →
      ∀ (dd : Darboux (symp (cA σ) (-1) (incM F W.J) (dbl (incM F X.J))) ((Fin n × Fin d) ⊕ (Fin n × Fin d))),
        IsDblCoord (cA σ) (-1) (incM F W.J) (incM F X.J) d' dd →
      ∀ (dd₁ : Darboux (symp (cA σ) (-1) (incM F W₁.J) (dbl (incM F X.J))) ((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁))),
        IsDblCoord (cA σ) (-1) (incM F W₁.J) (incM F X.J) d₁' dd₁ →
      ∃ L : Submodule F (((Fin n × Fin d) ⊕ (Fin n × Fin d) → F) × ((Fin n × Fin d) ⊕ (Fin n × Fin d) → F)),
        (∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) ∧
        Module.finrank F L = Fintype.card ((Fin n × Fin d) ⊕ (Fin n × Fin d)) ∧
        ∀ (t : AF F), ∀ w ∈ L, ∃ y : Fin n ⊕ Fin n → AE F E, ∃ z : Matrix (Fin d₁) (Fin n ⊕ Fin n) (AE F E),
          (dd₁.e z).1 = 0 ∧ dd.e (Matrix.vecMulVec (incV F H'.x) y + incM F H'.ι * z) =
            t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i))) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ d' hd' d₁' hd₁' dd hdd dd₁ hdd₁
  have hE : Module.finrank F E = 2 := hP.base.cm.2.2.1
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  obtain ⟨f, hf, hfe⟩ := exists_ratCoord dd.e (rat_dbl M hP.good.rat d' hd' dd hdd)
  obtain ⟨K, hK, hKz⟩ := exists_first_zero dd₁.e hE (by simp; ring) (rat_dbl M₁ hP₁.good.rat d₁' hd₁' dd₁ hdd₁)
  have hdet := GlobalTheory.SkewGram.det_ne_zero F E σ B d₁ W₁ r₁ s₁ hP₁.skew
  let Φ : (Fin n ⊕ Fin n → E) × K →ₗ[F] Matrix (Fin d) (Fin n ⊕ Fin n) E :=
    { toFun := fun p => Matrix.vecMulVec H'.x p.1 + H'.ι * (p.2 : Matrix (Fin d₁) (Fin n ⊕ Fin n) E)
      map_add' := fun p q => by
        simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, Matrix.vecMulVec_add, Matrix.mul_add]; abel
      map_smul' := fun c p => by
        ext i j
        simp [Matrix.vecMulVec_apply, Matrix.mul_apply, Finset.smul_sum, mul_smul_comm, smul_add] }
  have hΦ : ∀ p, Φ p = Matrix.vecMulVec H'.x p.1 + H'.ι * (p.2 : Matrix (Fin d₁) (Fin n ⊕ Fin n) E) := fun _ => rfl
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro p hp
    obtain ⟨h1, h2⟩ := eq_zero_of_sum hH hdet _ _ (hΦ p ▸ hp)
    exact Prod.ext h1 (Subtype.ext h2)
  have hhat : ∀ p, hat (f (Φ p)) = dd.e (Matrix.vecMulVec (incV F H'.x) (fun j => inclR (F := F) (AF F) (p.1 j)) +
      incM F H'.ι * incM F (p.2 : Matrix (Fin d₁) (Fin n ⊕ Fin n) E)) := by
    intro p
    rw [hfe, hΦ]
    congr 1
    ext i j
    simp [incM, incV, Matrix.vecMulVec_apply, Matrix.mul_apply, map_sum, map_mul]
  refine ⟨LinearMap.range (f ∘ₗ Φ), ?_, ?_, ?_⟩
  · rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
    have h := isotropic hH _ dd dd₁ (fun j => inclR (F := F) (AF F) (p.1 j)) (fun j => inclR (F := F) (AF F) (q.1 j))
      _ _ (hKz _ p.2.2) (hKz _ q.2.2)
    rw [← hhat, ← hhat] at h
    apply (AdeleRing.algebraMap_injective (𝓞 F) F)
    rw [RingHom.map_dotProduct, RingHom.map_dotProduct]
    exact h
  · have hfΦ : Function.Injective (f ∘ₗ Φ) := fun p q h => hinj (hf h)
    rw [LinearMap.finrank_range_of_inj hfΦ, Module.finrank_prod, Module.finrank_pi_fintype, hK]
    have hd := hH.rank
    subst hd
    simp [hE]
    ring
  · rintro t _ ⟨p, rfl⟩
    refine ⟨t • fun j => inclR (F := F) (AF F) (p.1 j), t • incM F (p.2 : Matrix (Fin d₁) (Fin n ⊕ Fin n) E), ?_, ?_⟩
    · rw [LinearEquiv.map_smul, Prod.smul_fst, hKz _ p.2.2, smul_zero]
    · rw [Matrix.vecMulVec_smul, Matrix.mul_smul, ← smul_add, LinearEquiv.map_smul, ← hhat]
      rfl

end GlobalTheory.DblLagr

end
