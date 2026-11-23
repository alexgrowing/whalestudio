import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAddCharIsStandardCharOfAdmissibleCM
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.DblVacEigen

section Alg

variable {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

omit [DecidableEq α] in

theorem hTens_dbl (JA : Matrix α α E) (JB : Matrix β β E) (x₁ x₂ y₁ y₂ : Matrix α β E) :
    hTens c JA (dbl JB) (Matrix.fromCols x₁ x₂) (Matrix.fromCols y₁ y₂) = hTens c JA JB x₁ y₁ - hTens c JA JB x₂ y₂ := by
  simp only [hTens, dbl, Fintype.sum_sum_type, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    Matrix.zero_apply, Matrix.neg_apply, mul_zero, zero_mul, add_zero, zero_add, mul_neg, neg_mul,
    Finset.sum_neg_distrib, Finset.sum_add_distrib, sub_eq_add_neg, Finset.sum_const_zero]

omit [DecidableEq α] [DecidableEq β] in

theorem hTens_transpose (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix β α E) :
    hTens c JA JB xᵀ yᵀ = hTens c JB JA x y := by
  unfold hTens
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.transpose_apply]
  ring

end Alg

end GlobalTheory.DblVacEigen

namespace GlobalTheory.DblVacEigen

variable {F : Type} [Field F] [NumberField F]

theorem dot_congr_at {κ : Type} [Fintype κ] (v : Pl F) {y : κ → AF F} (hy : At (evFin F v) y) {z z' : κ → AF F}
    (h : ∀ i, evFin F v (z i) = evFin F v (z' i)) : z ⬝ᵥ y = z' ⬝ᵥ y := by
  unfold dotProduct
  refine Finset.sum_congr rfl fun i _ => ?_
  have e := congrFun (hy (z i - z' i) (by rw [map_sub, h i, sub_self])) i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e
  rw [sub_mul] at e
  exact sub_eq_zero.mp e

theorem eigen_pointwise {κ : Type} [Fintype κ] (v : Pl F) (ψ : AddChar (AF F) ℂ) {φ : (κ → Fv F v) → ℂ}
    (hφ : φ ∈ SB (κ → Fv F v)) (p : (κ → AF F) × (κ → AF F)) (hp1 : At (evFin F v) p.1) (hp2 : At (evFin F v) p.2)
    (c : ℂ) (h : Acts (evFin F v) (schr ψ p) φ (c • φ)) (z : κ → AF F) :
    ψ (z ⬝ᵥ p.2 + ⅟(2 : AF F) * (p.1 ⬝ᵥ p.2)) * φ (fun i => evFin F v ((z + p.1) i)) =
      c * φ (fun i => evFin F v (z i)) := by
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest κ v
  have hr := hR φ hφ
  let Δ : κ → AF F := fun i => GlobalTheory.LatVac.liftV v (evFin F v (z i))
  have hΔ : At (evFin F v) Δ := fun u hu => funext fun i => GlobalTheory.LatVac.at_liftV v _ u hu
  have hevΔ : ∀ i, evFin F v (Δ i) = evFin F v (z i) := fun i => GlobalTheory.LatVac.evFin_liftV v _
  have e := congrFun (h R hr) Δ
  have hR2 : R Δ = R 0 := by simpa using hr.1 0 Δ hΔ
  have hR1 : R (Δ + p.1) = R 0 := by rw [hr.1 Δ p.1 hp1, hR2]
  simp only [schr, tens, Pi.smul_apply, smul_eq_mul] at e
  rw [hR1, hR2, dot_congr_at v hp2 hevΔ] at e
  have hev : (fun i => evFin F v ((Δ + p.1) i)) = fun i => evFin F v ((z + p.1) i) := by
    funext i; simp only [Pi.add_apply, map_add, hevΔ]
  have hev' : (fun i => evFin F v (Δ i)) = fun i => evFin F v (z i) := funext hevΔ
  rw [hev, hev'] at e
  exact mul_right_cancel₀ hR0 (by linear_combination e)

theorem acts_box {κ κ' : Type} [Fintype κ] [Fintype κ'] (v : Pl F) (ψ : AddChar (AF F) ℂ)
    {φ₁ : (κ → Fv F v) → ℂ} {φ₂ : (κ' → Fv F v) → ℂ} (X₁ Y₁ : κ → AF F)
    (X₂ Y₂ : κ' → AF F) (h11 : At (evFin F v) X₁) (h21 : At (evFin F v) X₂) (c₁ c₂ : ℂ)
    (h₁ : ∀ z, ψ (z ⬝ᵥ Y₁ + ⅟(2 : AF F) * (X₁ ⬝ᵥ Y₁)) * φ₁ (fun i => evFin F v ((z + X₁) i)) =
      c₁ * φ₁ (fun i => evFin F v (z i)))
    (h₂ : ∀ z, ψ (z ⬝ᵥ Y₂ + ⅟(2 : AF F) * (X₂ ⬝ᵥ Y₂)) * φ₂ (fun i => evFin F v ((z + X₂) i)) =
      c₂ * φ₂ (fun i => evFin F v (z i))) :
    Acts (evFin F v) (schr ψ (Sum.elim X₁ X₂, Sum.elim Y₁ Y₂)) (boxFun φ₁ φ₂)
      ((c₁ * c₂) • boxFun φ₁ φ₂) := by
  intro r hr
  have hX : At (evFin F v) (Sum.elim X₁ X₂ : κ ⊕ κ' → AF F) := by
    intro u hu; funext i
    cases i with
    | inl i => exact congrFun (h11 u hu) i
    | inr i => exact congrFun (h21 u hu) i
  funext x
  have hd1 : x ⬝ᵥ Sum.elim Y₁ Y₂ = (x ∘ Sum.inl) ⬝ᵥ Y₁ + (x ∘ Sum.inr) ⬝ᵥ Y₂ := by
    simp [dotProduct, Fintype.sum_sum_type]
  have hd2 : Sum.elim X₁ X₂ ⬝ᵥ Sum.elim Y₁ Y₂ = X₁ ⬝ᵥ Y₁ + X₂ ⬝ᵥ Y₂ :=
    by simp [dotProduct, Fintype.sum_sum_type]
  simp only [schr, tens, Pi.smul_apply, smul_eq_mul]
  rw [hr.1 x _ hX, hd1, hd2,
    show (x ∘ Sum.inl) ⬝ᵥ Y₁ + (x ∘ Sum.inr) ⬝ᵥ Y₂ + ⅟(2 : AF F) * (X₁ ⬝ᵥ Y₁ + X₂ ⬝ᵥ Y₂) =
      ((x ∘ Sum.inl) ⬝ᵥ Y₁ + ⅟(2 : AF F) * (X₁ ⬝ᵥ Y₁)) + ((x ∘ Sum.inr) ⬝ᵥ Y₂ + ⅟(2 : AF F) * (X₂ ⬝ᵥ Y₂))
      by ring, AddChar.map_add_eq_mul]
  have e1 := h₁ (x ∘ Sum.inl)
  have e2 := h₂ (x ∘ Sum.inr)
  simp only [boxFun, Function.comp_def, Pi.add_apply, Sum.elim_inl, Sum.elim_inr] at e1 e2 ⊢
  rw [show ∀ a e b f s : ℂ, a * e * ((b * f) * s) = (a * b) * (e * f) * s from fun _ _ _ _ _ => by ring, e1, e2]
  ring

end GlobalTheory.DblVacEigen

namespace GlobalTheory.DblVacEigen

theorem doubled_vac_eigen : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ (d' : Darboux (symp (cA σ) (-1 : AE F E) (incM F G.W.J) (incM F G.V.J)) (Fin a × Fin (a + a'))),
    (∀ x : Matrix (Fin a) (Fin (a + a')) (AE F E), d'.e xᵀ = G.M.co.e x) →
    ∀ (dd : Darboux (symp (cA σ) (-1 : AE F E) (incM F G.W.J) (dbl (incM F G.V.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')))),
    IsDblCoord (cA σ) (-1 : AE F E) (incM F G.W.J) (incM F G.V.J) d' dd →
    ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 →
    (∀ γ ∈ latAtV G.V G.W v, Acts (evFin F v) (G.M.co.rho B.ψ γ) (G.M.vac v)
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (incM F G.W.J) γ γ) • G.M.vac v)) →
    (∀ w₁ ∈ latAtV G.V G.W v, ∀ w₂ ∈ latAtV G.V G.W v,
      Acts (evFin F v) (dd.rho B.ψ (Matrix.fromCols w₁ᵀ w₂ᵀ)) (boxFun (G.M.vac v) (fun x => star (G.M.vac v x)))
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.W.J) (dbl (incM F G.V.J))
          (Matrix.fromCols w₁ᵀ w₂ᵀ) (Matrix.fromCols w₁ᵀ w₂ᵀ)) • (boxFun (G.M.vac v) (fun x => star (G.M.vac v x))))) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w _ _ d' hd' dd hdd θ _ hvac w₁ hw₁ w₂ hw₂
  have hSB := (hT.geo.hM.vac v).1
  have hψ : ∀ t, ‖B.ψ t‖ = 1 := GlobalTheory.StdCharWeilDatum.norm_psi hT.base.std
  have hstar : ∀ t, star (B.ψ t) = B.ψ (-t) := by
    intro t
    rw [AddChar.map_neg_eq_inv, Complex.inv_def, Complex.normSq_eq_norm_sq, hψ t]
    simp
  have hAt : ∀ γ ∈ latAtV G.V G.W v, At (evFin F v) γ := (GlobalTheory.LatVac.latAtV_at_stable G.V G.W v).1
  have hco : ∀ γ ∈ latAtV G.V G.W v, At (evFin F v) (G.M.co.e γ).1 ∧ At (evFin F v) (G.M.co.e γ).2 := by
    intro γ hγ
    have e : ∀ u, evFin F v u = 0 → u • G.M.co.e γ = 0 := fun u hu => by
      rw [← map_smul, hAt γ hγ u hu, map_zero]
    exact ⟨fun u hu => congrArg Prod.fst (e u hu), fun u hu => congrArg Prod.snd (e u hu)⟩
  have h1 := eigen_pointwise v B.ψ hSB (G.M.co.e w₁) (hco w₁ hw₁).1 (hco w₁ hw₁).2 _ (hvac w₁ hw₁)
  have h2 := eigen_pointwise v B.ψ hSB (G.M.co.e w₂) (hco w₂ hw₂).1 (hco w₂ hw₂).2 _ (hvac w₂ hw₂)
  have h2' : ∀ z, B.ψ (z ⬝ᵥ (-(G.M.co.e w₂).2) + ⅟(2 : AF F) * ((G.M.co.e w₂).1 ⬝ᵥ (-(G.M.co.e w₂).2))) *
      (fun x => star (G.M.vac v x)) (fun i => evFin F v ((z + (G.M.co.e w₂).1) i)) =
      star (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (incM F G.W.J) w₂ w₂)) * (fun x => star (G.M.vac v x)) (fun i => evFin F v (z i)) := by
    intro z
    have e := congrArg star (h2 z)
    simp only [star_mul, hstar] at e
    rw [hstar, show z ⬝ᵥ (-(G.M.co.e w₂).2) + ⅟(2 : AF F) * ((G.M.co.e w₂).1 ⬝ᵥ (-(G.M.co.e w₂).2)) =
      -(z ⬝ᵥ (G.M.co.e w₂).2 + ⅟(2 : AF F) * ((G.M.co.e w₂).1 ⬝ᵥ (G.M.co.e w₂).2)) by
        rw [dotProduct_neg, dotProduct_neg]; ring]
    linear_combination e
  have hbox := acts_box v B.ψ (φ₁ := G.M.vac v) (φ₂ := fun x => star (G.M.vac v x)) (G.M.co.e w₁).1 (G.M.co.e w₁).2 (G.M.co.e w₂).1 (-(G.M.co.e w₂).2)
    (hco w₁ hw₁).1 (hco w₂ hw₂).1 _ _ h1 h2'
  have hrho : dd.rho B.ψ (Matrix.fromCols w₁ᵀ w₂ᵀ) = schr B.ψ (Sum.elim (G.M.co.e w₁).1 (G.M.co.e w₂).1,
      Sum.elim (G.M.co.e w₁).2 (-(G.M.co.e w₂).2)) := by
    rw [Darboux.rho, hdd, hd', hd']
  have hS : symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.W.J) (dbl (incM F G.V.J))
      (Matrix.fromCols w₁ᵀ w₂ᵀ) (Matrix.fromCols w₁ᵀ w₂ᵀ) = symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (incM F G.W.J) w₁ w₁ - symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (incM F G.W.J) w₂ w₂ := by
    unfold symp
    rw [hTens_dbl, hTens_transpose, hTens_transpose, mul_sub, map_sub]
  have hc : B.ψ (⅟(2 : AF F) * (symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (incM F G.W.J) w₁ w₁ - symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (incM F G.W.J) w₂ w₂)) = B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (incM F G.W.J) w₁ w₁) * star (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (incM F G.W.J) w₂ w₂)) := by
    rw [hstar, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  rw [hrho, hS, hc]
  exact hbox

end GlobalTheory.DblVacEigen

end
