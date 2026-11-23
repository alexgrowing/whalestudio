import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergEigenLatticePointAtPlaceLocalIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import ReciprocityTheory.GeneralLinearIntegers.AlgebraMapIntMemOint
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.DblVacLine

theorem norm_psiAt_le {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) (v : Pl F)
    (y : Fv F v) : ‖GlobalTheory.LatVac.psiAt ψ v y‖ ≤ 1 := by
  have hc := GlobalTheory.SchrSB.continuous_psiAt ψ hψ v
  have hK := (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v).image
    (f := fun t : Fv F v => ‖GlobalTheory.LatVac.psiAt ψ v (y * t)‖) ((hc.comp (continuous_const.mul continuous_id)).norm)
  obtain ⟨C, hC⟩ := hK.bddAbove
  by_contra h
  push_neg at h
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C h
  have hle : ‖GlobalTheory.LatVac.psiAt ψ v y‖ ^ n ≤ C := by
    refine hC ⟨(n : Fv F v), natCast_mem _ n, ?_⟩
    show ‖GlobalTheory.LatVac.psiAt ψ v (y * (n : Fv F v))‖ = _
    rw [mul_comm, ← nsmul_eq_mul, AddChar.map_nsmul_eq_pow, norm_pow]
  linarith

theorem norm_psiAt {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) (v : Pl F)
    (y : Fv F v) : ‖GlobalTheory.LatVac.psiAt ψ v y‖ = 1 := by
  have h1 := norm_psiAt_le ψ hψ v y
  have h2 := norm_psiAt_le ψ hψ v (-y)
  have h3 : ‖GlobalTheory.LatVac.psiAt ψ v y‖ * ‖GlobalTheory.LatVac.psiAt ψ v (-y)‖ = 1 := by
    rw [← norm_mul, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one, norm_one]
  nlinarith [norm_nonneg (GlobalTheory.LatVac.psiAt ψ v y), norm_nonneg (GlobalTheory.LatVac.psiAt ψ v (-y))]

theorem star_psiAt {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) (v : Pl F)
    (y : Fv F v) : star (GlobalTheory.LatVac.psiAt ψ v y) = GlobalTheory.LatVac.psiAt ψ v (-y) := by
  rw [AddChar.map_neg_eq_inv]
  refine eq_inv_of_mul_eq_one_left ?_
  rw [Complex.star_def, Complex.conj_mul', norm_psiAt ψ hψ v y]
  simp

theorem symp_dbl_fromCols {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E)
    (w₁ w₂ : Matrix α β E) :
    symp (R := R) c ξ JA (dbl JB) (Matrix.fromCols w₁ w₂) (Matrix.fromCols w₁ w₂) =
      symp (R := R) c ξ JA JB w₁ w₁ - symp (R := R) c ξ JA JB w₂ w₂ := by
  unfold symp
  rw [← map_sub, ← mul_sub]
  congr 2
  unfold hTens
  simp only [dbl, Fintype.sum_sum_type, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    Matrix.zero_apply, Matrix.neg_apply, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add, mul_neg,
    neg_mul, Finset.sum_neg_distrib]
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, sub_eq_add_neg]

theorem at_symp_self {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n d : ℕ} (JA : Matrix (Fin n) (Fin n) (AE F E)) (JB : Matrix (Fin d) (Fin d) (AE F E))
    (ξ : AE F E) (v : Pl F) {w : Matrix (Fin n) (Fin d) (AE F E)} (hw : At (evFin F v) w) :
    At (evFin F v) (symp (R := AF F) (cA σ) ξ JA JB w w) := by
  intro u hu
  have h1 := GlobalTheory.LatVac.symp_smul_smul σ JA JB ξ u 1 w w
  have h0 := GlobalTheory.LatVac.symp_smul_smul σ JA JB ξ 0 1 w w
  rw [hw u hu, mul_one] at h1
  rw [zero_smul, zero_mul, zero_mul] at h0
  rw [smul_eq_mul, ← h1, h0]

end GlobalTheory.DblVacLine

namespace GlobalTheory.DblVacLine

theorem dbl_vac_acts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (dd : Darboux (symp (cA σ) (-1) (incM F G.V'.J) (dbl (incM F G.W.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a'))), IsDblCoord (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J) G.M'.co dd →
    ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 →
    (∀ γ ∈ latAtV G.V' G.W v, Acts (evFin F v) (G.M'.co.rho B.ψ γ) (G.M'.vac v)
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) γ γ) • (G.M'.vac v))) →
    (∀ w₁ ∈ latAtV G.V' G.W v, ∀ w₂ ∈ latAtV G.V' G.W v,
      Acts (evFin F v) (dd.rho B.ψ (Matrix.fromCols w₁ w₂)) (boxFun (G.M'.vac v) (fun x => star (G.M'.vac v x)))
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (dbl (incM F G.W.J))
          (Matrix.fromCols w₁ w₂) (Matrix.fromCols w₁ w₂)) • (boxFun (G.M'.vac v) (fun x => star (G.M'.vac v x))))) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v dd hdd θ hθ hvac w₁ hw₁ w₂ hw₂
  have hψc : Continuous B.ψ := hT.base.std.1
  have hSB : G.M'.vac v ∈ SB _ := (hT.geo.hM'.vac v).1
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest (F := F) (Fin a' × Fin (a + a')) v
  have hat := (GlobalTheory.LatVac.latAtV_at_stable G.V' G.W v).1
  have hloc : ∀ w ∈ latAtV G.V' G.W v, ∀ ξ, GlobalTheory.LatVac.psiAt B.ψ v (ξ ⬝ᵥ (GlobalTheory.LatVac.locCo G.M'.co v w).2 +
        (2 : Fv F v)⁻¹ * ((GlobalTheory.LatVac.locCo G.M'.co v w).1 ⬝ᵥ (GlobalTheory.LatVac.locCo G.M'.co v w).2)) *
      G.M'.vac v (ξ + (GlobalTheory.LatVac.locCo G.M'.co v w).1) =
        B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) w w) *
          G.M'.vac v ξ := fun w hw ξ =>
    GlobalTheory.LatVac.heis_at_local_identity v G.M'.co B.ψ w _ _ (hat w hw) (hvac w hw) R (hR _ hSB) 0 hR0 ξ
  have hatd : At (evFin F v) (Matrix.fromCols w₁ w₂) := by
    intro u hu
    have h1 := hat w₁ hw₁ u hu
    have h2 := hat w₂ hw₂ u hu
    ext i j
    rcases j with j | j
    · simpa using congrFun (congrFun h1 i) j
    · simpa using congrFun (congrFun h2 i) j
  have key := GlobalTheory.VacBridge.rho_acts_locCo dd B.ψ v _ hatd (boxFun (G.M'.vac v) (fun x => star (G.M'.vac v x)))

  set x₁ := (GlobalTheory.LatVac.locCo G.M'.co v w₁).1 with hx₁
  set y₁ := (GlobalTheory.LatVac.locCo G.M'.co v w₁).2 with hy₁
  set x₂ := (GlobalTheory.LatVac.locCo G.M'.co v w₂).1 with hx₂
  set y₂ := (GlobalTheory.LatVac.locCo G.M'.co v w₂).2 with hy₂
  have hdl : GlobalTheory.LatVac.locCo dd v (Matrix.fromCols w₁ w₂) = (Sum.elim x₁ x₂, Sum.elim y₁ (-y₂)) := by
    simp only [hx₁, hx₂, hy₁, hy₂, GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hdd w₁ w₂]
    ext k <;> rcases k with k | k <;> simp
  set s₁ := symp (R := AF F) (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) w₁ w₁ with hs₁
  set s₂ := symp (R := AF F) (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) w₂ w₂ with hs₂
  have hb : At (evFin F v) (⅟(2 : AF F) * s₂) :=
    GlobalTheory.VacIndic.at_mul_left (at_symp_self σ _ _ _ v (hat w₂ hw₂))
  have hstarg : star (B.ψ (⅟(2 : AF F) * s₂)) = B.ψ (-(⅟(2 : AF F) * s₂)) := by
    have hb' : At (evFin F v) (-(⅟(2 : AF F) * s₂)) := fun u hu => by rw [smul_neg, hb u hu, neg_zero]
    rw [GlobalTheory.VacIndic.psi_of_at B.ψ hb, GlobalTheory.VacIndic.psi_of_at B.ψ hb', map_neg, ← GlobalTheory.LatVac.psiAt_apply,
      ← GlobalTheory.LatVac.psiAt_apply, star_psiAt B.ψ hψc v]
  have hcd : B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (dbl (incM F G.W.J))
      (Matrix.fromCols w₁ w₂) (Matrix.fromCols w₁ w₂)) = B.ψ (⅟(2 : AF F) * s₁) * star (B.ψ (⅟(2 : AF F) * s₂)) := by
    rw [symp_dbl_fromCols, ← hs₁, ← hs₂, hstarg, mul_sub, sub_eq_add_neg, AddChar.map_add_eq_mul]
  have e : GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (Matrix.fromCols w₁ w₂))
      (boxFun (G.M'.vac v) (fun x => star (G.M'.vac v x))) =
      B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (dbl (incM F G.W.J))
        (Matrix.fromCols w₁ w₂) (Matrix.fromCols w₁ w₂)) • boxFun (G.M'.vac v) (fun x => star (G.M'.vac v x)) := by
    funext x
    rw [hdl, hcd]
    simp only [GlobalTheory.WeilM.schr, boxFun, Pi.smul_apply, smul_eq_mul, invOf_eq_inv]
    have hA : x ⬝ᵥ Sum.elim y₁ (-y₂) + (2 : Fv F v)⁻¹ * (Sum.elim x₁ x₂ ⬝ᵥ Sum.elim y₁ (-y₂)) =
        ((x ∘ Sum.inl) ⬝ᵥ y₁ + (2 : Fv F v)⁻¹ * (x₁ ⬝ᵥ y₁)) +
          -((x ∘ Sum.inr) ⬝ᵥ y₂ + (2 : Fv F v)⁻¹ * (x₂ ⬝ᵥ y₂)) := by
      simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Function.comp_apply, Pi.neg_apply,
        mul_neg, Finset.sum_neg_distrib]
      ring
    have h1 : (x + Sum.elim x₁ x₂) ∘ Sum.inl = x ∘ Sum.inl + x₁ := by funext i; simp
    have h2 : (x + Sum.elim x₁ x₂) ∘ Sum.inr = x ∘ Sum.inr + x₂ := by funext i; simp
    rw [hA, AddChar.map_add_eq_mul, ← star_psiAt B.ψ hψc v, h1, h2]
    have l1 := hloc w₁ hw₁ (x ∘ Sum.inl)
    have l2 := congrArg star (hloc w₂ hw₂ (x ∘ Sum.inr))
    rw [star_mul', star_mul'] at l2
    linear_combination (star (GlobalTheory.LatVac.psiAt B.ψ v ((x ∘ Sum.inr) ⬝ᵥ y₂ + (2 : Fv F v)⁻¹ * (x₂ ⬝ᵥ y₂))) *
      star (G.M'.vac v (x ∘ Sum.inr + x₂))) * l1 + (B.ψ (⅟(2 : AF F) * s₁) * G.M'.vac v (x ∘ Sum.inl)) * l2
  rw [← e]
  exact key

end GlobalTheory.DblVacLine
