import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalTranslationEquivariant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEmbeddingAtEveryPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlCharacterFactorsThroughDetOfTwoNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearBarFunctionalGoodPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryDeterminedBySplitImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSmulOfCommuteHeisenbergLinearModelSchwartzBruhStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumSplitPlaceIndicatorSource
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceDarbouxWeil
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedSphericalVacuumFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzTensorNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMemAdelicSchwartzSpaceNumberFieldOfMemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagMemDoubledVacuumLatticeStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceIdempotentLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitLatticeDoubleVectorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumLatticeStabilizerPreservesDoubledSpStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearFunctionalGoodPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceEmbeddingExists
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.SplitVacFixRight
open GlobalTheory.DblVacSiegel

theorem doubled_vac_eigen_any : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F),
    ∀ (dd : Darboux (symp (cA σ) (-1 : AE F E) (incM F G.V'.J) (dbl (incM F G.W.J))) ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')))),
    IsDblCoord (cA σ) (-1 : AE F E) (incM F G.V'.J) (incM F G.W.J) G.M'.co dd →
    ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 →
    (∀ γ ∈ latAtV G.V' G.W v, Acts (evFin F v) (G.M'.co.rho B.ψ γ) (G.M'.vac v)
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) γ γ) • G.M'.vac v)) →
    (∀ w₁ ∈ latAtV G.V' G.W v, ∀ w₂ ∈ latAtV G.V' G.W v,
      Acts (evFin F v) (dd.rho B.ψ (Matrix.fromCols w₁ w₂)) (boxFun (G.M'.vac v) (fun x => star (G.M'.vac v x)))
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (dbl (incM F G.W.J))
          (Matrix.fromCols w₁ w₂) (Matrix.fromCols w₁ w₂)) • (boxFun (G.M'.vac v) (fun x => star (G.M'.vac v x))))) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v dd hdd θ _ hvac w₁ hw₁ w₂ hw₂
  have hSB := (hT.geo.hM'.vac v).1
  have hψ : ∀ t, ‖B.ψ t‖ = 1 := GlobalTheory.StdCharWeilDatum.norm_psi hT.base.std
  have hstar : ∀ t, star (B.ψ t) = B.ψ (-t) := by
    intro t
    rw [AddChar.map_neg_eq_inv, Complex.inv_def, Complex.normSq_eq_norm_sq, hψ t]
    simp
  have hAt : ∀ γ ∈ latAtV G.V' G.W v, At (evFin F v) γ := (GlobalTheory.LatVac.latAtV_at_stable G.V' G.W v).1
  have hco : ∀ γ ∈ latAtV G.V' G.W v, At (evFin F v) (G.M'.co.e γ).1 ∧ At (evFin F v) (G.M'.co.e γ).2 := by
    intro γ hγ
    have e : ∀ u, evFin F v u = 0 → u • G.M'.co.e γ = 0 := fun u hu => by
      rw [← map_smul, hAt γ hγ u hu, map_zero]
    exact ⟨fun u hu => congrArg Prod.fst (e u hu), fun u hu => congrArg Prod.snd (e u hu)⟩
  have h1 := GlobalTheory.DblVacEigen.eigen_pointwise v B.ψ hSB (G.M'.co.e w₁) (hco w₁ hw₁).1 (hco w₁ hw₁).2 _ (hvac w₁ hw₁)
  have h2 := GlobalTheory.DblVacEigen.eigen_pointwise v B.ψ hSB (G.M'.co.e w₂) (hco w₂ hw₂).1 (hco w₂ hw₂).2 _ (hvac w₂ hw₂)
  have h2' : ∀ z, B.ψ (z ⬝ᵥ (-(G.M'.co.e w₂).2) + ⅟(2 : AF F) * ((G.M'.co.e w₂).1 ⬝ᵥ (-(G.M'.co.e w₂).2))) *
      (fun x => star (G.M'.vac v x)) (fun i => evFin F v ((z + (G.M'.co.e w₂).1) i)) =
      star (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) w₂ w₂)) * (fun x => star (G.M'.vac v x)) (fun i => evFin F v (z i)) := by
    intro z
    have e := congrArg star (h2 z)
    simp only [star_mul, hstar] at e
    rw [hstar, show z ⬝ᵥ (-(G.M'.co.e w₂).2) + ⅟(2 : AF F) * ((G.M'.co.e w₂).1 ⬝ᵥ (-(G.M'.co.e w₂).2)) =
      -(z ⬝ᵥ (G.M'.co.e w₂).2 + ⅟(2 : AF F) * ((G.M'.co.e w₂).1 ⬝ᵥ (G.M'.co.e w₂).2)) by
        rw [dotProduct_neg, dotProduct_neg]; ring]
    linear_combination e
  have hbox := GlobalTheory.DblVacEigen.acts_box v B.ψ (φ₁ := G.M'.vac v) (φ₂ := fun x => star (G.M'.vac v x)) (G.M'.co.e w₁).1 (G.M'.co.e w₁).2 (G.M'.co.e w₂).1 (-(G.M'.co.e w₂).2)
    (hco w₁ hw₁).1 (hco w₂ hw₂).1 _ _ h1 h2'
  have hrho : dd.rho B.ψ (Matrix.fromCols w₁ w₂) = schr B.ψ (Sum.elim (G.M'.co.e w₁).1 (G.M'.co.e w₂).1,
      Sum.elim (G.M'.co.e w₁).2 (-(G.M'.co.e w₂).2)) := by
    rw [Darboux.rho, hdd]
  have hS : symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (dbl (incM F G.W.J))
      (Matrix.fromCols w₁ w₂) (Matrix.fromCols w₁ w₂) = symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) w₁ w₁ - symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) w₂ w₂ := by
    unfold symp
    rw [GlobalTheory.DblVacEigen.hTens_dbl, mul_sub, map_sub]
  have hc : B.ψ (⅟(2 : AF F) * (symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) w₁ w₁ - symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) w₂ w₂)) = B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) w₁ w₁) * star (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) w₂ w₂)) := by
    rw [hstar, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  rw [hrho, hS, hc]
  exact hbox

theorem transport_any : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F),
    ∀ (dd : Darboux (symp (cA σ) (-1 : AE F E) (incM F G.V'.J) (dbl (incM F G.W.J))) ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')))),
    IsDblCoord (cA σ) (-1 : AE F E) (incM F G.V'.J) (incM F G.W.J) G.M'.co dd →
    ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 →
    (∀ γ ∈ latAtV G.V' G.W v, Acts (evFin F v) (G.M'.co.rho B.ψ γ) (G.M'.vac v)
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) γ γ) • G.M'.vac v)) →
    ∀ (omd : GlobalTheory.DblVac.UD σ G.W →* Module.End ℂ (((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → AF F) → ℂ)),
    IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1 : AE F E) (incM F G.V'.J) (dbl (incM F G.W.J)) dd X.α (diagCols (Fin (a + a'))) omd →
    ∀ g ∈ GlobalTheory.DblVac.KD σ G.W v, ∀ φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v), ∀ φ₁ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v),
    (∀ w₁ ∈ latAtV G.V' G.W v, ∀ w₂ ∈ latAtV G.V' G.W v,
      Acts (evFin F v) (dd.rho B.ψ (Matrix.fromCols w₁ w₂)) φ
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (dbl (incM F G.W.J))
          (Matrix.fromCols w₁ w₂) (Matrix.fromCols w₁ w₂)) • φ)) → Acts (evFin F v) (omd g) φ φ₁ →
    (∀ w₁ ∈ latAtV G.V' G.W v, ∀ w₂ ∈ latAtV G.V' G.W v,
      Acts (evFin F v) (dd.rho B.ψ (Matrix.fromCols w₁ w₂)) φ₁
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (dbl (incM F G.W.J))
          (Matrix.fromCols w₁ w₂) (Matrix.fromCols w₁ w₂)) • φ₁)) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' _ v dd _ θ _ _ omd hsp g hg φ hφ φ₁ _ hfix hact w₁ hw₁ w₂ hw₂ r hr
  by_cases h0 : φ₁ = 0
  · subst h0
    funext x
    simp [Darboux.rho, schr, tens]
  have hr' : Rest (evFin F v) φ r := GlobalTheory.RestCofactor.rest_of_rest v φ₁ φ r h0 hφ hr
  obtain ⟨h1m, h2m⟩ := (GlobalTheory.T.doubledVacuumLatticeStabilizer_preserves_doubledSpaceLattice F E σ G.V' G.W v g hg (Matrix.fromCols w₁ w₂)
    ⟨by simpa using hw₁, by simpa using hw₂⟩).2
  have hsplit : Matrix.fromCols w₁ w₂ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ =
      Matrix.fromCols ((Matrix.fromCols w₁ w₂ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ).toCols₁)
        ((Matrix.fromCols w₁ w₂ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ).toCols₂) := by
    rw [Matrix.fromCols_toCols]
  have hback : actB (cA σ) g (Matrix.fromCols w₁ w₂ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ) = Matrix.fromCols w₁ w₂ := by
    change Matrix.fromCols w₁ w₂ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ * (GlobalTheory.DblVac.matD g)ᵀ = _
    have e : GlobalTheory.DblVac.matD g * GlobalTheory.DblVac.matD g⁻¹ = 1 := Units.mul_inv g.1
    rw [Matrix.mul_assoc, ← Matrix.transpose_mul, e, Matrix.transpose_one, Matrix.mul_one]
  have hsy := GlobalTheory.VacTransport.symp_mul_transpose (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J)
    (dbl (incM F G.W.J)) (GlobalTheory.DblVac.matD g⁻¹) (g⁻¹).2 (Matrix.fromCols w₁ w₂) (Matrix.fromCols w₁ w₂)
  have hf := hfix _ h1m _ h2m r hr'
  rw [← hsplit, hsy] at hf
  have h1 := hsp.2.1.impl g (Matrix.fromCols w₁ w₂ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ) _ hr'.2
  rw [hback, hf, GlobalTheory.VacTransport.tens_smul, map_smul, hact r hr'] at h1
  rw [← h1, GlobalTheory.VacTransport.tens_smul]

theorem line_any : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F),
    ∀ (dd : Darboux (symp (cA σ) (-1 : AE F E) (incM F G.V'.J) (dbl (incM F G.W.J))) ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')))),
    IsDblCoord (cA σ) (-1 : AE F E) (incM F G.V'.J) (incM F G.W.J) G.M'.co dd →
    ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 →
    (∀ γ ∈ latAtV G.V' G.W v, Acts (evFin F v) (G.M'.co.rho B.ψ γ) (G.M'.vac v)
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) γ γ) • G.M'.vac v)) →
    ∀ φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v), (∀ w₁ ∈ latAtV G.V' G.W v, ∀ w₂ ∈ latAtV G.V' G.W v,
      Acts (evFin F v) (dd.rho B.ψ (Matrix.fromCols w₁ w₂)) φ
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (dbl (incM F G.W.J))
          (Matrix.fromCols w₁ w₂) (Matrix.fromCols w₁ w₂)) • φ)) → ∃ c : ℂ, φ = c • (boxFun (G.M'.vac v) (fun x => star (G.M'.vac v x))) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v dd hdc θ hθ hvac φ hφSB hφ
  classical
  have hψ := hT.base.std
  have hn := GlobalTheory.StdCharFromIsStd.norm_psi hψ
  have hnv : ∀ t, ‖GlobalTheory.LatVac.psiAt B.ψ v t‖ = 1 := fun t => hn (GlobalTheory.LatVac.liftV v t)
  have hψc : Continuous (GlobalTheory.LatVac.psiAt B.ψ v) := GlobalTheory.SchrSB.continuous_psiAt B.ψ hψ.1 v
  have hψ1 : GlobalTheory.LatVac.psiAt B.ψ v ≠ 1 := GlobalTheory.PsiNontriv.psiAt_ne_one B.ψ hψ v
  set Λ := latAtV G.V' G.W v with hΛ
  have hat : ∀ γ ∈ Λ, At (evFin F v) γ := (GlobalTheory.LatVac.latAtV_at_stable G.V' G.W v).1
  obtain ⟨hvSB, hv0, -⟩ := hT.geo.hM'.vac v
  set φ₀ := G.M'.vac v with hφ₀
  set φd := boxFun φ₀ (fun x => star (φ₀ x)) with hφd
  have loc : ∀ {κ : Type} [Fintype κ] {W' : Type} [AddCommGroup W'] [Module (AF F) W'] {Bf : W' → W' → AF F}
      (d : Darboux Bf κ) (f : (κ → Fv F v) → ℂ), f ∈ SB _ → ∀ γ, At (evFin F v) γ → ∀ c : ℂ,
      Acts (evFin F v) (d.rho B.ψ γ) f (c • f) →
      schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo d v γ) f = c • f := by
    intro κ _ W' _ _ Bf d f hf γ hγ c h
    obtain ⟨r, hr, x₀, hx₀⟩ := GlobalTheory.RestComplement.exists_rest_ne_zero v f hf
    refine GlobalTheory.DblVacLine.eq_of_tens v hr.1 hx₀ ?_
    rw [← GlobalTheory.VacBridge.rho_acts_locCo d B.ψ v γ hγ f r hr]
    exact h r hr
  have hco : ∀ w₁ w₂ : Matrix (Fin a') (Fin (a + a')) (AE F E),
      GlobalTheory.LatVac.locCo dd v (Matrix.fromCols w₁ w₂) =
      (Sum.elim (GlobalTheory.LatVac.locCo G.M'.co v w₁).1 (GlobalTheory.LatVac.locCo G.M'.co v w₂).1,
        Sum.elim (GlobalTheory.LatVac.locCo G.M'.co v w₁).2 (-(GlobalTheory.LatVac.locCo G.M'.co v w₂).2)) := by
    intro w₁ w₂
    change ((fun k => evFin F v ((dd.e (Matrix.fromCols w₁ w₂)).1 k)),
      fun k => evFin F v ((dd.e (Matrix.fromCols w₁ w₂)).2 k)) = _
    rw [hdc]
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
    · cases k <;> rfl
    · cases k with
      | inl k => rfl
      | inr k => exact map_neg (evFin F v) _
  let χ : Matrix (Fin a') (Fin (a + a')) (AE F E) → ℂ := fun γ =>
    B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) γ γ)
  let cf : Matrix (Fin a') (Fin (a + a')) (AE F E) → Matrix (Fin a') (Fin (a + a')) (AE F E) → ℂ := fun w₁ w₂ =>
    B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (dbl (incM F G.W.J))
      (Matrix.fromCols w₁ w₂) (Matrix.fromCols w₁ w₂))
  have hcf : ∀ w₁ w₂, cf w₁ w₂ = χ w₁ * star (χ w₂) := by
    intro w₁ w₂
    simp only [cf, χ]
    rw [GlobalTheory.DblVacLine.symp_dbl, GlobalTheory.DblVacLine.star_eq_neg B.ψ hn, ← AddChar.map_add_eq_mul, mul_sub,
      sub_eq_add_neg]
  have hvl : ∀ γ ∈ Λ, schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v γ) φ₀ = χ γ • φ₀ :=
    fun γ h => loc G.M'.co φ₀ hvSB γ (hat γ h) _ (hvac γ h)
  have hφl : ∀ w₁ ∈ Λ, ∀ w₂ ∈ Λ,
      schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (Matrix.fromCols w₁ w₂)) φ = cf w₁ w₂ • φ :=
    fun w₁ h₁ w₂ h₂ => loc dd φ hφSB _ (GlobalTheory.DblVacLine.at_fromCols v (hat w₁ h₁) (hat w₂ h₂)) _ (hφ w₁ h₁ w₂ h₂)
  have hdl : ∀ w₁ ∈ Λ, ∀ w₂ ∈ Λ,
      schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (Matrix.fromCols w₁ w₂)) φd = cf w₁ w₂ • φd := by
    intro w₁ h₁ w₂ h₂
    rw [hco, hφd, GlobalTheory.DblVacLine.schr_box _ hnv, hvl w₁ h₁, hvl w₂ h₂, hcf]
    funext x
    simp only [boxFun, Pi.smul_apply, smul_eq_mul, star_mul']
    ring
  obtain ⟨c, hc0, hcb⟩ := GlobalTheory.LatBound.locCo_latAtV_bounded G.V' G.W v G.M'.co hT.geo.hV'.lat hT.geo.hW.lat
  have hsd := GlobalTheory.LatSelfDualAll.latAtV_selfDual F E σ B _ _ G.V' G.W _ _ _ _ hT.base hT.geo.hV' hT.geo.hW v
  have hfill := GlobalTheory.SelfDualFirstProjAny.exists_pair_of_annihilator_any F v (Fin a' × Fin (a + a'))
    (GlobalTheory.LatVac.psiAt B.ψ v) hψc hnv hψ1
    (Λ.map (GlobalTheory.LatVac.locCo G.M'.co v)) c hc0
    (GlobalTheory.LatVac.DualLoc.map_selfDual v G.M'.co B.ψ Λ hat hsd)
    (fun l hl i => by
      obtain ⟨γ, hγ, rfl⟩ := AddSubgroup.mem_map.mp hl
      exact hcb γ hγ i)
  have hφd0 : φd ≠ 0 := by
    obtain ⟨t, ht⟩ := Function.ne_iff.mp hv0
    refine Function.ne_iff.mpr ⟨Sum.elim t t, ?_⟩
    show φ₀ t * star (φ₀ t) ≠ 0
    exact mul_ne_zero ht (star_ne_zero.mpr ht)
  obtain ⟨c', hc'⟩ := GlobalTheory.VacUniqInert.eq_smul_of_eigen (GlobalTheory.LatVac.psiAt B.ψ v)
    (fun i : Λ × Λ => GlobalTheory.LatVac.locCo dd v (Matrix.fromCols i.1.1 i.2.1))
    (fun i => cf i.1.1 i.2.1) (fun u hu => by
      have eu : u = Sum.elim (u ∘ Sum.inl) (u ∘ Sum.inr) := (Sum.elim_comp_inl_inr u).symm
      obtain ⟨y₁, γ₁, h₁, e₁⟩ := hfill (u ∘ Sum.inl) (by
        rintro b ⟨γ, hγ, he⟩
        have := hu (⟨γ, hγ⟩, 0) (by
          simp only [hco, he, ZeroMemClass.coe_zero, map_zero]
          funext k; cases k <;> rfl)
        simp only [hco, he, ZeroMemClass.coe_zero, map_zero] at this
        rw [eu, sumElim_dotProduct_sumElim] at this
        simpa using this)
      obtain ⟨y₂, γ₂, h₂, e₂⟩ := hfill (u ∘ Sum.inr) (by
        rintro b ⟨γ, hγ, he⟩
        have := hu (0, ⟨-γ, neg_mem hγ⟩) (by
          simp only [hco, he, ZeroMemClass.coe_zero, map_zero, map_neg]
          funext k; cases k <;> simp)
        simp only [hco, he, ZeroMemClass.coe_zero, map_zero, map_neg] at this
        rw [eu, sumElim_dotProduct_sumElim] at this
        simpa using this)
      refine ⟨(⟨γ₁, h₁⟩, ⟨γ₂, h₂⟩), ?_⟩
      simp only [hco, e₁, e₂]
      exact eu.symm) φ φd
    (fun i => hφl _ i.1.2 _ i.2.2) (fun i => hdl _ i.1.2 _ i.2.2) hφd0
  exact ⟨c', hc'⟩

theorem split_vdbl_eigen : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → v ∉ X.T →
    ∀ (dd : Darboux (symp (cA σ) (-1 : AE F E) (incM F G.V'.J) (dbl (incM F G.W.J))) ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a'))))
      (omd : GlobalTheory.DblVac.UD σ G.W →* Module.End ℂ (((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → AF F) → ℂ)),
    IsDblCoord (cA σ) (-1 : AE F E) (incM F G.V'.J) (incM F G.W.J) G.M'.co dd →
    IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1 : AE F E) (incM F G.V'.J) (dbl (incM F G.W.J)) dd X.α (diagCols (Fin (a + a'))) omd →
    ∀ r : (Fin a' × Fin (a + a') → AF F) → ℂ, Rest (evFin F v) (G.M'.vac v) r →
    ∀ g ∈ GlobalTheory.DblVac.KD σ G.W v, ∃ μ : ℂ,
      omd g (boxFun (tens (evFin F v) (G.M'.vac v) r) (fun x => star (tens (evFin F v) (G.M'.vac v) r x))) =
        μ • boxFun (tens (evFin F v) (G.M'.vac v) r) (fun x => star (tens (evFin F v) (G.M'.vac v) r x)) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v _ _ dd omd hdc hsp r hr g hg
  obtain ⟨hvSB, -, θ, hθ, hvac⟩ := hT.geo.hM'.vac v
  set φ := G.M'.vac v with hφ
  set vD := boxFun φ (fun x => star (φ x)) with hvD
  set RD := boxFun r (fun x => star (r x)) with hRD
  have hvDSB : vD ∈ SB _ := GlobalTheory.VDblEigAny.boxFun_mem_SB hvSB (GlobalTheory.VDblEigAny.star_mem_SB hvSB)
  have hS : boxFun (tens (evFin F v) φ r) (fun x => star (tens (evFin F v) φ r x)) = tens (evFin F v) vD RD := by
    funext x
    simp only [tens, boxFun, hvD, hRD, Function.comp_def, star_mul']
    ring
  have hRest : Rest (evFin F v) vD RD := by
    refine ⟨fun x z hz => ?_, ?_⟩
    · have hz1 : At (evFin F v) (z ∘ Sum.inl) := fun u hu => by
        funext i; exact congrFun (hz u hu) (Sum.inl i)
      have hz2 : At (evFin F v) (z ∘ Sum.inr) := fun u hu => by
        funext i; exact congrFun (hz u hu) (Sum.inr i)
      show r ((x + z) ∘ Sum.inl) * star (r ((x + z) ∘ Sum.inr)) = r (x ∘ Sum.inl) * star (r (x ∘ Sum.inr))
      rw [show (x + z) ∘ Sum.inl = x ∘ Sum.inl + z ∘ Sum.inl from rfl,
        show (x + z) ∘ Sum.inr = x ∘ Sum.inr + z ∘ Sum.inr from rfl, hr.1 _ _ hz1, hr.1 _ _ hz2]
    · rw [← hS]
      exact GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ _ hr.2 _ (GlobalTheory.ConjSch.star_mem_schA _ _ hr.2)
  have hU := hsp.2.1
  obtain ⟨φ₁, hφ₁, hA⟩ : ∃ φ₁ ∈ SB _, Acts (evFin F v) (omd g) vD φ₁ := by
    refine GlobalTheory.DblActs.acts_of_comm v B.ψ hT.base.std (omd g) (fun Φ hΦ => hU.pres g Φ hΦ)
      (fun μ hμ Φ hΦ => hU.unit μ hμ g Φ hΦ) ?_ vD hvDSB
    intro u hu x y Φ hΦ
    set z := dd.e.symm (x, y) with hz
    have he : dd.e (u • z) = (u • x, u • y) := by
      rw [LinearEquiv.map_smul, hz, LinearEquiv.apply_symm_apply, Prod.smul_mk]
    have h2 := hg.1 u hu
    have e2 : actB (cA σ) g (u • z) = u • z := by
      simp only [actB]
      set P := GlobalTheory.DblVac.matD g with hP
      set c : AE F E := algebraMap (AF F) (AE F E) u with hc
      have hs1 : u • z = c • z := (algebraMap_smul (AE F E) u z).symm
      have hs2 : u • (P - 1) = c • (P - 1) := (algebraMap_smul (AE F E) u (P - 1)).symm
      have h2' : c • (P - 1) = 0 := hs2 ▸ h2
      have : (c • z) * Pᵀ - c • z = z * (c • (P - 1))ᵀ := by
        rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_sub, Matrix.transpose_one,
          Matrix.mul_sub, Matrix.mul_one, smul_sub]
      rw [h2'] at this
      simp only [Matrix.transpose_zero, Matrix.mul_zero, sub_eq_zero] at this
      rw [hs1]
      exact this
    have h3 := hU.impl g (u • z) Φ hΦ
    simp only [Darboux.rho, he, e2] at h3
    exact h3
  have hE0 := doubled_vac_eigen_any F E σ B a a' G X om om' hT v dd hdc θ hθ hvac
  have hE1 := transport_any F E σ B a a' G X om om' hT v dd hdc θ hθ hvac omd hsp g hg vD hvDSB φ₁ hφ₁ hE0 hA
  obtain ⟨μ, hμ⟩ := line_any F E σ B a a' G X om om' hT v dd hdc θ hθ hvac φ₁ hφ₁ hE1
  refine ⟨μ, ?_⟩
  rw [hS, hA RD hRest, hμ]
  funext x
  simp only [tens, Pi.smul_apply, smul_eq_mul]
  ring

theorem siegel_eigen_eq_one_any : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), v ∉ X.T →
    ∀ (dd : Darboux (symp (cA σ) (-1 : AE F E) (incM F G.V'.J) (dbl (incM F G.W.J))) ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a'))))
      (omd : GlobalTheory.DblVac.UD σ G.W →* Module.End ℂ (((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → AF F) → ℂ)),
    IsDblCoord (cA σ) (-1 : AE F E) (incM F G.V'.J) (incM F G.W.J) G.M'.co dd →
    IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1 : AE F E) (incM F G.V'.J) (dbl (incM F G.W.J)) dd X.α (diagCols (Fin (a + a'))) omd →
    ∀ r : (Fin a' × Fin (a + a') → AF F) → ℂ, Rest (evFin F v) (G.M'.vac v) r → tens (evFin F v) (G.M'.vac v) r ≠ 0 →
    ∀ p ∈ GlobalTheory.DblVac.KD σ G.W v, p ∈ GlobalTheory.DblVac.PDiag σ G.W → ∀ μ : ℂ,
      omd p (boxFun (tens (evFin F v) (G.M'.vac v) r) (fun x => star (tens (evFin F v) (G.M'.vac v) r x))) =
        μ • boxFun (tens (evFin F v) (G.M'.vac v) r) (fun x => star (tens (evFin F v) (G.M'.vac v) r x)) → μ = 1 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v hv dd omd hdd hW r hr h0 p hp hpd μ hμ
  obtain ⟨t, ht₀⟩ := hpd
  have ht : GlobalTheory.DblVac.matD p * (diagCols (Fin (a + a')) : Matrix (Fin (a + a') ⊕ Fin (a + a')) (Fin (a + a')) (AE F E)) =
      (diagCols (Fin (a + a')) : Matrix (Fin (a + a') ⊕ Fin (a + a')) (Fin (a + a')) (AE F E)) * (t : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) := ht₀
  have hF := hT.base.cm.1
  set Ψ := tens (evFin F v) (G.M'.vac v) r with hΨ
  have hS := GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ Ψ hr.2 _ (GlobalTheory.SchAConj.star_mem_schA F _ Ψ hr.2)
  have hl := lDiag_box_ne_zero hF hr.2 h0
  have hS0 : (boxFun Ψ fun x => star (Ψ x)) ≠ 0 := fun h => hl (by rw [h, map_zero])
  have hn := norm_eq_one_of_eigen hF hW.2.1.unit hS hS0 hμ
  have hrule := hW.2.2 _ DiagForm.lDiag_adm (fun z φ hφ => by
    have e : z * (diagCols (Fin (a + a')) : Matrix _ _ (AE F E))ᵀ = Matrix.fromCols z z := by
      rw [diagCols, Matrix.transpose_fromRows, Matrix.mul_fromCols, Matrix.transpose_one, Matrix.mul_one]
    rw [e, Darboux.rho, hdd]
    exact DiagForm.lDiag_schr B.ψ _ _ hφ) p t ht _ hS
  have hvec : ∀ (g : GlobalTheory.DblVac.UD σ G.W) (s : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)),
      GlobalTheory.DblVac.matD g * (diagCols (Fin (a + a')) : Matrix (Fin (a + a') ⊕ Fin (a + a')) (Fin (a + a')) (AE F E)) = (diagCols (Fin (a + a')) : Matrix (Fin (a + a') ⊕ Fin (a + a')) (Fin (a + a')) (AE F E)) * s → ∀ z,
      (GlobalTheory.DblVac.matD g *ᵥ Sum.elim z z) ∘ Sum.inl = s *ᵥ z := fun g s hs z => by
    have e : ∀ z : Fin (a + a') → AE F E, (diagCols (Fin (a + a')) : Matrix (Fin (a + a') ⊕ Fin (a + a')) (Fin (a + a')) (AE F E)) *ᵥ z = Sum.elim z z := fun z => by
      rw [diagCols, Matrix.fromRows_mulVec, Matrix.one_mulVec]
    rw [← e, Matrix.mulVec_mulVec, hs, ← Matrix.mulVec_mulVec, e]
    rfl
  have ht' : GlobalTheory.DblVac.matD p⁻¹ * (diagCols (Fin (a + a')) : Matrix (Fin (a + a') ⊕ Fin (a + a')) (Fin (a + a')) (AE F E)) =
      (diagCols (Fin (a + a')) : Matrix (Fin (a + a') ⊕ Fin (a + a')) (Fin (a + a')) (AE F E)) * ((t⁻¹ : GL (Fin (a + a')) (AE F E)) : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) := by
    have e1 : GlobalTheory.DblVac.matD p⁻¹ * GlobalTheory.DblVac.matD p = 1 := p.1.inv_mul
    calc _ = GlobalTheory.DblVac.matD p⁻¹ * ((diagCols (Fin (a + a')) : Matrix (Fin (a + a') ⊕ Fin (a + a')) (Fin (a + a')) (AE F E)) * (t : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E))) *
          ((t⁻¹ : GL (Fin (a + a')) (AE F E)) : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, t.mul_inv, Matrix.mul_one]
      _ = _ := by rw [← ht, ← Matrix.mul_assoc, e1, Matrix.one_mul]
  have hunr : ∀ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) = v → UnrAt X.α P := fun P hP => by
    have hPT : P ∉ above E (X.T : Set (Pl F)) := fun h => hv (hP ▸ (h : P.under (𝓞 F) ∈ (X.T : Set (Pl F))))
    exact hT.chars.unrα P hPT
  have hβ : X.α (Matrix.GeneralLinearGroup.det t) = 1 := by
    refine GlobalTheory.DblVacSiegelAny.chr_det_eq_one_any (v := v) G.W hT.geo.hW.lat hunr t (fun u hu => ?_) fun z hz => ?_
    · have e1 : (GlobalTheory.DblVac.matD p - 1) * (diagCols (Fin (a + a')) : Matrix (Fin (a + a') ⊕ Fin (a + a')) (Fin (a + a')) (AE F E)) =
          (diagCols (Fin (a + a')) : Matrix (Fin (a + a') ⊕ Fin (a + a')) (Fin (a + a')) (AE F E)) * ((t : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) - 1) := by
        rw [Matrix.sub_mul, Matrix.mul_sub, ht, Matrix.one_mul, Matrix.mul_one]
      have e2 : (diagCols (Fin (a + a')) : Matrix (Fin (a + a') ⊕ Fin (a + a')) (Fin (a + a')) (AE F E)) * (u • ((t : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) - 1)) = 0 := by
        rw [Matrix.mul_smul, ← e1, ← Matrix.smul_mul, hp.1 u hu, Matrix.zero_mul]
      rw [diagCols, Matrix.fromRows_mul, Matrix.one_mul] at e2
      ext i j
      exact congrFun (congrFun e2 (Sum.inl i)) j
    · have hz' := hp.2 (Sum.elim z z) ⟨hz, hz⟩
      exact ⟨hvec p _ ht z ▸ hz'.1.1, hvec p⁻¹ _ ht' z ▸ hz'.2.1⟩
  rw [hμ, map_smul, smul_eq_mul, hβ, Circle.coe_one, one_mul] at hrule
  have hμ' := mul_right_cancel₀ hl hrule
  rw [hμ', Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)] at hn
  rw [hμ', hn, Complex.ofReal_one]

theorem vac_fixed_split_right : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), Nonempty (E →ₐ[F] Fv F v) → v ∉ X.T →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v, Acts (evFin F v) (om' (1, k)) (G.M'.vac v) (G.M'.vac v) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v hsp₁ hv k hk r hr
  have hsp₀ := GlobalTheory.SplitSphV.isSplit_of_nonempty hT.base.cm hsp₁
  obtain ⟨-, dd, omd, hdc, hsp, hbox⟩ := hT.weil'.1
  by_cases hr0 : tens (evFin F v) (G.M'.vac v) r = 0
  · rw [hr0, map_zero]
  set V₀ := tens (evFin F v) (G.M'.vac v) r with hV₀
  set S := boxFun V₀ (fun x => star (V₀ x)) with hS
  obtain ⟨x₀, hx₀⟩ := Function.ne_iff.mp hr0
  have hx₀' : V₀ x₀ ≠ 0 := hx₀
  have hSne : S ≠ 0 := fun h => by
    have := congrFun h (Sum.elim x₀ x₀)
    simp only [hS, boxFun, Sum.elim_comp_inl, Sum.elim_comp_inr, Pi.zero_apply] at this
    exact mul_ne_zero hx₀' (star_ne_zero.mpr hx₀') this
  obtain ⟨gd, hgd, hgdK⟩ := GlobalTheory.T.exists_diag_mem_doubledVacuumLatticeStabilizer σ G.W v k hk
  have hb := hbox k gd hgd V₀ hr.2 (fun x => star (V₀ x)) (GlobalTheory.T.conj_mem_adelicSchwartzSpaceNumberField_of_mem _ V₀ hr.2)
  obtain ⟨c, hgS⟩ := split_vdbl_eigen F E σ B a a' G X om om' hT v hsp₀ hv dd omd hdc hsp r hr gd hgdK
  change omd gd S = c • S at hgS
  obtain ⟨e, θ, he1, he2, he3, hθ1, hθ2, hθ3, hθ4⟩ := GlobalTheory.T.split_place_idempotent_lattice σ B hT.base v hsp₀
  obtain ⟨w₀, hw₀, hW⟩ := GlobalTheory.T.split_lattice_double_vector σ G.W v e θ he1 he2 he3 hθ1 hθ2 hθ3 (hθ4 G.W)
  obtain ⟨h1, h2⟩ := hW k hk gd hgd hgdK
  obtain ⟨μ, hμ⟩ := split_vdbl_eigen F E σ B a a' G X om om' hT v hsp₀ hv dd omd hdc hsp r hr w₀ hw₀
  change omd w₀ S = μ • S at hμ
  have e0 : omd w₀⁻¹ (omd w₀ S) = S := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hμ0 : μ ≠ 0 := fun h0 => by
    apply hSne
    rw [← e0, hμ, h0, zero_smul, map_zero]
  have hinv : omd w₀⁻¹ S = μ⁻¹ • S := by
    rw [hμ, LinearMap.map_smul] at e0
    calc omd w₀⁻¹ S = μ⁻¹ • (μ • omd w₀⁻¹ S) := by rw [smul_smul, inv_mul_cancel₀ hμ0, one_smul]
      _ = μ⁻¹ • S := by rw [e0]
  have hp : omd (w₀ * gd * w₀⁻¹) S = c • S := by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hinv, LinearMap.map_smul, hgS,
      LinearMap.map_smul, LinearMap.map_smul, hμ, smul_smul, smul_smul]
    rw [show μ⁻¹ * c * μ = c by field_simp]
  have hc := siegel_eigen_eq_one_any F E σ B a a' G X om om' hT v hv dd omd hdc hsp r hr hr0 _ h1 h2 c hp
  rw [hc, one_smul] at hgS
  change omd gd S = _ at hb
  rw [hgS] at hb
  funext x
  have hx := congrFun hb (Sum.elim x x₀)
  simp only [hS, boxFun, Sum.elim_comp_inl, Sum.elim_comp_inr, MonoidHom.comp_apply, MonoidHom.inr_apply] at hx
  exact (mul_right_cancel₀ (star_ne_zero.mpr hx₀') hx).symm

theorem vac_fixed_good : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W B.v₁, Acts (evFin F B.v₁) (om' (1, k)) (G.M'.vac B.v₁) (G.M'.vac B.v₁) :=
  fun _ F E _ _ _ _ _ σ B a a' G X om om' hT k hk =>
    vac_fixed_split_right F E σ B a a' G X om om' hT B.v₁ ⟨B.τ₁⟩ hT.chars.good.1 k hk

end GlobalTheory.SplitVacFixRight

end
