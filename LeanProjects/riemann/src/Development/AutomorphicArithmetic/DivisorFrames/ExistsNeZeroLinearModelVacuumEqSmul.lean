import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.FinMatchDefs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaussianDatumFlippedFiniteTensorBigRoute
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLagrModelOfIsLin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergLatticeSelfDualEveryFinitePlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeAtFinitePlaceEqSumSplitPlaceParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentMapsForThetaTriple

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model piW chrW unifAt latAtV At SInf)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section SlopeTestRemainingChoices

open GlobalTheory.LinCoords GlobalTheory.WeilM

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

private theorem hTens_half (h : IsCMExt F E σ) {v : HeightOneSpectrum (𝓞 F)} (t : E →ₐ[F] Fv F v) {n d : ℕ}
    (JA : Matrix (Fin n) (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)) (JB : Matrix (Fin d) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E))
    {x y : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)} (hx : At (evFin F v) x) (hx0 : x.map (piW t) = 0)
    (hy0 : y.map (piW t) = 0) : hTens (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) JA JB x y = 0 := by
  have hs : ∀ e, σ (σ e) = e := fun e => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [h.2.2.2, h.2.2.2, star_star]
  have ht : (t.comp σ).comp σ = t := AlgHom.ext fun e => by simp [hs]
  unfold hTens
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun k _ =>
    Finset.sum_eq_zero fun l _ => ?_
  have h1 : piW t (x a b) = 0 := congrFun (congrFun hx0 a) b
  have h2 : piW t (y k l) = 0 := congrFun (congrFun hy0 k) l
  have hat : At (evFin F v) (x a b * JA a k * JB b l * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ (y k l)) := fun u hu => by
    rw [← smul_mul_assoc, ← smul_mul_assoc, ← smul_mul_assoc, (at_mat_iff x).1 hx a b u hu, zero_mul, zero_mul, zero_mul]
  rw [eq_lift2 h t hat, map_mul, map_mul, map_mul, h1, map_mul (piW (t.comp σ)), piW_cA' (t.comp σ), ht, h2, zero_mul, zero_mul, zero_mul, mul_zero,
    lift2_zero]

end SlopeTestRemainingChoices

theorem UpperTheory.exists_ne_zero_linearModel_vacuum_eq_smul :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
        (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s →
        W.IsSkew σ B r' s' → M.IsGood B.ψ →
        ∀ (v : HeightOneSpectrum (𝓞 F)) (t₁ t₀ : E →ₐ[F] Fv F v), (∀ x, t₀ x = t₁ (σ x)) →
        ∀ (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v))
          (ι : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ)),
        M.IsLin B.ψ (piW t₁) (piW t₀) (fun u => b.1 * u.map (piW t₁) * c.1) ι →
        ∃ z : ℂ, z ≠ 0 ∧ ∀ x : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E), At (evFin F v) x → x.map (piW t₀) = 0 →
          ι (M.vac v) (b.1 * x.map (piW t₁) * c.1) = if x ∈ latAtV X W v then z else 0 := by

  intro F E _ _ _ _ _ σ B n d X W M r s r' s' hB hX hW hM v t₁ t₀ ht b c ι hι
  obtain rfl : t₀ = t₁.comp σ := AlgHom.ext ht
  have hat := (GlobalTheory.LatVac.latAtV_at_stable X W v).1
  have hs : ∀ {t : E →ₐ[F] Fv F v} (ξ) {x y : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)}, At (evFin F v) x →
      x.map (piW t) = 0 → y.map (piW t) = 0 → GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) ξ
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F W.J) x y = 0 := fun ξ x y hx hx0 hy0 => by
    unfold GlobalTheory.WeilM.symp
    rw [hTens_half hB.cm _ _ _ hx hx0 hy0, mul_zero, map_zero]
  obtain ⟨hSB, h0, θ, -, hθ⟩ := hM.vac v
  obtain ⟨hz, hv⟩ := GlobalTheory.BigDat.lagr_vac (GlobalTheory.BigNZ.isLagrModel_of_isLin hι) hSB h0 (latAtV X W v : Set _)
    (fun γ hγ hγ' => by
      have h1 := hθ γ hγ
      rcases hγ' with h | h <;>
        rwa [hs _ h.1 h.2 h.2, mul_zero, AddChar.map_zero_eq_one, one_smul] at h1)
    (fun z => by
      refine ⟨(b⁻¹.1 * z * c⁻¹.1).map fun p => GlobalTheory.LinCoords.lift2 hB.cm t₁ p 0,
        ⟨(GlobalTheory.LinCoords.at_mat_iff _).2 fun i j => GlobalTheory.LinCoords.at_lift2 _ _ _ _,
          Matrix.ext fun i j => GlobalTheory.LinCoords.piW_comp_lift2 _ _ _ _⟩, ?_⟩
      have e : ((b⁻¹.1 * z * c⁻¹.1).map fun p => GlobalTheory.LinCoords.lift2 hB.cm t₁ p 0).map (piW t₁) = b⁻¹.1 * z * c⁻¹.1 :=
        Matrix.ext fun i j => GlobalTheory.LinCoords.piW_lift2 _ _ _ _
      show b.1 * _ * c.1 = z
      rw [e, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc, Units.inv_mul,
        Matrix.mul_one])
    (fun x hx h => by
      refine (GlobalTheory.LatSelfDualAll.latAtV_selfDual F E σ B n d X W r s r' s' hB hX hW v x hx.1).2 fun γ hγ => ?_
      obtain ⟨γ₁, h₁, γ₂, h₂, rfl, e₁, e₂⟩ := GlobalTheory.LatSplit.latAtV_decomp hB.cm X W v t₁ γ hγ
      have e : GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1)
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F W.J) x (γ₁ + γ₂) =
          GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1)
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F W.J) x γ₁ +
          GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1)
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F W.J) x γ₂ := by
        simp only [GlobalTheory.WeilM.symp, GlobalTheory.WeilM.hTens, Matrix.add_apply, map_add, mul_add, Finset.sum_add_distrib]
      rw [e, hs _ hx.1 hx.2 e₁, zero_add]
      exact h γ₂ h₂ ⟨hat γ₂ h₂, e₂⟩)
  refine ⟨ι (M.vac v) 0, hz, fun x hx hx0 => ?_⟩
  rw [hv x ⟨hx, hx0⟩, Set.indicator_apply]
  rfl
