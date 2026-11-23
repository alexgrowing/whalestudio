import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveHomogeneousOperatorLinearStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalActionLinearInVectorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPairLocalSchwartzActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMomentMatrixTransformStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormUnitaryInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMatrixMomentSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMatrixMomentSurjectiveConjStatement

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.OppLinOp

theorem local_op_eq_smul : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (ι : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ)),
    G.M'.IsLinBar B.ψ t 1 1 ι → ∀ g ∈ UAt σ G.V' (evFin F v), ∀ h ∈ UAt σ G.W (evFin F v),
    ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
    Acts (evFin F v) (om' (g, h)) φ φ₁ →
    ∃ (c : ℂ) (P : GL (Fin a') (Fv F v)) (Q : GL (Fin (a + a')) (Fv F v)), ∀ Y, ι φ₁ Y = c * ι φ (P.1 * Y * Q.1) := by
  intro hPr F E _ _ _ _ _ σ B a a' G X om om' hT v t ι hι g hg h hh φ hφ φ₁ hφ₁ hacts
  classical
  set co : Matrix (Fin a') (Fin (a + a')) (AE F E) → Matrix (Fin a') (Fin (a + a')) (Fv F v) :=
    fun u => -((1 : GL (Fin a') (Fv F v)).1ᵀ * G.V'.J.map t * u.map (piW (t.comp σ)) * (G.W.J.map t)ᵀ *
      (1 : GL (Fin (a + a')) (Fv F v)).1) with hco
  have hL : G.M'.IsLin B.ψ (piW (t.comp σ)) (piW t) co ι := hι
  have hP' := (GlobalTheory.ThK.Check.isPair_of_isTriple hT).2
  obtain ⟨hex1, hex2, -⟩ := GlobalTheory.T.theta_action_exists hPr F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _ hP' v

  have hex1' : ∀ ξ : (Fin a' × Fin (a + a') → Fv F v) → ℂ, ∃ η, ξ ∈ SB (Fin a' × Fin (a + a') → Fv F v) →
      η ∈ SB (Fin a' × Fin (a + a') → Fv F v) ∧ Acts (evFin F v) (om' (g, h)) ξ η := by
    intro ξ
    by_cases hξ : ξ ∈ SB (Fin a' × Fin (a + a') → Fv F v)
    · obtain ⟨η, hη, -⟩ := hex1 g hg h hh ξ hξ
      exact ⟨η, fun _ => hη⟩
    · exact ⟨0, fun h' => absurd h' hξ⟩
  choose T hTspec using hex1'

  set ιi := Function.invFunOn ι (SB (Fin a' × Fin (a + a') → Fv F v) : Set ((Fin a' × Fin (a + a') → Fv F v) → ℂ))
    with hιi
  have hinv := hL.bij.invOn_invFunOn
  have hi1 : ∀ Ξ ∈ SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)),
      ιi Ξ ∈ SB (Fin a' × Fin (a + a') → Fv F v) ∧ ι (ιi Ξ) = Ξ :=
    fun Ξ hΞ => ⟨hL.bij.surjOn.mapsTo_invFunOn hΞ, hinv.2 hΞ⟩
  have hi2 : ∀ ξ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ιi (ι ξ) = ξ := fun ξ hξ => hinv.1 hξ

  set gt := (mat g).map (piW t) with hgt
  set gi := (mat g⁻¹).map (piW t) with hgi
  set ht' := (mat h).map (piW t) with hht
  set hi := (mat h⁻¹).map (piW t) with hhi
  have hg1 : gt * gi = 1 := by
    rw [hgt, hgi, ← Matrix.map_mul]
    have : mat g * mat g⁻¹ = 1 := by simp [mat]
    rw [this, Matrix.map_one _ (map_zero _) (map_one _)]
  have hg2 : gi * gt = 1 := by
    rw [hgt, hgi, ← Matrix.map_mul]
    have : mat g⁻¹ * mat g = 1 := by simp [mat]
    rw [this, Matrix.map_one _ (map_zero _) (map_one _)]
  have hh1 : ht' * hi = 1 := by
    rw [hht, hhi, ← Matrix.map_mul]
    have : mat h * mat h⁻¹ = 1 := by simp [mat]
    rw [this, Matrix.map_one _ (map_zero _) (map_one _)]
  have hh2 : hi * ht' = 1 := by
    rw [hht, hhi, ← Matrix.map_mul]
    have : mat h⁻¹ * mat h = 1 := by simp [mat]
    rw [this, Matrix.map_one _ (map_zero _) (map_one _)]
  have hPP : giᵀ * gtᵀ = 1 := by rw [← Matrix.transpose_mul, hg1, Matrix.transpose_one]
  have hPP' : gtᵀ * giᵀ = 1 := by rw [← Matrix.transpose_mul, hg2, Matrix.transpose_one]

  have at_conj : ∀ u : Matrix (Fin a') (Fin (a + a')) (AE F E), At (evFin F v) u →
      At (evFin F v) (mat g * u * (mat h)ᵀ) := by
    intro u hu c hc
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hu c hc, Matrix.mul_zero, Matrix.zero_mul]
  have hmap : ∀ (f : AE F E →+* Fv F v) (u : Matrix (Fin a') (Fin (a + a')) (AE F E)),
      (mat g * u * (mat h)ᵀ).map f = (mat g).map f * u.map f * ((mat h).map f)ᵀ := by
    intro f u
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  have hco_act : ∀ u : Matrix (Fin a') (Fin (a + a')) (AE F E), co (mat g * u * (mat h)ᵀ) = giᵀ * co u * hi := by
    intro u
    have hca : gtᵀ * co (mat g * u * (mat h)ᵀ) * ht' = co u := GlobalTheory.T.local_moment_matrix_transform F E σ a' (a + a') G.V' G.W v t g h u
    calc co (mat g * u * (mat h)ᵀ) = (giᵀ * gtᵀ) * co (mat g * u * (mat h)ᵀ) * (ht' * hi) := by
          rw [hPP, hh1, Matrix.one_mul, Matrix.mul_one]
      _ = giᵀ * (gtᵀ * co (mat g * u * (mat h)ᵀ) * ht') * hi := by simp only [Matrix.mul_assoc]
      _ = giᵀ * co u * hi := by rw [hca]

  set A : (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ) → Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ :=
    fun Ξ Y => ι (T (ιi Ξ)) (giᵀ * Y * hi) with hA
  have hlin : ∀ (c0 : ℂ), ∀ Ξ ∈ SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)),
      ∀ Ξ' ∈ SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)), A (c0 • Ξ + Ξ') = c0 • A Ξ + A Ξ' := by
    intro c0 Ξ hΞ Ξ' hΞ'
    obtain ⟨hξ, hιξ⟩ := hi1 Ξ hΞ
    obtain ⟨hξ', hιξ'⟩ := hi1 Ξ' hΞ'
    have hs : c0 • ιi Ξ + ιi Ξ' ∈ SB (Fin a' × Fin (a + a') → Fv F v) := add_mem (Submodule.smul_mem _ c0 hξ) hξ'
    have e1 : ιi (c0 • Ξ + Ξ') = c0 • ιi Ξ + ιi Ξ' := by
      have : ι (c0 • ιi Ξ + ιi Ξ') = c0 • Ξ + Ξ' := by rw [map_add, map_smul, hιξ, hιξ']
      rw [← this]; exact hi2 _ hs
    obtain ⟨-, hTa1⟩ := hTspec _ hξ
    obtain ⟨-, hTa2⟩ := hTspec _ hξ'
    obtain ⟨-, hTa3⟩ := hTspec _ hs
    have e2 := GlobalTheory.T.local_action_linear_in_vector F (Fin a' × Fin (a + a')) v (om' (g, h)) c0 (ιi Ξ) (ιi Ξ') _ _ _ hξ hξ' hTa1 hTa2 hTa3
    funext Y
    show ι (T (ιi (c0 • Ξ + Ξ'))) (giᵀ * Y * hi) = c0 * ι (T (ιi Ξ)) (giᵀ * Y * hi) + ι (T (ιi Ξ')) (giᵀ * Y * hi)
    rw [e1, e2, map_add, map_smul]
    rfl
  have hA0 : A 0 = 0 := by
    have h0 := hlin 1 0 (zero_mem _) 0 (zero_mem _)
    simp only [one_smul, add_zero] at h0
    have h2 : A 0 + A 0 = A 0 + 0 := by rw [add_zero]; exact h0.symm
    exact add_left_cancel h2
  have hadd : ∀ f ∈ SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)), ∀ f' ∈ SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)),
      A (f + f') = A f + A f' := fun f hf f' hf' => by simpa using hlin 1 f hf f' hf'
  have hsmul : ∀ (c : ℂ), ∀ f ∈ SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)), A (c • f) = c • A f :=
    fun c f hf => by simpa [hA0] using hlin c f hf 0 (zero_mem _)

  have hut_map : ∀ u : Matrix (Fin a') (Fin (a + a')) (AE F E), ∀ f : AE F E →+* Fv F v, u.map f = 0 →
      (mat g * u * (mat h)ᵀ).map f = 0 := by
    intro u f hu
    rw [hmap, hu, Matrix.mul_zero, Matrix.zero_mul]
  have hsurj := fun Y => GlobalTheory.T.local_matrix_moment_surjective F E σ B hT.base a' (a + a') _ _ _ _ G.V' G.W hT.geo.hV' hT.geo.hW v t Y
  have htr : ∀ Z : Matrix (Fin a') (Fin (a + a')) (Fv F v), ∀ Ξ ∈ SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)),
      A (fun Y => Ξ (Y + Z)) = fun Y => A Ξ (Y + Z) := by
    intro Z Ξ hΞ
    obtain ⟨hξ, hιξ⟩ := hi1 Ξ hΞ
    obtain ⟨u, hu, hut, hcu⟩ := hsurj Z
    have hcu' : co u = Z := hcu
    obtain ⟨ξ₁, ⟨hξ₁, hact₁⟩, -⟩ := hex2 u hu (ιi Ξ) hξ
    have e1 : ι ξ₁ = fun Y => Ξ (Y + Z) := by
      funext Y
      rw [hL.trans u hu hut (ιi Ξ) hξ ξ₁ hξ₁ hact₁ Y, hιξ, hcu']
    have e2 : ιi (fun Y => Ξ (Y + Z)) = ξ₁ := by rw [← e1]; exact hi2 ξ₁ hξ₁
    obtain ⟨hTξ, hTa⟩ := hTspec (ιi Ξ) hξ
    obtain ⟨ξ₄, ⟨hξ₄, hact₄⟩, -⟩ := hex2 _ (at_conj u hu) (T (ιi Ξ)) hTξ
    obtain ⟨-, hTa₁⟩ := hTspec ξ₁ hξ₁
    have e3 : ξ₄ = T ξ₁ := GlobalTheory.T.theta_pair_local_schwartz_action F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _ hP' v (g, h) u (ιi Ξ) ξ₁
      (T (ιi Ξ)) (T ξ₁) ξ₄ hξ hξ₁ hTξ hact₁ hTa hTa₁ hact₄
    funext Y
    show ι (T (ιi (fun Y => Ξ (Y + Z)))) (giᵀ * Y * hi) = ι (T (ιi Ξ)) (giᵀ * (Y + Z) * hi)
    rw [e2, ← e3, hL.trans _ (at_conj u hu) (hut_map u _ hut) (T (ιi Ξ)) hTξ ξ₄ hξ₄ hact₄, hco_act, hcu',
      Matrix.mul_add, Matrix.add_mul]

  have hmul : ∀ Z : Matrix (Fin a') (Fin (a + a')) (Fv F v), ∀ Ξ ∈ SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)),
      A (fun Y => GlobalTheory.LatVac.psiAt B.ψ v (∑ i, ∑ j, Y i j * Z i j) * Ξ Y) =
        fun Y => GlobalTheory.LatVac.psiAt B.ψ v (∑ i, ∑ j, Y i j * Z i j) * A Ξ Y := by
    intro Z Ξ hΞ
    obtain ⟨hξ, hιξ⟩ := hi1 Ξ hΞ
    obtain ⟨u, hu, hut, hchar⟩ := GlobalTheory.T.local_matrix_moment_surjective_conj F E σ B hT.base a' (a + a') _ _ _ _ G.V' G.W hT.geo.hV' hT.geo.hW v t Z
    have hchar' : ∀ x : Matrix (Fin a') (Fin (a + a')) (AE F E), At (evFin F v) x → x.map (piW t) = 0 →
        B.ψ (symp (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J) x u) =
          GlobalTheory.LatVac.psiAt B.ψ v (∑ i, ∑ j, co x i j * Z i j) := hchar
    obtain ⟨ξ₁, ⟨hξ₁, hact₁⟩, -⟩ := hex2 u hu (ιi Ξ) hξ
    have e1 : ι ξ₁ = fun Y => GlobalTheory.LatVac.psiAt B.ψ v (∑ i, ∑ j, Y i j * Z i j) * Ξ Y := by
      funext Y
      obtain ⟨x, hx, hxt, hcx⟩ := hsurj Y
      have hcx' : co x = Y := hcx
      rw [← hcx', hL.mult u hu hut (ιi Ξ) hξ ξ₁ hξ₁ hact₁ x hx hxt, hιξ, hchar' x hx hxt]
    have e2 : ιi (fun Y => GlobalTheory.LatVac.psiAt B.ψ v (∑ i, ∑ j, Y i j * Z i j) * Ξ Y) = ξ₁ := by
      rw [← e1]; exact hi2 ξ₁ hξ₁
    obtain ⟨hTξ, hTa⟩ := hTspec (ιi Ξ) hξ
    obtain ⟨ξ₄, ⟨hξ₄, hact₄⟩, -⟩ := hex2 _ (at_conj u hu) (T (ιi Ξ)) hTξ
    obtain ⟨-, hTa₁⟩ := hTspec ξ₁ hξ₁
    have e3 : ξ₄ = T ξ₁ := GlobalTheory.T.theta_pair_local_schwartz_action F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _ hP' v (g, h) u (ιi Ξ) ξ₁
      (T (ιi Ξ)) (T ξ₁) ξ₄ hξ hξ₁ hTξ hact₁ hTa hTa₁ hact₄
    funext Y
    obtain ⟨x, hx, hxt, hcx⟩ := hsurj Y
    have hcx' : co x = Y := hcx
    have e4 : co (mat g * x * (mat h)ᵀ) = giᵀ * Y * hi := by rw [hco_act, hcx']
    have hs : symp (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J) (mat g * x * (mat h)ᵀ) (mat g * u * (mat h)ᵀ) =
        symp (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J) x u := GlobalTheory.T.symplectic_form_unitary_invariant F E σ a' (a + a') G.V' G.W g h x u
    show ι (T (ιi (fun Y => GlobalTheory.LatVac.psiAt B.ψ v (∑ i, ∑ j, Y i j * Z i j) * Ξ Y))) (giᵀ * Y * hi) =
      GlobalTheory.LatVac.psiAt B.ψ v (∑ i, ∑ j, Y i j * Z i j) * ι (T (ιi Ξ)) (giᵀ * Y * hi)
    rw [e2, ← e3, ← e4, hL.mult _ (at_conj u hu) (hut_map u _ hut) (T (ιi Ξ)) hTξ ξ₄ hξ₄ hact₄ _ (at_conj x hx)
      (hut_map x _ hxt), hs, hchar' x hx hxt, hcx']
  obtain ⟨cc, hcc⟩ := GlobalTheory.T.additive_homogeneous_operator_linear (Fv F v) (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.SchrSB.continuous_psiAt B.ψ hT.base.std.1 v)
    (GlobalTheory.PsiNontriv.psiAt_ne_one B.ψ hT.base.std v) a' (a + a') A hadd hsmul htr hmul
  have hιφ : ι φ ∈ SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)) := hL.bij.mapsTo hφ
  have eT : φ₁ = T φ := (hex1 g hg h hh φ hφ).unique ⟨hφ₁, hacts⟩ (hTspec φ hφ)
  refine ⟨cc, ⟨gtᵀ, giᵀ, hPP', hPP⟩, ⟨ht', hi, hh1, hh2⟩, fun Y => ?_⟩
  have key := congrFun (hcc (ι φ) hιφ) (gtᵀ * Y * ht')
  change ι (T (ιi (ι φ))) (giᵀ * (gtᵀ * Y * ht') * hi) = cc * ι φ (gtᵀ * Y * ht') at key
  have ee : giᵀ * (gtᵀ * Y * ht') * hi = Y := by
    simp only [← Matrix.mul_assoc, hPP, Matrix.one_mul]
    rw [Matrix.mul_assoc, hh1, Matrix.mul_one]
  rw [hi2 φ hφ, ← eT, ee] at key
  exact key

end GlobalTheory.OppLinOp

end
