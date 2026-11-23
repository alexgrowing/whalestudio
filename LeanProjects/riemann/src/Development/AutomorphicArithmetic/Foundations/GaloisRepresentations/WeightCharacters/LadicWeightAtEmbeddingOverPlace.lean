import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNear
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.CAllFin
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAlgebraicCharacterUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfLocalLevelsUnitaryIsOpenIsCompactIsLeve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocEqOneOfMemGam

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching

namespace UpperTheory.Gal.Wt

theorem ladic_weight_at_embedding_over_place : Kap0 := by
  intro E _ _ _ l _ ι a v' τ hτ
  obtain ⟨u, hu⟩ := GlobalTheory.LadicPlace.exists_place_of_embedding E l (ι.symm.toRingHom.comp τ)
  have hle : v'.asIdeal ≤ u.asIdeal := fun x hx => by
    rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E)]
    exact (hu _).2 (hτ x hx)
  have huv : v' = u := HeightOneSpectrum.ext (v'.isMaximal.eq_of_le u.isPrime.ne_top hle)
  subst huv
  obtain ⟨j, hj, hjE⟩ := GlobalTheory.exists_continuous_extension_adicCompletion E l (ι.symm.toRingHom.comp τ) v' hu
  have hl : ((l : ℕ) : 𝓞 E) ∈ v'.asIdeal := by
    rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E)]
    have h1 : ‖(ι.symm.toRingHom.comp τ) ((((l : ℕ) : 𝓞 E)) : E)‖ < 1 := by
      have h0 : (ι.symm.toRingHom.comp τ) ((((l : ℕ) : 𝓞 E)) : E) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
      rw [h0, PadicAlgCl.norm_extends (p := l) (l : ℚ_[l])]
      exact Padic.norm_p_lt_one
    simpa using (hu (((l : ℕ) : 𝓞 E) : E)).2 h1
  have hκ : ∀ (g : UA E a) (p q : Fin a), ((((Matrix.GeneralLinearGroup.map (ι.toRingHom.comp j)).comp (cLoc v')) g :
      GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) p q = ι (j (((cLoc v' g : GL (Fin a) (v'.adicCompletion E)) :
        Matrix (Fin a) (Fin a) (v'.adicCompletion E)) p q)) := fun _ _ _ => rfl
  refine ⟨(Matrix.GeneralLinearGroup.map (ι.toRingHom.comp j)).comp (cLoc v'), ?_, ?_, ?_, ?_, ?_⟩
  · rintro γ ⟨g₀, hg₀⟩
    ext p q
    change ι (j (pLoc E v' (pFin E ((γ.1 : Matrix (Fin a) (Fin a) (Ad E)) p q)))) =
      coord τ (pInf E ((γ.1 : Matrix (Fin a) (Fin a) (Ad E)) p q))
    have hg₁ : (γ.1 : GL (Fin a) (Ad E)) = ratGL E a g₀ := hg₀.symm
    rw [hg₁]
    change ι (j (pLoc E v' (pFin E (algebraMap E (Ad E) ((g₀ : Matrix (Fin a) (Fin a) E) p q))))) =
      coord τ (pInf E (algebraMap E (Ad E) ((g₀ : Matrix (Fin a) (Fin a) E) p q)))
    rw [coord_algebraMap]
    have h := congrArg (fun φ : E →+* Qbar l => φ ((g₀ : Matrix (Fin a) (Fin a) E) p q)) hjE
    simp only [RingHom.coe_comp, Function.comp_apply] at h
    change ι (j (algebraMap E (v'.adicCompletion E) _)) = _
    rw [h]
    simp
  · intro x hx
    have hx' : Matrix.GeneralLinearGroup.map (pFin E) x.1 = 1 := hx
    have h2 : cLoc v' x = Matrix.GeneralLinearGroup.map (pLoc E v') (Matrix.GeneralLinearGroup.map (pFin E) x.1) := by
      ext; rfl
    rw [MonoidHom.comp_apply, h2, hx', map_one, map_one]
  · intro g
    constructor
    · intro h
      have hinj : Function.Injective (ι.toRingHom.comp j) := RingHom.injective _
      refine Units.ext (Matrix.ext fun p q => hinj ?_)
      have h3 := congrArg (fun m : GL (Fin a) ℂ => (m : Matrix (Fin a) (Fin a) ℂ) p q) h
      simp only [hκ] at h3
      have h4 : (ι.toRingHom.comp j) (((1 : GL (Fin a) (v'.adicCompletion E)) : Matrix (Fin a) (Fin a) (v'.adicCompletion E)) p q) =
          ((1 : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) p q := by
        simp only [Units.val_one, Matrix.one_apply]
        split_ifs <;> simp
      exact h3.trans h4.symm
    · intro h
      rw [MonoidHom.comp_apply, h, map_one]
  · intro p q
    have h1 : (fun g : UA E a => ι.symm (((((Matrix.GeneralLinearGroup.map (ι.toRingHom.comp j)).comp (cLoc v')) g :
        GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) p q)) =
        fun g => j (((cLoc v' g : GL (Fin a) (v'.adicCompletion E)) : Matrix (Fin a) (Fin a) (v'.adicCompletion E)) p q) :=
      funext fun g => by rw [hκ, RingEquiv.symm_apply_apply]
    rw [h1]
    exact hj.comp ((Units.continuous_val.matrix_elem p q).comp (GlobalTheory.BCT.GlobLev.continuous_cLoc v'))
  · intro g hg p q
    obtain ⟨h1, h2⟩ := GlobalTheory.EulerTwRestr.mem_KGL_iff.1 hg
    constructor
    · rw [hκ, RingEquiv.symm_apply_apply]
      exact UpperTheory.Gal.Gen.Loc.norm_map_integer_le_one l v' j hl hj _ (h1 p q)
    · rw [MonoidHom.comp_apply, ← map_inv]
      change ‖ι.symm (ι (j ((((cLoc v' g)⁻¹ : GL (Fin a) (v'.adicCompletion E)) :
        Matrix (Fin a) (Fin a) (v'.adicCompletion E)) p q)))‖ ≤ 1
      rw [RingEquiv.symm_apply_apply]
      exact UpperTheory.Gal.Gen.Loc.norm_map_integer_le_one l v' j hl hj _ (h2 p q)

end UpperTheory.Gal.Wt

end
