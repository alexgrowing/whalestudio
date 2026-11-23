import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis

noncomputable section

namespace GlobalTheory.LFun.SplitVal

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {v : HeightOneSpectrum (𝓞 F)} {w w' : HeightOneSpectrum (𝓞 E)}

private lemma sigR_tmul_adelic_iwasawa_hecke {K L : Type} [Field K] [Field L] [Algebra K L] {τ : L →ₐ[K] L} {R : Type} [CommRing R]
    [Algebra K R] (r : R) (e : L) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R τ (r ⊗ₜ[K] e) = r ⊗ₜ[K] τ e := by
  simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]

private lemma extZero_tmul {K L : Type} [Field K] [NumberField K] [Field L] [Algebra K L] (a : Af K) (e : L) :
    extZero K L (a ⊗ₜ[K] e) = (LinearMap.inr K (Ainf K) (Af K) a : AF K) ⊗ₜ[K] e :=
  GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU_tmul _ _ a e

omit [NumberField E] in
theorem sigR_extZero (y : Af F ⊗[F] E) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ (extZero F E y) = extZero F E (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Af F) σ y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a e =>
    rw [sigR_tmul_adelic_iwasawa_hecke, extZero_tmul, extZero_tmul]
    exact sigR_tmul_adelic_iwasawa_hecke (R := AF F) (LinearMap.inr F (Ainf F) (Af F) a) e
  | add x y hx hy => simp only [map_add, hx, hy]

omit [NumberField E] in
theorem evalV_sigR (y : Af F ⊗[F] E) :
    Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Af F) σ y) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a e => simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]
  | add x y hx hy => simp only [map_add, hx, hy]

private lemma map_evalV_eq_of_finAdEquiv_eq {v' : HeightOneSpectrum (𝓞 F)} {y₁ y₂ : Af F ⊗[F] E}
    (H : ∀ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 F) = v' → finAdEquiv F E y₁ u = finAdEquiv F E y₂ u) :
    Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v') (AlgHom.id F E) y₁ =
      Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v') (AlgHom.id F E) y₂ := by
  have hev1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v' (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV F v' 1) = 1 := by
    classical
    change (RestrictedProduct.single (fun u : HeightOneSpectrum (𝓞 F) => u.adicCompletionIntegers F) v'
      (1 : Fv F v')) v' = 1
    exact RestrictedProduct.single_eq_same _ _ _
  have hev0 : ∀ v'' : HeightOneSpectrum (𝓞 F), v'' ≠ v' →
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v'' (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV F v' 1) = 0 :=
    fun v'' hv => by
    classical
    change (RestrictedProduct.single (fun u : HeightOneSpectrum (𝓞 F) => u.adicCompletionIntegers F) v'
      (1 : Fv F v')) v'' = 0
    exact RestrictedProduct.single_eq_of_ne _ _ hv
  have hs1 : Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v') (AlgHom.id F E)
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV F v' 1 ⊗ₜ[F] (1 : E)) = 1 := by
    rw [Algebra.TensorProduct.map_tmul, hev1, AlgHom.id_apply]; rfl
  have key : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV F v' 1 ⊗ₜ[F] (1 : E)) * y₁ =
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV F v' 1 ⊗ₜ[F] (1 : E)) * y₂ := by
    apply (finAdEquiv F E).injective
    refine FiniteAdeleRing.ext _ fun u => ?_
    rw [map_mul, map_mul]
    change finAdEquiv F E _ u * finAdEquiv F E y₁ u = finAdEquiv F E _ u * finAdEquiv F E y₂ u
    by_cases hu : u.under (𝓞 F) = v'
    · rw [H u hu]
    · rw [finAdEquiv_apply (rfl : u.under (𝓞 F) = u.under (𝓞 F)), Algebra.TensorProduct.map_tmul, hev0 _ hu,
        TensorProduct.zero_tmul, map_zero, zero_mul, zero_mul]
  have := congrArg (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v') (AlgHom.id F E)) key
  rwa [map_mul, map_mul, hs1, one_mul, one_mul] at this

theorem single_apply_ne (x : (w.adicCompletion E)ˣ) {u : HeightOneSpectrum (𝓞 E)} (hu : u ≠ w) :
    (GlobalTheory.CMVal.single w x : FiniteAdeleRing (𝓞 E) E) u = 1 := by
  classical
  first
  | (change (RestrictedProduct.mulSingle (fun u : HeightOneSpectrum (𝓞 E) => u.adicCompletionIntegers E) w
        (x : w.adicCompletion E)) u = 1
     exact RestrictedProduct.mulSingle_eq_of_ne _ _ hu)
  | (unfold GlobalTheory.CMVal.single
     simp only [Units.coe_map, Neutral.B1.finiteSingle, MonoidHom.coe_mk, OneHom.coe_mk,
       RestrictedProduct.coe_mulSingle_apply]
     simp [Pi.mulSingle, Function.update, hu])

private lemma cmval_single_apply_self (x : (w.adicCompletion E)ˣ) :
    (GlobalTheory.CMVal.single w x : FiniteAdeleRing (𝓞 E) E) w = x := by
  classical
  first
  | (change (Pi.mulSingle w (x : w.adicCompletion E) : ∀ u : HeightOneSpectrum (𝓞 E), u.adicCompletion E) w = x
     exact Pi.mulSingle_eq_same _ _)
  | (change (RestrictedProduct.mulSingle (fun u : HeightOneSpectrum (𝓞 E) => u.adicCompletionIntegers E) w
        (x : w.adicCompletion E)) w = x
     exact RestrictedProduct.mulSingle_eq_same _ _)
  | (unfold GlobalTheory.CMVal.single
     simp only [Units.coe_map, Neutral.B1.finiteSingle, MonoidHom.coe_mk, OneHom.coe_mk,
       RestrictedProduct.coe_mulSingle_apply]
     exact Pi.mulSingle_eq_same _ _)

theorem sigR_single (hE : IsCMExt F E σ) (h : w.under (𝓞 F) = v) (h' : w'.under (𝓞 F) = v) (hne : w ≠ w')
    (a : (Fv F v)ˣ) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Af F) σ ((finAdEquiv F E).symm
      (GlobalTheory.CMVal.single w (Units.map (complMap h).toMonoidHom a) : FiniteAdeleRing (𝓞 E) E)) =
    (finAdEquiv F E).symm (GlobalTheory.CMVal.single w' (Units.map (complMap h').toMonoidHom a) : FiniteAdeleRing (𝓞 E) E) := by
  obtain ⟨τ, hτ, -⟩ := GlobalTheory.AdelicU.existsUnique_splitPrime_eq hE hne h h'
  have hτ' : GlobalTheory.AdelicU.splitPrime (τ.comp σ) = w' := by
    obtain ⟨τ', hτ'', -⟩ := GlobalTheory.AdelicU.existsUnique_splitPrime_eq hE (Ne.symm hne) h' h
    rcases GlobalTheory.AdelicU.eq_or_eq_comp_conj hE τ τ' with e | e
    · exact absurd (hτ''.symm.trans (e ▸ hτ)) (Ne.symm hne)
    · rw [← e]; exact hτ''
  have hz1 : GlobalTheory.AdelicU.splitProj τ (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E)
      ((finAdEquiv F E).symm (GlobalTheory.CMVal.single w (Units.map (complMap h).toMonoidHom a) : FiniteAdeleRing (𝓞 E) E)))
      = (a : Fv F v) := by
    apply (complMap h).injective
    rw [← GlobalTheory.LFun.ConjPlace.toCompl_eq hE h hτ, ← finAdEquiv_apply h, RingEquiv.apply_symm_apply, cmval_single_apply_self]
    rfl
  have hz2 : GlobalTheory.AdelicU.splitProj (τ.comp σ) (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E)
      ((finAdEquiv F E).symm (GlobalTheory.CMVal.single w (Units.map (complMap h).toMonoidHom a) : FiniteAdeleRing (𝓞 E) E)))
      = 1 := by
    apply (complMap h').injective
    rw [← GlobalTheory.LFun.ConjPlace.toCompl_eq hE h' hτ', ← finAdEquiv_apply h', RingEquiv.apply_symm_apply, map_one]
    exact single_apply_ne _ (Ne.symm hne)
  apply (finAdEquiv F E).injective
  rw [RingEquiv.apply_symm_apply]
  refine FiniteAdeleRing.ext _ fun u => ?_
  by_cases hu : u.under (𝓞 F) = v
  · have hu2 : u = w ∨ u = w' := by
      by_cases huw : u = w
      · exact Or.inl huw
      · right
        obtain ⟨τu, hτu, -⟩ := GlobalTheory.AdelicU.existsUnique_splitPrime_eq hE huw hu h
        rcases GlobalTheory.AdelicU.eq_or_eq_comp_conj hE τ τu with e | e
        · exact absurd (hτu.symm.trans (e ▸ hτ)) huw
        · rw [← hτu, e, hτ']
    rcases hu2 with huw | huw
    · rw [huw, finAdEquiv_apply h, evalV_sigR, GlobalTheory.LFun.ConjPlace.toCompl_eq hE h hτ, ← GlobalTheory.AdelicU.splitProj_comp,
        hz2, map_one]
      exact (single_apply_ne _ hne).symm
    · rw [huw, finAdEquiv_apply h', evalV_sigR, GlobalTheory.LFun.ConjPlace.toCompl_eq hE h' hτ',
        GlobalTheory.AdelicU.splitProj_comp_sigR hE τ, hz1, cmval_single_apply_self]
      rfl
  · have h1 := map_evalV_eq_of_finAdEquiv_eq (v' := u.under (𝓞 F))
      (y₁ := (finAdEquiv F E).symm (GlobalTheory.CMVal.single w (Units.map (complMap h).toMonoidHom a) : FiniteAdeleRing (𝓞 E) E))
      (y₂ := 1) (fun u' hu' => by
        rw [RingEquiv.apply_symm_apply, map_one]
        exact single_apply_ne _ (by rintro rfl; exact hu (hu'.symm.trans h)))
    rw [finAdEquiv_apply (rfl : u.under (𝓞 F) = u.under (𝓞 F)), evalV_sigR, h1]
    simp only [map_one]
    exact (single_apply_ne _ (by rintro rfl; exact hu h')).symm

private lemma coe_locIdele' (u : HeightOneSpectrum (𝓞 E)) (x : (u.adicCompletion E)ˣ) :
    ((locIdele F u x : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = 1 - extZero F E 1 +
      extZero F E ((finAdEquiv F E).symm (GlobalTheory.CMVal.single u x : FiniteAdeleRing (𝓞 E) E)) := rfl

theorem sigR_locIdele (hE : IsCMExt F E σ) (h : w.under (𝓞 F) = v) (h' : w'.under (𝓞 F) = v) (hne : w ≠ w')
    (a : (Fv F v)ˣ) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ (locIdele F w (Units.map (complMap h).toMonoidHom a) : AF F ⊗[F] E) =
      locIdele F w' (Units.map (complMap h').toMonoidHom a) := by
  rw [coe_locIdele', coe_locIdele', map_add, map_sub, map_one, sigR_extZero, sigR_extZero, map_one,
    sigR_single hE h h' hne a]

theorem val_mul_val_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (μ : (TensorProduct F (AF F) E)ˣ →* Circle) (b : ℕ), ResEta F E μ b → ∀ (w w' : HeightOneSpectrum (𝓞 E)), w.under (𝓞 F) = w'.under (𝓞 F) → w ≠ w' → UnrAt μ w → UnrAt μ w' → val μ w * val μ w' = 1 := by
  intro F E _ _ _ _ _ σ hE μ b hμ w w' hww hne hw hw'
  obtain ⟨τ, hτ, -⟩ := GlobalTheory.AdelicU.existsUnique_splitPrime_eq hE hne rfl hww.symm
  have hτ' : GlobalTheory.AdelicU.splitPrime (τ.comp σ) = w' := by
    obtain ⟨τ', hτ'', -⟩ := GlobalTheory.AdelicU.existsUnique_splitPrime_eq hE (Ne.symm hne) hww.symm rfl
    rcases GlobalTheory.AdelicU.eq_or_eq_comp_conj hE τ τ' with e | e
    · exact absurd (hτ''.symm.trans (e ▸ hτ)) (Ne.symm hne)
    · rw [← e]; exact hτ''
  have ha := Formalism.L2.Host.unif_spec (w.under (𝓞 F))
  set a := Formalism.L2.Host.atFin (w.under (𝓞 F)) (Formalism.L2.Host.unif (w.under (𝓞 F))) with ha_def
  have hx : Formalism.L2.Host.IsUnifAt w (Units.map (complMap (rfl : w.under (𝓞 F) = _)).toMonoidHom a) := by
    unfold Formalism.L2.Host.IsUnifAt at ha ⊢
    rw [← ha]
    exact GlobalTheory.LFun.ConjPlace.valued_complMap hE rfl hτ _
  have hx' : Formalism.L2.Host.IsUnifAt w' (Units.map (complMap hww.symm).toMonoidHom a) := by
    unfold Formalism.L2.Host.IsUnifAt at ha ⊢
    rw [← ha]
    exact GlobalTheory.LFun.ConjPlace.valued_complMap hE hww.symm hτ' _
  rw [← UnrAt.locChar_eq_val hw hx, ← UnrAt.locChar_eq_val hw' hx']
  simp only [locChar, MonoidHom.comp_apply]
  rw [← map_mul, ← map_mul]
  have hP : locIdele F w (Units.map (complMap (rfl : w.under (𝓞 F) = _)).toMonoidHom a) *
      locIdele F w' (Units.map (complMap hww.symm).toMonoidHom a) =
      ideleMap F E (Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F)
        (locIdele F w (Units.map (complMap (rfl : w.under (𝓞 F) = _)).toMonoidHom a))) := by
    apply Units.ext
    rw [Units.val_mul, ← sigR_locIdele hE rfl hww.symm hne a, ← GlobalTheory.Doubling.algebraMap_norm_eq hE]
    rfl
  obtain ⟨⟨η, hη⟩, hall⟩ := hμ
  rw [hP, hall η hη, hη.2.2.1, one_pow, map_one]

end GlobalTheory.LFun.SplitVal

end
