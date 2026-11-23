import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.IsTanZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.DerZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.ExistsAdjoinCoeffCharacterSubMemMaximalIdealPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.FlagCharsUnique
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.RepApi
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.MapApi
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.dvrFinite

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem res_iff {K : Type} [Field K] (a b : DualNumber K) :
    residue (DualNumber K) a = residue (DualNumber K) b ↔ a.fst = b.fst := by
  rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff,
    TrivSqZeroExt.isUnit_iff_isUnit_fst, isUnit_iff_ne_zero, not_not, TrivSqZeroExt.fst_sub, sub_eq_zero]

private theorem flag_const {K H : Type} [Field K] [Infinite K] [Group H] {n : ℕ} (ρ : H →* GL (Fin n) K)
    (ρ' : H →* GL (Fin n) (DualNumber K)) (Q : GL (Fin n) (DualNumber K))
    (hQ : ∀ g, ρ' g = Q * W.pushRep (algebraMap _ (DualNumber K)) ρ g * Q⁻¹) (ψ : Fin n → H →* (DualNumber K)ˣ)
    (hinj : Function.Injective fun i => W.pushCh (dF K) (ψ i)) (h0 : W.HasFlag ρ fun i => W.pushCh (dF K) (ψ i))
    (h1 : W.HasFlag ρ' ψ) (i : Fin n) (s : H) : (ψ i s : DualNumber K).snd = 0 := by
  obtain ⟨g, hg⟩ := h0
  obtain ⟨g', hg'⟩ := h1
  let ι : K →+* DualNumber K := algebraMap _ _
  have hinf : Infinite (ResidueField (DualNumber K)) :=
    Infinite.of_injective _ ((residue (DualNumber K)).comp ι).injective
  have e : ∀ s, GeneralLinearGroup.map ι g * Q⁻¹ * ρ' s * (GeneralLinearGroup.map ι g * Q⁻¹)⁻¹ =
      GeneralLinearGroup.map ι (g * ρ s * g⁻¹) := fun s => by
    rw [hQ, map_mul, map_mul, map_inv]
    show _ * (_ * GeneralLinearGroup.map ι (ρ s) * _) * _ = _
    group
  have := (AlgebraTools.flag_chars_unique ρ' ψ (fun i => W.pushCh ι (W.pushCh (dF K) (ψ i))) g'
    (GeneralLinearGroup.map ι g * Q⁻¹) ((Cardinal.natCast_lt_aleph0).le.trans (Cardinal.aleph0_le_mk _))
    (fun a b hab => hinj (MonoidHom.ext fun t => Units.ext ((res_iff _ _).1 (DFunLike.congr_fun hab t))))
    (fun a t => (res_iff _ _).2 rfl) hg' (fun t => by
      rw [e]
      refine ⟨fun a b hab => ?_, fun a => ?_⟩
      · show ι ((g * ρ t * g⁻¹ : GL (Fin n) K) a b) = 0
        rw [(hg t).1 a b hab, map_zero]
      · show ι ((g * ρ t * g⁻¹ : GL (Fin n) K) a a) = _
        rw [(hg t).2 a]
        rfl)).1
  rw [congrFun this i]
  rfl

theorem UpperTheory.V.Ws.Eb.constOf :
    ∀ {l : ℕ} [Fact l.Prime] {F : W.GFrame l} {c : Coef l} {n : ℕ} {r : W.Resid F c.O n} (B : W.UniversalOrdinaryDeterminantRing r) (x' : B.B →ₐ[c.O] DualNumber (PadicAlgCl l)) (ρ : F.G₀ →* GL (Fin n) (PadicAlgCl l)) (ρ' : F.G₀ →* GL (Fin n) (DualNumber (PadicAlgCl l))) (Q : GL (Fin n) (DualNumber (PadicAlgCl l))), B.u.D.map (x' : B.B →+* DualNumber (PadicAlgCl l)) = W.GDet.ofRep (W.mat ρ') → (∀ g, ρ' g = Q * W.pushRep (algebraMap _ (DualNumber (PadicAlgCl l))) ρ g * Q⁻¹) →
        (∀ v, Function.Injective fun i => W.pushCh ((dF _).comp (x' : B.B →+* DualNumber (PadicAlgCl l))) (B.u.ψ v i)) → (∀ v, W.HasFlag (ρ.comp (F.φ v)) fun i => W.pushCh ((dF _).comp (x' : B.B →+* DualNumber (PadicAlgCl l))) (B.u.ψ v i)) →
        (∀ v, W.HasFlag (ρ'.comp (F.φ v)) fun i => W.pushCh (x' : B.B →+* DualNumber (PadicAlgCl l)) (B.u.ψ v i)) → ∀ b, (x' b).snd = 0 := by
  intro l hl F c n r B x' ρ ρ' Q hD hQ hinj h0 h1
  obtain ⟨-, hfin, hlm, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  haveI : Finite (ResidueField c.O) := hfin
  haveI : CharP (ResidueField c.O) l := by
    refine (CharP.charP_iff_prime_eq_zero hl.out).2 ?_
    rw [← map_natCast (residue c.O), residue_eq_zero_iff]
    exact hlm
  refine derZero c B.B x' _ (CA.exists_adjoin_coeff_character_sub_mem_maximalIdeal_pow r B) ?_
  rintro a (⟨i, g, -, -, rfl⟩ | ⟨v, i, g, rfl⟩)
  · have e1 := (AlgebraTools.Det.mapApi B.u.D (x' : B.B →+* DualNumber (PadicAlgCl l))).2.2.1 i g
    have e2 : W.GDet.ofRep (W.mat ρ') =
        (W.GDet.ofRep (W.mat ρ)).map (algebraMap _ (DualNumber (PadicAlgCl l))) := by
      rw [(AlgebraTools.Det.repApi _).2.2.2.2.2.1]
      refine (AlgebraTools.Det.repApi _).2.2.2.2.2.2.2 _ Q⁻¹ fun y => ?_
      have : Q⁻¹ * ρ' y = W.pushRep (algebraMap _ (DualNumber (PadicAlgCl l))) ρ y * Q⁻¹ := by
        rw [hQ]; group
      exact congrArg Units.val this
    rw [hD, e2, (AlgebraTools.Det.mapApi _ _).2.2.1] at e1
    exact (congrArg TrivSqZeroExt.snd e1).symm
  · exact flag_const (ρ.comp (F.φ v)) (ρ'.comp (F.φ v)) Q (fun g => hQ _)
      (fun i => W.pushCh (x' : B.B →+* DualNumber (PadicAlgCl l)) (B.u.ψ v i)) (hinj v) (h0 v) (h1 v) i g
