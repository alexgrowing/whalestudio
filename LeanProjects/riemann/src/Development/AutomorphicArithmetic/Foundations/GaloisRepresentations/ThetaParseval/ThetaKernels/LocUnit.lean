import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.LdExOfLeaves
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsLocUnit

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem UpperTheory.TP.K.locUnit_coord {F E : Type} [Field F] [Field E] [CharZero E] [Algebra F E] {σ : E →ₐ[F] E}
    (h2 : Module.finrank F E = 2) {ξ : E} (hξ : ξ ≠ 0) (hσξ : σ ξ = -ξ) (y : E) :
    ∃ a b : F, y = algebraMap F E a + algebraMap F E b * ξ := by
  have hli : LinearIndependent F ![(1 : E), ξ] := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have h' : s • (1 : E) + -(t • ξ) = 0 := by
      have h0 := congrArg σ h
      simp only [Algebra.smul_def, map_add, map_mul, AlgHom.commutes, map_one, hσξ, map_zero] at h0
      simp only [Algebra.smul_def]
      linear_combination h0
    have hs : (2 : E) * (s • (1 : E)) = 0 := by linear_combination h + h'
    have ht : (2 : E) * (t • ξ) = 0 := by linear_combination h - h'
    have hs' := (mul_eq_zero.1 hs).resolve_left two_ne_zero
    have ht' := (mul_eq_zero.1 ht).resolve_left two_ne_zero
    exact ⟨(smul_eq_zero.1 hs').resolve_right one_ne_zero, (smul_eq_zero.1 ht').resolve_right hξ⟩
  have hsp := hli.span_eq_top_of_card_eq_finrank (by simp [h2])
  have hy : y ∈ Submodule.span F (Set.range ![(1 : E), ξ]) := by rw [hsp]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).1 hy
  refine ⟨c 0, c 1, ?_⟩
  rw [← hc, Fin.sum_univ_two]
  simp [Algebra.smul_def]

theorem UpperTheory.TP.K.locUnit_diff {F E : Type} [Field F] [Field E] [CharZero E] [Algebra F E] {σ : E →ₐ[F] E}
    (h2 : Module.finrank F E = 2) {ξ : E} (hξ : ξ ≠ 0) (hσξ : σ ξ = -ξ) (y : E) :
    σ (y - σ y) = -(y - σ y) ∧ ∃ c : F, algebraMap F E c = (y - σ y) * (y - σ y) := by
  obtain ⟨a, b, rfl⟩ := UpperTheory.TP.K.locUnit_coord h2 hξ hσξ y
  obtain ⟨p, q, hpq⟩ := UpperTheory.TP.K.locUnit_coord h2 hξ hσξ (ξ * ξ)
  have h' := congrArg σ hpq
  simp only [map_add, map_mul, AlgHom.commutes, hσξ] at h'
  have h3 : (2 : E) * (ξ * ξ) = 2 * algebraMap F E p := by linear_combination hpq + h'
  have h4 : ξ * ξ = algebraMap F E p := mul_left_cancel₀ two_ne_zero h3
  refine ⟨?_, 4 * b * b * p, ?_⟩
  · simp only [map_add, map_sub, map_mul, map_neg, AlgHom.commutes, hσξ]
    ring
  · simp only [map_add, map_mul, AlgHom.commutes, hσξ, map_ofNat, ← h4]
    ring

theorem UpperTheory.TP.K.locUnit_exists_diff_notMem (hu : Algebra.Unramified (𝓞 F) (𝓞 E)) {ξ : E} (hξ : ξ ≠ 0) (hσξ : σ ξ = -ξ)
    (w : Ideal (𝓞 E)) (hw : w ≠ ⊤) :
    ∃ x : 𝓞 E, x - RingOfIntegers.mapRingHom (σ : E →+* E) x ∉ w := by
  by_contra hcon
  push Not at hcon
  let s : 𝓞 E →ₐ[𝓞 F] 𝓞 E :=
    { RingOfIntegers.mapRingHom (σ : E →+* E) with
      commutes' := fun r => by
        apply RingOfIntegers.ext
        exact σ.commutes (r : F) }
  have hs : AlgHom.id (𝓞 F) (𝓞 E) = s :=
    Algebra.FormallyUnramified.ext_of_iInf w (Ideal.iInf_pow_eq_bot_of_isDomain w hw)
      (fun x => Ideal.Quotient.eq.2 (hcon x))
  have hx : ∀ x : 𝓞 E, σ (x : E) = x := fun x =>
    (congrArg (fun t : 𝓞 E => (t : E)) (DFunLike.congr_fun hs x)).symm
  obtain ⟨a, b, -, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 E) ξ
  have h1 : σ ξ = ξ := by
    rw [← hab, map_div₀]
    exact congrArg₂ (· / ·) (hx a) (hx b)
  have h2 : (2 : E) * ξ = 0 := by linear_combination hσξ - h1
  exact hξ ((mul_eq_zero.1 h2).resolve_left two_ne_zero)

theorem UpperTheory.TP.K.exists_locUnit {B : Base F E} (hB : UpperTheory.TP.W.GoodK σ B) {ξ : E} (hξ : ξ ≠ 0) (hσξ : σ ξ = -ξ) (v : Pl F) :
    ∃ u : (Fv F v ⊗[F] E)ˣ, (u : Fv F v ⊗[F] E) ∈ intLoc F E v ∧ ((u⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) ∈ intLoc F E v ∧
      sigR (Fv F v) σ (u : Fv F v ⊗[F] E) = -(u : Fv F v ⊗[F] E) :=
  _root_.UpperTheory.Reformulated.B.Gs6.exists_locUnit hB hξ hσξ v

end
