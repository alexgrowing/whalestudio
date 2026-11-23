import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsToQuadraticSignPowOfRestrictsToQuadrati
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemNormGroupIffEverywhereNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryCharOfOpenSubgroupAndHom
import Formalism.UnipotentAdelicQuotients.ThmBInHecke
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsNontrivialHeckeChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpenSigmaStableUnitNeighborhoodStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdeleCharacterTrivialOnCongruenceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticCharacterExtendsToIdeleClassStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.CMHeckeEta

theorem eq_one_of_congr : ∀ (E : Type) [Field E] [NumberField E] (m : ℕ), 3 ≤ m → ∀ u : E,
    IsIntegral ℤ ((u - 1) / (m : E)) → (∀ τ : E →+* ℂ, ‖τ u‖ = 1) → u = 1 := by
  intro E _ _ m hm u hint hnorm
  classical
  have hm0 : (m : E) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  set v := (u - 1) / (m : E) with hv
  suffices h0 : v = 0 by
    rw [hv, div_eq_zero_iff, or_iff_left hm0, sub_eq_zero] at h0
    exact h0
  have hb : ∀ τ : E →+* ℂ, ‖τ v‖ < 1 := fun τ => by
    rw [hv, map_div₀, map_sub, map_one, map_natCast, norm_div, Complex.norm_natCast]
    have h1 : ‖τ u - 1‖ ≤ 2 := (norm_sub_le _ _).trans (by rw [hnorm, norm_one]; norm_num)
    have h3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
    rw [div_lt_one (by linarith)]
    linarith
  let w : 𝓞 E := ⟨v, hint⟩
  have hN := Algebra.norm_eq_prod_embeddings ℚ ℂ v
  have hZ : ((Algebra.norm ℤ w : ℤ) : ℚ) = Algebra.norm ℚ v := Algebra.coe_norm_int w
  let τ₀ : E →ₐ[ℚ] ℂ := IsAlgClosed.lift
  have hprod : ‖∏ τ : E →ₐ[ℚ] ℂ, τ v‖ < 1 := by
    rw [norm_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ τ₀)]
    have hr : ∏ τ ∈ Finset.univ.erase τ₀, ‖τ v‖ ≤ 1 :=
      Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun τ _ => (hb τ.toRingHom).le)
    calc ‖τ₀ v‖ * ∏ τ ∈ Finset.univ.erase τ₀, ‖τ v‖ ≤ ‖τ₀ v‖ * 1 :=
          mul_le_mul_of_nonneg_left hr (norm_nonneg _)
      _ < 1 := by rw [mul_one]; exact hb τ₀.toRingHom
  rw [← hN, ← hZ] at hprod
  have hz : Algebra.norm ℤ w = 0 := by
    have : |((Algebra.norm ℤ w : ℤ) : ℝ)| < 1 := by
      have e : algebraMap ℚ ℂ ((Algebra.norm ℤ w : ℤ) : ℚ) = (((Algebra.norm ℤ w : ℤ) : ℝ) : ℂ) := by simp
      rwa [e, Complex.norm_real, Real.norm_eq_abs] at hprod
    have : |(Algebra.norm ℤ w : ℤ)| < 1 := by exact_mod_cast this
    exact Int.abs_lt_one_iff.1 this
  have : w = 0 := (Algebra.norm_eq_zero_iff).1 hz
  exact congrArg Subtype.val this

end GlobalTheory.CMHeckeEta

namespace GlobalTheory.CMHeckeEta

theorem mem_range_of_fixed : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ k : E, σ k = k → ∃ k₀ : F, algebraMap F E k₀ = k := by
  intro F E _ _ _ _ _ σ hcm k hk
  obtain ⟨-, htc, h2, hconj⟩ := hcm
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  obtain ⟨x, hx⟩ : ∃ x : E, σ x ≠ x := by
    by_contra hc
    push_neg at hc
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    refine (InfinitePlace.not_isReal_iff_isComplex.2 (htc.isComplex w)) ?_
    rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    ext y
    change star (w.embedding y) = w.embedding y
    rw [← hconj, hc]
  let f : E →ₗ[F] E := σ.toLinearMap - LinearMap.id
  have hV : LinearMap.ker f ≠ ⊤ := fun h => hx (by
    have : x ∈ LinearMap.ker f := h ▸ Submodule.mem_top
    rw [LinearMap.mem_ker] at this
    simpa [f, sub_eq_zero] using this)
  have hlt : Module.finrank F (LinearMap.ker f) < 2 := h2 ▸ Submodule.finrank_lt hV
  have hle : (F ∙ (1 : E)) ≤ LinearMap.ker f := by
    rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker]
    simp [f]
  have h1 : Module.finrank F (F ∙ (1 : E)) = 1 := finrank_span_singleton one_ne_zero
  have heq : (F ∙ (1 : E)) = LinearMap.ker f := Submodule.eq_of_le_of_finrank_le hle (by omega)
  have hk' : k ∈ F ∙ (1 : E) := by
    rw [heq, LinearMap.mem_ker]
    simp [f, hk]
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hk'
  exact ⟨a, by rw [← ha, Algebra.smul_def, mul_one]⟩

theorem isIntegral_of_finPart_mem : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (x : E), HeckeCharacterZeroLocus.ThmBIn.finPart F E (HeckeCharacterZeroLocus.ThmBIn.incA F E x) ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E → IsIntegral ℤ x := by
  intro F E _ _ _ _ _ x hx
  obtain ⟨Φ, -, hι, hint⟩ := GlobalTheory.HeckeInhabitant.exists_fin (F := F) (E := E)
  obtain ⟨p, hp⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one E x (R := 𝓞 E) fun P => by
    rw [← GlobalTheory.HeckeInhabitant.val_alg, ← hι]
    exact (hint _).1 hx P
  rw [← hp]
  exact RingOfIntegers.isIntegral_coe p

end GlobalTheory.CMHeckeEta

namespace GlobalTheory.CMHeckeEta

theorem base_congr_of_tmul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    Module.finrank F E = 2 → ∀ (y : FiniteAdeleRing (𝓞 F) F) (m : ℕ) (s : FiniteAdeleRing (𝓞 F) F ⊗[F] E),
      s ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E → y ⊗ₜ[F] (1 : E) = 1 + ((2 * m : ℕ) : FiniteAdeleRing (𝓞 F) F ⊗[F] E) * s →
      ∃ t ∈ HeckeCharacterZeroLocus.ThmBIn.intAf F, y = 1 + (m : FiniteAdeleRing (𝓞 F) F) * t := by
  intro F E _ _ _ _ _ h2 y m s hs he
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  let A := FiniteAdeleRing (𝓞 F) F
  let T : A ⊗[F] E →ₗ[F] A :=
    TensorProduct.lift ((LinearMap.mul F A).compl₂ ((Algebra.linearMap F A) ∘ₗ (Algebra.trace F E)))
  have hT : ∀ (a : A) (x : E), T (a ⊗ₜ[F] x) = a * algebraMap F A (Algebra.trace F E x) := fun a x => rfl
  have htr1 : Algebra.trace F E 1 = 2 := by
    rw [show (1 : E) = algebraMap F E 1 from (map_one _).symm, Algebra.trace_algebraMap, h2]
    norm_num
  have hnat : ∀ (k : ℕ) (z : A ⊗[F] E), T ((k : A ⊗[F] E) * z) = (k : A) * T z := fun k z => by
    rw [show ((k : A ⊗[F] E)) * z = (k : F) • z by rw [Algebra.smul_def, map_natCast], T.map_smul,
      Algebra.smul_def, map_natCast]

  have hint : ∀ z ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E, T z ∈ HeckeCharacterZeroLocus.ThmBIn.intAf F := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, x, rfl⟩ := hz
      rw [hT]
      have hxi : IsIntegral ℤ (Algebra.trace F E (x : E)) := Algebra.isIntegral_trace x.2
      let r : 𝓞 F := ⟨_, hxi⟩
      intro v
      rw [map_mul]
      refine mul_mem (ha v) ?_
      change ((Algebra.trace F E (x : E) : F) : v.adicCompletion F) ∈ v.adicCompletionIntegers F
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
        show Algebra.trace F E (x : E) = algebraMap (𝓞 F) F r from rfl, HeightOneSpectrum.valuation_of_algebraMap]
      exact HeightOneSpectrum.intValuation_le_one v r
    | zero => intro v; rw [map_zero, map_zero]; exact zero_mem _
    | add a b _ _ ha hb => intro v; rw [map_add, map_add]; exact add_mem (ha v) (hb v)
    | neg a _ ha => intro v; rw [map_neg, map_neg]; exact neg_mem (ha v)
  refine ⟨T s, hint s hs, ?_⟩
  have e := congrArg T he
  rw [hT, map_add, hnat, show (1 : A ⊗[F] E) = (1 : A) ⊗ₜ[F] (1 : E) from rfl, hT, htr1, one_mul] at e
  have h2A : (2 : A) * algebraMap F A (1 / 2) = 1 := by
    rw [show (2 : A) = algebraMap F A 2 from (map_ofNat _ 2).symm, ← map_mul]
    norm_num
  have e2 : y * algebraMap F A 2 = (1 + (m : A) * T s) * algebraMap F A 2 := by
    rw [e, map_ofNat, Nat.cast_mul, Nat.cast_ofNat]
    ring
  calc y = y * algebraMap F A 2 * algebraMap F A (1 / 2) := by
        rw [mul_assoc, ← map_mul]; norm_num
    _ = (1 + (m : A) * T s) * algebraMap F A 2 * algebraMap F A (1 / 2) := by rw [e2]
    _ = 1 + (m : A) * T s := by rw [mul_assoc, ← map_mul]; norm_num

end GlobalTheory.CMHeckeEta

namespace GlobalTheory.CMHeckeEta

theorem exists_congr_subgroup : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (m : ℕ), 0 < m → ∃ U : Subgroup (AdeleRing (𝓞 F) F ⊗[F] E)ˣ, IsOpen (U : Set (AdeleRing (𝓞 F) F ⊗[F] E)ˣ) ∧
      (∀ x ∈ U, Units.map (Algebra.TensorProduct.map (AlgHom.id (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F)) σ).toRingHom.toMonoidHom x ∈ U) ∧
      ∀ x ∈ U, ∃ s ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E,
        HeckeCharacterZeroLocus.ThmBIn.finPart F E (x : AdeleRing (𝓞 F) F ⊗[F] E) = 1 + (m : FiniteAdeleRing (𝓞 F) F ⊗[F] E) * s := GlobalTheory.T.open_sigma_stable_unit_neighborhood

theorem exists_level_of_sign_char : ∀ (F : Type) [Field F] [NumberField F] (φ : (AdeleRing (𝓞 F) F)ˣ →* Circle),
    Continuous φ → (∀ b, φ b = 1 ∨ φ b = -1) → (∀ b : (AdeleRing (𝓞 F) F)ˣ, (b : AdeleRing (𝓞 F) F).2 = 1 → φ b = 1) →
    ∃ m : ℕ, 0 < m ∧ ∀ n : ℕ, 0 < n → m ∣ n → ∀ b : (AdeleRing (𝓞 F) F)ˣ,
      (∃ t ∈ HeckeCharacterZeroLocus.ThmBIn.intAf F, (b : AdeleRing (𝓞 F) F).2 = 1 + (n : FiniteAdeleRing (𝓞 F) F) * t) →
      (∃ t ∈ HeckeCharacterZeroLocus.ThmBIn.intAf F, ((b⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 = 1 + (n : FiniteAdeleRing (𝓞 F) F) * t) →
      φ b = 1 := GlobalTheory.T.idele_character_trivial_on_congruence

theorem exists_arch_sign_char : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ η : (AdeleRing (𝓞 F) F)ˣ →* Circle, Continuous η → (∀ b, η (b * b) = 1) →
    ∃ ψ : (AdeleRing (𝓞 F) F ⊗[F] E)ˣ →* Circle, Continuous ψ ∧ (∀ b, ψ (ideleMap F E b) = 1 ∨ ψ (ideleMap F E b) = -1) ∧
      ∀ b : (AdeleRing (𝓞 F) F)ˣ, (b : AdeleRing (𝓞 F) F).2 = 1 → ψ (ideleMap F E b) = η b := GlobalTheory.T.quadratic_character_extends_to_idele_class

end GlobalTheory.CMHeckeEta

namespace GlobalTheory.CMHeckeEta

theorem norm_algebraMap_sq (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h2 : Module.finrank F E = 2) (b : AF F) :
    Algebra.norm (AF F) (algebraMap (AF F) (AF F ⊗[F] E) b) = b * b := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  haveI : Nontrivial (AF F) :=
    ((Pi.evalRingHom (fun u : InfinitePlace F => u.Completion) w).comp (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))).domain_nontrivial
  haveI : StrongRankCondition (AF F) := commRing_strongRankCondition _
  rw [Algebra.norm_algebraMap, Module.finrank_baseChange, h2, pow_two]

theorem sq_eq_one_circle (z : Circle) (h : z * z = 1) : z = 1 ∨ z = -1 := by
  have h3 : (z : ℂ) * z = 1 := by exact_mod_cast congrArg (fun w : Circle => (w : ℂ)) h
  rcases mul_self_eq_one_iff.1 h3 with h4 | h4
  · exact Or.inl (Circle.ext h4)
  · exact Or.inr (Circle.ext (by rw [h4]; simp))

theorem continuous_toUnits : Continuous (Circle.toUnits : Circle → ℂˣ) :=
  Units.continuous_iff.2 ⟨continuous_subtype_val, (continuous_subtype_val.comp (continuous_inv : Continuous fun x : Circle => x⁻¹)).congr fun x => Circle.coe_inv x⟩

end GlobalTheory.CMHeckeEta

namespace GlobalTheory.CMHeckeEta

theorem exists_hecke_of_eta (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (η : (AF F)ˣ →* Circle) (hη : IsEta F E η) :
    ∃ χ : Chr F E, IsHecke F E χ ∧ ∀ a, χ (ideleMap F E a) = η a := by
  have h2 : Module.finrank F E = 2 := hcm.2.2.1
  have hconj : ∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x) := hcm.2.2.2
  have hsq : ∀ b : (AF F)ˣ, η (b * b) = 1 := fun b => by
    have := hη.2.2.1 (ideleMap F E b)
    convert this using 2
    ext
    change (b : AF F) * b = Algebra.norm (AF F) (algebraMap (AF F) (AF F ⊗[F] E) (b : AF F))
    rw [norm_algebraMap_sq F E h2]
  obtain ⟨ψ, hψc, hψ2, hψη⟩ := exists_arch_sign_char F E σ hcm η hη.1 hsq
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hmapc : Continuous (ideleMap F E) := by
    have : Continuous (algebraMap (AF F) (AF F ⊗[F] E)) :=
      IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF F) (AF F ⊗[F] E))
    exact Continuous.units_map _ this
  let φ : (AF F)ˣ →* Circle := η / ψ.comp (ideleMap F E)
  have hφ : ∀ b, φ b = η b / ψ (ideleMap F E b) := fun b => rfl
  have hηpm : ∀ b, η b = 1 ∨ η b = -1 := fun b => sq_eq_one_circle _ (by rw [← map_mul]; exact hsq b)
  obtain ⟨m, hm0, hm⟩ := exists_level_of_sign_char F φ (hη.1.div' (hψc.comp hmapc))
    (fun b => by
      rw [hφ]
      rcases hηpm b with h | h <;> rcases hψ2 b with h' | h' <;> rw [h, h'] <;> simp)
    (fun b hb => by rw [hφ, hψη b hb, div_self'])
  set n := 3 * m with hn
  have hn0 : 0 < n := by omega
  set M := 2 * n with hM
  obtain ⟨U, hUo, hUc, hU⟩ := exists_congr_subgroup F E σ M (by omega)
  let α : Eˣ × (AF F)ˣ →* (AF F ⊗[F] E)ˣ :=
    (Units.map (inclR (F := F) (AF F)).toMonoidHom).coprod (ideleMap F E)
  let a : Eˣ × (AF F)ˣ →* ℂˣ := (Circle.toUnits.comp η).comp (MonoidHom.snd _ _)

  have hψu : ∀ x, ‖((Circle.toUnits (ψ x) : ℂˣ) : ℂ)‖ = 1 := fun x => Circle.norm_coe (ψ x)
  have hau : ∀ y, ‖((a y : ℂˣ) : ℂ)‖ = 1 := fun y => Circle.norm_coe (η y.2)
  obtain ⟨χ₀, hχc, hχu, -, hχα⟩ := GlobalTheory.exists_unitary_char_of_open_subgroup_and_hom (AF F ⊗[F] E)ˣ (Eˣ × (AF F)ˣ) U hUo α a
    (Circle.toUnits.comp ψ) (continuous_toUnits.comp hψc) hψu hau (fun y hy => by

      obtain ⟨k, b⟩ := y
      have hxe : α (k, b) = Units.map (inclR (F := F) (AF F)).toMonoidHom k * ideleMap F E b := rfl
      set x := α (k, b) with hx
      let C : (AF F ⊗[F] E)ˣ →* (AF F ⊗[F] E)ˣ :=
        Units.map (Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F)) σ).toRingHom.toMonoidHom
      let kσ : Eˣ := Units.map (σ : E →+* E).toMonoidHom k
      have hCi : C (Units.map (inclR (F := F) (AF F)).toMonoidHom k) = Units.map (inclR (F := F) (AF F)).toMonoidHom kσ := by
        apply Units.ext
        change Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F)) σ ((1 : AF F) ⊗ₜ[F] (k : E)) = (1 : AF F) ⊗ₜ[F] σ (k : E)
        rw [Algebra.TensorProduct.map_tmul]
        rfl
      have hCb : C (ideleMap F E b) = ideleMap F E b := by
        apply Units.ext
        change Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F)) σ ((b : AF F) ⊗ₜ[F] (1 : E)) = (b : AF F) ⊗ₜ[F] (1 : E)
        rw [Algebra.TensorProduct.map_tmul, map_one]
        rfl
      have hCx : C x = Units.map (inclR (F := F) (AF F)).toMonoidHom kσ * ideleMap F E b := by
        rw [hxe, map_mul, hCi, hCb]
      have hq : x / C x ∈ U := U.div_mem hy (hUc x hy)
      have hq' : x / C x = Units.map (inclR (F := F) (AF F)).toMonoidHom (k / kσ) := by
        rw [hCx, hxe, mul_div_mul_right_eq_div, map_div]
      obtain ⟨s, hs, hse⟩ := hU _ hq
      have hkσ0 : σ (k : E) ≠ 0 := (kσ).ne_zero
      set u : E := (k : E) / σ (k : E) with hu
      have hxq : ((x / C x : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = HeckeCharacterZeroLocus.ThmBIn.incA F E u := by
        rw [hq']
        simp only [Units.coe_map, MonoidHom.coe_coe, Units.val_div_eq_div_val]
        rfl
      rw [hxq] at hse
      have hM0 : (M : E) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
      have key : HeckeCharacterZeroLocus.ThmBIn.finPart F E (HeckeCharacterZeroLocus.ThmBIn.incA F E ((u - 1) / M)) = s := by
        have h1 : HeckeCharacterZeroLocus.ThmBIn.finPart F E (HeckeCharacterZeroLocus.ThmBIn.incA F E ((M : E))⁻¹) * (M : FiniteAdeleRing (𝓞 F) F ⊗[F] E) = 1 := by
          rw [← map_natCast (HeckeCharacterZeroLocus.ThmBIn.finPart F E), ← map_natCast (HeckeCharacterZeroLocus.ThmBIn.incA F E), ← map_mul, ← map_mul,
            inv_mul_cancel₀ hM0, map_one, map_one]
        rw [div_eq_mul_inv, map_mul, map_mul, map_sub, map_sub, map_one, map_one, hse, add_sub_cancel_left,
          mul_comm, ← mul_assoc, h1, one_mul]
      have hint := isIntegral_of_finPart_mem F E _ (key ▸ hs)
      have hnorm : ∀ τ : E →+* ℂ, ‖τ u‖ = 1 := fun τ => by
        have hk0 : τ (k : E) ≠ 0 := (map_ne_zero τ).2 k.ne_zero
        rw [hu, map_div₀, hconj, norm_div, norm_star, div_self (norm_ne_zero_iff.2 hk0)]
      have hu1 := eq_one_of_congr E M (by omega) u hint hnorm
      have hfix : σ (k : E) = k := ((div_eq_one_iff_eq hkσ0).1 hu1).symm
      obtain ⟨k₀, hk₀⟩ := mem_range_of_fixed F E σ hcm k hfix
      have hk00 : k₀ ≠ 0 := by
        rintro rfl
        rw [map_zero] at hk₀
        exact k.ne_zero hk₀.symm
      let c : (AF F)ˣ := Units.map (algebraMap F (AF F)).toMonoidHom (Units.mk0 k₀ hk00)
      have hkc : Units.map (inclR (F := F) (AF F)).toMonoidHom k = ideleMap F E c := by
        apply Units.ext
        change inclR (F := F) (AF F) (k : E) = algebraMap (AF F) (AF F ⊗[F] E) (algebraMap F (AF F) k₀)
        rw [← hk₀, ← IsScalarTower.algebraMap_apply]
        exact (Algebra.TensorProduct.includeRight : E →ₐ[F] AF F ⊗[F] E).commutes k₀
      have hxb : x = ideleMap F E (c * b) := by rw [hxe, hkc, map_mul]
      have hηc : η c = 1 := hη.2.1 (Units.mk0 k₀ hk00)
      have hfin : ∀ z : (AF F)ˣ, HeckeCharacterZeroLocus.ThmBIn.finPart F E ((ideleMap F E z : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) =
          (z : AF F).2 ⊗ₜ[F] (1 : E) := fun z => rfl
      have hcong : ∀ z : (AF F)ˣ, ideleMap F E z ∈ U → ∃ t ∈ HeckeCharacterZeroLocus.ThmBIn.intAf F, (z : AF F).2 = 1 + (n : FiniteAdeleRing (𝓞 F) F) * t := by
        intro z hz
        obtain ⟨s', hs', hse'⟩ := hU _ hz
        rw [hfin] at hse'
        exact base_congr_of_tmul F E h2 _ n s' hs' hse'
      have hφ1 := hm n hn0 (Dvd.intro_left _ rfl) (c * b) (hcong _ (hxb ▸ hy))
        (hcong _ (by rw [map_inv, ← hxb]; exact U.inv_mem hy))
      rw [hφ, div_eq_one] at hφ1
      change Circle.toUnits (η b) = Circle.toUnits (ψ x)
      rw [hxb, ← hφ1, map_mul, hηc, one_mul]
      )
  refine ⟨GlobalTheory.unitaryCharToCircle χ₀ hχu, ⟨Continuous.subtype_mk (Units.continuous_val.comp hχc) _, fun k => ?_⟩, fun b => ?_⟩
  · apply Circle.ext
    have := congrArg (fun u : ℂˣ => (u : ℂ)) (hχα (k, 1))
    have e : α (k, 1) = Units.map (inclR (F := F) (AF F)).toMonoidHom k := by simp [α]
    rw [e] at this
    change ((χ₀ (Units.map (inclR (F := F) (AF F)).toMonoidHom k) : ℂˣ) : ℂ) = ((1 : Circle) : ℂ)
    rw [this]
    simp [a]
  · apply Circle.ext
    have := congrArg (fun u : ℂˣ => (u : ℂ)) (hχα (1, b))
    have e : α (1, b) = ideleMap F E b := by simp [α]
    rw [e] at this
    change ((χ₀ (ideleMap F E b) : ℂˣ) : ℂ) = _
    rw [this]
    rfl

end GlobalTheory.CMHeckeEta

namespace GlobalTheory.CMHeckeEta

theorem exists_hecke_resEtaPow_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∃ χ : Chr F E, IsHecke F E χ ∧ ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ 1 := by
  intro F E _ _ _ _ _ σ B hB
  have hcm : IsCMExt F E σ := hB.cm
  have h2 : Module.finrank F E = 2 := hcm.2.2.1
  obtain ⟨η, hη, huniq⟩ := GlobalTheory.IdeleNormChar.globalNormIndexTwo F E h2
  obtain ⟨χ, hχ, hres⟩ := exists_hecke_of_eta F E σ hcm η hη
  refine ⟨χ, hχ, GlobalTheory.LFun.resEtaPow_of_resEta F E h2 χ 1 ⟨⟨η, hη⟩, fun η' hη' a => ?_⟩⟩
  rw [huniq η' hη', pow_one]
  exact hres a

end GlobalTheory.CMHeckeEta

end
