import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsToQuadraticSignPowOfRestrictsToQuadrati
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemNormGroupIffEverywhereNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryCharOfOpenSubgroupAndHom
import Formalism.UnipotentAdelicQuotients.ThmBInHecke
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsNontrivialHeckeChar
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ArchSignChar

def nrm : ℂˣ →* ℂˣ where
  toFun z := Units.mk0 ((z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ))
    (div_ne_zero z.ne_zero (Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 z.ne_zero)))
  map_one' := by ext; simp
  map_mul' z w := by
    ext
    simp only [Units.val_mul, Units.val_mk0, norm_mul, Complex.ofReal_mul]
    rw [mul_div_mul_comm]

theorem nrm_val (z : ℂˣ) : ((nrm z : ℂˣ) : ℂ) = (z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ) := rfl

theorem norm_nrm (z : ℂˣ) : ‖((nrm z : ℂˣ) : ℂ)‖ = 1 := by
  rw [nrm_val, norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 z.ne_zero)]

theorem continuous_nrm : Continuous nrm := by
  have h0 : ∀ z : ℂˣ, ((‖(z : ℂ)‖ : ℝ) : ℂ) ≠ 0 := fun z =>
    Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 z.ne_zero)
  have hc : Continuous fun z : ℂˣ => (z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ) :=
    Units.continuous_val.div (Complex.continuous_ofReal.comp (continuous_norm.comp Units.continuous_val)) h0
  refine Units.continuous_iff.2 ⟨hc, ?_⟩
  exact hc.inv₀ fun z => div_ne_zero z.ne_zero (h0 z)

def normChar {R : Type} [CommRing R] (θ : R →+* ℂ) : Rˣ →* Circle :=
  GlobalTheory.unitaryCharToCircle (nrm.comp (Units.map θ.toMonoidHom)) fun _ => norm_nrm _

theorem normChar_val {R : Type} [CommRing R] (θ : R →+* ℂ) (x : Rˣ) :
    ((normChar θ x : Circle) : ℂ) = θ x / ((‖θ x‖ : ℝ) : ℂ) := rfl

theorem continuous_normChar {R : Type} [CommRing R] [TopologicalSpace R] (θ : R →+* ℂ) (hθ : Continuous θ) :
    Continuous (normChar θ) :=
  Continuous.subtype_mk (Units.continuous_val.comp (continuous_nrm.comp (Continuous.units_map _ hθ))) _

theorem ofReal_div_norm (r : ℝ) (hr : r ≠ 0) :
    ((r : ℂ) / ((‖(r : ℂ)‖ : ℝ) : ℂ)) = if r < 0 then -1 else 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  split_ifs with h
  · rw [abs_of_neg h, Complex.ofReal_neg, div_neg, div_self (Complex.ofReal_ne_zero.2 hr)]
  · rw [abs_of_pos (lt_of_le_of_ne (not_lt.1 h) (Ne.symm hr)), div_self (Complex.ofReal_ne_zero.2 hr)]

theorem sq_eq_one (z : Circle) (h : z * z = 1) : z = 1 ∨ z = -1 := by
  have h3 : (z : ℂ) * z = 1 := by exact_mod_cast congrArg (fun w : Circle => (w : ℂ)) h
  rcases mul_self_eq_one_iff.1 h3 with h4 | h4
  · exact Or.inl (Circle.ext h4)
  · exact Or.inr (Circle.ext (by rw [h4]; simp))

theorem exists_coord {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (w : InfinitePlace F) : ∃ θ : AF F ⊗[F] E →+* ℂ, Continuous θ ∧
      ∀ a : AF F, θ (algebraMap (AF F) (AF F ⊗[F] E) a) = InfinitePlace.Completion.extensionEmbedding w (a.1 w) := by
  letI : Algebra F ℂ := w.embedding.toAlgebra
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  let τ : E →ₐ[F] ℂ := IsAlgClosed.lift
  let g0 : AF F →+* ℂ := (InfinitePlace.Completion.extensionEmbedding w).comp
    ((Pi.evalRingHom (fun u : InfinitePlace F => u.Completion) w).comp
      (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)))
  let g : AF F →ₐ[F] ℂ := ⟨g0, fun x => InfinitePlace.Completion.extensionEmbedding_coe w (WithAbs.toAbs _ x)⟩
  let θ : AF F ⊗[F] E →+* ℂ := (Algebra.TensorProduct.productMap g τ).toRingHom
  have hθ : ∀ a x, θ (a ⊗ₜ[F] x) = g0 a * τ x := fun a x => rfl
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  refine ⟨θ, ?_, fun a => ?_⟩
  · refine IsModuleTopology.continuous_of_ringHom (R := AF F) θ ?_
    have : Continuous g0 := (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp
      ((continuous_apply w).comp continuous_fst)
    refine this.congr fun a => ?_
    change _ = θ (a ⊗ₜ[F] 1)
    rw [hθ, map_one, mul_one]
  · change θ (a ⊗ₜ[F] 1) = _
    rw [hθ, map_one, mul_one]; rfl

def archIdele (F : Type) [Field F] [NumberField F] : ((w : InfinitePlace F) → (w.Completion)ˣ) →* (AF F)ˣ :=
  (MulEquiv.prodUnits (M := InfiniteAdeleRing F) (N := FiniteAdeleRing (𝓞 F) F)).symm.toMonoidHom.comp
    ((MonoidHom.inl _ _).comp (MulEquiv.piUnits (M := fun w : InfinitePlace F => w.Completion)).symm.toMonoidHom)

def archPart {F : Type} [Field F] [NumberField F] (b : (AF F)ˣ) : (w : InfinitePlace F) → (w.Completion)ˣ :=
  MulEquiv.piUnits (MulEquiv.prodUnits (M := InfiniteAdeleRing F) (N := FiniteAdeleRing (𝓞 F) F) b).1

theorem eq_archIdele {F : Type} [Field F] [NumberField F] (b : (AF F)ˣ) (hb : (b : AF F).2 = 1) :
    b = archIdele F (archPart b) := by
  apply Units.ext
  refine Prod.ext rfl ?_
  exact hb

end GlobalTheory.ArchSignChar

namespace GlobalTheory.ArchSignChar

theorem local_sign {K : Type} [Field K] {w : InfinitePlace K} (hw : w.IsReal) (χ : (w.Completion)ˣ →* Circle)
    (hχ : ∀ s, χ (s * s) = 1) (t : (w.Completion)ˣ) :
    χ t = if InfinitePlace.Completion.ringEquivRealOfIsReal hw (t : w.Completion) < 0 then χ (-1) else 1 := by
  set e := InfinitePlace.Completion.ringEquivRealOfIsReal hw with he
  have ht : e (t : w.Completion) ≠ 0 := (map_ne_zero e).2 t.ne_zero
  split_ifs with h
  · have hpos : 0 < -e t := neg_pos.2 h
    obtain ⟨s, hs⟩ : ∃ s : (w.Completion)ˣ, t = -1 * (s * s) := by
      have hs0 : e.symm (Real.sqrt (-e t)) ≠ 0 := (map_ne_zero e.symm).2 (Real.sqrt_ne_zero'.2 hpos)
      refine ⟨Units.mk0 _ hs0, Units.ext (e.injective ?_)⟩
      simp only [Units.val_mul, Units.val_neg, Units.val_one, Units.val_mk0, map_mul, map_neg, map_one,
        RingEquiv.apply_symm_apply, Real.mul_self_sqrt hpos.le]
      ring
    rw [hs, map_mul, hχ, mul_one]
  · have hpos : 0 < e t := lt_of_le_of_ne (not_lt.1 h) (Ne.symm ht)
    obtain ⟨s, hs⟩ : ∃ s : (w.Completion)ˣ, t = s * s := by
      have hs0 : e.symm (Real.sqrt (e t)) ≠ 0 := (map_ne_zero e.symm).2 (Real.sqrt_ne_zero'.2 hpos)
      refine ⟨Units.mk0 _ hs0, Units.ext (e.injective ?_)⟩
      simp only [Units.val_mul, Units.val_mk0, map_mul, RingEquiv.apply_symm_apply, Real.mul_self_sqrt hpos.le]
    rw [hs, hχ]

theorem eta_eq_prod {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (η : (AF F)ˣ →* Circle)
    (hsq : ∀ b, η (b * b) = 1) (b : (AF F)ˣ) (hb : (b : AF F).2 = 1) [DecidableEq (InfinitePlace F)] :
    η b = ∏ w, if InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w) ((b : AF F).1 w) < 0
      then η (archIdele F (Pi.mulSingle w (-1))) else 1 := by
  calc η b = η (archIdele F (archPart b)) := congrArg η (eq_archIdele b hb)
    _ = η (archIdele F (∏ w, Pi.mulSingle w (archPart b w))) := by rw [Finset.univ_prod_mulSingle]
    _ = ∏ w, η (archIdele F (Pi.mulSingle w (archPart b w))) := by rw [map_prod, map_prod]
    _ = _ := Finset.prod_congr rfl fun w _ =>
      local_sign (IsTotallyReal.isReal w) ((η.comp (archIdele F)).comp (MonoidHom.mulSingle (fun u : InfinitePlace F => (u.Completion)ˣ) w))
        (fun s => by
          change η (archIdele F (Pi.mulSingle w (s * s))) = 1
          rw [Pi.mulSingle_mul, map_mul]
          exact hsq _) (archPart b w)

end GlobalTheory.ArchSignChar

namespace GlobalTheory.ArchSignChar

theorem exists_arch_sign_char : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ η : (AdeleRing (𝓞 F) F)ˣ →* Circle, Continuous η → (∀ b, η (b * b) = 1) →
    ∃ ψ : (AdeleRing (𝓞 F) F ⊗[F] E)ˣ →* Circle, Continuous ψ ∧ (∀ b, ψ (ideleMap F E b) = 1 ∨ ψ (ideleMap F E b) = -1) ∧
      ∀ b : (AdeleRing (𝓞 F) F)ˣ, (b : AdeleRing (𝓞 F) F).2 = 1 → ψ (ideleMap F E b) = η b := by
  intro F E _ _ _ _ _ σ hcm η _ hsq
  classical
  haveI : IsTotallyReal F := hcm.1
  choose θ hθc hθ using fun w : InfinitePlace F => exists_coord (F := F) (E := E) w
  let c : InfinitePlace F → Circle := fun w => η (archIdele F (Pi.mulSingle w (-1)))
  let g : InfinitePlace F → ((AF F ⊗[F] E)ˣ →* Circle) := fun w => if c w = 1 then 1 else normChar (θ w)
  have hval : ∀ w b, normChar (θ w) (ideleMap F E b) =
      if InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w) ((b : AF F).1 w) < 0 then -1 else 1 := by
    intro w b
    have hne : (b : AF F).1 w ≠ 0 := (archPart b w).ne_zero
    apply Circle.ext
    rw [normChar_val]
    have e1 : θ w ((ideleMap F E b : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) =
        ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w) ((b : AF F).1 w) : ℝ) : ℂ) := by
      rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply, InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]
      exact hθ w b
    rw [e1, ofReal_div_norm _ ((map_ne_zero _).2 hne)]
    split_ifs <;> simp
  have hgc : ∀ w, Continuous (g w) := fun w => by
    by_cases h : c w = 1
    · simp only [g, h, if_true]; exact continuous_const
    · simp only [g, h, if_false]; exact continuous_normChar _ (hθc w)
  have happ : ∀ x, (∏ w, g w) x = ∏ w, g w x := fun x => MonoidHom.finset_prod_apply _ _ _
  have hc2 : ∀ w, c w = 1 ∨ c w = -1 := fun w => sq_eq_one _ (by simp only [c]; rw [← map_mul]; exact hsq _)
  refine ⟨∏ w, g w, ?_, fun b => ?_, fun b hb => ?_⟩
  · have : ⇑(∏ w, g w) = fun x => ∏ w, g w x := funext happ
    rw [this]; exact continuous_finset_prod _ fun w _ => hgc w
  · apply sq_eq_one
    rw [happ, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun w _ => ?_
    by_cases h : c w = 1
    · simp only [g, h, if_true, MonoidHom.one_apply, mul_one]
    · simp only [g, h, if_false]
      rw [hval]; split_ifs <;> simp
  · rw [happ, eta_eq_prod η hsq b hb]
    refine Finset.prod_congr rfl fun w _ => ?_
    by_cases h : c w = 1
    · simp only [g, h, if_true, MonoidHom.one_apply]
      change 1 = if _ then c w else 1
      rw [h]; split_ifs <;> rfl
    · have h' : c w = -1 := (hc2 w).resolve_left h
      simp only [g, h, if_false]
      rw [hval]
      change _ = if _ then c w else 1
      rw [h']

end GlobalTheory.ArchSignChar
