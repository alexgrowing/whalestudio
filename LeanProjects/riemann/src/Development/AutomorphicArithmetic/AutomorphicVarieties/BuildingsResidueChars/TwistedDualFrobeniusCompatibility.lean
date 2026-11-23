import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GuDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcPolar
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyScaledInverse
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeDualRep
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CyclotomicBarContinuous

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal
open GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Af.Gu UpperTheory.V.Published GlobalTheory.MonoConj
open scoped Matrix

private theorem eig_dual {K : Type} [Field K] (φ : K →+* ℂ) {n : ℕ} (M : GL (Fin n) K) (t : K) (S : Multiset ℂ)
    (h : (M : Matrix (Fin n) (Fin n) K).charpoly.map φ = (S.map fun b => X - C b).prod) :
    (t • ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ).charpoly.map φ =
      ((S.map fun a => φ t * a⁻¹).map fun b => X - C b).prod := by
  rw [← Matrix.charpoly_map] at h
  have h3 := GlobalTheory.charpoly_smul_inv_of_charpoly_eq_prod n (Matrix.GeneralLinearGroup.map φ M) (φ t) _ h
  have h4 : (t • ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).map φ =
      φ t • (((Matrix.GeneralLinearGroup.map φ M)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) := by
    rw [← map_inv]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
    rfl
  rw [← Matrix.transpose_smul, Matrix.charpoly_transpose, ← Matrix.charpoly_map, h4, h3, Multiset.map_map]
  rfl

private theorem cPl_eq {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) :
    cPl w = preplace (IsCMField.complexConj E).toRingEquiv w :=
  HeightOneSpectrum.ext ((GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc _ w))

private theorem normV_preplace {K : Type} [Field K] [NumberField K] (τ : K ≃+* K) (v : HeightOneSpectrum (𝓞 K)) :
    normV (preplace τ v) = normV v := by
  show Nat.card (𝓞 K ⧸ (preplace τ v).asIdeal) = Nat.card (𝓞 K ⧸ v.asIdeal)
  refine Nat.card_congr (Ideal.quotientEquiv _ _ (RingOfIntegers.mapRingEquiv τ) ?_).toEquiv
  exact (Ideal.map_comap_of_surjective (RingOfIntegers.mapRingEquiv τ : 𝓞 K →+* 𝓞 K)
    (RingOfIntegers.mapRingEquiv τ).surjective v.asIdeal).symm

private theorem isFrob_conjGal {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] {τ : K ≃+* K} {σ : Ω ≃+* Ω}
    (h : IsLift τ σ) {A A' : ValuationSubring Ω} (hA : ∀ x, σ x ∈ A' ↔ x ∈ A) {q : ℕ} {g : G K Ω}
    (hg : IsFrob (F := K) A' q g) : IsFrob (F := K) A q (conjGal h g) := by
  refine ⟨conjGal_mem_Dec h hA hg.1, fun x hx => ?_⟩
  rw [← val_lt_one hA, map_sub, apply_conjGal, map_pow]
  exact hg.2 _ ((A'.valuation_le_one_iff _).2 ((hA x).2 ((A.valuation_le_one_iff _).1 hx)))

private theorem isLift_conj {F Ω : Type} [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω]
    {c : G (maximalRealSubfield F) Ω} (hc : IsConjEl c) :
    IsLift (IsCMField.complexConj F).toRingEquiv c.symm.toRingEquiv := by
  obtain ⟨j, hj⟩ := hc
  intro x
  refine c.symm_apply_eq.2 (j.injective ?_)
  rw [hj]
  have h := IsCMField.complexEmbedding_complexConj F (j.comp (algebraMap F Ω)) x
  exact (Complex.conj_conj _).symm.trans (congrArg (starRingEnd ℂ) h.symm)

private noncomputable def dPerp {k : Type} [Field k] {a : ℕ} (W : Submodule k (Fin a → k)) : Submodule k (Fin a → k) :=
  W.dualAnnihilator.comap (dotProductEquiv k (Fin a)).toLinearMap

private theorem mem_dPerp {k : Type} [Field k] {a : ℕ} (W : Submodule k (Fin a → k)) (y : Fin a → k) :
    y ∈ dPerp W ↔ ∀ x ∈ W, y ⬝ᵥ x = 0 := by
  simp [dPerp, Submodule.mem_dualAnnihilator]

private theorem isCompl_dPerp {k : Type} [Field k] {a : ℕ} {W U : Submodule k (Fin a → k)}
    (h : IsCompl W U) : IsCompl (dPerp W) (dPerp U) :=
  (Submodule.orderIsoMapComap (dotProductEquiv k (Fin a))).symm.isCompl
    (Subspace.isCompl_dualAnnihilator h)

private theorem dPerp_dPerp {k : Type} [Field k] {a : ℕ} (W : Submodule k (Fin a → k)) :
    dPerp (dPerp W) = W := by
  ext y
  rw [mem_dPerp]
  constructor
  · intro h
    rw [← Subspace.dualAnnihilator_dualCoannihilator_eq (W := W), Submodule.mem_dualCoannihilator]
    intro φ hφ
    obtain ⟨x, rfl⟩ := (dotProductEquiv k (Fin a)).surjective φ
    have := h x hφ
    rw [dotProduct_comm] at this
    simpa using this
  · intro hy x hx
    rw [dotProduct_comm]
    exact (mem_dPerp W x).1 hx y hy

private theorem mulVec_mem_dPerp {k : Type} [Field k] {a : ℕ} {W : Submodule k (Fin a → k)}
    (M : Matrix (Fin a) (Fin a) k) (h : ∀ v ∈ W, M.transpose.mulVec v ∈ W) :
    ∀ y ∈ dPerp W, M.mulVec y ∈ dPerp W := by
  intro y hy
  rw [mem_dPerp] at hy ⊢
  intro x hx
  have := hy _ (h x hx)
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm]
  exact this

private theorem ss_dual : ∀ (Γ k : Type) [Group Γ] [Field k] (a : ℕ) (r : Γ →* GL (Fin a) k),
    IsSSRep r → IsSSRep (GlobalTheory.MonoConj.dualRep r) := by
  intro Γ k _ _ a r hr W hW
  obtain ⟨U, hU, hc⟩ := hr (dPerp W) (by
    intro g
    apply mulVec_mem_dPerp
    intro v hv
    have := hW g⁻¹ v hv
    rwa [coe_dualRep, inv_inv] at this)
  refine ⟨dPerp U, ?_, ?_⟩
  · intro g
    apply mulVec_mem_dPerp
    intro v hv
    rw [coe_dualRep, Matrix.transpose_transpose]
    exact hU g⁻¹ v hv
  · have := isCompl_dPerp hc
    rwa [dPerp_dPerp] at this

private theorem ss_tw {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ)
    (h : IsSSRep r) : IsSSRep (tw r χ) := by
  have key : ∀ W, IsInv (tw r χ) W ↔ IsInv r W := fun W => by
    constructor
    · intro h g v hv
      have := W.smul_mem ((χ g : k)⁻¹) (h g v hv)
      rwa [tw_val, Matrix.smul_mulVec, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul] at this
    · intro h g v hv
      rw [tw_val, Matrix.smul_mulVec]
      exact W.smul_mem _ (h g v hv)
  intro W hW
  obtain ⟨W', hW', hc⟩ := h W ((key W).1 hW)
  exact ⟨W', (key W').2 hW', hc⟩

private theorem ss_comp {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (f : Γ →* Γ)
    (hf : Function.Surjective f) (h : IsSSRep r) : IsSSRep (r.comp f) := by
  intro W hW
  obtain ⟨W', hW', hc⟩ := h W fun g v hv => by
    obtain ⟨g, rfl⟩ := hf g
    exact hW g v hv
  exact ⟨W', fun g v hv => hW' (f g) v hv, hc⟩

private theorem cont_cycBar (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime] :
    Continuous (cycBar F Ω l) :=
  _root_.UpperTheory.Reformulated.B.CyclotomicBarContinuous.cont_cycBar F Ω l

private theorem cont_twDual {Γ k : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Field k]
    [TopologicalSpace k] [IsTopologicalRing k] {n : ℕ} (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ)
    (hr : Continuous r) (hχ : Continuous χ) : Continuous (tw (dualRep r) χ) := by
  have h : Continuous fun s => (tw (dualRep r) χ s : Matrix (Fin n) (Fin n) k) := by
    simp only [tw_val, coe_dualRep]
    exact (Units.continuous_val.comp hχ).smul
      (Units.continuous_val.comp (hr.comp continuous_inv)).matrix_transpose
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  simp only [← map_inv]
  exact h.comp continuous_inv

private theorem frob_conj {F Ω : Type} [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {n : ℕ} {r : G F Ω →* GL (Fin n) (Qbar l)} {σ : Ω ≃+* Ω}
    (hL : IsLift (IsCMField.complexConj F).toRingEquiv σ) {w : HeightOneSpectrum (𝓞 F)} {B : Multiset ℂˣ}
    (hB : FrobEig ι r (cPl w) (algSat n (normV (cPl w)) B)) :
    FrobEig ι (r.comp (conjGal hL)) w (algSat n (normV w) B) := by
  intro A hA
  have hAA : ∀ y, σ y ∈ A ↔ y ∈ A.comap σ.toRingHom := fun _ => Iff.rfl
  rw [cPl_eq] at hB
  obtain ⟨h1, h2⟩ := hB _ (isPlaceOver_preplace hL hAA hA)
  refine ⟨fun s hs => h1 _ (conjGal_mem_Ine hL hAA hs), fun s hs => ?_⟩
  have e := h2 (conjGal hL s) (by rw [normV_preplace]; exact isFrob_conjGal hL hAA hs)
  rw [normV_preplace, ← map_inv] at e
  exact e

private theorem frob_twDual {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {n : ℕ} {r : G F Ω →* GL (Fin n) (Qbar l)}
    {w : HeightOneSpectrum (𝓞 F)} (hw : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal) {B : Multiset ℂˣ}
    (hB : FrobEig ι r w (algSat n (normV w) (B.map (·⁻¹)))) :
    FrobEig ι (tw (dualRep r) (cycBar F Ω l ^ (1 - (n : ℤ)))) w (algSat n (normV w) B) := by
  intro A hA
  obtain ⟨h0, h1⟩ := hB A hA
  refine ⟨fun s hs => ?_, fun σ hσ => ?_⟩
  · have hc : cycZ F Ω l s = 1 := by
      refine Units.ext (PadicInt.ext_of_toZModPow.mp fun m => ?_)
      rw [cycZ_toZModPow_eq hw hA (q := 1) (fun x hx => by simpa using hs.2 x hx) m]
      simp
    have hc' : cycBar F Ω l s = 1 := by
      rw [cycBar, MonoidHom.comp_apply, hc, map_one]
    apply Units.ext
    rw [tw_val, coe_dualRep, map_inv, h0 s hs, MonoidHom.zpow_apply, hc']
    simp
  have h2 : ((cycBar F Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV w : ℕ) := by
    change algebraMap ℚ_[l] (Qbar l) (PadicInt.Coe.ringHom ((cycZ F Ω l σ : ℤ_[l]ˣ) : ℤ_[l])) = _
    rw [cycZ_of_isFrob hw hA hσ, map_natCast, map_natCast]
  have hq0 : normV w ≠ 0 := by
    intro h0
    rw [h0, Nat.cast_zero] at h2
    exact Units.ne_zero _ h2
  have hqR : (0 : ℝ) < normV w := by exact_mod_cast Nat.pos_of_ne_zero hq0
  set d : ℂ := ((((normV w : ℕ) : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) with hd
  have hd0 : d ≠ 0 := by
    rw [hd]; exact_mod_cast (Real.rpow_pos_of_pos hqR _).ne'
  have hdd : d * d = (normV w : ℂ) ^ ((n : ℤ) - 1) := by
    rw [hd, ← Complex.ofReal_mul, ← Real.rpow_add hqR, add_halves,
      show ((n : ℝ) - 1) = (((n : ℤ) - 1 : ℤ) : ℝ) by push_cast; ring, Real.rpow_intCast]
    push_cast
    rfl
  have h4 : ι.toRingHom (((cycBar F Ω l ^ (1 - (n : ℤ))) σ⁻¹ : (Qbar l)ˣ) : Qbar l) = d * d := by
    change ι _ = _
    rw [MonoidHom.zpow_apply, map_inv (cycBar F Ω l),
      Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, h2, map_zpow₀, map_inv₀, map_natCast, hdd, inv_zpow',
      neg_sub]
  have hS : ∀ B : Multiset ℂˣ, algSat n (normV w) B = B.map fun α : ℂˣ => d * (α : ℂ) := fun B => by
    simp only [algSat, ← hd, Multiset.bind_def, Multiset.pure_def, Multiset.bind_singleton, Multiset.map_map,
      Function.comp_def]
  rw [tw_val, coe_dualRep, map_inv r σ⁻¹, eig_dual _ _ _ _ (h1 σ hσ), h4, hS, hS]
  simp only [Multiset.map_map, Function.comp_def]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun a _ => ?_)
  congr 2
  rw [Units.val_inv_eq_inv_val]
  have := a.ne_zero
  field_simp

theorem UpperTheory.twistedDual_frobenius_compatibility :
    IsoOfFrob → PolOfFrob := by
  intro H E Ω _ _ _ _ _ _ l _ ι n r hr hs hF c hc
  have hL := isLift_conj hc
  have h0 : Ideal.span {((l : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hl : ∀ᶠ v : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ((l : ℕ) : 𝓞 E) ∉ v.asIdeal :=
    (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)
  have hsurj : Function.Surjective (conjGal hL) := fun g =>
    ⟨conjGal hL.symm g, AlgEquiv.ext fun x => by simp [UpperTheory.V.conjGal_apply]⟩
  have hχ : Continuous (cycBar E Ω l ^ (1 - (n : ℤ)) : G E Ω →* (Qbar l)ˣ) :=
    (cont_cycBar E Ω l).zpow (1 - (n : ℤ))
  obtain ⟨P, hP⟩ := H E Ω l ι n (r.comp (conjGal hL)) (tw (dualRep r) (cycBar E Ω l ^ (1 - (n : ℤ))))
    (hr.comp (continuous_conjGal hL)) (cont_twDual r _ hr hχ) (ss_comp r _ hsurj hs)
    (ss_tw _ _ (ss_dual _ _ _ r hs)) (by
      filter_upwards [hF, hl] with w ⟨B, hB, hB'⟩ hw
      exact ⟨_, frob_conj hL hB', frob_twDual hw hB⟩)
  refine ⟨P, fun s s' hs' => ?_⟩
  have e : s' = conjGal hL s := AlgEquiv.ext fun x => DFunLike.congr_fun hs' x
  have h1 := congrArg (fun g : GL (Fin n) (Qbar l) => ((g * P : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l))) (hP s)
  simp only [inv_mul_cancel_right, Units.val_mul, tw_val, coe_dualRep, MonoidHom.comp_apply] at h1
  rw [e, Matrix.mul_assoc, ← h1, Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.transpose_mul,
    ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.transpose_one, Matrix.one_mul]
