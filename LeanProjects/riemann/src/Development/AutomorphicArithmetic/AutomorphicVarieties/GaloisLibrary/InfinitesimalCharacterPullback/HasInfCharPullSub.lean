import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Formalism.LocalToGlobal.UnitaryNorms.CharTransport
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis

noncomputable section

open NumberField IsDedekindDomain Topology Matrix Neutral.B1 Formalism.L2.Host Formalism.L2.Host.CT GlobalTheory.CuspRep
open scoped ContDiff

namespace UpperTheory.V.FieldIso

variable {E F : Type} [Field E] [NumberField E] [IsTotallyComplex E] [Field F] [NumberField F] [IsTotallyComplex F] {a : ℕ}

omit [NumberField E] in
theorem coord_conj (τ : E →+* ℂ) (x : Cinf E) :
    coord (ComplexEmbedding.conjugate τ) x = starRingEnd ℂ (coord τ x) := by
  have hne : ComplexEmbedding.conjugate τ ≠ τ := fun h =>
    InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk τ))
      (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 h))
  unfold coord
  simp only [InfinitePlace.mk_conjugate_eq]
  rcases InfinitePlace.embedding_mk_eq τ with h | h
  · rw [if_pos h, if_neg (by rw [InfinitePlace.mk_conjugate_eq, h]; exact hne.symm)]; rfl
  · rw [if_pos (by rw [InfinitePlace.mk_conjugate_eq, h]), if_neg (by rw [h]; exact hne)]; simp

omit [NumberField E] [IsTotallyComplex E] in
theorem coord_embedding (w : InfinitePlace E) (x : Cinf E) : coord w.embedding x = x w := by
  unfold coord
  rw [if_pos (by rw [InfinitePlace.mk_embedding])]
  simp [InfinitePlace.mk_embedding]

omit [NumberField E] [IsTotallyComplex E] in
theorem coord_smul (τ : E →+* ℂ) (t : ℝ) (x : Cinf E) : coord τ (t • x) = t • coord τ x := by
  unfold coord
  split_ifs <;> simp

omit [NumberField E] [IsTotallyComplex E] in
theorem coord_star (τ : E →+* ℂ) (x : Cinf E) : coord τ (star x) = star (coord τ x) := by
  unfold coord
  split_ifs <;> simp

omit [IsTotallyComplex E] in
theorem norm_coord_le (τ : E →+* ℂ) (x : Cinf E) : ‖coord τ x‖ ≤ ‖x‖ := by
  unfold coord
  split_ifs
  · exact norm_le_pi_norm x _
  · exact (Complex.norm_conj _).trans_le (norm_le_pi_norm x _)

omit [NumberField E] [IsTotallyComplex E] in
theorem coord_atEmb_of_ne {τ τ' : E →+* ℂ} (h : InfinitePlace.mk τ' ≠ InfinitePlace.mk τ) (z : ℂ) :
    coord τ' (atEmb τ z) = 0 := by
  classical
  unfold coord atEmb
  split_ifs <;> simp [Pi.single_eq_of_ne h]

variable (j : E ≃+* F)

omit [NumberField E] [IsTotallyComplex E] [NumberField F] [IsTotallyComplex F] in

def cinf : Cinf E →+* Cinf F := RingHom.pi fun u => coord (u.embedding.comp (j : E →+* F))

omit [NumberField E] [NumberField F] [IsTotallyComplex F] in
theorem coord_cinf (τ : F →+* ℂ) (x : Cinf E) : coord τ (cinf j x) = coord (τ.comp (j : E →+* F)) x := by
  have h0 : cinf j x (InfinitePlace.mk τ) = coord ((InfinitePlace.mk τ).embedding.comp (j : E →+* F)) x := rfl
  conv_lhs => unfold coord
  split_ifs with h
  · exact h0.trans (by rw [h])
  · have h' := (InfinitePlace.embedding_mk_eq τ).resolve_left h
    change starRingEnd ℂ (cinf j x _) = _
    rw [h0, h']
    exact (congrArg (starRingEnd ℂ) (coord_conj (τ.comp (j : E →+* F)) x)).trans (starRingEnd_self_apply _)

omit [NumberField E] [NumberField F] [IsTotallyComplex F] in
theorem cinf_cinf (x : Cinf E) : cinf j.symm (cinf j x) = x := by
  funext w
  change coord (w.embedding.comp _) _ = _
  rw [coord_cinf, ← coord_embedding w x]
  congr 2
  ext y
  simp

omit [NumberField E] [NumberField F] in
theorem cinf_atEmb (τ : F →+* ℂ) (z : ℂ) : cinf j (atEmb (τ.comp (j : E →+* F)) z) = atEmb τ z := by
  funext u
  rw [← coord_embedding u (atEmb τ z)]
  change coord (u.embedding.comp _) _ = _
  generalize u.embedding = σ
  by_cases h : InfinitePlace.mk σ = InfinitePlace.mk τ
  · rcases InfinitePlace.mk_eq_iff.1 h.symm with rfl | rfl
    · rw [coord_atEmb, coord_atEmb]
    · rw [coord_conj, coord_atEmb]
      exact (coord_conj (τ.comp (j : E →+* F)) _).trans (by rw [coord_atEmb])
  · rw [coord_atEmb_of_ne h, coord_atEmb_of_ne]
    intro h'
    apply h
    ext y
    simpa [InfinitePlace.apply] using congrArg (fun w : InfinitePlace E => w (j.symm y)) h'

def adm : Ad E →+* Ad F :=
  RingHom.prodMap ((infEq F).toRingHom.comp ((cinf j).comp (infEq E).symm.toRingHom)) (finMap j)

theorem pInf_adm (x : Ad E) : pInf F (adm j x) = cinf j (pInf E x) := (infEq F).symm_apply_apply _

theorem pFin_adm (x : Ad E) : pFin F (adm j x) = finMap j (pFin E x) := rfl

omit [IsTotallyComplex E] [IsTotallyComplex F] in
theorem finMap_algebraMap (k : E) : finMap j (algebraMap E (Af E) k) = algebraMap F (Af F) (j k) :=
  FiniteAdeleRing.ext _ fun v => by
    have h := compEquiv_symm_algebraMap j.symm v (j k)
    rw [RingEquiv.symm_apply_apply] at h
    exact h

omit [IsTotallyComplex E] [IsTotallyComplex F] in
theorem finMap_finMap (x : Af E) : finMap j.symm (finMap j x) = x := by
  have key : ∀ (v w : HeightOneSpectrum (𝓞 E)) (_ : w = v) (f : w.adicCompletion E → v.adicCompletion E),
      Continuous f → (∀ k : E, f (algebraMap E _ k) = algebraMap E _ k) → f (pLoc E w x) = pLoc E v x := by
    rintro _ v rfl f hf h
    exact congrFun ((HeightOneSpectrum.denseRange_algebraMap (K := E) v).equalizer hf continuous_id (funext h)) _
  refine FiniteAdeleRing.ext _ fun v => key v _ (plMap_symm_plMap j v)
    ((compEquiv j v).symm ∘ (compEquiv j.symm (plMap j v)).symm)
    ((continuous_compEquiv_symm _ _).comp (continuous_compEquiv_symm _ _)) fun k => ?_
  have h := compEquiv_symm_algebraMap j.symm (plMap j v) (j k)
  rw [RingEquiv.symm_apply_apply] at h
  rw [Function.comp_apply, h, compEquiv_symm_algebraMap]

theorem adm_adm (x : Ad E) : adm j.symm (adm j x) = x :=
  ad_ext (by rw [pInf_adm, pInf_adm, cinf_cinf]) (finMap_finMap j _)

theorem adm_algebraMap (k : E) : adm j (algebraMap E (Ad E) k) = algebraMap F (Ad F) (j k) :=
  ad_ext (funext fun u => by
    rw [pInf_adm, pInf_algebraMap]
    exact coord_algebraMap _ k) (finMap_algebraMap j k)

omit [IsTotallyComplex E] [IsTotallyComplex F] in
theorem norm_cinf_le (x : Cinf E) : ‖cinf j x‖ ≤ ‖x‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun _ => norm_coord_le _ x

omit [IsTotallyComplex E] [IsTotallyComplex F] in
variable (a) in

def lieMap : Lie E a →L[ℝ] Lie F a :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X i k => cinf j (X i k)
      map_add' := fun X Y => funext fun i => funext fun k => map_add (cinf j) _ _
      map_smul' := fun t X => funext fun i => funext fun k => funext fun u => coord_smul _ t _ }

omit [IsTotallyComplex E] [IsTotallyComplex F] in
theorem continuous_cinf : Continuous (cinf j) :=
  AddMonoidHomClass.continuous_of_bound (cinf j) 1 fun x => by simpa using norm_cinf_le j x

theorem continuous_adm : Continuous (adm j) := by
  have h : Continuous (infEq E).symm := continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)
  exact ((continuous_infEq F).comp ((continuous_cinf j).comp h)).prodMap (continuous_finMap j)

variable (a) in

def gaMap : GA E a →* GA F a := GeneralLinearGroup.map (adm j)

theorem gaMap_gaMap (g : GA E a) : gaMap a j.symm (gaMap a j g) = g :=
  Units.ext (Matrix.ext fun _ _ => adm_adm j _)

theorem pInf_gaMap (g : GA E a) : GeneralLinearGroup.map (pInf F) (gaMap a j g) =
    GeneralLinearGroup.map (cinf j) (GeneralLinearGroup.map (pInf E) g) :=
  Units.ext (Matrix.ext fun _ _ => pInf_adm j _)

theorem pFin_gaMap (g : GA E a) : GeneralLinearGroup.map (pFin F) (gaMap a j g) =
    GeneralLinearGroup.map (finMap j) (GeneralLinearGroup.map (pFin E) g) := rfl

theorem gaMap_infGL (y : GL (Fin a) (Cinf E)) :
    gaMap a j (infGL E a y) = infGL F a (GeneralLinearGroup.map (cinf j) y) :=
  ga_ext (by rw [pInf_gaMap, pInf_infGL, pInf_infGL]) (by rw [pFin_gaMap, pFin_infGL, pFin_infGL, map_one])

theorem gaMap_finGL (k : GL (Fin a) (Af E)) :
    gaMap a j (finGL E a k) = finGL F a (GeneralLinearGroup.map (finMap j) k) :=
  ga_ext (by rw [pInf_gaMap, pInf_finGL, pInf_finGL, map_one]) (by rw [pFin_gaMap, pFin_finGL, pFin_finGL])

theorem gaMap_ratGL (γ : GL (Fin a) E) :
    gaMap a j (ratGL E a γ) = ratGL F a (GeneralLinearGroup.map (j : E →+* F) γ) :=
  Units.ext (Matrix.ext fun _ _ => adm_algebraMap j _)

theorem chart_gaMap (φ : GA F a → ℂ) (g : GA E a) {x : Lie E a} (hx : x ∈ invSet E a) :
    chart (fun g => φ (gaMap a j g)) g x = chart φ (gaMap a j g) (lieMap a j x) ∧ lieMap a j x ∈ invSet F a := by
  obtain ⟨u, hu⟩ := id hx
  obtain rfl : x = toL u.val := hu.symm
  have e : lieMap a j (toL u.val) = toL (GeneralLinearGroup.map (cinf j) u).val := rfl
  rw [e, chart_val, chart_val, map_mul, gaMap_infGL]
  exact ⟨rfl, val_mem_invSet _⟩

theorem gaMap_mem_Sm {φ : GA F a → ℂ} (hφ : φ ∈ Sm F a) : (fun g => φ (gaMap a j g)) ∈ Sm E a := fun g =>
  ((hφ (gaMap a j g)).comp (lieMap a j).contDiff.contDiffOn
    fun _ hx => (chart_gaMap j φ g hx).2).congr fun _ hx => (chart_gaMap j φ g hx).1

variable (a) in

def pull : Sm F a ≃ₗ[ℂ] Sm E a where
  toFun φ := ⟨fun g => φ.1 (gaMap a j g), gaMap_mem_Sm j φ.2⟩
  invFun φ := ⟨fun g => φ.1 (gaMap a j.symm g), gaMap_mem_Sm j.symm φ.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv φ := Subtype.ext <| funext fun g => congrArg φ.1 (gaMap_gaMap j.symm g)
  right_inv φ := Subtype.ext <| funext fun g => congrArg φ.1 (gaMap_gaMap j g)

theorem pull_apply (φ : Sm F a) (g : GA E a) : (pull a j φ).1 g = φ.1 (gaMap a j g) := rfl

theorem pull_pull (φ : Sm F a) : pull a j.symm (pull a j φ) = φ := (pull a j).left_inv φ

theorem rt_pull (h : GA E a) (φ : Sm F a) : rt E a h (pull a j φ) = pull a j (rt F a (gaMap a j h) φ) :=
  Subtype.ext <| funext fun g => congrArg φ.1 (map_mul (gaMap a j) g h)

theorem lie_pull (X : Lie E a) (φ : Sm F a) : lie E a X (pull a j φ) = pull a j (lie F a (lieMap a j X) φ) := by
  refine Subtype.ext <| funext fun g => ?_
  have e : chart (pull a j φ).1 g =ᶠ[𝓝 (oneL E a)] chart φ.1 (gaMap a j g) ∘ lieMap a j :=
    Filter.eventually_of_mem (isOpen_invSet.mem_nhds isUnit_one) fun x hx => (chart_gaMap j φ.1 g hx).1
  have h1 : lieMap a j (oneL E a) = oneL F a := map_one (cinf j).mapMatrix
  have h2 := HasFDerivAt.comp (oneL E a) (f := lieMap a j)
    (by rw [h1]; exact (differentiableAt_chart φ.2 (gaMap a j g)).hasFDerivAt) (lieMap a j).hasFDerivAt
  change fderiv ℝ _ _ X = fderiv ℝ _ _ _
  rw [e.fderiv_eq, h2.fderiv]
  rfl

omit [IsTotallyComplex E] [IsTotallyComplex F] in

def opMap : Op E a → Op F a
  | .fin k => .fin (GeneralLinearGroup.map (finMap j) k)
  | .cpt k => .cpt ⟨(cinf j).mapMatrix k.1, Matrix.mem_unitaryGroup_iff.2 (by
      have e : star ((cinf j).mapMatrix k.1) = (cinf j).mapMatrix (star k.1) :=
        Matrix.ext fun _ _ => funext fun u => (coord_star _ _).symm
      rw [e, ← map_mul, Matrix.mem_unitaryGroup_iff.1 k.2, map_one])⟩
  | .lie X => .lie (lieMap a j X)

theorem act_pull (o : Op E a) (φ : Sm F a) : act o (pull a j φ) = pull a j (act (opMap j o) φ) := by
  cases o with
  | fin k => exact (rt_pull j _ φ).trans (by rw [gaMap_finGL]; rfl)
  | cpt k =>
    refine (rt_pull j (infGL E a (Unitary.toUnits k)) φ).trans ?_
    rw [gaMap_infGL]
    exact congrArg (fun y => pull a j (rt F a (infGL F a y) φ)) (Units.ext rfl)
  | lie X => exact lie_pull j X φ

theorem pull_act (o : Op F a) (φ : Sm F a) : pull a j (act o φ) = act (opMap j.symm o) (pull a j φ) := by
  conv_lhs => rw [← pull_pull j φ, act_pull]
  exact pull_pull j.symm _

theorem Eop_pull (τ : F →+* ℂ) (i k : Fin a) (φ : Sm F a) :
    Eop (τ.comp (j : E →+* F)) i k (pull a j φ) = pull a j (Eop τ i k φ) := by
  have h : ∀ z, lieMap a j (toL (Matrix.single i k (atEmb (τ.comp (j : E →+* F)) z))) =
      toL (Matrix.single i k (atEmb τ z)) := fun z => by
    rw [← cinf_atEmb j τ z]
    exact Matrix.map_single i k _ (cinf j)
  simp only [Eop, lieS_apply, LinearMap.smul_apply, LinearMap.sub_apply, lie_pull, h, map_smul, map_sub]

theorem cap_pull (τ : F →+* ℂ) (u : ℂ) (φ : Sm F a) :
    cap (τ.comp (j : E →+* F)) u (pull a j φ) = pull a j (cap τ u φ) := by
  have h := map_qdet ((pull a j).conjAlgEquiv ℂ).toAlgHom (Eop (a := a) τ) (u + ((a : ℂ) - 1) / 2)
  have e : (fun i k => ((pull a j).conjAlgEquiv ℂ).toAlgHom (Eop τ i k)) = Eop (τ.comp (j : E →+* F)) := by
    funext i k
    refine LinearMap.ext fun ψ => ?_
    obtain ⟨ψ, rfl⟩ := (pull a j).surjective ψ
    rw [Eop_pull]
    change pull a j (Eop τ i k ((pull a j).symm (pull a j ψ))) = _
    rw [LinearEquiv.symm_apply_apply]
  rw [e] at h
  rw [cap, ← h, cap]
  generalize Formalism.REAL.qdet (Eop (a := a) τ) (u + ((a : ℂ) - 1) / 2) = z
  change pull a j (z ((pull a j).symm (pull a j φ))) = _
  rw [LinearEquiv.symm_apply_apply]

omit [NumberField E] [IsTotallyComplex E] [NumberField F] [IsTotallyComplex F] in
theorem exists_comp (τ : E →+* ℂ) : ∃ σ : F →+* ℂ, σ.comp (j : E →+* F) = τ :=
  ⟨τ.comp (j.symm : F →+* E), RingHom.ext fun x => by simp⟩

theorem Zalg_pull {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) :
    ∃ z' ∈ Zalg F a, ∀ φ, z (pull a j φ) = pull a j (z' φ) := by
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨τ, u, rfl⟩ := hx
    obtain ⟨σ, rfl⟩ := exists_comp j τ
    exact ⟨_, Algebra.subset_adjoin (by exact ⟨_, _, rfl⟩), cap_pull j σ u⟩
  | algebraMap c => exact ⟨_, Subalgebra.algebraMap_mem _ c, fun φ => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨x', h1, h2⟩ := hx
    obtain ⟨y', h3, h4⟩ := hy
    exact ⟨x' + y', add_mem h1 h3, fun φ => by simp [h2, h4]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨x', h1, h2⟩ := hx
    obtain ⟨y', h3, h4⟩ := hy
    exact ⟨x' * y', mul_mem h1 h3, fun φ => by simp [h2, h4]⟩

omit [IsTotallyComplex E] [IsTotallyComplex F] in
theorem height_le (y : GL (Fin a) (Cinf E)) : height (GeneralLinearGroup.map (cinf j) y) ≤ height y := by
  have h1 : ∀ y : GL (Fin a) (Cinf E), ‖toL (GeneralLinearGroup.map (cinf j) y).val‖ ≤ ‖toL y.val‖ := fun y =>
    (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun k =>
      (norm_cinf_le j _).trans ((norm_le_pi_norm _ _).trans (norm_le_pi_norm (toL y.val) _))
  have h3 := h1 y⁻¹
  rw [map_inv] at h3
  unfold height
  linarith [h1 y]

theorem isAutForm_pull {φ : Sm F a} (h : IsAutForm φ) : IsAutForm (pull a j φ) where
  left γ g := by rw [pull_apply, map_mul, gaMap_ratGL, h.left, pull_apply]
  level := by
    have hc : Continuous (GeneralLinearGroup.map (n := Fin a) (finMap j)) :=
      Continuous.units_map _ (continuous_id.matrix_map (continuous_finMap j))
    convert h.level.preimage hc using 1
    ext k
    exact (Eq.congr_left (act_pull j (.fin k) φ)).trans (pull a j).injective.eq_iff
  kfin := by
    have := h.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k => cptRep F a k φ)).map
      (pull a j).toLinearMap) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨_, rfl⟩, (act_pull j (.cpt k) φ).symm⟩
  zfin := by
    have := h.zfin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ ((fun z : Module.End ℂ (Sm F a) => z φ) ''
      Zalg F a)).map (pull a j).toLinearMap) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨z', h1, h2⟩ := Zalg_pull j hz
    exact ⟨_, Submodule.subset_span ⟨z', h1, rfl⟩, (h2 φ).symm⟩
  growth g := by
    obtain ⟨C, N, h1⟩ := h.growth (gaMap a j g)
    refine ⟨|C|, N, fun y => ?_⟩
    rw [pull_apply, map_mul, gaMap_infGL]
    have h0 := one_le_height (GeneralLinearGroup.map (cinf j) y)
    exact (h1 _).trans (mul_le_mul (le_abs_self C) (pow_le_pow_left₀ (by linarith) (height_le j y) N)
      (by positivity) (abs_nonneg C))

theorem gaMap_unip {r : ℕ} (x : BlockIx a r → Ad E) : gaMap a j (unip x) = unip fun p => adm j (x p) := by
  ext i k
  change adm j ((1 + nilM x : Matrix (Fin a) (Fin a) (Ad E)) i k) =
    (1 + nilM fun p => adm j (x p) : Matrix (Fin a) (Fin a) (Ad F)) i k
  simp only [nilM, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply, map_add]
  split_ifs <;> simp

theorem mem_ratN {r : ℕ} {x : BlockIx a r → Ad E} (hx : x ∈ ratN E a r) : (fun p => adm j (x p)) ∈ ratN F a r := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨fun p => j (y p), funext fun p => (adm_algebraMap j _).symm⟩

open MeasureTheory in
theorem isCuspidal_pull {φ : GA F a → ℂ} (hφ : IsCuspidal φ) : IsCuspidal fun g => φ (gaMap a j g) := by
  intro r h0 h1 _ _ μ 𝓕 hμ hF g
  let β : (BlockIx a r → Ad E) ≃ₜ+ (BlockIx a r → Ad F) :=
    { toFun := fun x p => adm j (x p)
      invFun := fun x p => adm j.symm (x p)
      left_inv := fun x => funext fun p => adm_adm j _
      right_inv := fun x => funext fun p => adm_adm j.symm _
      map_add' := fun x y => funext fun p => map_add (adm j) _ _
      continuous_toFun := continuous_pi fun p => (continuous_adm j).comp (continuous_apply p)
      continuous_invFun := continuous_pi fun p => (continuous_adm j.symm).comp (continuous_apply p) }
  let e : ratN F a r ≃ ratN E a r :=
    { toFun := fun y => ⟨β.symm y, mem_ratN j.symm y.2⟩
      invFun := fun x => ⟨β x, mem_ratN j x.2⟩
      left_inv := fun y => Subtype.ext (β.apply_symm_apply y)
      right_inv := fun x => Subtype.ext (β.symm_apply_apply x) }
  borelize (BlockIx a r → Ad F)
  let m := β.toHomeomorph.toMeasurableEquiv
  have h2 := hφ r h0 h1 (μ.map m) (m '' 𝓕) (β.isAddHaarMeasure_map μ)
    (hF.image_of_equiv m.toEquiv (MeasurePreserving.symm m ⟨m.measurable, rfl⟩).quasiMeasurePreserving e fun y x => by
      change β (β.symm y + x) = y + β x
      rw [map_add, β.apply_symm_apply]) (gaMap a j g)
  rw [m.measurableEmbedding.setIntegral_map, m.injective.preimage_image] at h2
  rw [← h2]
  congr 1
  funext x
  beta_reduce
  rw [map_mul, gaMap_unip]
  rfl

def pullSub (π : CuspSub F a) : CuspSub E a where
  V := π.V.map (pull a j).toLinearMap
  cusp := by rintro _ ⟨φ, hφ, rfl⟩; exact ⟨isAutForm_pull j (π.cusp φ hφ).1, isCuspidal_pull j (π.cusp φ hφ).2⟩
  stable := by
    rintro o _ ⟨φ, hφ, rfl⟩
    exact ⟨_, π.stable _ φ hφ, (act_pull j o φ).symm⟩
  ne_bot h := π.ne_bot ((Submodule.map_eq_bot_iff (e := pull a j)).1 h)
  irred W hW hs := by
    have h := π.irred (W.comap (pull a j).toLinearMap) (fun φ hφ => by
      obtain ⟨ψ, h1, h2⟩ := hW hφ
      rwa [← (pull a j).injective h2]) fun o φ hφ => by
      change pull a j (act o φ) ∈ W
      rw [pull_act]
      exact hs _ _ hφ
    have e := Submodule.map_comap_eq_of_surjective (f := (pull a j).toLinearMap) (pull a j).surjective W
    exact h.imp (fun h => by rw [← e, h, Submodule.map_bot]) fun h => by rw [← e, h]

theorem hasInfChar_pullSub (π : CuspSub F a) (τ : F →+* ℂ) (m : Multiset ℂ) :
    (pullSub j π).HasInfChar (τ.comp (j : E →+* F)) m ↔ π.HasInfChar τ m := by
  refine and_congr_right fun _ => forall_congr' fun u => ⟨fun h φ hφ => (pull a j).injective ?_, ?_⟩
  · rw [← cap_pull, map_smul]
    exact h _ ⟨φ, hφ, rfl⟩
  · rintro h _ ⟨φ, hφ, rfl⟩
    change cap _ u (pull a j φ) = _ • pull a j φ
    rw [cap_pull, h φ hφ, map_smul]

theorem isRegAlg_pullSub {π : CuspSub F a} (h : (CG.mk π).IsRegAlg) : (CG.mk (pullSub j π)).IsRegAlg := by
  rw [CG.isRegAlg_iff] at h ⊢
  intro τ
  obtain ⟨σ, rfl⟩ := exists_comp j τ
  have e : (CG.mk (pullSub j π)).infChar (σ.comp (j : E →+* F)) = (CG.mk π).infChar σ := by
    by_cases h1 : ∃ m, (CG.mk π).HasInfChar σ m
    · obtain ⟨m, hm⟩ := h1
      rw [hm.infChar_eq]
      exact CG.HasInfChar.infChar_eq (π := CG.mk (pullSub j π)) ((hasInfChar_pullSub j π σ m).2 hm)
    · rw [CG.infChar, CG.infChar, dif_neg h1, dif_neg]
      rintro ⟨m, hm⟩
      exact h1 ⟨m, (hasInfChar_pullSub j π σ m).1 hm⟩
  rw [e]
  exact h σ

section Sat

open GlobalTheory.LFun GlobalTheory.LFun.ConjPlace Formalism.UG GlobalTheory.PRep

section Doset

variable {K K' : Type} [Field K] [Field K'] (c : K ≃+* K') {O : Subring K} {O' : Subring K'}
  (hO : ∀ x, c x ∈ O' ↔ x ∈ O)

include hO in
theorem mem_iff_mapEquiv (g : GL (Fin a) K) :
    g ∈ GLint (Fin a) O ↔ Units.mapEquiv c.mapMatrix.toMulEquiv g ∈ GLint (Fin a) O' := by
  rw [GlobalTheory.AdelicU.mem_GLint_iff, GlobalTheory.AdelicU.mem_GLint_iff]
  exact (and_congr (forall₂_congr fun _ _ => hO _) (forall₂_congr fun _ _ => hO _)).symm

theorem mapEquiv_dGL (ϖ : Kˣ) (i : ℕ) :
    Units.mapEquiv c.mapMatrix.toMulEquiv (dGL a ϖ i) = dGL a (Units.map (c : K →* K') ϖ) i :=
  Units.ext (Matrix.ext fun p q => by
    change c ((dGL a ϖ i).1 p q) = _
    simp only [dGL, diagJ, Matrix.diagonal_apply]
    split_ifs <;> simp)

include hO in
theorem Tj_mapEquiv (ϖ : Kˣ) (i : ℕ) (g : GL (Fin a) K) :
    Tj ℂ a O' (c ϖ) i (Units.mapEquiv c.mapMatrix.toMulEquiv g) = Tj ℂ a O ϖ i g := by
  classical
  have hK := mem_iff_mapEquiv (a := a) c hO
  refine (Tj_apply O' (Units.map (c : K →* K') ϖ) i _).trans ?_
  rw [Tj_apply, ← mapEquiv_dGL]
  generalize (Units.mapEquiv c.mapMatrix.toMulEquiv : GL (Fin a) K ≃* GL (Fin a) K') = e at hK ⊢
  refine if_congr ⟨?_, ?_⟩ rfl rfl
  · rintro ⟨x, hx, y, hy, H⟩
    obtain ⟨x, rfl⟩ := e.surjective x
    obtain ⟨y, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, e.apply_eq_iff_eq] at H
    exact ⟨x, (hK x).2 hx, y, (hK y).2 hy, H⟩
  · rintro ⟨x, hx, y, hy, H⟩
    exact ⟨_, (hK x).1 hx, _, (hK y).1 hy, by rw [H, map_mul, map_mul]⟩

end Doset

omit [IsTotallyComplex E] [IsTotallyComplex F] in
theorem hasSatGL_of_equiv {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}
    (c : v.adicCompletion F ≃+* w.adicCompletion E) (hc : ∀ x, Valued.v (c x) = Valued.v x)
    (hq : qV E w = qV F v) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GL (Fin a) (v.adicCompletion F)) V} {ρ' : Representation ℂ (GL (Fin a) (w.adicCompletion E)) W}
    (T : V ≃ₗ[ℂ] W) (hT : ∀ g x, ρ' (Units.mapEquiv c.mapMatrix.toMulEquiv g) (T x) = T (ρ g x)) {B : Multiset ℂˣ}
    (h : HasSatGL v ρ B) : HasSatGL w ρ' B := by
  set e : GL (Fin a) (v.adicCompletion F) ≃* GL (Fin a) (w.adicCompletion E) := Units.mapEquiv c.mapMatrix.toMulEquiv
  have hO : ∀ x, c x ∈ Ov E w ↔ x ∈ Ov F v := fun x => by
    change Valued.v (c x) ≤ 1 ↔ Valued.v x ≤ 1
    rw [hc]
  have hK : ∀ g, g ∈ KGL v a ↔ e g ∈ KGL w a := mem_iff_mapEquiv c hO
  have hTj : ∀ (ϖ : (v.adicCompletion F)ˣ) (i : ℕ) g, Tj ℂ a (Ov E w) (c ϖ) i (e g) = Tj ℂ a (Ov F v) ϖ i g :=
    Tj_mapEquiv c hO
  clear_value e
  have h1 : ∀ x, IsSatVecGL v ρ x B → IsSatVecGL w (ρ.comp e.symm.toMonoidHom) x B := by
    rintro x ⟨h0, hf, hB, hT⟩
    refine ⟨h0, (mem_fixed_comp_symm _ hK).2 hf, hB, fun ϖ' hϖ' i hi => ?_⟩
    obtain ⟨p, rfl⟩ := c.surjective ϖ'
    have hp : IsUnifV F v p := (hc p).symm.trans hϖ'
    obtain ⟨ϖ, rfl⟩ : ∃ ϖ : (v.adicCompletion F)ˣ, ϖ = p :=
      ⟨Units.mk0 p fun e => by simp [IsUnifV, e] at hp, rfl⟩
    rw [heckeVec_comp_symm _ hK (Tj_mem_hecke hϖ' i).1 hf, hq, ← hT _ hp i hi]
    congr 1
    exact funext (hTj ϖ i)
  have hf : ∀ g y, T.toLinearMap ((ρ.comp e.symm.toMonoidHom) g y) = ρ' g (T.toLinearMap y) := fun g y => by
    change T (ρ (e.symm g) y) = ρ' g (T y)
    rw [← hT, MulEquiv.apply_symm_apply]
  have key : ∀ x, IsSatVecGL v ρ x B → IsSatVecGL w ρ' (T x) B := fun x hx =>
    (h1 x hx).map T.toLinearMap hf ((map_ne_zero_iff T T.injective).2 hx.1)
  constructor
  · obtain ⟨x, hx⟩ := h.exists_vec
    exact (Submodule.ne_bot_iff _).2 ⟨_, (key x hx).2.1, (key x hx).1⟩
  · intro y hy h0
    obtain ⟨x, rfl⟩ := T.surjective y
    refine key x (h.2 x (GlobalTheory.LGrp.mem_fixed.2 fun k hk => T.injective ?_) ((map_ne_zero_iff T T.injective).1 h0))
    have := GlobalTheory.LGrp.mem_fixed.1 hy _ ((hK k).1 hk)
    rwa [hT] at this

end Sat

open scoped WithZeroTopology in
omit [IsTotallyComplex E] [IsTotallyComplex F] in
theorem valued_compEquiv (w : HeightOneSpectrum (𝓞 E)) (x : w.adicCompletion E) :
    Valued.v (compEquiv j w x) = Valued.v x := by
  refine (HeightOneSpectrum.denseRange_algebraMap E w).induction_on
    (p := fun x => Valued.v (compEquiv j w x) = Valued.v x) x
    (isClosed_eq ((Valued.continuous_valuation_of_surjective ((plMap j w).valuedAdicCompletion_surjective F)).comp
      (continuous_compEquiv j w))
      (Valued.continuous_valuation_of_surjective (w.valuedAdicCompletion_surjective E))) fun k => ?_
  rw [compEquiv_algebraMap]
  exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' _ _).trans
    ((valuation_plMap j w k).trans (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _).symm)

omit [IsTotallyComplex E] [IsTotallyComplex F] in
theorem finMap_locGL (v : HeightOneSpectrum (𝓞 F)) (g : GL (Fin a) (v.adicCompletion F)) :
    GeneralLinearGroup.map (finMap j)
      (locGL E a (plMap j.symm v) (Units.mapEquiv (compEquiv j.symm v).mapMatrix.toMulEquiv g)) = locGL F a v g := by
  have key : ∀ u (k : GL (Fin a) (Af E)), GeneralLinearGroup.map (pLoc F u) (GeneralLinearGroup.map (finMap j) k) =
      GeneralLinearGroup.map (compEquiv j.symm u).symm.toRingHom
        (GeneralLinearGroup.map (pLoc E (plMap j.symm u)) k) := fun u k => rfl
  have key2 : ∀ u, GeneralLinearGroup.map (pLoc F u) (GeneralLinearGroup.map (finMap j)
      (locGL E a (plMap j.symm v) (Units.mapEquiv (compEquiv j.symm v).mapMatrix.toMulEquiv g))) =
      GeneralLinearGroup.map (pLoc F u) (locGL F a v g) := fun u => by
    rw [key]
    by_cases h : u = v
    · subst h
      rw [pLoc_locGL, pLoc_locGL]
      exact Units.ext (Matrix.ext fun _ _ => (compEquiv j.symm u).symm_apply_apply _)
    · rw [pLoc_locGL_of_ne h, pLoc_locGL_of_ne (fun e => h (plMap_injective _ e)), map_one]
  refine Units.ext (Matrix.ext fun i k => FiniteAdeleRing.ext _ fun u => ?_)
  exact congrArg (fun x : GL (Fin a) (u.adicCompletion F) => x.val i k) (key2 u)

theorem hasSat_pullSub {π : CuspSub F a} {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ}
    (h : (CG.mk π).HasSat (plMap j w) B) : (CG.mk (pullSub j π)).HasSat w B := by
  obtain ⟨v, rfl⟩ : ∃ v, plMap j.symm v = w := ⟨_, plMap_symm_plMap j w⟩
  rw [plMap_plMap_symm] at h
  rw [CG.hasSat_mk] at h ⊢
  refine hasSatGL_of_equiv (compEquiv j.symm v) (valued_compEquiv j.symm v) (absNorm_plMap j.symm v)
    ((pull a j).submoduleMap π.V) (fun g x => ?_) h
  refine Subtype.ext ((act_pull j (.fin _) x.1).trans ?_)
  rw [opMap, finMap_locGL]
  rfl

end UpperTheory.V.FieldIso
