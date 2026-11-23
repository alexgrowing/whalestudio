import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemCharIdem
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv

open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.SplitWeil GlobalTheory.PRep GlobalTheory.LocGL
open scoped ComplexConjugate InnerProductSpace

noncomputable section

namespace GlobalTheory.Orb

section Algebra

variable {K Q V W : Type} [Group K] [Group Q] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {κ : Representation ℂ K V} {r : K →* Q}

theorem apply_eq_of_map_eq {v : V} (hv : v ∈ fixed κ r.ker) {a b : K} (h : r a = r b) : κ a v = κ b v := by
  have := mem_fixed.1 hv (b⁻¹ * a) (by simp [MonoidHom.mem_ker, h])
  conv_rhs => rw [← this]
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]

theorem apply_mem_fixed_ker {v : V} (hv : v ∈ fixed κ r.ker) (k : K) : κ k v ∈ fixed κ r.ker :=
  mem_fixed.2 fun n hn => by
    rw [← Module.End.mul_apply, ← map_mul]
    exact apply_eq_of_map_eq hv (by rw [map_mul, MonoidHom.mem_ker.1 hn, one_mul])

variable (κ) in

def kerRep (hr : Function.Surjective r) : Representation ℂ Q (fixed κ r.ker) where
  toFun q := (κ (Function.surjInv hr q)).restrict fun _ hv => apply_mem_fixed_ker hv _
  map_one' := LinearMap.ext fun v => Subtype.ext <|
    (apply_eq_of_map_eq v.2 (b := 1) (by rw [Function.surjInv_eq hr, map_one])).trans (by simp)
  map_mul' a b := LinearMap.ext fun v => Subtype.ext <|
    (apply_eq_of_map_eq v.2 (b := Function.surjInv hr a * Function.surjInv hr b)
      (by simp only [Function.surjInv_eq hr, map_mul])).trans (by rw [map_mul]; rfl)

theorem kerRep_apply (hr : Function.Surjective r) (k : K) (x : fixed κ r.ker) :
    (kerRep κ hr (r k) x : V) = κ k x :=
  apply_eq_of_map_eq x.2 (Function.surjInv_eq hr _)

theorem proj_of_charIdem [Fintype Q] [FiniteDimensional ℂ W] (hr : Function.Surjective r)
    {τ : Representation ℂ Q W} (hτ : τ.IsIrreducible) {A P : V →ₗ[ℂ] V} (h1 : ∀ v, A v ∈ fixed κ r.ker)
    (h2 : ∀ v ∈ fixed κ r.ker, A v = v) (h3 : ∀ k v, A (κ k v) = κ k (A v))
    (hP : ∀ v, P v = (charIdem (kerRep κ hr) τ ⟨A v, h1 v⟩ : V)) :
    (∀ k, P ∘ₗ κ k = κ k ∘ₗ P) ∧ P ∘ₗ P = P ∧
      LinearMap.range P = (isotypic κ (τ.comp r)).toSubmodule ∧
      (P ≠ 0 ↔ ∃ f : Representation.IntertwiningMap (τ.comp r) κ, f ≠ 0) := by
  have hx : ∀ x : fixed κ r.ker, P x = (charIdem (kerRep κ hr) τ x : V) := fun x => by
    rw [hP]
    congr 2
    exact Subtype.ext (h2 _ x.2)
  have hR : LinearMap.range P = (isotypic κ (τ.comp r)).toSubmodule := by
    refine le_antisymm ?_ (iSup_le fun f => ?_)
    · rintro _ ⟨v, rfl⟩
      rw [hP]
      refine Submodule.iSup_induction _ (motive := fun y : fixed κ r.ker => (y : V) ∈ (isotypic κ (τ.comp r)).toSubmodule)
        (charIdem_mem (kerRep κ hr) τ ⟨A v, h1 v⟩) ?_ (zero_mem _) fun x y hx hy => add_mem hx hy
      rintro f _ ⟨w, rfl⟩
      exact apply_mem_isotypic (σ := κ) (τ := τ.comp r) ⟨(fixed κ r.ker).subtype ∘ₗ f.toLinearMap, fun k =>
        LinearMap.ext fun w => (congrArg Subtype.val (f.isIntertwining _ _ (r k) w)).trans (kerRep_apply hr k _)⟩ w
    · rintro _ ⟨w, rfl⟩
      have hf : ∀ w, f w ∈ fixed κ r.ker := fun w => mem_fixed.2 fun n hn => by
        rw [← f.isIntertwining]
        simp [MonoidHom.mem_ker.1 hn]
      let f' : τ.IntertwiningMap (kerRep κ hr) := ⟨f.toLinearMap.codRestrict _ hf, fun q => LinearMap.ext fun w => by
        obtain ⟨k, rfl⟩ := hr q
        exact Subtype.ext ((f.isIntertwining _ _ k w).trans (kerRep_apply hr k ⟨_, hf w⟩).symm)⟩
      exact ⟨f w, (hx (f' w)).trans (congrArg Subtype.val (charIdem_of_mem hτ (apply_mem_isotypic f' w)))⟩
  refine ⟨fun k => LinearMap.ext fun v => ?_, LinearMap.ext fun v => ?_, hR, ?_⟩
  · have e : (⟨A (κ k v), h1 _⟩ : fixed κ r.ker) = kerRep κ hr (r k) ⟨A v, h1 v⟩ :=
      Subtype.ext ((h3 k v).trans (kerRep_apply hr k ⟨_, h1 v⟩).symm)
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hP, hP, e, charIdem_apply_rep, kerRep_apply]
  · rw [LinearMap.comp_apply, hP v, hx, charIdem_of_mem hτ (charIdem_mem _ _ _)]
  · rw [← isotypic_ne_bot_iff, Ne, ← LinearMap.range_eq_bot, hR]
    exact not_congr (Subrepresentation.toSubmodule_injective.eq_iff (b := ⊥))

theorem sum_character_mul [Fintype Q] [FiniteDimensional ℂ W] {τ : Representation ℂ Q W} (hτ : τ.IsIrreducible)
    (h : Q) : ((Module.finrank ℂ W : ℂ) / Fintype.card Q) * ∑ q, τ.character q * τ.character (q⁻¹ * h) =
      τ.character h := by
  have := congrArg (fun T => LinearMap.trace ℂ W (T * τ h)) (charIdem_self hτ)
  simp only [charIdem, smul_mul_assoc, Finset.sum_mul, map_smul, map_sum, one_mul, ← map_mul, smul_eq_mul] at this
  rw [Representation.character, ← this]
  congr 1
  exact Fintype.sum_equiv (Equiv.inv Q) _ _ fun q => by simp [Representation.character]

end Algebra

section Integral

variable {G Q : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [Group Q] (μ : Measure G) [μ.IsHaarMeasure] {K : Subgroup G} (ho : IsOpen (K : Set G)) (hc : IsCompact (K : Set G))
  {F : G → ℂ}

omit [IsTopologicalGroup G] [μ.IsHaarMeasure] in
include ho in

theorem integral_eq_subgroup (h0 : ∀ g ∉ K, F g = 0) : ∫ g, F g ∂μ = ∫ k : K, F k ∂(μ.comap K.subtype) :=
  (setIntegral_eq_integral_of_forall_compl_eq_zero (s := (K : Set G)) h0).symm.trans
    (integral_subtype_comap ho.measurableSet F).symm

include ho hc

theorem integral_mul_right_of_compact (h0 : ∀ g ∉ K, F g = 0) (k : K) : ∫ g, F (g * k) ∂μ = ∫ g, F g ∂μ := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hc
  haveI : (μ.comap K.subtype).IsHaarMeasure := .comap (mH := inferInstance) μ ho.isOpenEmbedding_subtypeVal
  haveI := GlobalTheory.isMulRightInvariant_of_compactSpace (μ.comap K.subtype)
  rw [integral_eq_subgroup μ ho h0,
    integral_eq_subgroup μ ho fun g hg => h0 _ (by rwa [K.mul_mem_cancel_right k.2])]
  exact integral_mul_right_eq_self (fun x : K => F x) k

theorem integral_inv_of_compact (h0 : ∀ g ∉ K, F g = 0) : ∫ g, F g⁻¹ ∂μ = ∫ g, F g ∂μ := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hc
  haveI : (μ.comap K.subtype).IsHaarMeasure := .comap (mH := inferInstance) μ ho.isOpenEmbedding_subtypeVal
  haveI := GlobalTheory.isInvInvariant_of_compactSpace (μ.comap K.subtype)
  rw [integral_eq_subgroup μ ho h0, integral_eq_subgroup μ ho fun g hg => h0 _ (by rwa [K.inv_mem_iff])]
  exact integral_inv_eq_self (fun x : K => F x) _

omit [μ.IsHaarMeasure] ho hc in

def kerSet (r : K →* Q) : Set G := (↑) '' (r.ker : Set K)

variable {r : K →* Q} (hr : Function.Surjective r) (hk : IsOpen (r.ker : Set K))

omit [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] ho hc in

theorem coe_mem_kerSet {k : K} : (k : G) ∈ kerSet r ↔ r k = 1 := Subtype.val_injective.mem_set_image

omit [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] hc in
include hk in

theorem isOpen_kerSet : IsOpen (kerSet r) := ho.isOpenMap_subtype_val _ hk

omit [MeasurableSpace G] [BorelSpace G] ho in
include hk in

theorem isCompact_kerSet : IsCompact (kerSet r) :=
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hc
  (r.ker.isClosed_of_isOpen hk).isCompact.image continuous_subtype_val

omit hc in
include hk in

theorem integral_eq_sum_ker [Fintype Q] (hF : Integrable F μ) (h0 : ∀ g ∉ K, F g = 0) :
    ∫ g, F g ∂μ = ∑ q, ∫ x in kerSet r, F ((Function.surjInv hr q : K) * x) ∂μ := by
  classical
  have hm := (isOpen_kerSet ho hk).measurableSet
  have e : ∀ g, F g = ∑ q, ((((Function.surjInv hr q : K) : G)⁻¹ * ·) ⁻¹' kerSet r).indicator F g := fun g => by
    by_cases hg : g ∈ K
    · have : ∀ q, g ∈ (((Function.surjInv hr q : K) : G)⁻¹ * ·) ⁻¹' kerSet r ↔ q = r ⟨g, hg⟩ := fun q => by
        refine (coe_mem_kerSet (r := r) (k := (Function.surjInv hr q)⁻¹ * ⟨g, hg⟩)).trans ?_
        rw [map_mul, map_inv, Function.surjInv_eq hr, inv_mul_eq_one]
      simp only [indicator_apply, this, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    · simp [indicator_apply, h0 g hg]
  rw [integral_congr_ae (.of_forall e), integral_finset_sum _ fun q _ => hF.indicator (hm.preimage (by fun_prop))]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← integral_mul_left_eq_self _ ((Function.surjInv hr q : K) : G), ← integral_indicator hm]
  refine integral_congr_ae (.of_forall fun x => ?_)
  simp [indicator_apply]

include hr hk in

theorem real_eq_card_mul [Fintype Q] : (μ.real K : ℂ) = Fintype.card Q * μ.real (kerSet r) := by
  have h := integral_eq_sum_ker μ ho hr hk (F := (K : Set G).indicator fun _ => 1)
    ((integrable_indicator_iff ho.measurableSet).2 (integrableOn_const hc.measure_ne_top))
    fun g hg => indicator_of_notMem hg _
  have e : ∀ q, ∫ x in kerSet r, (K : Set G).indicator (fun _ => (1 : ℂ)) (Function.surjInv hr q * x) ∂μ =
      μ.real (kerSet r) := fun q => by
    rw [setIntegral_congr_fun (g := fun _ => 1) (isOpen_kerSet ho hk).measurableSet]
    · simp
    · rintro _ ⟨k, -, rfl⟩
      exact indicator_of_mem (K.mul_mem (Subtype.prop _) k.2) _
  simpa [e, integral_indicator ho.measurableSet] using h

include hk in

theorem real_kerSet_ne_zero : (μ.real (kerSet r) : ℂ) ≠ 0 := by
  exact_mod_cast ENNReal.toReal_ne_zero.2 ⟨((isOpen_kerSet ho hk).measure_pos μ ⟨1, 1, one_mem _, rfl⟩).ne',
    (isCompact_kerSet hc hk).measure_ne_top⟩

variable {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (τ : Representation ℂ Q W)

include hr hk in

theorem typeIdem_mul_real [Fintype Q] (k : K) : typeIdem μ r τ k * μ.real (kerSet r) =
    (Module.finrank ℂ W : ℂ) / Fintype.card Q * conj (τ.character (r k)) := by
  have := real_kerSet_ne_zero μ ho hc hk
  rw [typeIdem_coe, real_eq_card_mul μ ho hc hr hk]
  field_simp

include hr hk in

theorem conv_typeIdem [Finite Q] (hτ : τ.IsIrreducible) :
    conv μ (typeIdem μ r τ) (typeIdem μ r τ) = typeIdem μ r τ := by
  have := Fintype.ofFinite Q
  have he := typeIdem_mem_SB μ r τ ho hc hk
  funext y
  by_cases hy : y ∈ K
  · lift y to K using hy
    rw [conv, integral_eq_sum_ker μ ho hr hk (F := fun x => typeIdem μ r τ x * typeIdem μ r τ (x⁻¹ * y))
      ((he.1.continuous.mul (he.1.continuous.comp (by fun_prop))).integrable_of_hasCompactSupport he.2.mul_right)
      fun g hg => by rw [typeIdem_of_notMem μ r τ hg, zero_mul]]
    have e : ∀ q, ∫ x in kerSet r, typeIdem μ r τ (((Function.surjInv hr q : K) : G) * x) *
        typeIdem μ r τ ((((Function.surjInv hr q : K) : G) * x)⁻¹ * y) ∂μ = (Module.finrank ℂ W : ℂ) * (μ.real K : ℂ)⁻¹ *
          conj ((Module.finrank ℂ W : ℂ) / Fintype.card Q * (τ.character q * τ.character (q⁻¹ * r y))) := fun q => by
      rw [setIntegral_congr_fun (g := fun _ => typeIdem μ r τ (Function.surjInv hr q : K) *
        typeIdem μ r τ ((Function.surjInv hr q)⁻¹ * y : K)) (isOpen_kerSet ho hk).measurableSet]
      · rw [setIntegral_const, Complex.real_smul, ← mul_assoc, mul_comm (μ.real _ : ℂ),
          typeIdem_mul_real μ ho hc hr hk, typeIdem_coe, map_mul r, map_inv, Function.surjInv_eq hr]
        simp only [map_mul, map_div₀, map_natCast]
        ring
      · rintro _ ⟨k, hk1, rfl⟩
        have h1 := (typeIdem_mul_ker μ r τ (k := k⁻¹) (inv_mem hk1) ((Function.surjInv hr q)⁻¹ * y : K)).1
        simp only
        rw [(typeIdem_mul_ker μ r τ hk1 _).2, ← h1]
        simp [mul_assoc]
    simp only [e]
    rw [← Finset.mul_sum, ← map_sum, ← Finset.mul_sum, sum_character_mul hτ, typeIdem_coe]
  · rw [typeIdem_of_notMem μ r τ hy]
    have : ∀ x, typeIdem μ r τ x * typeIdem μ r τ (x⁻¹ * y) = 0 := fun x => by
      by_cases hx : x ∈ K
      · rw [typeIdem_of_notMem μ r τ (g := x⁻¹ * y) (by rwa [K.mul_mem_cancel_left (inv_mem hx)]), mul_zero]
      · rw [typeIdem_of_notMem μ r τ hx, zero_mul]
    simp [conv, this]

omit [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] ho hc in

theorem conj_mem_kerSet (k : K) (g : G) : (k : G)⁻¹ * (g * k) ∈ kerSet r ↔ g ∈ kerSet r := by
  by_cases hg : g ∈ K
  · lift g to K using hg
    refine (coe_mem_kerSet (r := r) (k := k⁻¹ * (g * k))).trans (Iff.trans ?_ coe_mem_kerSet.symm)
    rw [map_mul, map_mul, map_inv, inv_mul_eq_one, right_eq_mul]
  · refine iff_of_false ?_ ?_
    · rintro ⟨x, -, e⟩
      have : (k : G)⁻¹ * (g * k) ∈ K := e ▸ x.2
      rw [K.mul_mem_cancel_left (inv_mem k.2), K.mul_mem_cancel_right k.2] at this
      exact hg this
    · rintro ⟨x, -, rfl⟩
      exact hg x.2

include hr hk in

theorem proj_of_weak [Finite Q] (hτ : τ.IsIrreducible) {V : Type} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} {L : Set (V →ₗ[ℂ] ℂ)} (hsep : ∀ v w, (∀ l ∈ L, l v = l w) → v = w)
    (hst : ∀ l ∈ L, ∀ g, l ∘ₗ ρ g ∈ L) (hct : ∀ l ∈ L, ∀ v, Continuous fun g => l (ρ g v)) {B P : V →ₗ[ℂ] V}
    (hB : ∀ l ∈ L, ∀ v, l (B v) = ∫ g, (kerSet r).indicator (1 : G → ℂ) g * l (ρ g v) ∂μ)
    (hP : ∀ l ∈ L, ∀ v, l (P v) = ∫ g, typeIdem μ r τ g * l (ρ g v) ∂μ) :
    (∀ k : K, P ∘ₗ ρ k = ρ k ∘ₗ P) ∧ P ∘ₗ P = P ∧
      LinearMap.range P = (isotypic (ρ.comp K.subtype) (τ.comp r)).toSubmodule ∧
      (P ≠ 0 ↔ ∃ f : Representation.IntertwiningMap (τ.comp r) (ρ.comp K.subtype), f ≠ 0) := by
  classical
  have := Fintype.ofFinite Q
  have he := typeIdem_mem_SB μ r τ ho hc hk
  have hm := (isOpen_kerSet ho hk).measurableSet
  have h0 := real_kerSet_ne_zero μ ho hc hk
  have hB' : ∀ l ∈ L, ∀ v, l (B v) = ∫ g in kerSet r, l (ρ g v) ∂μ := fun l hl v => by
    rw [hB l hl, ← integral_indicator hm]
    exact integral_congr_ae (.of_forall fun g => by simp [indicator_apply])
  have h1 : ∀ v, ((μ.real (kerSet r) : ℂ)⁻¹ • B) v ∈ fixed (ρ.comp K.subtype) r.ker := fun v => by
    refine Submodule.smul_mem _ _ (mem_fixed.2 fun n hn => hsep _ _ fun l hl => ?_)
    refine (hB _ (hst l hl n) v).trans ?_
    rw [hB l hl, ← integral_mul_left_eq_self (fun g => (kerSet r).indicator (1 : G → ℂ) g * l (ρ g v)) (n : G)]
    refine integral_congr_ae (.of_forall fun g => ?_)
    have : (n : G) * g ∈ kerSet r ↔ g ∈ kerSet r := (r.ker.map K.subtype).mul_mem_cancel_left ⟨n, hn, rfl⟩
    simp [indicator_apply, this]
  refine proj_of_charIdem (κ := ρ.comp K.subtype) hr hτ h1 (fun v hv => hsep _ _ fun l hl => ?_)
    (fun k v => hsep _ _ fun l hl => ?_) fun v => hsep _ _ fun l hl => ?_
  · rw [LinearMap.smul_apply, map_smul, hB' l hl, setIntegral_congr_fun (g := fun _ => l v) hm, setIntegral_const,
      Complex.real_smul, smul_eq_mul, inv_mul_cancel_left₀ h0]
    rintro _ ⟨k, hk1, rfl⟩
    exact congrArg l (mem_fixed.1 hv k hk1)
  · simp only [LinearMap.smul_apply, map_smul]
    congr 1
    refine (hB l hl _).trans (Eq.trans ?_ (hB _ (hst l hl k) v).symm)
    have h2 := integral_mul_right_of_compact μ ho hc
      (F := fun g => (kerSet r).indicator (1 : G → ℂ) ((k : G)⁻¹ * g) * l (ρ g v)) (fun g hg => by
        rw [indicator_of_notMem, zero_mul]
        rintro ⟨x, -, e⟩
        exact hg ((K.mul_mem_cancel_left (inv_mem k.2)).1 (e ▸ x.2))) k
    rw [← integral_mul_left_eq_self (fun g => (kerSet r).indicator (1 : G → ℂ) ((k : G)⁻¹ * g) * l (ρ g v)) (k : G)]
      at h2
    simpa [indicator_apply, conj_mem_kerSet] using h2
  · rw [hP l hl, integral_eq_sum_ker μ ho hr hk (F := fun g => typeIdem μ r τ g * l (ρ g v))
      ((he.1.continuous.mul (hct l hl v)).integrable_of_hasCompactSupport he.2.mul_right)
      fun g hg => by rw [typeIdem_of_notMem μ r τ hg, zero_mul], charIdem_apply]
    simp only [Submodule.coe_smul, Submodule.coe_sum, map_smul, map_sum, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    have e1 : l (kerRep (ρ.comp K.subtype) hr q ⟨_, h1 v⟩ : V) =
        (μ.real (kerSet r) : ℂ)⁻¹ * ∫ g in kerSet r, l (ρ (Function.surjInv hr q : K) (ρ g v)) ∂μ := by
      refine Eq.trans ?_ (congrArg _ (hB' _ (hst l hl (Function.surjInv hr q : K)) v))
      exact (l ∘ₗ ρ (Function.surjInv hr q : K)).map_smul _ _
    have e2 := typeIdem_mul_real μ ho hc hr hk τ (Function.surjInv hr q)
    have e3 : LinearMap.trace ℂ W (τ q⁻¹) = conj (τ.character q) := GlobalTheory.BadShare.ZCalc.character_inv (FDRep.of τ) q
    rw [Function.surjInv_eq hr] at e2
    rw [e1, e3, ← mul_assoc, ← e2, mul_assoc, mul_inv_cancel_left₀ h0, ← integral_const_mul]
    refine setIntegral_congr_fun hm ?_
    rintro _ ⟨k, hk1, rfl⟩
    simp only
    rw [(typeIdem_mul_ker μ r τ hk1 _).2, map_mul, Module.End.mul_apply]

include hr hk in

theorem smoothOp_typeIdem [T2Space G] [Finite Q] (hτ : τ.IsIrreducible) {V : Type} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) :
    (∀ k : K, smoothOp ρ μ (typeIdem μ r τ) ∘ₗ ρ k = ρ k ∘ₗ smoothOp ρ μ (typeIdem μ r τ)) ∧
      smoothOp ρ μ (typeIdem μ r τ) ∘ₗ smoothOp ρ μ (typeIdem μ r τ) = smoothOp ρ μ (typeIdem μ r τ) ∧
      LinearMap.range (smoothOp ρ μ (typeIdem μ r τ)) = (isotypic (ρ.comp K.subtype) (τ.comp r)).toSubmodule ∧
      (smoothOp ρ μ (typeIdem μ r τ) ≠ 0 ↔
        ∃ f : Representation.IntertwiningMap (τ.comp r) (ρ.comp K.subtype), f ≠ 0) := by
  have he := typeIdem_mem_SB μ r τ ho hc hk
  have hb := indicator_mem_SB (isOpen_kerSet ho hk) (isCompact_kerSet hc hk)
  exact proj_of_weak μ ho hc hr hk τ hτ (L := univ) (fun v w h => eq_of_forall_dual fun l => h l trivial)
    (fun _ _ _ => trivial) (fun l _ v => ((hρ.isLocallyConstant_orbit v).comp l).continuous)
    (fun l _ v => hρ.map_smoothOp hb.1 hb.2 l v) fun l _ v => hρ.map_smoothOp he.1 he.2 l v

omit [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] ho hc in

def linRep {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] (π : G →* (H →L[ℂ] H)) : Representation ℂ G H :=
  ContinuousLinearMap.toLinearMapRingHom.toMonoidHom.comp π

omit [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] ho hc in

@[simp] theorem linRep_apply {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] (π : G →* (H →L[ℂ] H)) (g : G)
    (v : H) : linRep π g v = π g v := rfl

include hr hk in

theorem repOp_typeIdem [T2Space G] [Finite Q] (hτ : τ.IsIrreducible) {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {π : G →* (H →L[ℂ] H)} (hπ : IsUnitaryRep π) :
    (∀ k : K, repOp π μ (typeIdem μ r τ) ∘L π k = π k ∘L repOp π μ (typeIdem μ r τ)) ∧
      repOp π μ (typeIdem μ r τ) ∘L repOp π μ (typeIdem μ r τ) = repOp π μ (typeIdem μ r τ) ∧
      IsSelfAdjoint (repOp π μ (typeIdem μ r τ)) ∧
      LinearMap.range (repOp π μ (typeIdem μ r τ)).toLinearMap =
        (isotypic ((linRep π).comp K.subtype) (τ.comp r)).toSubmodule ∧
      (repOp π μ (typeIdem μ r τ) ≠ 0 ↔
        ∃ f : Representation.IntertwiningMap (τ.comp r) ((linRep π).comp K.subtype), f ≠ 0) := by
  have he := typeIdem_mem_SB μ r τ ho hc hk
  have hb := indicator_mem_SB (isOpen_kerSet ho hk) (isCompact_kerSet hc hk)
  have hw : ∀ {f : G → ℂ}, f ∈ SB G → ∀ l ∈ {l : H →ₗ[ℂ] ℂ | Continuous l}, ∀ v,
      l ((repOp π μ f).toLinearMap v) = ∫ g, f g * l (linRep π g v) ∂μ := fun {f} hf l hl v => by
    have := (⟨l, hl⟩ : H →L[ℂ] ℂ).integral_comp_comm (hπ.isRepOp (μ := μ) hf.1.continuous hf.2 v).1
    rw [← hπ.repOp_apply hf.1.continuous hf.2] at this
    simpa using this.symm
  obtain ⟨h1, h2, h3, h4⟩ := proj_of_weak μ ho hc hr hk τ hτ (ρ := linRep π) (L := {l | Continuous l})
    (fun v w h => ext_inner_left ℂ fun u => h (innerSL ℂ u).toLinearMap (innerSL ℂ u).continuous)
    (fun l hl g => Continuous.comp (g := l) hl (π g).continuous) (fun l hl v => Continuous.comp hl (hπ.continuous_apply v))
    (hw hb) (hw he)
  refine ⟨fun k => ContinuousLinearMap.coe_injective (h1 k), ContinuousLinearMap.coe_injective h2, ?_, h3,
    (ContinuousLinearMap.coe_injective.ne_iff (y := 0)).symm.trans h4⟩
  refine ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.2 fun v w => ?_
  have e : ∀ g, conj (typeIdem μ r τ g⁻¹) = typeIdem μ r τ g := congrFun (starFn_typeIdem μ r τ)
  rw [ContinuousLinearMap.coe_coe, ← inner_conj_symm, hπ.inner_repOp he.1.continuous he.2,
    hπ.inner_repOp he.1.continuous he.2, ← integral_conj, ← integral_inv_of_compact μ ho hc
      fun g hg => by rw [typeIdem_of_notMem μ r τ hg, zero_mul, map_zero]]
  refine integral_congr_ae (.of_forall fun g => ?_)
  simp only
  rw [map_mul, e, inner_conj_symm, hπ.inner_apply_left, inv_inv]

end Integral

theorem typeIdem_projector {G Q W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] {K : Subgroup G} (ho : IsOpen (K : Set G))
    (hc : IsCompact (K : Set G)) [Group Q] [Finite Q] {r : K →* Q} (hr : Function.Surjective r)
    (hk : IsOpen (r.ker : Set K)) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] {τ : Representation ℂ Q W}
    (hτ : τ.IsIrreducible) :
    conv μ (typeIdem μ r τ) (typeIdem μ r τ) = typeIdem μ r τ ∧
    (∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), IsSmooth ρ →
      (∀ k : K, smoothOp ρ μ (typeIdem μ r τ) ∘ₗ ρ k = ρ k ∘ₗ smoothOp ρ μ (typeIdem μ r τ)) ∧
      smoothOp ρ μ (typeIdem μ r τ) ∘ₗ smoothOp ρ μ (typeIdem μ r τ) = smoothOp ρ μ (typeIdem μ r τ) ∧
      LinearMap.range (smoothOp ρ μ (typeIdem μ r τ)) =
        (isotypic (ρ.comp K.subtype) (τ.comp r)).toSubmodule ∧
      (smoothOp ρ μ (typeIdem μ r τ) ≠ 0 ↔
        ∃ f : Representation.IntertwiningMap (τ.comp r) (ρ.comp K.subtype), f ≠ 0)) ∧
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : G →* (H →L[ℂ] H)),
      IsUnitaryRep π →
      (∀ k : K, repOp π μ (typeIdem μ r τ) ∘L π k = π k ∘L repOp π μ (typeIdem μ r τ)) ∧
      repOp π μ (typeIdem μ r τ) ∘L repOp π μ (typeIdem μ r τ) = repOp π μ (typeIdem μ r τ) ∧
      IsSelfAdjoint (repOp π μ (typeIdem μ r τ)) ∧
      LinearMap.range (repOp π μ (typeIdem μ r τ)).toLinearMap =
        (isotypic ((linRep π).comp K.subtype) (τ.comp r)).toSubmodule ∧
      (repOp π μ (typeIdem μ r τ) ≠ 0 ↔
        ∃ f : Representation.IntertwiningMap (τ.comp r) ((linRep π).comp K.subtype), f ≠ 0) :=
  ⟨conv_typeIdem μ ho hc hr hk τ hτ, fun _ _ _ _ hρ => smoothOp_typeIdem μ ho hc hr hk τ hτ hρ,
    fun _ _ _ _ _ hπ => repOp_typeIdem μ ho hc hr hk τ hτ hπ⟩

namespace SplitAt

open NumberField IsDedekindDomain GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)} [Submodule.IsLattice E L]
  {v : HeightOneSpectrum (𝓞 F)} (s : SplitAt σ J L v)

theorem isOpen_ker_red : IsOpen (s.red.ker : Set (stabLoc σ J L v)) := by
  rw [show (s.red.ker : Set (stabLoc σ J L v)) = (↑) ⁻¹' (stabLocOne σ J s.emb L : Set (GLoc σ J v)) from
    Set.ext s.red_eq_one_iff]
  exact (isOpen_stabLocOne J s.emb L s.cm).preimage continuous_subtype_val

theorem idem_projector (μ : Measure (GLoc σ J v)) [μ.IsHaarMeasure] {W : Type} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] {τ : Representation ℂ (GL (Fin n) (ResF v)) W} (hτ : τ.IsIrreducible) :
    conv μ (s.idem μ τ) (s.idem μ τ) = s.idem μ τ ∧
    (∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GLoc σ J v) V), IsSmooth ρ →
      (∀ k : stabLoc σ J L v, smoothOp ρ μ (s.idem μ τ) ∘ₗ ρ k = ρ k ∘ₗ smoothOp ρ μ (s.idem μ τ)) ∧
      smoothOp ρ μ (s.idem μ τ) ∘ₗ smoothOp ρ μ (s.idem μ τ) = smoothOp ρ μ (s.idem μ τ) ∧
      LinearMap.range (smoothOp ρ μ (s.idem μ τ)) =
        (isotypic (ρ.comp (stabLoc σ J L v).subtype) (τ.comp s.red)).toSubmodule ∧
      (smoothOp ρ μ (s.idem μ τ) ≠ 0 ↔
        ∃ f : Representation.IntertwiningMap (τ.comp s.red) (ρ.comp (stabLoc σ J L v).subtype), f ≠ 0)) ∧
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : (GLoc σ J v) →* (H →L[ℂ] H)),
      IsUnitaryRep π →
      (∀ k : stabLoc σ J L v, repOp π μ (s.idem μ τ) ∘L π k = π k ∘L repOp π μ (s.idem μ τ)) ∧
      repOp π μ (s.idem μ τ) ∘L repOp π μ (s.idem μ τ) = repOp π μ (s.idem μ τ) ∧
      IsSelfAdjoint (repOp π μ (s.idem μ τ)) ∧
      LinearMap.range (repOp π μ (s.idem μ τ)).toLinearMap =
        (isotypic ((linRep π).comp (stabLoc σ J L v).subtype) (τ.comp s.red)).toSubmodule ∧
      (repOp π μ (s.idem μ τ) ≠ 0 ↔
        ∃ f : Representation.IntertwiningMap (τ.comp s.red) ((linRep π).comp (stabLoc σ J L v).subtype), f ≠ 0) :=
  typeIdem_projector μ (isOpen_stabLoc σ J L v) (isCompact_stabLoc σ J L v) s.red_surjective s.isOpen_ker_red hτ

end SplitAt

end GlobalTheory.Orb
