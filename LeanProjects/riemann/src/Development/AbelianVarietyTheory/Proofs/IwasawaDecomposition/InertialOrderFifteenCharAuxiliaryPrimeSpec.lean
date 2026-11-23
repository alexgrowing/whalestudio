import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniversalAnticyclotomicCharacterLaws
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerOfInfConn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseRangeUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNatCongrOfAbsNormPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostCmEmbeddingProperties
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EmbeddingClosedIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPlaceOverMoveValConjPl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BijectiveCmType
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemZpowersOfTameGen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGeneratorSqEqOfSqMemZpowers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedPowSubOneLtOne

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.FrobeniusOrbits GlobalTheory.HeckeGal

namespace GlobalTheory.GalChar

attribute [local instance 10000] isTorsionFree_field

section General

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime]
  {O : Type} [CommRing O] [IsDomain O]

theorem toQ_injective (κ : FractionRing O →+* Qbar l) : Function.Injective (toQ κ) :=
  κ.injective.comp (IsFractionRing.injective O (FractionRing O))

omit [NumberField E] in
theorem inQ_val (κ : FractionRing O →+* Qbar l) (r : G E Ω →* Oˣ) (g : G E Ω) :
    ((inQ κ r g : (Qbar l)ˣ) : Qbar l) = toQ κ (r g : Oˣ) := rfl

omit [NumberField E] in
theorem inQ_inj (κ : FractionRing O →+* Qbar l) {r r' : G E Ω →* Oˣ} {g g' : G E Ω} (h : inQ κ r g = inQ κ r' g') :
    r g = r' g' := Units.ext (toQ_injective κ (congrArg Units.val h))

omit [NumberField E] in
theorem inQ_eq_one (κ : FractionRing O →+* Qbar l) {r : G E Ω →* Oˣ} {g : G E Ω} : inQ κ r g = 1 ↔ r g = 1 :=
  ⟨fun h => inQ_inj κ (r' := 1) (g' := 1) (h.trans (map_one _).symm), fun h => by
    rw [inQ, MonoidHom.comp_apply, h, map_one]⟩

theorem continuous_units {Γ M : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Monoid M]
    [TopologicalSpace M] (r : Γ →* Mˣ) (h : Continuous fun g => ((r g : Mˣ) : M)) : Continuous r := by
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  exact (h.comp continuous_inv).congr fun g => by simp only [Function.comp, map_inv]

theorem norm_le_one_of_compact {Γ K : Type} [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] [NormedField K]
    (r : Γ →* Kˣ) (h : Continuous r) (g : Γ) : ‖((r g : Kˣ) : K)‖ ≤ 1 := by
  obtain ⟨C, hC⟩ := (isCompact_range (Units.continuous_val.comp h).norm).bddAbove
  by_contra hlt
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C (not_le.1 hlt)
  have := hC ⟨g ^ n, rfl⟩
  simp only [Function.comp, map_pow, Units.val_pow_eq_pow_val, norm_pow] at this
  exact absurd this (not_le.2 hn)

def AlmostIn {K : Type} [Field K] (ε : K →+* ℂ) (χ : HChar E) : Prop :=
  ∀ᶠ v in Filter.cofinite, ∃ y, ε y = ((χ.val v : ℂˣ) : ℂ)

theorem AlmostIn.mul {K : Type} [Field K] {ε : K →+* ℂ} {χ χ' : HChar E} (h : AlmostIn ε χ) (h' : AlmostIn ε χ') :
    AlmostIn ε (χ * χ') := by
  filter_upwards [h, h'] with v ⟨y, hy⟩ ⟨y', hy'⟩
  exact ⟨y * y', by rw [map_mul, hy, hy', HChar.val_mul, Units.val_mul]⟩

theorem AlmostIn.inv {K : Type} [Field K] {ε : K →+* ℂ} {χ : HChar E} (h : AlmostIn ε χ) : AlmostIn ε χ⁻¹ := by
  filter_upwards [h] with v ⟨y, hy⟩
  exact ⟨y⁻¹, by rw [map_inv₀, hy, HChar.val_inv, Units.val_inv_eq_inv_val]⟩

theorem unr_ae (χ : HChar E) : ∀ᶠ v in Filter.cofinite, χ.UnrAt v := (GlobalTheory.Mem.UnrAe.unr_ae_and_level E χ).1

theorem away_ae (l : ℕ) (hl : l ≠ 0) : ∀ᶠ v : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ((l : ℕ) : 𝓞 E) ∉ v.asIdeal := by
  have h0 : Ideal.span {((l : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hl
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  exact Ideal.dvd_span_singleton.mpr (not_not.1 hv)

theorem almostIn_of_valuesIn {K : Type} [Field K] {ε : K →+* ℂ} {χ : HChar E} (h : χ.ValuesIn 0 ε) : AlmostIn ε χ := by
  filter_upwards [unr_ae χ] with v hv
  obtain ⟨y, hy⟩ := h v hv
  exact ⟨y, by simpa [HChar.valTw] using hy⟩

theorem absNorm_ne_zero (v : HeightOneSpectrum (𝓞 E)) : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by
  exact_mod_cast fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)

theorem block_val (μ η : HChar E) (r : ℕ) (v : HeightOneSpectrum (𝓞 E)) :
    (((block μ η r).val v : ℂˣ) : ℂ) =
      ((μ * η⁻¹).val v : ℂˣ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (((r : ℝ) / 2 : ℝ) : ℂ) := by
  rw [block, HChar.val_mul, HChar.val_mul, HChar.val_mul, Units.val_mul, Units.val_mul, Units.val_mul,
    (Model.absPow_isAbsPow E _).2.1 v, mul_assoc]
  congr 3
  push_cast
  ring

theorem AlmostIn.block {K : Type} [Field K] {ε : K →+* ℂ} {μ η : HChar E} (h : AlmostIn ε μ)
    (hη : η.ValuesIn (1 / 2) ε) {r : ℕ} (hr : Odd r) : AlmostIn ε (block μ η r) := by
  obtain ⟨ρ, rfl⟩ := hr
  filter_upwards [h, unr_ae η] with v ⟨y, hy⟩ hv
  obtain ⟨z, hz⟩ := hη v hv
  refine ⟨y * z⁻¹ * (Ideal.absNorm v.asIdeal : K) ^ ρ, ?_⟩
  rw [block_val, map_mul, map_mul, map_inv₀, hy, hz, map_pow, map_natCast, HChar.val_mul, HChar.val_inv, Units.val_mul,
    Units.val_inv_eq_inv_val, HChar.valTw, mul_inv, ← Complex.cpow_neg, ← Complex.cpow_natCast, mul_assoc, mul_assoc,
    ← Complex.cpow_add _ _ (absNorm_ne_zero v), mul_assoc]
  congr 3
  push_cast
  ring

theorem block_loc {μ η : HChar E} {r : ℕ} {v : HeightOneSpectrum (𝓞 E)} (hη : η.UnrAt v) {x : (v.adicCompletion E)ˣ}
    (hx : IsUnitAt v x) : (block μ η r).loc v x = μ.loc v x := by
  rw [block, HChar.loc_mul, HChar.loc_mul, HChar.loc_inv, hη x hx, (Model.absPow_isAbsPow E _).1 v x hx]
  simp

theorem isAlgPos_mul {χ χ' : HChar E} {n n' : (E →+* ℂ) → ℤ} (h : IsAlgPos χ n) (h' : IsAlgPos χ' n') :
    IsAlgPos (χ * χ') (n + n') := fun k hk => by
  rw [HChar.inf_mul, Units.val_mul, h k hk, h' k hk, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun φ _ => (zpow_add₀ ((map_ne_zero φ).2 k.ne_zero) _ _).symm

theorem isAlgPos_inv {χ : HChar E} {n : (E →+* ℂ) → ℤ} (h : IsAlgPos χ n) : IsAlgPos χ⁻¹ (-n) := fun k hk => by
  rw [HChar.inf_inv, Units.val_inv_eq_inv_val, h k hk, ← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl fun φ _ => (zpow_neg _ _).symm

theorem eq_of_frob [IsAlgClosure E Ω] {art : Ideles E →* Gab E Ω} (ha : IsGlobalArtin art) {B : Type} [CommGroup B]
    [TopologicalSpace B] [IsTopologicalGroup B] [T2Space B] {r r' : G E Ω →* B} (hr : Continuous r) (hr' : Continuous r')
    (h : ∀ᶠ v : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ : G E Ω,
      IsFrob (F := E) A (normV v) σ → r σ = r' σ) : r = r' := by
  have := GlobalTheory.FrobDense.eq_one_of_frob E Ω art ha B (r * r'⁻¹) (hr.mul hr'.inv) (Filter.eventually_cofinite.1 h).toFinset
    fun v hv A hA σ hσ => by
      rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hv
      rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hv A hA σ hσ, mul_inv_cancel]
  exact mul_inv_eq_one.1 this

variable [TopologicalSpace O] {art : Ideles E →* Gab E Ω} {κ : FractionRing O →+* Qbar l} {ι : Qbar l ≃+* ℂ}
  {χ : HChar E} {n : (E →+* ℂ) → ℤ} {r : G E Ω →* Oˣ} {v : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}

theorem IsGal.frob (ha : IsGlobalArtin art) (h : IsGal art κ ι χ n r) (hv : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal ∨ n = 0)
    (hu : χ.UnrAt v) (hA : IsPlaceOver A v) {σ : G E Ω} (hσ : IsFrob (F := E) A (normV v) σ) :
    ι (toQ κ (r σ : Oˣ)) = ((χ.val v : ℂˣ) : ℂ)⁻¹ := by
  rw [← inQ_val, h.2.2.frob_unr ha hv hu hA hσ, map_inv₀, ι.apply_symm_apply]

theorem IsGal.loc (h : IsGal art κ ι χ n r) (hv : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal ∨ n = 0) {x : (v.adicCompletion E)ˣ}
    {σ : G E Ω} (hx : art (localIdele E v x) = toAb E Ω σ) : ι (toQ κ (r σ : Oˣ)) = ((χ.loc v x : ℂˣ) : ℂ) := by
  rw [← inQ_val, h.2.2.loc_away hv x σ hx, ι.apply_symm_apply]

theorem exists_unit (ha : IsGlobalArtin art) (hA : IsPlaceOver A v) {σ : G E Ω} (hσ : σ ∈ Ine (F := E) A) :
    ∃ x, IsUnitAt v x ∧ art (localIdele E v x) = toAb E Ω σ := (ha.ine v A hA _).2 ⟨σ, hσ, rfl⟩

theorem exists_ine (ha : IsGlobalArtin art) (hA : IsPlaceOver A v) {x : (v.adicCompletion E)ˣ} (hx : IsUnitAt v x) :
    ∃ σ ∈ Ine (F := E) A, art (localIdele E v x) = toAb E Ω σ := by
  obtain ⟨σ, hσ, e⟩ := (ha.ine v A hA _).1 ⟨x, hx, rfl⟩
  exact ⟨σ, hσ, e.symm⟩

omit [TopologicalSpace O] in
theorem pow_eq_one_iff_of_val {u : Oˣ} {z : ℂˣ} (h : ι (toQ κ (u : O)) = (z : ℂ)) (m : ℕ) : u ^ m = 1 ↔ z ^ m = 1 := by
  rw [← Units.val_eq_one, ← Units.val_eq_one, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, ← h, ← map_pow,
    ← map_pow, map_eq_one_iff _ ι.injective, map_eq_one_iff _ (toQ_injective κ)]

theorem IsGal.ine_pow_iff (ha : IsGlobalArtin art) (h : IsGal art κ ι χ n r)
    (hv : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal ∨ n = 0) (hA : IsPlaceOver A v) (m : ℕ) :
    (∀ σ ∈ Ine (F := E) A, r σ ^ m = 1) ↔ ∀ x, IsUnitAt v x → χ.loc v x ^ m = 1 := by
  constructor
  · intro H x hx
    obtain ⟨σ, hσ, e⟩ := exists_ine ha hA hx
    exact (pow_eq_one_iff_of_val (h.loc hv e) m).1 (H σ hσ)
  · intro H σ hσ
    obtain ⟨x, hx, e⟩ := exists_unit ha hA hσ
    exact (pow_eq_one_iff_of_val (h.loc hv e) m).2 (H x hx)

theorem IsGal.unr_iff (ha : IsGlobalArtin art) (h : IsGal art κ ι χ n r)
    (hv : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal ∨ n = 0) (hA : IsPlaceOver A v) :
    (∀ σ ∈ Ine (F := E) A, r σ = 1) ↔ χ.UnrAt v := by
  simpa only [pow_one, HChar.UnrAt] using h.ine_pow_iff ha hv hA 1

theorem IsGal.ramExactly (ha : IsGlobalArtin art) (h : IsGal art κ ι χ 0 r) {Q : Set (HeightOneSpectrum (𝓞 E))}
    (hQ : ∀ v, χ.UnrAt v ↔ v ∉ Q) : RamExactly r Q := fun v A hA => by
  rw [← not_iff_not, ← hQ, ← h.unr_iff ha (Or.inr rfl) hA]
  push Not
  rfl

theorem IsGal.pow_eq_one (ha : IsGlobalArtin art) (h : IsGal art κ ι χ 0 r) {m : ℕ} (hm : χ.OrderDvd m) (g : G E Ω) :
    r g ^ m = 1 := by
  have := DFunLike.congr_fun (h.2.2.pow_eq_one ha.quot.surjective hm) g
  rw [MonoidHom.pow_apply, ← map_pow, MonoidHom.one_apply, inQ_eq_one, map_pow] at this
  exact this

omit [TopologicalSpace O] in
theorem sideIso_true (ι : Qbar l ≃+* ℂ) : sideIso ι true = ι := rfl

omit [TopologicalSpace O] in
theorem sideIso_false (ι : Qbar l ≃+* ℂ) (x : Qbar l) : sideIso ι false x = starRingEnd ℂ (ι x) := rfl

theorem IsGal.side (h : IsGal art κ ι χ 0 r) {m : ℕ} (hm0 : 0 < m) (hm : χ.OrderDvd m) (b : Bool)
    {x : (v.adicCompletion E)ˣ} {σ : G E Ω} (hx : art (localIdele E v x) = toAb E Ω σ) :
    sideIso ι b (toQ κ ((if b then r σ else (r σ)⁻¹ : Oˣ) : O)) = ((χ.loc v x : ℂˣ) : ℂ) := by
  have e := h.loc (Or.inr rfl) hx
  cases b
  · have h1 : ((χ.loc v x : ℂˣ) : ℂ) ^ m = 1 := by
      rw [← Units.val_pow_eq_pow_val]
      exact congrArg (fun ξ : HChar E => ((ξ.loc v x : ℂˣ) : ℂ)) hm
    have h2 := Complex.norm_eq_one_of_pow_eq_one h1 hm0.ne'
    rw [sideIso_false, if_neg (by simp), map_units_inv, map_inv₀, e, map_inv₀, ← Complex.inv_eq_conj h2, inv_inv]
  · exact e

section Coef

variable [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsTopologicalRing O]
  (hO : IsAdic (IsLocalRing.maximalIdeal O))
  (hκ : ∀ z : ℤ_[l], κ (algebraMap O (FractionRing O) (algebraMap ℤ_[l] O z)) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]))
include hO hκ

theorem isEmbedding_toQ : Topology.IsEmbedding (toQ κ) := (GlobalTheory.CoefEmbed.embedding_closed_integral l O hO κ hκ).1

theorem IsGal.cont (h : IsGal art κ ι χ n r) : Continuous (inQ κ r) :=
  continuous_units _ ((isEmbedding_toQ hO hκ).continuous.comp h.2.1)

theorem IsGal.isOpen_ker (ha : IsGlobalArtin art) (h : IsGal art κ ι χ 0 r) {m : ℕ} (hm0 : 0 < m) (hm : χ.OrderDvd m) :
    IsOpen (r.ker : Set (G E Ω)) := by
  have := isOpen_ker_of_pow (inQ κ r) (h.cont hO hκ) hm0 fun g => by
    rw [← map_pow, inQ_eq_one, map_pow, h.pow_eq_one ha hm]
  convert this using 1
  ext g
  exact (inQ_eq_one κ).symm

theorem IsGal.dec_triv (ha : IsGlobalArtin art) (h : IsGal art κ ι χ 0 r) (hA : IsPlaceOver A v)
    (hv : ∀ x, χ.loc v x = 1) {σ : G E Ω} (hσ : σ ∈ Dec (F := E) A) : r σ = 1 :=
  (inQ_eq_one κ).1 ((h.2.2.dec_triv ha (h.cont hO hκ) (Or.inr rfl) hA).2 (MonoidHom.ext hv) σ hσ)

theorem continuous_cyc : Continuous fun g : G E Ω =>
    ((((Units.map (algebraMap ℤ_[l] O).toMonoidHom).comp (cycZ (F := E) (Ω := Ω) l)) g : Oˣ) : O) := by
  rw [(isEmbedding_toQ hO hκ).continuous_iff]
  have e : (toQ κ ∘ fun g : G E Ω =>
      ((((Units.map (algebraMap ℤ_[l] O).toMonoidHom).comp (cycZ (F := E) (Ω := Ω) l)) g : Oˣ) : O)) =
      fun g => algebraMap ℚ_[l] (Qbar l) (((cycZ E Ω l g : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) := funext fun g => hκ _
  rw [e]
  exact (continuous_algebraMap _ _).comp ((continuous_subtype_val : Continuous fun z : ℤ_[l] => (z : ℚ_[l])).comp
    ((Units.continuous_val (M := ℤ_[l])).comp (continuous_cycZ E Ω l)))

theorem exists_isGal [IsAlgClosure E Ω] (ha : IsGlobalArtin art) (hn : IsAlgPos χ n) {K : Type} [Field K] {ε : K →+* ℂ}
    {f : K →+* FractionRing O} (hf : ∀ x, ι (κ (f x)) = ε x) (hχ : AlmostIn ε χ) : ∃ r : G E Ω →* Oˣ, IsGal art κ ι χ n r := by
  obtain ⟨r, hr, hL⟩ := ha.exists_isLAdicOf ι hn
  obtain ⟨hemb, hcl, hint, -⟩ := GlobalTheory.CoefEmbed.embedding_closed_integral l O hO κ hκ
  let K0 : Subgroup (Qbar l)ˣ := (Units.map κ.toMonoidHom).range
  have hK0 : ∀ u : (Qbar l)ˣ, u ∈ K0 ↔ (u : Qbar l) ∈ Set.range κ := fun u =>
    ⟨fun ⟨y, hy⟩ => ⟨y, congrArg Units.val hy⟩, fun ⟨y, hy⟩ =>
      ⟨Units.mk0 y (by rintro rfl; exact u.ne_zero (by rw [← hy, map_zero])), Units.ext hy⟩⟩
  haveI : IsClosed (K0 : Set (Qbar l)ˣ) := by
    have : (K0 : Set (Qbar l)ˣ) = Units.val ⁻¹' Set.range κ := Set.ext hK0
    rw [this]
    exact hcl.preimage Units.continuous_val
  have h1 : (QuotientGroup.mk' K0).comp r = 1 := by
    refine eq_of_frob ha (QuotientGroup.continuous_mk.comp hr) continuous_const ?_
    filter_upwards [hχ, unr_ae χ, away_ae (E := E) l (Fact.out : l.Prime).ne_zero] with v ⟨y, hy⟩ hu hv A hA σ hσ
    refine (QuotientGroup.eq_one_iff _).2 ((hK0 _).2 ⟨(f y)⁻¹, ?_⟩)
    rw [hL.frob_unr ha (Or.inl hv) hu hA hσ, map_inv₀, ← hy, ← hf, ι.symm_apply_apply]
  haveI : IsGalois E Ω := IsAlgClosure.isGalois E Ω
  have h2 : ∀ g, ∃ y : O, toQ κ y = (r g : (Qbar l)ˣ) := fun g => by
    obtain ⟨x, hx⟩ := (hK0 _).1 ((QuotientGroup.eq_one_iff _).1 (DFunLike.congr_fun h1 g))
    obtain ⟨y, rfl⟩ := hint x (hx ▸ norm_le_one_of_compact r hr g)
    exact ⟨y, hx⟩
  choose s hs using h2
  let s' : G E Ω →* O :=
    { toFun := s
      map_one' := toQ_injective κ (by rw [hs, map_one, map_one, Units.val_one])
      map_mul' := fun a b => toQ_injective κ (by rw [map_mul, hs, hs, hs, map_mul, Units.val_mul]) }
  have e : inQ κ s'.toHomUnits = r := MonoidHom.ext fun g => Units.ext (hs g)
  refine ⟨s'.toHomUnits, hn, ?_, e ▸ hL⟩
  rw [(isEmbedding_toQ hO hκ).continuous_iff]
  exact (Units.continuous_val.comp hr).congr fun g => (hs g).symm

end Coef

theorem continuous_ringHom {O O' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
    [IsTopologicalRing O] [CommRing O'] [IsLocalRing O'] [TopologicalSpace O'] [IsTopologicalRing O']
    (hO : IsAdic (IsLocalRing.maximalIdeal O)) (hO' : IsAdic (IsLocalRing.maximalIdeal O')) {l : ℕ} (h0 : (l : O) ≠ 0)
    (hl : (l : O') ∈ IsLocalRing.maximalIdeal O') (t : O →+* O') : Continuous t := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ
  refine continuous_of_continuousAt_zero t ?_
  rw [ContinuousAt, map_zero, hO.hasBasis_nhds_zero.tendsto_iff hO'.hasBasis_nhds_zero]
  refine fun n _ => ⟨e * n, trivial, fun x hx => ?_⟩
  rw [SetLike.mem_coe, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
  obtain ⟨y, rfl⟩ := hx
  have : ϖ ^ e = (↑u⁻¹ : O) * l := by rw [hu, Units.inv_mul_cancel_left]
  rw [SetLike.mem_coe, pow_mul, this, map_mul, map_pow, map_mul, map_natCast]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (Ideal.mul_mem_left _ _ hl) n)

end General

section Statements

variable {R : Ranks} (H : Formalism.BasicNotions.Host R) {Ω : Type} [Field Ω] [Algebra H.E Ω] (cc : Ω ≃+* Ω)
  {e : Fin R.m → R.Psi → ℚ} (C : GlobalTheory.Mem.Chr.HFrame H e) (art : Ideles H.E →* Gab H.E Ω)

def HeckeTwistCharactersDeltaChi : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O]
    [Module.Finite ℤ_[l] O] [TopologicalSpace O] [IsTopologicalRing O], IsAdic (IsLocalRing.maximalIdeal O) →
    ∀ (κ : FractionRing O →+* Qbar l),
    (∀ z : ℤ_[l], κ (algebraMap O (FractionRing O) (algebraMap ℤ_[l] O z)) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l])) →
    ∀ (ι : Qbar l ≃+* ℂ),
    ∀ (K : Type) [Field K] (ε : K →+* ℂ) (f f' : K →+* FractionRing O), (∀ x, ι (κ (f x)) = ε x) →
    (∀ x, ι (κ (f' x)) = starRingEnd ℂ (ε x)) →
    (∀ j, (C.mu0 j).ValuesIn 0 ε) → C.eta.ValuesIn (1 / 2) ε → (delAt H C l).ValuesIn 0 ε →
    ∀ pD : Finset (PlE H), (pD : Set (PlE H)) = placesOver H.E (if l = H.pde then H.pde' else H.pde) →
    ∃ (delta : G H.E Ω →* Oˣ) (chi1 : ℕ → Bool → (G H.E Ω →* Oˣ)),
      IsGal art κ ι (delAt H C l) 0 delta ∧
      (∀ (j : Fin R.m) (b : Bool), ∃ n,
        IsGal art κ (sideIso ι b) (block (C.mu0 j * delAt H C l) C.eta R.r) n (chi1 (j.1 + 1) b)) ∧
      IsOpen (delta.ker : Set (G H.E Ω)) ∧ AntiHom cc delta ∧ RamExactly delta ↑pD ∧
      (∀ v ∈ pD, ∀ A : ValuationSubring Ω, IsPlaceOver A v → Nat.card ((Ine (F := H.E) A).map delta) = 15) ∧
      (∀ v ∈ pD, Ideal.absNorm v.asIdeal % 15 = 1) ∧
      (∀ j b, Continuous (fun g => ((chi1 j b g : Oˣ) : O))) ∧
      (∀ j b v, v ∉ placesOver H.E l → (∀ k, v ∉ placesOver H.E (H.g k)) → v ∉ pD →
        ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ ∈ Ine (F := H.E) A, chi1 j b σ = 1) ∧
      (∀ j b, ∀ v ∈ pD, ∀ A : ValuationSubring Ω, IsPlaceOver A v →
        ∀ σ ∈ Ine (F := H.E) A, chi1 j b σ = if b then delta σ else (delta σ)⁻¹) ∧
      (∀ j b k v, v ∈ placesOver H.E (H.g k) → v ∉ placesOver H.E l →
        ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ ∈ Ine (F := H.E) A, chi1 j b σ ^ (H.g k - 1) = 1)

def ToricHeckeQuotientCharacter : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O]
    [Module.Finite ℤ_[l] O] [TopologicalSpace O] [IsTopologicalRing O], IsAdic (IsLocalRing.maximalIdeal O) →
    ∀ (κ : FractionRing O →+* Qbar l),
    (∀ z : ℤ_[l], κ (algebraMap O (FractionRing O) (algebraMap ℤ_[l] O z)) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l])) →
    ∀ (ι : Qbar l ≃+* ℂ),
    ∀ (K : Type) [Field K] (ε : K →+* ℂ) (f f' : K →+* FractionRing O), (∀ x, ι (κ (f x)) = ε x) →
    (∀ x, ι (κ (f' x)) = starRingEnd ℂ (ε x)) →
    ∀ pD : Finset (PlE H), (pD : Set (PlE H)) = placesOver H.E (if l = H.pde then H.pde' else H.pde) →
    ∀ (delta : G H.E Ω →* Oˣ), IsGal art κ ι (delAt H C l) 0 delta →
    ∀ (O' : Type) [CommRing O'] [IsLocalRing O'] [Algebra O O'] [TopologicalSpace O'] [IsTopologicalRing O'],
    IsAdic (IsLocalRing.maximalIdeal O') → ((l : ℕ) : O') ∈ IsLocalRing.maximalIdeal O' →
    ∀ (j : Fin R.m) (b : Bool) (χ : HChar H.E) (c : R.Psi → ℤ), χ.TrivOn H.F → χ.HasInf (embPsi H) (fun τ => 2 * c τ) →
    (∀ v ∈ pD, ∀ x : (v.adicCompletion H.E)ˣ, x ^ (Ideal.absNorm v.asIdeal - 1) = 1 → χ.loc v x = 1) →
    (C.mu0 j).ValuesIn 0 ε → (delAt H C l).ValuesIn 0 ε → χ.ValuesIn 0 ε →
    ∀ S0 : Finset (PlE H), placesOver H.E l ⊆ ↑S0 → (∀ k, placesOver H.E (H.g k) ⊆ ↑S0) → pD ⊆ S0 →
    (∀ v, v ∉ S0 → χ.UnrAt v) →
    ∃ (lam0 : G H.E Ω →* Oˣ) (lamG : G H.E Ω →* O'ˣ) (Xv : PlE H → O'),
      (∃ n, IsGal art κ (sideIso ι b) (C.mu0 j * delAt H C l * χ⁻¹) n lam0) ∧
      lamG = (Units.map (algebraMap O O').toMonoidHom).comp lam0 ∧
      Continuous (fun g => ((lamG g : O'ˣ) : O')) ∧
      (∀ v, v ∉ S0 → ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ ∈ Ine (F := H.E) A, lamG σ = 1) ∧
      (∀ v ∈ pD, ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ ∈ Ine (F := H.E) A, ∃ n : ℕ,
        (lamG σ * (Units.map (algebraMap O O').toMonoidHom (if b then delta σ else (delta σ)⁻¹))⁻¹) ^
          (Ideal.absNorm v.asIdeal ^ n) = 1) ∧
      AntiHom cc lamG ∧
      ∀ P, P ∉ S0 → ∀ A : ValuationSubring Ω, IsPlaceOver A P → ∀ σ : G H.E Ω, IsFrob (F := H.E) A (normV P) σ →
        Xv P = ((lamG σ : O'ˣ) : O')

def LocalisationCharacterSpec : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O]
    [Module.Finite ℤ_[l] O] [TopologicalSpace O] [IsTopologicalRing O], IsAdic (IsLocalRing.maximalIdeal O) →
    ∀ (κ : FractionRing O →+* Qbar l),
    (∀ z : ℤ_[l], κ (algebraMap O (FractionRing O) (algebraMap ℤ_[l] O z)) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l])) →
    ∀ (ι : Qbar l ≃+* ℂ),
    ∀ (K : Type) [Field K] (ε : K →+* ℂ) (f : K →+* FractionRing O), (∀ x, ι (κ (f x)) = ε x) →
    ∀ (j : Fin R.m) (Q : Finset (PlE H)) (ψ : HChar H.E), IsPsi (H := H) l Q ψ →
    (∀ v ∈ Q, (∀ k, v ∉ placesOver H.E (H.g k)) ∧ v ∉ placesOver H.E (if l = H.pde then H.pde' else H.pde)) →
    (C.mu0 j).ValuesIn 0 ε → C.eta.ValuesIn (1 / 2) ε → (delAt H C l).ValuesIn 0 ε → ψ.ValuesIn 0 ε →
    ∃ (chi : ℕ → (G H.E Ω →* Oˣ)) (psiL : G H.E Ω →* Oˣ),
      (∃ n, IsGal art κ ι (block (C.mu0 j * (delAt H C l * ψ)) C.eta R.r) n (chi 1)) ∧ IsGal art κ ι ψ 0 psiL ∧
      (∀ c, Continuous (fun g => ((chi c g : Oˣ) : O))) ∧
      (∀ c : ℕ, chi c = chi 1 * ((Units.map (algebraMap ℤ_[l] O).toMonoidHom).comp
        (cycZ (F := H.E) (Ω := Ω) l)) ^ (-((c : ℤ) - 1))) ∧
      (∀ v ∈ Q, ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∃ g ∈ Ine (F := H.E) A, chi 1 g ≠ 1) ∧
      (∀ g, ∃ n : ℕ, psiL g ^ (l ^ n) = 1) ∧ IsOpen (psiL.ker : Set (G H.E Ω)) ∧ AntiHom cc psiL ∧
      RamExactly psiL ↑Q ∧
      (∀ v, v ∈ placesOver H.E l → ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ ∈ Dec (F := H.E) A, psiL σ = 1) ∧
      ∀ w, w ∉ placesOver H.E l → (∀ k, w ∉ placesOver H.E (H.g k)) →
        w ∉ placesOver H.E (if l = H.pde then H.pde' else H.pde) → w ∉ Q →
        (C.mu0 j * (delAt H C l * ψ) * C.eta⁻¹).UnrAt w ∧
        ∀ (B : ValuationSubring Ω) (σ : G H.E Ω), IsPlaceOver (F := H.E) B w → IsFrob (F := H.E) B (normV w) σ →
          (((C.mu0 j * (delAt H C l * ψ) * C.eta⁻¹).val w)⁻¹ : ℂˣ).1 *
              ((normV w : ℕ) : ℂ) ^ (((((R.t : ℝ) - 1) / 2 + (1 - (R.nV : ℝ)) / 2 : ℝ)) : ℂ) =
            ι (κ (algebraMap O (FractionRing O) ((chi 1 σ : Oˣ) : O)))

def LocalisationTwistCharacterCompat : Prop :=
  ∀ (l₀ : ℕ) [Fact l₀.Prime] (O₀ : Type) [CommRing O₀] [IsDomain O₀] [IsDiscreteValuationRing O₀] [Algebra ℤ_[l₀] O₀]
    [Module.Finite ℤ_[l₀] O₀] [TopologicalSpace O₀] [IsTopologicalRing O₀], IsAdic (IsLocalRing.maximalIdeal O₀) →
    ∀ (κ₀ : FractionRing O₀ →+* Qbar l₀),
    (∀ z : ℤ_[l₀], κ₀ (algebraMap O₀ (FractionRing O₀) (algebraMap ℤ_[l₀] O₀ z)) = algebraMap ℚ_[l₀] (Qbar l₀) (z : ℚ_[l₀])) →
    ∀ (ι₀ : Qbar l₀ ≃+* ℂ),
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O]
    [Module.Finite ℤ_[l] O] [TopologicalSpace O] [IsTopologicalRing O], IsAdic (IsLocalRing.maximalIdeal O) →
    ∀ (κ : FractionRing O →+* Qbar l),
    (∀ z : ℤ_[l], κ (algebraMap O (FractionRing O) (algebraMap ℤ_[l] O z)) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l])) →
    ∀ (ι : Qbar l ≃+* ℂ),
    l₀ = l → ∀ (K : Type) [Field K] (ε : K →+* ℂ) (f₀ : K →+* FractionRing O₀) (f : K →+* FractionRing O),
    (∀ x, ι₀ (κ₀ (f₀ x)) = ε x) → (∀ x, ι (κ (f x)) = ε x) → ∀ t : O₀ →+* O,
    (∀ (x : K) (y : O₀), algebraMap O₀ (FractionRing O₀) y = f₀ x → f x = algebraMap O (FractionRing O) (t y)) →
    ∀ (j : Fin R.m) (ψ : HChar H.E), (C.mu0 j).ValuesIn 0 ε → C.eta.ValuesIn (1 / 2) ε → (delAt H C l₀).ValuesIn 0 ε →
    ∀ (n₀ n n' : (H.E →+* ℂ) → ℤ) (chi1 : G H.E Ω →* O₀ˣ) (chi psiL : G H.E Ω →* Oˣ),
    IsGal art κ₀ ι₀ (block (C.mu0 j * delAt H C l₀) C.eta R.r) n₀ chi1 →
    IsGal art κ ι (block (C.mu0 j * (delAt H C l * ψ)) C.eta R.r) n chi → IsGal art κ ι ψ n' psiL →
    chi = (Units.map t.toMonoidHom).comp chi1 * psiL

def TameInertiaGeneratorCharacterSpec : Prop :=
  ∀ (k : Fin 2) (w : PlE H), C.P.Div k w → ∀ A : ValuationSubring Ω, IsPlaceOver A w → ∀ tg : G H.E Ω, TameGenAt A tg →
    ∀ teich : Fb (H.g k) (H.g_prime k) →* ℂ, (∀ x y, x ≠ 0 → y ≠ 0 → teich x = teich y → x = y) →
    haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩
    ∃ γ : (ZMod (H.g k))ˣ, Subgroup.zpowers γ = ⊤ ∧
      ∀ (l : ℕ) [Fact l.Prime], l ≠ H.g k → ∀ (O : Type) [CommRing O] [IsDomain O] [TopologicalSpace O]
        (κ : FractionRing O →+* Qbar l) (ι : Qbar l ≃+* ℂ) (j : Fin R.m) (ξ : HChar H.E), ξ.UnrAt w →
        ∀ (n : (H.E →+* ℂ) → ℤ) (chi : G H.E Ω →* Oˣ), IsGal art κ ι (block (C.mu0 j * ξ) C.eta R.r) n chi →
        ι (κ (algebraMap O (FractionRing O) ((chi tg : Oˣ) : O))) =
          teich (algebraMap (ZMod (H.g k)) (Formalism.CyclotomicNorms.Fbar (H.g k))
            (((γ ^ (2 * (j.1 + 1)))⁻¹ : (ZMod (H.g k))ˣ) : ZMod (H.g k)))

end Statements

section Host

theorem notMem_of_ne {E : Type} [Field E] [NumberField E] {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h : p ≠ q)
    {v : HeightOneSpectrum (𝓞 E)} (hv : ((p : ℕ) : 𝓞 E) ∈ v.asIdeal) : ((q : ℕ) : 𝓞 E) ∉ v.asIdeal := fun hv' => by
  obtain ⟨s, t, hst⟩ : IsCoprime (p : 𝓞 E) (q : 𝓞 E) := Nat.Coprime.cast ((Nat.coprime_primes hp hq).2 h)
  apply v.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hst]
  exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hv) (v.asIdeal.mul_mem_left _ hv')

theorem absNorm_eq_pow {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime)
    {v : HeightOneSpectrum (𝓞 E)} (hv : ((p : ℕ) : 𝓞 E) ∈ v.asIdeal) : ∃ a, Ideal.absNorm v.asIdeal = p ^ a := by
  have h := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 hv)
  rw [Ideal.absNorm_span_natCast] at h
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow hp).1 h
  exact ⟨a, ha⟩

theorem card_eq_of_pow_iff {O : Type} [CommRing O] [IsDomain O] (T : Subgroup Oˣ) {m : ℕ} (hm : m ≠ 0)
    (h : ∀ n : ℕ, (∀ t ∈ T, t ^ n = 1) ↔ m ∣ n) : Nat.card T = m := by
  haveI : NeZero m := ⟨hm⟩
  have hle : T ≤ rootsOfUnity m O := fun t ht => (h m).2 dvd_rfl t ht
  haveI : Finite T := Finite.of_injective _ (Subgroup.inclusion_injective hle)
  rw [← IsCyclic.exponent_eq_card]
  have key : ∀ n : ℕ, Monoid.exponent T ∣ n ↔ m ∣ n := fun n => by
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one, ← h]
    exact ⟨fun a t ht => congrArg Subtype.val (a ⟨t, ht⟩), fun a t => Subtype.ext (a t.1 t.2)⟩
  exact Nat.dvd_antisymm ((key m).2 dvd_rfl) ((key _).1 dvd_rfl)

theorem odd_r (R : Ranks) : Odd R.r := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨b, hb⟩ := R.m_even
  have := R.two_le_m
  exact ⟨a + b - 1, by unfold Ranks.r; omega⟩

theorem sideIso_read {l : ℕ} [Fact l.Prime] {L K : Type} [Field L] [Field K] {κ : L →+* Qbar l} {ι : Qbar l ≃+* ℂ}
    {ε : K →+* ℂ} {f f' : K →+* L} (hf : ∀ x, ι (κ (f x)) = ε x) (hf' : ∀ x, ι (κ (f' x)) = starRingEnd ℂ (ε x))
    (b : Bool) (x : K) : sideIso ι b (κ ((if b then f else f') x)) = ε x := by
  cases b
  · rw [sideIso_false, if_neg (by simp), hf', Complex.conj_conj]
  · exact hf x

theorem read_conj {l : ℕ} [Fact l.Prime] {L LL : Type} [Field L] [Field LL] [CharZero LL] [StarRing LL]
    (LL0 : IntermediateField ℚ LL) (ε : LL →+* ℂ) (hε : ∀ x, ε (star x) = starRingEnd ℂ (ε x))
    (h0 : ∀ x : LL0, star (x : LL) ∈ LL0) {κ : L →+* Qbar l} {ι : Qbar l ≃+* ℂ} {f f' : LL0 →+* L}
    (hc : ∀ x y : LL0, (y : LL) = star (x : LL) → f' x = f y) (hf : ∀ x : LL0, ι (κ (f x)) = ε x) (x : LL0) :
    ι (κ (f' x)) = starRingEnd ℂ (ε x) := by
  rw [hc x ⟨_, h0 x⟩ rfl, hf, ← hε]

variable {R : Ranks} {H : Formalism.BasicNotions.Host R} {Ω : Type} [Field Ω] [Algebra H.E Ω] {cc : Ω ≃+* Ω}
  {e : Fin R.m → R.Psi → ℚ} (C : GlobalTheory.Mem.Chr.HFrame H e) {art : Ideles H.E →* Gab H.E Ω}

theorem inertialOrderFifteenChar_auxiliaryPrime_spec {l : ℕ} : (if l = H.pde then H.pde' else H.pde).Prime ∧
    (if l = H.pde then H.pde' else H.pde) ≠ l ∧ (∀ k, (if l = H.pde then H.pde' else H.pde) ≠ H.g k) ∧
    (if l = H.pde then H.pde' else H.pde) % 15 = 1 ∧
    IsDelta (H := H) (if l = H.pde then H.pde' else H.pde) (delAt H C l) := by
  unfold delAt
  split_ifs with h
  · exact ⟨H.pde'_prime, h ▸ H.pde_ne.symm, fun k => (H.pde_ne_g k).2, H.pde_mod.2, C.isDel'⟩
  · exact ⟨H.pde_prime, Ne.symm h, fun k => (H.pde_ne_g k).1, H.pde_mod.1, C.isDel⟩

theorem exists_isAlgPos_mu0 (he : ∀ j τ, ∃ z : ℤ, e j τ = z) (j : Fin R.m) : ∃ n, IsAlgPos (C.mu0 j) n := by
  obtain ⟨n, hn, h⟩ := (C.isMu0 j).inf
  choose z hz using he j
  have e1 : n = fun τ => 2 * (-z τ) := funext fun τ => by
    have := hn τ
    simp only [hz] at this
    exact_mod_cast this
  obtain ⟨n', h'⟩ := (GlobalTheory.Mem.CharAlg.isAlg_even_odd R H).1 (C.mu0 j) (fun τ => -z τ) (e1 ▸ h)
  exact ⟨n', isAlgPos_of_isAlg h'⟩

theorem block_alg {μ : HChar H.E} (h : ∃ n, IsAlgPos μ n) : ∃ n, IsAlgPos (block μ C.eta R.r) n := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨n', hn'⟩ := (GlobalTheory.Mem.CharAlg.isAlg_even_odd R H).2 C.eta C.isEta.inf R.r (odd_r R)
  exact ⟨_, isAlgPos_mul hn (isAlgPos_of_isAlg hn')⟩

theorem del_alg (l : ℕ) : IsAlgPos (delAt H C l) 0 :=
  let ⟨_, h0, h⟩ := (inertialOrderFifteenChar_auxiliaryPrime_spec C (l := l)).2.2.2.2.fin
  isAlgPos_zero_of_orderDvd h0 h

variable [IsAlgClosure H.E Ω]

theorem IsGal.anti (hcc : IsCMConjOm H.E Ω cc) (ha : IsGlobalArtin art) {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O]
    [IsDomain O] [TopologicalSpace O] {κ : FractionRing O →+* Qbar l} {ι : Qbar l ≃+* ℂ} {χ : HChar H.E}
    {n : (H.E →+* ℂ) → ℤ} {r : G H.E Ω →* Oˣ} (h : IsGal art κ ι χ n r) (hc : Continuous (inQ κ r))
    (ht : χ.TrivOn H.F) : AntiHom cc r := by
  obtain ⟨c, hc1, hcm, hr, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  have h1 : ∀ x : H.E, cc (algebraMap H.E Ω x) = algebraMap H.E Ω (c x) := fun x => by
    obtain ⟨j, hj⟩ := hcc.1
    apply j.injective
    rw [hj, hc1]
    exact (H.conjE_apply (j.comp (algebraMap H.E Ω)) x).symm
  have h2 := GlobalTheory.AntiLAdic.antiHom_of_trivOn H.F H.E c hcm.rank hcm.ne (fun x => by rw [hc1, hc1, conj_conj]) hr Ω cc h1 art ha l ι χ n _ hc
    h.2.2 ht
  intro g g' hg
  rw [← map_inv]
  exact inQ_inj κ (by rw [h2 g g' hg, map_inv])

theorem hostHeckeFrame_twist_galois_characters (hcc : IsCMConjOm H.E Ω cc) (ha : IsGlobalArtin art) (he : ∀ j τ, ∃ z : ℤ, e j τ = z)
    (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) : HeckeTwistCharactersDeltaChi H cc C art := by
  intro l _ O _ _ _ _ _ _ _ hO κ hκ ι K _ ε f f' hf hf' hμ hη hδ pD hpD
  have hl : l.Prime := Fact.out
  obtain ⟨hp, hpl, hpg, hp15, hD⟩ := inertialOrderFifteenChar_auxiliaryPrime_spec C (l := l)
  set p := if l = H.pde then H.pde' else H.pde
  have hmem : ∀ v, v ∈ pD ↔ OverP H p v := fun v => by rw [← Finset.mem_coe, hpD]; rfl
  obtain ⟨m, hm0, hm⟩ := hD.fin
  obtain ⟨delta, hd⟩ := exists_isGal hO hκ ha (del_alg C l) hf (almostIn_of_valuesIn hδ)
  have hex : ∀ (j : Fin R.m) (b : Bool), ∃ r : G H.E Ω →* Oˣ, ∃ n,
      IsGal art κ (sideIso ι b) (block (C.mu0 j * delAt H C l) C.eta R.r) n r := fun j b => by
    obtain ⟨n0, h0⟩ := exists_isAlgPos_mu0 C he j
    obtain ⟨n, hn⟩ := block_alg C ⟨_, isAlgPos_mul h0 (del_alg C l)⟩
    obtain ⟨r, hr⟩ := exists_isGal hO hκ ha hn (sideIso_read hf hf' b)
      (((almostIn_of_valuesIn (hμ j)).mul (almostIn_of_valuesIn hδ)).block hη (odd_r R))
    exact ⟨r, n, hr⟩
  choose ch nn hch using hex
  have hm2 := R.two_le_m
  let ix : ℕ → Fin R.m := fun j => ⟨min (j - 1) (R.m - 1), by omega⟩
  have hix : ∀ j : Fin R.m, ix (j.1 + 1) = j := fun j => Fin.ext (by have := j.2; simp only [ix]; omega)
  refine ⟨delta, fun j b => ch (ix j) b, hd, fun j b => ⟨nn j b, by simpa only [hix] using hch j b⟩,
    hd.isOpen_ker hO hκ ha hm0 hm, hd.anti hcc ha (hd.cont hO hκ) hD.triv, hd.ramExactly ha fun v => ?_,
    fun v hv A hA => ?_, fun v hv => ?_, fun j b => (hch _ b).2.1, fun j b v h1 h2 h3 A hA => ?_,
    fun j b v hv A hA σ hσ => ?_, fun j b k v h1 h2 A hA => ?_⟩
  · rw [Finset.mem_coe, hmem]
    refine ⟨fun hu hv => ?_, hD.unr v⟩
    have := (hD.ine v hv 1).1 fun x hx => by rw [pow_one, hu x hx]
    omega
  · refine card_eq_of_pow_iff _ (by norm_num) fun n => ?_
    rw [← hD.ine v ((hmem v).1 hv) n, ← hd.ine_pow_iff ha (Or.inr rfl) hA n]
    exact ⟨fun a σ hσ => a _ ⟨σ, hσ, rfl⟩, by rintro a _ ⟨σ, hσ, rfl⟩; exact a σ hσ⟩
  · obtain ⟨a, ha'⟩ := absNorm_eq_pow hp ((hmem v).1 hv)
    rw [ha', Nat.pow_mod, hp15, one_pow]
    rfl
  · refine ((hch _ b).unr_iff ha (Or.inl h1) hA).2 fun x hx => ?_
    rw [block_loc (C.isEta.unr v) hx, HChar.loc_mul, (C.isMu0 _).unr v h2 x hx, hD.unr v (mt (hmem v).2 h3) x hx, one_mul]
  · obtain ⟨x, hx, ex⟩ := exists_unit ha hA hσ
    have hv' := (hmem v).1 hv
    have e1 := (hch (ix j) b).loc (Or.inl (notMem_of_ne hp hl hpl hv')) ex
    rw [block_loc (C.isEta.unr v) hx, HChar.loc_mul,
      (C.isMu0 _).unr v (fun k => notMem_of_ne hp (H.g_prime k) (hpg k) hv') x hx, one_mul,
      ← hd.side hm0 hm b ex] at e1
    exact Units.ext (toQ_injective κ ((sideIso ι b).injective e1))
  · refine ((hch _ b).ine_pow_iff ha (Or.inl h2) hA _).2 fun x hx => ?_
    have hN := (GlobalTheory.Mem.Chr.splitsC_main R H _ (H.g_prime k) (hg k) v h1).1
    rw [block_loc (C.isEta.unr v) hx, HChar.loc_mul,
      hD.unr v (notMem_of_ne (H.g_prime k) hp (hpg k).symm h1) x hx, mul_one, ← hN]
    exact (GlobalTheory.Mem.WildChar.orders_on_units _ _ v).1 ((C.isMu0 _).tame v) x hx

theorem hostHeckeFrame_toric_quotient_character (hcc : IsCMConjOm H.E Ω cc) (ha : IsGlobalArtin art) (he : ∀ j τ, ∃ z : ℤ, e j τ = z) :
    ToricHeckeQuotientCharacter H cc C art := by
  intro l _ O _ _ _ _ _ _ _ hO κ hκ ι K _ ε f f' hf hf' pD hpD delta hd O' _ _ _ _ _ hO' hlO' j b χ c hχF hχi hχw hμ hδ hχ
    S0 hS1 hS2 hS3 hS4
  have hl : l.Prime := Fact.out
  obtain ⟨hp, hpl, hpg, -, hD⟩ := inertialOrderFifteenChar_auxiliaryPrime_spec C (l := l)
  set p := if l = H.pde then H.pde' else H.pde
  have hmem : ∀ v, v ∈ pD ↔ OverP H p v := fun v => by rw [← Finset.mem_coe, hpD]; rfl
  obtain ⟨m, hm0, hm⟩ := hD.fin
  obtain ⟨n0, h0⟩ := exists_isAlgPos_mu0 C he j
  obtain ⟨n1, h1⟩ := (GlobalTheory.Mem.CharAlg.isAlg_even_odd R H).1 χ c hχi
  obtain ⟨r, hr⟩ := exists_isGal hO hκ ha
    (isAlgPos_mul (isAlgPos_mul h0 (del_alg C l)) (isAlgPos_inv (isAlgPos_of_isAlg h1))) (sideIso_read hf hf' b)
    (((almostIn_of_valuesIn hμ).mul (almostIn_of_valuesIn hδ)).mul (almostIn_of_valuesIn hχ).inv)
  have hl0 : ((l : ℕ) : O) ≠ 0 := fun h => by
    have := congrArg (toQ κ) h
    rw [map_natCast, map_zero] at this
    exact hl.ne_zero (by exact_mod_cast this)
  have hunr : ∀ v, v ∉ S0 → (C.mu0 j * delAt H C l * χ⁻¹).UnrAt v := fun v hv =>
    (((C.isMu0 j).unr v fun k hk => hv (hS2 k hk)).mul (hD.unr v fun hk => hv (hS3 ((hmem v).2 hk)))).mul (hS4 v hv).inv
  have hA := hr.anti hcc ha (hr.cont hO hκ) (((C.isMu0 j).triv.mul hD.triv).mul hχF.inv)
  refine ⟨r, _, fun P => algebraMap O O' (r (frobOf Ω P) : Oˣ), ⟨_, hr⟩, rfl,
    (continuous_ringHom hO hO' hl0 hlO' (algebraMap O O')).comp hr.2.1, fun v hv A hA σ hσ => ?_,
    fun v hv A hA σ hσ => ?_, fun g g' h => ?_, fun P hP A hA σ hσ => ?_⟩
  · rw [MonoidHom.comp_apply, (hr.unr_iff ha (Or.inl fun h => hv (hS1 h)) hA).2 (hunr v hv) σ hσ, map_one]
  · obtain ⟨x, hx, ex⟩ := exists_unit ha hA hσ
    have hv' := (hmem v).1 hv
    obtain ⟨n, hn⟩ := (GlobalTheory.Mem.WildChar.orders_on_units _ χ v).2 (hχw v hv) x hx
    have e1 := hr.loc (Or.inl (notMem_of_ne hp hl hpl hv')) ex
    rw [HChar.loc_mul, HChar.loc_mul, HChar.loc_inv,
      (C.isMu0 _).unr v (fun k => notMem_of_ne hp (H.g_prime k) (hpg k) hv') x hx, one_mul] at e1
    have e2 := hd.side hm0 hm b ex
    refine ⟨n, ?_⟩
    rw [MonoidHom.comp_apply, ← map_inv, ← map_mul, ← map_pow,
      (pow_eq_one_iff_of_val (κ := κ) (ι := sideIso ι b) (z := (χ.loc v x)⁻¹) ?_ _).2 (by rw [inv_pow, hn, inv_one]), map_one]
    rw [Units.val_mul, map_mul, map_mul, map_units_inv, map_inv₀, e1, e2, Units.val_mul,
      mul_comm, inv_mul_cancel_left₀ (Units.ne_zero _)]
  · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hA g g' h, map_inv]
  · have hPl : ((l : ℕ) : 𝓞 H.E) ∉ P.asIdeal := fun h => hP (hS1 h)
    have e1 := (hr.frob ha (Or.inl hPl) (hunr P hP) (isPlaceOver_placeOf Ω P) (isFrob_frobOf Ω P)).trans
      (hr.frob ha (Or.inl hPl) (hunr P hP) hA hσ).symm
    exact congrArg (algebraMap O O') (toQ_injective κ ((sideIso ι b).injective e1))

theorem hostHeckeFrame_localisation_character_spec (hcc : IsCMConjOm H.E Ω cc) (ha : IsGlobalArtin art) (he : ∀ j τ, ∃ z : ℤ, e j τ = z) :
    LocalisationCharacterSpec H cc C art := by
  intro l _ O _ _ _ _ _ _ _ hO κ hκ ι K _ ε f hf j Q ψ hψ hQ hμ hη hδ hψv
  have hl : l.Prime := Fact.out
  obtain ⟨hp, hpl, hpg, -, hD⟩ := inertialOrderFifteenChar_auxiliaryPrime_spec C (l := l)
  obtain ⟨a, ha'⟩ := hψ.ord
  have hla : 0 < l ^ a := pow_pos hl.pos a
  have hψa := isAlgPos_zero_of_orderDvd hla ha'
  obtain ⟨ps, hps⟩ := exists_isGal hO hκ ha hψa hf (almostIn_of_valuesIn hψv)
  obtain ⟨n0, h0⟩ := exists_isAlgPos_mu0 C he j
  obtain ⟨n, hn⟩ := block_alg C ⟨_, isAlgPos_mul h0 (isAlgPos_mul (del_alg C l) hψa)⟩
  obtain ⟨r, hr⟩ := exists_isGal hO hκ ha hn hf
    (((almostIn_of_valuesIn hμ).mul ((almostIn_of_valuesIn hδ).mul (almostIn_of_valuesIn hψv))).block hη (odd_r R))
  let cy : G H.E Ω →* Oˣ := (Units.map (algebraMap ℤ_[l] O).toMonoidHom).comp (cycZ (F := H.E) (Ω := Ω) l)
  have hcy : Continuous cy := continuous_units cy (continuous_cyc hO hκ)
  have h1 : r * cy ^ (-(((1 : ℕ) : ℤ) - 1)) = r := by simp
  refine ⟨fun c => r * cy ^ (-((c : ℤ) - 1)), ps, ⟨n, by beta_reduce; rw [h1]; exact hr⟩, hps, fun c => ?_, fun c => by beta_reduce; rw [h1],
    fun v hv A hA => ?_, fun g => ⟨a, hps.pow_eq_one ha ha' g⟩, hps.isOpen_ker hO hκ ha hla ha',
    hps.anti hcc ha (hps.cont hO hκ) hψ.triv, hps.ramExactly ha hψ.ram,
    fun v hv A hA σ hσ => hps.dec_triv hO hκ ha hA (hψ.atl v hv) hσ, fun w w1 w2 w3 w4 => ?_⟩
  · exact Units.continuous_val.comp ((continuous_units r hr.2.1).mul (hcy.zpow _))
  · beta_reduce
    rw [h1]
    have hvl : ((l : ℕ) : 𝓞 H.E) ∉ v.asIdeal := fun h => (hψ.ram v).1 (fun x _ => hψ.atl v h x) hv
    by_contra hn
    push Not at hn
    refine (hψ.ram v).1 (fun x hx => ?_) hv
    have := (hr.unr_iff ha (Or.inl hvl) hA).1 hn x hx
    rwa [block_loc (C.isEta.unr v) hx, HChar.loc_mul, HChar.loc_mul, (C.isMu0 j).unr v (hQ v hv).1 x hx,
      hD.unr v (hQ v hv).2 x hx, one_mul, one_mul] at this
  · have hu : (C.mu0 j * (delAt H C l * ψ)).UnrAt w := ((C.isMu0 j).unr w w2).mul ((hD.unr w w3).mul ((hψ.ram w).2 w4))
    refine ⟨hu.mul (C.isEta.unr w).inv, fun B σ hB hσ => ?_⟩
    beta_reduce
    rw [h1]
    have e1 := hr.frob ha (Or.inl w1) (fun x hx => (block_loc (C.isEta.unr w) hx).trans (hu x hx)) hB hσ
    rw [block_val, mul_inv, ← Complex.cpow_neg, ← Units.val_inv_eq_inv_val] at e1
    refine Eq.trans ?_ e1.symm
    congr 2
    unfold Ranks.nV
    push_cast
    ring

theorem hostFrame_localisationTwistCharacterCompat (ha : IsGlobalArtin art) : LocalisationTwistCharacterCompat H C art := by
  intro l₀ _ O₀ _ _ _ _ _ _ _ hO₀ κ₀ hκ₀ ι₀ l _ O _ _ _ _ _ _ _ hO κ hκ ι hll K _ ε f₀ f hf₀ hf t ht j ψ hμ hη hδ
    n₀ n n' chi1 chi psiL h1 h2 h3
  have hl : l.Prime := Fact.out
  have hl0 : ((l : ℕ) : O₀) ≠ 0 := fun h => by
    have := congrArg (toQ κ₀) h
    rw [map_natCast, map_zero] at this
    exact hl.ne_zero (by exact_mod_cast this)
  have htc := continuous_ringHom hO₀ hO hl0 (GlobalTheory.CoefEmbed.embedding_closed_integral l O hO κ hκ).2.2.2 t
  haveI : T2Space O := (isEmbedding_toQ hO hκ).t2Space
  have hb : block (C.mu0 j * (delAt H C l * ψ)) C.eta R.r = block (C.mu0 j * delAt H C l₀) C.eta R.r * ψ := by
    rw [hll, block, block, ← mul_assoc (C.mu0 j), mul_right_comm]
  rw [hb] at h2
  refine eq_of_frob ha (continuous_units _ h2.2.1)
    ((continuous_units ((Units.map t.toMonoidHom).comp chi1) (htc.comp h1.2.1)).mul (continuous_units _ h3.2.1)) ?_
  filter_upwards [(((almostIn_of_valuesIn hμ).mul (almostIn_of_valuesIn hδ)).block hη (odd_r R)).inv, unr_ae ψ,
    unr_ae (block (C.mu0 j * delAt H C l₀) C.eta R.r), away_ae (E := H.E) l hl.ne_zero] with v ⟨y, hy⟩ u1 u2 hv A hA σ hσ
  have e1 := h1.frob ha (Or.inl (hll ▸ hv)) u2 hA hσ
  have e2 := h2.frob ha (Or.inl hv) (u2.mul u1) hA hσ
  have e3 := h3.frob ha (Or.inl hv) u1 hA hσ
  rw [HChar.val_inv, Units.val_inv_eq_inv_val] at hy
  have e4 := ht y (chi1 σ : O₀ˣ) (κ₀.injective (ι₀.injective (e1.trans (hy.symm.trans (hf₀ y).symm))))
  refine Units.ext (toQ_injective κ (ι.injective ?_))
  rw [e2, MonoidHom.mul_apply, Units.val_mul, map_mul, map_mul, e3, HChar.val_mul, Units.val_mul, mul_inv, ← hy, ← hf, e4]
  rfl

theorem range_eq_rootsOfUnity {Γ : Type} [CommGroup Γ] [Finite Γ] (χ : Γ →* ℂˣ) (hχ : Function.Injective χ) :
    χ.range = rootsOfUnity (Nat.card Γ) ℂ := by
  haveI : NeZero (Nat.card Γ) := ⟨Nat.card_pos.ne'⟩
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨y, rfl⟩
    rw [mem_rootsOfUnity, ← map_pow, pow_card_eq_one', map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hχ).toEquiv]
    exact card_rootsOfUnity ℂ (Nat.card Γ)

theorem mu0_loc_eq_inv_om_pow_of_div_of_absNorm_eq {k : Fin 2} {w : PlE H} (hw : C.P.Div k w) (hN : Ideal.absNorm w.asIdeal = H.g k)
    {x : (w.adicCompletion H.E)ˣ} (hx : IsUnitAt w x) :
    ∃ a : (ZMod (H.g k))ˣ, ∀ j : Fin R.m, (C.mu0 j).loc w x = (C.W.om k a ^ (2 * (j.1 + 1)))⁻¹ := by
  obtain ⟨a, y, ha, hy, h⟩ := (GlobalTheory.localUnit_congr_global H.E w x hx).2 _ (H.g_prime k) hN
  refine ⟨ZMod.unitOfCoprime a ha, fun j => ?_⟩
  have hu := isUnitAt_nat (C.P.overP hw) ha hy
  have h1 := (C.isMu0 j).tame w (x * (atFin w y)⁻¹) (by
    unfold IsUnitAt at *
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hx, hu, inv_one, mul_one]) (by simpa using h)
  rw [map_mul, map_inv, mul_inv_eq_one] at h1
  rw [h1]
  exact (C.isMu0 j).atg k w hw a ha y hy

theorem hostHeckeFrame_tame_galois_characters (ha : IsGlobalArtin art) (he : ∀ j τ, ∃ z : ℤ, e j τ = z)
    (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) : TameInertiaGeneratorCharacterSpec H C art := by
  intro k w hw A hA tg htg teich hinj
  haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩
  have hwg := C.P.overP hw
  have hN := (GlobalTheory.Mem.Chr.splitsC_main R H _ (H.g_prime k) (hg k) w hwg).1
  obtain ⟨x, hx, ex⟩ := exists_unit ha hA htg.1
  obtain ⟨a, hxa⟩ := mu0_loc_eq_inv_om_pow_of_div_of_absNorm_eq C hw hN hx

  have hsq : ∀ b : (ZMod (H.g k))ˣ, b ^ 2 ∈ Subgroup.zpowers (a ^ 2) := by
    intro b
    haveI : Fact H.pde.Prime := ⟨H.pde_prime⟩
    obtain ⟨ι⟩ := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex H.pde
    have hm := R.two_le_m
    let j0 : Fin R.m := ⟨0, by omega⟩
    obtain ⟨n, hn⟩ := exists_isAlgPos_mu0 C he j0
    obtain ⟨r, hr, hL⟩ := ha.exists_isLAdicOf ι hn
    have hv : ((H.pde : ℕ) : 𝓞 H.E) ∉ w.asIdeal := notMem_of_ne (H.g_prime k) H.pde_prime (H.pde_ne_g k).1.symm hwg
    have hg1 : ((H.g k - 1 : ℕ) : 𝓞 H.E) ∉ w.asIdeal := fun h => by
      apply w.isPrime.ne_top
      rw [Ideal.eq_top_iff_one]
      have := w.asIdeal.sub_mem hwg h
      rwa [Nat.cast_sub (H.g_prime k).one_le, Nat.cast_one, sub_sub_cancel] at this
    have hcb := ZMod.val_coe_unit_coprime b
    have hb0 : (((b : ZMod (H.g k)).val : ℕ) : H.E) ≠ 0 := by
      rw [Nat.cast_ne_zero]
      intro h
      rw [h, Nat.coprime_zero_left] at hcb
      exact (H.g_prime k).ne_one hcb
    have hy := isUnitAt_nat hwg hcb (x := Units.mk0 _ hb0) rfl
    have hyb : (C.mu0 j0).loc w (atFin w (Units.mk0 _ hb0)) = _ := (C.isMu0 j0).atg k w hw _ hcb (Units.mk0 _ hb0) rfl
    have hu' : ZMod.unitOfCoprime _ hcb = b := by
      ext
      rw [ZMod.coe_unitOfCoprime, ZMod.natCast_zmod_val]
    rw [hu'] at hyb
    obtain ⟨σ, hσ, eσ⟩ := exists_ine ha hA hy
    obtain ⟨s, hs⟩ := GlobalTheory.TameGenPowers.mem_zpowers_of_tameGen H.E Ω w A hA tg htg (Qbar H.pde) r hr (H.g k - 1) hg1 (fun τ hτ => by
      obtain ⟨z, hz, ez⟩ := exists_unit ha hA hτ
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, hL.loc_away (Or.inl hv) z τ ez, ← map_pow, ← Units.val_pow_eq_pow_val, ← hN,
        (GlobalTheory.Mem.WildChar.orders_on_units _ _ w).1 ((C.isMu0 j0).tame w) z hz]
      simp) σ hσ
    have h1 := congrArg (fun u : (Qbar H.pde)ˣ => ι (u : Qbar H.pde)) hs
    simp only [Units.val_zpow_eq_zpow_val, map_zpow₀, hL.loc_away (Or.inl hv) _ _ ex, hL.loc_away (Or.inl hv) _ _ eσ,
      RingEquiv.apply_symm_apply, hxa j0, hyb] at h1
    rw [← Units.val_zpow_eq_zpow_val, Units.val_inj, inv_zpow, inv_inj] at h1
    refine ⟨s, C.W.gen k ?_⟩
    simp only [map_zpow, map_pow]
    exact h1
  obtain ⟨γ, hγ, hγa⟩ := GlobalTheory.exists_generator_sq_eq_of_sq_mem_zpowers (H.g k) (H.g_prime k) a hsq
  let tU : (ZMod (H.g k))ˣ →* ℂˣ := Units.map (teich.comp
    (algebraMap (ZMod (H.g k)) (Formalism.CyclotomicNorms.Fbar (H.g k)) : ZMod (H.g k) →* Formalism.CyclotomicNorms.Fbar (H.g k)))
  have htU : Function.Injective tU := fun y z h => by
    have hi := (algebraMap (ZMod (H.g k)) (Formalism.CyclotomicNorms.Fbar (H.g k))).injective
    exact Units.ext (hi (hinj _ _ ((map_ne_zero_iff _ hi).2 y.ne_zero) ((map_ne_zero_iff _ hi).2 z.ne_zero)
      (congrArg Units.val h)))
  have hr : (C.W.om k).range = tU.range :=
    (range_eq_rootsOfUnity _ (C.W.gen k)).trans (range_eq_rootsOfUnity _ htU).symm
  obtain ⟨γ', hγ'⟩ : C.W.om k γ ∈ tU.range := hr ▸ ⟨γ, rfl⟩
  refine ⟨γ', ?_, fun l _ hl O _ _ _ κ ι j ξ hξ n chi h => ?_⟩
  · rw [eq_top_iff]
    intro y _
    obtain ⟨z, hz⟩ : tU y ∈ (C.W.om k).range := hr.symm ▸ ⟨y, rfl⟩
    obtain ⟨n, rfl⟩ : z ∈ Subgroup.zpowers γ := hγ ▸ Subgroup.mem_top z
    refine ⟨n, htU ?_⟩
    rw [← hz, map_zpow, map_zpow, hγ']
  · have e1 := h.loc (Or.inl (notMem_of_ne (H.g_prime k) Fact.out hl.symm hwg)) ex
    rw [block_loc (C.isEta.unr w) hx, HChar.loc_mul, hξ x hx, mul_one, hxa j, pow_mul, ← map_pow, ← hγa, map_pow, ← hγ',
      ← pow_mul, ← map_pow, ← map_inv] at e1
    exact e1

end Host

theorem galois_characters_of_artin (R : Ranks) (H : Formalism.BasicNotions.Host R) (Ω : Type) [Field Ω] [Algebra H.E Ω]
    [IsAlgClosure H.E Ω] (cc : Ω ≃+* Ω) (hcc : IsCMConjOm H.E Ω cc) (e : Fin R.m → R.Psi → ℚ)
    (he : ∀ j τ, ∃ z : ℤ, e j τ = z) (C : GlobalTheory.Mem.Chr.HFrame H e)
    (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) (art : Ideles H.E →* Gab H.E Ω)
    (ha : IsGlobalArtin art) :
    HeckeTwistCharactersDeltaChi H cc C art ∧ ToricHeckeQuotientCharacter H cc C art ∧ LocalisationCharacterSpec H cc C art ∧ LocalisationTwistCharacterCompat H C art ∧ TameInertiaGeneratorCharacterSpec H C art ∧
      ∀ l : ℕ, UniversalAnticyclotomicCharLaws H cc l :=
  ⟨hostHeckeFrame_twist_galois_characters C hcc ha he hg, hostHeckeFrame_toric_quotient_character C hcc ha he, hostHeckeFrame_localisation_character_spec C hcc ha he, hostFrame_localisationTwistCharacterCompat C ha, hostHeckeFrame_tame_galois_characters C ha he hg,
    fun l => universal_anticyclotomic_character_laws H cc l⟩

end GlobalTheory.GalChar

end
