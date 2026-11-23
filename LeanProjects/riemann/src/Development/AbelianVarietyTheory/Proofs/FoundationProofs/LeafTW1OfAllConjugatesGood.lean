import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaSeriesTies
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.PlaceBelowAllPowers
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GoodPartMemBasisSeries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LenRBaseChangeSubquotient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCommensurableOfIsLatIn
import Formalism.LocalToGlobal.Columns.LocWLemmas
import Formalism.SharpRestriction.LevelLetterCocycles.TwGood
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TwistIndex

open NumberField IsDedekindDomain
open scoped TensorProduct

section Local

open Formalism.L2.Col Formalism.EigenvalueLevelCeiling

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}
  {O' : Type} [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] {emb : K →+* FractionRing O'}

def Induces (emb : K →+* FractionRing O') (v : HeightOneSpectrum (𝓞 K)) : Prop :=
  ∀ x : K, v.valuation K x ≤ 1 ↔ emb x ∈ (algebraMap O' (FractionRing O')).range

def Induces.hom (h : Induces emb v) : Ow v →+* O' :=
  ((RingEquiv.ofBijective (algebraMap O' (FractionRing O')).rangeRestrict
    ⟨fun _ _ e => IsFractionRing.injective O' (FractionRing O') (congrArg Subtype.val e),
      RingHom.rangeRestrict_surjective _⟩).symm : _ →+* O').comp
    ((emb.comp (algebraMap (Ow v) K)).codRestrict _ fun r => (h _).1 ((mem_range_ow_iff v _).1 ⟨r, rfl⟩))

omit [IsDomain O'] [IsDiscreteValuationRing O'] in
theorem Induces.hom_spec (h : Induces emb v) (r : Ow v) :
    algebraMap O' (FractionRing O') (h.hom r) = emb (algebraMap (Ow v) K r) :=
  congrArg Subtype.val ((RingEquiv.ofBijective (algebraMap O' (FractionRing O')).rangeRestrict
    ⟨fun _ _ e => IsFractionRing.injective O' (FractionRing O') (congrArg Subtype.val e),
      RingHom.rangeRestrict_surjective _⟩).apply_symm_apply _)

theorem Induces.hom_injective (h : Induces emb v) : Function.Injective h.hom := fun a b e =>
  algebraMap_ow_injective v (emb.injective (by rw [← h.hom_spec, ← h.hom_spec, e]))

theorem Induces.hom_local (h : Induces emb v) : IsLocalHom h.hom := by
  refine ⟨fun r hr => ?_⟩
  obtain ⟨s, hs⟩ := hr.exists_right_inv
  have e : emb (algebraMap (Ow v) K r) * algebraMap O' (FractionRing O') s = 1 := by
    rw [← h.hom_spec, ← map_mul, hs, map_one]
  have r0 : algebraMap (Ow v) K r ≠ 0 := fun h0 => by simp [h0] at e
  obtain ⟨t, ht⟩ := (mem_range_ow_iff v _).2 ((h (algebraMap (Ow v) K r)⁻¹).2
    ⟨s, by rw [map_inv₀]; exact eq_inv_of_mul_eq_one_right e⟩)
  refine IsUnit.of_mul_eq_one t (algebraMap_ow_injective v ?_)
  rw [map_mul, ht, mul_inv_cancel₀ r0, map_one]

variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  {W : Type} [AddCommGroup W] [Module (FractionRing O') W] [Module O' W] [IsScalarTower O' (FractionRing O') W]

omit [IsScalarTower (𝓞 K) K V] in

theorem relLength_read (h : Induces emb v) (rd : V →ₛₗ[emb] W) {ι : Type} [Fintype ι] (b : Module.Basis ι K V)
    (hli : LinearIndependent (FractionRing O') fun a => rd (b a)) :
    ∃ e : ℕ, 0 < e ∧ (∀ n : ℕ, IsDiscreteValuationRing.addVal O' (n : O') =
        IsDiscreteValuationRing.addVal (Ow v) (n : Ow v) * e) ∧
      ∀ A B : Submodule (𝓞 K) V,
        relLength (Submodule.span O' (rd '' A)) (Submodule.span O' (rd '' B)) = lenW v A B * e := by
  let _ : Algebra (Ow v) O' := h.hom.toAlgebra
  have : IsLocalHom (algebraMap (Ow v) O') := h.hom_local
  have : FaithfulSMul (Ow v) O' := (faithfulSMul_iff_algebraMap_injective _ _).2 h.hom_injective
  let _ : Module (Ow v) W := Module.compHom W h.hom
  have : IsScalarTower (Ow v) O' W := ⟨fun r s x => mul_smul (h.hom r) s x⟩
  have hr : ∀ (r : Ow v) (x : V), rd (r • x) = h.hom r • rd x := fun r x => by
    rw [ow_smul_def, map_smulₛₗ, ← h.hom_spec, algebraMap_smul]
  let r : V →ₗ[Ow v] W := ⟨rd.toAddHom, hr⟩
  let g : O' ⊗[Ow v] V →ₗ[O'] W := r.liftBaseChange O'
  have hg : ∀ (s : O') (x : V), g (s ⊗ₜ x) = s • rd x := fun s x => LinearMap.liftBaseChange_tmul _ _ _ _
  have hnorm : ∀ t : O' ⊗[Ow v] V, ∃ c : Ow v, c ≠ 0 ∧ ∃ s : ι → O', c • t = ∑ a, s a ⊗ₜ b a := by
    intro t
    induction t with
    | zero => exact ⟨1, one_ne_zero, 0, by simp⟩
    | tmul s x =>
      obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (Ow v)) (b.repr x)
      choose y hy using hc
      refine ⟨c, nonZeroDivisors.coe_ne_zero c, fun a => y a • s, ?_⟩
      rw [← TensorProduct.tmul_smul]
      conv_lhs => rw [← b.sum_repr x, Finset.smul_sum, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [TensorProduct.smul_tmul, ← smul_assoc, ← hy a, algebraMap_smul]
    | add x y hx hy =>
      obtain ⟨c, hc, s, hs⟩ := hx
      obtain ⟨d, hd, u, hu⟩ := hy
      refine ⟨c * d, mul_ne_zero hc hd, d • s + c • u, ?_⟩
      rw [smul_add, mul_comm c d, mul_smul, hs, mul_comm d c, mul_smul, hu, Finset.smul_sum, Finset.smul_sum,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [Pi.add_apply, Pi.smul_apply, TensorProduct.add_tmul, TensorProduct.smul_tmul']
  have hinj : Function.Injective g := by
    rw [injective_iff_map_eq_zero]
    intro t ht
    obtain ⟨c, hc, s, hs⟩ := hnorm t
    have h1 : ∑ a, algebraMap O' (FractionRing O') (s a) • rd (b a) = 0 := by
      have := congrArg g hs
      rw [← algebraMap_smul O' c, map_smul, ht, smul_zero, map_sum] at this
      simpa only [hg, algebraMap_smul] using this.symm
    have h2 : ∀ a, s a = 0 := fun a => (map_eq_zero_iff _ (IsFractionRing.injective O' (FractionRing O'))).1
      (Fintype.linearIndependent_iff.1 hli _ h1 a)
    have h3 : c • t = 0 := by simp [hs, h2]
    have cK : algebraMap (Ow v) K c ≠ 0 := (map_ne_zero_iff _ (algebraMap_ow_injective v)).2 hc
    let f : V →ₗ[Ow v] V := (((algebraMap (Ow v) K c)⁻¹ • LinearMap.id : V →ₗ[K] V)).restrictScalars (Ow v)
    have h4 : ∀ u : O' ⊗[Ow v] V, f.lTensor O' (c • u) = u := by
      intro u
      induction u with
      | zero => simp
      | tmul s x =>
        rw [← TensorProduct.tmul_smul, LinearMap.lTensor_tmul]
        congr 1
        exact inv_smul_smul₀ cK x
      | add x y hx hy => rw [smul_add, map_add, hx, hy]
    rw [← h4 t, h3, map_zero]
  have hsp : ∀ A : Submodule (𝓞 K) V, Submodule.span O' (rd '' A) = ((atW v A).baseChange O').map g := by
    intro A
    rw [atW, Submodule.baseChange_span, Submodule.map_span, Set.image_image]
    congr 1
    exact Set.image_congr fun x _ => by simp [hg]
  refine ⟨_, ramificationIdx_maximalIdeal_pos (Ow v) O', fun n => ?_, fun A B => ?_⟩
  · rw [← addVal_algebraMap O', map_natCast (algebraMap (Ow v) O')]
  · rw [hsp, hsp, relLength_map_of_injective g hinj]
    exact length_baseChange_subquotient_dvr (Ow v) O' _ _

omit [NumberField K] [IsDomain O'] [IsDiscreteValuationRing O'] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Module O' W]
  [IsScalarTower O' (FractionRing O') W] in

theorem exists_read {ι : Type} [Fintype ι] (b : Module.Basis ι K V) (x : ι → W) :
    ∃ rd : V →ₛₗ[emb] W, ∀ a, rd (b a) = x a := by
  classical
  refine ⟨⟨⟨fun y => ∑ a, emb (b.repr y a) • x a, fun y z => ?_⟩, fun r y => ?_⟩, fun a => ?_⟩
  · simp [add_smul, Finset.sum_add_distrib]
  · simp [mul_smul, Finset.smul_sum]
  · simp [Finsupp.single_apply, apply_ite emb]

variable [StarRing K]

theorem plc_eq_prW (v : HeightOneSpectrum (𝓞 K)) : plc v = prW v := eq_prW_of_mem v (plc_prime v) (plc_mem v)

theorem addVal_plc (v : HeightOneSpectrum (𝓞 K)) :
    (((IsDiscreteValuationRing.addVal (Ow v) ((plc v : ℕ) : Ow v)).toNat : ℕ) : ℤ) = ramw v := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (Ow v)
  obtain ⟨u, hu⟩ := prW_eq_unit_mul_pow v hπ
  rw [plc_eq_prW, IsDiscreteValuationRing.addVal_def _ u hπ _ hu, ENat.toNat_natCast]
  exact Formalism.L2.DIV.lf_eW_eq_ramw v

omit [StarRing K] in
theorem lix_eq_signedLength (v : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) V) :
    lix v A B = signedLength (atW v A) (atW v B) := by
  rw [lix, ← lidxW_eq_lidx, lidxW, lenW_inf, inf_comm, lenW_inf]
  rfl

theorem lix_le_of_read (h : Induces emb v) (rd : V →ₛₗ[emb] W) {ι : Type} [Fintype ι] (b : Module.Basis ι K V)
    (hli : LinearIndependent (FractionRing O') fun a => rd (b a)) {Z : Submodule K V} {M Θ X : Submodule (𝓞 K) V}
    (hM : IsLatIn Z M) (hΘ : IsLatIn Z Θ)
    (hc : LengthCommensurable (Submodule.span O' (rd '' Θ)) (Submodule.span O' (rd '' X))) {ε : ℝ}
    (hs : Formalism.MainNotions.IntegralHeckeForms.sIdx (plc v) (Submodule.span O' (rd '' Θ)) (Submodule.span O' (rd '' X)) ≤ ε) :
    (lix v M X : ℝ) ≤ (lix v M Θ : ℝ) + (ramw v : ℝ) * ε := by
  obtain ⟨e, he, hv, hl⟩ := relLength_read h rd b hli
  have key : ∀ {A B : Submodule (𝓞 K) V}, IsLatIn Z A → IsLatIn Z B → relLength (atW v A) (atW v B) ≠ ⊤ := by
    intro A B hA hB
    refine relLength_ne_top_of_isLatIn (V := atW v A ⊔ atW v B) ⟨atW_fg v hA.1, le_sup_left, fun x hx => ?_⟩
      ⟨atW_fg v hB.1, le_sup_right, fun x hx => ?_⟩
    all_goals
      have hx' : x ∈ Z := by
        refine (sup_le ?_ ?_ : _ ≤ Z.restrictScalars (Ow v)) hx
        · exact Submodule.span_le.2 fun y hy => hA.2.le (Submodule.subset_span hy)
        · exact Submodule.span_le.2 fun y hy => hB.2.le (Submodule.subset_span hy)
    · rw [← hA.2] at hx'
      obtain ⟨c, hc⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (Ow v)) K _ x hx'
      exact ⟨c, nonZeroDivisors.coe_ne_zero c, hc⟩
    · rw [← hB.2] at hx'
      obtain ⟨c, hc⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (Ow v)) K _ x hx'
      exact ⟨c, nonZeroDivisors.coe_ne_zero c, hc⟩
  have e0 : (e : ℕ∞) ≠ 0 := by exact_mod_cast he.ne'
  have hfin : ∀ {A B : Submodule (𝓞 K) V},
      relLength (Submodule.span O' (rd '' A)) (Submodule.span O' (rd '' B)) ≠ ⊤ → relLength (atW v A) (atW v B) ≠ ⊤ := by
    intro A B h1 h2
    rw [hl, show lenW v A B = ⊤ from h2, ENat.top_mul e0] at h1
    exact h1 rfl
  have c1 : LengthCommensurable (atW v M) (atW v Θ) := ⟨key hM hΘ, key hΘ hM⟩
  have c2 : LengthCommensurable (atW v Θ) (atW v X) := ⟨hfin hc.1, hfin hc.2⟩
  have hr : (0 : ℝ) < ramw v := by exact_mod_cast lt_of_lt_of_le zero_lt_one (one_le_ramw v)
  have hp : (((IsDiscreteValuationRing.addVal (Ow v) ((plc v : ℕ) : Ow v)).toNat : ℕ) : ℝ) = ramw v := by
    exact_mod_cast addVal_plc v
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  have h3 : signedLength (Submodule.span O' (rd '' Θ)) (Submodule.span O' (rd '' X)) =
      signedLength (atW v Θ) (atW v X) * e := by
    rw [signedLength, hl, hl, ENat.toNat_mul, ENat.toNat_mul, ENat.toNat_natCast, signedLength, _root_.sub_mul]
    push_cast
    rfl
  rw [sIdx_eq_signedLength_div, h3, hv, ENat.toNat_mul, ENat.toNat_natCast, Nat.cast_mul, hp, Int.cast_mul, Int.cast_natCast,
    mul_div_mul_right _ _ he'.ne', div_le_iff₀ hr] at hs
  rw [lix_eq_signedLength, lix_eq_signedLength, c1.signedLength_eq_add c2]
  push_cast
  linarith

end Local

section Export

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.IntegralHeckeForms GlobalTheory.ExportCompare
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
  (Y : NExp D.R D.host D.what₂ D.LL0 N X) (E : ExpDat Y) (i : X.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
  (φ : G D.host.E N.Om →* (X.Ok i k)ˣ)
  (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra (X.O i) O'] [Algebra (X.Ok i k) O']
  [IsScalarTower (X.O i) (X.Ok i k) O']
  {K : Type} [Field K] [NumberField K] {emb : K →+* FractionRing O'}
  {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

def Reads (e : V →ₗ[K] V) (Θ Θψ : Submodule (𝓞 K) V) (rd : V →ₛₗ[emb] FmExt Y i j b O') : Prop :=
  (∃ (n : ℕ) (β : Module.Basis (Fin n) K V), LinearIndependent (FractionRing O') fun a => rd (β a)) ∧
  (∀ x, rd (e x) = eExt Y i j b O' (rd x)) ∧
  Submodule.span O' (rd '' Θ) =
    Submodule.span O' ((fun a => (1 : FractionRing O') ⊗ₜ[X.O i] Y.th i j b a) '' SgJ Y E i j b) ∧
  Submodule.span O' (rd '' Θψ) =
    Submodule.span O' (incl Y i j b O' k '' ⋃ a ∈ SgJ Y E i j b, Y.thPsi i j b k Q φ a)

variable {Y E i j b k Q φ O'}

omit [IsDomain O'] [IsDiscreteValuationRing O'] [NumberField K] in

theorem Reads.comap {V' : Type} [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
    {e : V →ₗ[K] V} {Θ Θψ : Submodule (𝓞 K) V} {rd : V →ₛₗ[emb] FmExt Y i j b O'}
    (h : Reads Y E i j b k Q φ O' e Θ Θψ rd) (f : V' →ₗ[K] V) (hf : Function.Bijective f) {e' : V' →ₗ[K] V'}
    (he : f ∘ₗ e' = e ∘ₗ f) :
    Reads Y E i j b k Q φ O' e' (Θ.comap (f.restrictScalars (𝓞 K))) (Θψ.comap (f.restrictScalars (𝓞 K))) (rd.comp f) := by
  obtain ⟨⟨n, β, hβ⟩, h2, h3, h4⟩ := h
  have him : ∀ L : Submodule (𝓞 K) V, (rd.comp f) '' (L.comap (f.restrictScalars (𝓞 K))) = rd '' L := fun L => by
    rw [LinearMap.coe_comp, Set.image_comp]
    exact congrArg _ (Set.image_preimage_eq _ hf.2)
  refine ⟨⟨n, β.map (LinearEquiv.ofBijective f hf).symm, ?_⟩, fun x => ?_, by rw [him, h3], by rw [him, h4]⟩
  · convert hβ using 2 with a
    exact congrArg rd ((LinearEquiv.ofBijective f hf).apply_symm_apply _)
  · exact (congrArg rd (LinearMap.congr_fun he x)).trans (h2 _)

theorem Reads.lix_le [StarRing K] {v : HeightOneSpectrum (𝓞 K)} {e : V →ₗ[K] V} {Θ Θψ : Submodule (𝓞 K) V}
    {rd : V →ₛₗ[emb] FmExt Y i j b O'} (h : Reads Y E i j b k Q φ O' e Θ Θψ rd) (hv : Induces emb v)
    (hl : X.l i = Formalism.EigenvalueLevelCeiling.plc v) (hi : Function.Injective (algebraMap (X.Ok i k) O')) (hf : Module.Finite (X.Ok i k) O')
    (h0 : IsLatIn (eTh Y i j b (SgJ Y E i j b)) ((V0 Y i j b).restrictScalars (X.O i)))
    (h1 : IsLatIn (eThPsi Y i j b k Q φ (SgJ Y E i j b)) (((V0 Y i j b).restrictScalars (X.O i)).baseChange (X.Ok i k)))
    {ε : ℝ} (h2 : IdxAt Y i j b (SgJ Y E i j b) k Q φ ε) {Z : Submodule K V} {M : Submodule (𝓞 K) V}
    (hM : Formalism.EigenvalueLevelCeiling.IsLatIn Z M) (hΘ : Formalism.EigenvalueLevelCeiling.IsLatIn Z (Θ.map (e.restrictScalars (𝓞 K)))) :
    (Formalism.EigenvalueLevelCeiling.lix v M (Θψ.map (e.restrictScalars (𝓞 K))) : ℝ) ≤
      (Formalism.EigenvalueLevelCeiling.lix v M (Θ.map (e.restrictScalars (𝓞 K))) : ℝ) + (Formalism.EigenvalueLevelCeiling.ramw v : ℝ) * ε := by
  obtain ⟨⟨n, β, hβ⟩, g2, g3, g4⟩ := h
  have hi' : Function.Injective (algebraMap (X.O i) O') := by
    rw [IsScalarTower.algebraMap_eq (X.O i) (X.Ok i k) O']
    exact hi.comp (X.Ok_inj i k)
  have hmap : ∀ L : Submodule (𝓞 K) V, Submodule.span O' (rd '' (L.map (e.restrictScalars (𝓞 K)))) =
      (Submodule.span O' (rd '' L)).map (eExt Y i j b O') := fun L => by
    rw [Submodule.map_span, Submodule.map_coe, Set.image_image, Set.image_image]
    exact congrArg _ (Set.image_congr fun x _ => g2 x)
  have eΘ : Submodule.span O' (rd '' (Θ.map (e.restrictScalars (𝓞 K)))) =
      ((eTh Y i j b (SgJ Y E i j b)).baseChange O').map (toFrac _ _ O') := by
    rw [hmap, g3, eTh, Th, Submodule.map_span, Submodule.map_span, Submodule.baseChange_span, Submodule.map_span]
    simp only [Set.image_image]
    refine congrArg _ (Set.image_congr fun a _ => ?_)
    rw [TensorProduct.mk_apply, toFrac_tmul, map_one]
    rfl
  have eX : Submodule.span O' (rd '' (Θψ.map (e.restrictScalars (𝓞 K)))) =
      (ext Y i j b O' k (eThPsi Y i j b k Q φ (SgJ Y E i j b))).map (toFrac _ _ O') := by
    rw [hmap, g4, span_incl_map]
    rfl
  have l0 := isLatIn_baseChange O' hi' h0
  have l1 : IsLatIn (ext Y i j b O' k (eThPsi Y i j b k Q φ (SgJ Y E i j b)))
      (((V0 Y i j b).restrictScalars (X.O i)).baseChange O') := by
    rw [← ext_baseChange Y i j b O' k]
    exact isLatIn_span hi _ h1
  refine lix_le_of_read hv rd β hβ hM hΘ ?_ ?_
  · rw [eΘ, eX]
    have := lengthCommensurable_of_isLatIn l0 l1
    unfold LengthCommensurable at this ⊢
    rwa [relLength_map_of_injective _ (toFrac_injective _ _ _), relLength_map_of_injective _ (toFrac_injective _ _ _)]
  · have := h2 O' hi hf _ l0
    rw [← Set.image_congr fun y _ => up_eq Y i j b O' k y, sIdx_eq (X.l i) _ ((eTh Y i j b (SgJ Y E i j b)).baseChange O'),
      signedLength, sub_self, Int.cast_zero, zero_div, zero_add] at this
    rw [eΘ, eX, sIdx_map _ (toFrac_injective _ _ _), ← hl]
    exact this

end Export

section Chain

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef Formalism.L2.Indef.Tree

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df}
  {P : Type} [Group P] [Finite P] {oc : OnConst}

def GoodPartLattice (O : OnObj S P oc) : Prop := ∀ j, IsLatIn (O.Zg j) (cut (O.Zg j) (O.Ms j))

def ThetaFullRank (O : OnObj S P oc) : Prop := AtPair S fun v => ∀ j, IsLatIn (O.Zg j) (O.eJ v j)

theorem goodPartLattice_of_leafSup {O : OnObj S P oc} (h : LeafSup O) : GoodPartLattice O := fun j => by
  obtain ⟨h1, h2⟩ := (h j).1
  refine ⟨h1.of_le inf_le_left, le_antisymm (Submodule.span_le.2 fun x hx => hx.2) fun x hx => ?_⟩
  obtain ⟨c, hc⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K _ x (h2.ge Submodule.mem_top)
  rw [Submodule.span_eq] at hc
  have c0 : algebraMap (𝓞 K) K c ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 (nonZeroDivisors.coe_ne_zero c)
  rw [← inv_smul_smul₀ c0 x, algebraMap_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨hc, ((O.Zg j).restrictScalars (𝓞 K)).smul_mem _ hx⟩)

theorem leafTW1_of_places {O : OnObj S P oc}
    (h : AtPair S fun v => (∀ j, 0 ≤ O.ε0 v j ∧ (lix v (cut (O.Zg j) (O.Ms j)) (O.X₃ v j) : ℝ) ≤
      (lix v (cut (O.Zg j) (O.Ms j)) (O.eJ v j) : ℝ) + (ramw v : ℝ) * O.ε0 v j) ∧ ∑ j, O.ε0 v j ≤ ((plc v : ℝ) ^ 2)⁻¹) :
    LeafTW1 O := by
  refine ⟨fun w hw => ⟨(h w hw).1.1, (h w hw).2.1⟩, fun w hw => ?_⟩
  have h1 := (h w hw).1.2
  have h2 := (h w hw).2.2
  rw [plc_conjPl] at h2
  rw [Finset.sum_add_distrib, div_eq_mul_inv]
  linarith

theorem sum_side_le {J : Type} [Fintype J] {m : ℕ} {ι : J → Fin m} (hι : Function.Injective ι) {ε : ℕ → Bool → ℝ}
    (h0 : ∀ j b, 0 ≤ ε j b) (b : Bool) : ∑ j, ε ((ι j : ℕ) + 1) b ≤ ∑ j ∈ Finset.Icc 1 m, ∑ b' : Bool, ε j b' := by
  classical
  rw [← Finset.sum_image (s := Finset.univ) (g := fun j => (ι j : ℕ) + 1) (f := fun j => ε j b)
    fun x _ y _ e => hι (Fin.ext (Nat.succ_injective e))]
  refine (Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => ?_) fun n _ _ => h0 n b).trans
    (Finset.sum_le_sum fun n _ => Finset.single_le_sum (f := ε n) (fun b' _ => h0 n b') (Finset.mem_univ b))
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hn
  exact Finset.mem_Icc.2 ⟨Nat.le_add_left _ _, (ι j).2⟩

end Chain

section Record

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
open GlobalTheory.OnTies GlobalTheory.IndefiniteRowSideFullHecke.PlaceBelowAllPowers
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem induces_embW (c : NChoice D) (w : D.what₂.places.Pl) : Induces (c.embW w) (D.plEq w) := fun x => by
  rw [← c.embW_w]
  by_cases hx : x = 0
  · subst hx
    simp
  · have h0 : (D.plEq w).valuation D.what₂.LL x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
    rw [D.val_eq w x hx, vAdd, ← WithTop.coe_zero, WithTop.coe_le_coe, neg_nonneg, ← WithZero.log_one,
      WithZero.log_le_log h0 one_ne_zero]

theorem l_eq_plc (c : NChoice D) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) :
    D.ntw.l (c.twI (D.plEq.symm v)) = Formalism.EigenvalueLevelCeiling.plc v := by
  rw [c.twI_l, ← Formalism.L2.Col.prW_D, Equiv.apply_symm_apply, plc_eq_prW]

def chosenChar (c : NChoice D) (w : D.what₂.places.Pl) : G D.host.E D.nd.Om →* (D.ntw.Ok (c.twI w) (c.k' w))ˣ :=
  (c.psi' w).comp (D.ntw.art (c.twI w) (c.Q w))

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T0 : Type} (A : FamIn D.what₂.LL Γ Pl0 T0 D.R.m)

def ExportTie (c : NChoice D) (E : IntegralHeckeForms.XD D) {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A Ks) (ι : Fin D.R.m) (U : Subgroup Γ) (ψ : U →* D.what₂.LLˣ) (ph : ℂ)
    (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (p : ℕ) : Prop :=
  ∃ rd : (Fin (R.nW ι) → D.what₂.LL) →ₛₗ[c.embW (D.plEq.symm v)]
      FmExt D.nexp (c.twI (D.plEq.symm v)) ((ι : ℕ) + 1) (c.sd (D.plEq.symm v)) (c.Oe (D.plEq.symm v)),
    Reads D.nexp E (c.twI (D.plEq.symm v)) ((ι : ℕ) + 1) (c.sd (D.plEq.symm v)) (c.k' (D.plEq.symm v)) (c.Q (D.plEq.symm v))
      (chosenChar c (D.plEq.symm v)) (c.Oe (D.plEq.symm v)) ((R.FW ι).eOp fun g => (idemOf A.X).coeff g)
      (thetaBase R ι U ψ ph v p) (thetaTuple R ι U ψ ph (R.mu v)) rd

variable {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}

def TiedAt (c : NChoice D) (E : IntegralHeckeForms.XD D) (O : OnObj S P oc) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (i : Bs.J)
    (ι : Fin D.R.m) : Prop :=
  ∃ (T : Full D) (_ : Algebra T.J.Q.c.F D.what₂.LL) (R : RealDat D A T.J.Q.c.F)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
    (h : LawsP T.toTop) (fw : FWTie T.J R κ v₀) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ)
    (wL wF : WeightFamilies.Wt D ((ι : ℕ) + 1)) (nT : ℕ)
    (z : (Fin (O.nZ i) → D.what₂.LL) ≃ₗ[D.what₂.LL]
      D.what₂.LL ⊗[(recB h.toLawsCore).KO] (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι))
    (act : P → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι) → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι))
    (inc : P →* Γ)
    (ℓ : Γ → (LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l))
    (U : Subgroup Γ) (ψ : U →* D.what₂.LLˣ) (ph : ℂ)
    (y : (Fin (O.nX v i) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fin (srcDim A ι (R.mu v) U ψ) → D.what₂.LL)),
    OnTie h fw hinj EX p ι wL wF nT O v i z act inc ℓ U ψ ph y ∧ ExportTie A c E R ι U ψ ph v p

variable {A}

theorem TiedAt.lix_le {c : NChoice D} {E : IntegralHeckeForms.XD D} {O : OnObj S P oc} {v : HeightOneSpectrum (𝓞 D.what₂.LL)} {i : Bs.J}
    {ι : Fin D.R.m} (t : TiedAt A c E O v i ι)
    (hM : Formalism.EigenvalueLevelCeiling.IsLatIn (O.Zg i) (Formalism.EigenvalueLevelCeiling.cut (O.Zg i) (O.Ms i))) (hΘ : Formalism.EigenvalueLevelCeiling.IsLatIn (O.Zg i) (O.eJ v i))
    (h0 : IntegralHeckeForms.IsLatIn (IntegralHeckeForms.eTh D.nexp (c.twI (D.plEq.symm v)) ((ι : ℕ) + 1) (c.sd (D.plEq.symm v)) (IntegralHeckeForms.SgJ D.nexp E _ _ _))
      ((IntegralHeckeForms.V0 D.nexp _ _ _).restrictScalars _))
    {ε : ℝ} (h1 : PartBAt D.nexp E (c.twI (D.plEq.symm v)) ((ι : ℕ) + 1) (c.sd (D.plEq.symm v)) (c.k' (D.plEq.symm v))
      (c.Q (D.plEq.symm v)) (chosenChar c (D.plEq.symm v)) ε) :
    (Formalism.EigenvalueLevelCeiling.lix v (Formalism.EigenvalueLevelCeiling.cut (O.Zg i) (O.Ms i)) (O.X₃ v i) : ℝ) ≤
      (Formalism.EigenvalueLevelCeiling.lix v (Formalism.EigenvalueLevelCeiling.cut (O.Zg i) (O.Ms i)) (O.eJ v i) : ℝ) + (Formalism.EigenvalueLevelCeiling.ramw v : ℝ) * ε := by
  obtain ⟨T, _, R, κ, v₀, h, fw, hinj, EX, p, wL, wF, nT, z, act, inc, ℓ, U, ψ, ph, y, t, rd, hrd⟩ := t
  have hr := hrd.comap (toForms h fw ι z) (toForms_bijective h fw ι z) t.e_eq
  have hv : Induces (c.embW (D.plEq.symm v)) v := by
    simpa using induces_embW c (D.plEq.symm v)
  unfold OnObj.eJ at hΘ ⊢
  rw [t.ThJ_eq] at hΘ ⊢
  rw [t.X₃_eq]
  exact hr.lix_le hv (l_eq_plc c v) (c.Oe_inj _) (c.Oe_fin _) h0 h1.1 h1.2.1 hM hΘ

theorem isLatIn_eTh {I : TwIn D} {i : D.ntw.Tw} (h : I.Ok i) {j : ℕ} (hj : j ∈ Finset.Icc 1 D.R.m) (b : Bool) :
    IntegralHeckeForms.IsLatIn (IntegralHeckeForms.eTh D.nexp i j b (IntegralHeckeForms.SgJ D.nexp I.E i j b)) ((IntegralHeckeForms.V0 D.nexp i j b).restrictScalars _) := by
  refine GlobalTheory.ExportCompare.eTh_isLatIn D.nexp i j b _ ⟨?_, (h.1 j hj b).2.2⟩
  have := (h.2 j hj b).2.2
  unfold TwIn.Sg at this
  rw [← this]
  exact Submodule.fg_span ((I.S i j b).finite_toSet.image _)

theorem succ_mem_Icc (ι : Fin D.R.m) : (ι : ℕ) + 1 ∈ Finset.Icc 1 D.R.m := Finset.mem_Icc.2 ⟨Nat.le_add_left _ _, ι.2⟩

def ExportInputs (bkP : BlochKatoReduction.BK D) (I : TwIn D) : Prop :=
  ∀ i, D.ntw.NonzeroIndexPlace i → BlochKatoReduction.Gen.SetHyp (BlochKatoReduction.pin bkP) i ∧ I.Ok i

abbrev Twist (i : D.ntw.Tw) : Type := Σ (Q : Finset (PlE D.host)) (k : ℕ), D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ

def ChosenFrom (c : NChoice D) (w : D.what₂.places.Pl) (i : D.ntw.Tw) (b : Bool) (t : Twist i) : Prop :=
  D.ntw.NonzeroIndexPlace i ∧ D.ntw.NonzeroIndexPlace (c.twI w) ∧ SamePlace i b (c.twI w) (c.sd w) ∧ Disjoint (c.Q w) (D.ntw.S0 (c.twI w)) ∧
    ∃ ψ' : D.ntw.RCG i (c.Q w) →* (D.ntw.Ok i (c.k' w))ˣ, (⟨c.Q w, c.k' w, ψ'⟩ : Twist i) = t ∧
      IsReading i (c.twI w) (c.k' w) (ψ'.comp (D.ntw.art i (c.Q w))) (chosenChar c w)

def IsErrorFamily (E : IntegralHeckeForms.XD D) (i : D.ntw.Tw) (t : Twist i) (ε : ℕ → Bool → ℝ) : Prop :=
  (∀ j b, 0 ≤ ε j b) ∧ ∑ j ∈ Finset.Icc 1 D.R.m, ∑ b : Bool, ε j b ≤ twEps D i ∧
    ∀ (b : Bool) (i' : D.ntw.Tw) (b' : Bool), SamePlace i b i' b' → Disjoint t.1 (D.ntw.S0 i') →
      ∀ φ : G D.host.E D.nd.Om →* (D.ntw.Ok i' t.2.1)ˣ, IsReading i i' t.2.1 (t.2.2.comp (D.ntw.art i t.1)) φ →
        ∀ j ∈ Finset.Icc 1 D.R.m,
          IntegralHeckeForms.IsLatIn (IntegralHeckeForms.eTh D.nexp i' j b' (IntegralHeckeForms.SgJ D.nexp E i' j b')) ((IntegralHeckeForms.V0 D.nexp i' j b').restrictScalars (D.ntw.O i')) →
          PartBAt D.nexp E i' j b' t.2.1 t.1 φ (ε j b)

theorem exists_leafTW1_of_twGoodAt (A : FamIn D.what₂.LL Γ Pl0 T0 D.R.m) (c : NChoice D) (I : TwIn D) (hG : TwGoodAt D c I)
    (O : OnObj S P oc) (ι : Bs.J → Fin D.R.m) (hι : Function.Injective ι) (hM : GoodPartLattice O) (hΘ : ThetaFullRank O)
    (hT : AtPair S fun v => TwistedAt D (D.plEq.symm v) ∧ ∀ j, TiedAt A c I.E O v j (ι j)) :
    ∃ ε, LeafTW1 ({ O with ε0 := ε } : OnObj S P oc) := by
  have loc : ∀ v, ∃ ε : Bs.J → ℝ, (∀ j, Formalism.EigenvalueLevelCeiling.IsLatIn (O.Zg j) (O.eJ v j)) →
      (TwistedAt D (D.plEq.symm v) ∧ ∀ j, TiedAt A c I.E O v j (ι j)) →
      (∀ j, 0 ≤ ε j ∧ (Formalism.EigenvalueLevelCeiling.lix v (Formalism.EigenvalueLevelCeiling.cut (O.Zg j) (O.Ms j)) (O.X₃ v j) : ℝ) ≤
        (Formalism.EigenvalueLevelCeiling.lix v (Formalism.EigenvalueLevelCeiling.cut (O.Zg j) (O.Ms j)) (O.eJ v j) : ℝ) + (Formalism.EigenvalueLevelCeiling.ramw v : ℝ) * ε j) ∧
      ∑ j, ε j ≤ ((Formalism.EigenvalueLevelCeiling.plc v : ℝ) ^ 2)⁻¹ := fun v => by
    by_cases hv : TwistedAt D (D.plEq.symm v)
    · obtain ⟨hI, -, ⟨ε, h0, h1, h2⟩, h3, -⟩ := hG _ hv
      have hψ : BlochKatoReduction.Gen.psiAt (c.sd (D.plEq.symm v)) ((BlochKatoReduction.Gen.psiAt (c.sd (D.plEq.symm v)) (c.psi' (D.plEq.symm v))).comp
          (D.ntw.art (c.twI (D.plEq.symm v)) (c.Q (D.plEq.symm v)))) = chosenChar c (D.plEq.symm v) := by
        cases c.sd (D.plEq.symm v)
        · ext g
          simp [BlochKatoReduction.Gen.psiAt, chosenChar]
        · rfl
      refine ⟨fun j => ε ((ι j : ℕ) + 1) (c.sd (D.plEq.symm v)), fun hΘ hT => ⟨fun j => ⟨h0 _ _, ?_⟩, ?_⟩⟩
      · have g2 := h2 _ (succ_mem_Icc (ι j)) (c.sd (D.plEq.symm v))
        have g3 := h3 _ (succ_mem_Icc (ι j)) (c.sd (D.plEq.symm v))
        rw [hψ] at g2 g3
        exact (hT.2 j).lix_le (hM j) (hΘ j) (isLatIn_eTh hI (succ_mem_Icc (ι j)) _) ⟨g3.1, g2, g3.2⟩
      · rw [← l_eq_plc c v]
        exact (sum_side_le hι h0 _).trans h1
    · exact ⟨0, fun _ hT => absurd hT.1 hv⟩
  choose ε hε using loc
  exact ⟨ε, leafTW1_of_places fun w hw => ⟨hε _ (hΘ w hw).1 (hT w hw).1, hε _ (hΘ w hw).2 (hT w hw).2⟩⟩

end Record

end GlobalTheory.TwistIndex
