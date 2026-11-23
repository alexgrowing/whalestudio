import Mathlib

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter
open scoped RestrictedProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele

class IsCMExtension (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] : Prop where
  totallyReal : IsTotallyReal F
  totallyComplex : IsTotallyComplex E
  quadratic : Algebra.IsQuadraticExtension F E

section CM

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter in
open scoped RestrictedProduct in
variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.IsCMExtension.isCMField [h : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.IsCMExtension F E] : IsCMField E := by
  haveI := h.totallyReal
  haveI := h.totallyComplex
  haveI := h.quadratic
  exact IsCMField.ofCMExtension F E

instance isCMExtension_maximalRealSubfield (E : Type) [Field E] [NumberField E] [IsCMField E] :
    IsCMExtension (maximalRealSubfield E) E where
  totallyReal := inferInstance
  totallyComplex := inferInstance
  quadratic := inferInstance

def conj [h : IsCMExtension F E] : E ≃ₐ[F] E :=
  haveI := h.totallyReal
  haveI := h.totallyComplex
  haveI := h.quadratic
  haveI := IsCMExtension.isCMField F E
  { (IsCMField.complexConj E).toRingEquiv with
    commutes' := fun x => by
      have := IsCMField.complexConj_apply_eq_self E (CMExtension.equivMaximalRealSubfield F E x)
      rw [CMExtension.equivMaximalRealSubfield_apply] at this
      exact this }

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter in
open scoped RestrictedProduct in
variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] in

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.embedding_conj [_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.IsCMExtension F E] (φ : E →+* ℂ) (x : E) :
    φ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj F E x) = starRingEnd ℂ (φ (x)) := by
  haveI := _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.IsCMExtension.isCMField F E
  exact (IsCMField.isConj_complexConj E φ).eq x

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter in
open scoped RestrictedProduct in
variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj_conj [_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.IsCMExtension F E] (x : E) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj F E (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj F E x) = x := by
  haveI := _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.IsCMExtension.isCMField F E
  exact IsCMField.complexConj_apply_apply E x

theorem conj_ne_one [IsCMExtension F E] : conj F E ≠ 1 := by
  haveI := IsCMExtension.isCMField F E
  intro h
  apply IsCMField.complexConj_ne_one E
  ext x
  exact DFunLike.congr_fun h x

end CM

abbrev Idele (K : Type) [Field K] [NumberField K] : Type := (AdeleRing (𝓞 K) K)ˣ

def principalIdele (K : Type) [Field K] [NumberField K] : Kˣ →* Idele K :=
  Units.map (algebraMap K (AdeleRing (𝓞 K) K)).toMonoidHom

section Extension

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

instance liesOver_under (w : HeightOneSpectrum (𝓞 L)) :
    w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩

instance liesOver_comap (w : InfinitePlace L) : w.LiesOver (w.comap (algebraMap K L)) :=
  ⟨rfl⟩

def finiteCompletionMap (w : HeightOneSpectrum (𝓞 L)) :
    (w.under (𝓞 K)).adicCompletion K →+* w.adicCompletion L :=
  ((adicCompletion.equiv L w).symm.toRingHom.comp
    (UniformSpace.Completion.mapRingHom
      (algebraMap (WithVal ((w.under (𝓞 K)).valuation K)) (WithVal (w.valuation L)))
      (uniformContinuous_algebraMap_liesOver K L (w.under (𝓞 K)) w).continuous)).comp
    (adicCompletion.equiv K (w.under (𝓞 K))).toRingHom

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter in
open scoped RestrictedProduct in
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_finiteCompletionMap (w : HeightOneSpectrum (𝓞 L)) :
    Continuous (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap K L w) :=
  (adicCompletion.uniformEquiv L w).symm.uniformContinuous.continuous.comp
    (UniformSpace.Completion.continuous_map.comp
      (adicCompletion.uniformEquiv K (w.under (𝓞 K))).uniformContinuous.continuous)

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter in
open scoped RestrictedProduct in
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap_coe (w : HeightOneSpectrum (𝓞 L)) (x : K) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap K L w (algebraMap K _ x) =
      algebraMap L (w.adicCompletion L) (algebraMap K L x) := by
  simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingHom.coe_coe]
  erw [show (adicCompletion.equiv K (w.under (𝓞 K))) (algebraMap K _ x) =
    ((WithVal.equiv ((w.under (𝓞 K)).valuation K)).symm x :
      ((w.under (𝓞 K)).valuation K).Completion) from rfl]
  erw [UniformSpace.Completion.mapRingHom_apply, UniformSpace.Completion.map_coe
    (uniformContinuous_algebraMap_liesOver K L (w.under (𝓞 K)) w)]
  rfl

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter in
open scoped RestrictedProduct in
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap_mapsTo (w : HeightOneSpectrum (𝓞 L)) :
    Set.MapsTo (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap K L w)
      ((w.under (𝓞 K)).adicCompletionIntegers K : Set _) (w.adicCompletionIntegers L : Set _) := by
  intro x hx
  have hS : IsClosed ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap K L w) ⁻¹'
      (w.adicCompletionIntegers L : Set (w.adicCompletion L))) :=
    (Valued.isClopen_integer (w.adicCompletion L)).isClosed.preimage
      (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_finiteCompletionMap K L w)
  have hopen : IsOpen (((w.under (𝓞 K)).adicCompletionIntegers K :
      Set ((w.under (𝓞 K)).adicCompletion K))) :=
    (Valued.isClopen_integer ((w.under (𝓞 K)).adicCompletion K)).isOpen
  have hd := Dense.open_subset_closure_inter (denseRange_algebraMap K (w.under (𝓞 K))) hopen hx
  refine closure_minimal ?_ hS hd
  rintro _ ⟨hy, k, rfl⟩
  simp only [Set.mem_preimage, SetLike.mem_coe, mem_adicCompletionIntegers] at hy ⊢
  rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap_coe]
  have h1 : Valued.v (algebraMap K ((w.under (𝓞 K)).adicCompletion K) k) =
      (w.under (𝓞 K)).valuation K k := valuedAdicCompletion_eq_valuation' _ k
  have h2 : Valued.v (algebraMap L (w.adicCompletion L) (algebraMap K L k)) =
      w.valuation L (algebraMap K L k) := valuedAdicCompletion_eq_valuation' _ _
  rw [h1] at hy
  rw [h2, ← valuation_liesOver L (w.under (𝓞 K)) w]
  exact pow_le_one' hy _

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter in
open scoped RestrictedProduct in
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under :
    Tendsto (fun w : HeightOneSpectrum (𝓞 L) => w.under (𝓞 K)) cofinite cofinite := by
  intro s hs
  rw [mem_cofinite] at hs
  rw [mem_map, mem_cofinite]
  rw [← Set.preimage_compl]
  refine hs.preimage' fun v _ => ?_
  refine ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 L)).preimage
    (fun a _ b _ h => HeightOneSpectrum.ext h)).subset ?_
  rintro w rfl
  exact ⟨w.isPrime, ⟨rfl⟩⟩

def finiteAdeleMap : FiniteAdeleRing (𝓞 K) K →+* FiniteAdeleRing (𝓞 L) L :=
  RestrictedProduct.mapAlongRingHom
    (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
    (fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L)
    (fun w => w.under (𝓞 K)) (tendsto_under K L) (finiteCompletionMap K L)
    (Eventually.of_forall (finiteCompletionMap_mapsTo K L))

def infiniteAdeleMap : InfiniteAdeleRing K →+* InfiniteAdeleRing L :=
  Pi.ringHom fun w : InfinitePlace L =>
    (LiesOver.completionMap (v := w.comap (algebraMap K L)) (w := w)).comp
      (Pi.evalRingHom (fun v : InfinitePlace K => v.Completion) (w.comap (algebraMap K L)))

def adeleMap : AdeleRing (𝓞 K) K →+* AdeleRing (𝓞 L) L :=
  RingHom.prodMap (infiniteAdeleMap K L) (finiteAdeleMap K L)

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter in
open scoped RestrictedProduct in
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap_algebraMap (x : K) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap K L (algebraMap K _ x) =
      algebraMap L (AdeleRing (𝓞 L) L) (algebraMap K L x) := by
  refine Prod.ext ?_ ?_
  · funext w
    exact LiesOver.completionMap_coe _
  · ext w : 1
    exact _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap_coe K L w x

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter in
open scoped RestrictedProduct in
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_adeleMap : Continuous (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap K L) :=
  (continuous_pi fun w => LiesOver.continuous_completionMap.comp (continuous_apply _)).prodMap
    (RestrictedProduct.mapAlong_continuous _ _ _
      (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under K L) _
      (Eventually.of_forall (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap_mapsTo K L))
      fun w => _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_finiteCompletionMap K L w)

def ideleMap : Idele K →* Idele L := Units.map (adeleMap K L).toMonoidHom

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter in
open scoped RestrictedProduct in
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_ideleMap : Continuous (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap K L) :=
  Continuous.units_map _ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_adeleMap K L)

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter in
open scoped RestrictedProduct in
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap_principalIdele (x : Kˣ) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap K L (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.principalIdele K x) =
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.principalIdele L (Units.map (algebraMap K L).toMonoidHom x) :=
  Units.ext (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap_algebraMap K L x)

end Extension

def ideleConj (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsCMExtension F E] : Idele E →* Idele E :=
  @ideleMap E E _ _ _ _ (conj F E).toRingEquiv.toRingHom.toAlgebra

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter in
open scoped RestrictedProduct in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj_principalIdele (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] [_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.IsCMExtension F E] (x : Eˣ) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj F E (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.principalIdele E x) =
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.principalIdele E
        (Units.map (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj F E).toRingEquiv.toRingHom.toMonoidHom x) :=
  @_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap_principalIdele E E _ _ _ _
    (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj F E).toRingEquiv.toRingHom.toAlgebra x

example : IsCMExtension (maximalRealSubfield (CyclotomicField 4 ℚ)) (CyclotomicField 4 ℚ) :=
  haveI : IsCyclotomicExtension {4} ℚ (CyclotomicField 4 ℚ) :=
    CyclotomicField.isCyclotomicExtension 4 ℚ
  haveI : IsCMField (CyclotomicField 4 ℚ) :=
    IsCyclotomicExtension.Rat.isCMField _ (S := {4}) ⟨4, rfl, by norm_num⟩
  inferInstance

variable {E : Type} [Field E] [NumberField E]

open scoped Classical in

def localIdele (P : HeightOneSpectrum (𝓞 E)) : (P.adicCompletion E)ˣ →* Idele E :=
  Units.map ((MonoidHom.inr (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E)).comp
    { toFun := fun x => RestrictedProduct.mulSingle
        (fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletionIntegers E) P x
      map_one' := RestrictedProduct.mulSingle_one _ _
      map_mul' := RestrictedProduct.mulSingle_mul _ _ })

variable (E) in

@[ext]
structure UnitaryHeckeChar where

  toHom : Idele E →* Circle
  continuous_toHom : Continuous toHom
  map_principal : ∀ x : Eˣ, toHom (principalIdele E x) = 1

namespace UnitaryHeckeChar

def trivial (E : Type) [Field E] [NumberField E] : UnitaryHeckeChar E where
  toHom := 1
  continuous_toHom := continuous_const
  map_principal _ := rfl

def mul (χ ψ : UnitaryHeckeChar E) : UnitaryHeckeChar E where
  toHom := χ.toHom * ψ.toHom
  continuous_toHom := χ.continuous_toHom.mul ψ.continuous_toHom
  map_principal x := by simp [χ.map_principal, ψ.map_principal]

def inv (χ : UnitaryHeckeChar E) : UnitaryHeckeChar E where
  toHom := χ.toHom⁻¹
  continuous_toHom := χ.continuous_toHom.inv
  map_principal x := by simp [χ.map_principal]

def restrict (F : Type) [Field F] [NumberField F] [Algebra F E] (χ : UnitaryHeckeChar E) :
    UnitaryHeckeChar F where
  toHom := χ.toHom.comp (ideleMap F E)
  continuous_toHom := χ.continuous_toHom.comp (continuous_ideleMap F E)
  map_principal x := by
    rw [MonoidHom.comp_apply, ideleMap_principalIdele, χ.map_principal]

def IsTrivialOn (F : Type) [Field F] [NumberField F] [Algebra F E] (χ : UnitaryHeckeChar E) :
    Prop :=
  ∀ x : Idele F, χ.toHom (ideleMap F E x) = 1

def localComponent (χ : UnitaryHeckeChar E) (P : HeightOneSpectrum (𝓞 E)) :
    (P.adicCompletion E)ˣ →* Circle :=
  χ.toHom.comp (localIdele P)

def IsUnramifiedAt (χ : UnitaryHeckeChar E) (P : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ u : (P.adicCompletion E)ˣ, Valued.v (u : P.adicCompletion E) = 1 → χ.localComponent P u = 1

end UnitaryHeckeChar

def IsUniformiser (P : HeightOneSpectrum (𝓞 E)) (ϖ : (P.adicCompletion E)ˣ) : Prop :=
  Valued.v (ϖ : P.adicCompletion E) = WithZero.exp (-1 : ℤ)

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter in
open scoped RestrictedProduct in
variable {E : Type} [Field E] [NumberField E] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.exists_isUniformiser (P : HeightOneSpectrum (𝓞 E)) :
    ∃ ϖ, _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.IsUniformiser P ϖ := by
  obtain ⟨π, hπ⟩ := P.valuation_exists_uniformizer E
  have hv : Valued.v (algebraMap E (P.adicCompletion E) π) = WithZero.exp (-1 : ℤ) :=
    (valuedAdicCompletion_eq_valuation' P π).trans hπ
  have hne : algebraMap E (P.adicCompletion E) π ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  exact ⟨Units.mk0 _ hne, hv⟩

namespace UnitaryHeckeChar

open scoped Classical in

def valueAt (χ : UnitaryHeckeChar E) (P : HeightOneSpectrum (𝓞 E)) : ℂ :=
  if χ.IsUnramifiedAt P then (χ.localComponent P (exists_isUniformiser P).choose : ℂ) else 0

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter in
open scoped RestrictedProduct in
variable {E : Type} [Field E] [NumberField E] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar.valueAt_eq (χ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar E)
    {P : HeightOneSpectrum (𝓞 E)} (h : χ.IsUnramifiedAt P)
    {ϖ : (P.adicCompletion E)ˣ} (hϖ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.IsUniformiser P ϖ) :
    χ.valueAt P = (χ.localComponent P ϖ : ℂ) := by
  have hc := (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.exists_isUniformiser P).choose_spec
  rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar.valueAt, if_pos h]
  generalize (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.exists_isUniformiser P).choose = ϖ₀ at hc ⊢
  have hu : Valued.v ((ϖ₀ * ϖ⁻¹ : (P.adicCompletion E)ˣ) : P.adicCompletion E) = 1 := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hc, hϖ,
      mul_inv_cancel₀ WithZero.exp_ne_zero]
  have e : ϖ₀ = (ϖ₀ * ϖ⁻¹) * ϖ := by group
  rw [e, map_mul, h _ hu, one_mul]

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter in
open scoped RestrictedProduct in
variable {E : Type} [Field E] [NumberField E] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar.valueAt_of_ramified (χ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar E) {P : HeightOneSpectrum (𝓞 E)}
    (h : ¬ χ.IsUnramifiedAt P) : χ.valueAt P = 0 := by
  simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar.valueAt, h]

theorem norm_valueAt_le (χ : UnitaryHeckeChar E) (P : HeightOneSpectrum (𝓞 E)) :
    ‖χ.valueAt P‖ ≤ 1 := by
  unfold valueAt
  split_ifs
  · exact (Circle.norm_coe _).le
  · simp

def eulerFactor (χ : UnitaryHeckeChar E) (P : HeightOneSpectrum (𝓞 E)) (s : ℂ) : ℂ :=
  (1 - χ.valueAt P * (Ideal.absNorm P.asIdeal : ℂ) ^ (-s))⁻¹

def finiteL (χ : UnitaryHeckeChar E) (s : {s : ℂ // 1 < s.re}) : ℂ :=
  ∏' P : HeightOneSpectrum (𝓞 E), χ.eulerFactor P s

example (P : HeightOneSpectrum (𝓞 E)) : (trivial E).valueAt P = 1 := by
  have h : (trivial E).IsUnramifiedAt P := fun _ _ => rfl
  rw [valueAt, if_pos h]
  rfl

theorem norm_term_le (χ : UnitaryHeckeChar E) (P : HeightOneSpectrum (𝓞 E)) (s : ℂ) :
    ‖χ.valueAt P * (Ideal.absNorm P.asIdeal : ℂ) ^ (-s)‖ ≤
      (Ideal.absNorm P.asIdeal : ℝ) ^ (-s.re) := by
  have h := NumberField.HeightOneSpectrum.one_lt_absNorm P
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
  exact mul_le_of_le_one_left (by positivity) (χ.norm_valueAt_le P)

theorem one_sub_ne_zero (χ : UnitaryHeckeChar E) (P : HeightOneSpectrum (𝓞 E)) {s : ℂ}
    (hs : 0 < s.re) : 1 - χ.valueAt P * (Ideal.absNorm P.asIdeal : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have h1 := χ.norm_term_le P s
  rw [← sub_eq_zero.mp h, norm_one] at h1
  have h2 : (1 : ℝ) < Ideal.absNorm P.asIdeal := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm P
  exact absurd (Real.rpow_lt_one_of_one_lt_of_neg h2 (neg_neg_of_pos hs)) (not_lt.mpr h1)

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter in
open scoped RestrictedProduct in
variable {E : Type} [Field E] [NumberField E] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar.summable_absNorm_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable fun P : HeightOneSpectrum (𝓞 E) => (Ideal.absNorm P.asIdeal : ℝ) ^ (-σ) := by
  classical
  have hprime : ∀ P : HeightOneSpectrum (𝓞 E), (Ideal.absNorm (P.asIdeal.under ℤ)).Prime :=
    fun P => by
      haveI : NeZero P.asIdeal := ⟨P.ne_bot⟩
      exact Nat.absNorm_under_prime P.asIdeal
  let pr : HeightOneSpectrum (𝓞 E) → Nat.Primes := fun P => ⟨_, hprime P⟩
  have hle : ∀ P : HeightOneSpectrum (𝓞 E),
      (Ideal.absNorm P.asIdeal : ℝ) ^ (-σ) ≤ ((pr P : ℕ) : ℝ) ^ (-σ) := by
    intro P
    have h1 : Ideal.absNorm (P.asIdeal.under ℤ) ^ P.asIdeal.inertiaDeg ℤ = Ideal.absNorm P.asIdeal :=
      Ideal.absNorm_pow_inertiaDeg (P.asIdeal.under ℤ) P.asIdeal
    have h2 : (pr P : ℕ) ≤ Ideal.absNorm P.asIdeal :=
      h1 ▸ Nat.le_self_pow (Ideal.inertiaDeg_pos P.asIdeal ℤ).ne' _
    exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast (hprime P).pos) (by exact_mod_cast h2)
      (by linarith)
  have hcard : ∀ (m : Nat.Primes) (u : Finset (HeightOneSpectrum (𝓞 E))),
      (u.filter (fun P => pr P = m)).card ≤ Module.finrank ℚ E := by
    intro m u
    have hunder : ∀ P, pr P = m → P.asIdeal.under ℤ = Ideal.span {((m : ℕ) : ℤ)} := fun P hP => by
      rw [← hP]
      exact (Int.ideal_span_absNorm_eq_self _).symm
    have hq0 : Ideal.span {((m : ℕ) : ℤ)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact_mod_cast m.prop.ne_zero
    haveI hmax : (Ideal.span {((m : ℕ) : ℤ)}).IsMaximal :=
      (Ideal.span_singleton_prime (by exact_mod_cast m.prop.ne_zero)).mpr
        (Nat.prime_iff_prime_int.mp m.prop) |>.isMaximal hq0
    calc (u.filter (fun P => pr P = m)).card
        = ((u.filter (fun P => pr P = m)).image (fun P => P.asIdeal)).card :=
          (Finset.card_image_of_injective _ (fun a b h => HeightOneSpectrum.ext h)).symm
      _ ≤ (IsDedekindDomain.primesOverFinset (Ideal.span {((m : ℕ) : ℤ)}) (𝓞 E)).card := by
          refine Finset.card_le_card fun I hI => ?_
          obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hI
          rw [← Finset.mem_coe, IsDedekindDomain.coe_primesOverFinset hq0]
          exact ⟨P.isPrime, ⟨(hunder P (Finset.mem_filter.mp hP).2).symm⟩⟩
      _ ≤ Module.finrank ℚ E := Ideal.card_primesOverFinset_le_finrank (𝓞 E) ℚ E hq0
  have hsP : Summable fun m : Nat.Primes => ((m : ℕ) : ℝ) ^ (-σ) :=
    Nat.Primes.summable_rpow.mpr (by linarith)
  refine summable_of_sum_le (c := Module.finrank ℚ E * ∑' m : Nat.Primes, ((m : ℕ) : ℝ) ^ (-σ))
    (fun P => by positivity) fun u => ?_
  calc ∑ P ∈ u, (Ideal.absNorm P.asIdeal : ℝ) ^ (-σ)
      ≤ ∑ P ∈ u, ((pr P : ℕ) : ℝ) ^ (-σ) := Finset.sum_le_sum fun P _ => hle P
    _ = ∑ m ∈ u.image pr, ∑ P ∈ u.filter (fun P => pr P = m), ((pr P : ℕ) : ℝ) ^ (-σ) :=
        (Finset.sum_fiberwise_of_maps_to (fun P hP => Finset.mem_image_of_mem pr hP) _).symm
    _ ≤ ∑ m ∈ u.image pr, (Module.finrank ℚ E : ℝ) * ((m : ℕ) : ℝ) ^ (-σ) := by
        refine Finset.sum_le_sum fun m _ => ?_
        rw [Finset.sum_congr rfl fun P hP => by rw [(Finset.mem_filter.mp hP).2],
          Finset.sum_const, nsmul_eq_mul]
        gcongr
        exact_mod_cast hcard m u
    _ = Module.finrank ℚ E * ∑ m ∈ u.image pr, ((m : ℕ) : ℝ) ^ (-σ) := by rw [Finset.mul_sum]
    _ ≤ Module.finrank ℚ E * ∑' m : Nat.Primes, ((m : ℕ) : ℝ) ^ (-σ) := by
        gcongr
        exact hsP.sum_le_tsum _ fun _ _ => by positivity

theorem multipliable_eulerFactor (χ : UnitaryHeckeChar E) {s : ℂ} (hs : 1 < s.re) :
    Multipliable fun P => χ.eulerFactor P s := by
  have h1 : Summable fun P : HeightOneSpectrum (𝓞 E) =>
      χ.valueAt P * (Ideal.absNorm P.asIdeal : ℂ) ^ (-s) :=
    Summable.of_norm_bounded (summable_absNorm_rpow hs) fun P => χ.norm_term_le P s
  have h2 := h1.clog_one_sub.neg.hasSum.cexp.multipliable
  refine h2.congr fun P => ?_
  simp only [Function.comp_apply]
  rw [Complex.exp_neg, Complex.exp_log (χ.one_sub_ne_zero P (by linarith))]
  rfl

theorem hasProd_eulerFactor (χ : UnitaryHeckeChar E) (s : {s : ℂ // 1 < s.re}) :
    HasProd (fun P => χ.eulerFactor P s) (χ.finiteL s) :=
  (χ.multipliable_eulerFactor s.2).hasProd

end UnitaryHeckeChar

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter in
open scoped RestrictedProduct in
variable {E : Type} [Field E] [NumberField E] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.norm_eq_one_of_valued {P : HeightOneSpectrum (𝓞 E)}
    {x : P.adicCompletion E} (h : Valued.v x = 1) : ‖x‖ = 1 := by
  rw [FinitePlace.norm_def, h]
  simp

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter in
open scoped RestrictedProduct in
variable {E : Type} [Field E] [NumberField E] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finite_mulSupport (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.Idele E) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 E) => ‖x.val.2 v‖).Finite := by
  have hev := x.val.2.2.and x.inv.2.2
  rw [Filter.eventually_cofinite] at hev
  refine hev.subset fun v hv ⟨ha, hb⟩ => hv ?_
  simp only [SetLike.mem_coe, mem_adicCompletionIntegers] at ha hb
  have hab : x.val.2 v * x.inv.2 v = 1 := congrArg (fun y : AdeleRing (𝓞 E) E => y.2 v) x.val_inv
  have hv1 : Valued.v (x.val.2 v) * Valued.v (x.inv.2 v) = 1 := by rw [← map_mul, hab, map_one]
  refine _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.norm_eq_one_of_valued (le_antisymm ha ?_)
  calc (1 : _) = Valued.v (x.val.2 v) * Valued.v (x.inv.2 v) := hv1.symm
    _ ≤ Valued.v (x.val.2 v) := mul_le_of_le_one_right' hb

def finiteIdeleNorm : Idele E →* ℝ where
  toFun x := ∏ᶠ v : HeightOneSpectrum (𝓞 E), ‖x.val.2 v‖
  map_one' := finprod_eq_one_of_forall_eq_one fun v => norm_one (α := v.adicCompletion E)
  map_mul' x y := by
    rw [← finprod_mul_distrib (finite_mulSupport x) (finite_mulSupport y)]
    exact finprod_congr fun v => norm_mul (x.val.2 v) (y.val.2 v)

def infiniteIdeleNorm : Idele E →* ℝ where
  toFun x := ∏ v : InfinitePlace E, ‖x.val.1 v‖ ^ v.mult
  map_one' := Finset.prod_eq_one fun v _ => by
    rw [show (1 : Idele E).val.1 v = 1 from rfl, norm_one, one_pow]
  map_mul' x y := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [show (x * y).val.1 v = x.val.1 v * y.val.1 v from rfl, norm_mul, mul_pow]

def ideleNorm : Idele E →* ℝ := infiniteIdeleNorm * finiteIdeleNorm

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter in
open scoped RestrictedProduct in
variable {E : Type} [Field E] [NumberField E] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm_ne_zero (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.Idele E) : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm x ≠ 0 := by
  intro h
  have hx := map_mul _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm x x⁻¹
  rw [mul_inv_cancel, map_one, h, zero_mul] at hx
  exact one_ne_zero hx

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter in
open scoped RestrictedProduct in
variable {E : Type} [Field E] [NumberField E] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm_principalIdele (x : Eˣ) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.principalIdele E x) = 1 := by
  have hinf : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteIdeleNorm (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.principalIdele E x) =
      ∏ w : InfinitePlace E, w (x : E) ^ w.mult :=
    Finset.prod_congr rfl fun v _ => by
      congr 1
      exact InfinitePlace.Completion.norm_coe v ((WithAbs.equiv v.1).symm (x : E))
  have hfin : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteIdeleNorm (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.principalIdele E x) =
      ∏ᶠ w : FinitePlace E, w (x : E) := by
    refine (finprod_congr fun P => ?_).trans (finprod_comp_equiv
      FinitePlace.equivHeightOneSpectrum.symm (f := fun w : FinitePlace E => w (x : E)))
    show ‖FinitePlace.embedding P (x : E)‖ = _
    rw [← FinitePlace.mk_apply]
    rfl
  rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm, MonoidHom.mul_apply, hinf, hfin, prod_abs_eq_one x.ne_zero]

theorem continuous_finiteIdeleNorm : Continuous (finiteIdeleNorm (E := E)) := by
  have hO : IsOpen {a : FiniteAdeleRing (𝓞 E) E | ∀ v, a v ∈ v.adicCompletionIntegers E} :=
    RestrictedProduct.isOpen_forall_mem
      (A := fun v : HeightOneSpectrum (𝓞 E) => (v.adicCompletionIntegers E : Set (v.adicCompletion E)))
      fun _ => Valued.isOpen_valuationSubring _
  have h1 : Continuous fun x : Idele E => x.val.2 := continuous_snd.comp Units.continuous_val
  have h2 : Continuous fun x : Idele E => (x⁻¹).val.2 := h1.comp continuous_inv
  have key : ∀ y : Idele E, (∀ v, y.val.2 v ∈ v.adicCompletionIntegers E) →
      (∀ v, (y⁻¹).val.2 v ∈ v.adicCompletionIntegers E) → finiteIdeleNorm y = 1 := by
    intro y hy hy'
    refine finprod_eq_one_of_forall_eq_one fun v => norm_eq_one_of_valued ?_
    have e : y.val.2 v * (y⁻¹).val.2 v = 1 :=
      congrArg (fun a : AdeleRing (𝓞 E) E => a.2 v) y.mul_inv
    have e' := congrArg Valued.v e
    rw [map_mul, map_one] at e'
    exact eq_one_of_one_le_mul_left (hy v) (hy' v) e'.ge
  refine continuous_iff_continuousAt.mpr fun x => ?_
  have hc : Continuous fun y : Idele E => x⁻¹ * y := continuous_const.mul continuous_id
  have hU := (hO.preimage (h1.comp hc)).inter (hO.preimage (h2.comp hc))
  refine (continuousAt_const (y := finiteIdeleNorm x)).congr ?_
  filter_upwards [hU.mem_nhds (x := x) ⟨fun v => by
    simp only [Function.comp_apply, inv_mul_cancel]; exact one_mem _, fun v => by
    simp only [Function.comp_apply, inv_mul_cancel, inv_one]; exact one_mem _⟩] with y hy
  have := key _ hy.1 hy.2
  rw [← mul_one (finiteIdeleNorm x), ← this, ← map_mul, mul_inv_cancel_left]

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter in
open scoped RestrictedProduct in
variable {E : Type} [Field E] [NumberField E] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_ideleNorm : Continuous (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm (E := E)) := by
  have hinf : Continuous (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteIdeleNorm (E := E)) := by
    show Continuous fun x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.Idele E => ∏ v : InfinitePlace E, ‖x.val.1 v‖ ^ v.mult
    exact continuous_finset_prod _ fun v _ =>
      (((continuous_apply v).comp (continuous_fst.comp (Units.continuous_val (M := AdeleRing (𝓞 E) E)))).norm).pow _
  have hfin : Continuous (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteIdeleNorm (E := E)) := by
    refine continuous_of_continuousAt_one _ ?_
    have hW : IsOpen {a : FiniteAdeleRing (𝓞 E) E |
        ∀ P : HeightOneSpectrum (𝓞 E), True → a P ∈ (P.adicCompletionIntegers E : Set _)} :=
      RestrictedProduct.isOpen_forall_imp_mem fun P =>
        (Valued.isClopen_integer (P.adicCompletion E)).isOpen
    have hV := ((hW.preimage (continuous_snd.comp (Units.continuous_val (M := AdeleRing (𝓞 E) E)))).inter
      (hW.preimage (continuous_snd.comp (Units.continuous_coe_inv (M := AdeleRing (𝓞 E) E))))).mem_nhds
        (x := (1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.Idele E)) ⟨fun P _ => one_mem _, fun P _ => one_mem _⟩
    refine tendsto_nhds_of_eventually_eq ?_
    filter_upwards [hV] with x hx
    rw [map_one]
    refine finprod_eq_one_of_forall_eq_one fun P => ?_
    have ha := hx.1 P trivial
    have hb := hx.2 P trivial
    simp only [SetLike.mem_coe, mem_adicCompletionIntegers] at ha hb
    have hab : x.val.2 P * x.inv.2 P = 1 :=
      congrArg (fun y : AdeleRing (𝓞 E) E => y.2 P) x.val_inv
    have hv1 : Valued.v (x.val.2 P) * Valued.v (x.inv.2 P) = 1 := by rw [← map_mul, hab, map_one]
    refine _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.norm_eq_one_of_valued (le_antisymm ha ?_)
    calc (1 : _) = Valued.v (x.val.2 P) * Valued.v (x.inv.2 P) := hv1.symm
      _ ≤ Valued.v (x.val.2 P) := mul_le_of_le_one_right' hb
  show Continuous fun x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.Idele E => _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteIdeleNorm x * _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteIdeleNorm x
  exact hinf.mul hfin

namespace UnitaryHeckeChar

variable (E) in

def normPow (t : ℝ) : UnitaryHeckeChar E where
  toHom :=
    { toFun := fun x => Circle.exp (t * Real.log (ideleNorm x))
      map_one' := by simp
      map_mul' := fun x y => by
        rw [map_mul ideleNorm, Real.log_mul (ideleNorm_ne_zero x) (ideleNorm_ne_zero y), mul_add,
          Circle.exp_add] }
  continuous_toHom := Circle.exp.continuous.comp
    (continuous_const.mul (continuous_ideleNorm.log ideleNorm_ne_zero))
  map_principal x := by simp [ideleNorm_principalIdele]

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter in
open scoped RestrictedProduct in
variable {E : Type} [Field E] [NumberField E] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar.ideleNorm_localIdele (P : HeightOneSpectrum (𝓞 E))
    (u : (P.adicCompletion E)ˣ) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.localIdele P u) = ‖(u : P.adicCompletion E)‖ := by
  classical
  have hinf : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteIdeleNorm (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.localIdele P u) = 1 :=
    Finset.prod_eq_one fun v _ => by
      rw [show (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.localIdele P u).val.1 v = 1 from rfl, norm_one, one_pow]
  have hfin : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteIdeleNorm (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.localIdele P u) = ‖(u : P.adicCompletion E)‖ := by
    show ∏ᶠ v : HeightOneSpectrum (𝓞 E), ‖(_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.localIdele P u).val.2 v‖ = _
    rw [finprod_eq_single _ P]
    · exact congrArg norm (RestrictedProduct.mulSingle_eq_same _ _ _)
    · intro v hv
      rw [show (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.localIdele P u).val.2 v = 1 from
        RestrictedProduct.mulSingle_eq_of_ne _ _ hv, norm_one]
  rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm, MonoidHom.mul_apply, hinf, hfin, one_mul]

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter in
open scoped RestrictedProduct in
variable {E : Type} [Field E] [NumberField E] in

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar.normPow_isUnramifiedAt (t : ℝ) (P : HeightOneSpectrum (𝓞 E)) :
    (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar.normPow E t).IsUnramifiedAt P := by
  intro u hu
  show Circle.exp (t * Real.log (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.localIdele P u))) = 1
  rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar.ideleNorm_localIdele, _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.norm_eq_one_of_valued hu,
    Real.log_one, mul_zero, Circle.exp_zero]

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter in
open scoped RestrictedProduct in
variable {E : Type} [Field E] [NumberField E] in
private theorem norm_uniformiser_eq_absNorm_inv {P : HeightOneSpectrum (𝓞 E)}
    {ϖ : (P.adicCompletion E)ˣ} (hϖ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.IsUniformiser P ϖ) :
    ‖(ϖ : P.adicCompletion E)‖ = (Ideal.absNorm P.asIdeal : ℝ)⁻¹ := by
  rw [FinitePlace.norm_def, hϖ, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  simp only [show ∀ hx, Multiplicative.toAdd (WithZero.unzero (x := WithZero.exp (-1 : ℤ)) hx) = -1
    from fun _ => rfl]
  simp

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter in
open scoped RestrictedProduct in
variable {E : Type} [Field E] [NumberField E] in

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar.normPow_valueAt (t : ℝ) (P : HeightOneSpectrum (𝓞 E)) :
    (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar.normPow E t).valueAt P =
      Complex.exp ((-(t * Real.log (Ideal.absNorm P.asIdeal)) : ℝ) * Complex.I) := by
  obtain ⟨ϖ, hϖ⟩ := _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.exists_isUniformiser P
  rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar.valueAt_eq _ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar.normPow_isUnramifiedAt t P) hϖ]
  show ((Circle.exp (t * Real.log (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.localIdele P ϖ))) : ℂ)) = _
  rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar.ideleNorm_localIdele, norm_uniformiser_eq_absNorm_inv hϖ,
    Real.log_inv, mul_neg, Circle.coe_exp]

theorem exists_normPow_valueAt_eq_neg_one (P : HeightOneSpectrum (𝓞 E)) :
    ∃ t : ℝ, (normPow E t).valueAt P = -1 := by
  have h : (1 : ℝ) < Ideal.absNorm P.asIdeal := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm P
  refine ⟨-(Real.pi / Real.log (Ideal.absNorm P.asIdeal)), ?_⟩
  rw [normPow_valueAt, neg_mul, neg_neg, div_mul_cancel₀ _ (Real.log_pos h).ne',
    Complex.exp_pi_mul_I]

end UnitaryHeckeChar

end GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele
