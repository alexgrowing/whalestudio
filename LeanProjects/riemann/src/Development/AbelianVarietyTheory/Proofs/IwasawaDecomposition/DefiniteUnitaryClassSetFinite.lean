import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.Foundations.ClassMassEqSumOfBijective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Formalism.SatakeDualWeyl.KpqSubgroupCompact

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU GlobalTheory.LFun
open scoped TensorProduct Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.DefU.ClassFin

section Base

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

local notation "AF" => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F

theorem adMap_eq_complMap {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} (h : w.under (𝓞 F) = v) (a : AF) :
    (GlobalTheory.AdeleBaseChange.adMap F E a) w = complMap h (a v) := by
  subst h
  rfl

theorem under_conjSrc (c : E ≃+* E) (hc : ∀ x : F, c (algebraMap F E x) = algebraMap F E x)
    (w : HeightOneSpectrum (𝓞 E)) : (conjSrc c w).under (𝓞 F) = w.under (𝓞 F) := by
  have key : ∀ a : 𝓞 F, a ∈ ((conjSrc c w).under (𝓞 F)).asIdeal ↔ a ∈ (w.under (𝓞 F)).asIdeal := fun a => by
    have h1 : ∀ P : HeightOneSpectrum (𝓞 E), a ∈ (P.under (𝓞 F)).asIdeal ↔
        P.valuation E (algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) a)) < 1 := fun P => by
      rw [HeightOneSpectrum.valuation_lt_one_iff_mem]
      rfl
    have h2 : algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) a) = algebraMap F E (a : F) := rfl
    rw [h1, h1, h2, ← conjPl_conjSrc c w, hc]
  exact HeightOneSpectrum.ext (Ideal.ext key)

theorem conjFin_adMap (c : E ≃+* E) (hc : ∀ x : F, c (algebraMap F E x) = algebraMap F E x) (a : AF) :
    conjFin c (GlobalTheory.AdeleBaseChange.adMap F E a) = GlobalTheory.AdeleBaseChange.adMap F E a := by
  refine FiniteAdeleRing.ext _ fun w => ?_
  have hu := under_conjSrc c hc w
  have e1 : pLoc E w (conjFin c (GlobalTheory.AdeleBaseChange.adMap F E a)) = conjLoc c w (complMap hu (a (w.under (𝓞 F)))) := by
    rw [pLoc_conjFin]
    exact congrArg _ (adMap_eq_complMap hu a)
  have e2 := adMap_eq_complMap (E := E) (rfl : w.under (𝓞 F) = _) a
  have e3 := congrFun ((HeightOneSpectrum.denseRange_algebraMap F (w.under (𝓞 F))).equalizer
    ((conjLoc_spec c w).1.comp (InertChart.continuous_complMap hu)) (InertChart.continuous_complMap (rfl : w.under (𝓞 F) = _))
    (funext fun k => by
      change conjLoc c w (complMap hu (algebraMap F _ k)) = complMap rfl (algebraMap F _ k)
      rw [complMap_algebraMap, complMap_algebraMap, (conjLoc_spec c w).2.1, hc])) (a (w.under (𝓞 F)))
  exact e1.trans (e3.trans e2.symm)

theorem finAdEquiv_sigR (σ : E →ₐ[F] E) (c : E ≃+* E) (h : ∀ x, σ x = c x) (y : AF ⊗[F] E) :
    finAdEquiv F E (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR AF σ y) = conjFin c (finAdEquiv F E y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a x =>
    have hc : ∀ x : F, c (algebraMap F E x) = algebraMap F E x := fun x => by rw [← h]; exact σ.commutes x
    change toFinAd F E (a ⊗ₜ[F] σ x) = conjFin c (toFinAd F E (a ⊗ₜ[F] x))
    rw [toFinAd_tmul, toFinAd_tmul, map_mul, conjFin_adMap c hc, conjFin_algebraMap, h]

theorem continuous_adMap : Continuous (GlobalTheory.AdeleBaseChange.adMap F E) :=
  RestrictedProduct.mapAlong_continuous (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun w : HeightOneSpectrum (𝓞 E) => w.adicCompletion E) (fun w => w.under (𝓞 F))
    (Filter.Tendsto.cofinite_of_finite_preimage_singleton fun v => GlobalTheory.QNorm.finite_places_over F E v)
    (fun w => GlobalTheory.AdeleBaseChange.locMap F w)
    (Filter.Eventually.of_forall fun w _ hx => GlobalTheory.AdeleBaseChange.locMap_int w _ hx)
    fun w => InertChart.continuous_complMap (rfl : w.under (𝓞 F) = _)

theorem continuous_finAdEquiv : Continuous (finAdEquiv F E) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology AF (AF ⊗[F] E) := ⟨rfl⟩
  letI : Algebra AF (FiniteAdeleRing (𝓞 E) E) := (GlobalTheory.AdeleBaseChange.adMap F E).toAlgebra
  haveI : ContinuousSMul AF (FiniteAdeleRing (𝓞 E) E) := continuousSMul_of_algebraMap _ _ continuous_adMap
  let f : AF ⊗[F] E →ₗ[AF] FiniteAdeleRing (𝓞 E) E :=
    { toFun := finAdEquiv F E
      map_add' := map_add _
      map_smul' := fun r y => by
        induction y using TensorProduct.induction_on with
        | zero => simp only [smul_zero, map_zero]
        | add a b ha hb => simp only [smul_add, map_add, ha, hb]
        | tmul a x =>
          change toFinAd F E ((r * a) ⊗ₜ[F] x) = GlobalTheory.AdeleBaseChange.adMap F E r * toFinAd F E (a ⊗ₜ[F] x)
          rw [toFinAd_tmul, toFinAd_tmul, map_mul, mul_assoc] }
  exact IsModuleTopology.continuous_of_linearMap f

end Base

section Unitary

variable (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)

abbrev Fr : Type := maximalRealSubfield E

abbrev AFr : Type := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af (Fr E)

abbrev sg : E →ₐ[Fr E] E := (IsCMField.complexConj E : E →ₐ[Fr E] E)

abbrev cc : E ≃+* E := (IsCMField.complexConj E).toRingEquiv

abbrev HF : Type := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (AFr E) (sg E) (1 : Matrix (Fin n) (Fin n) E)

variable {E n}

omit [IsCMField E] in

theorem cT_map {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) (s : R →+* R) (t : S →+* S)
    (h : ∀ y, p (s y) = t (p y)) (M : Matrix (Fin n) (Fin n) R) : cT t (M.map p) = (cT s M).map p := by
  ext i j
  exact (h _).symm

omit [IsCMField E] in

theorem unitary_map {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) (s : R →+* R) (t : S →+* S)
    (h : ∀ y, p (s y) = t (p y)) (M : Matrix (Fin n) (Fin n) R) (hM : cT s M * M = 1) :
    cT t (M.map p) * M.map p = 1 := by
  rw [cT_map p s t h, ← Matrix.map_mul, hM]
  exact Matrix.map_one p (map_zero p) (map_one p)

theorem pFin_conjAd (y : Ad E) : pFin E (conjAd E y) = conjFin (cc E) (pFin E y) := rfl

theorem pInf_conjAd (y : Ad E) : pInf E (conjAd E y) = starRingEnd (Cinf E) (pInf E y) :=
  (infEq E).symm_apply_apply _

theorem finGL_mem_UA (k : GL (Fin n) (Af E)) (hk : cT (conjFin (cc E)) k.val * k.val = 1) : finGL E n k ∈ UA E n := by
  change cT (conjAd E) (finGL E n k).val * 1 * (finGL E n k).val = 1
  have h1 : (finGL E n k).val.map (pFin E) = k.val := congrArg Units.val (pFin_finGL k)
  have h2 : (finGL E n k).val.map (pInf E) = 1 := congrArg Units.val (pInf_finGL k)
  have h3 : (cT (conjAd E) (finGL E n k).val * (finGL E n k).val).map (pFin E) = 1 := by
    rw [Matrix.map_mul, ← cT_map (pFin E) (conjAd E) (conjFin (cc E)) pFin_conjAd, h1, hk]
  have h4 : (cT (conjAd E) (finGL E n k).val * (finGL E n k).val).map (pInf E) = 1 := by
    rw [Matrix.map_mul, ← cT_map (pInf E) (conjAd E) (starRingEnd (Cinf E)) pInf_conjAd, h2, cT_one, mul_one]
  rw [mul_one]
  ext1 i j
  refine ad_ext ((congrFun₂ h4 i j).trans ?_) ((congrFun₂ h3 i j).trans ?_) <;>
  · simp only [Matrix.one_apply]
    split_ifs <;> simp

theorem cT_pFin (g : UA E n) :
    cT (conjFin (cc E)) (GeneralLinearGroup.map (pFin E) g.1).val * (GeneralLinearGroup.map (pFin E) g.1).val = 1 := by
  have hg : cT (conjAd E) g.1.val * 1 * g.1.val = 1 := g.2
  rw [mul_one] at hg
  exact unitary_map (pFin E) (conjAd E) (conjFin (cc E)) pFin_conjAd g.1.val hg

theorem JR_one : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (F := Fr E) (AFr E) (1 : Matrix (Fin n) (Fin n) E) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

abbrev AEq : AFr E ⊗[Fr E] E →+* Af E := (finAdEquiv (Fr E) E : AFr E ⊗[Fr E] E →+* Af E)

theorem AEq_sig (y : AFr E ⊗[Fr E] E) :
    AEq (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AFr E) (sg E) y) = conjFin (cc E) (AEq y) :=
  finAdEquiv_sigR _ _ (fun _ => rfl) y

theorem AEq_symm_sig (y : Af E) : (finAdEquiv (Fr E) E).symm (conjFin (cc E) y) =
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AFr E) (sg E) ((finAdEquiv (Fr E) E).symm y) := by
  rw [RingEquiv.symm_apply_eq]
  refine Eq.trans ?_ (AEq_sig _).symm
  congr 1
  exact ((finAdEquiv (Fr E) E).apply_symm_apply y).symm

variable (E n) in

def toGL : HF E n →* GL (Fin n) (Af E) :=
  (GeneralLinearGroup.map (AEq (E := E))).comp
    (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (AFr E) (sg E) (1 : Matrix (Fin n) (Fin n) E)).subtype

theorem toGL_val (g : HF E n) : (toGL E n g).val = g.1.val.map AEq := rfl

theorem cT_toGL (g : HF E n) : cT (conjFin (cc E)) (toGL E n g).val * (toGL E n g).val = 1 := by
  have hg : cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AFr E) (sg E)) g.1.val * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (AFr E) (1 : Matrix (Fin n) (Fin n) E) *
      g.1.val = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (AFr E) (1 : Matrix (Fin n) (Fin n) E) := g.2
  rw [JR_one, mul_one] at hg
  rw [toGL_val]
  have h2 := unitary_map (n := n) (AEq (E := E)) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AFr E) (sg E)) (conjFin (cc E)) AEq_sig
  have h3 := h2 g.1.val
  exact h3 hg

variable (E n) in

def toFin : HF E n →* finU E n where
  toFun g := ⟨⟨finGL E n (toGL E n g), finGL_mem_UA _ (cT_toGL g)⟩, pInf_finGL _⟩
  map_one' := Subtype.ext (Subtype.ext (by simp))
  map_mul' a b := Subtype.ext (Subtype.ext (by simp))

theorem finGL_pFin (k : finU E n) : finGL E n (GeneralLinearGroup.map (pFin E) k.1.1) = k.1.1 :=
  ga_ext ((pInf_finGL _).trans (Eq.symm k.2)) (pFin_finGL _)

theorem toFin_surjective : Function.Surjective (toFin E n) := fun k => by
  let y := GeneralLinearGroup.map (pFin E) k.1.1
  have hy : cT (conjFin (cc E)) y.val * y.val = 1 := cT_pFin k.1
  let A' : Af E →+* AFr E ⊗[Fr E] E := ((finAdEquiv (Fr E) E).symm : Af E →+* AFr E ⊗[Fr E] E)
  have hm : GeneralLinearGroup.map A' y ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (AFr E) (sg E) (1 : Matrix (Fin n) (Fin n) E) := by
    change cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AFr E) (sg E)) (GeneralLinearGroup.map A' y).val *
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (AFr E) (1 : Matrix (Fin n) (Fin n) E) * (GeneralLinearGroup.map A' y).val =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (AFr E) (1 : Matrix (Fin n) (Fin n) E)
    rw [JR_one, mul_one]
    exact unitary_map A' _ _ AEq_symm_sig y.val hy
  refine ⟨⟨_, hm⟩, Subtype.ext (Subtype.ext ?_)⟩
  have : toGL E n ⟨_, hm⟩ = y := Units.ext (Matrix.ext fun i j =>
    (finAdEquiv (Fr E) E).apply_symm_apply _)
  change finGL E n (toGL E n ⟨_, hm⟩) = _
  rw [this]
  exact finGL_pFin k

theorem continuous_finGL : Continuous (finGL E n) :=
  Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map (continuous_const.prodMk continuous_id :
    Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E))))

theorem continuous_toFin : Continuous (toFin E n) := by
  have h1 : Continuous (GeneralLinearGroup.map (AEq (E := E)) : GL (Fin n) _ → GL (Fin n) (Af E)) :=
    Continuous.units_map _ (continuous_id.matrix_map continuous_finAdEquiv)
  have h2 : Continuous (toGL E n) := h1.comp continuous_subtype_val
  exact Continuous.subtype_mk (Continuous.subtype_mk (continuous_finGL.comp h2) _) _

theorem toGL_rat (t : HF E n) (ht : t ∈ GlobalTheory.Mass.ratIn (AFr E) (sg E) (1 : Matrix (Fin n) (Fin n) E)) :
    ∃ γ ∈ ratU E n, GeneralLinearGroup.map (pFin E) γ.1 = toGL E n t := by
  obtain ⟨γ₀, hγ₀, e⟩ := ht
  have hu : cT ((sg E : E →+* E)) γ₀.val * 1 * γ₀.val = 1 := hγ₀
  rw [mul_one] at hu
  have hm : ratGL E n γ₀ ∈ UA E n := by
    change cT (conjAd E) (γ₀.val.map (algebraMap E (Ad E))) * 1 * γ₀.val.map (algebraMap E (Ad E)) = 1
    rw [mul_one]
    exact unitary_map (algebraMap E (Ad E)) (sg E : E →+* E) (conjAd E) (fun y => (conjAd_algebraMap y).symm) _ hu
  refine ⟨⟨_, hm⟩, ⟨γ₀, rfl⟩, ?_⟩
  have e' : t.1 = Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (AFr E)) γ₀ := e.symm
  refine Units.ext (Matrix.ext fun i j => ?_)
  change algebraMap E (Af E) (γ₀.val i j) = AEq (t.1.val i j)
  rw [e']
  change _ = toFinAd (Fr E) E ((1 : AFr E) ⊗ₜ[Fr E] (γ₀.val i j))
  rw [toFinAd_tmul, map_one, one_mul]

theorem mul_inv_mem_infU {u v : UA E n}
    (h : GeneralLinearGroup.map (pFin E) u.1 = GeneralLinearGroup.map (pFin E) v.1) : u * v⁻¹ ∈ infU E n := by
  change GeneralLinearGroup.map (pFin E) (u * v⁻¹).1 = 1
  rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, h, mul_inv_cancel]

theorem assemble {g γ f₁ s k x₀ x₁ : UA E n} (hx₀ : x₀ ∈ infU E n) (hx₁ : x₁ ∈ infU E n) (hs : s ∈ finU E n)
    (h1 : g = x₀ * (f₁ * s * k)) (h2 : γ = x₁ * f₁) :
    ∃ x ∈ infU E n, g = γ * s * x * k := by
  have hy : γ⁻¹ * (x₀ * x₁⁻¹) * γ ∈ infU E n := by
    have := Subgroup.Normal.conj_mem' (inferInstance : (infU E n).Normal) (x₀ * x₁⁻¹) (mul_mem hx₀ (inv_mem hx₁)) γ
    exact this
  refine ⟨_, hy, ?_⟩
  rw [mul_assoc γ s, fin_mul_inf hs hy]
  subst h2 h1
  group

variable (E n) in

theorem classSet_finite (K : Subgroup (finU E n)) (hK : IsOpen (K : Set (finU E n))) :
    ∃ S : Finset (UA E n), ∀ g : UA E n, ∃ γ ∈ ratU E n, ∃ s ∈ S, ∃ x ∈ infU E n, ∃ k ∈ K,
      g = γ * s * x * (k : UA E n) := by
  classical
  haveI := GlobalTheory.Mass.topGroup_fin (sg E) (1 : Matrix (Fin n) (Fin n) E)
  let K' : Subgroup (HF E n) := K.comap (toFin E n) ⊓ GlobalTheory.Mass.stdLevel (sg E) 1
  have ho : IsOpen (K' : Set (HF E n)) :=
    (hK.preimage continuous_toFin).inter (GlobalTheory.Mass.isOpen_stdLevel _ _)
  have hc : IsCompact (K' : Set (HF E n)) :=
    (GlobalTheory.Mass.isCompact_stdLevel _ _ (by simp)).of_isClosed_subset (K'.isClosed_of_isOpen ho) Set.inter_subset_right
  have hcm : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt (Fr E) E (sg E) :=
    ⟨inferInstance, inferInstance, Algebra.IsQuadraticExtension.finrank_eq_two _ E,
      fun τ x => IsCMField.complexEmbedding_complexConj E τ x⟩
  have hstd := Formalism.UG.Final.StdFormDef (Fr E) E (Fin n) (sg E)
    (fun τ => RingHom.ext fun x => IsCMField.complexEmbedding_complexConj E τ x)
    (fun e he => ⟨⟨e, (IsCMField.complexConj_eq_self_iff E e).1 he⟩, rfl⟩) inferInstance
  have hnd : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND (sg E) (1 : Matrix (Fin n) (Fin n) E) :=
    ⟨fun i j => congrFun₂ hstd.1 i j, by simp⟩
  have hf := (GlobalTheory.Mass.finiteClasses_unitary hcm hnd hstd.2.1 hc ho).1
  haveI := Fintype.ofFinite (ClassSet (GlobalTheory.Mass.ratIn (AFr E) (sg E) (1 : Matrix (Fin n) (Fin n) E)) K')
  refine ⟨Finset.univ.image fun c : ClassSet (GlobalTheory.Mass.ratIn (AFr E) (sg E) (1 : Matrix (Fin n) (Fin n) E)) K' =>
    ((toFin E n (Quotient.out c) : finU E n) : UA E n), fun g => ?_⟩
  let f : finU E n := ⟨⟨finGL E n (GeneralLinearGroup.map (pFin E) g.1), finGL_mem_UA _ (cT_pFin g)⟩, pInf_finGL _⟩
  obtain ⟨h, hh⟩ := toFin_surjective f
  obtain ⟨a, b, ha, hb, e⟩ := DoubleCoset.mk_out_eq_mul
    (GlobalTheory.Mass.ratIn (AFr E) (sg E) (1 : Matrix (Fin n) (Fin n) E)) K' h
  obtain ⟨γ, hγ, hγe⟩ := toGL_rat a⁻¹ (inv_mem ha)
  have hout : h = a⁻¹ * Quotient.out (DoubleCoset.mk (GlobalTheory.Mass.ratIn (AFr E) (sg E) (1 : Matrix (Fin n) (Fin n) E)) K' h) * b⁻¹ := by
    rw [e]
    group
  have hbK : b⁻¹ ∈ K' := inv_mem hb
  have hmap : ∀ t : HF E n, GeneralLinearGroup.map (pFin E) ((toFin E n t : finU E n) : UA E n).1 = toGL E n t :=
    fun t => pFin_finGL _
  obtain ⟨x, hx, hg⟩ := assemble (g := g) (γ := γ) (f₁ := ((toFin E n a⁻¹ : finU E n) : UA E n))
    (s := ((toFin E n (Quotient.out (DoubleCoset.mk (GlobalTheory.Mass.ratIn (AFr E) (sg E) (1 : Matrix (Fin n) (Fin n) E)) K' h)) : finU E n) : UA E n))
    (k := ((toFin E n b⁻¹ : finU E n) : UA E n)) (x₀ := g * (f : UA E n)⁻¹)
    (x₁ := γ * ((toFin E n a⁻¹ : finU E n) : UA E n)⁻¹)
    (mul_inv_mem_infU (pFin_finGL _).symm) (mul_inv_mem_infU (hγe.trans (hmap _).symm)) (SetLike.coe_mem _)
    (by
      have : (f : UA E n) = _ * _ * _ := congrArg Subtype.val (hh.symm.trans (congrArg (toFin E n) hout |>.trans
        ((map_mul _ _ _).trans (congrArg (· * _) (map_mul _ _ _)))))
      rw [← this, inv_mul_cancel_right])
    (by group)
  exact ⟨γ, hγ, _, Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, x, hx, _, hbK.1, hg⟩

end Unitary

end GlobalTheory.DefU.ClassFin
