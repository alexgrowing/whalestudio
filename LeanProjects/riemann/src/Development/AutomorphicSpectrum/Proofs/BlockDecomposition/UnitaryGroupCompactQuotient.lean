import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical
open scoped ComplexOrder

noncomputable section

open scoped TensorProduct Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.DefU.ClassFin GlobalTheory.LFun

namespace GlobalTheory.CompanionTheory.DefiniteTransport

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem herm_map {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) (s : R →+* R) (t : S →+* S)
    (h : ∀ y, p (s y) = t (p y)) (J M : Matrix (Fin n) (Fin n) R) (hM : cT s M * J * M = J) :
    cT t (M.map p) * J.map p * M.map p = J.map p := by
  rw [cT_map p s t h, ← Matrix.map_mul, ← Matrix.map_mul, hM]

abbrev HH (H : Matrix (Fin n) (Fin n) E) : Type := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (AFr E) (sg E) H

theorem AEq_inclR (x : E) : AEq (E := E) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (AFr E) x) = algebraMap E (Af E) x := by
  change toFinAd (Fr E) E ((1 : AFr E) ⊗ₜ[Fr E] x) = _
  rw [toFinAd_tmul, map_one, one_mul]

theorem JR_map (H : Matrix (Fin n) (Fin n) E) :
    (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (AFr E) H).map (AEq (E := E)) = H.map (algebraMap E (Af E)) :=
  Matrix.ext fun i j => AEq_inclR (H i j)

def toGLH (H : Matrix (Fin n) (Fin n) E) : HH H →* GL (Fin n) (Af E) :=
  (GeneralLinearGroup.map (AEq (E := E))).comp (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (AFr E) (sg E) H).subtype

theorem toGLH_val (H : Matrix (Fin n) (Fin n) E) (g : HH H) : (toGLH H g).val = g.1.val.map AEq := rfl

theorem continuous_toGLH (H : Matrix (Fin n) (Fin n) E) : Continuous (toGLH H) := by
  have h1 : Continuous (GeneralLinearGroup.map (AEq (E := E)) : GL (Fin n) _ → GL (Fin n) (Af E)) :=
    Continuous.units_map _ (continuous_id.matrix_map continuous_finAdEquiv)
  exact h1.comp continuous_subtype_val

theorem toGLH_mem (H : Matrix (Fin n) (Fin n) E) (g : HH H) :
    toGLH H g ∈ UJ (conjFin (cc E)) (H.map (algebraMap E (Af E))) := by
  have hg : cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AFr E) (sg E)) g.1.val * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (AFr E) H * g.1.val =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (AFr E) H := g.2
  have h := herm_map (AEq (E := E)) _ _ AEq_sig _ _ hg
  rw [JR_map] at h
  exact h

theorem exists_toGLH (H : Matrix (Fin n) (Fin n) E) (y : GL (Fin n) (Af E))
    (hy : y ∈ UJ (conjFin (cc E)) (H.map (algebraMap E (Af E)))) : ∃ t : HH H, toGLH H t = y := by
  let A' : Af E →+* AFr E ⊗[Fr E] E := ((finAdEquiv (Fr E) E).symm : Af E →+* AFr E ⊗[Fr E] E)
  have hy' : cT (conjFin (cc E)) y.val * H.map (algebraMap E (Af E)) * y.val = H.map (algebraMap E (Af E)) := hy
  have hJ : (H.map (algebraMap E (Af E))).map A' = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (AFr E) H := by
    rw [← JR_map]
    exact Matrix.ext fun i j => (finAdEquiv (Fr E) E).symm_apply_apply _
  have hm : GeneralLinearGroup.map A' y ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (AFr E) (sg E) H := by
    have h := herm_map A' _ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AFr E) (sg E)) AEq_symm_sig _ _ hy'
    rw [hJ] at h
    exact h
  exact ⟨⟨_, hm⟩, Units.ext (Matrix.ext fun i j => (finAdEquiv (Fr E) E).apply_symm_apply _)⟩

theorem toGLH_rat (H : Matrix (Fin n) (Fin n) E) (t : HH H)
    (ht : t ∈ GlobalTheory.Mass.ratIn (AFr E) (sg E) H) :
    ∃ γ ∈ UJ ((sg E : E →ₐ[Fr E] E) : E →+* E) H, toGLH H t = ratF E n γ := by
  obtain ⟨γ₀, hγ₀, e⟩ := ht
  refine ⟨γ₀, hγ₀, Units.ext (Matrix.ext fun i j => ?_)⟩
  have e' : t.1 = Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (AFr E)) γ₀ := e.symm
  change AEq (t.1.val i j) = algebraMap E (Af E) (γ₀.val i j)
  rw [e']
  exact AEq_inclR _

theorem exists_rat (H : Matrix (Fin n) (Fin n) E) (γ : GL (Fin n) E)
    (hγ : γ ∈ UJ ((sg E : E →ₐ[Fr E] E) : E →+* E) H) :
    ∃ t : HH H, t ∈ GlobalTheory.Mass.ratIn (AFr E) (sg E) H ∧ toGLH H t = ratF E n γ := by
  have hu : cT ((sg E : E →ₐ[Fr E] E) : E →+* E) γ.val * H * γ.val = H := hγ
  have hs : ∀ y : E, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (AFr E) ((sg E : E →ₐ[Fr E] E) y) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AFr E) (sg E) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (AFr E) y) := fun y => by
    change (1 : AFr E) ⊗ₜ[Fr E] _ = Algebra.TensorProduct.map (AlgHom.id (Fr E) (AFr E)) (sg E) ((1 : AFr E) ⊗ₜ[Fr E] y)
    rw [Algebra.TensorProduct.map_tmul]
    rfl
  have hm : Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (AFr E)) γ ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (AFr E) (sg E) H := by
    exact herm_map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (AFr E)) _ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AFr E) (sg E)) hs _ _ hu
  refine ⟨⟨_, hm⟩, ⟨γ, hγ, rfl⟩, Units.ext (Matrix.ext fun i j => ?_)⟩
  exact AEq_inclR _

theorem emb_hform (H : Matrix (Fin n) (Fin n) E) (φ : E →+* ℂ) (x : Fin n → E) :
    φ (hform ((sg E : E →ₐ[Fr E] E) : E →+* E) H x x) =
      star (fun i => φ (x i)) ⬝ᵥ (H.map φ).mulVec (fun i => φ (x i)) := by
  have hs : ∀ z : E, φ ((sg E : E →ₐ[Fr E] E) z) = star (φ z) := fun z =>
    IsCMField.complexEmbedding_complexConj E φ z
  simp only [hform, map_sum, map_mul, dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply,
    Matrix.map_apply, mul_assoc]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  erw [hs]

theorem emb_hform_pos (H : Matrix (Fin n) (Fin n) E) (φ : E →+* ℂ) (hp : (H.map φ).PosDef) (x : Fin n → E)
    (hx : x ≠ 0) : 0 < φ (hform ((sg E : E →ₐ[Fr E] E) : E →+* E) H x x) := by
  rw [emb_hform]
  refine hp.dotProduct_mulVec_pos fun h0 => hx (funext fun i => φ.injective ?_)
  simpa using congrFun h0 i

theorem isTotDef (H : Matrix (Fin n) (Fin n) E) (hp : ∀ τ : E →+* ℂ, (H.map τ).PosDef) :
    IsTotDef (sg E) H := by
  refine ⟨inferInstance, fun ι => Or.inl fun x hx => ?_⟩
  letI : Algebra (Fr E) ℂ := (Complex.ofRealHom.comp ι).toAlgebra
  let τ : E →ₐ[Fr E] ℂ := IsAlgClosed.lift
  have he : hform ((sg E : E →ₐ[Fr E] E) : E →+* E) H x x ∈ maximalRealSubfield E := fun φ => by
    have := emb_hform_pos H φ (hp φ) x hx
    exact Complex.conj_eq_iff_im.2 (Complex.pos_iff.1 this).2.symm
  refine ⟨⟨_, he⟩, rfl, ?_⟩
  have h1 := emb_hform_pos H (τ : E →+* ℂ) (hp _) x hx
  have h2 : (τ : E →+* ℂ) (hform ((sg E : E →ₐ[Fr E] E) : E →+* E) H x x) = ((ι ⟨_, he⟩ : ℝ) : ℂ) :=
    τ.commutes (⟨_, he⟩ : Fr E)
  rw [h2] at h1
  exact Complex.zero_lt_real.1 h1

theorem isCMExt : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt (Fr E) E (sg E) :=
  ⟨inferInstance, inferInstance, Algebra.IsQuadraticExtension.finrank_eq_two _ E,
    fun τ x => IsCMField.complexEmbedding_complexConj E τ x⟩

theorem exists_compact_cover (H : Matrix (Fin n) (Fin n) E) (hnd : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND (sg E) H)
    (hd : IsTotDef (sg E) H) :
    ∃ C : Set (GL (Fin n) (Af E)), IsCompact C ∧
      ∀ g ∈ UJ (conjFin (cc E)) (H.map (algebraMap E (Af E))),
        ∃ γ ∈ UJ ((sg E : E →ₐ[Fr E] E) : E →+* E) H, ∃ k ∈ C, g = ratF E n γ * k := by
  haveI := GlobalTheory.Mass.topGroup_fin (sg E) H
  have hK := GlobalTheory.Mass.isCompact_stdLevel (sg E) H hnd.2
  have hf := GlobalTheory.Mass.finiteClasses_unitary isCMExt hnd hd hK (GlobalTheory.Mass.isOpen_stdLevel (sg E) H)
  haveI := hf.1
  refine ⟨⋃ q : ClassSet (GlobalTheory.Mass.ratIn (AFr E) (sg E) H) (GlobalTheory.Mass.stdLevel (sg E) H),
    toGLH H '' ((fun k => Quotient.out q * k) '' (GlobalTheory.Mass.stdLevel (sg E) H : Set (HH H))),
    isCompact_iUnion fun q => (hK.image (continuous_const.mul continuous_id)).image (continuous_toGLH H), fun g hg => ?_⟩
  obtain ⟨h, rfl⟩ := exists_toGLH H g hg
  obtain ⟨a, b, ha, hb, e⟩ := DoubleCoset.mk_out_eq_mul (GlobalTheory.Mass.ratIn (AFr E) (sg E) H) (GlobalTheory.Mass.stdLevel (sg E) H) h
  obtain ⟨γ, hγ, hγe⟩ := toGLH_rat H a⁻¹ (inv_mem ha)
  refine ⟨γ, hγ, _, Set.mem_iUnion.2 ⟨DoubleCoset.mk (GlobalTheory.Mass.ratIn (AFr E) (sg E) H) (GlobalTheory.Mass.stdLevel (sg E) H) h,
    ⟨_, ⟨b⁻¹, inv_mem hb, rfl⟩, rfl⟩⟩, ?_⟩
  rw [← hγe, ← map_mul, e]
  congr 1
  group

omit [IsCMField E] in

theorem algebraMap_injective (E : Type) [Field E] [NumberField E] : Function.Injective (algebraMap E (Af E)) := by
  haveI : Nontrivial (Af E) := by
    obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 E)
    exact (Formalism.UG.evalV E ⟨P, hP.isPrime,
      Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField E)⟩).toRingHom.domain_nontrivial
  exact (algebraMap E (Af E)).injective

theorem finite_rat_coset (H : Matrix (Fin n) (Fin n) E) (hnd : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND (sg E) H)
    (hd : IsTotDef (sg E) H) (g : HH H) :
    {t : HH H | t ∈ GlobalTheory.Mass.ratIn (AFr E) (sg E) H ∧ g⁻¹ * t ∈ GlobalTheory.Mass.stdLevel (sg E) H}.Finite := by
  have hK := GlobalTheory.Mass.isCompact_stdLevel (sg E) H hnd.2
  have hf := GlobalTheory.Mass.finiteClasses_unitary isCMExt hnd hd hK (GlobalTheory.Mass.isOpen_stdLevel (sg E) H)
  haveI := hf.2 1
  have h0 : (Subtype.val '' stabAt (GlobalTheory.Mass.ratIn (AFr E) (sg E) H) (GlobalTheory.Mass.stdLevel (sg E) H) 1).Finite :=
    (Set.toFinite _).image _
  by_cases hne : ∃ t₀ : HH H, t₀ ∈ GlobalTheory.Mass.ratIn (AFr E) (sg E) H ∧ g⁻¹ * t₀ ∈ GlobalTheory.Mass.stdLevel (sg E) H
  · obtain ⟨t₀, ht₀, hg₀⟩ := hne
    refine (h0.image fun x => t₀ * x).subset fun t ht => ?_
    refine ⟨t₀⁻¹ * t, ⟨⟨_, mul_mem (inv_mem ht₀) ht.1⟩, ?_, rfl⟩, by group⟩
    have := mul_mem (inv_mem hg₀) ht.2
    change 1⁻¹ * (t₀⁻¹ * t) * 1 ∈ GlobalTheory.Mass.stdLevel (sg E) H
    convert this using 1
    group
  · refine Set.finite_empty.subset fun t ht => hne ⟨t, ht⟩

theorem finite_rat_compact (H : Matrix (Fin n) (Fin n) E) (hnd : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND (sg E) H)
    (hd : IsTotDef (sg E) H) (X : Set (GL (Fin n) (Af E))) (hX : IsCompact X) :
    {γ : GL (Fin n) E | γ ∈ UJ ((sg E : E →ₐ[Fr E] E) : E →+* E) H ∧ ratF E n γ ∈ X}.Finite := by
  haveI := GlobalTheory.Mass.topGroup_fin (sg E) H
  haveI : Module.Finite (Fr E) E := Module.Finite.of_restrictScalars_finite ℚ (Fr E) E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField (Fr E)
  let D : Set (Af E) := ⋃ i, ⋃ j, (fun x : GL (Fin n) (Af E) => x.val i j) '' X
  have hD : IsCompact D := isCompact_iUnion fun i => isCompact_iUnion fun j =>
    hX.image ((Units.continuous_val.matrix_elem i j))
  obtain ⟨K₀, hK₀, hKe⟩ := GlobalTheory.StabCompact.exists_compact_of_entries (AFr E) (sg E) H hnd.2
    ((finAdEquiv (Fr E) E).symm '' D) (hD.image continuous_finAdEquiv_symm)
  have hcov := hK₀.elim_nhds_subcover
    (fun g : HH H => {t : HH H | g⁻¹ * t ∈ GlobalTheory.Mass.stdLevel (sg E) H}) fun g _ => by
      refine IsOpen.mem_nhds ((GlobalTheory.Mass.isOpen_stdLevel (sg E) H).preimage (continuous_const.mul continuous_id)) ?_
      change g⁻¹ * g ∈ GlobalTheory.Mass.stdLevel (sg E) H
      rw [inv_mul_cancel]
      exact one_mem _
  obtain ⟨s, -, hs⟩ := hcov
  have hT : ({t : HH H | t ∈ GlobalTheory.Mass.ratIn (AFr E) (sg E) H ∧ t ∈ K₀}).Finite := by
    refine (s.finite_toSet.biUnion fun g _ => finite_rat_coset H hnd hd g).subset fun t ht => ?_
    obtain ⟨g, hg, hgt⟩ := Set.mem_iUnion₂.1 (hs ht.2)
    exact Set.mem_iUnion₂.2 ⟨g, hg, ht.1, hgt⟩
  have hinj : Function.Injective (ratF E n) := fun a b hab => Units.ext (Matrix.ext fun i j =>
    algebraMap_injective E (congrArg (fun g : GL (Fin n) (Af E) => g.val i j) hab))
  refine ((hT.image (toGLH H)).preimage hinj.injOn).subset fun γ hγ => ?_
  obtain ⟨t, ht, e⟩ := exists_rat H γ hγ.1
  refine ⟨t, ⟨ht, hKe t fun i j => ?_⟩, e⟩
  refine ⟨(toGLH H t).val i j, Set.mem_iUnion₂.2 ⟨i, j, ratF E n γ, hγ.2, by rw [e]⟩, ?_⟩
  exact (finAdEquiv (Fr E) E).symm_apply_apply _

theorem cocompact_discrete : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (H : Matrix (Fin n) (Fin n) E),
    IsUnit H.det → cT (IsCMField.complexConj E).toRingEquiv.toRingHom H = H → (∀ τ : E →+* ℂ, (H.map τ).PosDef) →
    (∃ C : Set (GL (Fin n) (Af E)), IsCompact C ∧
      ∀ g ∈ UJ (conjFin (IsCMField.complexConj E).toRingEquiv) (H.map (algebraMap E (Af E))),
        ∃ γ ∈ UJ (IsCMField.complexConj E).toRingEquiv.toRingHom H, ∃ k ∈ C, g = ratF E n γ * k) ∧
    ∀ X : Set (GL (Fin n) (Af E)), IsCompact X →
      {γ : GL (Fin n) E | γ ∈ UJ (IsCMField.complexConj E).toRingEquiv.toRingHom H ∧ ratF E n γ ∈ X}.Finite := by
  intro E _ _ _ n H hu hc hp
  have hnd : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND (sg E) H := ⟨fun i j => congrFun₂ hc i j, hu.ne_zero⟩
  have hd := isTotDef H hp
  exact ⟨exists_compact_cover H hnd hd, fun X hX => finite_rat_compact H hnd hd X hX⟩

end GlobalTheory.CompanionTheory.DefiniteTransport
