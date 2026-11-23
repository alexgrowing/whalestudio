import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftQMk
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MulVecMemLatS

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module

namespace GlobalTheory.UseLoc.DescBD

section Abstract

theorem exists_retr_abs {Z O O' K K' : Type} [CommRing Z] [CommRing O] [CommRing O'] [IsDedekindDomain O]
    [Field K] [Field K'] [Algebra O K] [IsFractionRing O K] [Algebra Z O] [Algebra Z O'] [Module.Finite Z O']
    (f : O →+* O') (hf : ∀ c, algebraMap Z O' c = f (algebraMap Z O c)) (j : O' →+* K') (φ : K →+* K')
    (hc : ∀ a, φ (algebraMap O K a) = j (f a)) (hs : ∀ x : K', ∃ a : K, a ≠ 0 ∧ ∃ y, j y = φ a * x) :
    ∃ R : K' →+ K, (∀ a x, R (φ a * x) = a * R x) ∧ (∀ a, R (φ a) = a) ∧ ∀ x, ∃ y, j y = φ (R (j x)) := by
  letI : Algebra K K' := φ.toAlgebra
  letI : Algebra O K' := (φ.comp (algebraMap O K)).toAlgebra
  letI : Algebra O O' := f.toAlgebra
  letI : Algebra O' K' := j.toAlgebra
  haveI : IsScalarTower O K K' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower O O' K' := IsScalarTower.of_algebraMap_eq hc
  haveI : IsScalarTower Z O O' := IsScalarTower.of_algebraMap_eq hf
  haveI : Module.Finite O O' := Module.Finite.of_restrictScalars_finite Z _ _
  let L : Submodule O K' := LinearMap.range (IsScalarTower.toAlgHom O O' K').toLinearMap
  haveI : Module.Finite O L := inferInstance
  have hsp : Submodule.span K (L : Set K') = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨a, ha, y, hy⟩ := hs x
    have e : x = a⁻¹ • j y := by
      rw [hy]
      change x = φ a⁻¹ * (φ a * x)
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ ha, map_one, one_mul]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, rfl⟩)
  obtain ⟨T, hT, hT'⟩ := GlobalTheory.St.G.Inter.exists_retraction (O := O) (K := K)
    (Algebra.linearMap K K') φ.injective L hsp
  exact ⟨T.toAddMonoidHom, fun a x => T.map_smul a x, hT, fun x => hT' (j x) ⟨x, rfl⟩⟩

theorem mem_BD_iff {O K : Type} [CommRing O] [Field K] [Algebra O K]
    (hinj : Function.Injective (algebraMap O K)) {Γ : Type} [Group Γ] {k : ℕ}
    (N : Γ →* Matrix (Fin k) (Fin k) O) (z : Γ → (Fin k → K) ⧸ stdG O K k) :
    z ∈ BD (stdLatG hinj N) ↔ ∃ m : Fin k → K, ∀ g v, Submodule.Quotient.mk v = z g →
      ∃ u : Fin k → O, ∀ j, algebraMap O K (u j) = ∑ t, algebraMap O K (N g j t) * m t - m j - v j := by
  constructor
  · rintro ⟨m, hm⟩
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    refine ⟨m, fun g v hv => ?_⟩
    have hg := (congrFun hm g).trans hv.symm
    have hg' : matRep (mapM (algebraMap O K) N) g m - m - v ∈ stdG O K k := (Submodule.Quotient.eq _).1 hg
    obtain ⟨u, hu⟩ := hg'
    exact ⟨u, fun j => congrFun hu j⟩
  · rintro ⟨m, hm⟩
    refine ⟨Submodule.Quotient.mk m, funext fun g => ?_⟩
    obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective _ (z g)
    obtain ⟨u, hu⟩ := hm g v hv
    have key : matRep (mapM (algebraMap O K) N) g m - m - v ∈ stdG O K k := ⟨u, funext hu⟩
    exact ((Submodule.Quotient.eq _).2 key).trans hv

theorem desc_abs {O K O' K' : Type} [CommRing O] [Field K] [Algebra O K] [CommRing O'] [Field K'] [Algebra O' K']
    (hinj : Function.Injective (algebraMap O K)) (hinj' : Function.Injective (algebraMap O' K'))
    (f : O →+* O') (φ : K →+* K') (hc : ∀ a, algebraMap O' K' (f a) = φ (algebraMap O K a))
    (R : K' →+ K) (hR : ∀ a x, R (φ a * x) = a * R x) (hR1 : ∀ a, R (φ a) = a)
    (hRO : ∀ x, ∃ y, algebraMap O K y = R (algebraMap O' K' x))
    {Γ : Type} [Group Γ] {k : ℕ} (N : Γ →* Matrix (Fin k) (Fin k) O)
    (q : (Fin k → K) ⧸ stdG O K k → (Fin k → K') ⧸ stdG O' K' k)
    (hq : ∀ v, q (Submodule.Quotient.mk v) = Submodule.Quotient.mk (fun j => φ (v j)))
    (z : Γ → (Fin k → K) ⧸ stdG O K k) (hz : (fun g => q (z g)) ∈ BD (stdLatG hinj' (mapM f N))) :
    z ∈ BD (stdLatG hinj N) := by
  obtain ⟨m, hm⟩ := (mem_BD_iff hinj' (mapM f N) (fun g => q (z g))).1 hz
  refine (mem_BD_iff hinj N z).2 ⟨fun j => R (m j), fun g v hv => ?_⟩
  obtain ⟨u, hu⟩ := hm g (fun j => φ (v j)) (by rw [← hv, hq])
  choose r hr using hRO
  refine ⟨fun j => r (u j), fun j => ?_⟩
  have hj : algebraMap O' K' (u j) = ∑ t, algebraMap O' K' (f (N g j t)) * m t - m j - φ (v j) := hu j
  rw [hr, hj, map_sub, map_sub, map_sum, hR1]
  simp only [hc, hR]

end Abstract

section Gen
variable {l : ℕ} [Fact l.Prime]

theorem exists_retr {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) :
    ∃ R : ↥LL'.1 →+ ↥LL.1, (∀ a x, R (IntermediateField.inclusion h a * x) = a * R x) ∧
      (∀ a, R (IntermediateField.inclusion h a) = a) ∧ ∀ x ∈ OL LL', R x ∈ OL LL := by
  haveI := LL.2
  haveI := LL'.2
  haveI : IsDedekindDomain ↥(OL LL) := integralClosure.isDedekindDomain ℤ_[l] ℚ_[l] ↥LL.1
  haveI : IsFractionRing ↥(OL LL) ↥LL.1 := integralClosure.isFractionRing_of_finite_extension ℚ_[l] ↥LL.1
  haveI : Module.Finite ℤ_[l] ↥(OL LL') :=
    IsIntegralClosure.finite ℤ_[l] ℚ_[l] ↥LL'.1 (integralClosure ℤ_[l] ↥LL'.1)
  obtain ⟨R, h1, h2, h3⟩ := exists_retr_abs (Z := ℤ_[l]) (O := ↥(OL LL)) (O' := ↥(OL LL')) (K := ↥LL.1)
    (K' := ↥LL'.1) (incO h) (fun _ => rfl) (OL LL').val.toRingHom (IntermediateField.inclusion h).toRingHom
    (fun _ => rfl) (fun x => by
      have hx : IsAlgebraic ℤ_[l] x :=
        (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] ↥LL'.1).2 (Algebra.IsAlgebraic.isAlgebraic x)
      obtain ⟨y, hy, hi⟩ := hx.exists_integral_multiple
      refine ⟨algebraMap ℤ_[l] ↥LL.1 y, ?_, ⟨y • x, hi⟩, Algebra.smul_def y x⟩
      rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1]
      simpa using hy)
  refine ⟨R, h1, h2, fun x hx => ?_⟩
  obtain ⟨y, hy⟩ := h3 ⟨x, hx⟩
  have hy' : (y : ↥LL'.1) = ((IntermediateField.inclusion h).restrictScalars ℤ_[l]) (R x) := hy
  have : IsIntegral ℤ_[l] (((IntermediateField.inclusion h).restrictScalars ℤ_[l]) (R x)) := hy' ▸ y.2
  exact (isIntegral_algHom_iff ((IntermediateField.inclusion h).restrictScalars ℤ_[l])
    (IntermediateField.inclusion h).injective).1 this

theorem desc {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) {Γ : Type} [Group Γ] {k : ℕ}
    (N : Γ →* Matrix (Fin k) (Fin k) ↥(OL LL))
    (z : Γ → (Fin k → ↥LL.1) ⧸ stdG ↥(OL LL) ↥LL.1 k)
    (hz : (fun g => liftQ h k (z g)) ∈
      BD (stdLatG (O := ↥(OL LL')) (LL := ↥LL'.1) Subtype.val_injective (mapM (incO h) N))) :
    z ∈ BD (stdLatG (O := ↥(OL LL)) (LL := ↥LL.1) Subtype.val_injective N) := by
  obtain ⟨R, hR, hR1, hRO⟩ := exists_retr h
  exact desc_abs (O := ↥(OL LL)) (K := ↥LL.1) (O' := ↥(OL LL')) (K' := ↥LL'.1) Subtype.val_injective
    Subtype.val_injective (incO h) (IntermediateField.inclusion h).toRingHom (fun _ => rfl) R hR hR1
    (fun x => ⟨⟨R x, hRO _ x.2⟩, rfl⟩) N (liftQ h k) (liftQ_mk h k) z hz

end Gen

theorem main : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (z : Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T),
    (fun g => liftQ C.le k (z g)) ∈ BD (latC C (locOC C M)) → z ∈ BD (Br.locLat D.nbr i w hw M) :=
  fun D i w hw C _ M z hz => desc C.le (Br.locO (D.nbr i w hw) (M.comp (decS D.nd w))) z hz

end GlobalTheory.UseLoc.DescBD
