import Development.EtaleCohomology.EtaleSheaves.KerLocPf
import Development.EtaleCohomology.EtaleSheaves.LeafGhostCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.DescLocPf LateralTheory.E.LeafGhostCut

namespace LateralTheory.E.TruncationKernel

def RelExact : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {U E : Spc} (f : U ⟶ E) (n : ℤ) (x : H R E F n),
  pull R f F n x = 0 → ∃ y : Hrel R f F n, fgt R f F n y = x

def RelNat : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {U E U' E' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') (u : U' ⟶ U)
  (e : E' ⟶ E) (comm : f' ≫ e = u ≫ f) (n : ℤ) (y : Hrel R f F n),
  fgt R f' F n (rpull R f f' u e comm F n y) = pull R e F n (fgt R f F n y)

def FgtInj : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {U E : Spc} (f : U ⟶ E) (n : ℤ),
  (∀ m : ℤ, m + 1 = n → Function.Surjective (pull R f F m)) → Function.Injective (fgt R f F n)

def RelDesc : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i n : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  ∀ P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop, PushClosed P → EtClosed P →
  (∀ m < n, ∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → BCn q i m φ c) →
  ∀ (D : CommRingCat.{0}) (d : A ⟶ D), P D d →
  ∀ (Y' : CommRingCat.{0}) (w : Y ⟶ Y') (φ' : D ⟶ Y'), IsPushout φ d w φ' →
  ∀ (E : CommRingCat.{0}) (e : D ⟶ E) (Y'' : CommRingCat.{0}) (u : Y' ⟶ Y'') (φ'' : E ⟶ Y''),
    Et e → SpS e → P E (d ≫ e) → ∀ hpo' : IsPushout φ' e u φ'',
  Function.Injective (rpl q i (Spec.map φ') (Spec.map φ'') (Spec.map u) (Spec.map e)
    (by rw [← Spec.map_comp, ← Spec.map_comp, hpo'.w]) n)

theorem exists_fgt_eq_of_pull_eq_zero : ∀ (R : Type) [CommRing R] (F : Shv R) {U E : Spc} (f : U ⟶ E) (n : ℤ) (x : H R E F n),
  pull R f F n x = 0 → ∃ y : Hrel R f F n, fgt R f F n y = x := by
  intro R _ F U E f n x hx
  obtain ⟨z, rfl⟩ := x.mk_surjective
  change CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map f)) z (zero_add n)) = 0 at hx
  rw [CohomologyClass.mk_eq_zero_iff] at hx
  obtain ⟨m, hm, β, hβ⟩ := hx
  refine ⟨CohomologyClass.mk (mappingCone.descCocycle _ (n.negOnePow • β) z hm ?_), ?_⟩
  · rw [δ_units_smul, hβ]
    rfl
  · refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
    exact mappingCone.inr_descCochain _ _ _ hm

theorem fgt_injective_of_pull_surjective : ∀ (R : Type) [CommRing R] (F : Shv R) {U E : Spc} (f : U ⟶ E) (n : ℤ),
  (∀ m : ℤ, m + 1 = n → Function.Surjective (pull R f F m)) → Function.Injective (fgt R f F n) := by
  intro R _ F U E f n hs
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨c, rfl⟩ := y.mk_surjective
  change CohomologyClass.mk (zcomp (Cocycle.ofHom (mappingCone.inr ((chains R).map f))) c (zero_add n)) = 0 at hy
  rw [CohomologyClass.mk_eq_zero_iff] at hy
  obtain ⟨m, hm, γ, hγ⟩ := hy
  change δ m n γ = (Cochain.ofHom (mappingCone.inr ((chains R).map f))).comp c.1 (zero_add n) at hγ
  have hdec : c.1 = mappingCone.descCochain _ ((mappingCone.inl ((chains R).map f)).comp c.1 (show -1 + n = m by lia))
      (δ m n γ) hm := by
    rw [mappingCone.ext_cochain_from_iff _ m n hm, hγ]
    simp
  have hc : δ n (n + 1) c.1 = 0 := Cocycle.δ_eq_zero c (n + 1)
  rw [hdec, mappingCone.δ_descCochain _ _ _ _ _ rfl] at hc
  have hc' := congrArg (fun z => (mappingCone.inl ((chains R).map f)).comp z (show -1 + (n + 1) = n by lia)) hc
  simp at hc'
  set a := (mappingCone.inl ((chains R).map f)).comp c.1 (show -1 + n = m by lia) with ha
  have hz : δ m n (a - n.negOnePow • (Cochain.ofHom ((chains R).map f)).comp γ (zero_add m)) = 0 := by
    rw [δ_sub, δ_units_smul, δ_ofHom_comp]
    rw [Int.negOnePow_succ, Units.neg_smul, ← sub_eq_add_neg] at hc'
    exact hc'
  obtain ⟨w, hw⟩ := hs m hm (CohomologyClass.mk (Cocycle.mk _ n hm hz))
  obtain ⟨w', rfl⟩ := w.mk_surjective
  change CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map f)) w' (zero_add m)) = _ at hw
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff] at hw
  obtain ⟨k, hk, α0, hα0⟩ := hw
  change δ k m α0 = (Cochain.ofHom ((chains R).map f)).comp w'.1 (zero_add m) -
    (a - n.negOnePow • (Cochain.ofHom ((chains R).map f)).comp γ (zero_add m)) at hα0
  rw [CohomologyClass.mk_eq_zero_iff]
  refine ⟨m, hm, mappingCone.descCochain _ (-α0) (γ + n.negOnePow • w'.1) hk, ?_⟩
  rw [mappingCone.δ_descCochain _ _ _ _ _ hm, δ_add, δ_units_smul, Cocycle.δ_eq_zero, smul_zero, add_zero]
  conv_rhs => rw [hdec]
  rw [mappingCone.ext_cochain_from_iff _ m n hm]
  refine ⟨?_, ?_⟩
  · simp only [mappingCone.inl_descCochain, Cochain.comp_add, mappingCone.inl_fst_assoc]
    simp only [δ_neg, hα0, Cochain.comp_units_smul, smul_add, smul_smul, Int.units_mul_self, one_smul, mappingCone.inl_snd_assoc, zero_comp, Cochain.zero_comp, add_zero]
    abel
  · simp

theorem relExact : RelExact := exists_fgt_eq_of_pull_eq_zero
theorem fgtInj : FgtInj := fgt_injective_of_pull_surjective

end LateralTheory.E.TruncationKernel
