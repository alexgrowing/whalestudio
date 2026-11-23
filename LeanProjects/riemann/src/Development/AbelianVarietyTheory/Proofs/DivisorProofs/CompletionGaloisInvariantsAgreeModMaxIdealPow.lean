import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorPowCompAdicCompletionMapToQuotientPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicCompletionMapInvariantsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicCompletionRingInjectiveInvariantsOfModuleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatTensorGaloisInjectiveInvariantsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicCompletionEquivariantEquivOfLevelIsosStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.InvAlg

theorem ker_evalₐ {A : Type} [CommRing A] [IsNoetherianRing A] (J : Ideal A) (n : ℕ) :
    RingHom.ker (AdicCompletion.evalₐ J n) = (J ^ n).map (algebraMap A (AdicCompletion J A)) := by
  ext a
  rw [RingHom.mem_ker, ← Submodule.restrictScalars_mem A, ← Ideal.smul_top_eq_map,
    AdicCompletion.pow_smul_top_eq_ker_eval J.fg_of_isNoetherianRing, LinearMap.mem_ker]
  have hle : (J ^ n • ⊤ : Ideal A) ≤ J ^ n := by intro x hx; simpa using hx
  rw [← AdicCompletion.factor_eval_eq_evalₐ J a hle]
  constructor
  · intro h
    obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval J A n a)
    rw [← hb] at h ⊢
    have : b ∈ J ^ n := Ideal.Quotient.eq_zero_iff_mem.mp h
    exact (Submodule.Quotient.mk_eq_zero _).mpr (by simpa using this)
  · intro h; rw [h, map_zero]

theorem completion_invariants_agree : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] [Module.Finite R R'], Function.Injective (algebraMap R R') → IsGal (algebraMap R R') → ∀ (C' : Type) [CommRing C'] [Algebra R C'] [Algebra R' C'] [IsScalarTower R R' C'] [Algebra.FiniteType R' C'] (act : Gal (algebraMap R R') →* (C' ≃ₐ[R] C')), (∀ σ r, act σ (algebraMap R' C' r) = algebraMap R' C' (σ.1 r)) → ∀ (O : Type) [CommRing O] [Algebra R O] [Module.Flat R O] [Algebra.FiniteType R O] (i : ∀ e : ℕ, O →ₐ[R] C' ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R C')), (∀ e x y, Ideal.Quotient.mk _ y = i (e + 1) x → Ideal.Quotient.mk _ y = i e x) → (∀ e σ x y, Ideal.Quotient.mk _ y = i e x → Ideal.Quotient.mk _ (act σ y) = i e x) → (∀ e, Function.Surjective (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) ∧ RingHom.ker (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) = (maximalIdeal R ^ (e + 1)).map (algebraMap R (TensorProduct R O R'))) → ∀ C : Subalgebra R C', (∀ x, x ∈ C ↔ ∀ σ, act σ x = x) → Algebra.FiniteType R C → Module.Finite C C' → ∀ e : ℕ, ∃ gm : (O ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R O)) ≃ₐ[R] (C ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R C)), ∀ (x : O) (c : C), gm (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ c → Ideal.Quotient.mk ((maximalIdeal R ^ (e + 1)).map (algebraMap R C')) (c : C') = i e x := by
  intro R _ _ _ hR R' _ _ _ _ hinj hgal C' _ _ _ _ _ act hact O _ _ _ _ i h1 h2 h3 C hC hCft hCfin e
  classical
  haveI : IsNoetherianRing R := hR.1
  haveI := hCft
  haveI := hCfin
  haveI : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing R C
  haveI : IsNoetherianRing O := Algebra.FiniteType.isNoetherianRing R O
  haveI : Finite (Gal (algebraMap R R')) := hgal.1
  let T := TensorProduct R O R'
  let JC : Ideal C := (maximalIdeal R).map (algebraMap R C)
  let JO : Ideal O := (maximalIdeal R).map (algebraMap R O)
  let IC : Ideal C' := JC.map (algebraMap C C')
  let IT : Ideal T := JO.map (algebraMap O T)
  let gC : Gal (algebraMap R R') → (C' →ₐ[C] C') := fun σ =>
    { (act σ).toRingEquiv.toRingHom with commutes' := fun c => (hC _).1 c.2 σ }

  have hfixC : ∀ x : C', x ∈ LinearMap.range (Algebra.linearMap C C') ↔ ∀ σ, (gC σ).toLinearMap x = x := by
    intro x; constructor
    · rintro ⟨c, rfl⟩ σ; exact (gC σ).commutes c
    · intro hx; exact ⟨⟨x, (hC x).2 hx⟩, rfl⟩
  have hmC := GlobalTheory.T.adicCompletion_map_injective_and_invariants C JC C C' (Algebra.linearMap C C') _ (fun σ => (gC σ).toLinearMap) Subtype.val_injective hfixC
  obtain ⟨injC, rangeC⟩ := GlobalTheory.T.adicCompletion_ring_injective_invariants_of_module C C' JC _ gC hmC.1 hmC.2

  obtain ⟨injOT, fixOT⟩ := GlobalTheory.T.flat_tensor_galois_injective_invariants R R' O hinj hgal
  have hfixO : ∀ t : T, t ∈ LinearMap.range (Algebra.linearMap O T) ↔
      ∀ σ, (galTensor O σ).toLinearMap t = t := by
    intro t; constructor
    · rintro ⟨x, rfl⟩ σ; exact (galTensor O σ).commutes x
    · intro ht; obtain ⟨x, hx⟩ := fixOT t ht; exact ⟨x, hx⟩
  have hmO := GlobalTheory.T.adicCompletion_map_injective_and_invariants O JO O T (Algebra.linearMap O T) _ (fun σ => (galTensor O σ).toLinearMap) injOT hfixO
  obtain ⟨injO, rangeO⟩ := GlobalTheory.T.adicCompletion_ring_injective_invariants_of_module O T JO _ (galTensor O) hmO.1 hmO.2

  have hIT : IT = (maximalIdeal R).map (algebraMap R T) := by
    simp only [IT, JO, Ideal.map_map]; rw [← IsScalarTower.algebraMap_eq]
  have hIC : IC = (maximalIdeal R).map (algebraMap R C') := by
    simp only [IC, JC, Ideal.map_map]; rw [← IsScalarTower.algebraMap_eq]
  have hCσ : ∀ σ, IC.map (act σ).toRingEquiv.toRingHom ≤ IC := fun σ => map_algebraMap_le (gC σ) JC
  obtain ⟨Ψ, hΨσ, hΨi⟩ := GlobalTheory.T.adicCompletion_equivariant_equiv_of_level_isos R (maximalIdeal R) R' C' act hact O i h1 h2 h3 IT IC hIT hIC
    (fun σ => map_algebraMap_le (galTensor O σ) JO) hCσ
  let κC := cmap (algebraMap C C') JC IC le_rfl
  let κO1 := cmap (algebraMap O T) JO IT le_rfl
  let κO : AdicCompletion JO O →+* AdicCompletion IC C' := (Ψ : _ →+* _).comp κO1
  have hr : ∀ y, y ∈ Set.range κO ↔ y ∈ Set.range κC := by
    intro y
    rw [rangeC y]
    have : y ∈ Set.range κO ↔ Ψ.symm y ∈ Set.range κO1 := by
      constructor
      · rintro ⟨a, rfl⟩; exact ⟨a, by simp [κO]⟩
      · rintro ⟨a, ha⟩; exact ⟨a, by simp [κO, ha]⟩
    rw [this, rangeO]
    refine forall_congr' fun σ => ?_
    rw [← Ψ.injective.eq_iff, hΨσ, Ψ.apply_symm_apply]
  have hrange : κO.range = κC.range := by ext y; exact hr y
  have injκO : Function.Injective κO := Ψ.injective.comp injO
  let eO : AdicCompletion JO O ≃+* κO.range := RingEquiv.ofBijective κO.rangeRestrict
    ⟨fun a b h => injκO (congrArg Subtype.val h), κO.rangeRestrict_surjective⟩
  let eC : AdicCompletion JC C ≃+* κC.range := RingEquiv.ofBijective κC.rangeRestrict
    ⟨fun a b h => injC (congrArg Subtype.val h), κC.rangeRestrict_surjective⟩
  let Θ : AdicCompletion JO O ≃+* AdicCompletion JC C := (eO.trans (RingEquiv.subringCongr hrange)).trans eC.symm
  have hΘ : ∀ a, κC (Θ a) = κO a := fun a =>
    congrArg Subtype.val (eC.apply_symm_apply ((RingEquiv.subringCongr hrange) (eO a)))

  have hΘR : ∀ r : R, Θ (algebraMap R _ r) = algebraMap R _ r := by
    intro r
    apply injC
    rw [hΘ]
    show Ψ (κO1 (algebraMap R (AdicCompletion JO O) r)) = κC (algebraMap R (AdicCompletion JC C) r)
    rw [AdicCompletion.algebraMap_apply, AdicCompletion.algebraMap_apply, cmap_of, cmap_of,
      ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      ← AdicCompletion.algebraMap_apply IT r, ← AdicCompletion.algebraMap_apply IC r]
    exact Ψ.commutes r
  have hOm : ∀ k, (JO ^ k).map (algebraMap O (AdicCompletion JO O)) =
      ((maximalIdeal R) ^ k).map (algebraMap R (AdicCompletion JO O)) := by
    intro k; simp only [JO, Ideal.map_pow, Ideal.map_map]; rfl
  have hCm : ∀ k, (JC ^ k).map (algebraMap C (AdicCompletion JC C)) =
      ((maximalIdeal R) ^ k).map (algebraMap R (AdicCompletion JC C)) := by
    intro k; simp only [JC, Ideal.map_pow, Ideal.map_map]; rfl
  have key : ∀ a, AdicCompletion.evalₐ JC (e + 1) (Θ a) = 0 ↔ AdicCompletion.evalₐ JO (e + 1) a = 0 := by
    intro a
    rw [← RingHom.mem_ker, ← RingHom.mem_ker, ker_evalₐ, ker_evalₐ, hOm, hCm]
    have hmap : ((maximalIdeal R ^ (e + 1)).map (algebraMap R (AdicCompletion JC C))) =
        ((maximalIdeal R ^ (e + 1)).map (algebraMap R (AdicCompletion JO O))).map (Θ : _ →+* _) := by
      rw [Ideal.map_map]; congr 1; exact RingHom.ext fun r => (hΘR r).symm
    rw [hmap, Ideal.map_comap_of_equiv, Ideal.mem_comap, RingEquiv.symm_apply_apply]
  have hJC : JC ^ (e + 1) = ((maximalIdeal R) ^ (e + 1)).map (algebraMap R C) := (Ideal.map_pow _ _ _).symm
  let ψ0 : O →+* C ⧸ JC ^ (e + 1) :=
    (AdicCompletion.evalₐ JC (e + 1) : AdicCompletion JC C →+* C ⧸ JC ^ (e + 1)).comp
      ((Θ : _ →+* _).comp (algebraMap O (AdicCompletion JO O)))
  have hψ0 : ∀ x, ψ0 x = AdicCompletion.evalₐ JC (e + 1) (Θ (AdicCompletion.of JO O x)) := fun x => rfl
  have hsurj : Function.Surjective ψ0 := by
    intro z
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective
      (AdicCompletion.evalₐ JO (e + 1) (Θ.symm (AdicCompletion.of JC C c)))
    refine ⟨x, ?_⟩
    have h0 : AdicCompletion.evalₐ JO (e + 1)
        (AdicCompletion.of JO O x - Θ.symm (AdicCompletion.of JC C c)) = 0 := by
      rw [map_sub, AdicCompletion.evalₐ_of, hx, sub_self]
    have h1 := (key _).2 h0
    rw [map_sub, map_sub, RingEquiv.apply_symm_apply, AdicCompletion.evalₐ_of, sub_eq_zero] at h1
    rw [hψ0, h1]
  have hker : RingHom.ker ψ0 = ((maximalIdeal R) ^ (e + 1)).map (algebraMap R O) := by
    ext x
    rw [RingHom.mem_ker, hψ0, key, AdicCompletion.evalₐ_of, Ideal.Quotient.eq_zero_iff_mem]
    simp only [JO, Ideal.map_pow]
  let gR : (O ⧸ ((maximalIdeal R) ^ (e + 1)).map (algebraMap R O)) ≃+*
      (C ⧸ ((maximalIdeal R) ^ (e + 1)).map (algebraMap R C)) :=
    ((Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)).trans
      (Ideal.quotEquivOfEq hJC)
  have hgR : ∀ x, gR (Ideal.Quotient.mk _ x) = Ideal.quotEquivOfEq hJC (ψ0 x) := fun x => rfl
  let gm : (O ⧸ ((maximalIdeal R) ^ (e + 1)).map (algebraMap R O)) ≃ₐ[R]
      (C ⧸ ((maximalIdeal R) ^ (e + 1)).map (algebraMap R C)) :=
    AlgEquiv.ofRingEquiv (f := gR) (fun r => by
      change gR (Ideal.Quotient.mk _ (algebraMap R O r)) = Ideal.Quotient.mk _ (algebraMap R C r)
      rw [hgR, hψ0, ← AdicCompletion.algebraMap_apply JO r, hΘR, AdicCompletion.algebraMap_apply,
        AdicCompletion.evalₐ_of, Ideal.quotEquivOfEq_mk])
  refine ⟨gm, fun x c hxc => ?_⟩
  have h1' : ψ0 x = Ideal.Quotient.mk (JC ^ (e + 1)) c := by
    apply (Ideal.quotEquivOfEq hJC).injective
    rw [Ideal.quotEquivOfEq_mk]; exact (hgR x).symm.trans hxc
  have h2' : AdicCompletion.evalₐ IC (e + 1) (Ψ (AdicCompletion.of IT T (x ⊗ₜ[R] (1 : R')))) =
      Ideal.Quotient.mk (IC ^ (e + 1)) (c : C') := by
    have := congrArg (Ideal.quotientMap (IC ^ (e + 1)) (algebraMap C C')
      (pow_le_comap (algebraMap C C') (le_rfl : JC.map (algebraMap C C') ≤ IC) (e + 1))) h1'
    rw [hψ0, ← evalₐ_cmap] at this
    change AdicCompletion.evalₐ IC (e + 1) (κC (Θ _)) = _ at this
    rw [hΘ] at this
    rw [show κO (AdicCompletion.of JO O x) = Ψ (AdicCompletion.of IT T (x ⊗ₜ[R] (1 : R'))) from by
      show Ψ (κO1 _) = _
      rw [cmap_of]; rfl] at this
    rw [this, Ideal.quotientMap_mk]; rfl
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (i e x)
  have h3' := hΨi e x y hy
  rw [h2', Ideal.Quotient.eq] at h3'
  rw [← hy, Ideal.Quotient.eq]
  have hpow : IC ^ (e + 1) = ((maximalIdeal R) ^ (e + 1)).map (algebraMap R C') := by rw [hIC, Ideal.map_pow]
  rw [← hpow]; exact h3'

end GlobalTheory.InvAlg
