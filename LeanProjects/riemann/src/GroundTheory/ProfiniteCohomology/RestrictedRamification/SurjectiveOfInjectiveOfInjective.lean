import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.Brauer
import GroundTheory.ProfiniteCohomology.RestrictedRamification.FiniteSetOfNsmulEqZeroQZ
import GroundTheory.ProfiniteCohomology.RestrictedRamification.CohomologyMapAlongInvariantsGsKernelMorCompGsBra
import GroundTheory.ProfiniteCohomology.RestrictedRamification.DivisorModuleSupport
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BrauerFrob
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain IntermediateField GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

theorem surjective_of_injective_of_injective {α β : Type*} [Finite α] {f : α → β} {g : β → α}
    (hf : Function.Injective f) (hg : Function.Injective g) : Function.Surjective f := by
  have : Finite β := Finite.of_injective g hg
  have hfg : Function.Injective (f ∘ g) := hf.comp hg
  exact fun b => by
    obtain ⟨a, ha⟩ := Finite.injective_iff_surjective.1 hfg b
    exact ⟨g a, ha⟩

section Val

variable (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1))) (ℓ : ℕ) (hℓ : ℓ.Prime)
  (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S) (ιs : LocalEmbeddings K)

def gsVal (v : HeightOneSpectrum (𝓞 K.1)) (hv : v ∉ S) :
    cohomology (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 2 →+
      cohomology (trivRep Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1) ℤ) 2 :=
  (cohomologyMapAlong (decompHomS (v.adicCompletion K.1) S (ιs.fin v))
    (continuous_decompHomS (Kv := v.adicCompletion K.1) S (ιs.fin v))
    (ordEmbMor S (ιs.fin v) hv) 2).hom.toAddMonoidHom

def gsLoc (v : HeightOneSpectrum (𝓞 K.1)) :
    cohomology (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 2 →+ localGaloisCohomology K 2 (.inr v) :=
  (gsLocalRes S (ιs.fin v) 2).hom.toAddMonoidHom.comp
    (cohomologyULiftIntAddEquiv (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 2).toAddMonoidHom

theorem gsLoc_eq_zero_iff (v : HeightOneSpectrum (𝓞 K.1)) (hv : v ∉ S)
    (x : cohomology (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 2) :
    gsLoc K S ιs v x = 0 ↔ gsVal K S ιs v hv x = 0 :=
  gsLocalRes_eq_zero_iff S (ιs.fin v) hv x

variable (v : HeightOneSpectrum (𝓞 K.1)) (hv : v ∉ S)
  (gvChar : cohomology (trivRep Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1) ℤ) 2 ≃+
    (Additive Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1) →ₜ+ QZ))
  (σ : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1))

end Val

theorem exists_val_eq_of_counting {A L C Q : Type*} [AddCommGroup A] [AddCommGroup L] [AddCommGroup C]
    [AddCommGroup Q] (loc : A →+ L) (val : A →+ C) (hker : ∀ a, loc a = 0 ↔ val a = 0)
    {J : Type*} (evs : J → C →+ Q) (hP : ∀ a j, evs j (val a) = 0)
    (ev : C →+ Q) (hev : ∀ c, (∀ j, evs j c = 0) → ev c = 0 → c = 0) (inv : L ≃+ Q) (m : ℕ)
    (hQ : {q : Q | m • q = 0}.Finite) (R : A → Prop)
    (hsurj : ∀ t : L, m • t = 0 → ∃ a, loc a = t ∧ R a) (c : C) (hc : ∀ j, evs j c = 0)
    (hcm : m • c = 0) : ∃ a, val a = c ∧ R a := by
  let P : C → Prop := fun c => ∀ j, evs j c = 0
  have hPsub : ∀ c₁ c₂, P c₁ → P c₂ → P (c₁ - c₂) := fun c₁ c₂ h₁ h₂ j => by
    rw [map_sub, h₁ j, h₂ j, sub_zero]
  let T := {t : L // m • t = 0}
  choose X hX hX' using fun t : T => hsurj t.1 t.2
  let U := {c : C // m • c = 0 ∧ P c}
  have hΦ : ∀ t : T, m • val (X t) = 0 ∧ P (val (X t)) := fun t =>
    ⟨by rw [← map_nsmul]; exact (hker _).1 (by rw [map_nsmul, hX t, t.2]), hP _⟩
  let Φ : T → U := fun t => ⟨val (X t), hΦ t⟩
  have hΦi : Function.Injective Φ := by
    intro t₁ t₂ h
    have h1 : val (X t₁ - X t₂) = 0 := by rw [map_sub, sub_eq_zero]; exact congrArg Subtype.val h
    have h2 := (hker _).2 h1
    rw [map_sub, hX, hX, sub_eq_zero] at h2
    exact Subtype.ext h2
  have hΨ : ∀ c : U, m • inv.symm (ev c.1) = 0 := fun c => by
    apply inv.injective
    rw [map_nsmul, inv.apply_symm_apply, ← map_nsmul, c.2.1, map_zero, map_zero]
  let Ψ : U → T := fun c => ⟨inv.symm (ev c.1), hΨ c⟩
  have hΨi : Function.Injective Ψ := by
    intro c₁ c₂ h
    have h1 : ev c₁.1 = ev c₂.1 := inv.symm.injective (congrArg Subtype.val h)
    exact Subtype.ext (sub_eq_zero.1 (hev _ (hPsub _ _ c₁.2.2 c₂.2.2) (by rw [map_sub, h1, sub_self])))
  have hTfin : Finite T := by
    have := hQ.to_subtype
    exact Finite.of_injective (fun t : T => (⟨inv t.1, by
      change m • _ = 0
      rw [← map_nsmul, t.2, map_zero]⟩ : {q : Q | m • q = 0}))
      fun t₁ t₂ h => Subtype.ext (inv.injective (congrArg Subtype.val h))
  obtain ⟨t, ht⟩ := surjective_of_injective_of_injective hΦi hΨi ⟨c, hcm, hc⟩
  exact ⟨X t, congrArg Subtype.val ht, hX' t⟩

section Frob

variable (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1))) (ℓ : ℕ) (hℓ : ℓ.Prime)
  (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S) (ιs : LocalEmbeddings K)

def FrobData (v : HeightOneSpectrum (𝓞 K.1)) : Prop :=
  ∃ (gvChar : cohomology (trivRep Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1) ℤ) 2 ≃+
      (Additive Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1) →ₜ+ QZ))
    (σ : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1)),
    (∀ (A : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep A] (y : cohomology A 2)
      (f : Rep.res (decompHomS (v.adicCompletion K.1) S (ιs.fin v)) A ⟶
        trivRep Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1) ℤ) g,
      decompHomS (v.adicCompletion K.1) S (ιs.fin v) g = 1 →
        gvChar ((cohomologyMapAlong (decompHomS (v.adicCompletion K.1) S (ιs.fin v))
          (continuous_decompHomS (Kv := v.adicCompletion K.1) S (ιs.fin v)) f 2).hom y) (Additive.ofMul g) = 0) ∧
    (∀ χ : Additive Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1) →ₜ+ QZ,
      (∀ g, decompHomS (v.adicCompletion K.1) S (ιs.fin v) g = 1 → χ (Additive.ofMul g) = 0) →
        χ (Additive.ofMul σ) = 0 → χ = 0)

def evalChar {G : Type} [Group G] [TopologicalSpace G] (g : G) : (Additive G →ₜ+ QZ) →+ QZ where
  toFun χ := χ (Additive.ofMul g)
  map_zero' := rfl
  map_add' _ _ := rfl

set_option maxHeartbeats 2000000 in
include hℓ hS in

theorem exists_gsVal_eq (v : HeightOneSpectrum (𝓞 K.1)) (hv : v ∉ S) (hF : FrobData K S ιs v) (n : ℕ)
    {A : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)} [IsDiscreteRep A] (y : cohomology A 2)
    (f : Rep.res (decompHomS (v.adicCompletion K.1) S (ιs.fin v)) A ⟶
      trivRep Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1) ℤ)
    (hy : ℓ ^ n • (cohomologyMapAlong (decompHomS (v.adicCompletion K.1) S (ιs.fin v))
      (continuous_decompHomS (Kv := v.adicCompletion K.1) S (ιs.fin v)) f 2).hom y = 0) :
    ∃ x : cohomology (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 2,
      gsVal K S ιs v hv x = (cohomologyMapAlong (decompHomS (v.adicCompletion K.1) S (ιs.fin v))
        (continuous_decompHomS (Kv := v.adicCompletion K.1) S (ιs.fin v)) f 2).hom y ∧
      ∀ v' : HeightOneSpectrum (𝓞 K.1), v' ∉ S → v' ≠ v → gsLoc K S ιs v' x = 0 := by
  refine hF.elim fun gvChar hF => hF.elim fun σ hF => ?_
  have hU1 := hF.1
  have hU2 := hF.2
  exact exists_val_eq_of_counting (gsLoc K S ιs v) (gsVal K S ιs v hv) (gsLoc_eq_zero_iff K S ιs v hv)
    (J := {g // decompHomS (v.adicCompletion K.1) S (ιs.fin v) g = 1})
    (fun g => (evalChar g.1).comp gvChar.toAddMonoidHom)
    (fun x g => hU1 _ x (ordEmbMor S (ιs.fin v) hv) g.1 g.2)
    ((evalChar σ).comp gvChar.toAddMonoidHom)
    (fun c hc h0 => gvChar.injective ((hU2 _ (fun g hg => hc ⟨g, hg⟩) h0).trans (map_zero _).symm))
    (AddEquiv.ofBijective (placeInv (.inr v)) (placeInv_bijective_inr (K := K) v)) (ℓ ^ n)
    (finite_setOf_nsmul_eq_zero_QZ (pow_ne_zero n hℓ.ne_zero))
    (fun x => ∀ v' : HeightOneSpectrum (𝓞 K.1), v' ∉ S → v' ≠ v → gsLoc K S ιs v' x = 0)
    (fun t ht => (exists_gsLocalRes_eq_single K S ℓ hℓ hS ιs v hv t n ht).elim fun x hx =>
      ⟨(cohomologyULiftIntAddEquiv (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 2).symm x,
        (congrArg (gsLocalRes S (ιs.fin v) 2).hom (AddEquiv.apply_symm_apply _ x)).trans hx.2.1,
        fun v' hv' hne => (congrArg (gsLocalRes S (ιs.fin v') 2).hom (AddEquiv.apply_symm_apply _ x)).trans
          (hx.2.2 v' hv' hne)⟩) _ (fun g => hU1 A y f g.1 g.2) hy

end Frob

section H3

variable (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1))) (ℓ : ℕ) (hℓ : ℓ.Prime)
  (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S) (ιs : LocalEmbeddings K)

set_option maxHeartbeats 4000000 in
include hℓ hS in

theorem exists_sUnitsQuotDiv_gsQuotMor_eq (hF : ∀ v : HeightOneSpectrum (𝓞 K.1), v ∉ S → FrobData K S ιs v)
    (d : cohomology (gsDiv K S ιs ℤ) 2) (n : ℕ) (hd : ℓ ^ n • d = 0) :
    ∃ x : cohomology (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 2,
      (cohomologyMap (sUnitsQuotDiv K S ιs) 2).hom ((cohomologyMap (gsQuotMor K S) 2).hom x) = d := by
  have hfin := finite_divFunEval_ne_zero (gsDecomp K S ιs) (continuous_gsDecomp K S ιs) ℤ 2 d
  have hx : ∀ u : {v : HeightOneSpectrum (𝓞 K.1) // v ∉ S},
      ∃ x : cohomology (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 2,
        gsVal K S ιs u.1 u.2 x = (cohomologyMapAlong (gsDecomp K S ιs u) (continuous_gsDecomp K S ιs u)
          (divFunEval (gsDecomp K S ιs) ℤ u) 2).hom d ∧
        ∀ v' : HeightOneSpectrum (𝓞 K.1), v' ∉ S → v' ≠ u.1 → gsLoc K S ιs v' x = 0 := fun u =>
    exists_gsVal_eq K S ℓ hℓ hS ιs u.1 u.2 (hF u.1 u.2) n d (divFunEval (gsDecomp K S ιs) ℤ u)
      ((map_nsmul _ _ _).symm.trans ((congrArg _ hd).trans (map_zero _)))
  choose x hx hx' using hx
  refine ⟨∑ u ∈ hfin.toFinset, x u, sub_eq_zero.1 ?_⟩
  refine eq_zero_of_divFunEval_eq_zero (gsDecomp K S ιs) (continuous_gsDecomp K S ιs) _ fun u => ?_
  have e1 : (cohomologyMapAlong (gsDecomp K S ιs u) (continuous_gsDecomp K S ιs u)
      (divFunEval (gsDecomp K S ιs) ℤ u) 2).hom ((cohomologyMap (sUnitsQuotDiv K S ιs) 2).hom
        ((cohomologyMap (gsQuotMor K S) 2).hom (∑ u ∈ hfin.toFinset, x u))) =
      gsVal K S ιs u.1 u.2 (∑ u ∈ hfin.toFinset, x u) :=
    divFunEval_sUnitsQuotDiv_apply K S ιs u _
  have e2 : gsVal K S ιs u.1 u.2 (∑ u ∈ hfin.toFinset, x u) =
      (cohomologyMapAlong (gsDecomp K S ιs u) (continuous_gsDecomp K S ιs u)
        (divFunEval (gsDecomp K S ιs) ℤ u) 2).hom d := by
    rw [map_sum]
    have hne : ∀ w ∈ hfin.toFinset, w ≠ u → gsVal K S ιs u.1 u.2 (x w) = 0 := fun w _ hw =>
      (gsLoc_eq_zero_iff K S ιs u.1 u.2 _).1 (hx' w u.1 u.2 fun h => hw (Subtype.ext h).symm)
    by_cases hu : u ∈ hfin.toFinset
    · rw [Finset.sum_eq_single_of_mem u hu hne, hx u]
    · rw [Finset.sum_eq_zero fun w hw => hne w hw fun h => hu (h ▸ hw)]
      rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hu
      exact hu.symm
  exact (map_sub _ _ _).trans (sub_eq_zero.2 (e1.trans e2))

end H3

section H3Final

variable (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1))) (ℓ : ℕ) (hℓ : ℓ.Prime)
  (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)

def sUnitsδ : cohomology (galUnitsModSUnits K.1 ℚ̄ S) 2 →+ cohomology (galSUnitsMax K.1 ℚ̄ S) 3 :=
  (δ (sUnitsQuotSequence_shortExact K.1 ℚ̄ S) 2 3 rfl).hom.toAddMonoidHom

theorem exists_sUnitsδ_eq (z : cohomology (galSUnitsMax K.1 ℚ̄ S) 3)
    (hz : (cohomologyMap (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S)) 3).hom z = 0) :
    ∃ p, sUnitsδ K S p = z :=
  exists_δ_eq_of_cohomologyMap_f_eq_zero (sUnitsQuotSequence_shortExact K.1 ℚ̄ S) 2 3 rfl z hz

theorem sUnitsδ_gsQuotMor (x : cohomology (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 2) :
    sUnitsδ K S ((cohomologyMap (gsQuotMor K S) 2).hom x) = 0 :=
  congrArg (fun m => ModuleCat.Hom.hom m x) (comp_δ (sUnitsQuotSequence_shortExact K.1 ℚ̄ S) 2 3 rfl)

def gsDivH2 (ιs : LocalEmbeddings K) :
    cohomology (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 2 →+ cohomology (gsDiv K S ιs ℤ) 2 :=
  (cohomologyMap (sUnitsQuotDiv K S ιs) 2).hom.toAddMonoidHom.comp
    (cohomologyMap (gsQuotMor K S) 2).hom.toAddMonoidHom

set_option maxHeartbeats 4000000 in
include hℓ hS in

theorem eq_zero_of_h3_sUnits_of_frob (ιs : LocalEmbeddings K)
    (hF : ∀ v : HeightOneSpectrum (𝓞 K.1), v ∉ S → FrobData K S ιs v)
    (z : cohomology (galSUnitsMax K.1 ℚ̄ S) 3) (k : ℕ) (hz : ℓ ^ k • z = 0) : z = 0 := by
  have hf : (cohomologyMap (sUnitsToUnits S (maxUnramifiedOutside K.1 ℚ̄ S)) 3).hom z = 0 :=
    eq_zero_of_h3_gsUnits K S ℓ hℓ hS _ k
      ((map_nsmul _ _ _).symm.trans ((congrArg _ hz).trans (map_zero _)))
  refine (exists_sUnitsδ_eq K S z hf).elim fun p hp => ?_
  have hpk : ℓ ^ k • sUnitsδ K S p = 0 := hp.symm ▸ hz
  refine (exists_primary_map_eq (sUnitsδ K S) hℓ (isTorsion_cohomology _ (by norm_num) p) hpk).elim
    fun p' hp' => ?_
  refine hp'.1.elim fun j hj => ?_
  have hd : ℓ ^ j • (cohomologyMap (sUnitsQuotDiv K S ιs) 2).hom p' = 0 :=
    (map_nsmul _ _ _).symm.trans ((congrArg _ hj).trans (map_zero _))
  refine (exists_sUnitsQuotDiv_gsQuotMor_eq K S ℓ hℓ hS ιs hF _ j hd).elim fun x hx => ?_
  have hx2 : ℓ ^ j • gsDivH2 K S ιs x = 0 := by
    change ℓ ^ j • (cohomologyMap (sUnitsQuotDiv K S ιs) 2).hom ((cohomologyMap (gsQuotMor K S) 2).hom x) = 0
    rw [hx]
    exact hd
  refine (exists_primary_map_eq (gsDivH2 K S ιs) hℓ (isTorsion_cohomology _ (by norm_num) x) hx2).elim
    fun x' hx' => ?_
  refine hx'.1.elim fun i hi => ?_
  have hq : (cohomologyMap (sUnitsQuotDiv K S ιs) 2).hom (p' - (cohomologyMap (gsQuotMor K S) 2).hom x') = 0 := by
    rw [map_sub, sub_eq_zero]
    exact hx.symm.trans hx'.2.symm
  have hqk : ℓ ^ (i + j) • (p' - (cohomologyMap (gsQuotMor K S) 2).hom x') = 0 := by
    have h1 : ℓ ^ (i + j) • p' = 0 := by rw [pow_add, mul_smul, hj, smul_zero]
    have h2 : ℓ ^ (i + j) • (cohomologyMap (gsQuotMor K S) 2).hom x' = 0 := by
      rw [← map_nsmul, pow_add, mul_comm, mul_smul, hi, smul_zero, map_zero]
    rw [smul_sub, h1, h2, sub_zero]
  have hq0 : p' - (cohomologyMap (gsQuotMor K S) 2).hom x' = 0 :=
    eq_zero_of_mem_range_δ_of_coprime (picSequence_shortExact K S ιs) 1 2 rfl
      (exists_δ_pic_eq K S ιs _ hq) ℓ
      (fun r => exists_coprime_smul_cohomology_eq_zero (picInfRep K S ιs) ℓ
        (exists_coprime_smul_picInfRep K S ιs ℓ hℓ hS) 1 r) (i + j) hqk
  rw [← hp, ← hp'.2, sub_eq_zero.1 hq0]
  exact sUnitsδ_gsQuotMor K S x'

end H3Final

section H3Main

variable (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1)))

theorem frobData (ιs : LocalEmbeddings K) (v : HeightOneSpectrum (𝓞 K.1)) (hv : v ∉ S) :
    FrobData K S ιs v :=
  (exists_unramifiedDegree_eq_one (K := K) (v := v)).elim fun σ hσ =>
    ⟨gvChar _, σ, fun _ _ y f g hg => gvChar_decompHomS_eq_zero S (ιs.fin v) y f g hg,
      fun χ hχ h0 => eq_zero_of_decompHomS_of_unramifiedDegree S (ιs.fin v) hv χ hχ σ hσ h0⟩

theorem eq_zero_of_h3_sUnits (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (z : cohomology (galSUnitsMax K.1 ℚ̄ S) 3) (k : ℕ) (hz : ℓ ^ k • z = 0) : z = 0 :=
  eq_zero_of_h3_sUnits_of_frob K S ℓ hℓ hS (nonempty_localEmbeddings K).some
    (fun v hv => frobData K S _ v hv) z k hz

end H3Main

end

end GroundTheory.ProfCoh
