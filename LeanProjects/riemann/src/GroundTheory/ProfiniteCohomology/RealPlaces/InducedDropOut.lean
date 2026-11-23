import Mathlib
import GroundTheory.ProfiniteCohomology.RealPlaces.InducedDefs
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

universe u

section ProdSeq

variable {k : Type u} [CommRing k] (M N : CochainComplex (ModuleCat.{u} k) ℕ)

noncomputable def prodInr : N ⟶ prodComplex M N :=
  prodLift 0 (𝟙 N)

theorem prodInr_f_hom_apply (n : ℕ) (y : N.X n) :
    ((prodInr M N).f n).hom y = ((0 : M.X n), y) :=
  rfl

noncomputable def prodSeq : ShortComplex (CochainComplex (ModuleCat.{u} k) ℕ) :=
  ShortComplex.mk (prodInr M N) (prodFst M N)
    (HomologicalComplex.hom_ext _ _ fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl))

theorem prodSeq_shortExact : (prodSeq M N).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n => {
    exact := by
      rw [ShortComplex.moduleCat_exact_iff]
      intro (p : M.X n × N.X n) hp
      exact ⟨p.2, Prod.ext hp.symm rfl⟩
    mono_f := (ModuleCat.mono_iff_injective _).2 fun _ _ h => congrArg Prod.snd h
    epi_g := (ModuleCat.epi_iff_surjective _).2 fun (x : M.X n) =>
      ⟨((x, 0) : M.X n × N.X n), rfl⟩ }

end ProdSeq

section NormClass

variable {k F' : Type u} [CommRing k] [Group F'] [TopologicalSpace F'] [IsTopologicalGroup F']
  [Fintype F'] (B : Rep.{u} k F') [IsDiscreteRep B]

theorem exists_normClass_eq (hB : ∀ x ∈ B.ρ.invariants, ∃ m, B.ρ.norm m = x) (c : cohomology B 0) :
    ∃ m, normClass B m = c := by
  obtain ⟨z, rfl⟩ := homologyπ_hom_surjective (cochainsComplex B) 0 c
  obtain ⟨v, hx⟩ : ∃ v, ((cochainsComplex B).iCycles 0).hom z = zeroCochain B v := by
    refine ⟨cochainOf B (((cochainsComplex B).iCycles 0).hom z) Fin.elim0, ?_⟩
    apply cochainOf_injective
    funext σ
    rw [cochainOf_zeroCochain, Subsingleton.elim σ Fin.elim0]
  have hd : ((cochainsComplex B).d 0 1).hom (zeroCochain B v) = 0 := by
    rw [← hx]
    exact (hom_apply_hom_apply_of_comp_eq ((cochainsComplex B).iCycles_d 0 1) z).trans rfl
  have hinv : v ∈ B.ρ.invariants := fun g => by
    have h := congrFun (congrArg (cochainOf B) hd) (fun _ => g)
    rw [cochainOf_d_zeroCochain, cochainOf_zero] at h
    exact sub_eq_zero.1 h
  obtain ⟨m, hm⟩ := hB v hinv
  refine ⟨m, ?_⟩
  unfold normClass
  congr 1
  apply iCycles_hom_injective
  exact (((cochainsComplex B).i_cyclesMk _ _ _ _).trans (congrArg (zeroCochain B) hm)).trans hx.symm

end NormClass

section Tate

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)
  (A : Rep.{u} k G) [IsDiscreteRep A] (Aᵥ : ∀ v, Rep.{u} k (H v))
  [∀ v, IsDiscreteRep (Aᵥ v)] (a : ∀ v, Rep.res (φ v).toMonoidHom A ⟶ Aᵥ v)
  (Aᵣ : ∀ w, Rep.{u} k (F w)) [∀ w, IsDiscreteRep (Aᵣ w)]
  (ar : ∀ w, Rep.res (ψ w).toMonoidHom A ⟶ Aᵣ w)

theorem normCochains_prodInr :
    normCochains Aᵣ ≫ prodInr _ _ = prodInr _ _ ≫ tateCompactRes φ ψ A Aᵥ a Aᵣ ar := by
  ext n : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun m => ?_)
  change ((prodInr _ _).f n).hom (((normCochains Aᵣ).f n).hom m) =
    ((tateCompactRes φ ψ A Aᵥ a Aᵣ ar).f n).hom (((prodInr _ _).f n).hom m)
  rw [prodInr_f_hom_apply, prodInr_f_hom_apply]
  refine Prod.ext ?_ ?_
  · change (0 : (piComplex fun v => cochainsComplex (Aᵥ v)).X n) = ((localRes φ A Aᵥ a).f n).hom 0
    exact (map_zero _).symm
  · change ((normCochains Aᵣ).f n).hom m =
      ((localRes ψ A Aᵣ ar).f n).hom 0 + ((normCochains Aᵣ).f n).hom m
    rw [map_zero, zero_add]

noncomputable def tateResSeqHom :
    prodSeq (cochainsComplex A) (degZeroComplex (ModuleCat.of k (∀ w, Aᵣ w))) ⟶
      prodSeq (piComplex fun v => cochainsComplex (Aᵥ v)) (piComplex fun w => cochainsComplex (Aᵣ w)) where
  τ₁ := normCochains Aᵣ
  τ₂ := tateCompactRes φ ψ A Aᵥ a Aᵣ ar
  τ₃ := localRes φ A Aᵥ a
  comm₁₂ := normCochains_prodInr φ ψ A Aᵥ a Aᵣ ar
  comm₂₃ := tateCompactRes_prodFst φ ψ A Aᵥ a Aᵣ ar

theorem tateForgetShortComplex_shortExact :
    (mappingCoconeNat.mapShortComplex (tateResSeqHom φ ψ A Aᵥ a Aᵣ ar)).ShortExact :=
  mappingCoconeNat.shortExact_mapShortComplex _ (prodSeq_shortExact _ _) (prodSeq_shortExact _ _)

theorem isZero_homology_normCocone (hcoh : ∀ w n, IsZero (cohomology (Aᵣ w) (n + 1)))
    (hnorm : ∀ w, ∀ x ∈ (Aᵣ w).ρ.invariants, ∃ m, (Aᵣ w).ρ.norm m = x) (n : ℕ) :
    IsZero ((mappingCoconeNat (normCochains Aᵣ)).homology (n + 1)) := by
  have hK : IsZero ((degZeroComplex (ModuleCat.of k (∀ w, Aᵣ w))).homology (n + 1)) :=
    isZero_degZeroComplex_homology_succ _ n
  have hepi : Epi (HomologicalComplex.homologyMap (normCochains Aᵣ) n) := by
    cases n with
    | zero =>
      rw [ModuleCat.epi_iff_surjective]
      intro z
      choose m hm using fun w =>
        exists_normClass_eq (Aᵣ w) (hnorm w) ((localCohomologyIso Aᵣ 0).hom.hom z w)
      refine ⟨(degZeroHomologyIso (ModuleCat.of k (∀ w, Aᵣ w))).inv.hom
        (show ModuleCat.of k (∀ w, Aᵣ w) from m), ?_⟩
      have hinj : Function.Injective (localCohomologyIso Aᵣ 0).hom.hom :=
        (ModuleCat.mono_iff_injective _).1 inferInstance
      apply hinj
      rw [localCohomologyIso_homologyMap_normCochains, hom_apply_hom_apply_of_comp_eq
        (Iso.inv_hom_id (degZeroHomologyIso (ModuleCat.of k (∀ w, Aᵣ w))))]
      exact funext hm
    | succ n =>
      have hsub : ∀ w, Subsingleton (cohomology (Aᵣ w) (n + 1)) := fun w =>
        ModuleCat.isZero_iff_subsingleton.1 (hcoh w n)
      have hL : IsZero ((piComplex fun w => cochainsComplex (Aᵣ w)).homology (n + 1)) :=
        IsZero.of_iso (ModuleCat.isZero_of_subsingleton _) (localCohomologyIso Aᵣ (n + 1))
      exact ⟨fun _ _ _ => hL.eq_of_src _ _⟩
  have hex := mappingCoconeNat.homology_exact₂ (normCochains Aᵣ) n
  have hδ : mappingCoconeNat.homologyδ (normCochains Aᵣ) n = 0 :=
    (cancel_epi (HomologicalComplex.homologyMap (normCochains Aᵣ) n)).1
      ((mappingCoconeNat.homologyMap_homologyδ _ n).trans comp_zero.symm)
  exact hex.isZero_X₂ hδ (hK.eq_of_tgt _ _)

theorem isIso_tateForget (hcoh : ∀ w n, IsZero (cohomology (Aᵣ w) (n + 1)))
    (hnorm : ∀ w, ∀ x ∈ (Aᵣ w).ρ.invariants, ∃ m, (Aᵣ w).ρ.norm m = x) (n : ℕ) :
    IsIso (tateForget φ ψ A Aᵥ a Aᵣ ar (n + 1)) := by
  have hS := tateForgetShortComplex_shortExact φ ψ A Aᵥ a Aᵣ ar
  have h0 := isZero_homology_normCocone Aᵣ hcoh hnorm n
  have h1 := isZero_homology_normCocone Aᵣ hcoh hnorm (n + 1)
  have hmono := (hS.homology_exact₂ (n + 1)).mono_g (h0.eq_of_src _ _)
  have hepi := (hS.homology_exact₃ (n + 1) (n + 1 + 1) rfl).epi_f (h1.eq_of_tgt _ _)
  exact @isIso_of_mono_of_epi _ _ _ _ _ (tateForget φ ψ A Aᵥ a Aᵣ ar (n + 1)) hmono hepi

noncomputable def tateForgetIso (hcoh : ∀ w n, IsZero (cohomology (Aᵣ w) (n + 1)))
    (hnorm : ∀ w, ∀ x ∈ (Aᵣ w).ρ.invariants, ∃ m, (Aᵣ w).ρ.norm m = x) (n : ℕ) :
    tateCompactCohomology φ ψ A Aᵥ a Aᵣ ar (n + 1) ≅ compactCohomology φ A Aᵥ a (n + 1) :=
  @asIso _ _ _ _ (tateForget φ ψ A Aᵥ a Aᵣ ar (n + 1))
    (isIso_tateForget φ ψ A Aᵥ a Aᵣ ar hcoh hnorm n)

end Tate

end GroundTheory.ProfCoh
