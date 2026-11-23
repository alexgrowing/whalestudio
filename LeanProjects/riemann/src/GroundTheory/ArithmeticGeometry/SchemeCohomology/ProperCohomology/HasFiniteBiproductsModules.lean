import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.CokernelCoherent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits

universe u

noncomputable section

instance hasFiniteBiproducts_modules (X : Scheme.{u}) : HasFiniteBiproducts X.Modules :=
  .of_hasFiniteProducts

variable {X : Scheme.{u}}

lemma resF_app {M N : X.Modules} (φ : M ⟶ N) {U V : X.Opens} (h : V ≤ U) (m : Γ(M, U)) :
    resF N h (φ.app U m) = φ.app V (resF M h m) := by
  have := congrArg (fun g => g.hom m) (φ.mapPresheaf.naturality (homOfLE h).op)
  exact this.symm

section Biproduct

variable {ι : Type} [Fintype ι] [DecidableEq ι] (M : ι → X.Modules)

lemma biproduct_app_eq_sum (U : X.Opens) (m : Γ(⨁ M, U)) :
    m = ∑ j, (biproduct.ι M j).app U ((biproduct.π M j).app U m) := by
  have h := congrArg (fun g : (⨁ M) ⟶ (⨁ M) => g.app U m) (biproduct.total (f := M))
  simp only [Scheme.Modules.Hom.id_app] at h
  rw [← ConcreteCategory.id_apply (X := Γ(⨁ M, U)) m]
  change _ = ∑ j, ((biproduct.π M j ≫ biproduct.ι M j).app U) m
  rw [← h]
  have : ∀ (s : Finset ι), ((∑ j ∈ s, biproduct.π M j ≫ biproduct.ι M j).app U) m =
      ∑ j ∈ s, ((biproduct.π M j ≫ biproduct.ι M j).app U) m := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Scheme.Modules.Hom.add_app]
      rw [← ih]
      rfl
  exact this Finset.univ

lemma biproduct_π_app_ι_app (U : X.Opens) (i j : ι) (x : Γ(M i, U)) :
    (biproduct.π M j).app U ((biproduct.ι M i).app U x) =
      if h : i = j then (eqToHom (congrArg M h)).app U x else 0 := by
  rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, biproduct.ι_π]
  split_ifs with h
  · rfl
  · rfl

theorem isQuasicoherent_biproduct [∀ i, (M i).IsQuasicoherent] : (⨁ M).IsQuasicoherent := by
  refine isQuasicoherent_of_affineCover _ (fun V : X.affineOpens => (V : X.Opens)) (fun V => V.2)
    (iSup_affineOpens_eq_top X) ?_ ?_
  · intro V f m
    have key : ∀ j, ∃ (e : ℕ) (m' : Γ(M j, (V : X.Opens))),
        resF (M j) (X.basicOpen_le f) m' =
          resO (X.basicOpen_le f) f ^ e • (biproduct.π M j).app _ m :=
      fun j => qcoh_exists_res_eq (M j) V.2 f _
    choose e m' hm' using key
    refine ⟨∑ j, e j, ∑ j, (biproduct.ι M j).app _ (f ^ (∑ k, e k - e j) • m' j), ?_⟩
    rw [map_sum]
    conv_rhs => rw [biproduct_app_eq_sum M _ m, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [resF_app, resF_smul, hm' j, smul_smul, map_pow, ← pow_add,
      Nat.sub_add_cancel (Finset.single_le_sum (fun k _ => Nat.zero_le (e k))
        (Finset.mem_univ j)), Scheme.Modules.Hom.app_smul]
  · intro V f m hm
    have key : ∀ j, ∃ e : ℕ, f ^ e • (biproduct.π M j).app _ m = 0 := fun j => by
      refine qcoh_exists_pow_smul_eq_zero (M j) V.2 f _ ?_
      rw [resF_app, hm, map_zero]
    choose e he using key
    refine ⟨∑ j, e j, ?_⟩
    rw [biproduct_app_eq_sum M _ m, Finset.smul_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← Scheme.Modules.Hom.app_smul, ← Nat.sub_add_cancel (Finset.single_le_sum
      (fun k _ => Nat.zero_le (e k)) (Finset.mem_univ j)), pow_add, mul_smul, he j, smul_zero,
      map_zero]

end Biproduct

section Image

lemma surjective_app_of_epi {P Q : X.Modules} (e : P ⟶ Q) [Epi e] [P.IsQuasicoherent]
    [Q.IsQuasicoherent] {V : X.Opens} (hV : IsAffineOpen V) : Function.Surjective (e.app V) := by
  have hc : IsColimit (CokernelCofork.ofπ e (kernel.condition e)) :=
    Abelian.epiIsCokernelOfKernel (KernelFork.ofι _ (kernel.condition e)) (kernelIsKernel e)
  let i : cokernel (kernel.ι e) ≅ Q := (cokernelIsCokernel (kernel.ι e)).coconePointUniqueUpToIso hc
  have hi : cokernel.π (kernel.ι e) ≫ i.hom = e :=
    (cokernelIsCokernel _).comp_coconePointUniqueUpToIso_hom hc WalkingParallelPair.one
  have h1 := surjective_cokernel_π_app (kernel.ι e) hV
  rw [← hi, Scheme.Modules.Hom.comp_app]
  exact (bijective_app_of_iso i V).2.comp h1

lemma range_kernel_ι_cokernel_π_app {P G : X.Modules} (f : P ⟶ G) [P.IsQuasicoherent]
    [G.IsQuasicoherent] {V : X.Opens} (hV : IsAffineOpen V) :
    Set.range ((kernel.ι (cokernel.π f)).app V) = Set.range (f.app V) := by
  have hfac : Abelian.factorThruImage f ≫ kernel.ι (cokernel.π f) = f := Abelian.image.fac f
  have hs := surjective_app_of_epi (Abelian.factorThruImage f) hV
  ext m
  constructor
  · rintro ⟨k, rfl⟩
    obtain ⟨p, rfl⟩ := hs k
    refine ⟨p, ?_⟩
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, hfac]
  · rintro ⟨p, rfl⟩
    refine ⟨(Abelian.factorThruImage f).app V p, ?_⟩
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, hfac]

lemma mem_range_app_iff {P G : X.Modules} (f : P ⟶ G) [P.IsQuasicoherent] [G.IsQuasicoherent]
    {V : X.Opens} (hV : IsAffineOpen V) (m : Γ(G, V)) :
    m ∈ Set.range (f.app V) ↔ (cokernel.π f).app V m = 0 := by
  constructor
  · rintro ⟨p, rfl⟩
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, cokernel.condition,
      Scheme.Modules.Hom.zero_app]
    rfl
  · intro hm
    obtain ⟨k, hk⟩ := kernel_ι_app_exact (cokernel.π f) V m hm
    rw [← range_kernel_ι_cokernel_π_app f hV]
    exact ⟨k, hk⟩

end Image

end

end GroundTheory.Arith.SchemeCoh
