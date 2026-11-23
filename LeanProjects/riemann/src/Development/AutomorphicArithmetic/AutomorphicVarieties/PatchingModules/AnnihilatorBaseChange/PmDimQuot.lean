import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.YPrime
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplFlat
import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplModfree
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCmPatch
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplMap

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem pmDim_quot {A B σ M : Type} [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup M]
    [Module A M] (y : σ → A) :
    Nonempty (((B ⊗[A] M) ⧸ (Ideal.span (Set.range fun i => algebraMap A B (y i)) • ⊤ :
      Submodule B (B ⊗[A] M))) ≃ₗ[B] B ⊗[A] (M ⧸ (Ideal.span (Set.range y) • ⊤ : Submodule A M))) := by
  classical
  set I : Ideal A := Ideal.span (Set.range y) with hIdef
  have hI : Ideal.span (Set.range fun i => algebraMap A B (y i)) = I.map (algebraMap A B) := by
    rw [hIdef, Ideal.map_span, ← Set.range_comp]
    rfl
  rw [hI]
  refine ⟨(TensorProduct.AlgebraTensorModule.tensorQuotientEquiv (R := A) B A B
    (I • ⊤ : Submodule A M) ≪≫ₗ Submodule.quotEquivOfEq _ _ ?_).symm⟩
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b m =>
      obtain ⟨m, hm⟩ := m
      simp only [TensorProduct.AlgebraTensorModule.lTensor_tmul, LinearMap.coe_restrictScalars,
        Submodule.coe_subtype]
      refine Submodule.smul_induction_on hm ?_ ?_
      · intro a ha m' _
        rw [← TensorProduct.smul_tmul, algebra_compatible_smul B a, ← TensorProduct.smul_tmul']
        exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ ha) Submodule.mem_top
      · intro u v hu hv
        rw [TensorProduct.tmul_add]
        exact Submodule.add_mem _ hu hv
    | add x z hx hz =>
      rw [map_add]
      exact Submodule.add_mem _ hx hz
  · rw [Submodule.smul_le]
    intro r hr x hx
    clear hx
    induction hr using Submodule.span_induction generalizing x with
    | mem r hr =>
      obtain ⟨a, ha, rfl⟩ := hr
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul b m =>
        refine ⟨b ⊗ₜ[A] (⟨a • m, Submodule.smul_mem_smul ha Submodule.mem_top⟩ : (I • ⊤ : Submodule A M)), ?_⟩
        simp only [TensorProduct.AlgebraTensorModule.lTensor_tmul, LinearMap.coe_restrictScalars,
          Submodule.coe_subtype]
        rw [← TensorProduct.smul_tmul, algebra_compatible_smul B a, TensorProduct.smul_tmul']
      | add u v hu hv =>
        rw [smul_add]
        exact Submodule.add_mem _ hu hv
    | zero => simp
    | add r s _ _ hr hs =>
      rw [add_smul]
      exact Submodule.add_mem _ (hr x) (hs x)
    | smul c r _ hr =>
      rw [smul_eq_mul, mul_smul]
      exact Submodule.smul_mem _ c (hr x)

private theorem pmDim_step {L B σ M N : Type} [CommRing L] [IsRegularLocalRing L] [CommRing B]
    [IsLocalRing B] [IsNoetherianRing B] [Algebra L B] [IsLocalHom (algebraMap L B)] [Fintype σ]
    [AddCommGroup M] [Module B M] [Module.Finite B M] [AddCommGroup N] [Module B N] [Module L N]
    [IsScalarTower L B N] [Module.Free L N] [Module.Finite L N] (d : ℕ) (y : σ → B)
    (hd : ringKrullDim L = d) (hy : ∀ i, y i ∈ maximalIdeal B) (hq : GlobalTheory.IsQuasiRegularSeq M y)
    (e : (M ⧸ (Ideal.span (Set.range y) • ⊤ : Submodule B M)) ≃ₗ[B] N) :
    ∀ Z ∈ (Module.annihilator B M).minimalPrimes,
      ringKrullDim (B ⧸ Z) = ((d + Fintype.card σ : ℕ) : WithBot ℕ∞) := by
  classical
  intro Z hZ
  rcases subsingleton_or_nontrivial M with hM | hM
  · have htop : Module.annihilator B M = ⊤ := Module.annihilator_eq_top_iff.mpr hM
    rw [htop] at hZ
    exact absurd (top_le_iff.mp hZ.1.2) hZ.1.1.ne_top
  · letI : Module L M := Module.compHom M (algebraMap L B)
    haveI : IsScalarTower L B M := ⟨fun a b m => by
      show (a • b) • m = algebraMap L B a • (b • m)
      rw [Algebra.smul_def, mul_smul]⟩
    let eσ : Fin (Fintype.card σ) ≃ σ := (Fintype.equivFin σ).symm
    have hq' := hq.comp_equiv eσ
    have hspan : Ideal.span (Set.range (y ∘ eσ)) = Ideal.span (Set.range y) := by
      rw [Set.range_comp, EquivLike.range_eq_univ, Set.image_univ]
    let e' : (M ⧸ (Ideal.span (Set.range (y ∘ eσ)) • ⊤ : Submodule B M)) ≃ₗ[L] N :=
      ((Submodule.quotEquivOfEq _ _ (by rw [hspan])) ≪≫ₗ e).restrictScalars L
    have hfree : Module.Free L (M ⧸ (Ideal.span (Set.range (y ∘ eσ)) • ⊤ : Submodule B M)) :=
      Module.Free.of_equiv e'.symm
    have hfin : Module.Finite L (M ⧸ (Ideal.span (Set.range (y ∘ eσ)) • ⊤ : Submodule B M)) :=
      Module.Finite.equiv e'.symm
    have h := (UpperTheory.V.AlgebraTools.patched_depth_dim L B M (Fintype.card σ) d (y ∘ eσ) hd
      (fun i => hy _) hq' hfree hfin).2 Z hZ
    rw [h, Nat.add_comm]

theorem UpperTheory.V.Pa.Core.pmDim :
    ∀ (Λ R σ : Type) [CommRing Λ] [IsNoetherianRing Λ] [CommRing R] [IsNoetherianRing R] [Fintype σ] (c : Λ →+* R) (y : σ → R) (f : R) (ii : Ideal R) (X : Type) [AddCommGroup X] [Module R X] [Module Λ X] [Module.Free Λ X] [Module.Finite Λ X] (P : PMod y f ii X) (q : Ideal R) (d : ℕ) (La B : Type) [CommRing La] [IsLocalRing La] [Algebra Λ La] [CommRing B] [IsLocalRing B] [Algebra P.BB B], (∀ (a : Λ) (x : X), a • x = c a • x) → q.IsPrime → f ∉ q → (∀ a, y a ∈ q) → IsCplAt Λ (q.comap c) La → IsRegularLocalRing La → ringKrullDim La = d → IsCplAt P.BB (q.map (algebraMap R P.BB)) B → ∀ Z ∈ (Module.annihilator B (B ⊗[P.BB] P.MM)).minimalPrimes, ringKrullDim (B ⧸ Z) = ((d + Fintype.card σ : ℕ) : WithBot ℕ∞) := by
  intro Λ R σ _ _ _ _ _ c y f ii X _ _ _ _ _ P q d La B _ _ _ _ _ _ hc hq hf hy hLa hreg hdim hB
  classical
  have hYP := UpperTheory.V.Pa.Core.yPrime R σ y f P.BB P.cpl q hq hf hy
  haveI : IsNoetherianRing P.BB := P.cpl.noeth
  haveI : IsNoetherianRing B := hB.noeth
  haveI : Module.Finite P.BB P.MM := P.fin
  haveI : IsAdicComplete (maximalIdeal B) B := hB.complete
  letI : Algebra R B := ((algebraMap P.BB B).comp (algebraMap R P.BB)).toAlgebra
  haveI : IsScalarTower R P.BB B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hRB : IsCplAt R q B := hYP.2.2.2 B hB
  haveI : Module.Flat P.BB B := UpperTheory.V.AlgebraTools.IsCplAt.flat P.BB _ B hB
  let φ : Λ →+* B := (algebraMap R B).comp c
  have hφ : Ideal.comap φ (maximalIdeal B) = q.comap c := by
    show Ideal.comap ((algebraMap P.BB B).comp ((algebraMap R P.BB).comp c)) (maximalIdeal B) = q.comap c
    rw [← Ideal.comap_comap, ← Ideal.comap_comap, hB.comap_eq, hYP.2.1]
  obtain ⟨ψ, hψ, -⟩ := UpperTheory.V.AlgebraTools.IsCplAt.existsUnique_lift Λ (q.comap c) La hLa B φ hφ
  letI : Algebra La B := ψ.toAlgebra
  haveI : IsLocalHom (algebraMap La B) := by
    show IsLocalHom ψ
    refine ((IsLocalRing.local_hom_TFAE ψ).out 0 3).mpr ?_
    have hm : maximalIdeal La = (q.comap c).map (algebraMap Λ La) := by
      simpa using (UpperTheory.V.AlgebraTools.IsCplAt.map_pow_eq Λ (q.comap c) La hLa 1).symm
    rw [hm, Ideal.map_le_iff_le_comap, Ideal.comap_comap, hψ, hφ]
  letI : Algebra Λ R := c.toAlgebra
  letI : Algebra Λ B := φ.toAlgebra
  haveI : IsScalarTower Λ R B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower Λ La B :=
    IsScalarTower.of_algebraMap_eq (fun x => (RingHom.congr_fun hψ x).symm)
  haveI : IsScalarTower Λ R X := ⟨fun a r x => by
    show (c a * r) • x = a • (r • x)
    rw [mul_smul, hc]⟩
  obtain ⟨hfin, hfree⟩ :=
    UpperTheory.V.AlgebraTools.IsCplAt.finite_free_baseChange Λ R (q.comap c) q La B X hLa hRB rfl
  haveI := hfin
  haveI := hfree
  let y' : σ → B := fun i => algebraMap P.BB B (algebraMap R P.BB (y i))
  obtain ⟨e1⟩ := pmDim_quot (A := P.BB) (B := B) (M := P.MM) (fun a => algebraMap R P.BB (y a))
  let e : ((B ⊗[P.BB] P.MM) ⧸ (Ideal.span (Set.range y') • ⊤ : Submodule B (B ⊗[P.BB] P.MM))) ≃ₗ[B]
      B ⊗[R] X :=
    e1 ≪≫ₗ TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B B) P.fib ≪≫ₗ
      TensorProduct.AlgebraTensorModule.cancelBaseChange R P.BB B B X
  have hy' : ∀ i, y' i ∈ maximalIdeal B := by
    intro i
    have h : algebraMap R P.BB (y i) ∈ Ideal.comap (algebraMap P.BB B) (maximalIdeal B) := by
      rw [hB.comap_eq]
      exact Ideal.mem_map_of_mem _ (hy i)
    exact h
  have hqr : GlobalTheory.IsQuasiRegularSeq (B ⊗[P.BB] P.MM) y' := P.qr.baseChange B
  exact pmDim_step (L := La) (B := B) (M := B ⊗[P.BB] P.MM) (N := B ⊗[R] X) d y' hdim hy' hqr e
