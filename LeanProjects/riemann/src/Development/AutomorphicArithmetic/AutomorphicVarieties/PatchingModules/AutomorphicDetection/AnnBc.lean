import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.PmodEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.YPrime
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.PmFib
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.PmDimQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.PmMove
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.OutOfNil
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplEx

open IsLocalRing Filter UpperTheory.V.AlgebraTools UpperTheory.V.Pa.Core
open scoped TensorProduct

namespace UpperTheory.V.Pa

private theorem ann_bc {BB B MM : Type} [CommRing BB] [CommRing B] [Algebra BB B] [AddCommGroup MM] [Module BB MM]
    {a : BB} (ha : a ∈ Module.annihilator BB MM) : algebraMap BB B a ∈ Module.annihilator B (B ⊗[BB] MM) := by
  rw [Module.mem_annihilator] at ha ⊢
  intro t
  rw [algebraMap_smul]
  induction t using TensorProduct.induction_on with
  | zero => exact smul_zero _
  | tmul b m => rw [← TensorProduct.tmul_smul, ha, TensorProduct.tmul_zero]
  | add x y hx hy => rw [smul_add, hx, hy, add_zero]

private theorem s5_lemma {Λ R σ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [CommRing R]
    [IsNoetherianRing R] [Fintype σ] (s : MvPowerSeries σ Λ →+* R) (f : R) (ii : Ideal R) (X : Type)
    [AddCommGroup X] [Module R X] [Module Λ X] [Module.Free Λ X] [Module.Finite Λ X] [Module.Finite R X]
    (hC : ∀ (a : Λ) (x : X), a • x = s (MvPowerSeries.C a) • x)
    (P : PMod (fun a => s (MvPowerSeries.X a)) f ii X) [IsNoetherianRing P.BB]
    (ι : Type) (q : ι → Ideal R) (d : ℕ)
    (hq : ∀ i, (q i).IsPrime ∧ ii ≤ q i ∧ f ∉ q i ∧ ∀ (a : σ), s (MvPowerSeries.X a) ∈ q i)
    (hLa : ∀ i, ∃ (La : Type) (_ : CommRing La) (_ : IsLocalRing La) (_ : Algebra Λ La),
      IsCplAt Λ (Ideal.comap (s.comp MvPowerSeries.C) (q i)) La ∧ IsRegularLocalRing La ∧ ringKrullDim La = ↑d)
    (B : ι → Type) [∀ i, CommRing (B i)] [∀ i, IsLocalRing (B i)] [∀ i, Algebra P.BB (B i)]
    (hcpl : ∀ i, IsCplAt P.BB (Ideal.map (algebraMap R P.BB) (q i)) (B i)) :
    Nonempty (PatchedSupportCompletions s ii (Module.annihilator R X) q (d + Fintype.card σ)) := by
  haveI := P.fin
  have hyp := fun i => yPrime R σ (fun a => s (MvPowerSeries.X a)) f P.BB P.cpl (q i) (hq i).1 (hq i).2.2.1
    (hq i).2.2.2
  letI iAlgR : ∀ i, Algebra R (B i) := fun i => ((algebraMap P.BB (B i)).comp (algebraMap R P.BB)).toAlgebra
  haveI iTow : ∀ i, IsScalarTower R P.BB (B i) := fun i => IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  refine outOfNil Λ R σ s ii (Module.annihilator R X) ι q (d + Fintype.card σ) B
    (fun i => Module.annihilator (B i) (B i ⊗[P.BB] P.MM))
    (fun i => (hq i).2.1) (fun i => (hyp i).2.2.2 (B i) (hcpl i)) ?_ ?_ ?_ ?_
  · intro i x hx
    obtain ⟨k, hk⟩ := Ideal.mem_comap.mp (P.nil hx)
    refine Ideal.mem_comap.mpr ⟨k, ?_⟩
    have := ann_bc (B := B i) hk
    rw [← map_pow] at this
    rw [← map_pow]
    exact this
  · intro i Z hZ
    obtain ⟨La, _, _, _, hLcpl, hreg, hdim⟩ := hLa i
    rw [pmDim Λ R σ (s.comp MvPowerSeries.C) (fun a => s (MvPowerSeries.X a)) f ii X P (q i) d La (B i) hC
      (hq i).1 (hq i).2.2.1 (hq i).2.2.2 hLcpl hreg hdim (hcpl i) Z hZ]
  · intro i Q hQ _ hy
    have := pmFib R σ (fun a => s (MvPowerSeries.X a)) f ii X P (B i) Q hQ (fun a => hy a)
    rw [Ideal.comap_comap] at this
    exact this
  · intro i i' Z Q hZ hQ hSZ hZQ hy hQq
    have hP : Ideal.comap (algebraMap P.BB (B i)) Q ≤ Ideal.map (algebraMap R P.BB) (q i') :=
      (hyp i').2.2.1 _ (Ideal.comap_isPrime _ Q) (fun a => hy a) (by rw [Ideal.comap_comap]; exact hQq)
    obtain ⟨Z', hZ', hS', hc⟩ := pmMove P.BB P.MM (B i) (B i') _ Z (hcpl i') hZ hSZ
      (le_trans (Ideal.comap_mono hZQ) hP)
    refine ⟨Z', hZ', hS', ?_⟩
    have := congrArg (Ideal.comap (algebraMap R P.BB)) hc
    rw [Ideal.comap_comap, Ideal.comap_comap] at this
    exact this

theorem s5 : S5 := by
  intro Λ R σ _ _ _ _ _ _ _ _ _ s U f ii M _ _ X _ _ _ _ _ hU hC hX hM1 hM2 hG ι q d hq hLa
  obtain ⟨P⟩ := pmodEx Λ R σ s U f ii M X hU hC hX hM1 hM2 hG
  haveI : IsNoetherianRing P.BB := P.cpl.noeth
  haveI hfinR : Module.Finite R X := by
    letI : Algebra Λ R := (s.comp MvPowerSeries.C).toAlgebra
    haveI : IsScalarTower Λ R X := ⟨fun a r x => by
      rw [Algebra.smul_def, mul_smul, hC]
      rfl⟩
    exact Module.Finite.of_restrictScalars_finite Λ R X
  have hp := fun i => (yPrime R σ (fun a => s (MvPowerSeries.X a)) f P.BB P.cpl (q i) (hq i).1 (hq i).2.2.1
    (hq i).2.2.2).1
  exact s5_lemma s f ii X hC P ι q d hq hLa
    (fun i => @CplAt P.BB _ (Ideal.map (algebraMap R P.BB) (q i)) (hp i))
    (fun i => by
      haveI := hp i
      exact isCplAt_cplAt P.BB _)

end UpperTheory.V.Pa
