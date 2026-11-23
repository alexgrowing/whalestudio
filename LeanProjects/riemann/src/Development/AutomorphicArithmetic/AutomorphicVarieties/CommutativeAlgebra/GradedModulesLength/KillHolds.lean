import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleIrr

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem UpperTheory.V.Alg.M.kill_comp {B ι M : Type} [CommRing B] [AddCommGroup M] [Module B M]
    {G H : ι → Submodule B M} (hle : ∀ i, G i ≤ H i) (hind : iSupIndep H) (i : ι) {x : M}
    (hx : x ∈ H i) (hx' : x ∈ ⨆ j, G j) : x ∈ G i := by
  classical
  have h2 : (⨆ j, G j) ≤ G i ⊔ ⨆ (j) (_ : j ≠ i), G j := iSup_le fun j => by
    by_cases h : j = i
    · subst h; exact le_sup_left
    · exact le_sup_of_le_right (le_iSup₂_of_le j h le_rfl)
  obtain ⟨g, hg, y, hy, rfl⟩ := Submodule.mem_sup.1 (h2 hx')
  have h2 : y ∈ ⨆ (j) (_ : j ≠ i), H j := (iSup₂_mono fun j _ => hle j) hy
  have h3 : y ∈ H i := by
    have := (H i).sub_mem hx (hle i hg)
    simpa using this
  have h4 : y = 0 := by
    have := (hind i).le_bot ⟨h3, h2⟩
    simpa using this
  rw [h4, add_zero]
  exact hg

theorem UpperTheory.V.Alg.M.kill_holds :
    ∀ (k : ℕ) (X : HidaSetting k) (F : X.Mod), F.IsGr X.𝒜 → ∀ (J J' : Ideal X.B) (n : ℕ),
      (J.map (algebraMap X.B X.R) * Irr X.𝒜) ^ n ≤ F.Ann ⊔ J'.map (algebraMap X.B X.R) →
      ∀ᶠ d in atTop, J ^ n • F.gr d ≤ J' • F.gr d := by
  intro k X F hF J J' n hn
  have key1 : ∀ a ∈ J'.map (algebraMap X.B X.R), ∀ z : F.M,
      a • z ∈ J' • (⊤ : Submodule X.B F.M) := by
    intro a ha
    refine Submodule.span_induction
      (p := fun a _ => ∀ z : F.M, a • z ∈ J' • (⊤ : Submodule X.B F.M)) ?_ ?_ ?_ ?_ ha
    · rintro _ ⟨b, hb, rfl⟩ z
      rw [algebraMap_smul]
      exact Submodule.smul_mem_smul hb trivial
    · intro z
      rw [zero_smul]; exact zero_mem _
    · intro a b _ _ ha hb z
      rw [add_smul]; exact add_mem (ha z) (hb z)
    · intro r a _ ha z
      rw [smul_eq_mul, mul_comm, mul_smul]; exact ha _
  have key : ∀ a ∈ F.Ann ⊔ J'.map (algebraMap X.B X.R), ∀ z : F.M,
      a • z ∈ J' • (⊤ : Submodule X.B F.M) := by
    intro a ha z
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 ha
    rw [add_smul, Module.mem_annihilator.1 hu z, zero_add]
    exact key1 w hw z
  filter_upwards [hF.eventually_gr_le X.std X.iSup_eq_top n] with m hm
  refine Submodule.smul_le.2 fun b hb y hy => ?_
  refine kill_comp (G := fun d => J' • F.gr d) (H := F.gr) (fun _ => Submodule.smul_le_right)
    hF.internal.submodule_iSupIndep m (Submodule.smul_mem _ _ hy) ?_
  rw [← Submodule.smul_iSup, hF.internal.submodule_iSup_eq_top]
  refine Submodule.smul_induction_on (hm y hy) ?_ ?_
  · intro a ha z _
    have h1 : algebraMap X.B X.R b * a ∈ F.Ann ⊔ J'.map (algebraMap X.B X.R) := by
      apply hn
      rw [mul_pow, ← Ideal.map_pow]
      exact Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ hb) ha
    have h2 := key _ h1 z
    rwa [mul_smul, algebraMap_smul] at h2
  · intro x y hx hy
    rw [smul_add]; exact add_mem hx hy
