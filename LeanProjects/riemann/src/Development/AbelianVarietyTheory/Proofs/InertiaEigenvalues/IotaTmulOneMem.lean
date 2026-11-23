import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTmulOneOfFrobFixedOfMemFilZero
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory.HfZero

section
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

include PD in
theorem nontrivial_cris : Nontrivial B := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  apply PD.not_mem_filtration_two
  rw [Subsingleton.elim PD.t 0, map_zero]
  exact Submodule.zero_mem _

include PD in
theorem tmul_one_inj {v w : V} (h : v ⊗ₜ[Qp] (1 : B) = w ⊗ₜ[Qp] (1 : B)) : v = w := by
  have := nontrivial_cris PD
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap Qp B)
    (LinearMap.ker_eq_bot.2 (algebraMap Qp B).injective)
  have h1 : r 1 = 1 := by simpa using LinearMap.congr_fun hr 1
  have := congrArg (fun z => TensorProduct.rid Qp V (r.lTensor V z)) h
  simpa [h1] using this

theorem frob_act (g : G) (x : V ⊗[Qp] B) :
    φVB PD (LL := LL) (V := V) (actVB PD ρ g x) = actVB PD ρ g (φVB PD (LL := LL) (V := V) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [φVB, actVB, PD.φ_comm]
  | add y z hy hz => simp only [map_add, hy, hz]

theorem iota_act (g : G) (x : V ⊗[Qp] B) :
    ιV PD (LL := LL) (V := V) (actVB PD ρ g x) = actVdR PD ρ g (ιV PD (LL := LL) (V := V) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [ιV, actVB, actVdR, PD.ι_comm]
  | add y z hy hz => simp only [map_add, hy, hz]

theorem frob_tmul_one (v : V) :
    φVB PD (LL := LL) (V := V) (v ⊗ₜ[Qp] (1 : B)) = v ⊗ₜ[Qp] (1 : B) := by
  simp [φVB]

theorem act_tmul_one (g : G) (v : V) :
    actVB PD ρ g (v ⊗ₜ[Qp] (1 : B)) = ρ g v ⊗ₜ[Qp] (1 : B) := by
  simp [actVB]

theorem tmul_mem_filV (v : V) (a : ℤ) (b : BdR) (hb : b ∈ PD.Fil a) :
    v ⊗ₜ[Qp] b ∈ FilV PD (LL := LL) (V := V) a :=
  ⟨v ⊗ₜ ⟨b, hb⟩, by simp⟩

theorem iota_tmul_one_mem (v : V) :
    ιV PD (LL := LL) (V := V) (v ⊗ₜ[Qp] (1 : B)) ∈ FilV PD (LL := LL) (V := V) 0 := by
  have : ιV PD (LL := LL) (V := V) (v ⊗ₜ[Qp] (1 : B)) = v ⊗ₜ[Qp] (1 : BdR) := by simp [ιV]
  rw [this]
  exact tmul_mem_filV PD v 0 1 PD.one_mem

theorem filV_succ_le (a : ℤ) :
    FilV PD (LL := LL) (V := V) (a + 1) ≤ FilV PD (LL := LL) (V := V) a := by
  rintro x ⟨y, rfl⟩
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => exact ⟨v ⊗ₜ ⟨b.1, PD.Fil_anti a b.2⟩, by simp⟩
  | add y z hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz

theorem filV_antitone : Antitone (FilV PD (LL := LL) (V := V)) :=
  antitone_int_of_succ_le (filV_succ_le PD)

theorem exists_mem_filV (z : V ⊗[Qp] BdR) : ∃ a, z ∈ FilV PD (LL := LL) (V := V) a := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | tmul v b =>
    obtain ⟨a, ha⟩ := PD.Fil_exh b
    exact ⟨a, tmul_mem_filV PD v a b ha⟩
  | add y z hy hz =>
    obtain ⟨a, ha⟩ := hy
    obtain ⟨b, hb⟩ := hz
    exact ⟨min a b, Submodule.add_mem _ (filV_antitone PD (min_le_left a b) ha)
      (filV_antitone PD (min_le_right a b) hb)⟩

theorem mem_dcris_iff (x : V ⊗[Qp] B) : x ∈ Dcris PD ρ ↔ ∀ g, actVB PD ρ g x = x := by
  simp [Dcris, Submodule.mem_iInf, sub_eq_zero]

theorem mem_ddR_iff (x : V ⊗[Qp] BdR) : x ∈ DdR PD ρ ↔ ∀ g, actVdR PD ρ g x = x := by
  simp [DdR, Submodule.mem_iInf, sub_eq_zero]

theorem iota_mem_ddR (x : V ⊗[Qp] B) (hx : x ∈ Dcris PD ρ) :
    ιV PD (LL := LL) (V := V) x ∈ DdR PD ρ := by
  rw [mem_ddR_iff]
  intro g
  rw [← iota_act, (mem_dcris_iff PD ρ x).1 hx g]

end

theorem z1f_le_b1 : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) [TopologicalSpace Qp] {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] {O : Type} [CommRing O] [Algebra O LL], TateFilteredInvariants PD → fontCore PD → GoodO (Qp := Qp) LL O → ∀ A : GRep G Qp LL O, IsDR PD A.ρ → DdR PD A.ρ ≤ FilV PD (LL := LL) (V := A.V) 0 → H0V A.ρ = ⊥ → finiteCocycles PD A.ρ ≤ B1 A.ρ := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD _ LL _ _ _ O _ _ h5 hfont hO A
    hdR hFil hH0 c hc
  obtain ⟨-, x, hx⟩ := hc
  have : Module.Finite LL ↥(Dcris PD A.ρ) := (hfont LL O hO A).1.1
  let ψ : A.V ⊗[Qp] B →ₗ[LL] A.V ⊗[Qp] B := LinearMap.id - φVB PD (LL := LL) (V := A.V)
  have hψ : ∀ z, ψ z = z - φVB PD (LL := LL) (V := A.V) z := fun z => rfl
  have hstab : ∀ z ∈ Dcris PD A.ρ, ψ z ∈ Dcris PD A.ρ := by
    intro z hz
    rw [mem_dcris_iff] at hz ⊢
    intro g
    rw [hψ, map_sub, ← frob_act, hz g]
  have hinj : Function.Injective (ψ.restrict hstab) := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨z, hz⟩ h0
    have h1 : ψ z = 0 := congrArg Subtype.val h0
    rw [hψ, sub_eq_zero] at h1
    obtain ⟨v, rfl⟩ := exists_tmul_one_of_frob_fixed_of_mem_fil_zero PD (LL := LL) z h1.symm
      (hFil (iota_mem_ddR PD A.ρ z hz))
    have hv : v ∈ H0V A.ρ := by
      simp only [H0V, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero]
      intro g
      apply tmul_one_inj PD
      rw [← act_tmul_one PD A.ρ, (mem_dcris_iff PD A.ρ _).1 hz g]
    rw [hH0, Submodule.mem_bot] at hv
    subst hv
    exact Subtype.ext (TensorProduct.zero_tmul _ _)
  have hsurj := LinearMap.injective_iff_surjective.1 hinj
  have hy : ψ x ∈ Dcris PD A.ρ := by
    rw [mem_dcris_iff]
    intro g
    have h1 := frob_tmul_one PD (LL := LL) (c g)
    rw [hx g, map_sub, frob_act] at h1
    rw [hψ, map_sub, sub_eq_sub_iff_sub_eq_sub, h1]
  obtain ⟨⟨x', hx'⟩, hxx⟩ := hsurj ⟨ψ x, hy⟩
  have h2 : ψ x' = ψ x := congrArg Subtype.val hxx
  have hfix : φVB PD (LL := LL) (V := A.V) (x - x') = x - x' := by
    rw [hψ, hψ, sub_eq_sub_iff_sub_eq_sub] at h2
    rw [map_sub, ← neg_sub x' x, h2, neg_sub]
  obtain ⟨a, ha⟩ := exists_mem_filV PD (LL := LL) (ιV PD (LL := LL) (V := A.V) x)
  obtain ⟨w, ⟨hw, -⟩, hw'⟩ := h5 LL O hO A hdR a 0 _ ha (fun g => by
    rw [← iota_act, ← map_sub, ← hx g]
    exact iota_tmul_one_mem PD (c g))
  have hF : ιV PD (LL := LL) (V := A.V) (x - x') ∈ FilV PD (LL := LL) (V := A.V) 0 := by
    have h3 := Submodule.sub_mem _ (Submodule.add_mem _ hw' (hFil hw))
      (hFil (iota_mem_ddR PD A.ρ x' hx'))
    rwa [sub_add_cancel, ← map_sub] at h3
  obtain ⟨v, hv⟩ := exists_tmul_one_of_frob_fixed_of_mem_fil_zero PD (LL := LL) _ hfix hF
  refine ⟨v, funext fun g => ?_⟩
  change A.ρ g v - v = c g
  apply tmul_one_inj PD
  rw [hx g, TensorProduct.sub_tmul, ← act_tmul_one PD A.ρ, ← hv, map_sub,
    (mem_dcris_iff PD A.ρ _).1 hx' g]
  abel

end GlobalTheory.HfZero
