import Mathlib
import Formalism.MirabolicMackeyTheory.StatementL
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.OrthogonalityOfMackey
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
import Formalism.HermitianLattices.HermitianLatticesProofs.IndexBasic
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.IdxRules

open Module NumberField IsDedekindDomain

namespace Formalism.EigenvalueLevelCeiling

open Formalism.DivisionValues

section Abstract

variable {R : Type*} [CommRing R] {Y Q : Type*} [AddCommGroup Y] [Module R Y] [AddCommGroup Q]
  [Module R Q]

theorem gg_len_range {ι : Type*} [Fintype ι] [DecidableEq ι] (n : R) (s : ι → Y →ₗ[R] Q)
    (t : ι → Q →ₗ[R] Y) (hts : ∀ i j y, t i (s j y) = if i = j then n • y else 0) :
    (Fintype.card ι : ℕ∞) * Module.length R (LinearMap.range (n • (LinearMap.id : Y →ₗ[R] Y))) ≤
      Module.length R Q := by
  set NY := LinearMap.range (n • (LinearMap.id : Y →ₗ[R] Y)) with hNY
  have h1 : Module.length R (ι → NY) = (Fintype.card ι : ℕ∞) * Module.length R NY := by
    rw [Module.length_pi_of_fintype]
    simp
  rw [← h1]
  let T : Q →ₗ[R] (ι → Y) := LinearMap.pi t
  have h2 : Module.length R (LinearMap.range T) ≤ Module.length R Q :=
    Module.length_le_of_surjective T.rangeRestrict T.surjective_rangeRestrict
  refine le_trans ?_ h2
  let incl : (ι → NY) →ₗ[R] (ι → Y) := LinearMap.pi (fun i => NY.subtype ∘ₗ LinearMap.proj i)
  have hin : ∀ f, incl f ∈ LinearMap.range T := by
    intro f
    have hf : ∀ i, ∃ y : Y, n • y = (f i : Y) := by
      intro i
      obtain ⟨y, hy⟩ := (f i).2
      exact ⟨y, by simpa using hy⟩
    choose y hy using hf
    refine ⟨∑ j, s j (y j), ?_⟩
    ext i
    simp [T, incl, hts, hy]
  refine Module.length_le_of_injective (incl.codRestrict _ hin) ?_
  intro f g hfg
  have h3 : incl f = incl g := congrArg Subtype.val hfg
  ext i
  exact congrFun h3 i

theorem gg_len_split (f : Y →ₗ[R] Y) :
    Module.length R Y =
      Module.length R (LinearMap.range f) + Module.length R (Y ⧸ LinearMap.range f) :=
  Module.length_eq_add_of_exact (LinearMap.range f).subtype (LinearMap.range f).mkQ
    (Submodule.injective_subtype _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)

theorem gg_core {Z : Type*} [AddCommGroup Z] [Module R Z] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : R) (A A' C B B' : Submodule R Z) (s t : ι → Z →ₗ[R] Z)
    (hsA : ∀ i, ∀ a ∈ A, s i a ∈ B) (hsA' : ∀ i, ∀ a ∈ A', s i a ∈ B')
    (htB : ∀ i, ∀ b ∈ B, t i b ∈ A) (htB' : ∀ i, ∀ b ∈ B', t i b ∈ A')
    (hts : ∀ i j, ∀ a ∈ A, t i (s j a) = if i = j then n • a else 0)
    (hC : ∀ c ∈ C, c ∈ A → ∃ a ∈ A, c = n • a) :
    (Fintype.card ι : ℕ∞) * Module.length R (A ⧸ A'.comap A.subtype) ≤
      Module.length R (B ⧸ B'.comap B.subtype) +
        (Fintype.card ι : ℕ∞) * Module.length R (A ⧸ C.comap A.subtype) := by
  have hs' : ∀ i, A'.comap A.subtype ≤ (B'.comap B.subtype).comap ((s i).restrict (hsA i)) := by
    intro i x hx
    rw [Submodule.mem_comap, Submodule.mem_comap, Submodule.subtype_apply,
      LinearMap.coe_restrict_apply]
    exact hsA' i _ hx
  have ht' : ∀ i, B'.comap B.subtype ≤ (A'.comap A.subtype).comap ((t i).restrict (htB i)) := by
    intro i x hx
    rw [Submodule.mem_comap, Submodule.mem_comap, Submodule.subtype_apply,
      LinearMap.coe_restrict_apply]
    exact htB' i _ hx
  let sb : ι → (A ⧸ A'.comap A.subtype) →ₗ[R] (B ⧸ B'.comap B.subtype) := fun i =>
    Submodule.mapQ _ _ ((s i).restrict (hsA i)) (hs' i)
  let tb : ι → (B ⧸ B'.comap B.subtype) →ₗ[R] (A ⧸ A'.comap A.subtype) := fun i =>
    Submodule.mapQ _ _ ((t i).restrict (htB i)) (ht' i)
  have hb : ∀ i j y, tb i (sb j y) = if i = j then n • y else 0 := by
    intro i j y
    induction y using Submodule.Quotient.induction_on with
    | H x =>
      dsimp only [sb, tb]
      rw [Submodule.mapQ_apply, Submodule.mapQ_apply]
      have e : ((t i).restrict (htB i)) (((s j).restrict (hsA j)) x) =
          if i = j then n • x else 0 := by
        apply Subtype.ext
        rw [LinearMap.coe_restrict_apply, LinearMap.coe_restrict_apply, hts i j _ x.2]
        split_ifs <;> simp
      rw [e]
      split_ifs <;> simp
  have k1 := gg_len_range n sb tb hb
  have k2 := gg_len_split (n • (LinearMap.id : (A ⧸ A'.comap A.subtype) →ₗ[R] _))
  have k3 : Module.length R ((A ⧸ A'.comap A.subtype) ⧸
      LinearMap.range (n • (LinearMap.id : (A ⧸ A'.comap A.subtype) →ₗ[R] _))) ≤
      Module.length R (A ⧸ C.comap A.subtype) := by
    let F : (A ⧸ C.comap A.subtype) →ₗ[R] ((A ⧸ A'.comap A.subtype) ⧸
      LinearMap.range (n • (LinearMap.id : (A ⧸ A'.comap A.subtype) →ₗ[R] _))) :=
      Submodule.liftQ _ ((Submodule.mkQ _) ∘ₗ (Submodule.mkQ _)) (by
        intro x hx
        obtain ⟨a, ha, hxa⟩ := hC _ hx x.2
        rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mkQ_apply,
          Submodule.Quotient.mk_eq_zero]
        refine ⟨Submodule.Quotient.mk ⟨a, ha⟩, ?_⟩
        rw [LinearMap.smul_apply, LinearMap.id_apply, ← Submodule.Quotient.mk_smul]
        congr 1
        apply Subtype.ext
        exact hxa.symm)
    refine Module.length_le_of_surjective F ?_
    intro y
    obtain ⟨y1, rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨y2, rfl⟩ := Submodule.mkQ_surjective _ y1
    exact ⟨Submodule.Quotient.mk y2, rfl⟩
  rw [k2, mul_add]
  exact add_le_add k1 (mul_le_mul_right k3 _)

end Abstract

section Concrete

variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {Z : Type} [AddCommGroup Z] [Module K Z] [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z]

noncomputable def ggE {P : Type} [Group P] (ρ : Representation K P Z) (U : Subgroup P) [Fintype U]
    (ψ : P → 𝓞 K) : Z →ₗ[K] Z :=
  ∑ u : U, ((ψ ((u : P)⁻¹) : 𝓞 K) : K) • ρ (u : P)

theorem ggE_apply {P : Type} [Group P] (ρ : Representation K P Z) (U : Subgroup P) [Fintype U]
    (ψ : P → 𝓞 K) (x : Z) :
    ggE ρ U ψ x = ∑ u : U, ((ψ ((u : P)⁻¹) : 𝓞 K) : K) • ρ (u : P) x := by
  simp [ggE, LinearMap.sum_apply]

theorem gg_mem_eig {P : Type} [Group P] (ρ : Representation K P Z) (U : Subgroup P)
    (ψ : P → 𝓞 K) (z : Z) :
    z ∈ eig ρ U ψ ↔ ∀ u : U, ρ (u : P) z = ((ψ (u : P) : 𝓞 K) : K) • z := by
  unfold eig
  rw [Submodule.mem_iInf]
  refine forall_congr' (fun u => ?_)
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    sub_eq_zero]

theorem ggE_mem_eig {P : Type} [Group P] (ρ : Representation K P Z) (U : Subgroup P) [Fintype U]
    (ψ : P → 𝓞 K) (hMk : IsMackey U ψ) (x : Z) : ggE ρ U ψ x ∈ eig ρ U ψ := by
  obtain ⟨hone, hmul, -⟩ := hMk
  rw [gg_mem_eig]
  intro u0
  rw [ggE_apply, map_sum, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft u0) _ _ (fun u => ?_)
  simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, mul_inv_rev]
  rw [map_smul, hmul _ (U.inv_mem u.2) _ (U.inv_mem u0.2), smul_smul, map_mul,
    Module.End.mul_apply]
  congr 1
  have h1 : ψ (u0 : P)⁻¹ * ψ (u0 : P) = 1 := by
    rw [← hmul _ (U.inv_mem u0.2) _ u0.2, inv_mul_cancel, hone]
  rw [← map_mul, mul_comm, mul_assoc, h1, mul_one]

theorem ggE_eig {P : Type} [Group P] (ρ : Representation K P Z) (U : Subgroup P) [Fintype U]
    (ψ : P → 𝓞 K) (hMk : IsMackey U ψ) (z : Z) (hz : z ∈ eig ρ U ψ) :
    ggE ρ U ψ z = ((Fintype.card U : ℕ) : K) • z := by
  obtain ⟨hone, hmul, -⟩ := hMk
  rw [ggE_apply]
  have : ∀ u : U, ((ψ ((u : P)⁻¹) : 𝓞 K) : K) • ρ (u : P) z = z := by
    intro u
    rw [(gg_mem_eig ρ U ψ z).mp hz u, smul_smul, ← map_mul, ← hmul _ (U.inv_mem u.2) _ u.2,
      inv_mul_cancel, hone, map_one, one_smul]
  rw [Finset.sum_congr rfl (fun u _ => this u)]
  simp [Nat.cast_smul_eq_nsmul]

theorem ggE_stable {P : Type} [Group P] (ρ : Representation K P Z) (U : Subgroup P) [Fintype U]
    (ψ : P → 𝓞 K) (L : Submodule (𝓞 K) Z)
    (hst : ∀ g : P, L.map ((ρ g).restrictScalars (𝓞 K)) ≤ L) (x : Z) (hx : x ∈ L) :
    ggE ρ U ψ x ∈ L := by
  rw [ggE_apply]
  refine Submodule.sum_mem _ (fun u _ => ?_)
  rw [algebraMap_smul]
  exact L.smul_mem _ (hst _ ⟨x, hx, rfl⟩)

theorem mapsTo_locP {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W] (p : Ideal R)
    [p.IsPrime] (f : W →ₗ[R] W) (X Y : Submodule R W) (h : ∀ x ∈ X, f x ∈ Y) :
    ∀ x ∈ Formalism.HermitianLatticesTheory.localization₂ p X, f x ∈ Formalism.HermitianLatticesTheory.localization₂ p Y := by
  rintro x ⟨s, hs, hx⟩
  exact ⟨s, hs, by rw [← map_smul]; exact h _ hx⟩

theorem gg_lix_of_le (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) Z) (h : B ≤ A) :
    lix w A B = (Formalism.HermitianLatticesTheory.locLen w.asIdeal A B : ℤ) := by
  unfold lix Formalism.HermitianLatticesTheory.lidx
  rw [inf_eq_right.mpr h, Formalism.HermitianLatticesTheory.indexBasic_locLen_self]
  simp

theorem gg_isLatIn_cut [FiniteDimensional K Z] (W : Submodule K Z) (B : Submodule (𝓞 K) Z)
    (hB : IsLatIn ⊤ B) : IsLatIn W (cut W B) := by
  constructor
  · have hno : IsNoetherian (𝓞 K) B := isNoetherian_of_fg_of_noetherian B hB.1
    have h1 : ((cut W B).comap B.subtype).FG := IsNoetherian.noetherian _
    have h2 := h1.map B.subtype
    rw [Submodule.map_comap_subtype] at h2
    have : B ⊓ cut W B = cut W B := inf_eq_right.mpr inf_le_left
    rwa [this] at h2
  · apply le_antisymm
    · rw [Submodule.span_le]
      intro x hx
      exact hx.2
    · intro z hz
      have htop := Formalism.HermitianLatticesTheory.indexBasic_locS_top (K := K) B hB.2
      have hz' : z ∈ Formalism.HermitianLatticesTheory.locS (nonZeroDivisors (𝓞 K)) B := by rw [htop]; trivial
      obtain ⟨d, hd, hdz⟩ := hz'
      have hd0 : (d : K) ≠ 0 := by
        have := nonZeroDivisors.ne_zero hd
        exact_mod_cast this
      have e : z = (d : K)⁻¹ • (d • z) := by
        rw [← algebraMap_smul K d z, smul_smul, inv_mul_cancel₀ hd0, one_smul]
      rw [e]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨hdz, ?_⟩)
      rw [← algebraMap_smul K d z]
      exact W.smul_mem _ hz

end Concrete

theorem lemmaGG_of (hSc : IdxScaleIn) : LemmaGG := by
  intro K _ _ _ Z _ _ _ _ _ w P _ _ ρ U ψ hMk B B' hB hB' hle hst hst'
  classical
  have : Fintype P := Fintype.ofFinite P
  have : Fintype U := Fintype.ofFinite U
  have : Fintype (P ⧸ U) := Fintype.ofFinite _
  obtain ⟨W, hW⟩ : ∃ W, W = eig ρ U ψ := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N, N = Fintype.card U := ⟨_, rfl⟩
  have hN0 : N ≠ 0 := by rw [hN]; exact Fintype.card_ne_zero
  have hNK : (N : K) ≠ 0 := Nat.cast_ne_zero.mpr hN0
  rw [Nat.card_eq_fintype_card, ← hN, ← hW]
  have hidx : U.index = Fintype.card (P ⧸ U) := by
    unfold Subgroup.index
    rw [Nat.card_eq_fintype_card]
  rw [hidx]
  let rep : P ⧸ U → P := Quotient.out
  have hrep : ∀ i j, (rep i)⁻¹ * rep j ∈ U → i = j := by
    intro i j h
    have := QuotientGroup.eq.mpr h
    rwa [QuotientGroup.out_eq', QuotientGroup.out_eq'] at this
  have hkey : ∀ i j, ∀ a ∈ W, ggE ρ U ψ (ρ (rep i)⁻¹ (ρ (rep j) a)) =
      if i = j then (N : K) • a else 0 := by
    intro i j a ha
    have e0 : ρ (rep i)⁻¹ (ρ (rep j) a) = ρ ((rep i)⁻¹ * rep j) a := by
      rw [map_mul, Module.End.mul_apply]
    rw [e0]
    split_ifs with hij
    · rw [hij, inv_mul_cancel, map_one, Module.End.one_apply, hN]
      exact ggE_eig ρ U ψ hMk a (hW ▸ ha)
    · rw [ggE_apply]
      exact orthogonality_of_mackey K Z P ρ U ψ hMk _ (fun h => hij (hrep i j h)) a (hW ▸ ha)

  have hdim : Fintype.card (P ⧸ U) * finrank K W ≤ finrank K Z := by
    let S : ((P ⧸ U) → W) →ₗ[K] Z := ∑ i, (ρ (rep i)) ∘ₗ W.subtype ∘ₗ LinearMap.proj i
    have hS : Function.Injective S := by
      rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro f hf
      rw [LinearMap.mem_ker] at hf
      rw [Submodule.mem_bot]
      ext i
      have h1 : ggE ρ U ψ (ρ (rep i)⁻¹ (S f)) = (N : K) • (f i : Z) := by
        simp only [S, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
          Submodule.subtype_apply, map_sum]
        rw [Finset.sum_congr rfl (fun j _ => hkey i j _ (f j).2)]
        simp
      rw [hf, map_zero, map_zero] at h1
      have := (smul_eq_zero.mp h1.symm).resolve_left hNK
      simpa using this
    have := LinearMap.finrank_le_finrank_of_injective hS
    rw [Module.finrank_pi_fintype] at this
    simpa using this

  have hp : w.asIdeal.IsPrime := w.isPrime
  let s : P ⧸ U → Z →ₗ[𝓞 K] Z := fun i => (ρ (rep i)).restrictScalars (𝓞 K)
  let t : P ⧸ U → Z →ₗ[𝓞 K] Z := fun i => (ggE ρ U ψ ∘ₗ ρ (rep i)⁻¹).restrictScalars (𝓞 K)
  have hlocW : ∀ L : Submodule (𝓞 K) Z, ∀ a ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (cut W L), a ∈ W := by
    rintro L a ⟨σ, hσ, ha⟩
    have hσ0 : (σ : K) ≠ 0 := by
      have : σ ≠ 0 := fun h => hσ (by rw [h]; exact w.asIdeal.zero_mem)
      exact_mod_cast this
    have e : a = (σ : K)⁻¹ • (σ • a) := by
      rw [← algebraMap_smul K σ a, smul_smul, inv_mul_cancel₀ hσ0, one_smul]
    rw [e]
    exact W.smul_mem _ ha.2
  have hcore := gg_core (N : 𝓞 K) (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (cut W B))
    (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (cut W B')) (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (sc (N : K) (cut W B)))
    (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal B) (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal B') s t
    (fun i => mapsTo_locP _ _ _ _ (fun x hx => hst _ ⟨x, hx.1, rfl⟩))
    (fun i => mapsTo_locP _ _ _ _ (fun x hx => hst' _ ⟨x, hx.1, rfl⟩))
    (fun i => mapsTo_locP _ _ _ _ (fun x hx =>
      ⟨ggE_stable ρ U ψ B hst _ (hst _ ⟨x, hx, rfl⟩), hW ▸ ggE_mem_eig ρ U ψ hMk _⟩))
    (fun i => mapsTo_locP _ _ _ _ (fun x hx =>
      ⟨ggE_stable ρ U ψ B' hst' _ (hst' _ ⟨x, hx, rfl⟩), hW ▸ ggE_mem_eig ρ U ψ hMk _⟩))
    (by
      intro i j a ha
      have := hkey i j a (hlocW B a ha)
      have e : ((N : 𝓞 K)) • a = (N : K) • a := by
        rw [← algebraMap_smul K (N : 𝓞 K) a, map_natCast]
      rw [e]
      exact this)
    (by
      rintro c ⟨σ, hσ, hc⟩ -
      obtain ⟨y, hy, hyc⟩ := hc
      have hσ0 : (σ : K) ≠ 0 := by
        have : σ ≠ 0 := fun h => hσ (by rw [h]; exact w.asIdeal.zero_mem)
        exact_mod_cast this
      refine ⟨(σ : K)⁻¹ • y, ⟨σ, hσ, ?_⟩, ?_⟩
      · rw [← algebraMap_smul K σ, smul_smul, mul_inv_cancel₀ hσ0, one_smul]
        exact hy
      · have hyc' : (N : K) • y = (σ : K) • c := by
          rw [algebraMap_smul]
          simpa using hyc
        rw [← algebraMap_smul K (N : 𝓞 K), map_natCast, smul_comm, hyc', smul_smul,
          inv_mul_cancel₀ hσ0, one_smul])

  have hA := gg_isLatIn_cut W B hB
  obtain ⟨d, hd, hdB⟩ : ∃ d ∈ nonZeroDivisors (𝓞 K), ∀ x ∈ B, d • x ∈ B' := by
    apply Formalism.HermitianLatticesTheory.indexBasic_denom _ B B' hB.1
    rw [Formalism.HermitianLatticesTheory.indexBasic_locS_top (K := K) B' hB'.2]
    exact le_top
  have f1 := Module.length_ne_top_iff.mpr
    (Formalism.HermitianLatticesTheory.indexBasic_finLen w.asIdeal B B' hB.1 hd hdB)
  have f2 := Module.length_ne_top_iff.mpr
    (Formalism.HermitianLatticesTheory.indexBasic_finLen w.asIdeal (cut W B) (cut W B') hA.1 hd (fun x hx =>
      ⟨hdB x hx.1, (W.restrictScalars (𝓞 K)).smul_mem d hx.2⟩))
  have hNnz : (N : 𝓞 K) ∈ nonZeroDivisors (𝓞 K) :=
    mem_nonZeroDivisors_of_ne_zero (Nat.cast_ne_zero.mpr hN0)
  have eN : ∀ x : Z, (N : 𝓞 K) • x = (N : K) • x := by
    intro x
    rw [← algebraMap_smul K (N : 𝓞 K) x, map_natCast]
  have f3 := Module.length_ne_top_iff.mpr
    (Formalism.HermitianLatticesTheory.indexBasic_finLen w.asIdeal (cut W B) (sc (N : K) (cut W B)) hA.1 hNnz
      (fun x hx => ⟨x, hx, by rw [eN]; rfl⟩))
  have hscle : sc (N : K) (cut W B) ≤ cut W B := by
    rintro x ⟨y, hy, rfl⟩
    have : ((N : K) • (LinearMap.id : Z →ₗ[K] Z)).restrictScalars (𝓞 K) y = (N : 𝓞 K) • y := by
      rw [eN]; rfl
    rw [this]
    exact (cut W B).smul_mem _ hy
  obtain ⟨-, hsc⟩ := hSc K Z w W (cut W B) (cut W B) hA hA (N : K) hNK
  rw [gg_lix_of_le w _ _ hscle, gg_lix_of_le w _ _ le_rfl, Formalism.HermitianLatticesTheory.indexBasic_locLen_self] at hsc
  have hcutle : cut W B' ≤ cut W B := inf_le_inf_right _ hle
  rw [gg_lix_of_le w (cut W B) (cut W B') hcutle, gg_lix_of_le w _ _ hle]
  unfold Formalism.HermitianLatticesTheory.locLen at hsc ⊢
  revert hcore hsc
  generalize Module.length (𝓞 K) (↥(Formalism.HermitianLatticesTheory.localization₂ w.asIdeal B) ⧸
    (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal B').comap (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal B).subtype) = l1 at f1 ⊢
  generalize Module.length (𝓞 K) (↥(Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (cut W B)) ⧸
    (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (cut W B')).comap (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (cut W B)).subtype) = l2 at f2 ⊢
  generalize Module.length (𝓞 K) (↥(Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (cut W B)) ⧸
    (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (sc (N : K) (cut W B))).comap
      (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (cut W B)).subtype) = l3 at f3 ⊢
  intro hcore hsc
  lift l1 to ℕ using f1
  lift l2 to ℕ using f2
  lift l3 to ℕ using f3
  simp only [ENat.toNat_natCast] at hsc ⊢
  have hc' : Fintype.card (P ⧸ U) * l2 ≤ l1 + Fintype.card (P ⧸ U) * l3 := by exact_mod_cast hcore
  have hv : 0 ≤ vw w (N : K) := by
    have := (valuation_basic_properties K w).2.2.2.2.2.2 (N : 𝓞 K)
    simpa using this
  have hc'' : (Fintype.card (P ⧸ U) : ℤ) * l2 ≤ l1 + (Fintype.card (P ⧸ U) : ℤ) * l3 := by
    exact_mod_cast hc'
  have hdim' : (Fintype.card (P ⧸ U) : ℤ) * (finrank K W : ℤ) ≤ (finrank K Z : ℤ) := by
    exact_mod_cast hdim
  rw [hsc, Nat.cast_zero, zero_add, ← mul_assoc] at hc''
  have := mul_le_mul_of_nonneg_right hdim' hv
  linarith

theorem good_index_GG : LemmaGG := lemmaGG_of index_scale_inclusion

theorem data_trace : DataTrace := by
  intro K _ _ _ Z _ _ _ _ U _ _ ρ ψ X _ _ _ hfree Θ hΘ z hz heig
  classical
  obtain ⟨φ, rfl⟩ := hz

  obtain ⟨φ', hφ'⟩ : ∃ φ' : X → 𝓞 K, φ' = fun x => ∑ u : U, ψ u⁻¹ * φ (u⁻¹ • x) := ⟨_, rfl⟩
  have hinv : ∀ u : U, ψ u⁻¹ * ψ u = 1 := by
    intro u
    rw [← map_mul, inv_mul_cancel, map_one]
  have h1 : ((Fintype.card U : ℕ) : K) • Θ φ = Θ φ' := by
    have e1 : ∀ u : U, Θ φ = (ψ u⁻¹ : 𝓞 K) • Θ (fun x => φ (u⁻¹ • x)) := by
      intro u
      rw [← hΘ, heig u, algebraMap_smul, smul_smul, hinv, one_smul]
    have e2 : φ' = ∑ u : U, (ψ u⁻¹ : 𝓞 K) • (fun x => φ (u⁻¹ • x)) := by
      rw [hφ']
      ext x
      simp [Finset.sum_apply]
    rw [e2, map_sum]
    simp only [map_smul]
    rw [← Finset.sum_congr rfl (fun u _ => e1 u)]
    simp [Nat.cast_smul_eq_nsmul]
  have hequiv : ∀ (u0 : U) (x : X), φ' (u0⁻¹ • x) = ψ u0 * φ' x := by
    intro u0 x
    rw [hφ']
    simp only
    rw [Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft u0) _ _ (fun u => ?_)
    simp only [Equiv.coe_mulLeft, mul_inv_rev, map_mul, mul_smul]
    have := hinv u0
    have e : ψ u0 * (ψ u⁻¹ * ψ u0⁻¹ * φ (u⁻¹ • u0⁻¹ • x)) =
        (ψ u0⁻¹ * ψ u0) * (ψ u⁻¹ * φ (u⁻¹ • u0⁻¹ • x)) := by ring
    rw [e, this, one_mul]
  rw [h1]

  let Ω := MulAction.orbitRel.Quotient U X
  have : Fintype Ω := Fintype.ofFinite _
  let rep : Ω → X := Quotient.out
  have hdec : φ' = ∑ ω : Ω, φ' (rep ω) •
      (fun x => ∑ u : U, if x = u⁻¹ • rep ω then ψ u else 0) := by
    ext x
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    set ω0 : Ω := Quotient.mk'' x with hω0
    have hx : x ∈ MulAction.orbit U (rep ω0) := by
      have : (Quotient.mk'' (rep ω0) : Ω) = Quotient.mk'' x := Quotient.out_eq' ω0
      exact MulAction.orbitRel_apply.mp (Quotient.eq''.mp this.symm)
    obtain ⟨v, hv⟩ := hx
    have hv' : x = (v⁻¹)⁻¹ • rep ω0 := by rw [inv_inv]; exact hv.symm
    rw [Finset.sum_eq_single ω0]
    · rw [Finset.sum_eq_single v⁻¹]
      · rw [if_pos hv']
        conv_lhs => rw [hv']
        rw [hequiv, mul_comm]
      · intro u _ hu
        rw [if_neg]
        intro hxu
        apply hu
        have e : (u * v) • rep ω0 = rep ω0 := by
          have hv2 : v • rep ω0 = x := hv
          rw [mul_smul, hv2, hxu, smul_inv_smul]
        have := hfree _ _ e
        exact eq_inv_of_mul_eq_one_left this
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro ω _ hω
      rw [Finset.sum_eq_zero, mul_zero]
      intro u _
      rw [if_neg]
      intro hxu
      apply hω
      have : (Quotient.mk'' x : Ω) = Quotient.mk'' (rep ω) := by
        apply Quotient.eq''.mpr
        apply MulAction.orbitRel_apply.mpr
        exact ⟨u⁻¹, hxu.symm⟩
      rw [hω0, this]
      exact (Quotient.out_eq' ω).symm
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hdec, map_sum]
  refine Submodule.sum_mem _ (fun ω _ => ?_)
  rw [map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨rep ω, rfl⟩)

end Formalism.EigenvalueLevelCeiling
