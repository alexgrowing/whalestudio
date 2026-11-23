import Formalism.LocalToGlobal.GroupLattices.TrivialTransfer.OneAddPowOfSq
import Formalism.LocalToGlobal.GroupLattices.TrivialTransfer.FiniteStabAtOfLocal

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain Formalism.UG Formalism.UG.P Formalism.BasicNotions

namespace Formalism.L2.G.Triv

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {k : ℕ}

local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F

theorem gen_coprime (U : Subgroup (GL (Fin k) 𝒜)) (g : ℕ) (hg : g.Prime) (v : HeightOneSpectrum (𝓞 F))
    (hv : (g : 𝓞 F) ∈ v.asIdeal) (ρ : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F)
    (h : GL (Fin k) (v.adicCompletion F))
    (hU : ∀ z ∈ U, h⁻¹ * bc ρ (bc (prV (E := E) v) z) * h ∈ iwU F k v)
    (x : GL (Fin k) 𝒜) (γ : GL (Fin k) E) (hγ : x⁻¹ * bc (inclE (F := F) 𝔸) γ * x ∈ U) (N : ℕ) (hN : Nat.Coprime N g)
    (hγN : bc (inclE (F := F) 𝔸) γ ^ N = 1) : γ = 1 := by
  have hφ : ∀ A : GL (Fin k) E, bc ρ (bc (prV (E := E) v) (bc (inclE (F := F) 𝔸) A))
      = bc (ρ.comp ((prV (E := E) v).comp (inclE (F := F) 𝔸))) A := by
    intro A
    apply Units.ext
    ext i j
    simp [bc]
  have hinj : Function.Injective (ρ.comp ((prV (E := E) v).comp (inclE (F := F) 𝔸))) :=
    RingHom.injective _
  have hz : (x⁻¹ * bc (inclE (F := F) 𝔸) γ * x) ^ N = 1 := by
    rw [show x⁻¹ * bc (inclE (F := F) 𝔸) γ * x = MulAut.conj x⁻¹ (bc (inclE (F := F) 𝔸) γ) by
      simp [MulAut.conj_apply], ← map_pow, hγN, map_one]
  have hmem := hU _ hγ
  have hwN : (bc ρ (bc (prV (E := E) v) (x⁻¹ * bc (inclE (F := F) 𝔸) γ * x))) ^ N = 1 := by
    rw [← map_pow, ← map_pow, hz, map_one, map_one]
  have hδN : (h⁻¹ * bc ρ (bc (prV (E := E) v) (x⁻¹ * bc (inclE (F := F) 𝔸) γ * x)) * h) ^ N = 1 := by
    rw [show h⁻¹ * bc ρ (bc (prV (E := E) v) (x⁻¹ * bc (inclE (F := F) 𝔸) γ * x)) * h
        = MulAut.conj h⁻¹ (bc ρ (bc (prV (E := E) v) (x⁻¹ * bc (inclE (F := F) 𝔸) γ * x))) by
      simp only [MulAut.conj_apply, inv_inv], ← map_pow, hwN, map_one]
  have hδ1 := iwU_coprime v g hg hv _ hmem N hN hδN
  have hw1 : bc ρ (bc (prV (E := E) v) (x⁻¹ * bc (inclE (F := F) 𝔸) γ * x)) = 1 := by
    calc _ = h * (h⁻¹ * bc ρ (bc (prV (E := E) v) (x⁻¹ * bc (inclE (F := F) 𝔸) γ * x)) * h) * h⁻¹ := by
          group
      _ = 1 := by rw [hδ1]; group
  simp only [map_mul, map_inv] at hw1
  rw [hφ] at hw1
  have hγ1 : bc (ρ.comp ((prV (E := E) v).comp (inclE (F := F) 𝔸))) γ = 1 := by
    calc _ = bc ρ (bc (prV (E := E) v) x) * ((bc ρ (bc (prV (E := E) v) x))⁻¹
          * bc (ρ.comp ((prV (E := E) v).comp (inclE (F := F) 𝔸))) γ * bc ρ (bc (prV (E := E) v) x))
          * (bc ρ (bc (prV (E := E) v) x))⁻¹ := by group
      _ = 1 := by rw [hw1]; group
  apply Units.ext
  ext i j
  apply hinj
  have e := congrArg (fun A : GL (Fin k) (v.adicCompletion F) => A.1 i j) hγ1
  simpa [bc, Matrix.one_apply, apply_ite] using e

private lemma inv_mul_mul_pow {G : Type} [Group G] (x y : G) (n : ℕ) :
    (x⁻¹ * y * x) ^ n = x⁻¹ * y ^ n * x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, pow_succ]; group

theorem gen_triv (σ : E →ₐ[F] E) (J : Matrix (Fin k) (Fin k) E)
    (hτ : ∀ τ : E →+* ℂ, τ.comp (σ : E →+* E) = (starRingEnd ℂ).comp τ)
    (hH : IsHerm (σ : E →+* E) J) (hdet : IsUnit J.det) (hdef : IsTotDef σ J)
    (Λ : Submodule (𝓞 E) (Fin k → E)) (hfin : Module.Finite (𝓞 E) Λ)
    (hspan : Submodule.span E (Λ : Set (Fin k → E)) = ⊤)
    (U : Subgroup (GL (Fin k) 𝒜))
    (hU : ∀ x ∈ U, ∀ v : HeightOneSpectrum (𝓞 F),
      bc (prV (E := E) v) x ∈ stabGL (latS (F := F) (v.adicCompletion F) (SV E v) Λ))
    (g : Fin 2 → ℕ) (hg : ∀ i, (g i).Prime) (hne : g 0 ≠ g 1) (v : Fin 2 → HeightOneSpectrum (𝓞 F))
    (hv : ∀ i, (g i : 𝓞 F) ∈ (v i).asIdeal) (ρ : ∀ i, E ⊗[F] (v i).adicCompletion F →+* (v i).adicCompletion F)
    (h : ∀ i, GL (Fin k) ((v i).adicCompletion F))
    (hUg : ∀ i, ∀ z ∈ U, (h i)⁻¹ * bc (ρ i) (bc (prV (E := E) (v i)) z) * h i ∈ iwU F k (v i))
    (x : UPts σ J 𝔸) (γ : GL (Fin k) E) (hγJ : γ ∈ UJ (σ : E →+* E) J)
    (hγ : (x : GL (Fin k) 𝒜)⁻¹ * bc (inclE (F := F) 𝔸) γ * x ∈ U) : γ = 1 := by
  have hyR : bc (inclE (F := F) 𝔸) γ ∈ ratPts σ J 𝔸 := ⟨γ, hγJ, rfl⟩
  have hyU : bc (inclE (F := F) 𝔸) γ ∈ UPts σ J 𝔸 :=
    Formalism.UG.P.rational_points_le_holds F E (Fin k) σ J 𝔸 hyR
  have hpowU : ∀ m : ℕ, (x : GL (Fin k) 𝒜)⁻¹ * bc (inclE (F := F) 𝔸) γ ^ m * x ∈ U := by
    intro m
    rw [← inv_mul_mul_pow]
    exact U.pow_mem hγ m
  haveI hfinS := finite_stabAt_of_local σ J hτ hH hdet hdef Λ hfin hspan U hU x
  let f : ℕ → stabAt ((ratPts σ J 𝔸).subgroupOf (UPts σ J 𝔸)) (U.subgroupOf (UPts σ J 𝔸)) x :=
    fun m => ⟨⟨⟨bc (inclE (F := F) 𝔸) γ ^ m, pow_mem hyU m⟩, Subgroup.mem_subgroupOf.2 (pow_mem hyR m)⟩,
      by
        show _ ∈ U.subgroupOf (UPts σ J 𝔸)
        exact Subgroup.mem_subgroupOf.2 (hpowU m)⟩
  obtain ⟨m₁, m₂, hne12, heq⟩ := Finite.exists_ne_map_eq_of_infinite f
  have hpow : bc (inclE (F := F) 𝔸) γ ^ m₁ = bc (inclE (F := F) 𝔸) γ ^ m₂ := by
    have e := congrArg (fun s => ((s.1 : UPts σ J 𝔸) : GL (Fin k) 𝒜)) heq
    exact e

  obtain ⟨N, hN0, hyN⟩ : ∃ N : ℕ, 0 < N ∧ bc (inclE (F := F) 𝔸) γ ^ N = 1 := by
    rcases Nat.lt_or_gt_of_ne hne12 with hlt | hlt
    · refine ⟨m₂ - m₁, Nat.sub_pos_of_lt hlt, ?_⟩
      have e : bc (inclE (F := F) 𝔸) γ ^ m₂
          = bc (inclE (F := F) 𝔸) γ ^ m₁ * bc (inclE (F := F) 𝔸) γ ^ (m₂ - m₁) := by
        rw [← pow_add, Nat.add_sub_cancel' hlt.le]
      rw [← hpow] at e
      exact mul_left_cancel (a := bc (inclE (F := F) 𝔸) γ ^ m₁) (by rw [mul_one]; exact e.symm)
    · refine ⟨m₁ - m₂, Nat.sub_pos_of_lt hlt, ?_⟩
      have e : bc (inclE (F := F) 𝔸) γ ^ m₁
          = bc (inclE (F := F) 𝔸) γ ^ m₂ * bc (inclE (F := F) 𝔸) γ ^ (m₁ - m₂) := by
        rw [← pow_add, Nat.add_sub_cancel' hlt.le]
      rw [hpow] at e
      exact mul_left_cancel (a := bc (inclE (F := F) 𝔸) γ ^ m₂) (by rw [mul_one]; exact e.symm)

  obtain ⟨a, m, hm, hNam⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN0.ne' (g 0) (hg 0).one_lt.ne'
  have hg0m : Nat.Coprime m (g 0) :=
    Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd (hg 0)).mpr hm)
  have hγ1 : γ ^ (g 0 ^ a) = 1 := by
    refine gen_coprime U (g 0) (hg 0) (v 0) (hv 0) (ρ 0) (h 0) (hUg 0) (x : GL (Fin k) 𝒜)
      (γ ^ (g 0 ^ a)) ?_ m hg0m ?_
    · rw [map_pow]
      exact hpowU _
    · rw [map_pow, ← pow_mul, ← hNam]
      exact hyN
  have hcop : Nat.Coprime (g 0 ^ a) (g 1) :=
    Nat.Coprime.pow_left a ((Nat.coprime_primes (hg 0) (hg 1)).mpr hne)
  refine gen_coprime U (g 1) (hg 1) (v 1) (hv 1) (ρ 1) (h 1) (hUg 1) (x : GL (Fin k) 𝒜) γ hγ
    (g 0 ^ a) hcop ?_
  rw [← map_pow, hγ1, map_one]

end Formalism.L2.G.Triv

end
