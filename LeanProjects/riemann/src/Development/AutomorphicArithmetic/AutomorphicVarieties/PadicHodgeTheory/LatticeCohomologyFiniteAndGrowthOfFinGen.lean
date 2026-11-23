import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TateDefs
import ReciprocityTheory.GroupCohomology.ImportsAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.LenOfCard
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

open ReciprocityTheory.Coh in
private theorem latGrow_bound {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {n : ℕ}
    (ρ : Representation ℤ_[l] G (Fin n → ℤ_[l])) (h : ContAction ρ)
    (hF : Cx.FinGen (TRep.coch ({ V := Fin n → ℤ_[l], rho := ρ, cont := h } : TRep ℤ_[l] G)) 2) (k : ℕ) :
    ∃ C : ℕ, ∀ m : ℕ,
      (length ℤ_[l] (({ V := _, rho := redRep ρ m, cont := contAction_redRep h m } : TRep ℤ_[l] G).H k)).toNat ≤
        m * finrank ℤ_[l] (({ V := Fin n → ℤ_[l], rho := ρ, cont := h } : TRep ℤ_[l] G).H k) + C ∧
      m * finrank ℤ_[l] (({ V := Fin n → ℤ_[l], rho := ρ, cont := h } : TRep ℤ_[l] G).H k) ≤
      (length ℤ_[l] (({ V := _, rho := redRep ρ m, cont := contAction_redRep h m } : TRep ℤ_[l] G).H k)).toNat := by
  let L : TRep ℤ_[l] G := { V := Fin n → ℤ_[l], rho := ρ, cont := h }
  refine ⟨(length ℤ_[l] (Submodule.torsion ℤ_[l] (L.H k))).toNat +
    (length ℤ_[l] (Submodule.torsion ℤ_[l] (L.H (k + 1)))).toNat, fun m => ?_⟩
  let C : TRep ℤ_[l] G := { V := _, rho := redRep ρ m, cont := contAction_redRep h m }
  have hc : Continuous (((l : ℤ_[l]) ^ m) • (LinearMap.id : (Fin n → ℤ_[l]) →ₗ[ℤ_[l]] (Fin n → ℤ_[l]))) :=
    continuous_const_smul ((l : ℤ_[l]) ^ m)
  let i : Pair L L := Pair.ofMap (((l : ℤ_[l]) ^ m) • (LinearMap.id : (Fin n → ℤ_[l]) →ₗ[ℤ_[l]] (Fin n → ℤ_[l]))) hc
    fun g x => (map_smul (ρ g) ((l : ℤ_[l]) ^ m) x).symm
  let p : Pair L C := Pair.ofMap (lSub l (Fin n → ℤ_[l]) m).mkQ (continuous_mkQ _) fun _ _ => rfl
  have hl : (l : ℤ_[l]) ^ m ≠ 0 := pow_ne_zero _ PadicInt.irreducible_p.ne_zero
  have hA : admitted i p := by
    refine ⟨rfl, rfl, ?_, ?_, ?_⟩
    · refine (hc.isClosedEmbedding ?_).isEmbedding
      exact smul_right_injective (Fin n → ℤ_[l]) hl
    · exact LinearMap.exact_map_mkQ_range _
    · exact ⟨Function.surjInv (lSub l (Fin n → ℤ_[l]) m).mkQ_surjective,
        continuous_of_discreteTopology (α := (Fin n → ℤ_[l]) ⧸ lSub l (Fin n → ℤ_[l]) m),
        Function.surjInv_eq _⟩
  have hR := (rankLen_holds ℤ_[l] (l : ℤ_[l]) PadicInt.irreducible_p L.coch C.coch i.hom p.hom m 2
    (fun _ _ => rfl) (admissibility_holds _ _ _ _ _ i p hA) hF).2.2 k
  exact ⟨hR.1.trans (add_assoc _ _ _).le, hR.2⟩

private theorem latGrow_card {l : ℕ} [Fact l.Prime] {M N : Type} [AddCommGroup M] [Module ℤ_[l] M]
    [AddCommGroup N] [Module ℤ_[l] N] [Finite N] (e : M ≃ₗ[ℤ_[l]] N) {a b : ℕ}
    (h : (length ℤ_[l] M).toNat ≤ b ∧ a ≤ (length ℤ_[l] M).toNat) :
    l ^ a ≤ Nat.card N ∧ Nat.card N ≤ l ^ b := by
  obtain ⟨k, hk, hc⟩ := UpperTheory.V.Kum.lenOfCard l N
  rw [e.length_eq, hk, ENat.toNat_coe] at h
  rw [hc]
  have hp : 0 < l := (Fact.out : l.Prime).pos
  exact ⟨Nat.pow_le_pow_right hp h.2, Nat.pow_le_pow_right hp h.1⟩

open ReciprocityTheory.Coh in
theorem UpperTheory.lattice_cohomology_finite_and_growth_of_finGen :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {n : ℕ} (ρ : Representation ℤ_[l] G (Fin n → ℤ_[l])) (h : ContAction ρ), ReciprocityTheory.Coh.Cx.FinGen (ReciprocityTheory.Coh.TRep.coch ({ V := Fin n → ℤ_[l], rho := ρ, cont := h } : ReciprocityTheory.Coh.TRep ℤ_[l] G)) 2 → (∀ m, Finite (H1 (redRep ρ m)) ∧ Finite (H2 (redRep ρ m))) → Module.Finite ℤ_[l] (H1 ρ) ∧ Module.Finite ℤ_[l] (H2 ρ) ∧ Grows l (fun m => Nat.card ↥(H0 (redRep ρ m))) (finrank ℤ_[l] ↥(H0 ρ)) ∧ Grows l (fun m => Nat.card (H1 (redRep ρ m))) (finrank ℤ_[l] (H1 ρ)) ∧ Grows l (fun m => Nat.card (H2 (redRep ρ m))) (finrank ℤ_[l] (H2 ρ)) := by
  intro l _ G _ _ _ n ρ h hF hfin
  obtain ⟨-, ⟨e₀, -⟩, ⟨e₁, -⟩, e₂, -⟩ :=
    low_holds ℤ_[l] G ({ V := Fin n → ℤ_[l], rho := ρ, cont := h } : TRep ℤ_[l] G)
  have hq := fun m => low_holds ℤ_[l] G ({ V := _, rho := redRep ρ m, cont := contAction_redRep h m } : TRep ℤ_[l] G)
  haveI := hF.1 1
  haveI := hF.1 2
  refine ⟨Module.Finite.equiv e₁, Module.Finite.equiv e₂, ?_, ?_, ?_⟩
  · obtain ⟨C, hC⟩ := latGrow_bound ρ h hF 0
    refine ⟨C, fun m _ => ?_⟩
    obtain ⟨-, ⟨q, -⟩, -⟩ := hq m
    rw [e₀.finrank_eq] at hC
    haveI : Finite (H0 (redRep ρ m)) := inferInstance
    exact latGrow_card (N := H0 (redRep ρ m)) q (hC m)
  · obtain ⟨C, hC⟩ := latGrow_bound ρ h hF 1
    refine ⟨C, fun m _ => ?_⟩
    obtain ⟨-, -, ⟨q, -⟩, -⟩ := hq m
    rw [e₁.finrank_eq] at hC
    haveI := (hfin m).1
    exact latGrow_card (N := H1 (redRep ρ m)) q (hC m)
  · obtain ⟨C, hC⟩ := latGrow_bound ρ h hF 2
    refine ⟨C, fun m _ => ?_⟩
    obtain ⟨-, -, -, q, -⟩ := hq m
    rw [e₂.finrank_eq] at hC
    haveI := (hfin m).2
    exact latGrow_card (N := H2 (redRep ρ m)) q (hC m)
