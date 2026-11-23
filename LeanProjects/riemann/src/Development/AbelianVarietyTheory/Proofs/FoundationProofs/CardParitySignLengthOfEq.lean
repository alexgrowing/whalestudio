import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntSmulIntegral

noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.NearerNeighbour

theorem exists_step {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (N : Submodule R M)
    [Finite (M ⧸ N)] (hN : N ≠ ⊤) :
    ∃ (P : Ideal R) (x : M), P.IsMaximal ∧ x ∉ N ∧ (∀ p ∈ P, p • x ∈ N) ∧
      (Module.length R (M ⧸ (N ⊔ Submodule.span R {x}))).toNat + 1 = (Module.length R (M ⧸ N)).toNat := by
  haveI : Nontrivial (M ⧸ N) := Submodule.Quotient.nontrivial_iff.2 hN
  haveI : IsArtinian R (M ⧸ N) := isArtinian_of_finite
  haveI : IsNoetherian R (M ⧸ N) := isNoetherian_of_finite R _
  obtain ⟨S, hS⟩ := IsAtomic.exists_atom (Submodule R (M ⧸ N))
  haveI hs : IsSimpleModule R S := isSimpleModule_iff_isAtom.2 hS
  obtain ⟨P, hP, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.1 hs
  obtain ⟨x, hx⟩ := N.mkQ_surjective (e.symm 1 : S)
  have h0 : N.mkQ x ≠ 0 := by
    rw [hx]
    intro h
    have h1 : e.symm 1 = 0 := Subtype.ext h
    rw [LinearEquiv.map_eq_zero_iff] at h1
    exact hP.ne_top (Ideal.Quotient.zero_eq_one_iff.1 h1.symm)
  have hmap : (N ⊔ Submodule.span R {x}).map N.mkQ = S := by
    rw [Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq, Submodule.map_span, Set.image_singleton]
    refine (hS.le_iff.1 ?_).resolve_left ?_
    · rw [Submodule.span_singleton_le_iff_mem, hx]; exact (e.symm 1).2
    · rwa [Submodule.span_singleton_eq_bot]
  refine ⟨P, x, hP, fun h => h0 ((Submodule.Quotient.mk_eq_zero N).2 h), fun p hp => ?_, ?_⟩
  · rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_smul, hx, ← Submodule.coe_smul, ← map_smul]
    have : p • (1 : R ⧸ P) = 0 := by
      rw [← Algebra.algebraMap_eq_smul_one]
      exact Ideal.Quotient.eq_zero_iff_mem.2 hp
    rw [this, map_zero]; rfl
  · have h1 := Module.length_eq_add_of_exact S.subtype S.mkQ S.injective_subtype S.mkQ_surjective
      (LinearMap.exact_subtype_mkQ S)
    have h2 := (Submodule.quotientQuotientEquivQuotient N (N ⊔ Submodule.span R {x}) le_sup_left).length_eq
    rw [hmap] at h2
    have h3 : Module.length R ((M ⧸ N) ⧸ S) ≠ ⊤ := Module.length_ne_top
    rw [← h2, h1, Module.length_eq_one R S, ENat.toNat_add (by simp) h3, add_comm]
    simp

theorem exists_prime_mem {K : Type*} [Field K] [NumberField K] (P : Ideal (𝓞 K)) (hP : P.IsMaximal) :
    ∃ q : ℕ, q.Prime ∧ (q : 𝓞 K) ∈ P := by
  have hb : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField K)
  haveI : Finite (𝓞 K ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hb
  letI := Ideal.Quotient.field P
  refine ⟨ringChar (𝓞 K ⧸ P), CharP.prime_ringChar _, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact ringChar.Nat.cast_ringChar

theorem exists_int_smul_mem {K V : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (L : Submodule (𝓞 K) V)
    (hL : Submodule.span K (L : Set V) = ⊤) (y : V) : ∃ m : ℤ, m ≠ 0 ∧ m • y ∈ L := by
  first
  | exact @_root_.GlobalTheory.IntegerScalarIntegral.main
  | exact _root_.GlobalTheory.IntegerScalarIntegral.main
  | (apply _root_.GlobalTheory.IntegerScalarIntegral.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegerScalarIntegral.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegerScalarIntegral.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegerScalarIntegral.main ..)

theorem exists_nearer : ∀ (D : D7) (n : ℕ) (L₀ L : Lat D n), SD D L₀ → SD D L → L₀ ≠ L → ∃ (P : Ideal (𝓞 D.host.E)) (q : ℕ) (x : Fin n → D.host.E), P.IsMaximal ∧ q.Prime ∧ (q : 𝓞 D.host.E) ∈ P ∧ x ∈ L₀ ∧ NbD D P L x ∧ lenQ D L₀ (nbr D L x) + 1 = lenQ D L₀ L := by
  intro D n L₀ L h₀ h hne
  obtain ⟨fg₀, -, d₀⟩ := (sd_iff D L₀).1 h₀
  obtain ⟨-, sp, d⟩ := (sd_iff D L).1 h
  have hN : Submodule.comap L₀.subtype L ≠ ⊤ := by
    intro ht
    have hle : L₀ ≤ L := Submodule.comap_subtype_eq_top.1 ht
    exact hne (le_antisymm hle fun y hy => (d₀ y).2 fun x hx => (d y).1 hy x (hle hx))
  haveI : Module.Finite (𝓞 D.host.E) L₀ := Module.Finite.iff_fg.2 fg₀
  haveI : Module.Finite ℤ (L₀ ⧸ Submodule.comap L₀.subtype L) :=
    Module.Finite.trans (𝓞 D.host.E) _
  haveI : Finite (L₀ ⧸ Submodule.comap L₀.subtype L) := Module.finite_of_fg_torsion _ fun z => by
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    obtain ⟨m, hm, hy⟩ := exists_int_smul_mem L sp y.1
    refine ⟨⟨m, mem_nonZeroDivisors_of_ne_zero hm⟩, ?_⟩
    change m • (Submodule.mkQ (Submodule.comap L₀.subtype L) y) = 0
    rw [← map_zsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hy
  obtain ⟨P, x, hP, hx, hPx, hlen⟩ := exists_step _ hN
  obtain ⟨q, hq, hqP⟩ := exists_prime_mem P hP
  refine ⟨P, q, x.1, hP, hq, hqP, x.2, ⟨hx, hPx, (d₀ x.1).1 x.2 x.1 x.2⟩, ?_⟩
  have key : Submodule.comap L₀.subtype (nbr D L x.1) =
      Submodule.comap L₀.subtype L ⊔ Submodule.span (𝓞 D.host.E) {x} := by
    apply le_antisymm
    · intro y hy
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hy
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hb
      refine Submodule.mem_sup.2 ⟨y - c • x, ?_, c • x, Submodule.mem_span_singleton.2 ⟨c, rfl⟩, sub_add_cancel _ _⟩
      have : L₀.subtype (y - c • x) = a := by
        rw [map_sub, ← hab, map_smul]; exact add_sub_cancel_right _ _
      rw [Submodule.mem_comap, this]
      exact ha.1
    · refine sup_le (fun y hy => ?_) ?_
      · exact Submodule.mem_sup_left (S := nbM D L x.1) ⟨hy, (d₀ y.1).1 y.2 x.1 x.2⟩
      · rw [Submodule.span_singleton_le_iff_mem]
        exact Submodule.mem_sup_right (S := nbM D L x.1) (Submodule.mem_span_singleton_self _)
  unfold lenQ
  rw [key]
  exact hlen

end GlobalTheory.NearerNeighbour
