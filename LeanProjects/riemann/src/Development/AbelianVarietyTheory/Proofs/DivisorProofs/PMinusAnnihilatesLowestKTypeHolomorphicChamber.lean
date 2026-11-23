import Mathlib
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHighestVectorRealWeightUnitaryCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordReachingIrreducibleKModuleReachesHighestWeigStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VoganNormSqLtOfRemoveNoncompactRootStatement
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

theorem GlobalTheory.HolDS.pMinus_kills_lowest : ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ), GlRel E → IsUnitary ε E → StrictAnti lam → IsHolChamber ε lam → IsMin ε E lam → ∀ L : Submodule ℂ V, FiniteDimensional ℂ L → KStab ε E L → (∀ ν : Fin n → ℝ, ∀ x ∈ L, x ≠ 0 → KHighest ε E ν x → ν = lowK ε lam) → ∀ a b : Fin n, ε a = true → ε b = false → ∀ x ∈ L, E b a x = 0 := by
  intro n ε V _ _ E lam hgl hu hanti hhol hmin L hL hLs hLh a b ha hb x hx
  by_contra hne
  have hkrel : KRel ε E := fun a b c d _ _ => hgl a b c d
  have hkunit : KUnit ε E := fun a b hab x y => by
    rw [hu a b x y]; simp [Formalism.REAL.sgn, hab]
  let N : Submodule ℂ V := ⨆ p : {p : Fin n × Fin n // ε p.1 = true ∧ ε p.2 = false}, L.map (E p.1.2 p.1.1)
  have hNfd : FiniteDimensional ℂ N := by infer_instance
  have hgen : ∀ p : {p : Fin n × Fin n // ε p.1 = true ∧ ε p.2 = false}, ∀ y ∈ L, E p.1.2 p.1.1 y ∈ N :=
    fun p y hy => (le_iSup (fun p : {p : Fin n × Fin n // ε p.1 = true ∧ ε p.2 = false} => L.map (E p.1.2 p.1.1)) p)
      (Submodule.mem_map_of_mem hy)
  have hNs : KStab ε E N := by
    intro c d hcd v hv
    refine Submodule.iSup_induction _ (motive := fun v => E c d v ∈ N) hv ?_ ?_ ?_
    · intro p v hv
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hv
      have hc := hgl c d p.1.2 p.1.1
      have key : E c d (E p.1.2 p.1.1 y) = E p.1.2 p.1.1 (E c d y) +
          ((if d = p.1.2 then E c p.1.1 else 0) - (if p.1.1 = c then E p.1.2 d else 0)) y := by
        rw [← hc]; simp [Module.End.mul_apply]
      rw [key]
      refine N.add_mem (hgen p _ (hLs c d hcd y hy)) ?_
      rw [LinearMap.sub_apply]
      refine N.sub_mem ?_ ?_
      · split_ifs with h
        · exact hgen ⟨(p.1.1, c), p.2.1, by rw [hcd, h]; exact p.2.2⟩ y hy
        · simp
      · split_ifs with h
        · exact hgen ⟨(d, p.1.2), by rw [← hcd, ← h]; exact p.2.1, p.2.2⟩ y hy
        · simp
    · simp
    · intro u v hu hv; rw [map_add]; exact N.add_mem hu hv
  have hxN : E b a x ∈ N := hgen ⟨(a, b), ha, hb⟩ x hx
  have hN0 : N ≠ ⊥ := fun h => hne (by rw [h, Submodule.mem_bot] at hxN; exact hxN)
  obtain ⟨μ, w, hwN, hw0, hwh⟩ := GlobalTheory.T.exists_highest_vector_real_weight_unitary_compact n ε V E hkrel hkunit N hNfd hNs hN0
  have hex : ∃ p : {p : Fin n × Fin n // ε p.1 = true ∧ ε p.2 = false}, ∃ y ∈ L, ⟪E p.1.2 p.1.1 y, w⟫_ℂ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have horth : ∀ v ∈ N, ⟪v, w⟫_ℂ = 0 := fun v hv =>
      Submodule.iSup_induction _ (motive := fun v => ⟪v, w⟫_ℂ = 0) hv
        (fun p v hv => by obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hv; exact hcon p y hy)
        (by simp) (fun u v hu hv => by rw [inner_add_left, hu, hv, add_zero])
    exact hw0 (inner_self_eq_zero.1 (horth w hwN))
  obtain ⟨p, y, hy, hyw⟩ := hex
  have hyw' : ⟪y, ([(p.1.1, p.1.2)].map fun q : Fin n × Fin n => E q.1 q.2).prod w⟫_ℂ ≠ 0 := by
    have h1 := hu p.1.2 p.1.1 y w
    have hs : Formalism.REAL.sgn ε p.1.2 p.1.1 = -1 := by simp [Formalism.REAL.sgn, p.2.1, p.2.2]
    rw [hs] at h1
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    intro h0; apply hyw; rw [h1, h0]; simp
  obtain ⟨l', hl'len, hl'ε, hl'sum⟩ := GlobalTheory.T.word_reaching_irreducible_k_module_reaches_highest_weight n ε V E hgl hkunit L hL hLs (lowK ε lam) hLh μ w hwh
    true false [(p.1.1, p.1.2)] (by simp [p.2.1, p.2.2]) y hy hyw'
  obtain ⟨q, rfl⟩ := List.length_eq_one_iff.1 hl'len
  have hq := hl'ε q (by simp)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hl'sum
  have hμ : μ = lowK ε lam - root q.1 q.2 := eq_sub_of_add_eq hl'sum
  have hlt := GlobalTheory.T.voganNormSq_lt_of_remove_noncompactRoot n ε lam hanti hhol q.1 q.2 hq.1 hq.2
  have hle := hmin μ w hw0 hwh
  rw [hμ] at hle
  exact absurd (lt_of_lt_of_le hlt hle) (lt_irrefl _)
