import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.TraceQuot
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriTraceOfBorelCasselman
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LiftEigen

open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

private theorem lift_eigen {T V : Type} [CommGroup T] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ T V) {ψ μ : T →* ℂˣ} {v y : V} (hψ : ∀ t, ρ t v = (ψ t : ℂ) • v)
    (hne : μ ≠ ψ) (hy : y ∉ Submodule.span ℂ {v})
    (hq : ∀ t, ρ t y - (μ t : ℂ) • y ∈ Submodule.span ℂ {v}) (hv : v ≠ 0) :
    ∃ z, z ≠ 0 ∧ ∀ t, ρ t z = (μ t : ℂ) • z :=
  _root_.UpperTheory.Reformulated.B.R4.lift_eigen ρ hψ hne hy hq hv

private theorem exists_eigenchars {T : Type} [CommGroup T] (d : ℕ) : ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ T V), Module.finrank ℂ V = d →
    ∃ E : Multiset (T →* ℂˣ), (∀ t, LinearMap.trace ℂ V (ρ t) = (E.map fun χ => (χ t : ℂ)).sum) ∧
      ∀ μ, μ ∈ E ↔ ∃ y, y ≠ 0 ∧ ∀ t, ρ t y = (μ t : ℂ) • y := by
  induction d with
  | zero =>
    intro V _ _ _ ρ h
    haveI : Subsingleton V := Module.finrank_zero_iff.1 h
    refine ⟨0, fun t => ?_, fun μ => ?_⟩
    · simp [Subsingleton.elim (ρ t) 0]
    · simp [Subsingleton.elim _ (0 : V)]
  | succ d ih =>
    intro V _ _ _ ρ h
    haveI : Nontrivial V := Module.finrank_pos_iff.1 (by rw [h]; exact d.succ_pos)
    obtain ⟨ψ, v, hv, hψ⟩ := GlobalTheory.exists_character_eigenvector_of_commute ℂ T V ρ fun a b => by
      rw [← map_mul, mul_comm, map_mul]
    have hst : ∀ g, Submodule.span ℂ {v} ≤ (Submodule.span ℂ {v}).comap (ρ g) := fun g => by
      rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Submodule.mem_comap, hψ]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
    have hd : Module.finrank ℂ (V ⧸ Submodule.span ℂ {v}) = d := by
      have := (Submodule.span ℂ {v}).finrank_quotient_add_finrank
      rw [finrank_span_singleton hv, h] at this
      omega
    obtain ⟨E, h1, h2⟩ := ih _ (ρ.quotient _ hst) hd
    refine ⟨ψ ::ₘ E, fun t => ?_, fun μ => ⟨fun hμ => ?_, ?_⟩⟩
    · rw [GlobalTheory.IwahoriTraceProof.trace_eq_add_quot (ρ t) hv (hψ t) (ρ.quotient _ hst t) fun _ => rfl, h1,
        Multiset.map_cons, Multiset.sum_cons]
    · by_cases hne : μ = ψ
      · exact ⟨v, hv, hne ▸ hψ⟩
      obtain ⟨q, hq0, hq⟩ := (h2 μ).1 ((Multiset.mem_cons.1 hμ).resolve_left hne)
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      refine lift_eigen ρ hψ hne (fun hy => hq0 ((Submodule.Quotient.mk_eq_zero _).2 hy)) (fun t => ?_) hv
      refine (Submodule.Quotient.eq _).1 ?_
      exact hq t
    · rintro ⟨y, hy, hμ⟩
      by_cases hne : μ = ψ
      · exact hne ▸ Multiset.mem_cons_self _ _
      refine Multiset.mem_cons_of_mem ((h2 μ).2 ⟨Submodule.Quotient.mk y, fun h0 => hne ?_, fun t => ?_⟩)
      · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 ((Submodule.Quotient.mk_eq_zero _).1 h0)
        refine MonoidHom.ext fun t => Units.ext ?_
        have h3 := hμ t
        rw [map_smul, hψ, smul_comm, ← sub_eq_zero, ← sub_smul] at h3
        rcases smul_eq_zero.1 h3 with h3 | h3
        · exact (sub_eq_zero.1 h3).symm
        · exact absurd h3 hy
      · exact congrArg (Submodule.Quotient.mk (p := Submodule.span ℂ {v})) (hμ t)

theorem UpperTheory.Gal.Join.traceExp :
    UpperTheory.Gal.Join.TraceExp := by
  intro T X _ _ _ ρ P _ hP
  let R : Representation ℂ T P :=
    { toFun := fun t => (ρ t).restrict (hP t)
      map_one' := by
        ext y
        simp
      map_mul' := fun a b => by
        ext y
        simp }
  obtain ⟨E, h1, h2⟩ := exists_eigenchars (T := T) _ P R rfl
  refine ⟨E, fun t => ?_, fun μ => ?_⟩
  · rw [trIn, dif_pos (hP t)]
    exact h1 t
  · rw [h2]
    constructor
    · rintro ⟨y, hy, h⟩
      exact ⟨y, y.2, fun h0 => hy (Subtype.ext h0), fun t => congrArg Subtype.val (h t)⟩
    · rintro ⟨y, hyP, hy, h⟩
      exact ⟨⟨y, hyP⟩, fun h0 => hy (congrArg Subtype.val h0), fun t => Subtype.ext (h t)⟩
