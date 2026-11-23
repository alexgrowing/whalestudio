import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HeckeLocalBlock
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalSatakeAlmostAll

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

section

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

private theorem stable_eq {ρ : Representation ℂ G V} (hi : ρ.IsIrreducible) (S : Submodule ℂ V)
    (hS : ∀ g, ∀ x ∈ S, ρ g x ∈ S) : S = ⊥ ∨ S = ⊤ := by
  let P : Subrepresentation ρ := ⟨S, fun g x hx => hS g x hx⟩
  exact (hi.eq_bot_or_eq_top P).imp (fun e => congrArg Subrepresentation.toSubmodule e)
    fun e => congrArg Subrepresentation.toSubmodule e

private theorem rank_le_aleph0_of_irred [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    {ρ : Representation ℂ G V} (hs : GlobalTheory.PRep.IsSmooth ρ) (hi : ρ.IsIrreducible) {v : V} (hv : v ≠ 0) :
    Module.rank ℂ V ≤ Cardinal.aleph0 := by
  rw [← rank_top]
  refine GlobalTheory.CompanionTheory.SatAe.rank_le_of_simple (⊤ : Submodule ℂ V) (fun g : G => ρ g)
    ((Submodule.ne_bot_iff _).2 ⟨v, trivial, hv⟩) (fun W _ hW => stable_eq hi W hW) fun x _ => ?_
  exact ⟨_, GlobalTheory.CompanionTheory.SatAe.countable_orbit ρ x (hs x), fun _ _ => trivial, fun g => Submodule.subset_span ⟨g, rfl⟩⟩

end

private theorem biSimple {E : Type} [Field E] [NumberField E] {a : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GL (Fin a) (Af E)) V} (hi : ρ.IsIrreducible) (w : Pl E) :
    GlobalTheory.CompanionTheory.SatAe.IsBiSimple (locOf ρ w) := by
  intro S h1 h2
  refine stable_eq hi S fun k x hx => ?_
  let g := Matrix.GeneralLinearGroup.map (pLoc E w) k
  have h3 := h2 (ρ (k * (locGL E a w g)⁻¹)) (fun g' => by
    change ρ _ * ρ _ = ρ _ * ρ _
    rw [← map_mul, ← map_mul, LocSph.comm_locGL w _ (by rw [map_mul, map_inv, pLoc_locGL, mul_inv_cancel])])
    _ (h1 g x hx)
  have h4 : ρ (k * (locGL E a w g)⁻¹) (locOf ρ w g x) = ρ k x := by
    change ρ _ (ρ _ x) = ρ k x
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
  rwa [h4] at h3

theorem UpperTheory.V.Cj.S.tauSat :
    UpperTheory.V.Cj.S.TauSat := by
  intro E _ _ _ a τ v hv
  haveI := GlobalTheory.CompanionTheory.SatAe.secondCountable_GL (E := E) (a := a)
  rcases τ with @⟨V, _, _, ρ, hs, hi⟩
  change V at v
  have hr := rank_le_aleph0_of_irred hs hi hv
  filter_upwards [LocSph.eventually_mem ((hs v).mem_nhds (by simp))] with w hw
  have hfix : v ∈ fixed (locOf ρ w) (KGL w a) := by
    refine GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_
    obtain ⟨g, rfl⟩ := hk
    exact hw g
  have hsl : GlobalTheory.PRep.IsSmooth (locOf ρ w) := fun x => (hs x).preimage (CuspSub.continuous_locGL w)
  obtain ⟨B, hB⟩ := GlobalTheory.CompanionTheory.SatAe.exists_hasSatGL_of_scalar (fun h hh => GlobalTheory.CompanionTheory.SatAe.exists_scalar hsl
    (SatCompare.isOpen_isCompact_KGL w a).2 (Final.GLintComm E w a) (Final.HeckeCommGL E w a ℂ) (biSimple hi w) hr h hh)
    ((Submodule.ne_bot_iff _).2 ⟨v, hfix, hv⟩)
  exact ⟨B, hB, hB.2 v hfix hv⟩
