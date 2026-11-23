import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.OneAddPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VecPairApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameRelationCocycleSquareZeroInertiaStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedRepresentationKillsSmallSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevInductionGrowBoundOfPresentation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelaxedResidualSelmerMemUnrelaxed
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousAndResidualTrivComplexConj

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrimeUnr

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} {i : X.Tw}

theorem vanish (hT : TameQuotient) (_hl : 0 < nu X i) {M : ℕ} {L : Subgroup (GE N)} {p : PlE D.host}
    {d : GE N →* Multiplicative (ZMod (X.l i ^ M))} {σ γ : GE N} (hM : nu X i + 2 ≤ M) (hp : NewPl i M L p d σ γ)
    {R W : Type} [CommRing R] [AddCommGroup W] [Module R W] [TopologicalSpace W] [DiscreteTopology W]
    (ρ : Representation R (GE N) W) (h4 : ∀ m : W, (X.l i ^ (nu X i + 1)) • m = 0) (hρ : ∀ g ∈ DecV N p, ∀ m, ρ g m = m) (z : Z1 ρ)
    (hz : z.1 γ = 0) : ∀ τ ∈ Ine (F := D.host.E) (N.plOm.1 p), z.1 τ = 0 := by
  have := X.lPrime i
  obtain ⟨h0, -, hn, -, hd, hσ, hγ, hdγ⟩ := hp
  have h8 : normV p % (2 * X.l i ^ (nu X i + 1)) = 1 :=
    KStar.Tree.mod_two_mul_pow_of_le (X.lPrime i).out (by omega) hn
  exact (GlobalTheory.T.tame_relation_cocycle_squareZero_inertia hT D.host.E N.Om (X.l i) (N.plOm.1 p) p (N.plOm.2 p)
    (fun h => h0 p (Or.inl rfl) (X.twistExcludedPlaces_contains_residueChar i h)) (nu X i + 1) h8 M d γ σ (by omega) hd hγ hdγ hσ R W ρ 0 0 h4 (mul_zero _)
    (fun τ hτ m => by rw [mul_zero, zero_smul, add_zero]; exact hρ τ (Ine_le_Dec _ hτ) m)
    (fun m => by rw [zero_smul, add_zero]; exact hρ σ hσ.1 m) z).2 rfl hz

theorem selC_of_vanish : TameLocal → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), 0 < nu X i → ∀ (M : ℕ) (L : Subgroup (GE N)) (z : GE N) (p : PlE D.host) (d : GE N →* Multiplicative (ZMod (X.l i ^ M))) (σ γ : GE N), nu X i + 2 ≤ M → Small2 i s M L z → NewPl i M L p d σ γ → ∀ (A : Type) [CommRing A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ), Kills i A → AntiHom X.cc κ → (∀ g ∈ DecV N p, κ g = 1) → ∀ (Q Q' : Finset (PlE D.host)), (∀ v, v ∈ Q' ↔ v ∈ Q ∨ Over p v) → ∀ (Y : Type) [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y] (f : GE N → Fin D.R.r → Y), SelC bkP i s κ Y Q' f → (∀ b, f (two X γ b) = 0) → SelC bkP i s κ Y Q f := by
  intro hT D N X bkP i s hl M L z₀ p d σ γ hM hL hp A _ _ κ hK hκ hκp Q Q' hQ Y _ _ _ _ f hf hγ
  obtain ⟨z, rfl, hz⟩ := hf
  refine ⟨z, rfl, ?_⟩
  have h4 : ∀ m : Fin D.R.r → Y, (X.l i ^ (nu X i + 1)) • m = 0 := fun m => by
    have h1 := hK _ (GlobalTheory.Growth.sq_mem_idl (X := X) (i := i))
    rw [map_natCast] at h1
    rw [← Nat.cast_smul_eq_nsmul A]
    exact (congrArg (· • m) h1).trans (zero_smul _ _)
  have htr : ∀ g ∈ L, ∀ m, repOn (Tgl i s) κ Y g m = ((κ g : Aˣ) : A) • m := fun g hg =>
    (GlobalTheory.T.twisted_representation_kills_small_subgroup D N X i s hl M L z₀ (by omega) hL A κ _ hK (isDual_dualRep i s) Y g hg).1
  have hdec : DecV N p ≤ L := hp.2.2.2.1
  have a1 := vanish hT.1 hl hM hp (repOn (Tgl i s) κ Y) h4
    (fun g hg m => by rw [htr g (hdec hg), hκp g hg, Units.val_one, one_smul]) z (hγ false)
  have a2 := vanish hT.1 hl hM hp ((repOn (Tgl i s) κ Y).comp (cConj X)) h4
    (fun g hg m => by
      change repOn (Tgl i s) κ Y (cConj X g) m = m
      rw [htr _ ((hL.1.2.2.1 g _ (cConj_apply X g)).1 (hdec hg)), antiHom_cConj X hκ, hκp g hg, inv_one, Units.val_one,
        one_smul])
    ⟨fun g => z.1 (cConj X g), z.2.1.comp (GlobalTheory.ResConjTriv.continuous_cConj X), fun g h => by
      change z.1 (cConj X (g * h)) = _
      rw [map_mul]
      exact z.2.2 _ _⟩ (hγ true)
  refine (mem_Sel _ _ _ _ _).2 fun v => ?_
  have hv := (mem_Sel _ _ _ _ _).1 hz v
  refine GlobalTheory.Growth.mem_bkCond_of hv fun _ h3 => ?_
  by_cases h2 : v ∈ Spl i ∪ (Q' : Set (PlE D.host))
  · rcases h2 with h2 | h2
    · exact absurd (Or.inl h2) h3
    · rcases (hQ v).1 h2 with h5 | rfl | h5
      · exact absurd (Or.inr h5) h3
      · exact Or.inr (GlobalTheory.ResUnr.res_mem_unrAt _ z _ 0 fun τ hτ => by rw [a1 τ hτ, map_zero, sub_self])
      · exact Or.inr (GlobalTheory.ResUnr.res_mem_unrAt_of_conj X h5 _ z a2)
  · exact Or.inl h2

end GlobalTheory.NewPrimeUnr
