import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VecPairApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousAlgebraMapPadicInt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RepOnEqOfEqOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatCastEqOneOfMod

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrime.LocInv

theorem tors_of_finite (A : Type) [CommRing A] [IsLocalRing A] [Finite A] (Y : Type) [AddCommGroup Y] [Module A Y] :
    Tors A Y := by
  intro b
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hn
  refine ⟨n, fun x hx => ?_⟩
  rw [hn] at hx
  rw [(Submodule.mem_bot _).1 hx, zero_smul]

theorem dual_eq_one {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X)
    (i : X.Tw) (s : X.Sig i) (h : IsotypicValuationAtRing bkP i s) {ρ : GE N →* GL (Fin D.R.r) (X.O0 i)} (hρ : IsDual i s ρ)
    (v : PlE D.host) (hl : v ∉ placesOver D.host.E (X.l i)) (hS : v ∉ Spl i) (σ : GE N)
    (hσ : σ ∈ Ine (F := D.host.E) (N.plOm.1 v)) : ρ σ = 1 := by
  have hvl : ((X.l i : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal := hl
  have h1 : cycZ D.host.E N.Om (X.l i) σ = 1 := by
    refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
    rw [cycZ_toZModPow_eq hvl (N.plOm.2 v) (q := 1) (fun x hx => by simpa using hσ.2 x hx) n]
    simp
  have h2 : eps0 X i σ = 1 := by
    rw [eps0, MonoidHom.comp_apply, h1, map_one]
  have h3 := GlobalTheory.SelFun.Colim.tgl_eq_one bkP i s h v hl hS _ (N.plOm.2 v) σ hσ
  apply Units.ext
  rw [hρ σ, Tdual, h2, ← Tgl_coe, h3]
  simp

theorem local_invariants_killed : TameLocal → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), 0 < nu X i → ∀ (M R n : ℕ) (d : PlE D.host → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) (A₀ : Finset (PlE D.host)) (L : Subgroup (GE N)) (z : GE N) (P : Fin R ⊕ Fin n → PlE D.host), 1 ≤ M → IsTameInertiaElementAtTwistPrime X i z → Small2 i s M L z → PiLocalization₂ i M d A₀ L z P → ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)) (t : A) (a : Fin R ⊕ Fin n → A), IsQ P Q → Setup bkP i s κ Q → Kills i A → IsDual i s ρ → IsChar i κ (fun q => a q * t) (fun q => d (P q)) → (∀ q, IsUnit (a (.inr q))) → ∀ (Y : Type) [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y], ∀ v, v ∈ Spl i ∨ v ∈ Q → ∀ m, (∀ g ∈ DecV N v, repOn ρ κ⁻¹ Y g m = m) → t • m = 0 := by
  intro _ D N X bkP i s _ M R n d A₀ L z P hM hz hL hSt A _ _ _ _ κ Q ρ t a hQ hSet _ hρ hch ha Y _ _ _ _ v hv m hm
  obtain ⟨hG, hloc, -, hκo, hκl, -, hQl, -⟩ := hSet
  have hκl' : ∀ g, ∃ k : ℕ, κ⁻¹ g ^ (X.l i ^ k) = 1 := fun g => by
    obtain ⟨k, hk⟩ := hκl g
    exact ⟨k, by rw [MonoidHom.inv_apply, inv_pow, hk, inv_one]⟩
  by_cases hS : v ∈ Spl i
  · have hker : (κ⁻¹).ker = κ.ker := by
      ext g
      simp [MonoidHom.mem_ker]
    have h0 := (GlobalTheory.PrimeToInertia.local_cohomology_vanishes D N X bkP i s hG v hS A κ⁻¹ (hker ▸ hκo) hκl' Y
      (tors_of_finite A Y) ρ (Or.inr hρ)).1
    have : m ∈ H0 ((repOn ρ κ⁻¹ Y).comp (DecV N v).subtype) := (mem_riemannRochSpace_iff_regularAt_everywhere _ _).2 fun g => hm g.1 g.2
    rw [h0, Submodule.mem_bot] at this
    rw [this, smul_zero]
  have hvQ : v ∈ Q := hv.resolve_left hS
  obtain ⟨q, hq⟩ := (hQ v).1 hvQ
  rcases q with b | q
  · have hA : ∀ w, Over (P (.inl b)) w → w ∉ X.S0 i ∧ normV w % X.l i = 1 := fun w hw => by
      obtain ⟨-, -, -, h0, -, hn⟩ := hSt.1.1 _ w hw
      exact ⟨h0, mod_l_eq_one i hM hn⟩
    have hp := hA v hq
    have hn := GlobalTheory.ScalarFrob.natCast_eq_one_of_mod i hp.2
    obtain ⟨σ, hσ⟩ := exists_isFrob (N.plOm.2 v)
    obtain ⟨c, c0, c1, hc⟩ := GlobalTheory.ScalarFrob.frob_scalar_place i s bkP hG hz hL.1 hA (hSt.2.1 b).2 hq hσ
    have hc' : ((ρ σ : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).map (IsLocalRing.residue _) =
        c⁻¹ • 1 := by
      rw [hρ, GlobalTheory.ScalarFrob.dual_of_scalar i s (GlobalTheory.ScalarFrob.eps_frob i hp.1 hn hσ) c0 hc]
    rw [GlobalTheory.ScalarFrob.eq_zero_of_scalar Fact.out (GlobalTheory.PrimeToInertia.l_mem i) ρ κ⁻¹ (hκl' σ) (inv_ne_one.2 c1) hc'
      (q := 1) Nat.cast_one m (by rw [one_smul]; exact hm σ hσ.1), smul_zero]
  · obtain ⟨γ, hγ, hd⟩ := (hSt.1.2.2 (.inr q)).2.2.2.2 v hq _ (N.plOm.2 v) (Multiplicative.ofAdd 1)
    have hρ1 := dual_eq_one bkP i s hG.1 hρ v (hQl v hvQ) hS γ hγ
    have hk := hch γ
    haveI : Fact (1 < X.l i ^ M) := ⟨Nat.one_lt_pow (by omega) (Fact.out : (X.l i).Prime).one_lt⟩
    rw [Finset.prod_eq_single (Sum.inr q)] at hk
    · have hd' : d (P (.inr q)) γ = Multiplicative.ofAdd 1 := hd
      simp only [hd', toAdd_ofAdd, ZMod.val_one, pow_one] at hk
      have hinv : ((κ⁻¹ γ : Aˣ) : A) = 1 + a (.inr q) * t := by
        rw [MonoidHom.inv_apply]
        exact Units.inv_eq_of_mul_eq_one_right hk
      have e := hm γ (Ine_le_Dec _ hγ)
      have e2 : repOn ρ κ⁻¹ Y γ m = (1 + a (.inr q) * t) • m := by
        simp [repOn, hρ1, matAct_one, ← hinv]
      rw [e2, add_smul, one_smul, add_eq_left, mul_smul] at e
      exact ((ha q).smul_eq_zero).1 e
    · intro q' _ hne
      have hn : ¬ Over (P q') v := fun h' => hne (hSt.1.2.1 _ _ (over_trans h' (over_symm hq)))
      have : d (P q') γ = 1 := (hSt.1.2.2 q').2.2.2.1 v hn _ (N.plOm.2 v) γ hγ
      simp [this]
    · simp

end GlobalTheory.NewPrime.LocInv
