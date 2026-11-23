import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VecPairApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FirstHalfLocalCohomologyVanishingOfLocalDualityT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOneOfMemProKer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedRepresentationKillsSmallSubgroupStatement

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.StageFirst

open IsLocalRing GlobalTheory.ScalarFrob GlobalTheory.PrimeToInertia GlobalTheory.AntiRamConj
open scoped Pointwise

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (i : X.Tw) (s : X.Sig i)

theorem isLocalHom_of_kills {A : Type} [CommRing A] [Nontrivial A] [Algebra (X.O0 i) A] (h : Kills i A) :
    IsLocalHom (algebraMap (X.O0 i) A) := by
  refine ⟨fun x hx => ?_⟩
  by_contra hn
  have hm : x ∈ maximalIdeal (X.O0 i) := hn
  have : CharZero (FractionRing (X.O0 i)) := (X.emb0 i).charZero_iff (X.emb0 i).injective |>.1 inferInstance
  have : CharZero (X.O0 i) := (algebraMap (X.O0 i) (FractionRing (X.O0 i))).charZero
  have hl : ((X.l i : ℕ) : X.O0 i) ^ nu X i ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : (X.l i).Prime).ne_zero)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (X.O0 i)
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl hϖ
  have h1 : ϖ ∣ x := by
    rwa [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
  have h2 : ((X.l i : ℕ) : X.O0 i) ^ nu X i ∣ x ^ n := by
    rw [hu, Units.mul_left_dvd]
    exact pow_dvd_pow_of_dvd h1 n
  have h3 := h (x ^ n * x) (Ideal.mul_mem_mul (Ideal.mem_span_singleton.2 h2) hm)
  rw [← pow_succ, map_pow] at h3
  exact (hx.pow _).ne_zero h3

theorem frob_scalar (bkP : BKPh X) (h : GalHyp bkP i s) {z : GE N} {L : Subgroup (GE N)} (hz : IsTameInertiaElementAtTwistPrime X i z)
    (hL : Small i s L z) {P : PlE D.host}
    (hA : ∀ v, Over P v → v ∉ X.S0 i ∧ (normV v : ResidueField (X.O0 i)) = 1)
    (hS : ∀ σ : GE N, IsFrob (N.plOm.1 P) (normV P) σ → ∃ g : GE N, g * σ * g⁻¹ * z⁻¹ ∈ L)
    {v : PlE D.host} (hv : Over P v) {σ : GE N}
    (hσ : IsFrob (N.plOm.1 v) (normV v) σ) : ∃ c : ResidueField (X.O0 i), c ≠ 0 ∧ c ≠ 1 ∧ resT i s σ = c • 1 := by
  obtain ⟨e, he, -, hu, -⟩ := GlobalTheory.T.tameInertiaElement_acts_by_scalar D N X bkP i s z h.1 hz
  have c0 : residue (X.O0 i) e ≠ 0 := (residue_ne_zero_iff_isUnit _).2 e.isUnit
  have c1 : residue (X.O0 i) e ≠ 1 := by
    rw [← residue_ne_zero_iff_isUnit, map_sub, map_one, sub_ne_zero] at hu
    exact hu
  have key : ∀ τ : GE N, IsFrob (N.plOm.1 P) (normV P) τ → resT i s τ = residue (X.O0 i) e • 1 := by
    intro τ hτ
    obtain ⟨g, hg⟩ := hS τ hτ
    have e1 : resT i s (g * τ * g⁻¹ * z⁻¹ * z) = residue (X.O0 i) e • 1 := by
      rw [map_mul, resT_apply, (hL.2.2.2.2 _ hg).1, one_mul, resT_apply, he]
      ext a b
      by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
    have e2 := conj_scalar _ e1 g⁻¹
    rwa [show g⁻¹ * (g * τ * g⁻¹ * z⁻¹ * z) * g⁻¹⁻¹ = τ by group] at e2
  have hp := hA v hv
  have hp0 := hA _ (over_refl P)
  rcases hv with rfl | hv
  · exact ⟨_, c0, c1, key σ hσ⟩
  · have ε := eps_frob i hp.1 hp.2 hσ
    obtain ⟨τ, g, hτ, rfl⟩ := exists_frob_of_conj X hv hσ
    have ε0 := eps_frob i hp0.1 hp0.2 hτ
    rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm] at ε
    refine ⟨_, inv_ne_zero c0, inv_ne_one.2 c1, conj_scalar _ (scalar_of_dual i s ε c0 ?_) g⟩
    obtain ⟨A, hA⟩ := h.2.2.1
    have e3 : ((((eps0 X i τ : (X.O0 i)ˣ) : X.O0 i) ^ D.R.t) • Tmat i s τ).map (residue (X.O0 i)) =
        residue (X.O0 i) e • 1 := by
      rw [← key τ hτ, resT_apply]
      ext a b
      simp [ε0]
    rw [hA τ _ (cConj_apply X τ), Matrix.map_mul, Matrix.map_mul, e3, mul_smul_comm, mul_one, smul_mul_assoc,
      ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]

theorem firstHalf : TameLocal → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → 0 < nu X i → ∀ (M R n : ℕ) (d : PlE D.host → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) (A₀ : Finset (PlE D.host)) (L : Subgroup (GE N)) (z : GE N) (P : Fin R ⊕ Fin n → PlE D.host), nu X i + 1 ≤ M → IsTameInertiaElementAtTwistPrime X i z → Small2 i s M L z → PiLocalization₂ i M d A₀ L z P → ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)), Kills i A → (∀ g, ∃ k : ℕ, κ g ^ (X.l i ^ k) = 1) → (ρ = Tgl i s ∨ IsDual i s ρ) → ∀ (Y : Type) [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y] (b : Fin R), (∀ v, Over (P (.inl b)) v → ∀ m, (∀ g ∈ DecV N v, repOn ρ κ Y g m = m) → m = 0) ∧ (AntiHom X.cc κ → (∀ τ ∈ Ine (F := D.host.E) (N.plOm.1 (P (.inl b))), κ τ = 1) → ∀ f : Z1 (repOn ρ κ Y), ∀ τ ∈ Ine (F := D.host.E) (N.plOm.1 (P (.inl b))), f.1 τ = 0 ∧ f.1 (cConj X τ) = 0) := by
  intro hT D N X bkP i s h hl2 M R n d A₀ L z P hM hz hL hP A _ _ _ _ κ ρ hK hκ hρ Y _ _ _ _ b
  have := isLocalHom_of_kills i hK
  have hA : ∀ v, Over (P (.inl b)) v → v ∉ X.S0 i ∧ (normV v : ResidueField (X.O0 i)) = 1 := fun v hv =>
    ⟨(hP.1.1 _ v hv).2.2.2.1, natCast_eq_one i (show 1 ≤ M by omega) (hP.1.1 _ v hv).2.2.2.2.2⟩
  have fix0 : ∀ v, Over (P (.inl b)) v → ∀ σ : GE N, IsFrob (N.plOm.1 v) (normV v) σ →
      ∀ m, repOn ρ κ Y σ m = m → m = 0 := by
    intro v hv σ hσ m hm
    obtain ⟨c, c0, c1, hc⟩ := frob_scalar i s bkP h hz hL.1 hA (hP.2.1 b).2 hv hσ
    obtain ⟨c', c1', hc'⟩ : ∃ c' : ResidueField (X.O0 i), c' ≠ 1 ∧
        ((ρ σ : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).map (residue _) = c' • 1 := by
      rcases hρ with rfl | hρ
      · exact ⟨c, c1, by rw [Tgl_coe, ← resT_apply, hc]⟩
      · exact ⟨c⁻¹, inv_ne_one.2 c1, by rw [hρ, dual_of_scalar i s (eps_frob i (hA v hv).1 (hA v hv).2 hσ) c0 hc]⟩
    exact eq_zero_of_scalar Fact.out (l_mem i) ρ κ (hκ σ) c1' hc' (q := 1) Nat.cast_one m (by rw [one_smul]; exact hm)
  have fix : ∀ v, Over (P (.inl b)) v → ∀ B : ValuationSubring N.Om, IsPlaceOver B v → ∀ σ : GE N, IsFrob B (normV v) σ →
      ∀ m, repOn ρ κ Y σ m = m → m = 0 := by
    intro v hv B hB σ hσ m hm
    obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (F := D.host.E) hB (N.plOm.2 v)
    have h3 := isFrob_smul hσ g
    rw [hg] at h3
    have h4 := fix0 v hv _ h3 (repOn ρ κ Y g m) (by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, map_mul, Module.End.mul_apply, hm])
    have h5 := congrArg (repOn ρ κ Y g⁻¹) h4
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, map_zero] at h5
  have van : ∀ v, Over (P (.inl b)) v → ∀ B : ValuationSubring N.Om, IsPlaceOver B v →
      (∀ τ ∈ Ine (F := D.host.E) B, κ τ = 1) → ∀ f : Z1 (repOn ρ κ Y), ∀ τ ∈ Ine (F := D.host.E) B, f.1 τ = 0 := by
    intro v hv B hB hκB f
    obtain ⟨γ, -, hγ⟩ := GlobalTheory.TameRead.exists_gen_read hT.1 D.host.E N.Om (X.l i) B v hB
      (fun h => (hA v hv).1 (X.twistExcludedPlaces_contains_residueChar i h))
    have h1 : ∀ m : Fin D.R.r → Y, (X.l i ^ (nu X i + 1)) • m = 0 := fun m => by
      have := hK ((X.l i : X.O0 i) ^ nu X i * (X.l i : X.O0 i))
        (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) (l_mem i))
      rw [map_mul, map_pow, map_natCast] at this
      rw [← Nat.cast_smul_eq_nsmul A, Nat.cast_pow, pow_succ, this, zero_smul]
    have h2 : normV v ≡ 1 [MOD X.l i ^ (nu X i + 1)] := by
      have hq := (hP.1.1 _ v hv).2.2.2.2.2
      have hd : X.l i ^ (nu X i + 1) ∣ 2 * X.l i ^ M := Dvd.dvd.mul_left (pow_dvd_pow _ hM) 2
      have h6 : normV v ≡ 1 [MOD 2 * X.l i ^ M] := by
        rw [← hq]
        exact (Nat.mod_modEq _ _).symm
      exact h6.of_dvd hd
    have h3 : ∀ σ ∈ Ine (F := D.host.E) B, ∀ m, repOn ρ κ Y σ m = m := by
      intro σ hσ m
      have hσL := (hP.2.1 b).1 v hv B hB hσ
      rcases hρ with rfl | hρ
      · rw [(GlobalTheory.T.twisted_representation_kills_small_subgroup D N X i s hl2 M L z hM hL A κ _ hK (isDual_dualRep i s) Y σ hσL).1, hκB σ hσ, Units.val_one,
          one_smul]
      · rw [(GlobalTheory.T.twisted_representation_kills_small_subgroup D N X i s hl2 M L z hM hL A κ _ hK hρ Y σ hσL).2.1, hκB σ hσ, Units.val_one, one_smul]
    obtain ⟨h4, h5⟩ := hγ A _ (repOn ρ κ Y) (nu X i + 1) h1 h2 h3 f
    obtain ⟨φ, hφ⟩ := exists_isFrob (F := D.host.E) hB
    exact h4 (fix v hv B hB φ hφ _ (h5 φ hφ))
  refine ⟨fun v hv m hm => ?_, fun hanti hκI f τ hτ => ⟨van _ (over_refl _) _ (N.plOm.2 _) hκI f τ hτ, ?_⟩⟩
  · obtain ⟨σ, hσ⟩ := exists_isFrob (N.plOm.2 v)
    exact fix0 v hv σ hσ m (hm σ hσ.1)
  · obtain ⟨v, hv⟩ := exists_isConjPl (P (.inl b))
    refine van v (Or.inr hv) _ (isPlaceOver_moveVal_cc X hv (N.plOm.2 _)) (fun σ hσ => ?_) f _ (cConj_mem_ine X hτ)
    have h1 := cConj_mem_ine X hσ
    have e : moveVal X.cc (moveVal X.cc (N.plOm.1 (P (.inl b)))) = N.plOm.1 (P (.inl b)) := by
      ext y
      rw [mem_moveVal, mem_moveVal, cc_symm, cc_symm, cc_cc]
    rw [e] at h1
    have h2 := hκI _ h1
    rwa [antiHom_cConj X hanti, inv_eq_one] at h2

end GlobalTheory.StageFirst
