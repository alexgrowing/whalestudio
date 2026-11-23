import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VecPairApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleUnramifiedOutsideVanishOnKernel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedRepresentationKillsSmallSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PairingEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumInvEqZeroOfUnramifiedCocyclePowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameCupProductInvariantUnramifiedHomStatement

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published
  GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate GlobalTheory.AntiRamConj GlobalTheory.UnramCocycle

namespace GlobalTheory.NewRecip

section Group

variable {Γ R M M' : Type} [Group Γ] [TopologicalSpace Γ] [CommRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [DiscreteTopology M] [AddCommGroup M'] [Module R M'] [TopologicalSpace M'] [DiscreteTopology M'] {n : ℕ}
  {ρ : Representation R Γ M} {ρ' : Representation R Γ M'} {χ : Γ →* (ZMod n)ˣ} {P : M →+ M' →+ ZMod n}

def cupZ (hc : ContAction ρ') (hP : ∀ g x y, P (ρ g x) (ρ' g y) = ((χ g : (ZMod n)ˣ) : ZMod n) * P x y)
    (x : Z1 ρ) (y : Z1 ρ') : Z2 (charRep χ) :=
  ⟨fun p => P (x.1 p.1) (ρ' p.1 (y.1 p.2)),
    (continuous_of_discreteTopology (f := fun q : M × M' => P q.1 q.2)).comp
      ((x.2.1.comp continuous_fst).prodMk (hc.comp (continuous_fst.prodMk (y.2.1.comp continuous_snd)))),
    fun g h k => by
      dsimp only
      rw [charRep_apply, ← hP, x.2.2 g h, y.2.2 h k, map_mul, Module.End.mul_apply]
      simp only [map_add, AddMonoidHom.add_apply]
      abel⟩

end Group

section General

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}

def locZ (A : ValuationSubring Ω) (w : Z2 (muRep F Ω l n)) : Z2 (muLoc F l n A) :=
  ⟨fun p => w.1 (p.1, p.2), w.2.1.comp (continuous_subtype_val.prodMap continuous_subtype_val),
    fun g h k => w.2.2 g h k⟩

omit [NumberField F] in
theorem conj_root {c : Ω ≃+* Ω} (hc : IsCMConjOm F Ω c) {ζ : Ω} (hζ : IsPrimitiveRoot ζ (l ^ n)) :
    c ζ = ζ ^ (-1 : ZMod (l ^ n)).val := by
  have hl : l ^ n ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
  haveI : NeZero (l ^ n) := ⟨hl⟩
  obtain ⟨j, hj⟩ := hc.1
  have h1 : c ζ * ζ = 1 := by
    apply j.injective
    have hn : ‖j ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hζ.pow_eq_one, map_one]) hl
    rw [map_mul, hj, map_one, Complex.conj_mul', hn]
    simp
  have h2 : ζ ^ (-1 : ZMod (l ^ n)).val * ζ = 1 := by
    rw [← pow_succ, hζ.pow_eq_one_iff_dvd, ← ZMod.natCast_eq_zero_iff]
    simp
  exact mul_right_cancel₀ (hζ.ne_zero hl) (h1.trans h2.symm)

theorem ine_le_of_normal [IsAlgClosure F Ω] {H : Subgroup (G F Ω)} (hH : H.Normal) {v : HeightOneSpectrum (𝓞 F)}
    {A B : ValuationSubring Ω} (hA : IsPlaceOver A v) (hB : IsPlaceOver B v) (h : Ine (F := F) A ≤ H) :
    Ine (F := F) B ≤ H := by
  intro τ hτ
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := F) hA hB
  have h1 := hH.conj_mem _ (h (conj_mem_ine_of_smul A g τ hτ)) g
  have e : g * (g⁻¹ * τ * g) * g⁻¹ = τ := by group
  rwa [e] at h1

theorem NS_le [IsAlgClosure F Ω] {H : Subgroup (G F Ω)} (hH : H.Normal) (hc : IsClosed (H : Set (G F Ω)))
    {S : Set (HeightOneSpectrum (𝓞 F))} (A : Formalism.GaloisCohomology.Places F Ω) (h : ∀ v ∉ S, Ine (F := F) (A.1 v) ≤ H) :
    NS Ω S ≤ H := by
  refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal fun τ hτ => ?_) hc
  simp only [Set.mem_iUnion] at hτ
  obtain ⟨v, hv, B, hB, hτ⟩ := hτ
  exact ine_le_of_normal hH (A.2 v) hB (h v hv) hτ

variable {R M M' : Type} [CommRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [DiscreteTopology M] [AddCommGroup M'] [Module R M'] [TopologicalSpace M'] [DiscreteTopology M']
  {ρ : Representation R (G F Ω) M} {ρ' : Representation R (G F Ω) M'} {P : M →+ M' →+ ZMod (l ^ n)}

omit [NumberField F] in

theorem loc_eq_zero (hc : ContAction ρ')
    (hP : ∀ g x y, P (ρ g x) (ρ' g y) = ((cycMod F Ω l n g : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) * P x y)
    (x : Z1 ρ) (y : Z1 ρ') (A : ValuationSubring Ω) (m : M') (hm : ∀ g ∈ Dec (F := F) A, y.1 g = ρ' g m - m) :
    (Submodule.Quotient.mk (locZ A (cupZ hc hP x y)) : H2 _) = 0 := by
  rw [Submodule.Quotient.mk_eq_zero]
  refine (separated_dvr_second_cohomology_mem _ _).2 ⟨fun g => -P (x.1 g) (ρ' g m), ?_, ?_⟩
  · exact ((continuous_of_discreteTopology (f := fun q : M × M' => -P q.1 q.2)).comp
      (x.2.1.prodMk (hc.comp (continuous_id.prodMk (continuous_const (y := m)))))).comp continuous_subtype_val
  · funext ⟨g, h⟩
    change ((cycMod F Ω l n g : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) * (-P (x.1 h) (ρ' h m)) -
      (-P (x.1 (g * h)) (ρ' (g * h) m)) + -P (x.1 g) (ρ' g m) = P (x.1 g) (ρ' g (y.1 h))
    rw [mul_neg, ← hP, hm h h.2, x.2.2, map_mul, Module.End.mul_apply]
    simp only [map_add, map_sub, AddMonoidHom.add_apply]
    abel

end General

section HidaSetting

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} {i : X.Tw}

theorem continuous_cConj : Continuous (cConj X) := by
  refine continuous_of_continuousAt_one (cConj X) ?_
  rw [ContinuousAt, map_one]
  intro U hU
  obtain ⟨L, hL, hLU⟩ := (krullTopology_mem_nhds_one_iff D.host.E N.Om U).1 hU
  exact Filter.mem_of_superset ((isOpen_comap_cConj X (IntermediateField.fixingSubgroup_isOpen L)).mem_nhds
    (Subgroup.one_mem _)) fun g hg => hLU hg

theorem spl_subset : Spl (X := X) i ⊆ ↑(X.S0 i) := by
  rintro v ⟨h | h, -⟩
  · obtain ⟨k, hk⟩ := Set.mem_iUnion.1 h
    exact X.placesOver_subset_exceptional i k hk
  · exact X.primes_subset_exceptional i h

theorem sq_eq_zero {A : Type} [CommRing A] [Algebra (X.O0 i) A] (hK : Kills i A) : ((X.l i ^ (nu X i + 1) : ℕ) : A) = 0 := by
  have h : ((X.l i : ℕ) : X.O0 i) ∈ IsLocalRing.maximalIdeal (X.O0 i) := fun h => by
    have h2 := h.map (algebraMap (X.O0 i) (X.O i))
    rw [map_natCast] at h2
    exact X.O_l i h2
  have := hK _ (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) h)
  rw [map_mul, map_pow, map_natCast] at this
  rw [Nat.cast_pow, pow_succ, this]

theorem local_pair (hT : TameLocal) {n : ℕ} (hn : 0 < n) {R W W' : Type} [CommRing R] [AddCommGroup W] [Module R W]
    [TopologicalSpace W] [DiscreteTopology W] [AddCommGroup W'] [Module R W'] [TopologicalSpace W'] [DiscreteTopology W']
    {ρ : Representation R (GE N) W} {ρ' : Representation R (GE N) W'} {B : W →+ W' →+ ZMod (X.l i ^ n)}
    (hc : ContAction ρ')
    (hB : ∀ g x y, B (ρ g x) (ρ' g y) =
      ((cycMod D.host.E N.Om (X.l i) n g : (ZMod (X.l i ^ n))ˣ) : ZMod (X.l i ^ n)) * B x y)
    (hW : ∀ m : W', X.l i ^ n • m = 0)
    {ζ : N.Om} (hζ : IsPrimitiveRoot ζ (X.l i ^ n)) {inv : InvFam D.host.E N.Om (X.l i) n}
    (hinv : IsLocalInvariants ζ inv) {P : PlE D.host} (hl : P ∉ placesOver D.host.E (X.l i))
    (hq : normV P ≡ 1 [MOD X.l i ^ n])
    (hP : ∀ g ∈ DecV N P, (∀ m, ρ g m = m) ∧ (∀ m, ρ' g m = m) ∧ cycMod D.host.E N.Om (X.l i) n g = 1)
    (hP' : ∀ g ∈ DecV N P, (∀ m, ρ (cConj X g) m = m) ∧ (∀ m, ρ' (cConj X g) m = m) ∧
      cycMod D.host.E N.Om (X.l i) n (cConj X g) = 1) {M : ℕ} (hM : 1 ≤ M)
    (d : GE N →* Multiplicative (ZMod (X.l i ^ M))) (hd : IsOpen (d.ker : Set (GE N))) {γ φ : GE N}
    (hγ : γ ∈ Ine (F := D.host.E) (N.plOm.1 P)) (hdγ : d γ = Multiplicative.ofAdd 1)
    (hφ : IsFrob (N.plOm.1 P) (normV P) φ) :
    ∃ u : (ZMod (X.l i ^ n))ˣ, ∀ (x : Z1 ρ) (y : Z1 ρ'),
      (∀ σ ∈ Ine (F := D.host.E) (N.plOm.1 P), y.1 σ = 0) →
      (∀ σ ∈ Ine (F := D.host.E) (moveVal X.cc (N.plOm.1 P)), y.1 σ = 0) →
      inv _ (Submodule.Quotient.mk (locZ (N.plOm.1 P) (cupZ hc hB x y))) = (u : ZMod (X.l i ^ n)) * B (x.1 γ) (y.1 φ) ∧
      inv _ (Submodule.Quotient.mk (locZ (moveVal X.cc (N.plOm.1 P)) (cupZ hc hB x y))) =
        -((u : ZMod (X.l i ^ n)) * B (x.1 (cConj X γ)) (y.1 (cConj X φ))) := by
  have hA := N.plOm.2 P
  obtain ⟨u, hu⟩ := GlobalTheory.T.tame_cupProduct_invariant_unramified_hom hT D.host.E N.Om (X.l i) n _ P hn hA hl hq (inv _) (hinv.1 _ _ hA).1 M hM d hd
    ⟨γ, Ine_le_Dec _ hγ⟩ ⟨φ, hφ.1⟩ hγ hdγ hφ
  refine ⟨u, fun x y hy hy' => ?_⟩
  have hμ : ∀ (g : DecV N P) m, muLoc D.host.E (X.l i) n (N.plOm.1 P) g m = m := fun g m => by
    change ((cycMod D.host.E N.Om (X.l i) n g : (ZMod (X.l i ^ n))ˣ) : ZMod (X.l i ^ n)) * m = m
    rw [(hP g g.2).2.2, Units.val_one, one_mul]
  have key := hu W W' B
  constructor
  · exact key (fun g => x.1 g) (fun g => y.1 g) hW (x.2.1.comp continuous_subtype_val) (y.2.1.comp continuous_subtype_val)
      (fun g h => by rw [Subgroup.coe_mul, x.2.2, (hP g g.2).1])
      (fun g h => by rw [Subgroup.coe_mul, y.2.2, (hP g g.2).2.1])
      (fun g hg => hy g hg) _ (fun g h => by
        change B (x.1 g) (ρ' g (y.1 h)) = B (x.1 g) (y.1 h)
        rw [(hP g g.2).2.1])
  · have hcc : Continuous ((cConj X).comp (DecV N P).subtype) := continuous_cConj.comp continuous_subtype_val
    let w : Z2 (muLoc D.host.E (X.l i) n (N.plOm.1 P)) :=
      compatiblePairCocycles2 (muRep D.host.E N.Om (X.l i) n) _ ((cConj X).comp (DecV N P).subtype) hcc LinearMap.id continuous_id
        (fun g m => by
          rw [hμ]
          change ((cycMod D.host.E N.Om (X.l i) n (cConj X g) : (ZMod (X.l i ^ n))ˣ) : ZMod (X.l i ^ n)) * m = m
          rw [(hP' g g.2).2.2, Units.val_one, one_mul]) (cupZ hc hB x y)
    have h1 := key (fun g => x.1 (cConj X g)) (fun g => y.1 (cConj X g)) hW (x.2.1.comp hcc) (y.2.1.comp hcc)
      (fun g h => by rw [Subgroup.coe_mul, map_mul, x.2.2, (hP' g g.2).1])
      (fun g h => by rw [Subgroup.coe_mul, map_mul, y.2.2, (hP' g g.2).2.1])
      (fun g hg => hy' _ (cConj_mem_ine X hg)) w (fun g h => by
        change B (x.1 (cConj X g)) (ρ' (cConj X g) (y.1 (cConj X h))) = B (x.1 (cConj X g)) (y.1 (cConj X h))
        rw [(hP' g g.2).2.1])
    have h2 := hinv.2 X.cc D.host.conj.toRingEquiv (cc_algebraMap X) (-1) (conj_root X.cc_cm hζ) _
      (moveVal X.cc (N.plOm.1 P)) P hA (fun x => by rw [mem_moveVal, RingEquiv.symm_apply_apply]) (-w)
      (locZ _ (cupZ hc hB x y)) (fun g h g' h' hg hh => by
        have e : ∀ {a b : GE N}, (∀ x, b (X.cc x) = X.cc (a x)) → b = cConj X a := fun hab => by
          ext x
          rw [cConj_apply, ← hab, RingEquiv.apply_symm_apply]
        change (cupZ hc hB x y).1 (g', h') = -1 * -(cupZ hc hB x y).1 (cConj X g, cConj X h)
        rw [e hg, e hh, neg_one_mul, neg_neg])
    rw [h2, Submodule.Quotient.mk_neg, map_neg, h1]

end HidaSetting

set_option maxHeartbeats 800000 in

theorem reciprocity : PoitouTateTotallyComplex → TameLocal → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), 0 < nu X i → ∀ (M : ℕ) (L : Subgroup (GE N)) (z : GE N) (p : PlE D.host) (d : GE N →* Multiplicative (ZMod (X.l i ^ M))) (σ γ : GE N), nu X i + 2 ≤ M → Small2 i s M L z → NewPl i M L p d σ γ → ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q Q' : Finset (PlE D.host)) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)), Setup bkP i s κ Q → Kills i A → IsDual i s ρ → AntiHom X.cc κ → (∀ g ∈ DecV N p, κ g = 1) → (∀ v, v ∈ Q' ↔ v ∈ Q ∨ Over p v) → ∀ (Y : Type) [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y] (Y' : Type) [AddCommGroup Y'] [Module A Y'] [TopologicalSpace Y'] [DiscreteTopology Y'] (β : Y →+ Y' →+ ZMod (X.l i ^ (nu X i + 1))), Bal A β → ∀ (y : Z1 (repOn ρ κ⁻¹ Y')) (f : GE N → Fin D.R.r → Y), DualSel bkP i s κ ρ β Q y → SelC bkP i s κ Y Q' f → vecPair D.R.r β (f γ) (y.1 σ) = vecPair D.R.r β (f (cConj X γ)) (y.1 (cConj X σ)) := by
  intro hPT hT D N X bkP i s hl2 M L z p d σ γ hM hS hp A _ _ _ _ κ Q Q' ρ hset hK hρ hanti hκ hQ' Y _ _ _ _ Y' _ _ _ _ β hβ
    y f hy hf
  classical
  obtain ⟨x, rfl, hx⟩ := hf
  obtain ⟨hp0, hsplit, hnorm, hDL, hd, hσ, hγ, hdγ⟩ := hp
  have hl : (X.l i).Prime := Fact.out
  haveI : NeZero (X.l i ^ (nu X i + 1)) := ⟨pow_ne_zero _ hl.ne_zero⟩
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  haveI : IsAlgClosed N.Om := IsAlgClosure.isAlgClosed D.host.E
  haveI : CharZero N.Om := charZero_of_injective_algebraMap (algebraMap D.host.E N.Om).injective
  haveI : NeZero ((X.l i : ℕ) : N.Om) := ⟨Nat.cast_ne_zero.mpr hl.ne_zero⟩
  haveI : NeZero ((X.l i ^ (nu X i + 1) : ℕ) : N.Om) := ⟨Nat.cast_ne_zero.mpr (pow_ne_zero _ hl.ne_zero)⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot N.Om (X.l i ^ (nu X i + 1))
  obtain ⟨inv, hinv, hsum⟩ := GlobalTheory.T.sum_local_inv_eq_zero_of_unramified_cocycle_pow hPT D.host.E N.Om (X.l i) (nu X i + 1) ζ (show 0 < nu X i + 1 by omega) hζ
  obtain ⟨hc, hc', hB, hunr⟩ := GlobalTheory.T.pairing_equivariant_alt D N X bkP i s A κ Q ρ hset hK hρ Y Y' β hβ
  have hS0 : ∀ v, Over p v → v ∉ placesOver D.host.E (X.l i) ∧ v ∉ Spl (X := X) i := fun v hv =>
    ⟨fun e => hp0 v hv (X.twistExcludedPlaces_contains_residueChar i e), fun e => hp0 v hv (spl_subset e)⟩
  have hq : normV p ≡ 1 [MOD X.l i ^ (nu X i + 1)] := by
    have h1 : normV p ≡ 1 [MOD 2 * X.l i ^ M] := by
      rw [← hnorm]
      exact (Nat.mod_modEq _ _).symm
    exact h1.of_dvd (Dvd.dvd.mul_left (pow_dvd_pow _ (by omega)) 2)
  let H : Subgroup (GE N) := L ⊓ κ.ker
  have hHn : H.Normal := haveI := hS.1.2.1; inferInstance
  have hHc : ∀ g ∈ H, cConj X g ∈ H := fun g hg =>
    ⟨(hS.1.2.2.1 g _ (cConj_apply X g)).1 hg.1, by
      change κ (cConj X g) = 1
      rw [antiHom_cConj X hanti, show κ g = 1 from hg.2, inv_one]⟩
  have hHt : ∀ g ∈ H, (∀ m, repOn (Tgl i s) κ Y g m = m) ∧ (∀ m, repOn ρ κ⁻¹ Y' g m = m) ∧
      cycMod D.host.E N.Om (X.l i) (nu X i + 1) g = 1 := fun g hg => by
    have h1 := GlobalTheory.T.twisted_representation_kills_small_subgroup D N X i s hl2 M L z (by omega) hS A κ ρ hK hρ Y g hg.1
    have h2 := GlobalTheory.T.twisted_representation_kills_small_subgroup D N X i s hl2 M L z (by omega) hS A κ⁻¹ ρ hK hρ Y' g hg.1
    have h3 : κ g = 1 := hg.2
    refine ⟨fun m => ?_, fun m => ?_, h1.2.2⟩
    · rw [h1.1, h3, Units.val_one, one_smul]
    · rw [h2.2.1, MonoidHom.inv_apply, h3, inv_one, Units.val_one, one_smul]
  have hDH : ∀ g ∈ DecV N p, g ∈ H := fun g hg => ⟨hDL hg, hκ g hg⟩
  obtain ⟨pb, hpb⟩ := exists_isConjPl p
  have hne : p ≠ pb := ne_of_isSplitPl hsplit hpb
  have hover : ∀ v, Over p v ↔ v = p ∨ v = pb := fun v =>
    or_congr_right ⟨fun e => isConjPl_unique e hpb, fun e => e ▸ hpb⟩
  have hIp : ∀ B, IsPlaceOver B p → Ine (F := D.host.E) B ≤ H := fun B hB =>
    ine_le_of_normal hHn (N.plOm.2 p) hB fun g hg => hDH g (Ine_le_Dec _ hg)
  have hI : ∀ v, Over p v → Ine (F := D.host.E) (N.plOm.1 v) ≤ H := fun v hv g hg => by
    rcases hv with rfl | hv
    · exact hIp _ (N.plOm.2 _) hg
    · have := hHc _ (hIp _ (isPlaceOver_moveVal_cc X (isConjPl_symm hv) (N.plOm.2 v)) (cConj_mem_ine X hg))
      rwa [cConj_cConj] at this
  have hyI : ∀ v, Over p v → ∀ B, IsPlaceOver B v → ∀ τ ∈ Ine (F := D.host.E) B, y.1 τ = 0 := fun v hv B hB τ hτ => by
    refine (ine_le_of_normal (kerSub_normal _ y) (N.plOm.2 v) hB (fun g hg => ?_) hτ).1
    have ht := (hHt g (hI v hv hg)).2.1
    refine ⟨?_, ht⟩
    by_cases e : v ∈ Q
    · obtain ⟨m, hm⟩ := hy.2.1 v (Or.inr e)
      rw [hm g (Ine_le_Dec _ hg), ht, sub_self]
    · exact hy.1 v (hS0 v hv).1 (hS0 v hv).2 e g hg
  obtain ⟨u, hu⟩ := local_pair hT (show 0 < nu X i + 1 by omega) hc' hB
    (fun m => by rw [← Nat.cast_smul_eq_nsmul A, sq_eq_zero hK, zero_smul]) hζ hinv (hS0 _ (over_refl p)).1 hq
    (fun g hg => hHt g (hDH g hg)) (fun g hg => hHt _ (hHc g (hDH g hg))) (by omega) d hd hγ hdγ hσ
  obtain ⟨e1, e2⟩ := hu x y (hyI _ (over_refl _) _ (N.plOm.2 _))
    (hyI _ (Or.inr hpb) _ (isPlaceOver_moveVal_cc X hpb (N.plOm.2 _)))
  let Av : PlE D.host → ValuationSubring N.Om := Function.update N.plOm.1 pb (moveVal X.cc (N.plOm.1 p))
  have hAb : Av pb = moveVal X.cc (N.plOm.1 p) := Function.update_self ..
  have hAv : ∀ v, v ≠ pb → Av v = N.plOm.1 v := fun v hv => Function.update_of_ne hv ..
  have hplace : ∀ v, IsPlaceOver (Av v) v := fun v => by
    by_cases hv : v = pb
    · rw [hv, hAb]
      exact isPlaceOver_moveVal_cc X hpb (N.plOm.2 _)
    · rw [hAv v hv]
      exact N.plOm.2 v
  let S : Finset (PlE D.host) := (X.S0 i).filter (fun v => v ∈ placesOver D.host.E (X.l i) ∨ v ∈ Spl (X := X) i) ∪ Q'
  have hmem : ∀ v, v ∈ S ↔ v ∈ placesOver D.host.E (X.l i) ∨ v ∈ Spl (X := X) i ∨ v ∈ Q' := fun v => by
    rw [Finset.mem_union, Finset.mem_filter, ← or_assoc]
    exact or_congr_left ⟨fun e => e.2, fun e => ⟨e.elim (fun e => X.twistExcludedPlaces_contains_residueChar i e) fun e => spl_subset e, e⟩⟩
  have hout : ∀ v ∉ (S : Set (PlE D.host)), v ∉ placesOver D.host.E (X.l i) ∧ v ∉ Spl (X := X) i ∧ v ∉ Q' := fun v hv => by
    simpa only [Finset.mem_coe, hmem, not_or] using hv
  have houtQ : ∀ v ∉ (S : Set (PlE D.host)), v ∉ Q := fun v hv e => (hout v hv).2.2 ((hQ' v).2 (Or.inl e))
  have hxloc := (mem_Sel _ _ _ _ _).1 hx
  have hxN := NS_le (S := S) (kerSub_normal _ x) (kerSub_isClosed _ hc x) N.plOm fun v hv τ hτ => by
    have ht := (hunr v (hout v hv).1 (hout v hv).2.1 (houtQ v hv) _ (N.plOm.2 v) τ hτ).1
    refine ⟨?_, fun m => by rw [ht, Module.End.one_apply]⟩
    have h := hxloc v
    unfold Formalism.GaloisCohomology.bkCond at h
    rw [if_neg (show ¬ ((X.l i : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal from (hout v hv).1),
      if_neg (fun e => e.elim (hout v hv).2.1 (hout v hv).2.2)] at h
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 h)
    have h3 : x.1 τ = repOn (Tgl i s) κ Y τ m - m := hm ⟨⟨τ, Ine_le_Dec _ hτ⟩, hτ⟩
    rw [h3, ht, Module.End.one_apply, sub_self]
  have hyN := NS_le (S := S) (kerSub_normal _ y) (kerSub_isClosed _ hc' y) N.plOm fun v hv τ hτ =>
    ⟨hy.1 v (hout v hv).1 (hout v hv).2.1 (houtQ v hv) τ hτ, fun m => by
      rw [(hunr v (hout v hv).1 (hout v hv).2.1 (houtQ v hv) _ (N.plOm.2 v) τ hτ).2, Module.End.one_apply]⟩
  let t : ValuationSubring N.Om → ZMod (X.l i ^ (nu X i + 1)) := fun B =>
    inv B (Submodule.Quotient.mk (locZ B (cupZ hc' hB x y)))
  have h0 : ∑ v ∈ S, t (Av v) = 0 :=
    hsum S (fun v hv => (hmem v).2 (Or.inl hv)) Av hplace (cupZ hc' hB x y) (fun g k n hn n' hn' => by
      change vecPair D.R.r β (x.1 (g * n)) (repOn ρ κ⁻¹ Y' (g * n) (y.1 (k * n'))) =
        vecPair D.R.r β (x.1 g) (repOn ρ κ⁻¹ Y' g (y.1 k))
      rw [x.2.2, y.2.2, (hxN hn).1, (hyN hn').1, map_zero, map_zero, add_zero, add_zero, map_mul,
        Module.End.mul_apply, (hyN hn).2]) (fun v => locZ (Av v) (cupZ hc' hB x y)) fun _ _ _ => rfl
  have h1 : ∑ v ∈ S, t (Av v) = t (Av p) + t (Av pb) := by
    refine Finset.sum_eq_add_of_mem p pb ((hmem _).2 (Or.inr (Or.inr ((hQ' _).2 (Or.inr (over_refl _))))))
      ((hmem _).2 (Or.inr (Or.inr ((hQ' _).2 (Or.inr (Or.inr hpb)))))) hne fun v hv hv' => ?_
    rw [hAv v hv'.2]
    have : (Submodule.Quotient.mk (locZ (N.plOm.1 v) (cupZ hc' hB x y)) : H2 _) = 0 := by
      by_cases e : v ∈ placesOver D.host.E (X.l i)
      · have h := hxloc v
        unfold Formalism.GaloisCohomology.bkCond at h
        rw [if_pos (show ((X.l i : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal from e)] at h
        obtain ⟨c, hc1, hc2⟩ := hy.2.2 v e (restrictCocycles1 _ _ continuous_subtype_val x) h
        rw [Submodule.Quotient.mk_eq_zero]
        refine (separated_dvr_second_cohomology_mem _ _).2 ⟨c, hc1.continuous, ?_⟩
        funext ⟨g, h⟩
        exact (hc2 g h).symm
      · obtain ⟨m, hm⟩ := hy.2.1 v (by
          rcases (hmem v).1 hv with e' | e' | e'
          · exact absurd e' e
          · exact Or.inl e'
          · exact Or.inr (((hQ' v).1 e').resolve_right fun o => ((hover v).1 o).elim hv'.1 hv'.2))
        exact loc_eq_zero hc' hB x y _ m hm
    change inv _ _ = 0
    rw [this, map_zero]
  rw [h0, hAb, hAv p hne] at h1
  simp only [t] at h1
  rw [e1, e2, ← sub_eq_add_neg, ← mul_sub, eq_comm, Units.mul_right_eq_zero, sub_eq_zero] at h1
  exact h1

end GlobalTheory.NewRecip
