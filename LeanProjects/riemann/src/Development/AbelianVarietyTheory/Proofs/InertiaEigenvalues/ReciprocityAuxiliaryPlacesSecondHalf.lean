import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDualDualRep
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousAlgebraMapPadicInt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceOverMoveValCc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TamePairingStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvCupPairingOfInvCupCharactersStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumInvEqZeroOfUnramifiedCocycleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleUnramifiedOutsideVanishOnKernelStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActsTriviallyResidualOfComplexConjugateStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalCupPairingReducedCocyclesStatement

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published
  GlobalTheory.Published.PoitouTate GlobalTheory.ResSel GlobalTheory.PrimeToInertia GlobalTheory.TwistDet GlobalTheory.AntiRamConj

namespace GlobalTheory.ResRecip

section General

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime]

def locZ (A : ValuationSubring Ω) (w : Z2 (muRep F Ω l 1)) : Z2 (muLoc F l 1 A) :=
  ⟨fun p => w.1 (p.1, p.2), w.2.1.comp (continuous_subtype_val.prodMap continuous_subtype_val),
    fun g h k => w.2.2 g h k⟩

theorem mem_NS {S : Set (HeightOneSpectrum (𝓞 F))} {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) {A : ValuationSubring Ω}
    (hA : IsPlaceOver A v) {σ : G F Ω} (hσ : σ ∈ Ine (F := F) A) : σ ∈ NS Ω S := by
  apply Subgroup.le_topologicalClosure
  apply Subgroup.subset_normalClosure
  simp only [Set.mem_iUnion]
  exact ⟨v, hv, A, hA, hσ⟩

omit [NumberField F] in
theorem conj_root {c : Ω ≃+* Ω} (hc : IsCMConjOm F Ω c) {ζ : Ω} (hζ : IsPrimitiveRoot ζ (l ^ 1)) :
    c ζ = ζ ^ (-1 : ZMod (l ^ 1)).val := by
  have hl : l ^ 1 ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
  haveI : NeZero (l ^ 1) := ⟨hl⟩
  obtain ⟨j, hj⟩ := hc.1
  have h1 : c ζ * ζ = 1 := by
    apply j.injective
    have hn : ‖j ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hζ.pow_eq_one, map_one]) hl
    rw [map_mul, hj, map_one, Complex.conj_mul', hn]
    simp
  have h2 : ζ ^ (-1 : ZMod (l ^ 1)).val * ζ = 1 := by
    rw [← pow_succ, hζ.pow_eq_one_iff_dvd, ← ZMod.natCast_eq_zero_iff]
    simp
  exact mul_right_cancel₀ (hζ.ne_zero hl) (h1.trans h2.symm)

theorem eq_zero_of_forall_dual {n : ℕ} [Fact n.Prime] {K : Type} [AddCommGroup K] [Module (ZMod n) K] (k : K)
    (h : ∀ lam : K →+ ZMod n, lam k = 0) : k = 0 :=
  (Module.forall_dual_apply_eq_zero_iff (ZMod n) k).1 fun φ => h φ.toAddMonoidHom

theorem eq_zero_of_forall_additive {K : Type} [AddCommGroup K] (hK : ∀ k : K, l • k = 0) (k : K)
    (h : ∀ lam : K →+ ZMod (l ^ 1), lam k = 0) : k = 0 :=
  haveI : Fact (l ^ 1).Prime := ⟨by rw [pow_one]; exact Fact.out⟩
  @eq_zero_of_forall_dual (l ^ 1) _ K _ (AddCommGroup.zmodModule (by simpa using hK)) k h

end General

section HidaSetting

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} {i : X.Tw} {s : X.Sig i}
  {K : Type} [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K]
  {ρ : GE N →* GL (Fin D.R.r) (X.O0 i)}

omit [TopologicalSpace K] [DiscreteTopology K] in
theorem l_eq_zero (hK : IsRes i K) : ((X.l i : ℕ) : K) = 0 := by
  rw [← map_natCast (algebraMap (X.O0 i) K)]
  exact hK _ (l_mem i)

omit [TopologicalSpace K] [DiscreteTopology K] in
theorem isLocalHom_of_isRes (hK : IsRes i K) : IsLocalHom (algebraMap (X.O0 i) K) :=
  ⟨fun a ha => by
    by_contra h
    exact ha.ne_zero (hK a h)⟩

theorem tors_field (K : Type) [Field K] : Tors K K := fun b => ⟨1, fun x hx => by
  rw [pow_one, IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at hx
  rw [hx, zero_smul]⟩

omit [TopologicalSpace K] [DiscreteTopology K] in
theorem eps_eq (hK : IsRes i K) (g : GE N) : algebraMap (X.O0 i) K ((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) =
    ((((cycMod D.host.E N.Om (X.l i) 1 g : (ZMod (X.l i ^ 1))ˣ) : ZMod (X.l i ^ 1)).val : ℕ) : K) := by
  haveI : NeZero (X.l i ^ 1) := ⟨pow_ne_zero _ (Fact.out : (X.l i).Prime).ne_zero⟩
  set u : ℤ_[X.l i] := ((cycZ D.host.E N.Om (X.l i) g : ℤ_[X.l i]ˣ) : ℤ_[X.l i])
  change algebraMap (X.O0 i) K (algebraMap ℤ_[X.l i] (X.O0 i) u) = (((PadicInt.toZModPow 1 u).val : ℕ) : K)
  have h : u - (((PadicInt.toZModPow 1 u).val : ℕ) : ℤ_[X.l i]) ∈ RingHom.ker (PadicInt.toZModPow 1) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at h
  obtain ⟨c, hc⟩ := h
  have h2 := congrArg (fun t => algebraMap (X.O0 i) K (algebraMap ℤ_[X.l i] (X.O0 i) t)) hc
  simp only [map_sub, map_natCast, map_mul, pow_one, l_eq_zero hK, zero_mul] at h2
  exact sub_eq_zero.1 h2

theorem lam_natCast_mul {n : ℕ} [NeZero n] {K : Type} [Ring K] (lam : K →+ ZMod n) (c : ZMod n) (k : K) :
    lam ((c.val : K) * k) = c * lam k := by
  rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val]

omit [TopologicalSpace K] [DiscreteTopology K] in
theorem red_apply (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)) (g : GE N) (m : Fin D.R.r → K) :
    red i K ρ g m = (((ρ g : GL (Fin D.R.r) (X.O0 i)) : Matrix _ _ (X.O0 i)).map (algebraMap (X.O0 i) K)).mulVec m := by
  funext a
  simp [repOn, matAct, Matrix.mulVec, dotProduct]

omit [TopologicalSpace K] [DiscreteTopology K] in
theorem red_dot (hρ : IsDual i s ρ) (g : GE N) (a b : Fin D.R.r → K) :
    red i K (Tgl i s) g a ⬝ᵥ red i K ρ g b = algebraMap (X.O0 i) K ((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) * (a ⬝ᵥ b) := by
  have h3 : IsUnit (Tmat i s g).det := by
    rw [← Tgl_coe]; exact Matrix.isUnits_det_units _
  have h4 : ((Tmat i s g)⁻¹).map (algebraMap (X.O0 i) K) * (Tmat i s g).map (algebraMap (X.O0 i) K) = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ h3, Matrix.map_one _ (map_zero _) (map_one _)]
  have h5 : (Tdual i s g).map (algebraMap (X.O0 i) K) = algebraMap (X.O0 i) K ((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) •
      (((Tmat i s g)⁻¹).map (algebraMap (X.O0 i) K)).transpose := by
    ext a b
    simp [Tdual]
  rw [red_apply, red_apply, hρ, Tgl_coe, h5, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, Matrix.mulVec_mulVec, h4, Matrix.one_mulVec]

theorem contAction_red (hK : IsRes i K) (hρ : ρ = Tgl i s ∨ IsDual i s ρ) : ContAction (red i K ρ) := by
  haveI := isLocalHom_of_isRes hK
  refine contAction_repOn (X.twistBaseCoefficientRing_isAdic i) ρ ?_ 1 (by rw [MonoidHom.ker_one]; exact isOpen_univ) (tors_field K)
  rcases hρ with rfl | hρ
  · simp_rw [Tgl_coe]; exact continuous_Tmat i s
  · simp_rw [hρ _]; exact continuous_Tdual i s

def cupZ (hK : IsRes i K) (hρ : IsDual i s ρ) (lam : K →+ ZMod (X.l i ^ 1)) (x : Z1 (red i K (Tgl i s)))
    (y : Z1 (red i K ρ)) : Z2 (muRep D.host.E N.Om (X.l i) 1) :=
  ⟨fun p => lam (x.1 p.1 ⬝ᵥ red i K ρ p.1 (y.1 p.2)),
    (continuous_of_discreteTopology (f := fun q : (Fin D.R.r → K) × (Fin D.R.r → K) => lam (q.1 ⬝ᵥ q.2))).comp
      ((x.2.1.comp continuous_fst).prodMk
        ((contAction_red hK (Or.inr hρ)).comp (continuous_fst.prodMk (y.2.1.comp continuous_snd)))),
    fun g h k => by
      haveI : NeZero (X.l i ^ 1) := ⟨pow_ne_zero _ (Fact.out : (X.l i).Prime).ne_zero⟩
      dsimp only
      rw [charRep_apply, ← lam_natCast_mul, ← eps_eq hK, ← red_dot hρ, x.2.2 g h, y.2.2 h k, map_mul,
        Module.End.mul_apply]
      simp only [map_add, dotProduct_add, add_dotProduct]
      abel⟩

omit [TopologicalSpace K] [DiscreteTopology K] in
theorem map_eq_one_of_residue (hK : IsRes i K) {M : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)}
    (h : M.map (IsLocalRing.residue (X.O0 i)) = 1) : M.map (algebraMap (X.O0 i) K) = 1 := by
  ext a b
  have h1 : IsLocalRing.residue (X.O0 i) (M a b - (1 : Matrix _ _ (X.O0 i)) a b) = 0 := by
    have := congrFun (congrFun h a) b
    rw [Matrix.map_apply] at this
    rw [map_sub, this]
    by_cases e : a = b <;> simp [Matrix.one_apply, e]
  have h2 := hK _ ((IsLocalRing.residue_eq_zero_iff _).1 h1)
  rw [map_sub, sub_eq_zero] at h2
  rw [Matrix.map_apply, h2]
  by_cases e : a = b <;> simp [Matrix.one_apply, e]

omit [TopologicalSpace K] [DiscreteTopology K] in
theorem red_T_of_resTriv (hK : IsRes i K) {g : GE N} (hg : ResTriv i s g) (m : Fin D.R.r → K) :
    red i K (Tgl i s) g m = m := by
  rw [red_apply, Tgl_coe, map_eq_one_of_residue hK hg.1, Matrix.one_mulVec]

omit [TopologicalSpace K] [DiscreteTopology K] in
theorem eps_of_resTriv (hK : IsRes i K) {g : GE N} (hg : ResTriv i s g) :
    algebraMap (X.O0 i) K ((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) = 1 := by
  have h := hK (((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) - 1) (by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hg.2, map_one, sub_self])
  rwa [map_sub, map_one, sub_eq_zero] at h

omit [TopologicalSpace K] [DiscreteTopology K] in
theorem red_dual_of_resTriv (hK : IsRes i K) (hρ : IsDual i s ρ) {g : GE N} (hg : ResTriv i s g) (m : Fin D.R.r → K) :
    red i K ρ g m = m := by
  funext a
  have h := red_dot (K := K) hρ g (Pi.single a 1) m
  rw [red_T_of_resTriv hK hg, eps_of_resTriv hK hg, one_mul, single_dotProduct, single_dotProduct] at h
  simpa using h

omit [TopologicalSpace K] [DiscreteTopology K] in
theorem cycMod_of_resTriv (hK : IsRes i K) {g : GE N} (hg : ResTriv i s g) : cycMod D.host.E N.Om (X.l i) 1 g = 1 := by
  have hl : (X.l i).Prime := Fact.out
  haveI : NeZero (X.l i ^ 1) := ⟨pow_ne_zero _ hl.ne_zero⟩
  haveI : CharP K (X.l i ^ 1) := by
    rw [pow_one]; exact (CharP.charP_iff_prime_eq_zero hl).2 (l_eq_zero hK)
  have h := eps_eq hK g
  rw [eps_of_resTriv hK hg, ← Nat.cast_one, CharP.natCast_eq_natCast K (X.l i ^ 1),
    ← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val, Nat.cast_one] at h
  exact Units.ext h.symm

theorem resTriv_of_inertia {bkP : BKPh X} (h : GalHyp bkP i s) {v : PlE D.host} (hv : v ∉ placesOver D.host.E (X.l i))
    (hv' : v ∉ Spl (X := X) i) {B : ValuationSubring N.Om} (hB : IsPlaceOver B v) {σ : GE N}
    (hσ : σ ∈ Ine (F := D.host.E) B) : ResTriv i s σ := by
  have hg : ∀ k, v ∉ placesOver D.host.E (D.host.g k) := fun k hk => hv' ⟨Or.inl (Set.mem_iUnion.2 ⟨k, hk⟩), hv⟩
  have hp : v ∉ X.pD i := fun hp => hv' ⟨Or.inr hp, hv⟩
  have h1 : cycZ D.host.E N.Om (X.l i) σ = 1 := by
    refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
    rw [cycZ_toZModPow_eq hv hB (q := 1) (fun x hx => by simpa using hσ.2 x hx) n]
    simp
  constructor
  · rw [Tmat, h.1.1 v hv hg B hB σ hσ, chiS, X.twistCharacterFamily_unramified i _ _ v hv hg hp B hB σ hσ]
    simp
  · rw [eps0, MonoidHom.comp_apply, h1]
    simp

theorem loc_eq_zero_of_subsingleton (hK : IsRes i K) (hρ : IsDual i s ρ) (lam : K →+ ZMod (X.l i ^ 1))
    (x : Z1 (red i K (Tgl i s))) (y : Z1 (red i K ρ)) (v : PlE D.host)
    (h : Subsingleton (H1 ((red i K (Tgl i s)).comp (DecV N v).subtype))) :
    (Submodule.Quotient.mk (locZ (N.plOm.1 v) (cupZ hK hρ lam x y)) : H2 _) = 0 := by
  haveI : NeZero (X.l i ^ 1) := ⟨pow_ne_zero _ (Fact.out : (X.l i).Prime).ne_zero⟩
  have h1 : (Submodule.Quotient.mk (restrictCocycles1 _ (DecV N v).subtype continuous_subtype_val x) :
    H1 ((red i K (Tgl i s)).comp (DecV N v).subtype)) = 0 := Subsingleton.elim _ _
  rw [Submodule.Quotient.mk_eq_zero] at h1 ⊢
  obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 h1
  refine (separated_dvr_second_cohomology_mem _ _).2 ⟨fun g => lam (m ⬝ᵥ y.1 g),
    (continuous_of_discreteTopology (f := fun q : Fin D.R.r → K => lam (m ⬝ᵥ q))).comp
      (y.2.1.comp continuous_subtype_val), ?_⟩
  funext ⟨g, h⟩
  have e : x.1 g = red i K (Tgl i s) g m - m := hm g
  change ((cycMod D.host.E N.Om (X.l i) 1 g : (ZMod (X.l i ^ 1))ˣ) : ZMod (X.l i ^ 1)) * lam (m ⬝ᵥ y.1 h) -
    lam (m ⬝ᵥ y.1 (g * h)) + lam (m ⬝ᵥ y.1 g) = lam (x.1 g ⬝ᵥ red i K ρ g (y.1 h))
  rw [← lam_natCast_mul, ← eps_eq hK, ← red_dot hρ, e, y.2.2]
  simp only [map_add, map_sub, dotProduct_add, sub_dotProduct]
  abel

theorem continuous_cConj : Continuous (cConj X) := by
  refine continuous_of_continuousAt_one (cConj X) ?_
  rw [ContinuousAt, map_one]
  intro U hU
  obtain ⟨L, hL, hLU⟩ := (krullTopology_mem_nhds_one_iff D.host.E N.Om U).1 hU
  exact Filter.mem_of_superset ((isOpen_comap_cConj X (IntermediateField.fixingSubgroup_isOpen L)).mem_nhds
    (Subgroup.one_mem _)) fun g hg => hLU hg

theorem local_pair (hT : TameLocal) {bkP : BKPh X} (h : GalHyp bkP i s) (hK : IsRes i K) (hρ : IsDual i s ρ)
    {ζ : N.Om} (hζ : IsPrimitiveRoot ζ (X.l i ^ 1)) {inv : InvFam D.host.E N.Om (X.l i) 1}
    (hinv : IsLocalInvariants ζ inv) {P : PlE D.host} (hl : P ∉ placesOver D.host.E (X.l i))
    (hq : normV P ≡ 1 [MOD X.l i ^ 1]) (hP : ∀ g ∈ DecV N P, ResTriv i s g) {M : ℕ} (hM : 1 ≤ M)
    (d : GE N →* Multiplicative (ZMod (X.l i ^ M))) (hd : IsOpen (d.ker : Set (GE N))) {γ φ : GE N}
    (hγ : γ ∈ Ine (F := D.host.E) (N.plOm.1 P)) (hdγ : d γ = Multiplicative.ofAdd 1)
    (hφ : IsFrob (N.plOm.1 P) (normV P) φ) :
    ∃ u : (ZMod (X.l i ^ 1))ˣ, ∀ (lam : K →+ ZMod (X.l i ^ 1)) (x : Z1 (red i K (Tgl i s))) (y : Z1 (red i K ρ)),
      (∀ σ ∈ Ine (F := D.host.E) (N.plOm.1 P), y.1 σ = 0) →
      (∀ σ ∈ Ine (F := D.host.E) (moveVal X.cc (N.plOm.1 P)), y.1 σ = 0) →
      inv _ (Submodule.Quotient.mk (locZ (N.plOm.1 P) (cupZ hK hρ lam x y))) = (u : ZMod (X.l i ^ 1)) * lam (x.1 γ ⬝ᵥ y.1 φ) ∧
      inv _ (Submodule.Quotient.mk (locZ (moveVal X.cc (N.plOm.1 P)) (cupZ hK hρ lam x y))) =
        -((u : ZMod (X.l i ^ 1)) * lam (x.1 (cConj X γ) ⬝ᵥ y.1 (cConj X φ))) := by
  have hA := N.plOm.2 P
  haveI : IsGalois D.host.E N.Om := {}
  haveI : CompactSpace (DecV N P) := isCompact_iff_compactSpace.1 (isClosed_Dec _).isCompact
  have hcyc : ∀ g : DecV N P, cycMod D.host.E N.Om (X.l i) 1 g = 1 := fun g => cycMod_of_resTriv hK (hP g g.2)
  have hP' : ∀ g : DecV N P, ResTriv i s (cConj X g) := fun g =>
    GlobalTheory.T.actsTriviallyResidual_of_complexConjugate D N X i s h.2.2.1 g _ (cConj_apply X g) (hP g g.2)
  obtain ⟨u, hu⟩ := GlobalTheory.T.tame_pairing_statement hT D.host.E N.Om (X.l i) _ P hA hl hq hcyc (inv _) (hinv.1 _ _ hA).1 M hM d hd
    ⟨γ, Ine_le_Dec _ hγ⟩ ⟨φ, hφ.1⟩ hγ hdγ hφ
  refine ⟨u, fun lam x y hy hy' => ?_⟩
  have hμ : ∀ (g : DecV N P) m, muLoc D.host.E (X.l i) 1 (N.plOm.1 P) g m = m := fun g m => by
    change ((cycMod D.host.E N.Om (X.l i) 1 g : (ZMod (X.l i ^ 1))ˣ) : ZMod (X.l i ^ 1)) * m = m
    rw [hcyc, Units.val_one, one_mul]
  have key := GlobalTheory.T.inv_cup_pairing_of_inv_cup_characters_alt (DecV N P) (X.l i) _ hμ (inv _) _ u _ _ hu (Fin D.R.r → K) (Fin D.R.r → K)
    (fun m => by rw [← Nat.cast_smul_eq_nsmul K, l_eq_zero hK, zero_smul])
    ((LinearMap.toAddMonoidHom'.comp (dotProductBilin K K).toAddMonoidHom).compr₂ lam)
  constructor
  · exact key (fun g => x.1 g) (fun g => y.1 g) (x.2.1.comp continuous_subtype_val) (y.2.1.comp continuous_subtype_val)
      (fun g h => by rw [Subgroup.coe_mul, x.2.2, red_T_of_resTriv hK (hP g g.2)])
      (fun g h => by rw [Subgroup.coe_mul, y.2.2, red_dual_of_resTriv hK hρ (hP g g.2)])
      (fun g hg => hy g hg) _ (fun g h => by
        change lam (x.1 g ⬝ᵥ red i K ρ g (y.1 h)) = lam (x.1 g ⬝ᵥ y.1 h)
        rw [red_dual_of_resTriv hK hρ (hP g g.2)])
  · have hc : Continuous ((cConj X).comp (DecV N P).subtype) := continuous_cConj.comp continuous_subtype_val
    let w : Z2 (muLoc D.host.E (X.l i) 1 (N.plOm.1 P)) :=
      compatiblePairCocycles2 (muRep D.host.E N.Om (X.l i) 1) _ ((cConj X).comp (DecV N P).subtype) hc LinearMap.id continuous_id
        (fun g m => by
          rw [hμ]
          change ((cycMod D.host.E N.Om (X.l i) 1 (cConj X g) : (ZMod (X.l i ^ 1))ˣ) : ZMod (X.l i ^ 1)) * m = m
          rw [cycMod_of_resTriv hK (hP' g), Units.val_one, one_mul]) (cupZ hK hρ lam x y)
    have h1 := key (fun g => x.1 (cConj X g)) (fun g => y.1 (cConj X g)) (x.2.1.comp hc) (y.2.1.comp hc)
      (fun g h => by rw [Subgroup.coe_mul, map_mul, x.2.2, red_T_of_resTriv hK (hP' g)])
      (fun g h => by rw [Subgroup.coe_mul, map_mul, y.2.2, red_dual_of_resTriv hK hρ (hP' g)])
      (fun g hg => hy' _ (cConj_mem_ine X hg)) w (fun g h => by
        change lam (x.1 (cConj X g) ⬝ᵥ red i K ρ (cConj X g) (y.1 (cConj X h))) =
          lam (x.1 (cConj X g) ⬝ᵥ y.1 (cConj X h))
        rw [red_dual_of_resTriv hK hρ (hP' g)])
    have h2 := hinv.2 X.cc D.host.conj.toRingEquiv (cc_algebraMap X) (-1) (conj_root X.cc_cm hζ) _
      (moveVal X.cc (N.plOm.1 P)) P hA (fun x => by rw [mem_moveVal, RingEquiv.symm_apply_apply]) (-w)
      (locZ _ (cupZ hK hρ lam x y)) (fun g h g' h' hg hh => by
        have e : ∀ {a b : GE N}, (∀ x, b (X.cc x) = X.cc (a x)) → b = cConj X a := fun hab => by
          ext x
          rw [cConj_apply, ← hab, RingEquiv.apply_symm_apply]
        change (cupZ hK hρ lam x y).1 (g', h') = -1 * -(cupZ hK hρ lam x y).1 (cConj X g, cConj X h)
        rw [e hg, e hh, neg_one_mul, neg_neg])
    rw [h2, Submodule.Quotient.mk_neg, map_neg, h1]
    rfl

theorem mem_unrAt {bkP : BKPh X} {Q : Finset (PlE D.host)} {x : H1 (red i K ρ)}
    (hx : x ∈ selOn bkP i ρ (1 : GE N →* Kˣ) K Q) {v : PlE D.host} (hv : v ∉ placesOver D.host.E (X.l i))
    (hv' : v ∉ Spl (X := X) i) (hQ : v ∉ Q) :
    resH1 (red i K ρ) (DecV N v).subtype continuous_subtype_val x ∈ Formalism.GaloisCohomology.unrAt (red i K ρ) (N.plOm.1 v) := by
  have h := (mem_Sel _ _ _ _ _).1 hx v
  unfold Formalism.GaloisCohomology.bkCond at h
  rwa [if_neg (show ¬ ((X.l i : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal from hv), if_neg (fun e => e.elim hv' hQ)] at h

theorem mem_bkOn {bkP : BKPh X} {Q : Finset (PlE D.host)} {x : H1 (red i K ρ)}
    (hx : x ∈ selOn bkP i ρ (1 : GE N →* Kˣ) K Q) {v : PlE D.host} (hv : v ∈ placesOver D.host.E (X.l i)) :
    resH1 (red i K ρ) (DecV N v).subtype continuous_subtype_val x ∈ bkOn bkP i ρ (1 : GE N →* Kˣ) K v := by
  have h := (mem_Sel _ _ _ _ _).1 hx v
  unfold Formalism.GaloisCohomology.bkCond at h
  rwa [if_pos (show ((X.l i : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal from hv)] at h

theorem vanish_NS {bkP : BKPh X} (h : GalHyp bkP i s) (hK : IsRes i K) (hρ : ρ = Tgl i s ∨ IsDual i s ρ)
    {Q : Finset (PlE D.host)} {x : Z1 (red i K ρ)} (hx : cl x ∈ selOn bkP i ρ (1 : GE N →* Kˣ) K Q)
    {S : Set (PlE D.host)} (hS : ∀ v ∉ S, v ∉ placesOver D.host.E (X.l i) ∧ v ∉ Spl (X := X) i ∧ v ∉ Q) :
    ∀ n ∈ NS N.Om S, x.1 n = 0 ∧ ∀ m, red i K ρ n m = m := by
  refine GlobalTheory.T.cocycle_unramified_outside_vanish_on_kernel D.host.E N.Om K _ _ (contAction_red hK hρ) N.plOm S (fun v hv B hB σ hσ m => ?_) x
    fun v hv => mem_unrAt hx (hS v hv).1 (hS v hv).2.1 (hS v hv).2.2
  have := resTriv_of_inertia h (hS v hv).1 (hS v hv).2.1 hB hσ
  rcases hρ with rfl | hρ
  · exact red_T_of_resTriv hK this m
  · exact red_dual_of_resTriv hK hρ this m

theorem spl_subset : Spl (X := X) i ⊆ ↑(X.S0 i) := by
  rintro v ⟨h | h, -⟩
  · obtain ⟨k, hk⟩ := Set.mem_iUnion.1 h
    exact X.placesOver_subset_exceptional i k hk
  · exact X.primes_subset_exceptional i h

end HidaSetting

theorem reciprocity : Cheb → PoitouTateTotallyComplex → CohDimTwo → TameLocal → LocalFiniteness → LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerChar → UnramifiedOrthogonality → Gen.ArchimedeanSignatureMatching → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → FirstHalf i s → Recip bkP i s := by
  intro _ hPT _ hT _ hLD _ _ _ _ _ D N X bkP i s h hF K _ _ _ _ hK ρ hρ M R P d φ φ' Q hM hpos hQ γ γ' hγ
  classical
  have hl : (X.l i).Prime := Fact.out
  haveI : NeZero (X.l i ^ 1) := ⟨pow_ne_zero _ hl.ne_zero⟩
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  haveI : IsAlgClosed N.Om := IsAlgClosure.isAlgClosed D.host.E
  haveI : CharZero N.Om := charZero_of_injective_algebraMap (algebraMap D.host.E N.Om).injective
  haveI : NeZero ((X.l i : ℕ) : N.Om) := ⟨Nat.cast_ne_zero.mpr hl.ne_zero⟩
  haveI := isLocalHom_of_isRes hK
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot N.Om (X.l i ^ 1)
  obtain ⟨inv, hinv, hsum⟩ := GlobalTheory.T.sum_local_inv_eq_zero_of_unramified_cocycle hPT D.host.E N.Om (X.l i) ζ hζ
  obtain ⟨haux, -, hφ⟩ := id hpos
  have hS0 : ∀ q v, Over (P q) v → v ∉ placesOver D.host.E (X.l i) ∧ v ∉ Spl (X := X) i := fun q v hv =>
    ⟨fun e => (haux.1 q v hv).2.2.2.1 (X.twistExcludedPlaces_contains_residueChar i e), fun e => (haux.1 q v hv).2.2.2.1 (spl_subset e)⟩
  have hq : ∀ q, normV (P q) ≡ 1 [MOD X.l i ^ 1] := fun q => by
    have h1 : normV (P q) ≡ 1 [MOD 2 * X.l i ^ M] := by
      have := (haux.1 q _ (over_refl _)).2.2.2.2.2
      rw [← this]
      exact (Nat.mod_modEq _ _).symm
    exact h1.of_dvd (Dvd.dvd.mul_left (pow_dvd_pow _ hM) 2)
  choose u hu using fun a : Fin R => local_pair hT h hK hρ hζ hinv (hS0 _ _ (over_refl (P (.inr a)))).1 (hq _)
    (hφ a).1 hM (d (.inr a)) (haux.2.2 _).1 (hγ a).1 (hγ a).2.1 (hφ a).2.1
  have hu0 : ∀ a, ((((u a : (ZMod (X.l i ^ 1))ˣ) : ZMod (X.l i ^ 1)).val : ℕ) : K) ≠ 0 := fun a e => by
    haveI : CharP K (X.l i ^ 1) := by
      rw [pow_one]; exact (CharP.charP_iff_prime_eq_zero hl).2 (l_eq_zero hK)
    haveI : Fact (1 < X.l i ^ 1) := ⟨by rw [pow_one]; exact hl.one_lt⟩
    rw [CharP.cast_eq_zero_iff K (X.l i ^ 1), ← ZMod.natCast_eq_zero_iff, ZMod.natCast_zmod_val] at e
    exact (u a).ne_zero e
  refine ⟨fun a => Units.mk0 _ (hu0 a), fun x y hx hy => ?_⟩
  refine eq_zero_of_forall_additive (l := X.l i) (fun k => by rw [nsmul_eq_mul, l_eq_zero hK, zero_mul]) _ fun lam => ?_
  choose Pb hPb using fun a : Fin R => exists_isConjPl (P (.inr a))
  have hne : ∀ a b, P (.inr a) ≠ Pb b := fun a b e => by
    have : Sum.inr b = Sum.inr a := haux.2.1 _ _ (Or.inr (e ▸ hPb b))
    obtain rfl : b = a := Sum.inr_injective this
    exact ne_of_isSplitPl (haux.1 _ _ (over_refl _)).1 (hPb b) e
  have hPbinj : Function.Injective Pb := fun a b e =>
    Sum.inr_injective (haux.2.1 (.inr a) (.inr b) (over_trans (Or.inr (hPb a)) (over_symm (Or.inr (e ▸ hPb b)))))
  have hPinj : Function.Injective fun a => P (.inr a) := fun a b e =>
    Sum.inr_injective (haux.2.1 (.inr a) (.inr b) (Or.inl e.symm))
  let Av : PlE D.host → ValuationSubring N.Om := Function.extend Pb
    (fun a => moveVal X.cc (N.plOm.1 (P (.inr a)))) N.plOm.1
  have hAb : ∀ a, Av (Pb a) = moveVal X.cc (N.plOm.1 (P (.inr a))) := fun a => hPbinj.extend_apply _ _ a
  have hAv : ∀ v, (¬ ∃ a, Pb a = v) → Av v = N.plOm.1 v := fun v hv => Function.extend_apply' _ _ v hv
  have hplace : ∀ v, IsPlaceOver (Av v) v := fun v => by
    by_cases hv : ∃ a, Pb a = v
    · obtain ⟨a, rfl⟩ := hv
      rw [hAb]
      exact isPlaceOver_moveVal_cc X (hPb a) (N.plOm.2 _)
    · rw [hAv v hv]
      exact N.plOm.2 v
  let S : Finset (PlE D.host) := (X.S0 i).filter (fun v => v ∈ placesOver D.host.E (X.l i) ∨ v ∈ Spl (X := X) i) ∪ Q
  have hmem : ∀ v, v ∈ S ↔ v ∈ placesOver D.host.E (X.l i) ∨ v ∈ Spl (X := X) i ∨ v ∈ Q := fun v => by
    rw [Finset.mem_union, Finset.mem_filter, ← or_assoc]
    exact or_congr_left ⟨fun e => e.2, fun e => ⟨e.elim (fun e => X.twistExcludedPlaces_contains_residueChar i e) fun e => spl_subset e, e⟩⟩
  have hout : ∀ v ∉ (S : Set (PlE D.host)), v ∉ placesOver D.host.E (X.l i) ∧ v ∉ Spl (X := X) i ∧ v ∉ Q := fun v hv => by
    simpa only [Finset.mem_coe, hmem, not_or] using hv
  have hxN := vanish_NS h hK (Or.inl rfl) hx hout
  have hyN := vanish_NS h hK (Or.inr hρ) hy (S := S) fun v hv => ⟨(hout v hv).1, (hout v hv).2.1, by simp⟩
  have hyI := vanish_NS h hK (Or.inr hρ) hy (S := placesOver D.host.E (X.l i) ∪ Spl (X := X) i)
    fun v hv => ⟨fun e => hv (Or.inl e), fun e => hv (Or.inr e), by simp⟩
  have hyI' : ∀ q v, Over (P q) v → ∀ B, IsPlaceOver B v → ∀ σ ∈ Ine (F := D.host.E) B, y.1 σ = 0 :=
    fun q v hv B hB σ hσ => (hyI σ (mem_NS (fun e => e.elim (hS0 q v hv).1 (hS0 q v hv).2) hB hσ)).1
  let t : ValuationSubring N.Om → ZMod (X.l i ^ 1) := fun A =>
    inv A (Submodule.Quotient.mk (locZ A (cupZ hK hρ lam x y)))
  have h0 : ∑ v ∈ S, t (Av v) = 0 :=
    hsum S (fun v hv => (hmem v).2 (Or.inl hv)) Av hplace (cupZ hK hρ lam x y) (fun g k n hn n' hn' => by
      change lam (x.1 (g * n) ⬝ᵥ red i K ρ (g * n) (y.1 (k * n'))) = lam (x.1 g ⬝ᵥ red i K ρ g (y.1 k))
      rw [x.2.2, y.2.2, (hxN n hn).1, (hyN n' hn').1, map_zero, map_zero, add_zero, add_zero, map_mul,
        Module.End.mul_apply, (hyN n hn).2]) (fun v => locZ (Av v) (cupZ hK hρ lam x y)) fun _ _ _ => rfl
  have h1 : ∑ q : Fin R ⊕ Fin R, t (Av (Sum.elim (fun a => P (.inr a)) Pb q)) = ∑ v ∈ S, t (Av v) := by
    refine Finset.sum_of_injOn (Sum.elim (fun a => P (.inr a)) Pb) (hPinj.sumElim hPbinj hne).injOn ?_ ?_ fun _ _ => rfl
    · rintro (a | a) -
      · exact (hmem _).2 (Or.inr (Or.inr ((hQ _).2 ⟨_, over_refl _⟩)))
      · exact (hmem _).2 (Or.inr (Or.inr ((hQ _).2 ⟨_, Or.inr (hPb a)⟩)))
    · intro v hv hv'
      rw [hAv v fun ⟨a, e⟩ => hv' ⟨.inr a, by simp, e⟩]
      have : (Submodule.Quotient.mk (locZ (N.plOm.1 v) (cupZ hK hρ lam x y)) : H2 _) = 0 := by
        rcases (hmem v).1 hv with e | e | e
        · exact GlobalTheory.T.local_cup_pairing_reduced_cocycles hLD D N X bkP i s h K hK ρ hρ v e (restrictCocycles1 _ _ continuous_subtype_val x)
            (restrictCocycles1 _ _ continuous_subtype_val y) (mem_bkOn hx e) (mem_bkOn hy e) lam _ fun _ _ => rfl
        · exact loc_eq_zero_of_subsingleton hK hρ lam x y v (local_cohomology_vanishes D N X bkP i s h v e K 1
            (by rw [MonoidHom.ker_one]; exact isOpen_univ) (fun g => ⟨0, by simp⟩) K (tors_field K) _ (Or.inl rfl)).2.1
        · obtain ⟨a | a, ha⟩ := (hQ v).1 e
          · exact loc_eq_zero_of_subsingleton hK hρ lam x y v (hF M R P d φ φ' hM hpos K 1
              (by rw [MonoidHom.ker_one]; exact isOpen_univ) (fun g => ⟨0, by simp⟩) K (tors_field K) _ (Or.inl rfl)
              a v ha).2.1
          · rcases ha with rfl | ha
            · exact absurd ⟨.inl a, by simp, rfl⟩ hv'
            · exact absurd ⟨.inr a, by simp, isConjPl_unique (hPb a) ha⟩ hv'
      change inv _ _ = 0
      rw [this, map_zero]
  rw [h0, Fintype.sum_sum_type, ← Finset.sum_add_distrib] at h1
  rw [map_sum, ← h1]
  refine Finset.sum_congr rfl fun a _ => ?_
  obtain ⟨e1, e2⟩ := hu a lam x y (hyI' _ _ (over_refl _) _ (N.plOm.2 _))
    (hyI' _ _ (Or.inr (hPb a)) _ (isPlaceOver_moveVal_cc X (hPb a) (N.plOm.2 _)))
  have g1 : γ' a = cConj X (γ a) := AlgEquiv.ext (hγ a).2.2
  have g2 : φ' a = cConj X (φ a) := AlgEquiv.ext (hφ a).2.2
  rw [Sum.elim_inl, Sum.elim_inr, hAb, hAv _ fun ⟨b, e⟩ => hne a b e.symm, Units.val_mk0, lam_natCast_mul]
  simp only [t]
  rw [e1, e2, form, map_sub, g1, g2]
  ring

end GlobalTheory.ResRecip
