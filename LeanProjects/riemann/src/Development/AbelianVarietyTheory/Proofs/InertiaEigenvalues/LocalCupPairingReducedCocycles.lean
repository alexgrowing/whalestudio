import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDualDualRep
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CupCoboundaryStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MuCocycleCoboundaryLiftStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsZmodPowCoboundaryOfRationalCoboundaryStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousAlgebraMapPadicInt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteQuotientPow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntegralOfNormLeOne
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.Published.PoitouTate GlobalTheory.ResSel

namespace GlobalTheory.CupAbove

theorem cup_mem_of_span {R Γ M M' P : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
    [AddCommGroup M'] [Module R M'] [TopologicalSpace M'] [IsTopologicalAddGroup M'] [ContinuousConstSMul R M']
    [AddCommGroup P] [Module R P] [TopologicalSpace P] [IsTopologicalAddGroup P] [ContinuousConstSMul R P]
    (π : Representation R Γ M) (π' : Representation R Γ M') (μ : Representation R Γ P)
    (b : M →ₗ[R] M' →ₗ[R] P) (hb : Continuous fun p : M × M' => b p.1 p.2)
    (hbe : ∀ g x y, b (π g x) (π' g y) = μ g (b x y)) (hc : ContAction π')
    (W : Submodule R (Z2 μ)) (hW : (B2 μ).comap (Z2 μ).subtype ≤ W) (S : Set (H1 π)) (S' : Set (H1 π'))
    (h : ∀ s ∈ S, ∀ s' ∈ S', ∃ z z', s = Submodule.Quotient.mk z ∧ s' = Submodule.Quotient.mk z' ∧
      cupCocycleZ1Z1 π π' μ b hb hbe hc z z' ∈ W)
    (x : Z1 π) (y : Z1 π') (hx : Submodule.Quotient.mk x ∈ Submodule.span R S)
    (hy : Submodule.Quotient.mk y ∈ Submodule.span R S') : cupCocycleZ1Z1 π π' μ b hb hbe hc x y ∈ W := by
  have e : ∀ z z', cupProductH1H1 π π' μ b hb hbe hc (Submodule.Quotient.mk z) (Submodule.Quotient.mk z') =
      Submodule.mkQ _ (cupCocycleZ1Z1 π π' μ b hb hbe hc z z') := fun _ _ => rfl
  have h1 : Submodule.map₂ (cupProductH1H1 π π' μ b hb hbe hc) (Submodule.span R S) (Submodule.span R S') ≤
      W.map (Submodule.mkQ _) := by
    rw [Submodule.map₂_span_span, Submodule.span_le]
    rintro _ ⟨s, hs, s', hs', rfl⟩
    obtain ⟨z, z', rfl, rfl, hz⟩ := h s hs s' hs'
    exact ⟨_, hz, (e z z').symm⟩
  have h2 := h1 (Submodule.apply_mem_map₂ _ hx hy)
  rw [e, ← Submodule.mem_comap, Submodule.comap_map_mkQ, sup_eq_right.2 hW] at h2
  exact h2

def addCob {K Γ A : Type} [CommRing K] [Group Γ] [TopologicalSpace Γ] [TopologicalSpace K] [DiscreteTopology K]
    [CommRing A] [TopologicalSpace A] [DiscreteTopology A] (μ : Representation K Γ K) (χ : Γ → A) : Submodule K (Z2 μ) where
  carrier := {z | ∀ lam : K →+ A, ∃ a : Γ → A, Continuous a ∧ ∀ g h, lam (z.1 (g, h)) = χ g * a h - a (g * h) + a g}
  zero_mem' := fun lam => ⟨0, continuous_const, fun g h => by simp⟩
  add_mem' := fun {z z'} hz hz' lam => by
    obtain ⟨a, ha, h1⟩ := hz lam
    obtain ⟨a', ha', h2⟩ := hz' lam
    refine ⟨a + a', ha.add ha', fun g h => ?_⟩
    simp only [Submodule.coe_add, Pi.add_apply, map_add, h1, h2]
    ring
  smul_mem' := fun k z hz lam => hz (lam.comp (AddMonoidHom.mulLeft k))

theorem map_padic_mul {l : ℕ} [Fact l.Prime] {K : Type} [CommRing K] (φ : ℤ_[l] →+* K) (hl : (l : K) = 0)
    (lam : K →+ ZMod (l ^ 1)) (u : ℤ_[l]) (k : K) : lam (φ u * k) = PadicInt.toZModPow 1 u * lam k := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec 1 u)
  have h1 : φ u = (u.appr 1 : ℕ) := by
    have := congrArg φ hc
    rw [map_mul, map_pow, map_natCast, hl, map_sub, map_natCast, pow_one, mul_zero] at this
    exact sub_eq_zero.1 this.symm
  have h2 : PadicInt.toZModPow 1 u = (u.appr 1 : ℕ) := rfl
  rw [h1, h2, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]

section Galois

variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω}

theorem mk_eq_zero_iff (w : Z2 (muLoc F l 1 A)) : (Submodule.Quotient.mk w : H2 (muLoc F l 1 A)) = 0 ↔
    ∃ a : Dec (F := F) A → ZMod (l ^ 1), Continuous a ∧ ∀ g h : Dec (F := F) A, w.1 (g, h) =
      PadicInt.toZModPow 1 ((cycZ F Ω l g : ℤ_[l]ˣ) : ℤ_[l]) * a h - a (g * h) + a g := by
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, separated_dvr_second_cohomology_mem]
  refine exists_congr fun a => and_congr_right fun _ => ⟨fun e g h => (congrFun e (g, h)).symm, fun e => ?_⟩
  funext ⟨g, h⟩
  exact (e g h).symm

variable {K : Type} [CommRing K] [TopologicalSpace K] [DiscreteTopology K] (φ : ℤ_[l] →+* K) (hl : (l : K) = 0)
  (μ : Representation K (Dec (F := F) A) K) (hμ : ∀ g k, μ g k = φ ((cycZ F Ω l g : ℤ_[l]ˣ) : ℤ_[l]) * k)

include hl hμ

theorem exists_push (z : Z2 μ) (lam : K →+ ZMod (l ^ 1)) : ∃ w : Z2 (muLoc F l 1 A), ∀ g h, w.1 (g, h) = lam (z.1 (g, h)) := by
  refine ⟨⟨fun p => lam (z.1 p), continuous_of_discreteTopology.comp z.2.1, fun g h k => ?_⟩, fun _ _ => rfl⟩
  have e := congrArg lam (z.2.2 g h k)
  rw [map_sub, map_add, map_sub, hμ, map_padic_mul φ hl, map_zero] at e
  exact e

theorem coboundaries_le_cyclotomic_additive : (B2 μ).comap (Z2 μ).subtype ≤
    addCob μ (fun g => PadicInt.toZModPow 1 ((cycZ F Ω l g : ℤ_[l]ˣ) : ℤ_[l])) := by
  rintro z ⟨c, hc, e⟩ lam
  refine ⟨fun g => lam (c g), continuous_of_discreteTopology.comp hc, fun g h => ?_⟩
  have e' : z.1 (g, h) = μ g (c h) - c (g * h) + c g := (congrFun e (g, h)).symm
  rw [e', map_add, map_sub, hμ, map_padic_mul φ hl]

end Galois

theorem mk_eq_zero_of_rational (hT : LocalTateDuality) {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)} (hA : IsPlaceOver A v)
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O)
    (β : O →+ ZMod (l ^ 1)) (z : Dec (F := F) A → Dec (F := F) A → O) (f : Dec (F := F) A → ↥Bw.LL.1) (hf : Continuous f)
    (hz : ∀ g h, Bw.toLL (z g h) =
      Bw.toLL (algebraMap ℤ_[l] O ((cycZ F Ω l g : ℤ_[l]ˣ) : ℤ_[l])) * f h - f (g * h) + f g)
    (w : Z2 (muLoc F l 1 A)) (hw : ∀ g h, w.1 (g, h) = β (z g h)) :
    (Submodule.Quotient.mk w : H2 (muLoc F l 1 A)) = 0 := by
  have : IsGalois F Ω := {}
  have : CompactSpace (Dec (F := F) A) := isCompact_iff_compactSpace.1 (isClosed_Dec A).isCompact
  have : IsTopologicalRing ↥Bw.LL.1 := inferInstanceAs (IsTopologicalRing ↥Bw.LL.1.toSubfield.toSubring)
  have hr : Set.range Bw.toLL = Set.range (algebraMap ↥(Loc.OL Bw.LL) ↥Bw.LL.1) :=
    Bw.eO.surjective.range_comp (algebraMap ↥(Loc.OL Bw.LL) ↥Bw.LL.1)
  obtain ⟨n, a, ha, e⟩ := GlobalTheory.T.exists_zmod_pow_coboundary_of_rational_coboundary' (Dec (F := F) A) l (fun g => ((cycZ F Ω l g : ℤ_[l]ˣ) : ℤ_[l])) O ↥Bw.LL.1 Bw.toLL
    (GlobalTheory.BlochKatoIntegralScalars.toLL_injective Bw) (hr ▸ GlobalTheory.LocalIntegers.isOpen_integers l Bw.LL)
    (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
    (fun x => by
      obtain ⟨n, hn⟩ := GlobalTheory.BlochKatoIntegralScalars.exists_pow_mul_mem_OL Bw.LL (fun (_ : Unit) (_ : Fin 1) => x)
        continuous_const
      exact ⟨n, hr ▸ ⟨⟨_, hn () 0⟩, rfl⟩⟩) β z f hf hz
  refine GlobalTheory.T.mu_cocycle_coboundary_lift hT F Ω l A v hA n w a ha fun g h => ?_
  rw [hw]
  exact e g h

section Matrices

variable {Γ O K : Type} [Group Γ] [CommRing O] [CommRing K] [Algebra O K] {r : ℕ}

theorem repOn_one_apply (ρ : Γ →* GL (Fin r) O) (g : Γ) (m : Fin r → K) :
    repOn ρ (1 : Γ →* Kˣ) K g m = (((ρ g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O).map (algebraMap O K)).mulVec m := by
  funext a
  simp [repOn, matAct, Matrix.mulVec, dotProduct]

theorem dot_equivariant (T T' : Matrix (Fin r) (Fin r) O) (hT : IsUnit T.det) (u : O) (h : T' = u • T⁻¹.transpose)
    (x y : Fin r → K) :
    (T.map (algebraMap O K)).mulVec x ⬝ᵥ (T'.map (algebraMap O K)).mulVec y = algebraMap O K u * (x ⬝ᵥ y) := by
  have e : (T.map (algebraMap O K)).transpose * T'.map (algebraMap O K) = algebraMap O K u • 1 := by
    rw [← Matrix.transpose_map, ← Matrix.map_mul, h, Matrix.mul_smul, ← Matrix.transpose_mul,
      Matrix.nonsing_inv_mul _ hT, Matrix.transpose_one]
    ext a b
    by_cases hab : a = b <;> simp [hab]
  rw [← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, e]
  rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]

theorem dot_generators (T : Matrix (Fin r) (Fin r) O) (y y' : Fin r → O) (b b' : K) :
    (fun a => algebraMap O K (y a) • b) ⬝ᵥ (T.map (algebraMap O K)).mulVec (fun a => algebraMap O K (y' a) • b') =
      (b * b') * algebraMap O K (y ⬝ᵥ T.mulVec y') := by
  simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, Finset.mul_sum, Matrix.map_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by ring

end Matrices

theorem cup_eq_zero_above : LocalTateDuality → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → ∀ (K : Type) [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K], IsRes i K → ∀ ρ, IsDual i s ρ → ∀ v ∈ placesOver D.host.E (X.l i), ∀ (x : Z1 ((red i K (Tgl i s)).comp (DecV N v).subtype)) (y : Z1 ((red i K ρ).comp (DecV N v).subtype)), Submodule.Quotient.mk x ∈ bkOn bkP i (Tgl i s) (1 : GE N →* Kˣ) K v → Submodule.Quotient.mk y ∈ bkOn bkP i ρ (1 : GE N →* Kˣ) K v → ∀ (lam : K →+ ZMod (X.l i ^ 1)) (w : Z2 (muLoc D.host.E (X.l i) 1 (N.plOm.1 v))), (∀ g h : ↥(DecV N v), w.1 (g, h) = lam (x.1 g ⬝ᵥ red i K ρ g (y.1 h))) → (Submodule.Quotient.mk w : H2 (muLoc D.host.E (X.l i) 1 (N.plOm.1 v))) = 0 := by
  intro hT D N X bkP i s _ K _ _ _ _ hK ρ hρ v hv x y hx hy lam w hw
  let φ : ℤ_[X.l i] →+* K := (algebraMap (X.O0 i) K).comp (algebraMap ℤ_[X.l i] (X.O0 i))
  have hl : ((X.l i : ℕ) : K) = 0 := by
    rw [← map_natCast (algebraMap (X.O0 i) K)]
    exact hK _ (GlobalTheory.PrimeToInertia.l_mem i)
  let μ : Representation K (DecV N v) K :=
    charRep (((Units.map (algebraMap (X.O0 i) K).toMonoidHom).comp (eps0 X i)).comp (DecV N v).subtype)
  have hμ : ∀ (g : DecV N v) k, μ g k = φ ((cycZ D.host.E N.Om (X.l i) g : ℤ_[X.l i]ˣ) : ℤ_[X.l i]) * k := fun _ _ => rfl
  have hbe : ∀ (g : DecV N v) (m m' : Fin D.R.r → K),
      dotProductBilin K K (((red i K (Tgl i s)).comp (DecV N v).subtype) g m) (((red i K ρ).comp (DecV N v).subtype) g m') =
        μ g (dotProductBilin K K m m') := by
    intro g m m'
    change red i K (Tgl i s) g m ⬝ᵥ red i K ρ g m' = algebraMap (X.O0 i) K ((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) * (m ⬝ᵥ m')
    rw [repOn_one_apply, repOn_one_apply]
    refine dot_equivariant _ _ (Matrix.isUnits_det_units _) _ ?_ m m'
    rw [hρ, Tgl_coe]
    rfl
  have hc : ContAction ((red i K ρ).comp (DecV N v).subtype) := by
    have : IsLocalHom (algebraMap (X.O0 i) K) := ⟨fun a ha => by
      by_contra hn
      exact ha.ne_zero (hK a hn)⟩
    have h1 : ContAction (red i K ρ) := by
      refine GlobalTheory.PrimeToInertia.contAction_repOn (X.twistBaseCoefficientRing_isAdic i) ρ ?_ 1 (by rw [MonoidHom.ker_one, Subgroup.coe_top]; exact isOpen_univ) fun b => ⟨1, fun c hc => ?_⟩
      · simp_rw [show ∀ g, _ from hρ]; exact GlobalTheory.PrimeToInertia.continuous_Tdual i s
      · rw [pow_one, IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at hc
        rw [hc, zero_smul]
    exact h1.comp (f := fun p : DecV N v × (Fin D.R.r → K) => ((p.1 : GE N), p.2)) (by fun_prop)
  rw [bkOn, dif_pos hv] at hx hy
  have key := cup_mem_of_span _ _ μ (dotProductBilin K K) continuous_of_discreteTopology hbe hc _
    (coboundaries_le_cyclotomic_additive φ hl μ hμ) _ _ (by
      rintro _ ⟨z, c, t, b, h1, h2, h3, rfl⟩ _ ⟨z', c', t', b', h1', h2', h3', rfl⟩
      refine ⟨z, z', rfl, rfl, fun lam => ?_⟩
      obtain ⟨f, hf, e⟩ := GlobalTheory.T.cup_coboundary_alt D N X bkP i s ‹_› ρ hρ v hv c c' t t' h1 h1' h2 h2'
      obtain ⟨w, hw⟩ := exists_push φ hl μ hμ
        (cupCocycleZ1Z1 _ _ μ (dotProductBilin K K) continuous_of_discreteTopology hbe hc z z') lam
      simp_rw [← hw]
      refine (mk_eq_zero_iff w).1 (mk_eq_zero_of_rational hT (N.plOm.2 v) (bkP.br i v hv)
        ((lam.comp (AddMonoidHom.mulLeft (b * b'))).comp (algebraMap (X.O0 i) K).toAddMonoidHom) _ f hf e w fun g h => ?_)
      rw [hw]
      change lam (z.1 g ⬝ᵥ red i K ρ g (z'.1 h)) = lam (b * b' * algebraMap (X.O0 i) K _)
      rw [repOn_one_apply, show z.1 g = _ from funext (h3 g), show z'.1 h = _ from funext (h3' h), dot_generators])
    x y hx hy
  obtain ⟨a, ha, e⟩ := key lam
  exact (mk_eq_zero_iff w).2 ⟨a, ha, fun g h => (hw g h).trans (e g h)⟩

end GlobalTheory.CupAbove
