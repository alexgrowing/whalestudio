import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftBlochKatoCocycleIffOrthogonalLatticeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CobOfGen
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousAlgebraMapPadicInt
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.ResDual

namespace GlobalTheory.ResOrth

theorem mem_of_mk_mem_span {k Z : Type} [CommRing k] [AddCommGroup Z] [Module k Z] {A B : Submodule k Z} (hB : B ≤ A)
    {S : Set (Z ⧸ B)} (hS : ∀ ξ ∈ S, ∃ z ∈ A, ξ = Submodule.Quotient.mk z) {x : Z}
    (hx : Submodule.Quotient.mk x ∈ Submodule.span k S) : x ∈ A := by
  have h1 : Submodule.span k S ≤ A.map B.mkQ := Submodule.span_le.2 fun ξ hξ => by
    obtain ⟨z, hz, rfl⟩ := hS ξ hξ
    exact ⟨z, hz, rfl⟩
  obtain ⟨z, hz, e⟩ := h1 hx
  have h2 : z - x ∈ B := (Submodule.Quotient.eq B).1 e
  simpa using A.sub_mem hz (hB h2)

section General

variable {Γ k M M' : Type} [Group Γ] [TopologicalSpace Γ] [CommRing k] [AddCommGroup M] [Module k M] [AddCommGroup M']
  [Module k M'] (χ : Γ → k) (ρ : Representation k Γ M) (ρ' : Representation k Γ M') (P : M →ₗ[k] M' →ₗ[k] k)

def leftPerp (y : Γ → M') : Submodule k (Γ → M) where
  carrier := {x | CupCob χ ρ' P x y}
  zero_mem' := ⟨0, IsLocallyConstant.const 0, fun g h => by simp⟩
  add_mem' := by
    rintro x x' ⟨f, hf, e⟩ ⟨f', hf', e'⟩
    refine ⟨f + f', hf.add hf', fun g h => ?_⟩
    simp only [Pi.add_apply, map_add, LinearMap.add_apply, e, e']
    ring
  smul_mem' := by
    rintro c x ⟨f, hf, e⟩
    refine ⟨fun g => c * f g, hf.comp _, fun g h => ?_⟩
    simp only [Pi.smul_apply, map_smul, LinearMap.smul_apply, e, smul_eq_mul]
    ring

def rightPerp (x : Γ → M) : Submodule k (Γ → M') where
  carrier := {y | CupCob χ ρ' P x y}
  zero_mem' := ⟨0, IsLocallyConstant.const 0, fun g h => by simp⟩
  add_mem' := by
    rintro y y' ⟨f, hf, e⟩ ⟨f', hf', e'⟩
    refine ⟨f + f', hf.add hf', fun g h => ?_⟩
    simp only [Pi.add_apply, map_add, e, e']
    ring
  smul_mem' := by
    rintro c y ⟨f, hf, e⟩
    refine ⟨fun g => c * f g, hf.comp _, fun g h => ?_⟩
    simp only [Pi.smul_apply, map_smul, e, smul_eq_mul]
    ring

variable [TopologicalSpace M] [DiscreteTopology M] [TopologicalSpace M'] [DiscreteTopology M']
  [ContinuousConstSMul k M] [ContinuousConstSMul k M']

variable {χ ρ ρ' P}

theorem cupCob_of_left_coboundary (hP : ∀ g x y, P (ρ g x) (ρ' g y) = χ g * P x y) {x : Γ → M} (hx : x ∈ B1 ρ)
    {y : Γ → M'} (hy : y ∈ Z1 ρ') : CupCob χ ρ' P x y := by
  obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 hx
  refine ⟨fun g => P m (y g), ((IsLocallyConstant.iff_continuous _).2 hy.1).comp _, fun g h => ?_⟩
  simp only [hm, hy.2, map_sub, map_add, LinearMap.sub_apply, hP]
  ring

theorem cupCob_of_right_coboundary (hP : ∀ g x y, P (ρ g x) (ρ' g y) = χ g * P x y) (hρ' : ContAction ρ')
    {x : Γ → M} (hx : x ∈ Z1 ρ) {y : Γ → M'} (hy : y ∈ B1 ρ') : CupCob χ ρ' P x y := by
  obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 hy
  have h1 : Continuous fun g => ρ' g m := hρ'.comp (f := fun g : Γ => (g, m)) (by fun_prop)
  refine ⟨fun g => -P (x g) (ρ' g m), (((IsLocallyConstant.iff_continuous _).2 hx.1).prodMk
    ((IsLocallyConstant.iff_continuous _).2 h1)).comp fun p => -P p.1 p.2, fun g h => ?_⟩
  simp only [hm, hx.2, map_sub, map_add, map_mul, LinearMap.add_apply, Module.End.mul_apply, hP]
  ring

theorem cupCob_of_span (hP : ∀ g x y, P (ρ g x) (ρ' g y) = χ g * P x y) (hρ' : ContAction ρ')
    {S : Set (H1 ρ)} {S' : Set (H1 ρ')} (p : Z1 ρ → Prop) (p' : Z1 ρ' → Prop)
    (hS : ∀ ξ ∈ S, ∃ z, p z ∧ ξ = Submodule.Quotient.mk z) (hS' : ∀ ξ ∈ S', ∃ z, p' z ∧ ξ = Submodule.Quotient.mk z)
    (h : ∀ z z', p z → p' z' → CupCob χ ρ' P z.1 z'.1) (x : Z1 ρ) (y : Z1 ρ')
    (hx : Submodule.Quotient.mk x ∈ Submodule.span k S) (hy : Submodule.Quotient.mk y ∈ Submodule.span k S') :
    CupCob χ ρ' P x.1 y.1 := by
  refine mem_of_mk_mem_span (A := (leftPerp χ ρ' P y.1).comap (Z1 ρ).subtype)
    (fun z hz => cupCob_of_left_coboundary hP hz y.2) (fun ξ hξ => ?_) hx
  obtain ⟨z, hz, rfl⟩ := hS ξ hξ
  refine ⟨z, ?_, rfl⟩
  refine mem_of_mk_mem_span (A := (rightPerp χ ρ' P z.1).comap (Z1 ρ').subtype)
    (fun z' hz' => cupCob_of_right_coboundary hP hρ' z.2 hz') (fun ξ' hξ' => ?_) hy
  obtain ⟨z', hz', rfl⟩ := hS' ξ' hξ'
  exact ⟨z', h z z' hz hz', rfl⟩

end General

section DVR

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem exists_residue_embedding {ϖ : O} (hϖ : Irreducible ϖ) :
    ∃ f : IsLocalRing.ResidueField O →ₗ[O] KmodO O, Function.Injective f ∧ ∀ a : O,
      f (IsLocalRing.residue O a) =
        Submodule.Quotient.mk ((algebraMap O (FractionRing O) ϖ)⁻¹ * algebraMap O (FractionRing O) a) := by
  have h0 : algebraMap O (FractionRing O) ϖ ≠ 0 := by simpa using hϖ.ne_zero
  let φ : O →ₗ[O] KmodO O := (Submodule.mkQ _).comp
    ((LinearMap.mulLeft O (algebraMap O (FractionRing O) ϖ)⁻¹).comp (Algebra.linearMap O (FractionRing O)))
  have hk : LinearMap.ker φ = IsLocalRing.maximalIdeal O := by
    ext a
    rw [LinearMap.mem_ker, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton]
    refine (Submodule.Quotient.mk_eq_zero _).trans ⟨?_, ?_⟩
    · rintro ⟨b, hb⟩
      refine ⟨b, IsFractionRing.injective O (FractionRing O) ?_⟩
      have hb' : algebraMap O (FractionRing O) b =
        (algebraMap O (FractionRing O) ϖ)⁻¹ * algebraMap O (FractionRing O) a := hb
      rw [map_mul, hb', mul_inv_cancel_left₀ h0]
    · rintro ⟨b, rfl⟩
      refine ⟨b, ?_⟩
      change algebraMap O (FractionRing O) b =
        (algebraMap O (FractionRing O) ϖ)⁻¹ * algebraMap O (FractionRing O) (ϖ * b)
      rw [map_mul, inv_mul_cancel_left₀ h0]
  exact ⟨(IsLocalRing.maximalIdeal O).liftQ φ hk.ge,
    LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot _ _ _ hk.le), fun a => rfl⟩

theorem kmod_torsion {l : ℕ} (hl : (l : O) ∈ IsLocalRing.maximalIdeal O) (b : KmodO O) :
    ∃ n : ℕ, l ^ n • b = 0 := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := O) a
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible hy0 hϖ
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hl
  obtain ⟨c, hc⟩ := hn.dvd.trans (pow_dvd_pow_of_dvd hl n)
  refine ⟨n, ?_⟩
  rw [← Submodule.mkQ_apply, ← map_nsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  refine ⟨c * x, ?_⟩
  have h1 : algebraMap O (FractionRing O) y ≠ 0 := by simpa using hy0
  rw [Algebra.linearMap_apply, nsmul_eq_mul, Nat.cast_pow, ← map_natCast (algebraMap O (FractionRing O)), ← map_pow,
    hc, map_mul, map_mul]
  field_simp

end DVR

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} {i : X.Tw}
  {K : Type} [Field K] [Algebra (X.O0 i) K]

theorem red_apply (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)) (g : GE N) (m : Fin D.R.r → K) :
    red i K ρ g m = ((ρ g : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).map (algebraMap (X.O0 i) K)).mulVec m := by
  funext a
  simp [repOn, matAct, Matrix.mulVec, dotProduct]

theorem red_dot (s : X.Sig i) {ρ : GE N →* GL (Fin D.R.r) (X.O0 i)} (hρ : IsDual i s ρ) (g : GE N)
    (x y : Fin D.R.r → K) :
    red i K (Tgl i s) g x ⬝ᵥ red i K ρ g y = algebraMap (X.O0 i) K ((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) * (x ⬝ᵥ y) := by
  have h3 : IsUnit (Tmat i s g).det := by
    rw [← Tgl_coe]; exact Matrix.isUnits_det_units _
  have e : (Tmat i s g).transpose * Tdual i s g = ((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) • 1 := by
    rw [Tdual, Matrix.mul_smul, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ h3, Matrix.transpose_one]
  rw [red_apply, red_apply, hρ, Tgl_coe, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    ← Matrix.transpose_map, ← Matrix.map_mul, e, Matrix.smul_one_eq_diagonal, Matrix.diagonal_map (map_zero _),
    ← Matrix.smul_one_eq_diagonal, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]

theorem bkOn_orthogonal : LocalTateDuality → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → ∀ (K : Type) [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K], IsRes i K → ∀ ρ, IsDual i s ρ → ∀ v ∈ placesOver D.host.E (X.l i), ∀ (x : Z1 ((red i K (Tgl i s)).comp (DecV N v).subtype)) (y : Z1 ((red i K ρ).comp (DecV N v).subtype)), Submodule.Quotient.mk x ∈ bkOn bkP i (Tgl i s) (1 : GE N →* Kˣ) K v → Submodule.Quotient.mk y ∈ bkOn bkP i ρ (1 : GE N →* Kˣ) K v → CupCob (fun g : DecV N v => algebraMap (X.O0 i) K ((eps0 X i g.1 : (X.O0 i)ˣ) : X.O0 i)) ((red i K ρ).comp (DecV N v).subtype) (dotProductBilin K K) x.1 y.1 := by
  intro hT D N X bkP i s hG K _ _ _ _ hK ρ hρ v hv x y hx hy
  have hloc : IsLocalHom (algebraMap (X.O0 i) K) := ⟨fun a ha => by
    by_contra hn
    exact ha.ne_zero (hK a hn)⟩
  have hc : ContAction (red i K ρ) := by
    refine GlobalTheory.PrimeToInertia.contAction_repOn (X.twistBaseCoefficientRing_isAdic i) ρ ?_ 1 (by rw [MonoidHom.ker_one, Subgroup.coe_top]; exact isOpen_univ) fun b => ⟨1, fun x hx => ?_⟩
    · simp_rw [hρ _]; exact GlobalTheory.PrimeToInertia.continuous_Tdual i s
    · rw [pow_one, IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at hx
      rw [hx, zero_smul]
  rw [bkOn, dif_pos hv] at hx hy
  refine cupCob_of_span (ρ := (red i K (Tgl i s)).comp (DecV N v).subtype)
    (ρ' := (red i K ρ).comp (DecV N v).subtype) (P := dotProductBilin K K) (fun g a b => red_dot s hρ g.1 a b)
    (hc.comp (f := fun p : DecV N v × (Fin D.R.r → K) => ((p.1 : GE N), p.2)) (by fun_prop))
    (fun z => ∃ d b, IsFCoc bkP i v hv (Tgl i s) d ∧ ∀ g a, z.1 g a = algebraMap (X.O0 i) K (d g a) • b)
    (fun z => ∃ d b, IsFCoc bkP i v hv ρ d ∧ ∀ g a, z.1 g a = algebraMap (X.O0 i) K (d g a) • b) ?_ ?_ ?_ x y hx hy
  · rintro ξ ⟨z, c, d, b, h1, h2, h3, rfl⟩
    exact ⟨z, ⟨d, b, isFCoc_iff.2 ⟨c, h1, h2⟩, h3⟩, rfl⟩
  · rintro ξ ⟨z, c, d, b, h1, h2, h3, rfl⟩
    exact ⟨z, ⟨d, b, isFCoc_iff.2 ⟨c, h1, h2⟩, h3⟩, rfl⟩
  rintro z z' ⟨d, b, hd, e⟩ ⟨d', b', hd', e'⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (X.O0 i)
  have hopen : IsOpen ((IsLocalRing.maximalIdeal (X.O0 i) : Ideal (X.O0 i)) : Set (X.O0 i)) := by
    simpa using (isAdic_iff.1 (X.twistBaseCoefficientRing_isAdic i)).1 1
  have hlc : ∀ a, IsLocallyConstant fun g => IsLocalRing.residue (X.O0 i) (d' g a) := fun a => by
    have hca : Continuous fun g => d' g a := (continuous_apply a).comp hd'.continuous
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun g => ?_
    filter_upwards [(hopen.preimage (hca.sub (continuous_const (y := d' g a)))).mem_nhds (x := g) (by simp)] with h hh
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact hh
  obtain ⟨f, hf, ef⟩ := (GlobalTheory.T.lift_blochKatoCocycle_iff_orthogonal_lattice D N X bkP i s hG ρ hρ v hv ϖ hϖ d' hlc (fun g h a => by
    rw [hd'.cocycle, hρ]; simp)).1 ⟨d', hd', fun g a => by simp⟩ d hd
  obtain ⟨ι, hι, eι⟩ := exists_residue_embedding hϖ
  have := X.twistBaseCoefficientRing_residueField_finite i
  obtain ⟨c, hc, ec⟩ := GlobalTheory.LocalH2Injective.h2_inj hT D.host.E N.Om (X.l i) _ v (N.plOm.2 v) (X.O0 i) _ _ ι hι
    (kmod_torsion (GlobalTheory.PrimeToInertia.l_mem i))
    (fun g h => IsLocalRing.residue (X.O0 i) (d g ⬝ᵥ (Tdual i s g.1).mulVec (d' h))) f hf
    (fun g h => (eι _).trans (ef g h))
  let π : IsLocalRing.ResidueField (X.O0 i) →+* K := IsLocalRing.ResidueField.lift (algebraMap (X.O0 i) K)
  have hπ : ∀ a, π (IsLocalRing.residue (X.O0 i) a) = algebraMap (X.O0 i) K a := fun a => rfl
  refine ⟨fun g => b * b' * π (c g), hc.comp fun t => b * b' * π t, fun g h => ?_⟩
  have e1 := congrArg π (ec g h)
  rw [hπ, map_add, map_sub, Algebra.smul_def, map_mul] at e1
  have e2 : π (algebraMap (X.O0 i) _ (algebraMap ℤ_[X.l i] (X.O0 i)
      ((cycZ D.host.E N.Om (X.l i) g.1 : ℤ_[X.l i]ˣ) : ℤ_[X.l i]))) =
      algebraMap (X.O0 i) K ((eps0 X i g.1 : (X.O0 i)ˣ) : X.O0 i) := rfl
  rw [e2] at e1
  have e3 : z.1 g ⬝ᵥ red i K ρ g.1 (z'.1 h) =
      b * b' * algebraMap (X.O0 i) K (d g ⬝ᵥ (Tdual i s g.1).mulVec (d' h)) := by
    rw [red_apply, hρ]
    simp only [dotProduct, Matrix.mulVec, e, e', map_sum, map_mul, Matrix.map_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  refine e3.trans ?_
  rw [e1]
  ring

end GlobalTheory.ResOrth
