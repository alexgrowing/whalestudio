import Mathlib
import Formalism.WachLatticeTwists.LatticeDualFibres.FibreDualStable
import Formalism.WachLatticeTwists.CharacterSplitJumps.Statement
import Formalism.WachLatticeTwists.CoprimeLiftBounds.Statement
import Formalism.GaloisCohomology.LocalTateDualityK
import ReciprocityTheory.Hypotheses.GalCohDefs
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

noncomputable section

namespace ReciprocityTheory.ChartRestriction.T2

open Formalism.NG Formalism.RepresentationBoundsCohomology.LOC Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.BR
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

abbrev GK (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) : Type := Formalism.GaloisCohomology.GK p K

structure PadicCoeff (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] : Prop where
  ring : IsTopologicalRing O
  compact : CompactSpace O
  t2 : T2Space O
  adic : IsAdic (IsLocalRing.maximalIdeal O)
  p_mem : (p : O) ∈ IsLocalRing.maximalIdeal O
  p_ne : (p : O) ≠ 0

structure FracTop (O : Type) [CommRing O] [TopologicalSpace O] [TopologicalSpace (FractionRing O)] : Prop where
  emb : Topology.IsOpenEmbedding (algebraMap O (FractionRing O))

structure IsFGTop (O : Type) [CommRing O] [TopologicalSpace O] (M : Type) [AddCommGroup M] [Module O M]
    [TopologicalSpace M] : Prop where
  fg : Module.Finite O M
  t2 : T2Space M
  csmul : ContinuousSMul O M

def IsCycOn (p : ℕ) {E Ω O : Type} [Field E] [Field Ω] [Algebra E Ω] [CommRing O] (H : Subgroup (Ω ≃ₐ[E] Ω))
    (ε : H →* Oˣ) : Prop :=
  ∀ (g : H) (n : ℕ) (ζ : Ω), ζ ^ (p ^ n) = 1 →
    ∃ a : ℕ, (g : Ω ≃ₐ[E] Ω) ζ = ζ ^ a ∧ ((ε g : Oˣ) : O) - (a : O) ∈ Ideal.span {(p : O) ^ n}

def IsCyc (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) {O : Type} [CommRing O]
    (ε : GK p K →* Oˣ) : Prop :=
  ∀ (g : GK p K) (n : ℕ) (ζ : PadicAlgCl p), ζ ^ (p ^ n) = 1 →
    ∃ a : ℕ, g ζ = ζ ^ a ∧ ((ε g : Oˣ) : O) - (a : O) ∈ Ideal.span {(p : O) ^ n}

abbrev carry {G G' O : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G'] [CommRing O]
    (i : G ≃ₜ* G') (ε : G →* Oˣ) : G' →* Oˣ := ε.comp i.symm.toMulEquiv.toMonoidHom

theorem twist_map {O G M M' : Type} [CommRing O] [Group G] [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M']
    (ε : G →* Oˣ) (f : M →ₗ[O] M') (g : G) (m : M) : f (twist ε M g m) = twist ε M' g (f m) := by
  exact map_smul f _ m

structure NatInv {O : Type} [CommRing O] [TopologicalSpace O] {Γ : Type} [Group Γ] [TopologicalSpace Γ] (ε : Γ →* Oˣ)
    (P : ∀ (M : Type) [AddCommGroup M] [Module O M] [TopologicalSpace M], Prop) where
  θ : ∀ (M : Type) [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul O M],
    P M → (H2 (twist ε M) ≃ₗ[O] M)
  nat : ∀ (M M' : Type) [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul O M]
    [AddCommGroup M'] [Module O M'] [TopologicalSpace M'] [IsTopologicalAddGroup M'] [ContinuousConstSMul O M']
    (h : P M) (h' : P M') (f : M →ₗ[O] M') (hf : Continuous f) (z : H2 (twist ε M)),
    θ M' h' (mapH2 (twist ε M) (twist ε M') f hf (twist_map ε f) z) = f (θ M h z)

structure RealLatG {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    {VT VT' : Type}
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
    [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
    [ContinuousSMul O VT'] [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT'] {G : Type} [Group G] [TopologicalSpace G]
    (i : G ≃ₜ* GK p K) (D : LatData O G VT VT') : Prop where
  cyc : IsCyc p K (carry i D.ε)
  lat : IsLatticeIn D.T
  perf : PerfectRight D.bT
  contT : ContAction D.ρT
  openT : IsOpen (D.T : Set VT)
  t2 : T2Space VT
  t2' : T2Space VT'
  cs : ContinuousConstSMul (FractionRing O) VT
  cs' : ContinuousConstSMul (FractionRing O) VT'

def cupFG {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    {VT VT' : Type}
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
    [ContinuousSMul O VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
    [ContinuousSMul O VT'] {G : Type} [Group G] [TopologicalSpace G] (D : LatData O G VT VT') :
    H1 D.ρT →ₗ[O] H1 D.ρT' →ₗ[O] H2 (twist D.ε (FractionRing O)) :=
  cupProductH1H1 D.ρT D.ρT' (twist D.ε (FractionRing O)) D.bT D.contbT D.eqT D.contT'

theorem inv_smul_smul_frac {O : Type} [CommRing O] [IsDomain O] {X : Type} [AddCommGroup X] [Module O X]
    [Module (FractionRing O) X] [IsScalarTower O (FractionRing O) X] {c : O} (hc : c ≠ 0) (y : X) :
    (algebraMap O (FractionRing O) c)⁻¹ • (c • y) = y := by
  have h0 : algebraMap O (FractionRing O) c ≠ 0 := fun h => hc (IsFractionRing.injective O (FractionRing O) (by simpa using h))
  rw [← algebraMap_smul (FractionRing O) c y, smul_smul, inv_mul_cancel₀ h0, one_smul]

def fracBilinear {O : Type} [CommRing O] [IsDomain O] {X Y : Type} [AddCommGroup X] [Module O X]
    [Module (FractionRing O) X] [IsScalarTower O (FractionRing O) X] [AddCommGroup Y] [Module O Y]
    [Module (FractionRing O) Y] [IsScalarTower O (FractionRing O) Y]
    (b : X →ₗ[O] Y →ₗ[O] FractionRing O) : X →ₗ[FractionRing O] Y →ₗ[FractionRing O] FractionRing O :=
  LinearMap.mk₂ (FractionRing O) (fun x y => b x y) (fun x x' y => by simp)
    (fun c x y => (IsLocalization.linearMap_compatibleSMul (nonZeroDivisors O) (FractionRing O) X (FractionRing O)).map_smul (b.flip y) c x)
    (fun x y y' => by simp)
    (fun c x y => (IsLocalization.linearMap_compatibleSMul (nonZeroDivisors O) (FractionRing O) Y (FractionRing O)).map_smul (b x) c y)

section Tr
variable {O Γ Γ' M M' : Type} [CommRing O] [Group Γ] [Group Γ'] [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M']

theorem trCompat_symm (e : Γ ≃* Γ') (u : M ≃ₗ[O] M') (ρ : Representation O Γ M) (ρ' : Representation O Γ' M')
    (hu : ∀ g m, u (ρ g m) = ρ' (e g) (u m)) (g : Γ) (y : M') : u.symm (ρ' (e g) y) = ρ g (u.symm y) := by
  rw [LinearEquiv.symm_apply_eq, hu, LinearEquiv.apply_symm_apply]

def transportCocycles (e : Γ ≃* Γ') (u : M ≃ₗ[O] M') (ρ : Representation O Γ M) (ρ' : Representation O Γ' M')
    (hu : ∀ g m, u (ρ g m) = ρ' (e g) (u m)) : coZ1s ρ' →ₗ[O] coZ1s ρ where
  toFun c := ⟨fun g => u.symm (c.1 (e g)), fun g h => by
    show u.symm (c.1 (e (g * h))) = u.symm (c.1 (e g)) + ρ g (u.symm (c.1 (e h)))
    rw [map_mul, c.2, map_add, trCompat_symm e u ρ ρ' hu]⟩
  map_add' a b := Subtype.ext (funext fun g => map_add u.symm _ _)
  map_smul' r a := Subtype.ext (funext fun g => map_smul u.symm _ _)

def traceH1 (e : Γ ≃* Γ') (u : M ≃ₗ[O] M') (ρ : Representation O Γ M) (ρ' : Representation O Γ' M')
    (hu : ∀ g m, u (ρ g m) = ρ' (e g) (u m)) : H1z ρ' →ₗ[O] H1z ρ :=
  Submodule.mapQ _ _ (transportCocycles e u ρ ρ' hu) (by
    rintro x ⟨v, hv⟩
    refine ⟨u.symm v, funext fun g => ?_⟩
    have h1 : ρ' (e g) v - v = x.1 (e g) := congrFun hv (e g)
    show ρ g (u.symm v) - u.symm v = u.symm (x.1 (e g))
    rw [← h1, map_sub, trCompat_symm e u ρ ρ' hu])

theorem transportH1_injective (e : Γ ≃* Γ') (u : M ≃ₗ[O] M') (ρ : Representation O Γ M) (ρ' : Representation O Γ' M')
    (hu : ∀ g m, u (ρ g m) = ρ' (e g) (u m)) : Function.Injective (traceH1 e u ρ ρ' hu) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h1 : (Submodule.Quotient.mk (transportCocycles e u ρ ρ' hu z) : H1z ρ) = 0 := hx
  rw [Submodule.Quotient.mk_eq_zero] at h1 ⊢
  obtain ⟨v, hv⟩ := h1
  refine ⟨u v, funext fun g' => ?_⟩
  obtain ⟨g, rfl⟩ := e.surjective g'
  have h2 : ρ g v - v = u.symm (z.1 (e g)) := congrFun hv g
  show ρ' (e g) (u v) - u v = z.1 (e g)
  rw [← hu, ← map_sub, h2, LinearEquiv.apply_symm_apply]

end Tr

section Cont
variable {O Γ M : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [Module O M]

def HcLC (ρ : Representation O Γ M) : Submodule O (H1z ρ) :=
  Submodule.map (Submodule.mkQ _)
    { carrier := {c : coZ1s ρ | IsLocallyConstant (c : Γ → M)}
      add_mem' := fun {_ _} ha hb => IsLocallyConstant.add ha hb
      zero_mem' := IsLocallyConstant.const 0
      smul_mem' := fun c _ hx => IsLocallyConstant.comp hx (fun m => c • m) }

variable [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul O M]

def continuousCocycleInclusion (ρ : Representation O Γ M) : ReciprocityTheory.Gal.Z1 ρ →ₗ[O] coZ1s ρ where
  toFun z := ⟨z.1, z.2.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def toH1Cocycles (ρ : Representation O Γ M) : ReciprocityTheory.Gal.H1 ρ →ₗ[O] H1z ρ :=
  Submodule.mapQ _ _ (continuousCocycleInclusion ρ) (by
    intro z hz
    obtain ⟨m, hm⟩ := (ReciprocityTheory.Gal.mem_coboundaries1 ρ _).1 hz
    exact ⟨m, funext fun g => (hm g).symm⟩)

theorem continuousH1_toH1_injective (ρ : Representation O Γ M) : Function.Injective (toH1Cocycles ρ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h1 : (Submodule.Quotient.mk (continuousCocycleInclusion ρ z) : H1z ρ) = 0 := hx
  rw [Submodule.Quotient.mk_eq_zero] at h1
  obtain ⟨v, hv⟩ := h1
  rw [Submodule.Quotient.mk_eq_zero]
  exact (ReciprocityTheory.Gal.mem_coboundaries1 ρ _).2 ⟨v, fun g => (congrFun hv g).symm⟩

end Cont

def DecEquiv : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (A : ValuationSubring Ω), A.valuation (p : Ω) < 1 →
    ∃ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] K)
      (i : ↥(A.decompositionSubgroup F) ≃ₜ* GK p K),
      (∀ (O : Type) [CommRing O] (ε : ↥(A.decompositionSubgroup F) →* Oˣ),
        IsCycOn p (A.decompositionSubgroup F) ε → IsCyc p K (carry i ε)) ∧
      (∀ g : ↥(A.decompositionSubgroup F), i g ∈ Formalism.GaloisCohomology.inertiaK p K ↔ (g : Ω ≃ₐ[F] Ω) ∈ Ine (F := F) A) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), IsPlaceOver A v → Module.finrank ℚ_[p] K = locDeg v

def InvIso : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)] {G : Type} [Group G] [TopologicalSpace G],
    FiniteDimensional ℚ_[p] K → PadicCoeff p O → FracTop O → ∀ (i : G ≃ₜ* GK p K) {ε : G →* Oˣ}, IsCyc p K (carry i ε) →
    ∃ (inv : H2 (twist ε (KO O)) ≃ₗ[O] KO O) (invF : H2 (twist ε (FractionRing O)) ≃ₗ[O] FractionRing O),
      ∀ z, inv (mapH2 (twist ε (FractionRing O)) (twist ε (KO O)) (toKO O) toKO_cont (toKO_equiv ε) z) = toKO O (invF z)

def FinIso : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    {VT VT' : Type}
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
    [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
    [ContinuousSMul O VT'] [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT'] {G : Type} [Group G] [TopologicalSpace G],
    FiniteDimensional ℚ_[p] K → PadicCoeff p O → ∀ (i : G ≃ₜ* GK p K) {D : LatData O G VT VT'}, RealLatG i D →
    Module.Finite O (H1 D.ρTl')

def RatIso : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    {VT VT' : Type}
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
    [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
    [ContinuousSMul O VT'] [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT'] {G : Type} [Group G] [TopologicalSpace G],
    FiniteDimensional ℚ_[p] K → PadicCoeff p O → FracTop O → ∀ (i : G ≃ₜ* GK p K) {D : LatData O G VT VT'}, RealLatG i D →
    Function.Injective D.invF → ∀ f : H1 D.ρT' →ₗ[O] FractionRing O, ∃ a, ∀ b, D.invF (cupFG D a b) = f b

def IntIso : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    {VT VT' : Type}
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
    [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
    [ContinuousSMul O VT'] [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT'] {G : Type} [Group G] [TopologicalSpace G],
    FiniteDimensional ℚ_[p] K → PadicCoeff p O → FracTop O → ∀ (i : G ≃ₜ* GK p K) {D : LatData O G VT VT'}, RealLatG i D →
    Function.Injective D.inv → ∀ x, (∀ t, D.pr x t = 0) → x = 0

def JSpan : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    {VT VT' : Type}
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
    [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
    [ContinuousSMul O VT'] [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT'] {G : Type} [Group G] [TopologicalSpace G],
    PadicCoeff p O → FracTop O → ∀ (i : G ≃ₜ* GK p K) {D : LatData O G VT VT'}, RealLatG i D →
    ∀ y : H1 D.ρT', ∃ c : O, c ≠ 0 ∧ c • y ∈ LinearMap.range D.j'

def NatInvIso : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] {G : Type} [Group G] [TopologicalSpace G],
    FiniteDimensional ℚ_[p] K → PadicCoeff p O → ∀ (i : G ≃ₜ* GK p K) {ε : G →* Oˣ}, IsCyc p K (carry i ε) →
    Nonempty (NatInv ε (fun M _ _ _ => IsFGTop O M))

def ShapeG : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)] {G : Type} [Group G] [TopologicalSpace G],
    FiniteDimensional ℚ_[p] K → PadicCoeff p O → FracTop O → ∀ (i : G ≃ₜ* GK p K) {ε : G →* Oˣ}, IsCyc p K (carry i ε) →
    ∀ e : ℕ, 0 < e → ∀ {M : Type} [AddCommGroup M] [Module O M] (_u : M ≃ₗ[O] KO O) (ρ : Representation O G M),
    (∀ g m, ρ g m = ((((ε g) ^ e)⁻¹ : Oˣ) : O) • m) → QuotShape (HcLC ρ) ⊥ (Module.finrank ℚ_[p] K)

def ShapeUnr : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)] {G : Type} [Group G] [TopologicalSpace G],
    FiniteDimensional ℚ_[p] K → PadicCoeff p O → FracTop O → ∀ (i : G ≃ₜ* GK p K)
    {M : Type} [AddCommGroup M] [Module O M] (_u : M ≃ₗ[O] KO O) (ρ : Representation O G M),
    (∀ g m, ρ g m = m) → ∀ I : Subgroup G, (∀ g, g ∈ I ↔ i g ∈ Formalism.GaloisCohomology.inertiaK p K) →
    QuotShape (HcLC ρ) (unrH1 ρ I) (Module.finrank ℚ_[p] K)

def UnrDec : Prop :=
  ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime]
    (A : ValuationSubring Ω), A.valuation (p : Ω) < 1 →
    ∃ χ : ↥(A.decompositionSubgroup F) → ℤ_[p], Continuous χ ∧ (∀ g h, χ (g * h) = χ g + χ h) ∧
      (∀ g : ↥(A.decompositionSubgroup F), (g : Ω ≃ₐ[F] Ω) ∈ Ine (F := F) A → χ g = 0) ∧ ∃ g, χ g = 1

def VhE : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (Av : HeightOneSpectrum (𝓞 E) → ValuationSubring Ω), (∀ v, IsPlaceOver (Av v) v) →
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O]
      [Module.Finite ℤ_[l] O], (l ≠ 2 ∨ InfinitePlace.nrRealPlaces E = 0) →
    ∀ (M : Type) [AddCommGroup M] [Module O M], Nonempty (M ≃ₗ[O] KO O) →
    ∀ (ρ : Representation O (G E Ω) M), (∀ g m, ρ g m = m) →
    ∀ S : Submodule O (H1z ρ),
      (∀ x ∈ S, ∃ z : coZ1s ρ, Submodule.mkQ _ z = x ∧ IsLocallyConstant (z : G E Ω → M)) →
      (∀ v, S ≤ unrH1 ρ (Ine (F := E) (Av v))) →
      Module.length O S ≤ Module.length O (O ⧸ Ideal.span {(l : O)}) * (padicValNat l (classNumber E) : ℕ∞)

def TopEx : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[p] O] [Module.Finite ℤ_[p] O], Function.Injective (algebraMap ℤ_[p] O) →
    ∃ (_ : TopologicalSpace O) (_ : TopologicalSpace (FractionRing O)) (_ : IsTopologicalAddGroup (FractionRing O))
      (_ : ContinuousSMul O (FractionRing O)), PadicCoeff p O ∧ FracTop O

structure Elem : Prop where
  padicInt : ∀ {p : ℕ} [Fact p.Prime], PadicCoeff p ℤ_[p]
  mulSub : ∀ {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
    {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M],
    IsFGTop O M → PadicCoeff p O → ∀ {a : O}, a ≠ 0 → IsOpen ((mulSub a M : Submodule O M) : Set M)
  contQuot : ∀ {O G V : Type} [CommRing O] [Group G] [TopologicalSpace G] [AddCommGroup V] [Module O V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] {ρ : Representation O G V}, ContAction ρ →
    ∀ (T : Submodule O V) (hT : StableUnder ρ T), ContAction (ρ.quotient T hT)
  swapCob : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    {VT VT' : Type}
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
    [ContinuousSMul O VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
    [ContinuousSMul O VT'] {G : Type} [Group G] [TopologicalSpace G] (D : LatData O G VT VT') (x : Z1 D.ρA) (t : Z1 D.ρTl') (c : G → KO O), Continuous c →
    (∀ g k, pairKO D.bT D.T (D.ρA g (x.1 k)) (t.1 g) = ((D.ε g : Oˣ) : O) • c k - c (g * k) + c g) →
    D.pr (Submodule.Quotient.mk x) (Submodule.Quotient.mk t) = 0
  shapeEquiv : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X : Type} [AddCommGroup X] [Module O X]
    (Hc F Hc' F' : Submodule O X) (d : ℕ),
    ((Hc ⧸ F.comap Hc.subtype) ≃ₗ[O] (Hc' ⧸ F'.comap Hc'.subtype)) → QuotShape Hc F d → QuotShape Hc' F' d
  memOL : ∀ {l : ℕ} [Fact l.Prime] (LL : Formalism.BasicNotions.Loc.FinExt l) (x : ↥LL.1),
    x ∈ Formalism.BasicNotions.Loc.OL LL ↔ ‖(x : Formalism.BasicNotions.Loc.Om l)‖ ≤ 1
  openOL : ∀ {l : ℕ} [Fact l.Prime] (LL : Formalism.BasicNotions.Loc.FinExt l),
    IsOpen (Set.range (algebraMap ↥(Formalism.BasicNotions.Loc.OL LL) ↥LL.1))

structure Core : Prop where
  dec : DecEquiv
  inv : InvIso
  fin : FinIso
  rat : RatIso
  int : IntIso
  jspan : JSpan
  nat : NatInvIso
  shape : ShapeG
  shapeUnr : ShapeUnr
  unr : UnrDec
  vhE : VhE
  top : TopEx
  elem : Elem

section Wrap
variable [hT2Core : Fact Core]

theorem exists_dec_equiv {p : ℕ} [Fact p.Prime] {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (A : ValuationSubring Ω) (hp : A.valuation (p : Ω) < 1) :
    ∃ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] K)
      (i : ↥(A.decompositionSubgroup F) ≃ₜ* GK p K),
      (∀ (O : Type) [CommRing O] (ε : ↥(A.decompositionSubgroup F) →* Oˣ),
        IsCycOn p (A.decompositionSubgroup F) ε → IsCyc p K (carry i ε)) ∧
      (∀ g : ↥(A.decompositionSubgroup F), i g ∈ Formalism.GaloisCohomology.inertiaK p K ↔ (g : Ω ≃ₐ[F] Ω) ∈ Ine (F := F) A) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), IsPlaceOver A v → Module.finrank ℚ_[p] K = locDeg v := hT2Core.out.dec A hp

theorem exists_invariants_iso {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)] {G : Type} [Group G] [TopologicalSpace G]
    (hK : FiniteDimensional ℚ_[p] K) (hO : PadicCoeff p O) (hF : FracTop O) (i : G ≃ₜ* GK p K) {ε : G →* Oˣ}
    (hε : IsCyc p K (carry i ε)) :
    ∃ (inv : H2 (twist ε (KO O)) ≃ₗ[O] KO O) (invF : H2 (twist ε (FractionRing O)) ≃ₗ[O] FractionRing O),
      ∀ z, inv (mapH2 (twist ε (FractionRing O)) (twist ε (KO O)) (toKO O) toKO_cont (toKO_equiv ε) z) = toKO O (invF z) :=
  hT2Core.out.inv hK hO hF i hε

theorem finite_H1_of_iso {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    {VT VT' : Type}
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
    [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
    [ContinuousSMul O VT'] [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT'] {G : Type} [Group G] [TopologicalSpace G]
    (hK : FiniteDimensional ℚ_[p] K) (hO : PadicCoeff p O) (i : G ≃ₜ* GK p K) {D : LatData O G VT VT'} (hD : RealLatG i D) :
    Module.Finite O (H1 D.ρTl') := hT2Core.out.fin hK hO i hD

theorem tate_integral_iso {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    {VT VT' : Type}
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
    [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
    [ContinuousSMul O VT'] [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT'] {G : Type} [Group G] [TopologicalSpace G]
    (hK : FiniteDimensional ℚ_[p] K) (hO : PadicCoeff p O) (hF : FracTop O) (i : G ≃ₜ* GK p K) {D : LatData O G VT VT'}
    (hD : RealLatG i D) (hi : Function.Injective D.inv) (x : H1 D.ρA) (hx : ∀ t, D.pr x t = 0) : x = 0 :=
  hT2Core.out.int hK hO hF i hD hi x hx

theorem tate_rational_frac {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    {VT VT' : Type}
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
    [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
    [ContinuousSMul O VT'] [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT'] {G : Type} [Group G] [TopologicalSpace G]
    (hK : FiniteDimensional ℚ_[p] K) (hO : PadicCoeff p O) (hF : FracTop O) (i : G ≃ₜ* GK p K) {D : LatData O G VT VT'}
    (hD : RealLatG i D) (hi : Function.Injective D.invF)
    [Module (FractionRing O) (H1 D.ρT)] [IsScalarTower O (FractionRing O) (H1 D.ρT)]
    [Module (FractionRing O) (H1 D.ρT')] [IsScalarTower O (FractionRing O) (H1 D.ρT')]
    (f : H1 D.ρT' →ₗ[FractionRing O] FractionRing O) :
    ∃ a, ∀ b, fracBilinear ((cupFG D).compr₂ D.invF) a b = f b :=
  hT2Core.out.rat hK hO hF i hD hi (f.restrictScalars O)

theorem j'_span_iso {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    {VT VT' : Type}
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
    [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
    [ContinuousSMul O VT'] [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT'] {G : Type} [Group G] [TopologicalSpace G]
    (hO : PadicCoeff p O) (hF : FracTop O) (i : G ≃ₜ* GK p K) {D : LatData O G VT VT'} (hD : RealLatG i D) (y : H1 D.ρT') :
    ∃ c : O, c ≠ 0 ∧ c • y ∈ LinearMap.range D.j' := hT2Core.out.jspan hO hF i hD y

theorem natInv_all_iso {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] {G : Type} [Group G] [TopologicalSpace G]
    (hK : FiniteDimensional ℚ_[p] K) (hO : PadicCoeff p O) (i : G ≃ₜ* GK p K) {ε : G →* Oˣ} (hε : IsCyc p K (carry i ε)) :
    Nonempty (NatInv ε (fun M _ _ _ => IsFGTop O M)) := hT2Core.out.nat hK hO i hε

theorem quotShape_G {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)] {G : Type} [Group G] [TopologicalSpace G]
    (hK : FiniteDimensional ℚ_[p] K) (hO : PadicCoeff p O) (hF : FracTop O) (i : G ≃ₜ* GK p K) {ε : G →* Oˣ}
    (hε : IsCyc p K (carry i ε)) (e : ℕ) (he : 0 < e) {M : Type} [AddCommGroup M] [Module O M] (u : M ≃ₗ[O] KO O)
    (ρ : Representation O G M) (h : ∀ g m, ρ g m = ((((ε g) ^ e)⁻¹ : Oˣ) : O) • m) :
    QuotShape (HcLC ρ) ⊥ (Module.finrank ℚ_[p] K) := hT2Core.out.shape hK hO hF i hε e he u ρ h

theorem quotShape_G_unr {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)] {G : Type} [Group G] [TopologicalSpace G]
    (hK : FiniteDimensional ℚ_[p] K) (hO : PadicCoeff p O) (hF : FracTop O) (i : G ≃ₜ* GK p K)
    {M : Type} [AddCommGroup M] [Module O M] (u : M ≃ₗ[O] KO O) (ρ : Representation O G M) (h : ∀ g m, ρ g m = m)
    (I : Subgroup G) (hI : ∀ g, g ∈ I ↔ i g ∈ Formalism.GaloisCohomology.inertiaK p K) :
    QuotShape (HcLC ρ) (unrH1 ρ I) (Module.finrank ℚ_[p] K) := hT2Core.out.shapeUnr hK hO hF i u ρ h I hI

theorem padicCoeff_padicInt {p : ℕ} [Fact p.Prime] : PadicCoeff p ℤ_[p] := hT2Core.out.elem.padicInt

theorem IsFGTop.isOpen_mulSub {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
    {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    (h : IsFGTop O M) (hO : PadicCoeff p O) {a : O} (ha : a ≠ 0) : IsOpen ((mulSub a M : Submodule O M) : Set M) :=
  hT2Core.out.elem.mulSub h hO ha

theorem contAction_quotient {O G V : Type} [CommRing O] [Group G] [TopologicalSpace G] [AddCommGroup V] [Module O V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] {ρ : Representation O G V} (h : ContAction ρ)
    (T : Submodule O V) (hT : StableUnder ρ T) : ContAction (ρ.quotient T hT) := hT2Core.out.elem.contQuot h T hT

theorem pr_eq_zero_of_swap_cob {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    {VT VT' : Type}
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
    [ContinuousSMul O VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
    [ContinuousSMul O VT'] {G : Type} [Group G] [TopologicalSpace G] (D : LatData O G VT VT') (x : Z1 D.ρA) (t : Z1 D.ρTl') (c : G → KO O)
    (hc : Continuous c)
    (h : ∀ g k, pairKO D.bT D.T (D.ρA g (x.1 k)) (t.1 g) = ((D.ε g : Oˣ) : O) • c k - c (g * k) + c g) :
    D.pr (Submodule.Quotient.mk x) (Submodule.Quotient.mk t) = 0 := hT2Core.out.elem.swapCob D x t c hc h

theorem quotShape_of_equiv {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X : Type} [AddCommGroup X] [Module O X]
    (Hc F Hc' F' : Submodule O X) (d : ℕ) (e : (Hc ⧸ F.comap Hc.subtype) ≃ₗ[O] (Hc' ⧸ F'.comap Hc'.subtype))
    (h : QuotShape Hc F d) : QuotShape Hc' F' d := hT2Core.out.elem.shapeEquiv Hc F Hc' F' d e h

theorem GlobAlg.mem_OL {l : ℕ} [Fact l.Prime] (LL : Formalism.BasicNotions.Loc.FinExt l) (x : ↥LL.1) :
    x ∈ Formalism.BasicNotions.Loc.OL LL ↔ ‖(x : Formalism.BasicNotions.Loc.Om l)‖ ≤ 1 := hT2Core.out.elem.memOL LL x

theorem GlobAlg.isOpen_range_OL {l : ℕ} [Fact l.Prime] (LL : Formalism.BasicNotions.Loc.FinExt l) :
    IsOpen (Set.range (algebraMap ↥(Formalism.BasicNotions.Loc.OL LL) ↥LL.1)) := hT2Core.out.elem.openOL LL

end Wrap

theorem quotShape_congr {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X : Type} [AddCommGroup X] [Module O X]
    (Hc F F' : Submodule O X) (d : ℕ) (h : ∀ x ∈ Hc, x ∈ F ↔ x ∈ F') (hs : QuotShape Hc F d) : QuotShape Hc F' d := by
  have e : F.comap Hc.subtype = F'.comap Hc.subtype := Submodule.ext fun x => h x.1 x.2
  unfold QuotShape at hs ⊢
  rw [← e]
  exact hs

theorem tate_compat_iso {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    {VT VT' : Type}
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
    [ContinuousSMul O VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
    [ContinuousSMul O VT'] {G : Type} [Group G] [TopologicalSpace G] (D : LatData O G VT VT') (hc : D.InvCompat) (a : H1 D.ρT) (t : H1 D.ρTl') :
    D.pr (D.q a) t = Submodule.Quotient.mk (D.invF (cupFG D a (D.j' t))) := by
  have h : D.pr (D.q a) t = D.inv (mapH2 (twist D.ε (FractionRing O)) (twist D.ε (KO O)) (toKO O) toKO_cont
      (toKO_equiv D.ε) (cupProductH1H1 D.ρT D.ρT' (twist D.ε (FractionRing O)) D.bT D.contbT D.eqT D.contT' a (D.j' t))) := by
    induction a using Submodule.Quotient.induction_on with
    | H a =>
      induction t using Submodule.Quotient.induction_on with
      | H t => rfl
  rw [h, hc]
  rfl

end ReciprocityTheory.ChartRestriction.T2

end
