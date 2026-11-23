import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.DualSide

section Anti

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [TopologicalSpace G]
  {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
  {M' : Type*} [AddCommGroup M'] [Module R M'] [TopologicalSpace M']
  [IsTopologicalAddGroup M'] [ContinuousConstSMul R M']
  {P : Type*} [AddCommGroup P] [Module R P] [TopologicalSpace P]
  [IsTopologicalAddGroup P] [ContinuousConstSMul R P]

theorem cupH11_anticomm (rho : Representation R G M) (rho' : Representation R G M')
    (rhoP : Representation R G P) (b : M →ₗ[R] M' →ₗ[R] P)
    (hb : Continuous fun p : M × M' => b p.1 p.2)
    (hbe : ∀ g x y, b (rho g x) (rho' g y) = rhoP g (b x y))
    (hb' : Continuous fun p : M' × M => b.flip p.1 p.2)
    (hbe' : ∀ g y x, b.flip (rho' g y) (rho g x) = rhoP g (b.flip y x))
    (h : ContAction rho) (h' : ContAction rho') (x : H1 rho) (y : H1 rho') :
    cupProductH1H1 rho' rho rhoP b.flip hb' hbe' h y x = -cupProductH1H1 rho rho' rhoP b hb hbe h' x y := by
  induction x using Submodule.Quotient.induction_on with | H x =>
  induction y using Submodule.Quotient.induction_on with | H y =>
  rw [eq_neg_iff_add_eq_zero]
  change Submodule.Quotient.mk (cupCocycleZ1Z1 rho' rho rhoP b.flip hb' hbe' h y x +
    cupCocycleZ1Z1 rho rho' rhoP b hb hbe h' x y) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  refine (separated_dvr_second_cohomology_mem _ _).2 ⟨fun g => -b (x.1 g) (y.1 g), (hb.comp (x.2.1.prodMk y.2.1)).neg, ?_⟩
  funext p
  obtain ⟨g, k⟩ := p
  change _ = b (rho g (x.1 k)) (y.1 g) + b (x.1 g) (rho' g (y.1 k))
  simp only [d1_apply, map_neg, ← hbe, x.2.2 g k, y.2.2 g k, map_add, LinearMap.add_apply]
  abel

theorem mapH1_bijective (rho : Representation R G M) (rho' : Representation R G M')
    (u : M ≃ₗ[R] M') (hu : Continuous u.toLinearMap) (hu' : Continuous u.symm.toLinearMap)
    (he : ∀ g m, u.toLinearMap (rho g m) = rho' g (u.toLinearMap m)) :
    Function.Bijective (mapH1 rho rho' u.toLinearMap hu he) := by
  have he' : ∀ g m, u.symm.toLinearMap (rho' g m) = rho g (u.symm.toLinearMap m) := fun g m => by
    apply u.injective
    have := he g (u.symm m)
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at this ⊢
    exact this.symm
  refine Function.bijective_iff_has_inverse.2 ⟨mapH1 rho' rho u.symm.toLinearMap hu' he',
    fun x => ?_, fun x => ?_⟩
  · induction x using Submodule.Quotient.induction_on with
    | H z => exact congrArg Submodule.Quotient.mk (Subtype.ext (funext fun g => u.symm_apply_apply _))
  · induction x using Submodule.Quotient.induction_on with
    | H z => exact congrArg Submodule.Quotient.mk (Subtype.ext (funext fun g => u.apply_symm_apply _))

end Anti

section Dual

variable {R : Type*} [CommRing R] {Γ : Type*} [Group Γ] {M : Type*} [AddCommGroup M] [Module R M]

theorem finite_TDual [Finite R] [Finite M] : Finite (TDual R M) :=
  Finite.of_injective _ (DFunLike.coe_injective (F := TDual R M))

def evalBidual : M →ₗ[R] TDual R (TDual R M) := evalPair

@[simp] theorem twistedDual_evalBidual_apply (m : M) (φ : TDual R M) :
    (evalBidual m : TDual R (TDual R M)) φ = φ m := rfl

theorem evalBidual_equiv (χ : Γ →* Rˣ) (rho : Representation R Γ M) (g : Γ) (m : M) :
    evalBidual (rho g m) = twDual χ (twDual χ rho) g (evalBidual m) := by
  ext φ
  simp only [twistedDual_evalBidual_apply, twDual_apply, inv_inv, map_inv]
  rw [← mul_assoc, Units.mul_inv, one_mul]

variable [TopologicalSpace R] [DiscreteTopology R] [TopologicalSpace M] [DiscreteTopology M]

theorem contAction_twDual [TopologicalSpace Γ] [ContinuousInv Γ] [Finite M] {χ : Γ →* Rˣ}
    {rho : Representation R Γ M} (hχ : ContAction (charRep χ)) (h : ContAction rho) :
    ContAction (twDual χ rho) := by
  have h1 : Continuous fun (p : Γ × TDual R M) (m : M) => twDual χ rho p.1 p.2 m :=
    continuous_pi fun m => hχ.comp (continuous_fst.prodMk
      ((continuous_of_discreteTopology (f := fun q : TDual R M × M => q.1 q.2)).comp
        (continuous_snd.prodMk (h.comp (continuous_fst.inv.prodMk continuous_const)))))
  exact (IsLocallyConstant.desc _ (fun (φ : TDual R M) (m : M) => φ m)
    ((IsLocallyConstant.iff_continuous _).2 h1) DFunLike.coe_injective).continuous

variable {D : Type*} [Group D] [TopologicalSpace D]

def evalH1 (χ : D →* Rˣ) (rho : Representation R D M) : H1 rho →ₗ[R] H1 (twDual χ (twDual χ rho)) :=
  mapH1 rho _ evalBidual continuous_of_discreteTopology (evalBidual_equiv χ rho)

theorem cup11_res_evalH1 [TopologicalSpace Γ] (χ : Γ →* Rˣ) (rho : Representation R Γ M)
    (φ : D →* Γ) (hφ : Continuous φ) (h : ContAction (rho.comp φ))
    (h' : ContAction ((twDual χ rho).comp φ)) (x : H1 rho) (y : H1 ((twDual χ rho).comp φ)) :
    cupH1H1TwistedDual χ (twDual χ rho) φ h' (resH1 (twDual χ (twDual χ rho)) φ hφ (evalH1 χ rho x)) y =
      -cupH1H1TwistedDual χ rho φ h y (resH1 rho φ hφ x) := by
  have e := cupH11_anticomm ((twDual χ rho).comp φ) (rho.comp φ) ((charRep χ).comp φ) evalPair.flip
    continuous_of_discreteTopology (fun g y x => evalPair_equiv χ rho (φ g) x y)
    continuous_of_discreteTopology (fun g x y => evalPair_equiv χ rho (φ g) x y) h' h y
    (resH1 rho φ hφ x)
  refine Eq.trans ?_ e
  induction x using Submodule.Quotient.induction_on with | H x =>
  induction y using Submodule.Quotient.induction_on with | H y =>
  rfl

end Dual

theorem evalH1_bijective {n : ℕ} [NeZero n] {Γ : Type*} [Group Γ] [TopologicalSpace Γ] {M : Type}
    [AddCommGroup M] [Module (ZMod n) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (χ : Γ →* (ZMod n)ˣ) (rho : Representation (ZMod n) Γ M) :
    Function.Bijective (evalH1 χ rho) :=
  mapH1_bijective rho _ (LinearEquiv.ofBijective (evalBidual (R := ZMod n) (M := M))
    (GlobalTheory.TateTop.eval_bijective (n := n) (M := M))) continuous_of_discreteTopology
    continuous_of_discreteTopology (evalBidual_equiv χ rho)

section Global

open GlobalTheory.Published GlobalTheory.Published.PoitouTate

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {l : ℕ} [Fact l.Prime] {r : ℕ} {S : Finset (HeightOneSpectrum (𝓞 F))}
  {Av : S → ValuationSubring Ω}
  {μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ}
  {j : ∀ v : S, H2 ((charRep μ).comp (locFam S Av v)) →ₗ[ZMod (l ^ r)] ZMod (l ^ r)}
  {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M]
  [DiscreteTopology M]
  {ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M}

omit [TopologicalSpace M] [DiscreteTopology M] in
theorem finite_TDual_pow : Finite (TDual (ZMod (l ^ r)) M) :=
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  finite_TDual

theorem mem_range_loc1_twDual_iff (hρ : ContAction ρ) {hρ' : ContAction (twDual μ ρ)}
    (h : NineTermExact S Av μ j (twDual μ ρ) hρ')
    (y : ∀ v : S, H1 ((twDual μ ρ).comp (locFam S Av v))) :
    y ∈ LinearMap.range (loc1 S Av (twDual μ ρ)) ↔ ∀ x : H1 ρ,
      ∑ v : S, j v (cupH1H1TwistedDual μ ρ (locFam S Av v) (hρ.comp' (continuous_locFam S Av v)) (y v)
        (resH1 ρ (locFam S Av v) (continuous_locFam S Av v) x)) = 0 := by
  have : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  rw [h.mem_range_localization_H1_iff, (evalH1_bijective μ ρ).2.forall]
  refine forall_congr' fun x => ?_
  simp only [cup11_res_evalH1 μ ρ _ _ (hρ.comp' (continuous_locFam S Av _)), map_neg,
    Finset.sum_neg_distrib, neg_eq_zero]

end Global

open GlobalTheory.Published GlobalTheory.Published.PoitouTate in

theorem exact_annihilators (h : PoitouTateTotallyComplex)
    (F Ω : Type) [Field F] [NumberField F] [IsTotallyComplex F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (hr : 0 < r) (ζ : Ω)
    (hζ : IsPrimitiveRoot ζ (l ^ r)) :
    ∃ inv : InvFam F Ω l r, IsLocalInvariants ζ inv ∧
    ∀ (S : Finset (HeightOneSpectrum (𝓞 F))), ContainsAbove S l →
    ∀ (Av : S → ValuationSubring Ω), (∀ v, IsPlaceOver (Av v) v.1) →
    ∀ (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ)
      (hμ : μ.comp (toGS Ω _) = cycMod F Ω l r),
    ∀ (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M]
      [DiscreteTopology M]
      (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
      (hρ : ContAction ρ),
      (∀ x : ∀ v : S, H1 (ρ.comp (locFam S Av v)),
        x ∈ LinearMap.range (loc1 S Av ρ) ↔ ∀ y : H1 (twDual μ ρ),
          ∑ v : S, invAt S Av μ hμ inv v (cupH1H1TwistedDual μ ρ (locFam S Av v)
            (hρ.comp' (continuous_locFam S Av v))
            (resH1 (twDual μ ρ) (locFam S Av v) (continuous_locFam S Av v) y) (x v)) = 0) ∧
      (∀ y : ∀ v : S, H1 ((twDual μ ρ).comp (locFam S Av v)),
        y ∈ LinearMap.range (loc1 S Av (twDual μ ρ)) ↔ ∀ x : H1 ρ,
          ∑ v : S, invAt S Av μ hμ inv v (cupH1H1TwistedDual μ ρ (locFam S Av v)
            (hρ.comp' (continuous_locFam S Av v)) (y v)
            (resH1 ρ (locFam S Av v) (continuous_locFam S Av v) x)) = 0) := by
  obtain ⟨inv, hinv, h⟩ := h F Ω l r hr ζ hζ
  refine ⟨inv, hinv, fun S hS Av hA μ hμ M _ _ _ _ _ ρ hρ => ⟨?_, ?_⟩⟩
  · exact (h S hS Av hA μ hμ M ρ hρ).1.mem_range_localization_H1_iff
  · have := finite_TDual_pow (l := l) (r := r) (M := M)
    exact mem_range_loc1_twDual_iff hρ (h S hS Av hA μ hμ _ (twDual μ ρ)
      (contAction_twDual (contAction_charRep hμ) hρ)).1

end GlobalTheory.DualSide
