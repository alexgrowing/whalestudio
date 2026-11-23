import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsDefs
import GroundTheory.ProfiniteCohomology.PoitouTate.PoitouTateNineTermGs

noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global ReciprocityTheory.Gal Formalism.ConjugateSelfDual

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

section Roots

variable {L : Type} [Field L] {N : ℕ} [NeZero N] (w : rootsOfUnity N L)

theorem rootsOfUnity_pow_N : w ^ N = 1 := by
  apply Subtype.ext
  rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
  exact (mem_rootsOfUnity N (w : Lˣ)).1 w.2

def rootOf : ZMod N →+ Additive (rootsOfUnity N L) where
  toFun c := Additive.ofMul (w ^ c.val)
  map_zero' := by simp
  map_add' a b := by
    show Additive.ofMul (w ^ (a + b).val) = Additive.ofMul (w ^ a.val) + Additive.ofMul (w ^ b.val)
    rw [← ofMul_mul, ← pow_add, ZMod.val_add]
    congr 1
    conv_rhs => rw [← Nat.mod_add_div (a.val + b.val) N, pow_add, pow_mul, rootsOfUnity_pow_N w,
      one_pow, mul_one]

theorem rootOf_apply (c : ZMod N) : rootOf w c = Additive.ofMul (w ^ c.val) := rfl

theorem rootOf_bijective (hw : IsPrimitiveRoot (((w : Lˣ) : L)) N) : Function.Bijective (rootOf w) := by
  have hwu : IsPrimitiveRoot w N := by
    rw [← IsPrimitiveRoot.coe_submonoidClass_iff, ← IsPrimitiveRoot.coe_units_iff]
    exact hw
  refine ⟨fun a b h => ?_, fun x => ?_⟩
  · have h' : w ^ a.val = w ^ b.val := Additive.ofMul.injective h
    exact ZMod.val_injective N (hwu.pow_inj (ZMod.val_lt a) (ZMod.val_lt b) h')
  · obtain ⟨i, hi, hx⟩ := hw.eq_pow_of_pow_eq_one
      (ξ := (((Additive.toMul x : rootsOfUnity N L) : Lˣ) : L)) (by
        have := (mem_rootsOfUnity N _).1 (Additive.toMul x).2
        rw [← Units.val_pow_eq_pow_val, this, Units.val_one])
    refine ⟨(i : ZMod N), ?_⟩
    rw [rootOf_apply, ZMod.val_natCast, Nat.mod_eq_of_lt hi]
    have : w ^ i = Additive.toMul x :=
      Subtype.ext (Units.ext (by rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val]; exact hx))
    rw [this]
    rfl

end Roots

section DualGen

variable {Γ H : Type} [Group Γ] [Group H] [TopologicalSpace Γ] [TopologicalSpace H] (θ : Γ ≃ₜ* H)
  {N : ℕ} [NeZero N]
  {M : Type} [AddCommGroup M] [Module (ZMod N) M] (ρ : Representation (ZMod N) Γ M)
  (χ : Γ →* (ZMod N)ˣ) (A D : Rep.{0} (ULift.{0} ℤ) H) (eM : M ≃+ A.V)
  (hM : ∀ g m, eM (ρ g m) = A.ρ (θ g) (eM m)) (rr : ZMod N ≃+ D.V)
  (hr : ∀ g c, D.ρ (θ g) (rr c) = rr ((χ g : ZMod N) * c))

include hM hr in

theorem dualGen : ∃ eD : TDual (ZMod N) M ≃+ (dualRep D A).V,
    (∀ g f, eD (twDual χ ρ g f) = (dualRep D A).ρ (θ g) (eD f)) ∧
      ∀ f m, (eD f : A.V →ₗ[ULift.{0} ℤ] D.V) (eM m) = rr (f m) := by
  let fwd : TDual (ZMod N) M → (A.V →ₗ[ULift.{0} ℤ] D.V) := fun f =>
    (uliftIntLinearEquivAddHom A.V D.V).symm
      (rr.toAddMonoidHom.comp (((f : M →ₗ[ZMod N] ZMod N)).toAddMonoidHom.comp eM.symm.toAddMonoidHom))
  let bwd : (A.V →ₗ[ULift.{0} ℤ] D.V) → TDual (ZMod N) M := fun φ =>
    (rr.symm.toAddMonoidHom.comp ((uliftIntLinearEquivAddHom A.V D.V φ).comp eM.toAddMonoidHom)).toZModLinearMap N
  let eD : TDual (ZMod N) M ≃+ (dualRep D A).V :=
    { toFun := fwd
      invFun := bwd
      left_inv := fun f => LinearMap.ext fun m => by
        show rr.symm (rr (f (eM.symm (eM m)))) = f m
        rw [AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
      right_inv := fun φ => LinearMap.ext fun a => by
        show rr (rr.symm (φ (eM (eM.symm a)))) = φ a
        rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
      map_add' := fun f f' => LinearMap.ext fun a => by
        show rr ((f + f') (eM.symm a)) = rr (f (eM.symm a)) + rr (f' (eM.symm a))
        rw [← map_add]
        rfl }
  refine ⟨eD, fun g f => ?_, fun f m => ?_⟩
  · refine LinearMap.ext fun a => ?_
    have h1 : eM.symm (A.ρ (θ g⁻¹) a) = ρ g⁻¹ (eM.symm a) := by
      apply eM.injective
      rw [AddEquiv.apply_symm_apply, hM, AddEquiv.apply_symm_apply]
    show rr ((twDual χ ρ g f) (eM.symm a)) = D.ρ (θ g) (rr (f (eM.symm (A.ρ (θ g)⁻¹ a))))
    rw [hr, ← map_inv, h1]
    rfl
  · show rr (f (eM.symm (eM m))) = rr (f m)
    rw [AddEquiv.symm_apply_apply]

end DualGen

theorem exists_root_of_primitive {L : Type} [Field L] {N : ℕ} (hN0 : N ≠ 0) {z : L}
    (hz : IsPrimitiveRoot z N) : ∃ w : rootsOfUnity N L, ((w : Lˣ) : L) = z :=
  ⟨⟨(hz.isUnit hN0).unit, (mem_rootsOfUnity _ _).2 (Units.ext (by
      rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, hz.pow_eq_one, Units.val_one]))⟩,
    IsUnit.unit_spec _⟩

set_option maxHeartbeats 1000000 in

theorem gsRoots_act_rootOf (Kf : FiniteSubfield) [NumberField Kf.1] [IsAlgClosure Kf.1 (AlgebraicClosure ℚ)]
    (S : Finset (HeightOneSpectrum (𝓞 Kf.1))) {l r : ℕ} [Fact l.Prime] [NeZero (l ^ r)]
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ (l ^ r))
    (e : GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))) ≃ₜ*
        galUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))
    (he : ∀ (σ : G Kf.1 (AlgebraicClosure ℚ))
        (y : maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))),
        ((e (toGS (AlgebraicClosure ℚ) _ σ) y :
          maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) :
            AlgebraicClosure ℚ) = σ (y : AlgebraicClosure ℚ))
    (μ : GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))) →* (ZMod (l ^ r))ˣ)
    (hμ : μ.comp (toGS (AlgebraicClosure ℚ) _) = cycMod Kf.1 (AlgebraicClosure ℚ) l r)
    (w : rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ)
      (S : Set (HeightOneSpectrum (𝓞 Kf.1)))))
    (hwv : (((w : (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ)
      (S : Set (HeightOneSpectrum (𝓞 Kf.1))))ˣ) : maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ)
      (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) : AlgebraicClosure ℚ) = ζ)
    (g : GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) (c : ZMod (l ^ r)) :
    (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)).ρ (e g) (rootOf w c) =
      rootOf w (((μ g : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) * c) := by
  induction g using QuotientGroup.induction_on with
  | H τ =>
  have hm : μ (toGS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))) τ) =
      cycMod Kf.1 (AlgebraicClosure ℚ) l r τ := DFunLike.congr_fun hμ τ
  have hτ : τ ζ = ζ ^ ((cycMod Kf.1 (AlgebraicClosure ℚ) l r τ : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)).val :=
    cyclotomicCharacter.spec (L := AlgebraicClosure ℚ) l
      (MulSemiringAction.toRingAut (G Kf.1 (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ) τ) ζ hζ.pow_eq_one
  have hζN : ζ ^ (l ^ r) = 1 := hζ.pow_eq_one
  have hmod : ∀ k : ℕ, ζ ^ (k % (l ^ r)) = ζ ^ k := fun k => by
    conv_rhs => rw [← Nat.mod_add_div k (l ^ r), pow_add, pow_mul, hζN, one_pow, mul_one]
  show (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)).ρ
      (e (toGS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))) τ)) (rootOf w c) =
    rootOf w (((μ (toGS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))) τ) :
      (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) * c)
  rw [hm]
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  apply Subtype.ext
  show ((e (toGS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))) τ)
      ((((w ^ c.val : rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))) : (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))ˣ) : maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))) : maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) : AlgebraicClosure ℚ) =
    ((((w ^ (((cycMod Kf.1 (AlgebraicClosure ℚ) l r τ : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) * c).val :
      rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))) : (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))ˣ) : maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) : AlgebraicClosure ℚ)
  rw [he τ, SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, IntermediateField.coe_pow, hwv,
    SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, IntermediateField.coe_pow, hwv, map_pow, hτ,
    ← pow_mul, ZMod.val_mul, hmod]

theorem natCast_pow_not_mem (Kf : FiniteSubfield) (S : Finset (HeightOneSpectrum (𝓞 Kf.1))) {l r : ℕ}
    [Fact l.Prime] (hS : ContainsAbove S l) :
    ∀ v ∉ (S : Set (HeightOneSpectrum (𝓞 Kf.1))), (((l ^ r : ℕ) : ℕ) : 𝓞 Kf.1) ∉ v.asIdeal := by
  intro v hv h
  apply hv
  have : ((l : ℕ) : 𝓞 Kf.1) ^ r ∈ v.asIdeal := by simpa using h
  exact Finset.mem_coe.2 (hS v (v.isPrime.mem_of_pow_mem r this))

set_option maxHeartbeats 1000000 in
theorem dualCmp' (Kf : FiniteSubfield) [NumberField Kf.1] [IsAlgClosure Kf.1 (AlgebraicClosure ℚ)]
    (S : Finset (HeightOneSpectrum (𝓞 Kf.1))) {l r : ℕ} [Fact l.Prime] (hr : 0 < r)
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ (l ^ r)) (hS : ContainsAbove S l)
    (e : GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))) ≃ₜ*
        galUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))
    (he : ∀ (σ : G Kf.1 (AlgebraicClosure ℚ))
        (y : maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))),
        ((e (toGS (AlgebraicClosure ℚ) _ σ) y :
          maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) :
            AlgebraicClosure ℚ) = σ (y : AlgebraicClosure ℚ))
    (μ : GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))) →* (ZMod (l ^ r))ˣ)
    (hμ : μ.comp (toGS (AlgebraicClosure ℚ) _) = cycMod Kf.1 (AlgebraicClosure ℚ) l r)
    {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M]
    (ρ : Representation (ZMod (l ^ r)) (GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) M)
    (A : Rep.{0} (ULift.{0} ℤ)
      (galUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))))
    [IsDiscreteRep A] (eM : M ≃+ A.V) (hM : ∀ g m, eM (ρ g m) = A.ρ (e g) (eM m)) :
    ∃ eD : TDual (ZMod (l ^ r)) M ≃+
        (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) A).V,
      (∀ g f, eD (twDual μ ρ g f) =
        (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) A).ρ (e g) (eD f)) ∧
      ∀ f m, ((((Additive.toMul ((eD f : A.V →ₗ[ULift.{0} ℤ] _) (eM m)) :
          rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ)
            (S : Set (HeightOneSpectrum (𝓞 Kf.1))))) :
          (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))ˣ) :
            maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) :
              AlgebraicClosure ℚ) = ζ ^ (f m).val := by
  classical
  have hN0 : l ^ r ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
  have hmem : ζ ∈ maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))) :=
    mem_maxUnramifiedOutside_of_pow_eq_one _ hN0 (natCast_pow_not_mem Kf S hS) hζ.pow_eq_one
  haveI : NeZero (l ^ r) := ⟨hN0⟩
  have hζL : IsPrimitiveRoot (⟨ζ, hmem⟩ : maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) (l ^ r) := by
    rw [← IsPrimitiveRoot.coe_submonoidClass_iff]
    exact hζ
  have hex := exists_root_of_primitive (L := maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) hN0 hζL
  refine Exists.elim hex (fun w hwv => ?_)
  have hwv' : (((w : (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))ˣ) : maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) : AlgebraicClosure ℚ) = ζ := congrArg Subtype.val hwv
  have hw : IsPrimitiveRoot (((w : (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))ˣ) : maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))) (l ^ r) := by
    rw [hwv]
    exact hζL
  let rr : ZMod (l ^ r) ≃+ (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)).V :=
    AddEquiv.ofBijective (rootOf w) (rootOf_bijective w hw)
  have hrr : ∀ c, rr c = rootOf w c := fun _ => rfl
  have hr : ∀ g c, (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)).ρ
      (e g) (rr c) = rr (((μ g : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) * c) := fun g c => by
    rw [hrr, hrr]
    exact gsRoots_act_rootOf Kf S ζ hζ e he μ hμ w hwv' g c
  refine Exists.elim (dualGen e ρ μ A
    (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) eM hM rr hr) (fun eD h => ?_)
  refine ⟨eD, h.1, fun f m => ?_⟩
  rw [h.2, hrr, rootOf_apply]
  show ((((w ^ (f m).val : rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))) : (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))ˣ) : maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) : AlgebraicClosure ℚ) =
    ζ ^ (f m).val
  rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, IntermediateField.coe_pow, hwv']

end PositivityTheory.Lit1.PTN
