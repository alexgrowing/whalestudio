import Formalism.AdmissibleDesigns.RowTopOf
import Formalism.AdmissibleDesigns.FiniteClassesLocalEq
import Formalism.AdmissibleDesigns.EKSymmCont

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

set_option linter.style.haveILetI false

open Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.KRowA

open Formalism.MainNotions.N.KHf Module Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.RepresentationBoundsCohomology.FIN Formalism.NG Formalism.RepresentationBoundsCohomology.BR
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)

section Gen

theorem sub_of_fam {LL : Type} [Field LL] {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module LL V]
    [FiniteDimensional LL V] {ρ : Representation LL G V} {ιx : Type} {k : ℕ}
    {Ms : ιx → G → Matrix (Fin k) (Fin k) LL} {I : Type} (xx : I → ιx)
    (Ψ : I → V →ₗ[LL] (Fin k → LL)) (hinj : ∀ v, (∀ a, Ψ a v = 0) → v = 0)
    (heq : ∀ a g v, Ψ a (ρ g v) = (Ms (xx a) g).mulVec (Ψ a v)) : IsSubOfSums ρ Ms := by
  obtain ⟨m, xs, hxs⟩ := KLift.fin_sel Ψ hinj
  refine ⟨m, xx ∘ xs, LinearMap.pi fun a => Ψ (xs a), fun v w hvw => ?_, fun g v => funext fun a => heq _ g v⟩
  rw [← sub_eq_zero]
  refine hxs _ fun a => ?_
  rw [map_sub, sub_eq_zero]
  exact congrFun hvw a

theorem orb_of_sub {LL : Type} [Field LL] [TopologicalSpace LL] [IsTopologicalRing LL] {G : Type} [Group G]
    [TopologicalSpace G] {V : Type} [AddCommGroup V] [Module LL V] [TopologicalSpace V] [IsModuleTopology LL V]
    [ContinuousAdd V] [ContinuousSMul LL V]
    {ρ : Representation LL G V} {ιx : Type} {k : ℕ} {Ms : ιx → G → Matrix (Fin k) (Fin k) LL}
    (h : IsSubOfSums ρ Ms) (hMs : ∀ x, Continuous (Ms x)) (v : V) : Continuous fun g => ρ g v := by
  obtain ⟨m, xs, φ, hφ, heq⟩ := h
  exact KLift.cont_of_inj xs φ hφ heq hMs v

end Gen

section Fin

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X' d : Type} [Fintype d] [DecidableEq d]
  {R' : Subalgebra O (X' → Matrix d d (FractionRing O))}

theorem r_free [Module.Finite O R'] : Module.Free O R' := by
  haveI h1 : NoZeroSMulDivisors O (FractionRing O) := ⟨fun {c x} h => by
    rw [Algebra.smul_def] at h
    rcases mul_eq_zero.1 h with hc | hx
    · exact Or.inl ((IsFractionRing.injective O (FractionRing O)) (by rw [hc, map_zero]))
    · exact Or.inr hx⟩
  haveI h2a : NoZeroSMulDivisors O (d → FractionRing O) := Pi.noZeroSMulDivisors _
  haveI h2 : NoZeroSMulDivisors O (Matrix d d (FractionRing O)) := Pi.noZeroSMulDivisors _
  haveI h3 : NoZeroSMulDivisors O (X' → Matrix d d (FractionRing O)) := Pi.noZeroSMulDivisors _
  haveI h4 : NoZeroSMulDivisors O R' := ⟨fun {c x} h => by
    have h' : c • (x : X' → Matrix d d (FractionRing O)) = 0 := congrArg Subtype.val h
    rcases smul_eq_zero.1 h' with hc | hx
    · exact Or.inl hc
    · exact Or.inr (Subtype.ext hx)⟩
  exact Module.free_of_finite_type_torsion_free'

theorem idempotent_part_finite [Module.Finite O R'] (e₁ : R') : Module.Finite O (FirstSummandSubmodule O e₁) := by
  exact Module.Finite.of_injective (FirstSummandSubmodule O e₁).subtype Subtype.val_injective

theorem idempotent_part_free [Module.Finite O R'] (e₁ : R') : Module.Free O (FirstSummandSubmodule O e₁) := by
  haveI := idempotent_part_finite (O := O) (R' := R') e₁
  haveI h1 : NoZeroSMulDivisors O (FractionRing O) := ⟨fun {c x} h => by
    rw [Algebra.smul_def] at h
    rcases mul_eq_zero.1 h with hc | hx
    · exact Or.inl ((IsFractionRing.injective O (FractionRing O)) (by rw [hc, map_zero]))
    · exact Or.inr hx⟩
  haveI h2a : NoZeroSMulDivisors O (d → FractionRing O) := Pi.noZeroSMulDivisors _
  haveI h2 : NoZeroSMulDivisors O (Matrix d d (FractionRing O)) := Pi.noZeroSMulDivisors _
  haveI h3 : NoZeroSMulDivisors O (X' → Matrix d d (FractionRing O)) := Pi.noZeroSMulDivisors _
  haveI h4 : NoZeroSMulDivisors O R' := ⟨fun {c x} h => by
    have h' : c • (x : X' → Matrix d d (FractionRing O)) = 0 := congrArg Subtype.val h
    rcases smul_eq_zero.1 h' with hc | hx
    · exact Or.inl hc
    · exact Or.inr (Subtype.ext hx)⟩
  haveI h5 : NoZeroSMulDivisors O (FirstSummandSubmodule O e₁) := ⟨fun {c x} h => by
    have h' : c • (x : R') = 0 := congrArg Subtype.val h
    rcases smul_eq_zero.1 h' with hc | hx
    · exact Or.inl hc
    · exact Or.inr (Subtype.ext hx)⟩
  exact Module.free_of_finite_type_torsion_free'

end Fin

section Rec

attribute [local instance 2000] K.Topo.fracTopology K.Topo.rTopology

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))

def kap1 : FirstSummandSubmodule (D.nd.O i) Dd.e₁ →ₗ[D.nd.O i]
    (Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) where
  toFun p := (((p : Dd.R')) : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i)))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem lattice_inclusion_injective : Function.Injective (kap1 i Dd) := by
  intro a b h
  exact Subtype.ext (Subtype.ext h)

theorem idempotent_part_representation_at
    (hr' : ∀ g x', ((Dd.r g : Dd.R') : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) x' =
      (rO D.nd i r (Dd.p x') g).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))))
    (hsm : ∀ (f : Dd.T') (a : Dd.R') x', ((f • a : Dd.R') : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV)
      (FractionRing (D.nd.O i))) x' = algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) ((f : Dd.X' → D.nd.O i) x') •
        (a : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) x')
    (hχ : ∀ g x', (((Dd.χ g : (Dd.T')ˣ) : Dd.T') : Dd.X' → D.nd.O i) x' = (chiU D.nd i 1 g : D.nd.O i))
    (g : GE D.nd) (p : FirstSummandSubmodule (D.nd.O i) Dd.e₁) (x' : Dd.X') :
    kap1 i Dd (firstSummandRep (D.nd.O i) Dd.r Dd.χ Dd.e₁ (epsU D.nd i) g p) x' =
      algebraMap (D.nd.O i) (FractionRing (D.nd.O i))
          ((chiU D.nd i 1 g : D.nd.O i) * ((epsU D.nd i g : (D.nd.O i)ˣ) : D.nd.O i)) •
        (kap1 i Dd p x' * (rO D.nd i r (Dd.p x') g⁻¹).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))) := by
  show (((((epsU D.nd i g : (D.nd.O i)ˣ) : D.nd.O i) • (((Dd.χ g : (Dd.T')ˣ) : Dd.T') •
    ((p : Dd.R') * Dd.r g⁻¹)) : Dd.R')) : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) x' = _
  rw [Subalgebra.coe_smul, Pi.smul_apply, hsm, hχ, Subalgebra.coe_mul, Pi.mul_apply, hr', map_mul, mul_smul,
    ← algebraMap_smul (FractionRing (D.nd.O i)) ((epsU D.nd i g : (D.nd.O i)ˣ) : D.nd.O i), smul_comm]
  rfl

theorem locC_apply {n : ℕ} (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) {k : ℕ}
    (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i _ hn) (a b : Fin k) :
    TruncatedSeriesCountingIdentities.locC (TruncatedSeriesCountingIdentities.CoefExt.self i _ hn) M g a b = eK (D.nbr i _ hn) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))
      (M ((Br.iota D.nbr i _ hn g : Gw D.nd (K.plOf i dc n)) : GE D.nd) a b)) := by
  rw [← KLift.heO_br i dc hn]
  rfl

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem rowSub_at
    (hr' : ∀ g x', ((Dd.r g : Dd.R') : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) x' =
      (rO D.nd i r (Dd.p x') g).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))))
    (hsm : ∀ (f : Dd.T') (a : Dd.R') x', ((f • a : Dd.R') : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV)
      (FractionRing (D.nd.O i))) x' = algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) ((f : Dd.X' → D.nd.O i) x') •
        (a : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) x')
    (hχ : ∀ g x', (((Dd.χ g : (Dd.T')ˣ) : Dd.T') : Dd.X' → D.nd.O i) x' = (chiU D.nd i 1 g : D.nd.O i))
    [Module.Finite (D.nd.O i) (FirstSummandSubmodule (D.nd.O i) Dd.e₁)] [Module.Free (D.nd.O i) (FirstSummandSubmodule (D.nd.O i) Dd.e₁)]
    {n : ℕ} (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) :
    IsSubOfSums (repL (eK (D.nbr i _ hn))
        (locRep (resRep (firstSummandRep (D.nd.O i) Dd.r Dd.χ Dd.e₁ (epsU D.nd i)) (Γn i dc n))) (Br.iota D.nbr i _ hn))
      (fun x : D.nd.X i => ⇑(TruncatedSeriesCountingIdentities.locC (TruncatedSeriesCountingIdentities.CoefExt.self i _ hn) (rDuO D.nd i r x))) := by
  set ρP := resRep (firstSummandRep (D.nd.O i) Dd.r Dd.χ Dd.e₁ (epsU D.nd i)) (Γn i dc n) with hρP
  set e := eK (D.nbr i _ hn)
  let Λ := liftK (V := Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) (kap1 i Dd)
  have hΛs : ∀ m (s : nonZeroDivisors (D.nd.O i)), (s : D.nd.O i) • Λ (LocalizedModule.mk m s) = kap1 i Dd m := by
    intro m s
    rw [← map_smul, KLift.smul_mk, liftK_mkK]
  have hΛi : ∀ v, Λ v = 0 → v = 0 := by
    intro v hv
    induction v using LocalizedModule.induction_on with
    | h m s =>
      have h1 := hΛs m s
      rw [hv, smul_zero] at h1
      rw [lattice_inclusion_injective i Dd (h1.symm.trans (map_zero (kap1 i Dd)).symm), LocalizedModule.zero_mk]
  have hΛe : ∀ (γ : ↥(Γn i dc n)) v x', Λ (locRep ρP γ v) x' =
      algebraMap (D.nd.O i) (FractionRing (D.nd.O i))
          ((chiU D.nd i 1 (γ : GE D.nd) : D.nd.O i) * ((epsU D.nd i (γ : GE D.nd) : (D.nd.O i)ˣ) : D.nd.O i)) •
        (Λ v x' * (rO D.nd i r (Dd.p x') (γ : GE D.nd)⁻¹).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))) := by
    intro γ v x'
    induction v using LocalizedModule.induction_on with
    | h m s =>
      have h0 : locRep ρP γ (LocalizedModule.mk m s) = LocalizedModule.mk (ρP γ m) s := LocalizedModule.map_mk _ _ _ _
      rw [h0]
      apply KLift.smul_cancel s
      have h1 := congrFun (hΛs (ρP γ m) s) x'
      have h2 := congrFun (hΛs m s) x'
      rw [Pi.smul_apply] at h1 h2
      rw [h1, smul_comm, ← Matrix.smul_mul, h2]
      exact idempotent_part_representation_at i r Dd hr' hsm hχ (γ : GE D.nd) m x'
  let Ψ : Dd.X' × Fin D.R.nV → TrV e (MK (O := D.nd.O i) (FirstSummandSubmodule (D.nd.O i) Dd.e₁)) →ₗ[Br.LLw (D.nbr i _ hn)]
      (Fin D.R.nV → Br.LLw (D.nbr i _ hn)) := fun q =>
    { toFun := fun v j => e ((Λ (KLift.untr e v)) q.1 q.2 j)
      map_add' := fun v w => funext fun j => by
        show e ((Λ (KLift.untr e v + KLift.untr e w)) q.1 q.2 j) = _
        rw [map_add]
        simp [map_add]
      map_smul' := fun c v => funext fun j => by
        show e ((Λ (e.symm c • KLift.untr e v)) q.1 q.2 j) = c * e ((Λ (KLift.untr e v)) q.1 q.2 j)
        rw [smulK]
        simp [Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, map_mul] }
  haveI : FiniteDimensional (Br.LLw (D.nbr i _ hn)) (TrV e (MK (O := D.nd.O i) (FirstSummandSubmodule (D.nd.O i) Dd.e₁))) :=
    KLift.finDim_of_lat (Ow := Br.Ow (D.nbr i _ hn)) (Qp := ℚ_[D.nd.l i])
      (KLift.latOf e (D.nbr i _ hn).eO mkK (Br.iota D.nbr i _ hn) (KLift.heO_br i dc hn) (locRep ρP) ρP KLift.mkK_inj
        (fun γ m => (locRep_mkK _ γ m).symm) KLift.mkK_span)
  refine sub_of_fam (fun q => Dd.p q.1) Ψ (fun v hv => ?_) (fun q g v => ?_)
  · have h0 : Λ (KLift.untr e v) = 0 := by
      funext x'
      ext a b
      have := congrFun (hv (x', a)) b
      simpa [Ψ] using this
    exact hΛi _ h0
  · funext j
    have key : ∀ γ : ↥(Γn i dc n), (γ : GE D.nd) = ((Br.iota D.nbr i _ hn g : Gw D.nd (K.plOf i dc n)) : GE D.nd) →
        e ((Λ (locRep ρP γ (KLift.untr e v))) q.1 q.2 j) =
          (TruncatedSeriesCountingIdentities.locC (TruncatedSeriesCountingIdentities.CoefExt.self i _ hn) (rDuO D.nd i r (Dd.p q.1)) g).mulVec (Ψ q v) j := by
      intro γ hγ
      rw [hΛe, hγ]
      simp only [Matrix.mulVec, dotProduct, locC_apply i dc hn, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul,
        Finset.mul_sum, map_sum, map_mul, Matrix.map_apply, rDuO, twistM, dualM, MonoidHom.coe_mk, OneHom.coe_mk,
        Matrix.transpose_apply, Ψ, LinearMap.coe_mk, AddHom.coe_mk]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [MonoidHom.mul_apply, Units.val_mul, map_mul]
      rw [show eK (D.nbr i _ hn) = e from rfl]
      have hc : ∀ x y z w : Br.LLw (D.nbr i _ hn), x * y * (z * w) = x * y * w * z := fun x y z w => by ring
      exact hc _ _ _ _
    exact key (Br.iota D.nbr i _ hn g) rfl

end Rec

end Formalism.MainNotions.N.KRowA

end
