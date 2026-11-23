import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSubFibreSubFib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsUnitNatCastStalk
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsConstStalk
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FinrankFiniteFlatTorsionSubschemeEqCardPoints
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtEigen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagFib.FibOrth

open GroundTheory.Heights₂.Heights LieTangent

section Form

variable {L : Type} [Field L]

theorem one_tmul_smul (σ : L →+* ℂ) {V : Type} [AddCommGroup V] [Module (𝓞 L) V] (r : 𝓞 L) (x : V) :
    (1 : ComplexAt σ) ⊗ₜ[𝓞 L] (r • x) = (σ (r : L)) • ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x) := by
  rw [tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul']
  congr 1

variable [NumberField L]

theorem core_span {R V F : Type} [CommRing R] [AddCommGroup V] [Module R V] [AddCommGroup F] [Module ℂ F]
    (C : InnerProductSpace.Core ℂ F) (f : V →+ F) (φ : R → ℂ) (hs : ∀ r x, f (r • x) = φ r • f x) (A A' : Set V)
    (h : ∀ x ∈ A, ∀ x' ∈ A', C.inner (f x) (f x') = 0) :
    ∀ x ∈ Submodule.span R A, ∀ x' ∈ Submodule.span R A', C.inner (f x) (f x') = 0 := by
  let c : PreInnerProductSpace.Core ℂ F := C.toCore
  intro x hx x' hx'
  induction hx using Submodule.span_induction with
  | mem a ha =>
    induction hx' using Submodule.span_induction with
    | mem b hb => exact h a ha b hb
    | zero => rw [map_zero]; exact InnerProductSpace.Core.inner_zero_right _
    | add u v _ _ hu hv =>
      rw [map_add]
      exact (InnerProductSpace.Core.inner_add_right _ _ _).trans (by rw [show _ = _ from hu, show _ = _ from hv, add_zero])
    | smul r u _ hu =>
      rw [hs]
      exact (InnerProductSpace.Core.inner_smul_right _ _).trans (by rw [show _ = _ from hu, mul_zero])
  | zero => rw [map_zero]; exact InnerProductSpace.Core.inner_zero_left _
  | add u v _ _ hu hv =>
    rw [map_add]
    exact (InnerProductSpace.Core.inner_add_left _ _ _).trans (by rw [show _ = _ from hu, show _ = _ from hv, add_zero])
  | smul r u _ hu =>
    rw [hs]
    exact (InnerProductSpace.Core.inner_smul_left _ _).trans (by rw [show _ = _ from hu, mul_zero])

theorem orth_sat (B : HermitianBundle.{0} L) (σ : L →+* ℂ) (A A' : Set B.carrier)
    (h : ∀ x ∈ A, ∀ x' ∈ A',
      (B.metric.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x) ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x') = 0)
    (x x' : B.carrier) (a a' : 𝓞 L) (ha : a ≠ 0) (ha' : a' ≠ 0) (hx : a • x ∈ Submodule.span (𝓞 L) A)
    (hx' : a' • x' ∈ Submodule.span (𝓞 L) A') :
    (B.metric.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x) ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x') = 0 := by
  let f : B.carrier →+ Fibre σ B.carrier :=
    { toFun := fun x => (1 : ComplexAt σ) ⊗ₜ[𝓞 L] x
      map_zero' := TensorProduct.tmul_zero _ _
      map_add' := fun x y => TensorProduct.tmul_add _ _ _ }
  have key := core_span (B.metric.form σ) f (fun r : 𝓞 L => σ (r : L)) (fun r x => one_tmul_smul σ r x) A A' h _ hx _ hx'
  let c : PreInnerProductSpace.Core ℂ (Fibre σ B.carrier) := (B.metric.form σ).toCore
  have ne : ∀ b : 𝓞 L, b ≠ 0 → σ (b : L) ≠ 0 := fun b hb =>
    (map_ne_zero σ).2 (by simpa using hb)
  have e : (B.metric.form σ).inner (f (a • x)) (f (a' • x')) =
      (starRingEnd ℂ) (σ (a : L)) * (σ (a' : L) * (B.metric.form σ).inner (f x) (f x')) := by
    rw [show f (a • x) = σ (a : L) • f x from one_tmul_smul σ a x,
      show f (a' • x') = σ (a' : L) • f x' from one_tmul_smul σ a' x']
    exact (InnerProductSpace.Core.inner_smul_left _ _).trans
      (congrArg _ (InnerProductSpace.Core.inner_smul_right _ _))
  rw [e] at key
  have h1 : (starRingEnd ℂ) (σ (a : L)) ≠ 0 := (map_ne_zero _).2 (ne a ha)
  exact (mul_eq_zero.1 ((mul_eq_zero.1 key).resolve_left h1)).resolve_left (ne a' ha')

end Form

section Eigen

theorem epsMul_eq (c : ℂ) : GlobalTheory.CompanionTheory.Ar.epsMul c = ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsScale c := rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K]
  {J : K → Type} {y : (Σ k, J k) → Ω}

theorem isLieEigen_of_gen (𝔐 : HodgeCpt Y S y) {L : Type} [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ 𝔐.X)
    (hp : genPt 𝔐.ξ ⤳ centre (spMap (algebraMap (𝓞 L) L) ≫ z))
    (g₀ : c.F →+* 𝔐.X.presheaf.stalk (centre (spMap (algebraMap (𝓞 L) L) ≫ z)))
    (hg : (genMap 𝔐.ξ ⟨_, hp⟩).comp g₀ = 𝔐.cst) (s : CMType H ⊕ CMType H) (U : Submodule Ω 𝔐.Li) (hU : U ≤ 𝔐.Vgen s)
    (σ : L →+* ℂ) {V : Type} [AddCommGroup V] [Module (𝓞 L) V] (MB : LieModel 𝔐.t.G z V) (x : V)
    (hx : x ∈ subGens 𝔐.M U z MB)
    (w : epsAt (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z) ⟶ 𝔐.t.G)
    (hw : MB.Lifts (σ.comp (algebraMap (𝓞 L) L)) (𝟙 𝔐.t.G.left) x w) :
    IsLieEigen 𝔐.t.act (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z)
      ((σ.comp ((Scheme.stalkClosedPointTo (spMap (algebraMap (𝓞 L) L) ≫ z)).hom.comp g₀)).comp (labelEmb c s)) w := by
  obtain ⟨e, he, v, hval, hl⟩ := hx
  have hσ : spMap σ ≫ spMap (algebraMap (𝓞 L) L) ≫ z = spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z := by
    rw [← Category.assoc]
    exact congrArg (· ≫ z) (spec_comp _ _)
  have hd : dualMap (σ.comp (algebraMap (𝓞 L) L)) = (dualMap σ).comp (dualMap (algebraMap (𝓞 L) L)) := by
    refine RingHom.ext fun a => ?_
    ext <;> simp
  have hw' : w = epsBase σ hσ ≫ v := by
    refine (left_eq_iff σ hσ w v).1 ?_
    have h1 : w.left = spMap (dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (MB.pt x).left := by
      simpa [LieModel.Lifts] using hw
    have h2 : v.left = spMap (dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt x).left := by
      simpa [LieModel.Lifts] using hl
    rw [h1, h2, hd, ← Category.assoc]
    exact congrArg (· ≫ (MB.pt x).left) (spec_comp _ _).symm
  subst hw'
  refine ⟨isTanAt_base σ hσ hval.isTanAt, fun a => ?_⟩
  have ev := GlobalTheory.CompanionTheory.Ar.FlagFib.valAt_eigen E H D l Xo c Y S Ω K J y 𝔐 L _ hp g₀ hg s e v a (hU he) hval
  have e1 : ((epsBase σ hσ ≫ v) ≫ 𝔐.t.act.act a).left =
      Spec.map (CommRingCat.ofHom (dualMap σ)) ≫ (v ≫ 𝔐.t.act.act a).left := rfl
  rw [e1, ev, ← Category.assoc, spec_dual_eps, Category.assoc]
  rfl

end Eigen

theorem orthAt_subFib : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (h : LieMetric 𝔐.M y), h.Orth 𝔐.t.act → ∀ (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ 𝔐.X) (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel 𝔐.t.G z B.carrier), IsFibre (fun z v w c => c = h.ip z v w) z B MB → ∀ (s s' : CMType H ⊕ CMType H), s ≠ s' → ∀ U U' : Submodule Ω 𝔐.Li, U ≤ 𝔐.Vgen s → U' ≤ 𝔐.Vgen s' → OrthAt B (FlagFib.subFib 𝔐.M U z MB) (FlagFib.subFib 𝔐.M U' z MB) := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J y 𝔐 h hO L _ _ z B MB hF s s' hss U U' hU hU' σ x hx x' hx'
  have hp : genPt 𝔐.ξ ⤳ centre (spMap (algebraMap (𝓞 L) L) ≫ z) := 𝔐.all _
  obtain ⟨g₀, hg⟩ := GlobalTheory.CompanionTheory.Ar.Flat.KonstReg.exists_const_stalk E H D l Xo c Y S Ω K J y 𝔐 ⟨_, hp⟩
    (fun n hn => isUnit_natCast_stalk 𝔐.X L _ n hn)
  classical
  let : Fintype (CMType H) := Fintype.ofFinite _
  let ι₀ : c.F →+* ℂ := σ.comp ((Scheme.stalkClosedPointTo (spMap (algebraMap (𝓞 L) L) ≫ z)).hom.comp g₀)
  have hinj := (GlobalTheory.CompanionTheory.Ar.LabelCount.labels_injective_card E H l c ℂ ι₀).1
  have hne : ι₀.comp (labelEmb c s) ≠ ι₀.comp (labelEmb c s') := fun e => hss (hinj e)
  obtain ⟨a, ha, hax⟩ := hx
  obtain ⟨a', ha', hax'⟩ := hx'
  refine orth_sat B σ _ _ ?_ x x' a a' ha ha' hax hax'
  intro u hu u' hu'
  let w := epsBase (σ.comp (algebraMap (𝓞 L) L)) rfl ≫ MB.pt u
  let w' := epsBase (σ.comp (algebraMap (𝓞 L) L)) rfl ≫ MB.pt u'
  have hl : MB.Lifts (σ.comp (algebraMap (𝓞 L) L)) (𝟙 𝔐.t.G.left) u w := Category.comp_id _
  have hl' : MB.Lifts (σ.comp (algebraMap (𝓞 L) L)) (𝟙 𝔐.t.G.left) u' w' := Category.comp_id _
  have e1 := isLieEigen_of_gen 𝔐 z hp g₀ hg s U hU σ MB u hu w hl
  have e2 := isLieEigen_of_gen 𝔐 z hp g₀ hg s' U' hU' σ MB u' hu' w' hl'
  exact (hF σ u u' w w' hl hl').trans (hO _ _ _ w w' hne e1 e2)

end GlobalTheory.CompanionTheory.Ar.FlagFib.FibOrth
