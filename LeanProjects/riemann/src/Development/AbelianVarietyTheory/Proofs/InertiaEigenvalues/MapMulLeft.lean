import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ApplyLayers
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeAinfSandwichInvertPi
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachFunctorThreeLayerPropertiesEveryPlaceStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionXQFrobeniusStatement

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

namespace GlobalTheory.NL.SandArb

theorem map_mulLeft {O R M : Type} [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup M] [Module O M]
    (a : R) (z : R ⊗[O] M) :
    TensorProduct.map (LinearMap.mulLeft O a) LinearMap.id z = a • z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [TensorProduct.smul_tmul']
  | add x y hx hy => rw [map_add, smul_add, hx, hy]

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    {W : LocWach PD LL O v n} (E : EtTie W RA RW inclR φR gR πA) {s : ℕ} (hs : W.s = s)
    (hp : PD.p.Prime) (hL : LevLaws W) (hI : IoLaws E)

set_option maxHeartbeats 1000000 in

theorem of_layers {Zl : Type} [CommRing Zl] (zl : PowerSeries Zl →+* LetA O n) (h1 : IsCrys PD W.one.ρ)
    (hP : ∀ T, @Module.Projective (PowerSeries Zl) _ ↥(W.N T) _ (Module.compHom _ zl))
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (w : RA) (c : RW) (hc : c = inclR w)
    (hS : GlobalTheory.HWL.Sand (latOf E hs hp hL hI zl h1 hP) T w) :
    (∀ x ∈ W.N T, ∃ y : TW RA T, TWincl inclR T y =
        TensorProduct.map (LinearMap.mulLeft O c) LinearMap.id (E.jD T x)) ∧
      ∀ t : ↥T.L.T, (c ⊗ₜ[O] t : TW RW T) ∈ Submodule.span O {z : TW RW T | ∃ a : RA, ∃ y ∈ W.N T,
        z = TensorProduct.map (LinearMap.mulLeft O (inclR a)) LinearMap.id (E.jD T y)} := by
  subst hc
  have hN : nOf W T = W.N T := nOf_crys W hT
  have h1' : ∀ x ∈ nOf W T, ∃ y : TW RA T, TWincl inclR T y = inclR w • E.jD T x := hS.1
  have h2' : ∀ t : ↥T.L.T, inclR w • ((1 : RW) ⊗ₜ[O] t : TW RW T) ∈
      Submodule.span O {z : TW RW T | ∃ (a : RA), ∃ y ∈ nOf W T, z = inclR a • E.jD T y} := hS.2
  rw [hN] at h1' h2'
  refine ⟨fun x hx => ?_, fun t => ?_⟩
  · rw [map_mulLeft]; exact h1' x hx
  · have := h2' t
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one] at this
    simp only [map_mulLeft]
    exact this

end Generic

section
variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (H : LocHW l P) (F : LocFon l P AI H)
  {K : FinExt l} {s : ℕ} {LL : FinExt l} (h : Good K s LL) (hL : Laws H F h)

set_option maxHeartbeats 400000 in

theorem sand_layers (T : Lt K LL) (hT : IsCrys (P.PD K) T.ρ) :
    ∃ m : ℕ, GlobalTheory.HWL.Sand (LatL H F h hL) T ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (AI.π₁ ^ m) : RA LL) :=
  apply_layers H F h hL
    (fun _ _ _ _ Mo => ∃ m : ℕ, GlobalTheory.HWL.Sand Mo T ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (AI.π₁ ^ m) : RA LL))
    (fun Γ R I hI E Mo => GlobalTheory.HWL.SandProof.sandwich l P AI K s LL h Γ R I hI E Mo T hT)

theorem incl_pow (a : RA LL) (w : Ainf l) (ha : a = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] w) (m : ℕ) :
    inclR LL a ^ m = inclR LL ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (w ^ m)) := by
  rw [ha, ← map_pow, Algebra.TensorProduct.tmul_pow, one_pow]

end

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem sandwich : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∃ m : ℕ, (∀ x ∈ W.N T, ∃ y : TW (RA LL) T, TWincl (inclR LL) T y = TensorProduct.map (LinearMap.mulLeft ↥(OL LL) (inclR LL (E.io W.X) ^ m)) LinearMap.id (E.jD T x)) ∧ ∀ t : ↥T.L.T, ((inclR LL (E.io W.X) ^ m) ⊗ₜ[↥(OL LL)] t : TW (RW LL) T) ∈ Submodule.span ↥(OL LL) {z : TW (RW LL) T | ∃ a : RA LL, ∃ y ∈ W.N T, z = TensorProduct.map (LinearMap.mulLeft ↥(OL LL) (inclR LL a)) LinearMap.id (E.jD T y)} := by
  intro D HW F l _ K s LL h
  have hL : Laws (HW l) (F l) h := GlobalTheory.T.wach_functor_three_layer_properties_every_place D HW F l K s LL h
  have hX := (GlobalTheory.T.wachInclusion_X_Q_frobenius D HW F l K s LL h).1
  refine fun T hT => (sand_layers (HW l) (F l) h hL T hT).imp fun m hm => ?_
  exact of_layers ((F l).E K s LL h).tie ((HW l).W_s K s LL h) (p_prime (D.loc l) K) hL.lev hL.io _ hL.one
    ((HW l).W_proj K s LL h) T hT _ _ (incl_pow _ _ hX m) hm

end GlobalTheory.NL.SandArb
