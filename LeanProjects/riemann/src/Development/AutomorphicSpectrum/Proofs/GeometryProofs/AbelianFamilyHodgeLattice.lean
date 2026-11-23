import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptAwayFromPrimesStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspCorrespondenceBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyExpDerivativeLie
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueSemilinearStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPushAlongMap
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsEigAtIffOfIsDerivAt0
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsValueBasis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.ChartEig

theorem mem_eig {K V O : Type} [Field K] [AddCommGroup V] [Module K V] [CommRing O] {ρ : O →+* Module.End K V}
    {σ : O →+* K} {e : V} (he : e ∈ eigSp ρ σ) (a : O) : ρ a e = σ a • e := by
  have := (Submodule.mem_iInf _).1 he a
  simpa [sub_eq_zero] using this

theorem eig_sum_zero {K V O I : Type} [Field K] [AddCommGroup V] [Module K V] [CommRing O] [DecidableEq I]
    (ρ : O →+* Module.End K V) (σ : I → (O →+* K)) (hσ : Function.Injective σ) (A : Finset I) :
    ∀ f : I → V, (∀ s ∈ A, f s ∈ eigSp ρ (σ s)) → ∑ s ∈ A, f s = 0 → ∀ s ∈ A, f s = 0 := by
  induction A using Finset.induction_on with
  | empty => simp
  | insert t A ht ih =>
    intro f hf hsum
    rw [Finset.sum_insert ht] at hsum
    have key : ∀ s ∈ A, f s = 0 := by
      intro s hs
      have hne : s ≠ t := fun e => ht (e ▸ hs)
      obtain ⟨a, ha⟩ : ∃ a, σ s a ≠ σ t a := by
        by_contra h
        push_neg at h
        exact hne (hσ (RingHom.ext h))
      have hg : ∑ u ∈ A, (σ u a - σ t a) • f u = 0 := by
        have e : ∑ u ∈ A, (σ u a - σ t a) • f u =
            ρ a (f t + ∑ u ∈ A, f u) - σ t a • (f t + ∑ u ∈ A, f u) := by
          rw [map_add, map_sum, mem_eig (hf t (Finset.mem_insert_self _ _)) a, smul_add, Finset.smul_sum]
          simp only [sub_smul, Finset.sum_sub_distrib]
          rw [Finset.sum_congr rfl fun u hu => (mem_eig (hf u (Finset.mem_insert_of_mem hu)) a).symm]
          abel
        rw [e, hsum]
        simp
      have h1 := ih (fun u => (σ u a - σ t a) • f u)
        (fun u hu => (eigSp ρ (σ u)).smul_mem _ (hf u (Finset.mem_insert_of_mem hu))) hg s hs
      exact (smul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 ha)
    intro s hs
    rcases Finset.mem_insert.1 hs with rfl | hs
    · rw [Finset.sum_eq_zero key, add_zero] at hsum
      exact hsum
    · exact key s hs

def modelOfEquiv {S : Scheme.{0}} {R : Type} [CommRing R] {G : Over S} [GrpObj G]
    {x : Spec (CommRingCat.of R) ⟶ S} {F F' : Type} [AddCommGroup F] [Module R F] [AddCommGroup F'] [Module R F']
    (M : LieModel G x F) (e : F' ≃ₗ[R] F) : LieModel G x F' where
  pt v := M.pt (e v)
  tan v := M.tan _
  inj := M.inj.comp e.injective
  onto v hv := by
    obtain ⟨w, h⟩ := M.onto v hv
    exact ⟨e.symm w, by simpa using h⟩
  add v w := by rw [map_add, M.add]
  smul c v := by rw [map_smul, M.smul]

theorem exists_basis_of_base {S : Scheme.{0}} {G : Over S} [GrpObj G] [Smooth G.hom] {R C : Type} [CommRing R]
    [CommRing C] (φ : R →+* C) {x : Sp R ⟶ S} {y : Sp C ⟶ S} (hy : spMap φ ≫ x = y) {E F I : Type}
    [AddCommGroup E] [Module R E] [AddCommGroup F] [Module C F] (M : LieModel G x E) (M' : LieModel G y F)
    (b : Module.Basis I R E) :
    ∃ (j : E →ₛₗ[φ] F) (β : Module.Basis I C F),
      (∀ e, (M'.pt (j e)).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ) ≫ (M.pt e).left) ∧ ∀ i, β i = j (b i) := by
  subst hy
  obtain ⟨j, hj, -⟩ := GlobalTheory.T.lie_model_existsUnique_semilinear S G R C φ x E F M M'
  have hj' : ∀ e, (M'.pt (j e)).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ) ≫ (M.pt e).left := fun e => by
    have := hj e
    unfold LieModel.Lifts at this
    rwa [Category.comp_id] at this
  letI : Algebra R C := φ.toAlgebra
  letI : Module R F := Module.compHom F φ
  haveI : IsScalarTower R C F := ⟨fun r c f => by
    show (φ r * c) • f = φ r • c • f
    rw [mul_smul]⟩
  let jl : E →ₗ[R] F :=
    { toFun := j, map_add' := j.map_add, map_smul' := fun r e => j.map_smulₛₗ r e }
  have hbc : IsBaseChange C jl := (GlobalTheory.T.lie_model_finite_base_change S G R x E M).2.2 C F M' jl hj'
  refine ⟨j, IsBaseChange.basis b hbc, hj', fun i => ?_⟩
  rw [IsBaseChange.basis_apply]
  rfl

theorem exists_model_at {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] [Smooth G.hom] {g : ℕ}
    (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (φ : R →+* ℂ) :
    ∃ N : LieModel G (spMap φ) (Fin g → ℂ), ∀ u : Fin g → R,
      (N.pt (fun k => φ (u k))).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ) ≫ (M.pt u).left := by
  obtain ⟨F, _, _, ⟨MF⟩⟩ := lieModel_exists _ G ℂ (spMap φ)
  obtain ⟨j, β, hj, hβ⟩ := exists_basis_of_base φ (Category.comp_id _) M MF (Pi.basisFun R (Fin g))
  refine ⟨modelOfEquiv MF β.equivFun.symm, fun u => ?_⟩
  have h : β.equivFun.symm (fun k => φ (u k)) = j u := by
    have hu : u = ∑ a, u a • (Pi.basisFun R (Fin g)) a := by
      funext c
      simp [Finset.sum_apply, Pi.single_apply]
    conv_rhs => rw [hu]
    rw [map_sum]
    simp only [Module.Basis.equivFun_symm_apply, map_smulₛₗ, hβ]
  show (MF.pt (β.equivFun.symm _)).left = _
  rw [h, hj]

section Deriv

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {g n : ℕ}
  {M : LieModel G (𝟙 (Sp R)) (Fin g → R)} {B : Set (Fin n → ℂ)} {ψ : (Fin n → ℂ) → (R →+* ℂ)}

theorem isDerivAt0_all (e : Flat.FamExp G M B ψ) {b : Fin n → ℂ} (hb : b ∈ B)
    (N : LieModel G (spMap (ψ b)) (Fin g → ℂ))
    (hN : ∀ u : Fin g → R, (N.pt (fun k => ψ b (u k))).left =
      spMap (GlobalTheory.CompanionTheory.Ar.dualMap (ψ b)) ≫ (M.pt u).left) (x : Fin g → ℂ) :
    IsDerivAt0 (fun z => (e.ex b z).left) x (N.pt x).left := by
  have hF0 : (fun z => (e.ex b z).left) 0 = (1 : Over.mk (spMap (ψ b)) ⟶ G).left :=
    congrArg (·.left) (Flat.ExpLift.ex_zero e hb)
  have hpt : ∀ u : Fin g → R, IsDerivAt0 (fun z => (e.ex b z).left) (fun c => ψ b (u c)) (N.pt (fun k => ψ b (u k))).left :=
    fun u => by
      rw [hN]
      exact Flat.FrameDeriv.isDerivAt0_pt e hb u
  have h0 : IsDerivAt0 (fun z => (e.ex b z).left) 0 (N.pt 0).left := by
    have h3 : (fun c => ψ b ((0 : Fin g → R) c)) = (0 : Fin g → ℂ) := by
      funext c
      simp
    have := hpt 0
    rwa [h3] at this
  have hsingle : ∀ a : Fin g, IsDerivAt0 (fun z => (e.ex b z).left) (Pi.single a 1) (N.pt (Pi.single a 1)).left := by
    intro a
    have h3 : (fun c => ψ b ((Pi.single a 1 : Fin g → R) c)) = (Pi.single a 1 : Fin g → ℂ) := by
      funext c
      by_cases h : c = a
      · subst h; simp
      · simp [Pi.single_apply, h]
    have := hpt (Pi.single a 1)
    rwa [h3] at this
  have hsm : ∀ (c : ℂ) (w : Fin g → ℂ), IsDerivAt0 (fun z => (e.ex b z).left) w (N.pt w).left →
      IsDerivAt0 (fun z => (e.ex b z).left) (c • w) (N.pt (c • w)).left := by
    intro c w h
    have h1 := ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_smul h c
    have h2 : (N.pt (c • w)).left = spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul c) ≫ (N.pt w).left := by
      rw [N.smul]
      congr 2
    rw [h2]
    exact h1
  have hs : ∀ s : Finset (Fin g), IsDerivAt0 (fun z => (e.ex b z).left) (∑ a ∈ s, x a • (Pi.single a 1 : Fin g → ℂ))
      (N.pt (∑ a ∈ s, x a • (Pi.single a 1 : Fin g → ℂ))).left := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using h0
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, N.add]
      exact GlobalTheory.UnifCompare.isDerivAt0_mul (y := spMap (ψ b)) (G := G) hF0 (hsm _ _ (hsingle a)) ih
  have hx : ∑ a, x a • (Pi.single a 1 : Fin g → ℂ) = x := by
    funext c
    simp [Finset.sum_apply, Pi.single_apply]
  have := hs Finset.univ
  rwa [hx] at this

theorem pt_linear (e : Flat.FamExp G M B ψ) {b : Fin n → ℂ} (hb : b ∈ B)
    (N : LieModel G (spMap (ψ b)) (Fin g → ℂ))
    (hN : ∀ u : Fin g → R, (N.pt (fun k => ψ b (u k))).left =
      spMap (GlobalTheory.CompanionTheory.Ar.dualMap (ψ b)) ≫ (M.pt u).left)
    (f : G ⟶ G) (L : Module.End ℂ (Fin g → ℂ)) (hL : ∀ x, e.ex b (L x) = e.ex b x ≫ f) (x : Fin g → ℂ) :
    N.pt (L x) = N.pt x ≫ f := by
  have hhol : GlobalTheory.HolHom.HolAt (fun z => (e.ex b z).left) 0 := by
    let c : (Fin n → ℂ) × (Fin g → ℂ) → (Sp ℂ ⟶ G.left) := fun bz => (e.ex bz.1 bz.2).left
    have h1 : GlobalTheory.HolHom.HolAt c (b, 0) := GlobalTheory.HolHom.holAt_of_isHolTo e.hol ⟨hb, trivial⟩
    have hk : DifferentiableAt ℂ (fun z : Fin g → ℂ => (b, z)) 0 :=
      (differentiableAt_const b).prodMk differentiableAt_id
    exact GlobalTheory.HolHom.HolAt.precomp (c := c) (k := fun z : Fin g → ℂ => (b, z)) (z := 0) h1 hk
  have hv := (GlobalTheory.HolHom.isDerivAt0_iff _ _ _).1 (isDerivAt0_all e hb N hN x)
  have e1 := hv.comp f.left
  let L' : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ) := LinearMap.toContinuousLinearMap L
  have e2 : (fun t => (e.ex b t).left ≫ f.left) = fun t => (e.ex b (L' t)).left := by
    funext t
    rw [← Over.comp_left]
    show _ = (e.ex b (L t)).left
    rw [hL]
  rw [e2] at e1
  have e3 := GlobalTheory.DerivEig.isDerivAt_of_comp_linear hhol L' e1
  have e4 := (GlobalTheory.HolHom.isDerivAt0_iff _ _ _).1 (isDerivAt0_all e hb N hN (L x))
  exact Over.OverMorphism.ext (e4.unique e3)

end Deriv

section Core

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {G : Over X} [GrpObj G]
  {Li : Type} [AddCommGroup Li] [Module Ω Li]

theorem exists_value_basis [IsCommMonObj G] [Smooth G.hom] (hξ : IsCptGen ξ) (M : LieModel G ξ Li) (z : Sp ℂ ⟶ X)
    (h : genPt ξ ⤳ centre z) {V I : Type} [AddCommGroup V] [Module ℂ V] (Mz : LieModel G z V) [Fintype I]
    (F : I → Li) (hli : LinearIndependent Ω F)
    (hsp : M.lat ⟨centre z, h⟩ = Submodule.span (regAt ξ ⟨centre z, h⟩) (Set.range F)) :
    ∃ y : Module.Basis I ℂ V, ∀ j, M.ValAt z (F j) (Mz.pt (y j)) :=
  _root_.UpperTheory.Reformulated.B.Ga4.exists_value_basis hξ M z h Mz F hli hsp

theorem eig_of_value (hξ : IsCptGen ξ) (M : LieModel G ξ Li) (z : Sp ℂ ⟶ X) {V : Type} [AddCommGroup V] [Module ℂ V]
    (Mz : LieModel G z V) {O : Type} [CommRing O] (act : OAct O G) (ρ : O →+* Module.End Ω Li)
    (hρ : M.IsActOf act.act ρ) (χ : O →+* Ω) (c : O →+* ℂ) (hc : ∀ a, Ar.ValAt ξ z (χ a) (c a))
    (Bz : O →+* Module.End ℂ V) (hB : ∀ a x, Mz.pt (Bz a x) = Mz.pt x ≫ act.act a) {e : Li}
    (he : e ∈ eigSp ρ χ) {y : V} (hy : M.ValAt z e (Mz.pt y)) : y ∈ eigSp Bz c := by
  refine (Submodule.mem_iInf _).2 fun a => ?_
  rw [LinearMap.mem_ker]
  show Bz a y - c a • y = 0
  refine sub_eq_zero.2 (Mz.inj ?_)
  obtain ⟨h, v, hv, hw⟩ := (M.valAt_iff z e _).1 hy
  obtain ⟨_, s, hs, hcs⟩ := hc a
  have := act.hom a
  have e1 : M.Extends ⟨centre z, h⟩ (ρ a e) (v ≫ act.act a) := by
    have hv' := hv
    rw [LieModel.extends_iff] at hv' ⊢
    refine ⟨?_, ?_⟩
    · have h1 := hv'.1
      rw [LieTangent.isTanAt_iff] at h1 ⊢
      rw [← Category.assoc, h1, MonObj.one_comp]
    · rw [hρ a e, hv'.2, Category.assoc]
  have e2 := hv.smul s
  rw [hs, ← mem_eig he a] at e2
  have e3 := e1.unique (hξ.inj _) e2
  rw [hB, Mz.pt_smul, hw, Category.assoc, e3, ← Category.assoc, LieTangent.base_scale, Category.assoc]
  exact congrArg (fun c' : ℂ => LieTangent.epsScale z c' ≫ LieTangent.epsBase _ (LieTangent.spec_centre z) ≫ v) hcs

end Core

theorem values_eig : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (R : Type) [CommRing R] (t : SAB H (Sp R)) (jj : Sp R ⟶ 𝔐.X) (m : SABMap t 𝔐.t jj) (g n : ℕ) (M : LieModel t.G (𝟙 (Sp R)) (Fin g → R)) (B₀ : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : Flat.FamExp t.G M B₀ ψ) (b : Fin n → ℂ) (Bb : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (lab : CMType H ⊕ CMType H) (r : ℕ) (s : Fin r → 𝔐.Li) (sc : Fin r → Fin g → R) (σ : CMType H ⊕ CMType H → (𝓞 E →+* ℂ)), b ∈ B₀ → (∀ a' x, e.ex b (Bb a' x) = e.ex b x ≫ t.act.act a') → 𝔐.LabVal (spMap (ψ b) ≫ jj) id σ → (∀ h : genPt 𝔐.ξ ⤳ centre (spMap (ψ b) ≫ jj), (𝔐.V lab).IsFrameAt s ⟨centre (spMap (ψ b) ≫ jj), h⟩) → (∀ i, ∃ v : epsAt (spMap (ψ b) ≫ jj) ⟶ 𝔐.t.G, 𝔐.M.ValAt (spMap (ψ b) ≫ jj) (s i) v ∧ v.left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap (ψ b)) ≫ (M.pt (sc i)).left ≫ m.φ) → LinearIndependent ℂ (fun i k => ψ b (sc i k)) ∧ Submodule.span ℂ (Set.range fun i k => ψ b (sc i k)) = eigSp Bb (σ lab) := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K _ J _ y 𝔐 R _ t jj m g n M B₀ ψ e b Bb lab r s sc σ hb hB hσ hF hV
  classical
  have sm1 := 𝔐.t.semi.smooth
  have sm2 := t.semi.smooth
  have hgen := 𝔐.tie.gen
  obtain ⟨z, hz⟩ : ∃ z, z = spMap (ψ b) ≫ jj := ⟨_, rfl⟩
  rw [← hz] at hσ hF hV
  let q : Cpt 𝔐.ξ := ⟨centre z, 𝔐.all _⟩
  have hfib : ∀ r' : ℕ, r'.Prime → ¬ InFibre 𝔐.ξ r' q := by
    intro r' hr'
    refine not_not.2 ⟨Nat.cast_ne_zero.2 hr'.ne_zero, natCast_mem _ _, ?_⟩
    have hu : IsUnit ((r' : ℕ) : 𝔐.X.presheaf.stalk (centre z)) := by
      refine isUnit_of_map_unit (Scheme.stalkClosedPointTo z).hom _ ?_
      rw [map_natCast]
      exact (Nat.cast_ne_zero.2 hr'.ne_zero : (r' : ℂ) ≠ 0).isUnit
    obtain ⟨u, hu⟩ := hu
    refine ⟨((u⁻¹ : (𝔐.X.presheaf.stalk (centre z))ˣ) : 𝔐.X.presheaf.stalk (centre z)), ?_⟩
    refine eq_inv_of_mul_eq_one_left ?_
    have h1 := congrArg (genMap 𝔐.ξ q) (Units.inv_mul u)
    rw [map_mul, hu, map_natCast, map_one] at h1
    exact h1
  obtain ⟨hVd, -, hlat⟩ := GlobalTheory.T.hodge_cpt_away_from_primes E H D l Xo c (𝓞 c.F) (algebraMap (𝓞 c.F) c.F) Y S Ω K J y 𝔐
    RingOfIntegers.coe_injective q hfib
  have hσinj : Function.Injective σ := by
    obtain ⟨σ₀, -, hu, hbij, -⟩ := GlobalTheory.T.cusp_correspondence_bound E H D l Xo c Y S Ω K J y 𝔐 ℂ z
    rw [hu σ hσ]
    exact hbij.1
  have hemb : Function.Injective 𝔐.emb := by
    intro u v huv
    refine hσinj (RingHom.ext fun a => ?_)
    obtain ⟨h1, c1, e1, f1⟩ := hσ u a
    obtain ⟨h2, c2, e2, f2⟩ := hσ v a
    have e3 : genMap 𝔐.ξ ⟨centre z, h1⟩ c1 = genMap 𝔐.ξ ⟨centre z, h1⟩ c2 := by
      refine e1.trans ?_
      have : genMap 𝔐.ξ ⟨centre z, h1⟩ c2 = 𝔐.emb (id v) a := e2
      rw [this]
      simp only [id]
      rw [huv]
    rw [← f1, ← f2, hgen.inj _ e3]
  have hfr : ∀ u, ∃ (k : ℕ) (f : Fin k → 𝔐.Li), (𝔐.V u).IsFrameAt f q ∧ (u = lab → k = r ∧ HEq f s) := fun u => by
    by_cases hu : u = lab
    · subst hu
      exact ⟨r, s, hF _, fun _ => ⟨rfl, HEq.rfl⟩⟩
    · obtain ⟨U, hU, f, -, hf⟩ := 𝔐.vb u q trivial
      exact ⟨_, f, hf q trivial hU, fun h => absurd h hu⟩
  choose k f hf hlab using hfr
  obtain ⟨hk, hfs⟩ := hlab lab rfl
  subst hk
  have hfs' := eq_of_heq hfs
  subst hfs'
  have hmem : ∀ u i, f u i ∈ 𝔐.M.lat q ∧ f u i ∈ eigSp 𝔐.ρ (𝔐.emb u) := by
    intro u i
    have h1 : f u i ∈ 𝔐.V u q := by
      rw [(hf u).2]
      exact Submodule.subset_span ⟨i, rfl⟩
    rw [hVd u] at h1
    exact h1
  have hli : LinearIndependent Ω (fun p : (Σ u, Fin (k u)) => f p.1 p.2) := by
    refine Fintype.linearIndependent_iff.2 fun a ha p => ?_
    rw [Fintype.sum_sigma] at ha
    have h0 := eig_sum_zero 𝔐.ρ 𝔐.emb hemb Finset.univ (fun u => ∑ i, a ⟨u, i⟩ • f u i)
      (fun u _ => Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hmem u i).2) ha p.1 (Finset.mem_univ _)
    exact Fintype.linearIndependent_iff.1 (hf p.1).1 (fun i => a ⟨p.1, i⟩) h0 p.2
  have hsp : 𝔐.M.lat q = Submodule.span (regAt 𝔐.ξ q) (Set.range fun p : (Σ u, Fin (k u)) => f p.1 p.2) := by
    rw [hlat]
    refine le_antisymm (iSup_le fun u => ?_) (Submodule.span_le.2 ?_)
    · rw [← hVd u, (hf u).2]
      exact Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨⟨u, i⟩, rfl⟩)
    · rintro _ ⟨⟨u, i⟩, rfl⟩
      refine Submodule.mem_iSup_of_mem u ?_
      rw [← hVd u, (hf u).2]
      exact Submodule.subset_span ⟨i, rfl⟩
  obtain ⟨N, hN⟩ := exists_model_at M (ψ b)
  obtain ⟨Mz', hMz⟩ := SabLie.lieModel_of_sabMap E H 𝔐.X (Sp R) t 𝔐.t jj m ℂ (spMap (ψ b)) _ N
  subst hz
  have hBz : ∀ a x, Mz'.pt (Bb a x) = Mz'.pt x ≫ 𝔐.t.act.act a := by
    intro a x
    refine Over.OverMorphism.ext ?_
    rw [hMz, pt_linear e hb N hN (t.act.act a) (Bb a) (fun x => hB a x) x, Over.comp_left, Over.comp_left, hMz,
      Category.assoc, Category.assoc, m.act a]
  obtain ⟨yb, hyb⟩ := exists_value_basis hgen 𝔐.M _ (𝔐.all _) Mz' _ hli hsp
  have hey : ∀ p : (Σ u, Fin (k u)), yb p ∈ eigSp Bb (σ p.1) := fun p =>
    eig_of_value hgen 𝔐.M _ Mz' 𝔐.t.act 𝔐.ρ 𝔐.act (𝔐.emb p.1) (σ p.1) (hσ p.1) Bb hBz (hmem p.1 p.2).2 (hyb p)
  have hx : ∀ i, yb ⟨lab, i⟩ = fun k' => ψ b (sc i k') := by
    intro i
    obtain ⟨v, hv1, hv2⟩ := hV i
    have h1 : v = Mz'.pt (fun k' => ψ b (sc i k')) := by
      refine Over.OverMorphism.ext ?_
      rw [hv2, hMz, hN, Category.assoc]
    rw [h1] at hv1
    exact Mz'.inj (LieModel.ValAt.unique hgen (hyb ⟨lab, i⟩) hv1)
  have hfun : (fun i k' => ψ b (sc i k')) = fun i => yb ⟨lab, i⟩ := funext fun i => (hx i).symm
  rw [hfun]
  refine ⟨yb.linearIndependent.comp _ sigma_mk_injective, le_antisymm ?_ ?_⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    exact hey ⟨lab, i⟩
  · intro w hw
    let wt : CMType H ⊕ CMType H → (Fin g → ℂ) := fun u => ∑ i, yb.repr w ⟨u, i⟩ • yb ⟨u, i⟩
    have hsum : ∑ u, wt u = w := by
      have := yb.sum_repr w
      rwa [Fintype.sum_sigma] at this
    have hwt : ∀ u, wt u ∈ eigSp Bb (σ u) := fun u =>
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hey ⟨u, i⟩)
    have h0 := eig_sum_zero Bb σ hσinj Finset.univ (fun u => wt u - if u = lab then w else 0) (fun u _ => by
      by_cases hu : u = lab
      · subst hu
        simpa using Submodule.sub_mem _ (hwt _) hw
      · simpa [hu] using hwt u) (by
        rw [Finset.sum_sub_distrib, hsum]
        simp) lab (Finset.mem_univ _)
    have h1 : wt lab = w := by simpa [sub_eq_zero] using h0
    rw [← h1]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end GlobalTheory.CompanionTheory.Ar.Cusp.ChartEig
