import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrdInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeFamilyFiniteLocallyFreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeNonzeroInFunctionField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalChainsGlueRootOfPStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalChainsGlueQuasicoherentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalChainsGlueLieDifferentialsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackChainCoverAdditiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackChainCoverFreeModuleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackChainCoverExactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackChainCoverQuotientStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalChainsGlueQuotientModuleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalChainsGlueCharPUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalChainsGlueBelowLengthStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalChainsGlueCharPFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPointFactorsAffineCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackChainCoverUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackChainCoverCompatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorBundleSectionsFiniteProjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainFiniteRelationsAffineOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeSpanBoundedDenominatorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainQuasicoherentCoverCompatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixActionGeneratedAdditiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainQuasicoherentCoverUniqueStatement

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.GroupBplus (AffOp)
open GlobalTheory.RingChain (RChain mv baseOf Qt IsFrobLin)
open GlobalTheory.ChainPts.PullHT (pullA)
open GlobalTheory.PerfdLat (piMap)
open scoped TensorProduct Pointwise
open GlobalTheory.ChainPts
open GlobalTheory.ChainDesc

namespace GlobalTheory.ChainDesc

theorem isRootOfP_pull {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p : ℕ} {B B' : Vert.Model O}
    (f : B'.X ⟶ B.X) {a : Γ(B.X, ⊤)} {k : ℕ} (h : IsRootOfP p a k) : IsRootOfP p (f.appTop a) k := by
  obtain ⟨u, hu⟩ := h
  refine ⟨Units.map f.appTop.hom.toMonoidHom u, ?_⟩
  rw [Units.coe_map, ← map_pow, hu, map_mul, map_natCast]
  rfl

theorem map_cstBp_ne_zero {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p : ℕ} [Fact p.Prime]
    {B : Vert.Model O} {a : Γ(B.X, ⊤)} (h : IsRootOfP p a (p - 1)) (U : AffOp B.X) {R : Type} [CommRing R]
    (φ : U.Bp →+* R) (hp : (p : R) ≠ 0) : φ (cstBp U a) ≠ 0 := fun h0 => by
  obtain ⟨u, hu⟩ := h
  let χ : Γ(B.X, ⊤) →+* R := (φ.comp (algebraMap Γ(B.X, U.1) U.Bp)).comp (resG B.X le_top)
  have h1 : χ a = 0 := h0
  have h2 := congrArg χ hu
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  rw [map_pow, h1, zero_pow (by omega), map_mul, map_natCast, eq_comm, (u.isUnit.map χ).mul_right_eq_zero] at h2
  exact hp h2

theorem exists_finite_affOp_cover {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (B : Vert.Model O) :
    (∃ (I : Type) (_ : Finite I) (U : I → AffOp B.X), ∀ z : B.X, ∃ i, z ∈ (U i).1) ∧
      ∀ U U' : AffOp B.X, IsAffineOpen (U.1 ⊓ U'.1) ∧ Nonempty ↥(U.1 ⊓ U'.1) := by
  haveI := B.isProper
  haveI : CompactSpace B.X := QuasiCompact.compactSpace_of_compactSpace B.str
  haveI : B.X.IsSeparated := ⟨by rw [← terminal.comp_from B.str]; infer_instance⟩
  refine ⟨?_, fun U U' => ⟨U.2.1.inf U'.2.1, ?_⟩⟩
  · obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun U : AffOp B.X => (U.1 : Set B.X)) (fun U => U.1.isOpen)
      fun z _ => by
        obtain ⟨U, hU, hy, -⟩ := QCoh.exists_affine_mem_le (U := ⊤) z trivial
        exact Set.mem_iUnion.2 ⟨⟨U, hU, ⟨⟨_, hy⟩⟩⟩, hy⟩
    refine ⟨t, inferInstance, fun i => i.1, fun z => ?_⟩
    obtain ⟨U, hU, hz⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ z))
    exact ⟨⟨U, hU⟩, hz⟩
  · obtain ⟨x⟩ := U.2.2
    obtain ⟨y⟩ := U'.2.2
    obtain ⟨z, hz⟩ := nonempty_preirreducible_inter U.1.isOpen U'.1.isOpen ⟨_, x.2⟩ ⟨_, y.2⟩
    exact ⟨⟨z, hz⟩⟩

theorem mv_one {A A' : Type} [CommRing A] [CommRing A'] (φ : A →+* A') {h : ℕ} (x : Fin h → A) :
    mv φ 1 x = piMap φ (Fin h) x := by
  rw [mv, Matrix.map_one _ Int.cast_zero Int.cast_one, Matrix.one_mulVec]; rfl

theorem exists_rho_lift {A : Type} [CommRing A] {p h o : ℕ} {π : A} {γ : ℕ → A} {Lie Om : Type} [AddCommGroup Lie]
    [Module A Lie] [AddCommGroup Om] [Module A Om] (C : RChain p A h o π γ Lie Om) (w : Om) :
    ∃ y : C.L 0, C.ρ w = Submodule.Quotient.mk (Submodule.Quotient.mk y) := by
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (C.ρ w)
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  exact ⟨y, hz.symm⟩

theorem map_rho_lift {A A' : Type} [CommRing A] [CommRing A'] {p h o : ℕ} {π : A} {γ : ℕ → A} {Lie Om : Type}
    [AddCommGroup Lie] [Module A Lie] [AddCommGroup Om] [Module A Om] {π' : A'} {γ' : ℕ → A'} {Lie' Om' : Type}
    [AddCommGroup Lie'] [Module A' Lie'] [AddCommGroup Om'] [Module A' Om'] {C : RChain p A h o π γ Lie Om}
    {C' : RChain p A' h o π' γ' Lie' Om'} {φ : A →+* A'} {M : Matrix (Fin h) (Fin h) ℤ} {l : Lie → Lie'} {m : Om → Om'}
    (k : C.Map C' φ M l m) {w : Om} {w' : Om'} (e : m w = w') {y : C.L 0}
    (hy : C.ρ w = Submodule.Quotient.mk (Submodule.Quotient.mk y)) :
    ∃ y' : C'.L 0, y'.1 = mv φ M y.1 ∧ C'.ρ w' = Submodule.Quotient.mk (Submodule.Quotient.mk y') :=
  ⟨⟨_, k.mem 0 _ y.2⟩, rfl, e ▸ k.ρ w y _ rfl hy⟩

section Pairs

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B : Vert.Model O} {Λ : Type} [CommRing Λ]
  {p h o : ℕ} {Lie Om : AM B Λ} {π : Γ(B.X, ⊤)} {γ : ℕ → Γ(B.X, ⊤)} {M : Λ →+* Matrix (Fin h) (Fin h) ℤ}
  (C : ChainsBp p h o Lie Om π γ)

def RhoAt (U : AffOp B.X) (s : Γ(Om.V, U.1) × (C U).L 0) : Prop :=
  (C U).ρ (1 ⊗ₜ s.1) = Submodule.Quotient.mk (Submodule.Quotient.mk s.2)

theorem exists_rhoAt (U : AffOp B.X) (w : Γ(Om.V, U.1)) : ∃ y : (C U).L 0, RhoAt C U (w, y) :=
  exists_rho_lift (C U) (1 ⊗ₜ w)

variable {C}

set_option maxHeartbeats 800000 in

theorem RhoAt.res (hS : IsSys C M) {U U' : AffOp B.X} (hle : U'.1 ≤ U.1) {w : Γ(Om.V, U.1)} {y : (C U).L 0}
    (hy : RhoAt C U (w, y)) : ∃ s : Γ(Om.V, U'.1) × (C U').L 0,
      s.1 = resM Om.V hle w ∧ s.2.1 = piMap (AffOp.res hle) (Fin h) y.1 ∧ RhoAt C U' s := by
  obtain ⟨-, l, m, -, hm, k⟩ := hS.1 U U' hle
  obtain ⟨y', h1, h2⟩ := map_rho_lift k (hm w) hy
  exact ⟨(resM Om.V hle w, y'), rfl, h1.trans (mv_one _ _), h2⟩

set_option maxHeartbeats 800000 in

theorem RhoAt.act (hS : IsSys C M) (a : Λ) {U : AffOp B.X} {w : Γ(Om.V, U.1)} {y : (C U).L 0}
    (hy : RhoAt C U (w, y)) : ∃ s : Γ(Om.V, U.1) × (C U).L 0,
      s.1 = (Om.ρ a : Om.V ⟶ Om.V).app _ w ∧ s.2.1 = mv (RingHom.id _) (M a) y.1 ∧ RhoAt C U s := by
  obtain ⟨l, m, -, hm, k⟩ := hS.2 U a
  obtain ⟨y', h1, h2⟩ := map_rho_lift k (hm w) hy
  exact ⟨((Om.ρ a : Om.V ⟶ Om.V).app _ w, y'), rfl, h1, h2⟩

theorem exists_down [Fact p.Prime] {r r' : ℕ} (vL : GlobalTheory.VB.IsVB Lie.V r) (vO : GlobalTheory.VB.IsVB Om.V r') (U : AffOp B.X)
    (S : Set (Γ(Om.V, U.1) × (C U).L 0)) (hf : S.Finite) (h0 : cstBp U π ≠ 0) (hS : ∀ s ∈ S, RhoAt C U s) :
    ∃ T : Set U.Bp, T.Finite ∧ ∀ (B' : GlobalTheory.Vert.Model O) (f : GlobalTheory.Vert.Model.Hom B' B)
      (g : ∀ U : AffOp B.X, Γ(B'.X, f.f ⁻¹ᵁ U.1) →+* U.Bp), IsCov f g → T ⊆ Set.range (g U) →
        ∃ D : ChainUp p h o Lie Om π γ f (f.f ⁻¹ᵁ U.1), IsDown C f g U S D :=
  GlobalTheory.T.chain_finite_relations_affine_open O p B Λ h o r r' Lie Om π γ C vL vO U S hf h0 hS

end Pairs

set_option maxHeartbeats 800000 in

theorem exists_stage : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O) (Λ : Type) [CommRing Λ] [Module.Finite ℤ Λ] (h o r r' : ℕ) (Lie Om : AM B Λ) (π : Γ(B.X, ⊤)) (γ : ℕ → Γ(B.X, ⊤)) (M : Λ →+* Matrix (Fin h) (Fin h) ℤ) (C : ChainsBp p h o Lie Om π γ), GlobalTheory.IsNormalScheme B.X → IsAdd Lie → IsAdd Om → GlobalTheory.VB.IsVB Lie.V r → GlobalTheory.VB.IsVB Om.V r' → IsRootOfP p π (p - 1) → IsSys C M → ∃ (B' : GlobalTheory.Vert.Model O) (f : GlobalTheory.Vert.Model.Hom B' B) (g : ∀ U : AffOp B.X, Γ(B'.X, f.f ⁻¹ᵁ U.1) →+* U.Bp) (E : ℕ → B'.X.Modules) (ι : ∀ n, E n ⟶ freeModule B'.X (Fin h)) (I : Type) (U : I → AffOp B.X) (S : ∀ i, Set (Γ(Om.V, (U i).1) × (C (U i)).L 0)) (D : ∀ i, ChainUp p h o Lie Om π γ f (f.f ⁻¹ᵁ (U i).1)), f.relDim = 0 ∧ IsCov f g ∧ IsLatOf C f g ι ∧ (∀ z : B.X, ∃ i, z ∈ (U i).1) ∧ (∀ i, IsDown C f g (U i) (S i) (D i)) ∧ IsLoc M ι (fun i => f.f ⁻¹ᵁ (U i).1) D := by
  intro O _ _ _ p _ _ _ B Λ _ _ h o r r' Lie Om π γ M C hB aL aO vL vO hπ hS
  classical
  have qL := vL.isQuasicoherent
  have qO := vO.isQuasicoherent
  obtain ⟨⟨I, _, U, hU⟩, hinf⟩ := exists_finite_affOp_cover B
  let U₂ : I → I → AffOp B.X := fun i k => ⟨(U i).1 ⊓ (U k).1, hinf _ _⟩
  obtain ⟨G, hG⟩ : ∃ G : Finset Λ, Submodule.span ℤ (G : Set Λ) = ⊤ := Module.Finite.fg_top
  have hπ0 : ∀ U : AffOp B.X, cstBp U π ≠ 0 := fun U => map_cstBp_ne_zero hπ U (RingHom.id _) fun h0 =>
    GlobalTheory.Vert.Model.natCast_prime_ne_zero_kbar O p B (by simpa using congrArg Subtype.val h0)
  choose Wg hWg using fun U : AffOp B.X => (GlobalTheory.T.vector_bundle_sections_finite_projective B.X Om.V r' vO U.1 U.2.1).1.fg_top
  choose y hy using fun (U : AffOp B.X) (w : Γ(Om.V, U.1)) => exists_rhoAt C U w
  choose rs hrs1 hrs2 hrs3 using fun (U U' : AffOp B.X) (hle : U'.1 ≤ U.1) (w : Γ(Om.V, U.1)) =>
    RhoAt.res hS hle (hy U w)
  choose ac hac1 hac2 hac3 using fun (U : AffOp B.X) (a : Λ) (w : Γ(Om.V, U.1)) => RhoAt.act hS a (hy U w)
  let S : ∀ i, Set (Γ(Om.V, (U i).1) × (C (U i)).L 0) := fun i =>
    (fun w => (w, y (U i) w)) '' (Wg (U i)) ∪ ⋃ a ∈ G, ac (U i) a '' (Wg (U i))
  let S₂ : ∀ i k, Set (Γ(Om.V, (U₂ i k).1) × (C (U₂ i k)).L 0) := fun i k =>
    rs (U i) (U₂ i k) inf_le_left '' (Wg (U i)) ∪ rs (U k) (U₂ i k) inf_le_right '' (Wg (U k))
  choose T hT hTD using fun i => exists_down (C := C) vL vO (U i) (S i)
    (((Wg _).finite_toSet.image _).union (G.finite_toSet.biUnion fun a _ => (Wg _).finite_toSet.image _)) (hπ0 _) (by
      rintro s (⟨w, -, rfl⟩ | hs)
      · exact hy _ _
      · obtain ⟨a, -, w, -, rfl⟩ := Set.mem_iUnion₂.1 hs
        exact hac3 _ _ _)
  choose T₂ hT₂ hTD₂ using fun i k => exists_down (C := C) vL vO (U₂ i k) (S₂ i k)
    (((Wg _).finite_toSet.image _).union ((Wg _).finite_toSet.image _)) (hπ0 _) (by
      rintro s (⟨w, -, rfl⟩ | ⟨w, -, rfl⟩) <;> exact hrs3 _ _ _ _)
  have hbase : ∀ (U : AffOp B.X) (n : ℕ) (x : Fin h → U.Bp), cstBp U π • x ∈ (C U).L n := fun U n x =>
    (C U).base_le n (Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top)
  have hdvd : ∀ U : AffOp B.X, cstBp U π ∣ (p : U.Bp) := fun U => by
    obtain ⟨u, hu⟩ := hπ
    have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    have h1 : π ∣ (p : Γ(B.X, ⊤)) := (Units.dvd_mul_left (u := u)).1 (hu ▸ dvd_pow_self π (by omega))
    simpa [cstBp] using map_dvd ((algebraMap Γ(B.X, U.1) U.Bp).comp (resG B.X le_top)) h1
  obtain ⟨B', f, g, E, ι, hn, hd, hfin, hinj, halg, hres, hTg, hE⟩ := GlobalTheory.T.lattice_family_finite_locally_free O p B hB (Fin (o + 1)) h
    (fun j U => (C U).L j) ((⋃ i, Sigma.mk (U i) '' T i) ∪ ⋃ i, ⋃ k, Sigma.mk (U₂ i k) '' T₂ i k)
    ((Set.finite_iUnion fun i => (hT i).image _).union
      (Set.finite_iUnion fun i => Set.finite_iUnion fun k => (hT₂ i k).image _))
    (fun j U => ⟨(C U).finite j, (C U).projective j, fun x => by
      obtain ⟨c, hc⟩ := hdvd U
      rw [hc, mul_smul]
      exact hbase U j _⟩)
    (fun j U U' hle => (hS.1 U U' hle).1 j)
  have hc : IsCov f g := ⟨hn, hfin, hinj, halg, hres⟩
  let c : ℕ → Fin (o + 1) := fun n => ⟨min n o, Nat.lt_succ_of_le (min_le_right n o)⟩
  have hl : IsLatOf C f g fun n => ι (c n) := fun n => by
    obtain ⟨h1, h2, h3⟩ := hE (c n)
    refine ⟨h1, h2, fun U => ?_⟩
    have h4 : (C U).L (min n o) =
        Submodule.span U.Bp (piMap (g U) (Fin h) '' (latOf (ι (c n)) (f.f ⁻¹ᵁ U.1) : Set _)) := by
      refine (h3 U).trans (congrArg _ (Set.ext fun x => ⟨?_, ?_⟩))
      · rintro ⟨s, hs⟩
        exact ⟨_, ⟨s, rfl⟩, funext fun i => (hs i).symm⟩
      · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
        exact ⟨s, fun i => rfl⟩
    exact ⟨GlobalTheory.T.lattice_span_bounded_denominators O B B' f g hc h _ _ h1 h2 U _ _ (hπ0 U) (hbase U _) h4, h4⟩
  choose D hD using fun i => hTD i B' f g hc fun x hx =>
    hTg ⟨U i, x⟩ (Or.inl (Set.mem_iUnion.2 ⟨i, x, hx, rfl⟩))
  choose D₂ hD₂ using fun i k => hTD₂ i k B' f g hc fun x hx =>
    hTg ⟨U₂ i k, x⟩ (Or.inr (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨k, x, hx, rfl⟩⟩))
  refine ⟨B', f, g, _, fun n => ι (c n), I, U, S, D, hd, hc, hl, hU, hD, fun i => hc.isAffineOpen _,
    fun x => hU (f.f x), fun i k => hc.isAffineOpen (U₂ i k), fun n => ⟨(hl n).1, (hl n).2.1⟩,
    fun i => (hD i).fits hl, fun i k => ⟨D₂ i k, (hD₂ i k).fits hl, ?_, ?_⟩, fun i => ?_⟩
  · refine GlobalTheory.T.chain_quasicoherent_cover_compat O p B B' Λ h o Lie Om π γ M C f g qL qO hS hc (U i) (U₂ i k) inf_le_left _ _ _ _ (hD i) (hD₂ i k)
      (top_le_iff.1 ((hWg _).ge.trans (Submodule.span_mono fun w hw => ?_)))
    exact ⟨_, Or.inl ⟨w, hw, rfl⟩, rfl, _, Or.inl ⟨w, hw, rfl⟩, hrs1 _ _ _ _, hrs2 _ _ _ _⟩
  · refine GlobalTheory.T.chain_quasicoherent_cover_compat O p B B' Λ h o Lie Om π γ M C f g qL qO hS hc (U k) (U₂ i k) inf_le_right _ _ _ _ (hD k) (hD₂ i k)
      (top_le_iff.1 ((hWg _).ge.trans (Submodule.span_mono fun w hw => ?_)))
    exact ⟨_, Or.inl ⟨w, hw, rfl⟩, rfl, _, Or.inr ⟨w, hw, rfl⟩, hrs1 _ _ _ _, hrs2 _ _ _ _⟩
  · refine GlobalTheory.T.matrix_action_generated_additive p h o _ Λ _ _ _ _ (D i) M _ _ G (fun a b s => ?_) (fun a b s => ?_) hG fun a ha => ?_
    · rw [PullHT.isAdd_pullA f.f aL a b]
      rfl
    · rw [PullHT.isAdd_pullA f.f aO a b]
      rfl
    · refine GlobalTheory.T.chain_quasicoherent_cover_unique O p B B' Λ h o Lie Om π γ M C f g qL qO hS hc (U i) _ _ a (hD i)
        (top_le_iff.1 ((hWg _).ge.trans (Submodule.span_mono fun w hw => ?_)))
      exact ⟨_, Or.inl ⟨w, hw, rfl⟩, rfl, _, Or.inr (Set.mem_iUnion₂.2 ⟨a, ha, w, hw, rfl⟩), hac1 _ _ _, hac2 _ _ _⟩

theorem exists_preChain_kerMatch : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O) (Λ : Type) [CommRing Λ] [Module.Finite ℤ Λ] (h o r r' : ℕ) (Lie Om : AM B Λ) (π : Γ(B.X, ⊤)) (γ : ℕ → Γ(B.X, ⊤)) (M : Λ →+* Matrix (Fin h) (Fin h) ℤ) (C : ChainsBp p h o Lie Om π γ), GlobalTheory.IsNormalScheme B.X → IsAdd Lie → IsAdd Om → GlobalTheory.VB.IsVB Lie.V r → GlobalTheory.VB.IsVB Om.V r' → IsRootOfP p π (p - 1) → (∀ k ≤ o, IsRootOfP p (γ k) (p ^ (k + 1))) → IsSys C M → ∃ (B' : GlobalTheory.Vert.Model O) (f : GlobalTheory.Vert.Model.Hom B' B) (P : PreChain p o ((pullA f.f).obj Lie) ((pullA f.f).obj Om) (f.f.appTop π)), GlobalTheory.IsNormalScheme B'.X ∧ f.relDim = 0 ∧ KerMatch C f.f P.j.hom P.ρ.hom := by
  intro O _ _ _ p _ _ _ B Λ _ _ h o r r' Lie Om π γ M C hB aL aO vL vO hπ hγ hS
  obtain ⟨B', f, g, E, ι, I, U, S, D, hd, hc, hl, hU, hD, hL⟩ :=
    exists_stage O p B Λ h o r r' Lie Om π γ M C hB aL aO vL vO hπ hS
  have qL := vL.isQuasicoherent
  have qO := vO.isQuasicoherent
  have qL' : ((pullA f.f).obj Lie).V.IsQuasicoherent := (vL.pullback f.f).isQuasicoherent
  have qO' : ((pullA f.f).obj Om).V.IsQuasicoherent := (vO.pullback f.f).isQuasicoherent
  have hp := GlobalTheory.MixedLocalChains.FrobQuot.natCast_eq_zero_fibI p B'
  obtain ⟨q, l, tq, tl, hq, hl', hstep⟩ := GlobalTheory.T.local_chains_glue_root_of_p O p B' Λ h o _ _ _ _ M E ι I _ D (isRootOfP_pull f.f hπ) hL
  have hq0 := hq 0 (Nat.zero_le o)
  obtain ⟨j, hjk, hj, hj'⟩ := GlobalTheory.T.local_chains_glue_quasicoherent O p B' Λ h o _ _ _ _ M E ι I _ D qL' hL _ _ hq0
  obtain ⟨ρ, hρe, hρ⟩ := GlobalTheory.T.local_chains_glue_lie_differentials O p B' Λ h o _ _ _ _ M E ι I _ D qL' qO' hL _ _ hq0 j hj hj'
  have hJ : ∀ U : AffOp B.X, JUp C f g U (ι 0) (tq 0) j.hom :=
    GlobalTheory.T.pullback_chain_cover_additive O p B B' Λ h o Lie Om π γ M C f g E ι _ _ j hS hc hl hq0 fun z => (hU z).elim fun i hi =>
      ⟨U i, hi, GlobalTheory.T.pullback_chain_cover_free_module O p B B' Λ h o Lie Om π γ M C f g E ι _ _ _ qL hS hc hl _ _ _ (hD i) (hj i)⟩
  have hR : ∀ U : AffOp B.X, RUp C f g U (ι 0) (tq 0 ≫ (cokernel.π j).hom) ρ.hom :=
    GlobalTheory.T.pullback_chain_cover_exact O p B B' Λ h o Lie Om π γ M C f g E ι _ _ j ρ qL hS hc hl hq0 hJ fun z => (hU z).elim fun i hi =>
      ⟨U i, hi, GlobalTheory.T.pullback_chain_cover_quotient O p B B' Λ h o Lie Om π γ M C f g E ι _ _ _ qO hS hc hl _ _ _ (hD i) (hρ i)⟩
  refine ⟨B', f,
    { g := f.f.appTop (γ 0)
      γ := fun n => f.f.appTop (γ n)
      π_root := isRootOfP_pull f.f hπ
      g_root := isRootOfP_pull f.f (by simpa using hγ 0 (Nat.zero_le o))
      γ_root := fun n hn => isRootOfP_pull f.f (hγ n hn.le)
      hp := hp
      q := q
      l := l
      step := hstep
      l_free := fun n hn => GlobalTheory.T.local_chains_glue_quotient_module O p B' Λ h o _ _ _ _ M E ι I _ D hL n hn _ _ (hl' n hn)
      l_last := fun n hn => GlobalTheory.T.local_chains_glue_char_p_unique O p B' Λ h o _ _ _ _ M E ι I _ D hp qL' hL n hn _ _ (hl' n hn)
      q_kill := fun n hn => GlobalTheory.T.local_chains_glue_below_length O p B' Λ h o _ _ _ _ M E ι I _ D hL n hn _ _ (hq (n + 1) hn)
      q_frob := fun n hn => GlobalTheory.T.local_chains_glue_char_p_fibre O p B' Λ h o _ _ _ _ M E ι I _ D hp hL n hn _ _ _ _ (hq n hn.le) (hq (n + 1) hn)
      j := j
      j_kill := hjk
      ρ := ρ
      ρ_epi := hρe }, hc.1, hd, fun K _ _ R hR' hpK w U₀ hw => ?_⟩
  obtain ⟨φ, h1, rfl⟩ := GlobalTheory.T.integral_point_factors_affine_cover O B B' f g hc K R hR' w U₀ hw
  have hπR : φ (cstBp U₀ π) ∈ nonZeroDivisors R := mem_nonZeroDivisors_of_ne_zero
    (map_cstBp_ne_zero hπ U₀ φ fun h0 => hpK (by simpa using congrArg Subtype.val h0))
  exact ⟨φ, h1, GlobalTheory.T.pullback_chain_cover_unique O p B B' Λ h o Lie Om π γ M C f g E ι _ _ j hc hl hq0 U₀ (hJ U₀) R φ hπR hw,
    GlobalTheory.T.pullback_chain_cover_compat O p B B' Λ h o Lie Om π γ M C f g E ι _ _ j ρ hc qL hl hq0 U₀ (hJ U₀) (hR U₀) R φ hπR hw⟩

end GlobalTheory.ChainDesc

end
