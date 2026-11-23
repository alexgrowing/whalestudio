import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarizationCrystalFormPerfectSelfAnnihila
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsDetEquivOfSubsingleton

set_option autoImplicit false
noncomputable section
open Module

namespace GlobalTheory.PolExistsRing

theorem mem_of_annihilates {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (ψ : LinearMap.BilinForm R V) [hψ : ψ.IsPerfPair] (W W' : Submodule R V) (hc : IsCompl W W')
    [Module.Finite R W'] [Module.Projective R W'] [Module.Finite R (Dual R W)]
    [Module.Projective R (Dual R W)]
    (hrk : ∀ p : PrimeSpectrum R, rankAtStalk W' p = rankAtStalk (Dual R W) p)
    (hiso : ∀ f ∈ W, ∀ g ∈ W, ψ f g = 0) (f : V) (hf : ∀ g ∈ W, ψ f g = 0) : f ∈ W := by
  let Φ : W' →ₗ[R] Dual R W := W.subtype.dualMap ∘ₗ ψ ∘ₗ W'.subtype
  let e := Submodule.prodEquivOfIsCompl W W' hc
  have hdec : ∀ v : V, (((e.symm v).1 : W) : V) + ((e.symm v).2 : V) = v := fun v ↦ by
    rw [← Submodule.coe_prodEquivOfIsCompl' W W' hc, LinearEquiv.apply_symm_apply]
  have hΦ' : ∀ v : V, ∀ g : W, Φ (e.symm v).2 g = ψ v g := by
    intro v g
    have h := congrArg (fun u ↦ ψ u g) (hdec v)
    simp only [map_add, LinearMap.add_apply] at h
    rw [hiso _ (Submodule.coe_mem _) g g.2, zero_add] at h
    simpa [Φ] using h
  have hΦ : Function.Surjective Φ := by
    intro l
    obtain ⟨v, hv⟩ := hψ.bijective_left.2 (l ∘ₗ W.projectionOnto W' hc)
    refine ⟨(e.symm v).2, LinearMap.ext fun g ↦ ?_⟩
    rw [hΦ' v g, hv]
    simp
  obtain ⟨s, hs⟩ := Module.projective_lifting_property Φ LinearMap.id hΦ
  have hsinj : Function.Injective s := fun x y h ↦ by
    have := congrArg Φ h
    rwa [← LinearMap.comp_apply, hs, ← LinearMap.comp_apply, hs] at this
  have hc2 : IsCompl (LinearMap.range s) (LinearMap.ker Φ) := by
    have h := LinearMap.isCompl_of_proj (f := s.rangeRestrict ∘ₗ Φ) (fun x ↦ by
      obtain ⟨_, y, rfl⟩ := x
      apply Subtype.ext
      simp only [LinearMap.comp_apply, LinearMap.codRestrict_apply]
      rw [← LinearMap.comp_apply Φ s, hs, LinearMap.id_apply])
    have hk : LinearMap.ker s.rangeRestrict = ⊥ := by
      rw [LinearMap.ker_rangeRestrict]; exact LinearMap.ker_eq_bot.2 hsinj
    rwa [LinearMap.ker_comp_of_ker_eq_bot _ hk] at h
  let ep := Submodule.prodEquivOfIsCompl _ _ hc2
  let es : Dual R W ≃ₗ[R] LinearMap.range s := LinearEquiv.ofInjective s hsinj
  haveI : Module.Finite R (LinearMap.range s) := Module.Finite.equiv es
  haveI : Module.Projective R (LinearMap.range s) := Module.Projective.of_equiv es
  let pr : W' →ₗ[R] LinearMap.ker Φ := LinearMap.snd R _ _ ∘ₗ ep.symm.toLinearMap
  have hpr : pr ∘ₗ (LinearMap.ker Φ).subtype = LinearMap.id := LinearMap.ext fun x ↦ by
    simp [pr, ep, Submodule.prodEquivOfIsCompl_symm_apply_right]
  haveI : Module.Finite R (LinearMap.ker Φ) :=
    Module.Finite.of_surjective pr (fun x ↦ ⟨x, by simpa using congrArg (fun m ↦ m x) hpr⟩)
  haveI : Module.Projective R (LinearMap.ker Φ) := Module.Projective.of_split _ _ hpr
  have hr0 : rankAtStalk (R := R) (LinearMap.ker Φ) = 0 := by
    have h1 := rankAtStalk_eq_of_equiv ep
    rw [rankAtStalk_prod, rankAtStalk_eq_of_equiv es.symm] at h1
    funext p
    have := congrFun h1 p
    simp only [Pi.add_apply] at this
    rw [hrk p] at this
    simp only [Pi.zero_apply]
    omega
  haveI := (rankAtStalk_eq_zero_iff_subsingleton).1 hr0
  have hb : (e.symm f).2 ∈ LinearMap.ker Φ := LinearMap.mem_ker.2 (LinearMap.ext fun g ↦ by
    rw [hΦ' f g]; exact hf g g.2)
  have h0 : (e.symm f).2 = 0 := by
    have := Subsingleton.elim (⟨_, hb⟩ : LinearMap.ker Φ) 0
    simpa using congrArg Subtype.val this
  rw [← hdec f, h0]
  simp

theorem mem_of_annihilates_dual {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (ψ : LinearMap.BilinForm R (Dual R M)) [ψ.IsPerfPair] (F N : Submodule R M) (hc : IsCompl F N)
    [Module.Finite R M] [Module.Projective R M] [Module.Finite R F] [Module.Projective R F] (g : ℕ)
    (hM : ∀ p : PrimeSpectrum R, rankAtStalk M p = 2 * g)
    (hF : ∀ p : PrimeSpectrum R, rankAtStalk F p = g)
    (hiso : ∀ f ∈ F.dualAnnihilator, ∀ h ∈ F.dualAnnihilator, ψ f h = 0) (f : Dual R M)
    (hf : ∀ h ∈ F.dualAnnihilator, ψ f h = 0) : f ∈ F.dualAnnihilator := by
  let e := Submodule.prodEquivOfIsCompl F N hc
  have hdec : ∀ x : M, (((e.symm x).1 : F) : M) + ((e.symm x).2 : M) = x := fun x ↦ by
    rw [← Submodule.coe_prodEquivOfIsCompl' F N hc, LinearEquiv.apply_symm_apply]
  have hc' : IsCompl F.dualAnnihilator N.dualAnnihilator := by
    constructor
    · rw [disjoint_iff_inf_le]
      rintro φ ⟨h1, h2⟩
      rw [Submodule.mem_bot]
      refine LinearMap.ext fun x ↦ ?_
      rw [← hdec x, map_add, (Submodule.mem_dualAnnihilator _).1 h1 _ (Submodule.coe_mem _),
        (Submodule.mem_dualAnnihilator _).1 h2 _ (Submodule.coe_mem _)]
      simp
    · rw [codisjoint_iff_le_sup]
      intro φ _
      rw [Submodule.mem_sup]
      refine ⟨φ ∘ₗ N.subtype ∘ₗ LinearMap.snd R F N ∘ₗ e.symm.toLinearMap, ?_,
        φ ∘ₗ F.subtype ∘ₗ LinearMap.fst R F N ∘ₗ e.symm.toLinearMap, ?_, ?_⟩
      · refine (Submodule.mem_dualAnnihilator _).2 fun x hx ↦ ?_
        simp [e]
        rw [Submodule.projection_apply_of_mem_right _ hx, map_zero]
      · refine (Submodule.mem_dualAnnihilator _).2 fun x hx ↦ ?_
        simp [e]
        rw [Submodule.projection_apply_of_mem_right _ hx, map_zero]
      · refine LinearMap.ext fun x ↦ ?_
        conv_rhs => rw [← hdec x]
        simp [add_comm]
  let eW' : Dual R F ≃ₗ[R] N.dualAnnihilator :=
    (Submodule.quotientEquivOfIsCompl N F hc.symm).dualMap.trans (Submodule.dualQuotEquivDualAnnihilator N)
  let eW : Dual R N ≃ₗ[R] F.dualAnnihilator :=
    (Submodule.quotientEquivOfIsCompl F N hc).dualMap.trans (Submodule.dualQuotEquivDualAnnihilator F)
  have hpN : (N.projectionOnto F hc.symm) ∘ₗ N.subtype = LinearMap.id :=
    LinearMap.ext fun x ↦ Submodule.projectionOnto_apply_left hc.symm x
  haveI : Module.Projective R N := Module.Projective.of_split _ _ hpN
  haveI : Module.Finite R N := Module.Finite.of_surjective _ (Submodule.projectionOnto_surjective hc.symm)
  let eN : Dual R F.dualAnnihilator ≃ₗ[R] N := eW.dualMap.trans (Module.evalEquiv R N).symm
  haveI : Module.Finite R N.dualAnnihilator := Module.Finite.equiv eW'
  haveI : Module.Projective R N.dualAnnihilator := Module.Projective.of_equiv eW'
  haveI : Module.Finite R (Dual R F.dualAnnihilator) := Module.Finite.equiv eN.symm
  haveI : Module.Projective R (Dual R F.dualAnnihilator) := Module.Projective.of_equiv eN.symm
  refine mem_of_annihilates ψ _ _ hc' (fun p ↦ ?_) hiso f hf
  rw [← rankAtStalk_eq_of_equiv eW', rankAtStalk_eq_of_equiv eN, GlobalTheory.TopExt.rankAtStalk_dual F p, hF p]
  have h1 := congrFun (rankAtStalk_eq_of_equiv e) p
  rw [rankAtStalk_prod, Pi.add_apply, hM p, hF p] at h1
  omega

end GlobalTheory.PolExistsRing

namespace GlobalTheory.PolExistsRing

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
open GlobalTheory.Published GlobalTheory.CatCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem polForm_exists : GlobalTheory.Published.AbelianDeRham → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X}
    {A : Over (Sp S)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left}, IsGrpPullback A Xo.univ.t.G x π →
    ∃ ψ : LinearMap.BilinForm S (HdR A), IsPolForm (dp0 S) (𝟙 _) A (Xo.univ.t.PP.L.pull π) ψ ∧
      (∀ f ∈ Fil A, ∀ g ∈ Fil A, ψ f g = 0) ∧ LinearMap.IsPerfPair ψ ∧
      ∀ f, (∀ g ∈ Fil A, ψ f g = 0) → f ∈ Fil A := by
  intro P E _ _ _ H Dw l Xo S _ x A _ π hπ
  have hA := PolPull.isAbelianScheme_of_isGrpPullback (ObjDim.isAbelianScheme Xo.univ) hπ
  have gA := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ.1
    (ObjDim.smoothOfRelativeDimension Xo.univ)
  obtain ⟨h0, -, -, -, e, he⟩ := P.1 S A _ hA gA
  have hLB : (Xo.univ.t.PP.L.pull π).IsLB := pull_isLB Xo.univ.t.PP.isLB π
  obtain ⟨z, hz, -⟩ := (isChern_existsUnique_and_iso S ⊥ (dp0 S) _ (A.hom ≫ 𝟙 _)).1 _ hLB
  obtain ⟨n, a, b, hab⟩ := GlobalTheory.PolExists.exists_sum_wedge (e.symm z)
  have hm : ∀ c : FirstDeRham (A.hom ≫ 𝟙 _), c ∈ primDR A := fun c ↦ by
    change c ∈ prim (dp0 S) (𝟙 _) A
    rw [show prim (dp0 S) (𝟙 _) A = ⊤ from h0]; trivial
  let a' : Fin n → primDR A := fun k ↦ ⟨a k, hm _⟩
  let b' : Fin n → primDR A := fun k ↦ ⟨b k, hm _⟩
  have hz' : IsChern (dp0 S) (A.hom ≫ 𝟙 _) (Xo.univ.t.PP.L.pull π) (∑ k, cup _ (a' k).1 (b' k).1) := by
    have : z = ∑ k, cup _ (a k) (b k) := by
      rw [← e.apply_symm_apply z, ← hab, map_sum]
      exact Finset.sum_congr rfl fun k _ ↦ he _ _
    exact this ▸ hz
  have hpol : IsPolForm (dp0 S) (𝟙 _) A (Xo.univ.t.PP.L.pull π) (wedgeForm (dp0 S) (𝟙 _) A a' b') :=
    ⟨n, a', b', hz', rfl⟩
  have hK : Out.KTriv A (Xo.univ.t.PP.L.pull π) :=
    kTriv_pull hπ Xo.univ.t.PP.isLB hLB ((isGen_iff _).1 (GlobalTheory.PolExists.isGen_self hLB)) Xo.univ.ktriv
  obtain ⟨hiso, hperf⟩ := P.2.2.2.2 S A _ hA gA _ hLB _ hpol
  have hperf' := hperf hK
  refine ⟨_, hpol, hiso, hperf', fun f hf ↦ ?_⟩

  obtain ⟨hfin, hproj, hrk⟩ := AbelianDeRham.Free.prim P.1 hA gA
  obtain ⟨-, ⟨N, hN⟩, hFfin, hFproj, hFrk⟩ := P.2.1 S A _ hA gA
  exact mem_of_annihilates_dual (wedgeForm (dp0 S) (𝟙 _) A a' b') (PrimitiveSubmodule A) N hN _ hrk hFrk hiso f hf

end GlobalTheory.PolExistsRing
