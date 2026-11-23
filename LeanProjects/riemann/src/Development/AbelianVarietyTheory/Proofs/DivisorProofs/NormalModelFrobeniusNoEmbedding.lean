import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroPresZeroMod
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusPresentationExistsStatement
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open GlobalTheory GlobalTheory.Vert GlobalTheory.MixedLocalChains GlobalTheory.FrobFilt

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.FrobFilt

open TopologicalSpace

theorem bijective_app_of_isIso_pullback_ι {X : Scheme.{0}} {F G : X.Modules} (f : F ⟶ G)
    (U : X.Opens) (hf : IsIso ((Scheme.Modules.pullback U.ι).map f)) {D : X.Opens} (hD : D ≤ U) :
    Function.Bijective (f.app D) := by
  have hr : IsIso ((Scheme.Modules.restrictFunctor U.ι).map f) :=
    (NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback U.ι) f).2 hf
  have e : U.ι ''ᵁ (U.ι ⁻¹ᵁ D) = D := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right.2 hD]
  have h1 : Function.Bijective (((Scheme.Modules.restrictFunctor U.ι).map f).app (U.ι ⁻¹ᵁ D)) :=
    ConcreteCategory.bijective_of_isIso _
  have h2 : Function.Bijective (f.app (U.ι ''ᵁ (U.ι ⁻¹ᵁ D))) := h1
  rwa [e] at h2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B : GlobalTheory.Vert.Model O}

theorem isGenSpecial_fromSpec {W : B.X.Opens} (hW : IsAffineOpen W) [Nonempty W] {a : Γ(B.X, W)}
    (ha : a ≠ 0) (hD : B.X.basicOpen a = W ⊓ B.gen) (q : PrimeSpectrum Γ(B.X, W))
    (hq : q.asIdeal.height = 1) (haq : a ∈ q.asIdeal) : IsGenSpecial B (hW.fromSpec q) := by
  haveI : IsNoetherianRing Γ(B.X, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  have key : ∀ r : PrimeSpectrum Γ(B.X, W), hW.fromSpec r ∈ B.gen ↔ a ∉ r.asIdeal := fun r => by
    have h1 : hW.fromSpec r ∈ B.X.basicOpen a ↔ a ∉ r.asIdeal := by
      change r ∈ hW.fromSpec ⁻¹ᵁ B.X.basicOpen a ↔ _
      rw [hW.fromSpec_preimage_basicOpen]
      rfl
    have h2 : hW.fromSpec r ∈ W := by
      have : hW.fromSpec r ∈ Set.range hW.fromSpec := ⟨r, rfl⟩
      rwa [hW.range_fromSpec] at this
    rw [← h1, hD]
    exact ⟨fun h => ⟨h2, h⟩, fun h => h.2⟩
  refine ⟨fun h => (key q).1 h haq, fun y hy hyx => ?_⟩
  have hx : hW.fromSpec q ∈ W := by
    have : hW.fromSpec q ∈ Set.range hW.fromSpec := ⟨q, rfl⟩
    rwa [hW.range_fromSpec] at this
  have hyW : y ∈ Set.range hW.fromSpec := by
    rw [hW.range_fromSpec]
    exact hyx.mem_open W.isOpen hx
  obtain ⟨r, rfl⟩ := hyW
  have hle : r.asIdeal ≤ q.asIdeal := (PrimeSpectrum.le_iff_specializes r q).2
    (hW.fromSpec.isOpenEmbedding.isInducing.specializes_iff.1 hyx)
  have har : a ∈ r.asIdeal := by
    by_contra h
    exact hy ((key r).2 h)
  have hge := (mem_minimalPrimes_span_singleton_of_height_eq_one hq ha haq).2
    ⟨r.isPrime, (Ideal.span_singleton_le_iff_mem _).2 har⟩ hle
  rw [show r = q from PrimeSpectrum.ext (le_antisymm hle hge)]

theorem exists_basicOpen_eq_inf_gen (W : B.X.Opens) [Nonempty W] :
    ∃ a : Γ(B.X, W), a ≠ 0 ∧ B.X.basicOpen a = W ⊓ B.gen := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hb : B.X.basicOpen (B.X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (B.const ϖ)) =
      W ⊓ B.gen := by
    rw [B.X.basicOpen_res, B.gen_eq_basicOpen hϖ.ne_zero hϖ.not_isUnit]
  refine ⟨_, fun h => ?_, hb⟩
  rw [h, Scheme.basicOpen_zero] at hb
  obtain ⟨x⟩ := ‹Nonempty W›
  have : genericPoint B.X ∈ W ⊓ B.gen := ⟨VB.genericPoint_mem x.2, B.genericPoint_mem_gen⟩
  rw [← hb] at this
  exact this

theorem eq_zero_of_affine (hB : GlobalTheory.IsNormalScheme B.X) (P : Pres B) {W : B.X.Opens}
    (hW : IsAffineOpen W) [Nonempty W] [Module.Free Γ(B.X, W) Γ(P.E, W)]
    [Module.Free Γ(B.X, W) Γ(P.E', W)] (s : Γ(P.mod, W))
    (hs : ∀ x ∈ W, IsGenSpecial B x → ∃ (V : B.X.Opens) (h : V ≤ W), x ∈ V ∧
      (Scheme.Modules.presheaf P.mod).map (homOfLE h).op s = 0) : s = 0 := by
  haveI := P.vb.isQuasicoherent
  haveI := P.vb'.isQuasicoherent
  haveI : P.mod.IsQuasicoherent := QCoh.isQuasicoherent_cokernel P.ψ
  haveI : IsNoetherianRing Γ(B.X, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  haveI : IsIntegrallyClosed Γ(B.X, W) := IsNormalScheme.isIntegrallyClosed_of_isAffineOpen hW
  obtain ⟨a, ha, hD⟩ := exists_basicOpen_eq_inf_gen W
  have hbij : Function.Bijective (P.ψ.app (B.X.basicOpen a)) :=
    bijective_app_of_isIso_pullback_ι P.ψ B.gen P.iso (hD.le.trans inf_le_right)
  have hinj : Function.Injective (QCoh.appLinear P.ψ W) := by
    refine (injective_iff_map_eq_zero _).2 fun v hv => ?_
    have h0 : P.E'.presheaf.map (homOfLE (B.X.basicOpen_le a)).op v = 0 := by
      apply hbij.1
      rw [QCoh.app_res, map_zero]
      change P.E.presheaf.map _ (QCoh.appLinear P.ψ W v) = 0
      rw [hv, map_zero]
    obtain ⟨n, hn⟩ := QCoh.exists_pow_smul_eq_zero P.E' hW a _ rfl v h0
    exact (smul_eq_zero_iff_right (pow_ne_zero n ha)).1 hn
  obtain ⟨v, rfl⟩ := QCoh.surjective_cokernel_π_app P.ψ hW s
  have hker := QCoh.ker_cokernel_π_app P.ψ hW
  have hpow : ∀ t : Γ(B.X, W), (Scheme.Modules.presheaf P.mod).map
      (homOfLE (B.X.basicOpen_le t)).op ((cokernel.π P.ψ).app W v) = 0 →
      ∃ n : ℕ, t ^ n • v ∈ LinearMap.range (QCoh.appLinear P.ψ W) := fun t ht => by
    obtain ⟨n, hn⟩ := QCoh.exists_pow_smul_eq_zero P.mod hW t _ rfl _ ht
    refine ⟨n, ?_⟩
    rw [← hker, LinearMap.mem_ker, map_smul]
    exact hn
  obtain ⟨n, hn⟩ := hpow a (by
    obtain ⟨w, hw⟩ := hbij.2 (P.E.presheaf.map (homOfLE (B.X.basicOpen_le a)).op v)
    refine (QCoh.app_res (cokernel.π P.ψ) (B.X.basicOpen_le a) v).symm.trans ?_
    rw [← hw, QCoh.app_app, cokernel.condition]
    rfl)
  have hv : v ∈ LinearMap.range (QCoh.appLinear P.ψ W) := by
    refine mem_range_of_forall_height_eq_one_of_projective _ hinj (pow_ne_zero n ha) hn
      fun q hqp hq haq => ?_
    have hx : hW.fromSpec ⟨q, hqp⟩ ∈ W := by
      have : hW.fromSpec ⟨q, hqp⟩ ∈ Set.range hW.fromSpec := ⟨_, rfl⟩
      rwa [hW.range_fromSpec] at this
    obtain ⟨V, hVW, hxV, hV⟩ := hs _ hx
      (isGenSpecial_fromSpec hW ha hD ⟨q, hqp⟩ hq (hqp.mem_of_pow_mem n haq))
    obtain ⟨t, htV, hxt⟩ := hW.exists_basicOpen_le ⟨_, hxV⟩ hx
    have htq : t ∉ q := by
      have : (⟨q, hqp⟩ : PrimeSpectrum Γ(B.X, W)) ∈ hW.fromSpec ⁻¹ᵁ B.X.basicOpen t := hxt
      rw [hW.fromSpec_preimage_basicOpen] at this
      exact this
    obtain ⟨m, hm⟩ := hpow t (by
      have := congrArg ((Scheme.Modules.presheaf P.mod).map (homOfLE htV).op) hV
      rw [map_zero, ← ConcreteCategory.comp_apply, ← Functor.map_comp] at this
      exact this)
    exact ⟨t ^ m, fun h => htq (hqp.mem_of_pow_mem m h), hm⟩
  rw [← hker] at hv
  exact hv

theorem noEmb_pres (hB : GlobalTheory.IsNormalScheme B.X) (P : Pres B) : NoEmb B P.mod := by
  intro U V hVU hV
  refine (injective_iff_map_eq_zero ((Scheme.Modules.presheaf P.mod).map (homOfLE hVU).op).hom).2
    fun s hs => ?_
  have H : ∀ x : U, ∃ (W : B.X.Opens) (h : W ≤ U), x.1 ∈ W ∧ GlobalTheory.Twist.resM P.mod h s = 0 := by
    intro x
    obtain ⟨W₁, e, -, hx₁, h₁, he⟩ := P.vb.exists_affine x.2
    obtain ⟨W, e', hW, hx, h, he'⟩ := P.vb'.exists_affine hx₁
    haveI : Nonempty W := ⟨⟨_, hx⟩⟩
    haveI := Module.Free.of_basis (he.basis h)
    haveI := Module.Free.of_basis (he'.basis le_rfl)
    refine ⟨W, h.trans h₁, hx, eq_zero_of_affine hB P hW _ fun y hy hg =>
      ⟨W ⊓ V, inf_le_left, ⟨hy, hV y (h₁ (h hy)) hg⟩, ?_⟩⟩
    have := congrArg ((Scheme.Modules.presheaf P.mod).map (homOfLE (inf_le_right : W ⊓ V ≤ V)).op) hs
    rw [map_zero] at this
    exact (GlobalTheory.Twist.resM_resM _ _ _).trans ((GlobalTheory.Twist.resM_resM _ _ _).symm.trans this)
  choose W h hx h0 using H
  refine GlobalTheory.Twist.sec_ext_of_cover W h (fun x hxU => Opens.mem_iSup.2 ⟨⟨x, hxU⟩, hx _⟩) fun k => ?_
  rw [h0, map_zero]

theorem noEmb_frob_rankOne : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X → ∀ (g : Γ(B.X, ⊤)), IsRootOfP p g p → ∀ R : Pres B, R.r = 1 → Kills g R.mod → NoEmb B ((frob p B).obj R.mod) := by
  intro O _ _ _ p _ _ _ B hB g hg R hR hk
  obtain ⟨R', hR'⟩ := GlobalTheory.T.frobenius_presentation_exists O p B g hg R hR hk
  obtain ⟨e⟩ := isFrob_iff.1 hR'
  exact (noEmb_pres hB R').of_iso e

end GlobalTheory.FrobFilt
