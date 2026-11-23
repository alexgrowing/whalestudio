import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.FrobFactsAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.NumberField
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.BrMain
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Places

noncomputable section
open NumberField IsDedekindDomain ValuativeRel Matrix GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Geo (incFin galFin)
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DZA UpperTheory.V.Published UpperTheory.CBC

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.Gal.InertialTypesAlt.L

private theorem finsum_smul_comp {G W : Type} [Finite G] [AddCommGroup W] [Module ℂ W] (a : G → ℂ) (L : G → W →ₗ[ℂ] W)
    (R : W →ₗ[ℂ] W) : ∑ᶠ g, a g • (L g ∘ₗ R) = (∑ᶠ g, a g • L g) ∘ₗ R := by
  letI := Fintype.ofFinite G
  simp only [finsum_eq_sum_of_fintype]
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.smul_apply]

private theorem trace_finsum_smul {G W : Type} [Finite G] [AddCommGroup W] [Module ℂ W] (a : G → ℂ) (L : G → W →ₗ[ℂ] W) :
    LinearMap.trace ℂ W (∑ᶠ g, a g • L g) = ∑ᶠ g, a g * LinearMap.trace ℂ W (L g) := by
  letI := Fintype.ofFinite G
  simp only [finsum_eq_sum_of_fintype, map_sum, map_smul, smul_eq_mul]

private theorem trace_step {G G' W W' : Type} [Finite G] [Finite G'] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (a : G' → ℂ) (L : G' → W' →ₗ[ℂ] W') (R : W' →ₗ[ℂ] W') (b : G → ℂ) (M : G → W →ₗ[ℂ] W) (R' : W →ₗ[ℂ] W) (hR' : R' = LinearMap.id)
    (c d d' : ℂ) (hc : c ≠ 0) (hd : d ≠ 0)
    (e : d' * LinearMap.trace ℂ W' (∑ᶠ g, a g • (L g ∘ₗ R)) = c * (d * LinearMap.trace ℂ W (∑ᶠ g, b g • (M g ∘ₗ R'))))
    (hne : ∑ᶠ g, b g * LinearMap.trace ℂ W (M g) ≠ 0) : ∑ᶠ g, a g • L g ≠ 0 := by
  subst hR'
  simp only [LinearMap.comp_id] at e
  rw [finsum_smul_comp, trace_finsum_smul] at e
  intro h0
  rw [h0, LinearMap.zero_comp, map_zero, mul_zero] at e
  exact mul_ne_zero hc (mul_ne_zero hd hne) e.symm

open scoped Classical in
private theorem normLift_eq {F F' : Type} [Field F] [Field F'] [Algebra F F'] (s : F' ≃ₐ[F] F') {n : ℕ} (f : GL (Fin n) F → ℂ) :
    normLift s f = GlobalTheory.Shin.shLift s f := by
  have e : ∀ δ : GL (Fin n) F', GlobalTheory.LBC.norm F s δ = GlobalTheory.Shin.nrm s δ := by
    intro δ
    unfold GlobalTheory.LBC.norm GlobalTheory.Shin.nrm GlobalTheory.Shin.nrmG
    congr 1
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
      ext a b
      rfl
  funext δ
  have e2 : IsFinNorm s δ = GlobalTheory.Shin.IsNorm s δ := by
    funext γ
    unfold IsFinNorm GlobalTheory.Shin.IsNorm
    rw [e]
    rfl
  have aux : ∀ P Q : GL (Fin n) F → Prop, P = Q →
      (if h : ∃ γ, P γ then f h.choose else 0) = (if h : ∃ γ, Q γ then f h.choose else 0) := by
    rintro P _ rfl; rfl
  exact aux _ _ e2

private theorem twTr_level (hAct : FinAct) {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) k) V) (fb : GL (Fin n) 𝓀[k] → ℂ) (A : V →ₗ[ℂ] V)
    (hA : ∀ x ∈ fixed ρ (GlobalTheory.SplitWeil.KOne k (Fin n)), A x ∈ fixed ρ (GlobalTheory.SplitWeil.KOne k (Fin n))) :
    GlobalTheory.BCT.twTr ρ (KO k n) (K1 (IsLocalRing.residue 𝒪[k]) n) (infl (IsLocalRing.residue 𝒪[k]) fb) A =
      (Nat.card (GL (Fin n) 𝓀[k]) : ℂ)⁻¹ * LinearMap.trace ℂ _ (∑ᶠ g, fb g • (GlobalTheory.LocGL.levelZero ρ g ∘ₗ A.restrict hA)) := by
  letI := Fintype.ofFinite 𝓀[k]
  obtain ⟨hl, r, hr, hT⟩ := hAct k 𝓀[k] (IsLocalRing.residue 𝒪[k]) IsLocalRing.residue_surjective n V ρ
  have er : r = GlobalTheory.LocGL.levelZero ρ := by
    ext g x
    obtain ⟨y, rfl⟩ := hl g
    have e1 := hr y x
    have e2 := GlobalTheory.LocGL.levelZero_apply ρ ((GlobalTheory.LocGL.toKO k (Fin n)) y) x
    have e3 : GlobalTheory.LocGL.redK k (Fin n) ((GlobalTheory.LocGL.toKO k (Fin n)) y) = GeneralLinearGroup.map (IsLocalRing.residue 𝒪[k]) y := by
      simp [GlobalTheory.LocGL.redK]
    rw [e3] at e2
    exact e1.trans e2.symm
  subst er
  exact hT fb A hA

private theorem exists_isRes (hRes : ResEx) {k K : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra k K] [ValuativeExtension k K] [FiniteDimensional k K] [IsGalois k K] (hu : PositivityTheory.Rg.Tf.Loc.IsUnramifiedLoc k K)
    [Algebra 𝓀[k] 𝓀[K]] [Fintype 𝓀[k]]
    (hinc : ∀ (x : 𝒪[k]) (y : 𝒪[K]), (y : K) = algebraMap k K x →
      IsLocalRing.residue _ y = algebraMap 𝓀[k] 𝓀[K] (IsLocalRing.residue _ x))
    (s : 𝓀[K] ≃ₐ[𝓀[k]] 𝓀[K]) (hs : ∀ z, s z = z ^ Nat.card 𝓀[k]) :
    ∃ t : K ≃ₐ[k] K, IsRes (IsLocalRing.residue 𝒪[k]) (IsLocalRing.residue 𝒪[K]) t s := by
  obtain ⟨F₀, F₁, _, _, _, _, _, rk, rK, t, sb, h⟩ := hRes k K hu

  have kk : ∀ x : 𝒪[k], rk x = 0 ↔ IsLocalRing.residue 𝒪[k] x = 0 := by
    intro x
    have hm : RingHom.ker rk = IsLocalRing.maximalIdeal 𝒪[k] :=
      IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective rk h.onto₀)
    rw [IsLocalRing.residue_eq_zero_iff, ← hm, RingHom.mem_ker]
  have kK : ∀ x : 𝒪[K], rK x = 0 ↔ IsLocalRing.residue 𝒪[K] x = 0 := by
    intro x
    have hm : RingHom.ker rK = IsLocalRing.maximalIdeal 𝒪[K] :=
      IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective rK h.onto₁)
    rw [IsLocalRing.residue_eq_zero_iff, ← hm, RingHom.mem_ker]
  let φ₀ : 𝓀[k] →+* F₀ := Ideal.Quotient.lift (IsLocalRing.maximalIdeal 𝒪[k]) rk
    fun a ha => (kk a).2 ((IsLocalRing.residue_eq_zero_iff a).2 ha)
  let φ₁ : 𝓀[K] →+* F₁ := Ideal.Quotient.lift (IsLocalRing.maximalIdeal 𝒪[K]) rK
    fun a ha => (kK a).2 ((IsLocalRing.residue_eq_zero_iff a).2 ha)
  have hφ₀ : ∀ x, φ₀ (IsLocalRing.residue _ x) = rk x := fun x => rfl
  have hφ₁ : ∀ x, φ₁ (IsLocalRing.residue _ x) = rK x := fun x => rfl
  have b₀ : Function.Bijective φ₀ := ⟨φ₀.injective, fun z => by
    obtain ⟨x, rfl⟩ := h.onto₀ z
    exact ⟨_, hφ₀ x⟩⟩
  have b₁ : Function.Bijective φ₁ := ⟨φ₁.injective, fun z => by
    obtain ⟨x, rfl⟩ := h.onto₁ z
    exact ⟨_, hφ₁ x⟩⟩
  let e₀ : 𝓀[k] ≃+* F₀ := RingEquiv.ofBijective φ₀ b₀
  let e₁ : 𝓀[K] ≃+* F₁ := RingEquiv.ofBijective φ₁ b₁
  have hint : ∀ x : 𝒪[k], ∃ y : 𝒪[K], (y : K) = algebraMap k K x := by
    intro x
    have h1 : (x : k) ≤ᵥ 1 := (Valuation.Compatible.vle_iff_le (v := valuation k) _ _).2 (by rw [map_one]; exact (Valuation.mem_integer_iff _ _).1 x.2)
    have h2 : algebraMap k K x ≤ᵥ algebraMap k K 1 := (ValuativeExtension.vle_iff_vle _ _).2 h1
    rw [map_one] at h2
    exact ⟨⟨algebraMap k K x, (Valuation.mem_integer_iff _ _).2 (by simpa using (Valuation.Compatible.vle_iff_le (v := valuation K) _ _).1 h2)⟩, rfl⟩
  have hc : (algebraMap F₀ F₁).comp e₀.toRingHom = e₁.toRingHom.comp (algebraMap 𝓀[k] 𝓀[K]) := by
    ext z
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
    obtain ⟨y, hy⟩ := hint x
    show algebraMap F₀ F₁ (φ₀ _) = φ₁ (algebraMap 𝓀[k] 𝓀[K] _)
    rw [← hinc x y hy, hφ₀, hφ₁, h.inc x y hy]
  have hq : Fintype.card F₀ = Nat.card 𝓀[k] := by
    rw [← Nat.card_eq_fintype_card]; exact (Nat.card_congr e₀.toEquiv).symm
  refine ⟨t, ?_, IsLocalRing.residue_surjective, IsLocalRing.residue_surjective, hinc, ?_, ?_⟩
  · rw [← h.deg]
    exact Algebra.finrank_eq_of_equiv_equiv e₀ e₁ hc
  · intro x y hy
    have h1 : rK y = rK x ^ Nat.card 𝓀[k] := by rw [h.gal x y hy, h.frob, hq]
    have h2 : rK (y - x ^ Nat.card 𝓀[k]) = 0 := by rw [map_sub, map_pow, h1, sub_self]
    have h3 := (kK _).1 h2
    rw [map_sub, map_pow, sub_eq_zero] at h3
    rw [h3, hs]
  · intro z
    rw [hs, Nat.card_eq_fintype_card]

theorem finTrace :
    ResEx → FinAct → InflFacts → FrobFacts → InflTrace → UpperTheory.Gal.InertialTypesAlt.FinTrace := by
  intro hRes hAct hInfl hFrob hIT F E _ _ _ _ _ _ _ _ hp n hn π P hcj hbc v w hsp hu τ τ' hτ hτ' _ hinc s hs f hf hne
  obtain ⟨w', hw'⟩ := UpperTheory.V.Z.Tf.Orb.placeUniq_holds F E hp v hsp
  have hw : ∀ x : PlacesOver E v, x = w := fun x => (hw' x).trans (hw' w).symm
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos hp.pos
  haveI : Fact (Module.finrank F E).Prime := ⟨hp⟩
  haveI : IsCyclic (E ≃ₐ[F] E) := by
    apply isCyclic_of_prime_card (p := Module.finrank F E)
    exact IsGalois.card_aut_eq_finrank F E
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := E ≃ₐ[F] E)
  obtain ⟨i1, i2, i3, i4, s0, hs0, hr, h1, h2, h3⟩ := UpperTheory.V.Z.Tf.Orb.placeData_holds F E σ hσ v w hw
  letI := Fintype.ofFinite 𝓀[v.adicCompletion F]
  letI := Fintype.ofFinite 𝓀[w.1.adicCompletion E]
  have hcm : ∀ x, completionMap v w.1 x = algebraMap _ (w.1.adicCompletion E) x := h1
  obtain ⟨t, ht⟩ := exists_isRes hRes (h3 (hu w))
    (fun x y hy => hinc x y (hy.trans (hcm x).symm)) s hs
  obtain ⟨I, c, hI, hc, H⟩ := hIT F E hp n hn π P hcj hbc v w hw hu hcm _ _ _ _ t s ht τ τ' hτ hτ'
  have hst := ((hFrob _ _ _ _ _ _ t s ht).2 n).1
  have hA : ∀ x ∈ fixed τ'.ρ (GlobalTheory.SplitWeil.KOne (w.1.adicCompletion E) (Fin n)),
      I x ∈ fixed τ'.ρ (GlobalTheory.SplitWeil.KOne (w.1.adicCompletion E) (Fin n)) :=
    fun x hx => hI.mem_fixed hst hx
  have hB : ∀ x ∈ fixed τ.ρ (GlobalTheory.SplitWeil.KOne (v.adicCompletion F) (Fin n)),
      (LinearMap.id : τ.V →ₗ[ℂ] τ.V) x ∈ fixed τ.ρ (GlobalTheory.SplitWeil.KOne (v.adicCompletion F) (Fin n)) :=
    fun x hx => hx
  have e := H f hf
  rw [normLift_eq, twTr_level hAct n τ'.ρ _ I hA, twTr_level hAct n τ.ρ f _ hB] at e
  have hid : (LinearMap.id : τ.V →ₗ[ℂ] τ.V).restrict hB = LinearMap.id := by
    ext x
    rfl
  have hcard : (Nat.card (GL (Fin n) 𝓀[v.adicCompletion F]) : ℂ)⁻¹ ≠ 0 :=
    inv_ne_zero (Nat.cast_ne_zero.2 Nat.card_pos.ne')
  exact trace_step _ _ _ _ _ _ hid _ _ _ hc hcard e hne

end UpperTheory.Gal.InertialTypesAlt.L
