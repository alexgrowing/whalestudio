import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSubFibreSubFib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FinrankFiniteFlatTorsionSubschemeEqCardPoints
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsConstStalk
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenspaceDecompositionInternalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagFrames

theorem mem_of_sum_mem {Ω : Type} [Field Ω] (R : Subring Ω) {Li : Type} [AddCommGroup Li] [Module Ω Li]
    {O : Type} [CommRing O] (ρ : O →+* Module.End Ω Li) {I : Type} [DecidableEq I] (σ : I → (O →+* Ω))
    (Λ : Submodule R Li) (hst : ∀ a, ∀ e ∈ Λ, ρ a e ∈ Λ) (hval : ∀ s a, σ s a ∈ R)
    (hinv : ∀ s s' a, σ s a ≠ σ s' a → (σ s a - σ s' a)⁻¹ ∈ R)
    (hsep : ∀ s s', s ≠ s' → ∃ a, σ s a ≠ σ s' a) (T : Finset I) :
    ∀ x : I → Li, (∀ t, x t ∈ eigSp ρ (σ t)) → ∑ t ∈ T, x t ∈ Λ → ∀ t ∈ T, x t ∈ Λ := by
  have hact : ∀ (t : I) (a : O) (e : Li), e ∈ eigSp ρ (σ t) → ρ a e = σ t a • e := by
    intro t a e he
    have := (Submodule.mem_iInf _).1 he a
    simpa [sub_eq_zero] using this
  have hRs : ∀ (r : Ω), r ∈ R → ∀ e ∈ Λ, r • e ∈ Λ := fun r hr e he => Λ.smul_mem ⟨r, hr⟩ he
  induction T using Finset.induction_on with
  | empty => simp
  | insert u T hu ih =>
    intro x hx hs
    rw [Finset.sum_insert hu] at hs
    have hT : ∀ t ∈ T, x t ∈ Λ := by
      intro t ht
      have hne : t ≠ u := fun h => hu (h ▸ ht)
      obtain ⟨a, ha⟩ := hsep t u hne
      have h1 : ρ a (x u + ∑ t ∈ T, x t) - σ u a • (x u + ∑ t ∈ T, x t) ∈ Λ :=
        Λ.sub_mem (hst a _ hs) (hRs _ (hval u a) _ hs)
      have h2 : ρ a (x u + ∑ t ∈ T, x t) - σ u a • (x u + ∑ t ∈ T, x t) =
          ∑ t ∈ T, (σ t a - σ u a) • x t := by
        rw [map_add, map_sum, hact u a _ (hx u), smul_add, Finset.smul_sum]
        rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [hact t a _ (hx t), sub_smul]
      rw [h2] at h1
      have h3 := ih (fun t => (σ t a - σ u a) • x t)
        (fun t => (eigSp ρ (σ t)).smul_mem _ (hx t)) h1 t ht
      have h4 := hRs _ (hinv t u a ha) _ h3
      rwa [smul_smul, inv_mul_cancel₀ (sub_ne_zero.2 ha), one_smul] at h4
    have hu' : x u ∈ Λ := by
      have := Λ.sub_mem hs (Λ.sum_mem hT)
      simpa using this
    intro t ht
    rcases Finset.mem_insert.1 ht with rfl | ht
    · exact hu'
    · exact hT t ht

theorem eq_span_sigma {Ω : Type} [Field Ω] (R : Subring Ω) {Li : Type} [AddCommGroup Li] [Module Ω Li]
    {O : Type} [CommRing O] (ρ : O →+* Module.End Ω Li) {I : Type} [DecidableEq I] (σ : I → (O →+* Ω))
    (Λ : Submodule R Li) (hst : ∀ a, ∀ e ∈ Λ, ρ a e ∈ Λ) (hval : ∀ s a, σ s a ∈ R)
    (hinv : ∀ s s' a, σ s a ≠ σ s' a → (σ s a - σ s' a)⁻¹ ∈ R)
    (hsep : ∀ s s', s ≠ s' → ∃ a, σ s a ≠ σ s' a)
    (hspan : ⨆ s, eigSp ρ (σ s) = ⊤) {r : I → ℕ} (b : ∀ s, Fin (r s) → Li)
    (hb : ∀ s, Λ ⊓ (eigSp ρ (σ s)).restrictScalars R = Submodule.span R (Set.range (b s))) :
    Λ = Submodule.span R (Set.range fun q : Σ s, Fin (r s) => b q.1 q.2) := by
  apply le_antisymm
  · intro e he
    have hm : e ∈ ⨆ s, eigSp ρ (σ s) := hspan ▸ Submodule.mem_top
    obtain ⟨f, hf, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hm
    refine Submodule.sum_mem _ fun t ht => ?_
    have h1 := mem_of_sum_mem R ρ σ Λ hst hval hinv hsep f.support f hf he t ht
    have h2 : f t ∈ Submodule.span R (Set.range (b t)) := by
      rw [← hb t]
      exact ⟨h1, hf t⟩
    refine Submodule.span_mono ?_ h2
    rintro _ ⟨k, rfl⟩
    exact ⟨⟨t, k⟩, rfl⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨s, k⟩, rfl⟩
    have : b s k ∈ Λ ⊓ (eigSp ρ (σ s)).restrictScalars R := by
      rw [hb s]
      exact Submodule.subset_span ⟨k, rfl⟩
    exact this.1

theorem mem_span_image_of_mem_flagStep {Ω : Type} [Field Ω] (R : Subring Ω) {Li : Type} [AddCommGroup Li]
    [Module Ω Li] {r : ℕ} (b : Fin r → Li) (hli : LinearIndependent Ω b) (i : ℕ) {e : Li}
    (h1 : e ∈ flagStep Ω b i) (h2 : e ∈ Submodule.span R (Set.range b)) :
    e ∈ Submodule.span R (b '' {k | (k : ℕ) < i}) := by
  obtain ⟨w, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 h2
  obtain ⟨l, hl, hle⟩ := (Finsupp.mem_span_image_iff_linearCombination Ω).1 h1
  have hc : l = Finsupp.equivFunOnFinite.symm (fun k => (w k : Ω)) := by
    apply hli
    rw [hle, Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)]
    exact Finset.sum_congr rfl fun k _ => rfl
  refine Submodule.sum_mem _ fun k _ => ?_
  by_cases hk : (k : ℕ) < i
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, hk, rfl⟩)
  · have h0 : l k = 0 := by
      by_contra h
      exact hk (hl (Finsupp.mem_support_iff.2 h))
    have hw : w k = 0 := by
      rw [hc] at h0
      exact Subtype.ext h0
    rw [hw, zero_smul]
    exact Submodule.zero_mem _

section Geo

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

theorem unitAt_natCast [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ)
    (hu : ∀ n : ℕ, n ≠ 0 → IsUnit ((n : X.presheaf.stalk p.1))) (n : ℕ) (hn : n ≠ 0) : unitAt ξ p (n : Ω) := by
  obtain ⟨u, hu⟩ := hu n hn
  have h1 : genMap ξ p u = (n : Ω) := by rw [hu, map_natCast]
  have h0 : (n : Ω) ≠ 0 := Nat.cast_ne_zero.2 hn
  refine ⟨h0, RingHom.mem_range.2 ⟨u, h1⟩, RingHom.mem_range.2 ⟨(↑u⁻¹ : X.presheaf.stalk p.1), ?_⟩⟩
  have h2 : genMap ξ p (↑u⁻¹ : X.presheaf.stalk p.1) * (n : Ω) = 1 := by
    rw [← h1, ← map_mul, Units.inv_mul, map_one]
  exact eq_inv_of_mul_eq_one_left h2

theorem not_inFibre [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ)
    (hu : ∀ n : ℕ, n ≠ 0 → IsUnit ((n : X.presheaf.stalk p.1))) (n : ℕ) (hn : n ≠ 0) : ¬ InFibre ξ n p :=
  not_not.2 (unitAt_natCast ξ p hu n hn)

variable {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {Li : Type} [AddCommGroup Li] [Module Ω Li]

open LieTangent in

theorem lat_stable (M : LieModel G ξ Li) (p : Cpt ξ) (f : G ⟶ G) [IsMonHom f] (A : Li →ₗ[Ω] Li)
    (hA : M.IsDiffOf f A) (e : Li) (he : e ∈ M.lat p) : A e ∈ M.lat p := by
  obtain ⟨v, hv⟩ := (M.mem_lat_iff p e).1 he
  refine (M.mem_lat_iff p _).2 ⟨v ≫ f, ?_⟩
  rw [LieModel.extends_iff] at hv ⊢
  refine ⟨?_, ?_⟩
  · have h := hv.1
    rw [isTanAt_iff] at h ⊢
    rw [← Category.assoc, h, one_comp]
  · rw [hA e, hv.2, Category.assoc]

end Geo

open HodgeCpt in

theorem exists_frames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) [Fintype (CMType H)] (Fl : 𝔐.Flag) (p : Cpt 𝔐.ξ), (∀ n : ℕ, n ≠ 0 → IsUnit ((n : 𝔐.X.presheaf.stalk p.1))) → ∃ b : ∀ s, Fin (labelRk D s) → 𝔐.Li, (∀ s (i : ℕ), flagStep Ω (b s) i = flagStep Ω (Fl.b s) i) ∧ (∀ s (i : ℕ), ∀ e ∈ flagStep Ω (b s) i, e ∈ 𝔐.M.lat p → e ∈ Submodule.span (regAt 𝔐.ξ p) (b s '' {k | (k : ℕ) < i})) ∧ LinearIndependent Ω (fun q : Σ s, Fin (labelRk D s) => b q.1 q.2) ∧ Submodule.span Ω (Set.range fun q : Σ s, Fin (labelRk D s) => b q.1 q.2) = ⊤ ∧ 𝔐.M.lat p = Submodule.span (regAt 𝔐.ξ p) (Set.range fun q : Σ s, Fin (labelRk D s) => b q.1 q.2) ∧ ∀ s, Submodule.span Ω (Set.range (b s)) = 𝔐.Vgen s := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J y 𝔐 _ Fl p hu
  classical
  haveI : CharZero c.F := charZero_of_injective_algebraMap (algebraMap ℚ c.F).injective
  haveI : CharZero Ω := charZero_of_injective_ringHom 𝔐.cst.injective

  have hVd : ∀ s, 𝔐.V s p = 𝔐.dR s p := fun s =>
    Lat.patch_of_not S _ _ fun n hn => not_inFibre 𝔐.ξ p hu n (𝔐.S_prime n hn).ne_zero
  choose U hU b hflag hfr using fun s => Fl.sub s p (Set.mem_univ p)
  have hF : ∀ s, (𝔐.V s).IsFrameAt (b s) p := fun s => hfr s p (Set.mem_univ p) (hU s)
  have hli : ∀ s, LinearIndependent Ω (b s) := fun s => (hF s).1
  have hst : ∀ s, 𝔐.M.lat p ⊓ (eigSp 𝔐.ρ (𝔐.emb s)).restrictScalars (regAt 𝔐.ξ p) =
      Submodule.span (regAt 𝔐.ξ p) (Set.range (b s)) := fun s => (hVd s).symm.trans (hF s).2

  have hΩ : ∀ s, Submodule.span Ω (Set.range (b s)) = 𝔐.Vgen s := by
    intro s
    obtain ⟨U', hU', b', hb', hfr'⟩ := 𝔐.vb s p (Set.mem_univ p)
    have h' : 𝔐.V s p = Submodule.span (regAt 𝔐.ξ p) (Set.range b') := (hfr' p (Set.mem_univ p) hU').2
    have e1 := Submodule.span_span_of_tower (regAt 𝔐.ξ p) Ω (Set.range (b s))
    have e2 := Submodule.span_span_of_tower (regAt 𝔐.ξ p) Ω (Set.range b')
    rw [← e1, ← (hF s).2, h', e2]
    exact hb'

  have hlab := GlobalTheory.CompanionTheory.Ar.LabelCount.labels_injective_card E H l c Ω 𝔐.cst
  have hinj : Function.Injective 𝔐.emb := hlab.1
  have hint : DirectSum.IsInternal fun s => eigSp 𝔐.ρ (𝔐.emb s) :=
    GlobalTheory.T.eigenspace_decomposition_internal Ω 𝔐.Li E 𝔐.ρ (CMType H ⊕ CMType H) 𝔐.emb hinj hlab.2
  let v : ∀ s, Module.Basis (Fin (labelRk D s)) Ω (eigSp 𝔐.ρ (𝔐.emb s)) := fun s =>
    (Module.Basis.span (hli s)).map (LinearEquiv.ofEq _ _ (hΩ s))
  have hB : ⇑(hint.collectedBasis v) = fun q : Σ s, Fin (labelRk D s) => b q.1 q.2 := by
    rw [hint.collectedBasis_coe]
    funext q
    simp [v, Module.Basis.span_apply]

  obtain ⟨g₀, hg₀⟩ := GlobalTheory.CompanionTheory.Ar.Flat.KonstReg.exists_const_stalk E H D l Xo c Y S Ω K J y 𝔐 p hu
  have hcst : ∀ x : c.F, 𝔐.cst x ∈ regAt 𝔐.ξ p := fun x =>
    RingHom.mem_range.2 ⟨g₀ x, by rw [← hg₀]; rfl⟩
  have hval : ∀ s a, 𝔐.emb s a ∈ regAt 𝔐.ξ p := fun s a => hcst _
  have hinv : ∀ s s' a, 𝔐.emb s a ≠ 𝔐.emb s' a → (𝔐.emb s a - 𝔐.emb s' a)⁻¹ ∈ regAt 𝔐.ξ p := by
    intro s s' a _
    have : (𝔐.emb s a - 𝔐.emb s' a)⁻¹ = 𝔐.cst (labelEmb c s a - labelEmb c s' a)⁻¹ := by
      rw [map_inv₀, map_sub]; rfl
    rw [this]
    exact hcst _
  have hsep : ∀ s s', s ≠ s' → ∃ a, 𝔐.emb s a ≠ 𝔐.emb s' a := by
    intro s s' h
    by_contra hc
    push_neg at hc
    exact h (hinj (RingHom.ext hc))
  have hstab : ∀ a, ∀ e ∈ 𝔐.M.lat p, 𝔐.ρ a e ∈ 𝔐.M.lat p := fun a e he =>
    haveI := 𝔐.t.act.hom a
    lat_stable 𝔐.M p (𝔐.t.act.act a) (𝔐.ρ a) (𝔐.act a) e he
  refine ⟨b, fun s i => hflag s i, ?_, ?_, ?_, ?_, hΩ⟩
  · intro s i e he hl
    refine mem_span_image_of_mem_flagStep _ (b s) (hli s) i he ?_
    rw [← hst s]
    refine ⟨hl, ?_⟩
    have h1 : flagStep Ω (b s) i ≤ Submodule.span Ω (Set.range (b s)) :=
      Submodule.span_mono (Set.image_subset_range _ _)
    have h2 := h1 he
    rw [hΩ s] at h2
    exact h2
  · rw [← hB]
    exact (hint.collectedBasis v).linearIndependent
  · rw [← hB]
    exact (hint.collectedBasis v).span_eq
  · exact eq_span_sigma (regAt 𝔐.ξ p) 𝔐.ρ 𝔐.emb (𝔐.M.lat p) hstab hval hinv hsep
      hint.submodule_iSup_eq_top b hst

end GlobalTheory.CompanionTheory.Ar.FlagFrames
