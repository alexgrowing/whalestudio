import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenWeil
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsChartOfLineBundle
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptFieldExtensionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalIsoOfIntegrallyClosedStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SegreRefineLineBundlesStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieOmegaLatticeVectorBundleStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateWeilPullbackStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagModelStatementHoldsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalCptIffNormalSchemeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorGenericStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptAwayFromPrimesStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptBlockRefinementStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimitiveRootHodgeCptStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtNoetherianModelNoetherianStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeDominantCompatStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HFlag

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

section Lattices

variable {X X' Z : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {ξ' : Spec (CommRingCat.of Ω) ⟶ X'} {ξ₁ : Spec (CommRingCat.of Ω) ⟶ Z}
  {V V' : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω V']

theorem flagStep_map (J : V →ₗ[Ω] V') {r : ℕ} (b : Fin r → V) (i : ℕ) :
    flagStep Ω (fun k => J (b k)) i = (flagStep Ω b i).map J := by
  unfold flagStep
  rw [Submodule.map_span, Set.image_image]

theorem flagStep_last {r : ℕ} (b : Fin r → V) : flagStep Ω b r = Submodule.span Ω (Set.range b) := by
  unfold flagStep
  congr 1
  ext x
  simp

theorem pull_span {f : X' ⟶ X} (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f (RingHom.id Ω)) (J : V →ₗ[Ω] V') {L : Lat ξ V}
    (q : Cpt ξ') {I : Type} {b : I → V}
    (hb : L ⟨f q.1, LatModel.dominates_spec hd q⟩ = Submodule.span _ (Set.range b)) :
    L.pull ξ' f J.toAddMonoidHom q = Submodule.span _ (Set.range fun k => J (b k)) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨hs, e, he, rfl⟩
    rw [hb] at he
    show J e ∈ Submodule.span (regAt ξ' q) (Set.range fun k => J (b k))
    induction he using Submodule.span_induction with
    | mem x hx => obtain ⟨k, rfl⟩ := hx; exact Submodule.subset_span ⟨k, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx =>
      have : J (c • x) = (⟨(c : Ω), LatModel.dominates_regAt hd q hs c.2⟩ : regAt ξ' q) • J x :=
        J.map_smul (c : Ω) x
      rw [this]
      exact Submodule.smul_mem _ _ hx
  · refine Submodule.span_mono ?_
    rintro _ ⟨k, rfl⟩
    exact ⟨LatModel.dominates_spec hd q, b k, hb ▸ Submodule.subset_span ⟨k, rfl⟩, rfl⟩

theorem isVBOn_pull {f : X' ⟶ X} (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f (RingHom.id Ω)) (J : V →ₗ[Ω] V')
    (hJ : Function.Injective J) {L : Lat ξ V} {T : Set (Cpt ξ)} {T' : Set (Cpt ξ')}
    (hT : ∀ q ∈ T', (⟨f q.1, LatModel.dominates_spec hd q⟩ : Cpt ξ) ∈ T) {r : ℕ} {W : Submodule Ω V}
    (h : L.IsVBOn T r W) : (L.pull ξ' f J.toAddMonoidHom).IsVBOn T' r (W.map J) := by
  intro p hp
  obtain ⟨U, hU, b, rfl, hb⟩ := h _ (hT p hp)
  refine ⟨f ⁻¹ᵁ U, hU, fun k => J (b k), ?_, fun q hq hqU => ?_⟩
  · rw [Submodule.map_span, ← Set.range_comp]; rfl
  · obtain ⟨h1, h2⟩ := hb _ (hT q hq) hqU
    exact ⟨h1.map' J (LinearMap.ker_eq_bot.2 hJ), pull_span hd J q h2⟩

theorem isFlag_pull {f : X' ⟶ X} (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f (RingHom.id Ω)) (J : V →ₗ[Ω] V')
    (hJ : Function.Injective J) {L : Lat ξ V} {r : ℕ} {b₀ : Fin r → V}
    (h : L.IsFlagVBOn Set.univ b₀) : (L.pull ξ' f J.toAddMonoidHom).IsFlagVBOn Set.univ fun k => J (b₀ k) := by
  intro p _
  obtain ⟨U, hU, b, hb0, hb⟩ := h ⟨f p.1, LatModel.dominates_spec hd p⟩ trivial
  refine ⟨f ⁻¹ᵁ U, hU, fun k => J (b k), fun i => ?_, fun q _ hqU => ?_⟩
  · rw [flagStep_map, flagStep_map, hb0]
  · obtain ⟨h1, h2⟩ := hb ⟨f q.1, LatModel.dominates_spec hd q⟩ trivial hqU
    exact ⟨h1.map' J (LinearMap.ker_eq_bot.2 hJ), pull_span hd J q h2⟩

theorem span_of_isVB {L : Lat ξ V} {r : ℕ} {W : Submodule Ω V} (h : L.IsVB r W) (p : Cpt ξ) :
    Submodule.span Ω (L p : Set V) = W := by
  obtain ⟨U, hU, b, rfl, hb⟩ := h p trivial
  rw [(hb p trivial hU).2, Submodule.span_span_of_tower]

theorem dom_iff {f : X' ⟶ X} : GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f (RingHom.id Ω) ↔ ξ' ≫ f = ξ := by
  unfold GlobalTheory.CompanionTheory.Ar.Dominates
  rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]

theorem regAt_iso (e : X' ≅ Z) (he : ξ' ≫ e.hom = ξ₁) (q : Cpt ξ') (h : genPt ξ₁ ⤳ e.hom q.1) :
    regAt ξ' q = regAt ξ₁ ⟨e.hom q.1, h⟩ := by
  apply le_antisymm
  · intro a ha
    have hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ₁ ξ' e.inv (RingHom.id Ω) := dom_iff.2 (by rw [← he]; simp)
    have h1 := LatModel.dominates_spec hd ⟨e.hom q.1, h⟩
    have h2 : (⟨e.inv (e.hom q.1), h1⟩ : Cpt ξ') = q := Subtype.ext (by simp)
    exact LatModel.dominates_regAt hd ⟨e.hom q.1, h⟩ h1 (by rw [h2]; exact ha)
  · intro a ha
    exact LatModel.dominates_regAt (dom_iff.2 he) q h ha

theorem mem_pull_iso (e : X' ≅ Z) (he : ξ' ≫ e.hom = ξ₁) (J : V →ₗ[Ω] V') (L : Lat ξ₁ V) (q : Cpt ξ')
    (h : genPt ξ₁ ⤳ e.hom q.1) (x : V') :
    x ∈ L.pull ξ' e.hom J.toAddMonoidHom q ↔ ∃ v ∈ L ⟨e.hom q.1, h⟩, J v = x := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨_, v, hv, rfl⟩ := hx; exact ⟨v, hv, rfl⟩
    | zero => exact ⟨0, zero_mem _, map_zero _⟩
    | add x y _ _ hx hy =>
      obtain ⟨v, hv, rfl⟩ := hx
      obtain ⟨w, hw, rfl⟩ := hy
      exact ⟨v + w, add_mem hv hw, map_add _ _ _⟩
    | smul c x _ hx =>
      obtain ⟨v, hv, rfl⟩ := hx
      refine ⟨(⟨(c : Ω), regAt_iso e he q h ▸ c.2⟩ : regAt ξ₁ ⟨e.hom q.1, h⟩) • v, Submodule.smul_mem _ _ hv, ?_⟩
      exact J.map_smul (c : Ω) v
  · rintro ⟨v, hv, rfl⟩
    exact Submodule.subset_span ⟨h, v, hv, rfl⟩

theorem flag_transfer (e : X' ≅ Z) (he : ξ' ≫ e.hom = ξ₁) {f : Z ⟶ X}
    (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ₁ ξ f (RingHom.id Ω)) (J : V →ₗ[Ω] V') (hJ : Function.Injective J) (L : Lat ξ V)
    (W : Submodule Ω V) {r : ℕ} {b₀ : Fin r → V}
    (h : ((L.pull ξ₁ f (AddMonoidHom.id V)).inter W).IsFlagVBOn Set.univ b₀) :
    ((L.pull ξ' (e.hom ≫ f) J.toAddMonoidHom).inter (W.map J)).IsFlagVBOn Set.univ fun k => J (b₀ k) := by
  have hd' : GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ (e.hom ≫ f) (RingHom.id Ω) :=
    dom_iff.2 (by rw [← Category.assoc, he, dom_iff.1 hd])
  convert isFlag_pull (dom_iff.2 he) J hJ h using 1
  funext q
  have hq := LatModel.dominates_spec (dom_iff.2 he) q
  have h1 : L.pull ξ' (e.hom ≫ f) J.toAddMonoidHom q =
      (L.pull ξ₁ f (AddMonoidHom.id V)).pull ξ' e.hom J.toAddMonoidHom q := by
    have a1 := pull_span hd' J (L := L) q (b := Subtype.val) (by rw [Subtype.range_coe]; exact (Submodule.span_eq _).symm)
    have a2 := pull_span hd LinearMap.id (L := L) ⟨e.hom q.1, hq⟩ (b := Subtype.val)
      (by rw [Subtype.range_coe]; exact (Submodule.span_eq _).symm)
    rw [a1]
    exact (pull_span (dom_iff.2 he) J q a2).symm
  ext x
  rw [mem_pull_iso e he J _ q hq]
  simp only [Lat.inter, Submodule.mem_inf, Submodule.restrictScalars_mem, h1, mem_pull_iso e he J _ q hq,
    Submodule.mem_map]
  constructor
  · rintro ⟨⟨v, hv, rfl⟩, w, hw, hwv⟩
    exact ⟨v, ⟨hv, hJ hwv ▸ hw⟩, rfl⟩
  · rintro ⟨v, ⟨hv, hw⟩, rfl⟩
    exact ⟨⟨v, hv, rfl⟩, v, hw, rfl⟩

theorem frame_quot {L : Lat ξ V} {p : Cpt ξ} {I : Type} [Finite I] {c : I → V} (hc : LinearIndependent Ω c)
    (hL : L p = Submodule.span _ (Set.range c)) (P : Set I) {F : Submodule Ω V}
    (hF : F = Submodule.span Ω (c '' P)) : ∃ (s : ℕ) (h : Fin s → V ⧸ F), (L.map F.mkQ).IsFrameAt h p := by
  obtain ⟨s, ⟨ε⟩⟩ := Finite.exists_equiv_fin (Pᶜ : Set I)
  refine ⟨s, fun k => F.mkQ (c (ε.symm k)), ?_, ?_⟩
  · have h1 : LinearIndependent Ω fun k => c (ε.symm k) :=
      hc.comp (fun k => (ε.symm k : I)) (Subtype.val_injective.comp ε.symm.injective)
    refine h1.map ?_
    rw [Submodule.ker_mkQ, hF]
    have h2 : Set.range (fun k => c (ε.symm k)) = c '' Pᶜ := by
      ext x
      constructor
      · rintro ⟨k, rfl⟩; exact ⟨_, (ε.symm k).2, rfl⟩
      · rintro ⟨i, hi, rfl⟩; exact ⟨ε ⟨i, hi⟩, by simp⟩
    rw [h2]
    exact hc.disjoint_span_image disjoint_compl_left
  · show (L p).map _ = _
    rw [hL, Submodule.map_span]
    apply le_antisymm
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      by_cases hi : i ∈ P
      · have : F.mkQ (c i) = 0 := (Submodule.Quotient.mk_eq_zero F).2 (hF ▸ Submodule.subset_span ⟨i, hi, rfl⟩)
        show F.mkQ (c i) ∈ _
        rw [this]; exact zero_mem _
      · exact Submodule.subset_span ⟨ε ⟨i, hi⟩, by simp⟩
    · refine Submodule.span_mono ?_
      rintro _ ⟨k, rfl⟩
      exact ⟨_, ⟨_, rfl⟩, rfl⟩

theorem isoAt_comp (e : X' ≅ Z) (he : ξ' ≫ e.hom = ξ₁) {f : Z ⟶ X} {q : Cpt ξ}
    (h : IsoAt ξ₁ f (RingHom.id Ω) q) : IsoAt ξ' (e.hom ≫ f) (RingHom.id Ω) q := by
  have hs := LatModel.dominates_spec (dom_iff.2 he)
  have hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ₁ ξ' e.inv (RingHom.id Ω) := dom_iff.2 (by rw [← he]; simp)
  obtain ⟨⟨p, hp, hu⟩, h2, h3⟩ := h
  refine ⟨⟨⟨e.inv p.1, LatModel.dominates_spec hd p⟩, by simpa using hp, fun p' hp' => Subtype.ext ?_⟩,
    fun p' hp' => ?_, (Category.assoc _ _ _).symm.trans (he ▸ h3)⟩
  · have := hu ⟨e.hom p'.1, hs p'⟩ (by simpa using hp')
    rw [← this]
    simp
  · rw [regAt_iso e he p' (hs p')]
    exact h2 _ (by simpa using hp')

theorem generic_map {Ω₀ : Type} [Field Ω₀] [Algebra Ω₀ Ω] {V₀ : Type} [AddCommGroup V₀] [Module Ω₀ V₀]
    (j : V₀ →+ V) {S : Type} {r : S → ℕ} (W : S → Submodule Ω₀ V₀) (b : ∀ σ, Fin (r σ) → V) (d : ℕ)
    (J : V →ₗ[Ω] V') (hJ : Function.Injective J) (h : IsGenericFlag (Ω' := Ω) j W b d) :
    IsGenericFlag (Ω' := Ω) (J.toAddMonoidHom.comp j) W (fun σ k => J (b σ k)) d := by
  obtain ⟨c, u, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨c, u, h1, fun a e => ?_, fun σ => (h3 σ).map' J (LinearMap.ker_eq_bot.2 hJ),
    fun σ => (h4 σ).map' J (LinearMap.ker_eq_bot.2 hJ), h5, h6, fun σ i => ?_, h8⟩
  · show J (j (a • e)) = _ • J (j e)
    rw [h2, map_smul]
  · rw [flagStep_map, h7, ← flagStep_map]
    simp

end Lattices

section Hodge

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ} {Ω : Type} [Field Ω]
  {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}

def pmodel (𝔐 : HodgeCpt Y S y) : PModel ℤ fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩ where
  X := 𝔐.X
  ξ := 𝔐.ξ
  s := specZIsTerminal.from _
  hover := specZIsTerminal.hom_ext _ _
  all := 𝔐.all
  tie := 𝔐.tie

theorem V_inter (𝔐 : HodgeCpt Y S y) (s : CMType H ⊕ CMType H) : (𝔐.V s).inter (𝔐.Vgen s) = 𝔐.V s := by
  funext q
  refine inf_eq_left.2 fun v hv => ?_
  have h : Submodule.span Ω (𝔐.V s q : Set 𝔐.Li) = 𝔐.Vgen s := span_of_isVB (𝔐.vb s) q
  show v ∈ 𝔐.Vgen s
  rw [← h]
  exact Submodule.subset_span hv

theorem quot_free (𝔐 : HodgeCpt Y S y) (b : ∀ s, Fin (labelRk D s) → 𝔐.Li)
    (hb : ∀ s, Submodule.span Ω (Set.range (b s)) = 𝔐.Vgen s) (q : Cpt 𝔐.ξ) (hq : q ∈ genFib 𝔐.ξ)
    (hf : ∀ s, (𝔐.V s).IsFlagVBOn {q} (b s)) (s : CMType H ⊕ CMType H) (n : ℕ) :
    (∃ (r : ℕ) (h : Fin r → 𝔐.Li ⧸ flagStep Ω (b s) n), ((𝔐.V s).map (flagStep Ω (b s) n).mkQ).IsFrameAt h q) ∧
    ∃ (r : ℕ) (h : Fin r → 𝔐.Li ⧸ flagStep Ω (b s) n), (𝔐.M.lat.map (flagStep Ω (b s) n).mkQ).IsFrameAt h q := by
  have hβ : Function.Injective (algebraMap (𝓞 c.F) c.F) := RingOfIntegers.coe_injective
  choose U hU b' hb' hfr using fun s => hf s q rfl
  replace hfr := fun s => hfr s q rfl (hU s)
  have hsp : ∀ t, Submodule.span Ω (Set.range (b' t)) = 𝔐.Vgen t := fun t => by
    rw [← flagStep_last, hb', flagStep_last, hb]
  refine ⟨frame_quot (hfr s).1 (hfr s).2 {k | (k : ℕ) < n} (hb' s n).symm, ?_⟩
  obtain ⟨-, -, -, -, -, -, hind, -⟩ := GlobalTheory.T.hodge_cpt_interior_generic E H D l Xo c _ _ Y S Ω K J y 𝔐 hβ
  obtain ⟨h1, -, h2⟩ := GlobalTheory.T.hodge_cpt_away_from_primes E H D l Xo c _ _ Y S Ω K J y 𝔐 hβ q fun r hr h => h (hq r hr.pos)
  have hli : LinearIndependent Ω fun a : Σ t, Fin (labelRk D t) => b' a.1 a.2 := by
    refine linearIndependent_iUnion_finite (fun t => (hfr t).1) fun t T _ ht => ?_
    simp only [hsp]
    exact hind.disjoint_biSup ht
  refine frame_quot hli ?_ (Sigma.mk s '' {k | (k : ℕ) < n}) ?_
  · rw [h2]
    simp only [← h1, (hfr _).2]
    rw [← Submodule.span_iUnion, Set.range_sigma_eq_iUnion_range]
  · rw [Set.image_image]
    exact (hb' s n).symm

theorem omP_pull [CharZero Ω] (hW : Out.WeilSt) {K' : Type} [Fintype K'] {J' : K' → Type} [∀ k, Fintype (J' k)]
    {y' : (Σ k, J' k) → Ω} (𝔐 : HodgeCpt Y S y) (A : HodgeCpt Y S y') (g : A.X ⟶ 𝔐.X)
    (hd : GlobalTheory.CompanionTheory.Ar.Dominates A.ξ 𝔐.ξ g (RingHom.id Ω)) (hf : A.f = g ≫ 𝔐.f) (hR : A.R = 𝔐.R)
    (m : SABMap A.t 𝔐.t g) (φ : 𝔐.Li ≃ₗ[Ω] A.Li)
    (hφ : ∀ v, (A.M.pt (φ v)).left ≫ m.φ = spMap (dualMap (RingHom.id Ω)) ≫ (𝔐.M.pt v).left)
    (y₀ : Sp Ω ⟶ Xo.XF c) (hy : 𝔐.ξ ≫ 𝔐.f = y₀ ≫ Y.j) (p : ℕ) (hp : p ∈ S)
    (hζ : ∃ ζ : Ω, IsPrimitiveRoot ζ (p ^ 𝔐.R p))
    (h : (HT.omP 𝔐 p).IsVBOn {q | InFibre 𝔐.ξ p q} (Module.finrank Ω 𝔐.Li) ⊤) :
    (HT.omP A p).IsVBOn {q | InFibre A.ξ p q} (Module.finrank Ω A.Li) ⊤ := by
  classical
  have hn : p ^ 𝔐.R p ≠ 0 := pow_ne_zero _ (𝔐.S_prime p hp).ne_zero
  obtain ⟨ζ, hζ⟩ := hζ
  obtain ⟨ζ, rfl⟩ := hζ.isUnit hn
  have hζ' := IsPrimitiveRoot.coe_units_iff.1 hζ
  obtain ⟨-, e, -, -, -, -, he, -⟩ := GlobalTheory.T.primitive_root_hodge_cpt hW E H D l Xo c Y S Ω K J y 𝔐 y₀ p ζ hp hy hζ'
  obtain ⟨-, e', -, -, -, -, he', -⟩ := GlobalTheory.T.primitive_root_hodge_cpt hW E H D l Xo c Y S Ω K' J' y' A y₀ p ζ hp
    (by rw [hf, ← Category.assoc, dom_iff.1 hd, hy]) (by rw [hR]; exact hζ')
  have := ((GlobalTheory.T.regAt_noetherian_model_noetherian _ Ω 𝔐.ξ ℤ _ _ 𝔐.tie).2 𝔐.all).1
  have := ((GlobalTheory.T.regAt_noetherian_model_noetherian _ Ω A.ξ ℤ _ _ A.tie).2 A.all).1
  rw [hR] at he'
  have key := (GlobalTheory.T.hodge_tate_weil_pullback 𝔐.X Ω 𝔐.ξ 𝔐.tie.gen ((GlobalTheory.T.normal_cpt_iff_normal_scheme _ Ω 𝔐.ξ 𝔐.tie.gen 𝔐.all).2.2 𝔐.normal) 𝔐.t.G 𝔐.t.semi
    𝔐.t.PP.L _ (Nat.one_le_iff_ne_zero.2 hn) (𝔐.tors p hp) e he 𝔐.Li 𝔐.M A.X Ω A.ξ A.tie.gen
    ((GlobalTheory.T.normal_cpt_iff_normal_scheme _ Ω A.ξ A.tie.gen A.all).2.2 A.normal) g (RingHom.id Ω) hd A.t.G m.φ m.cart A.t.PP.L e' he' A.Li
    A.M φ.toLinearMap.toAddMonoidHom φ.symm.dualMap.toLinearMap.toAddMonoidHom hφ (fun w v => by simp)).1
  have h2 := isVBOn_pull hd φ.symm.dualMap.toLinearMap φ.symm.dualMap.injective
    (T := {q | InFibre 𝔐.ξ p q}) (T' := {q | InFibre A.ξ p q}) (fun q hq (hu : unitAt _ _ _) => hq ⟨hu.1, LatModel.dominates_regAt hd q _ hu.2.1,
      LatModel.dominates_regAt hd q _ hu.2.2⟩) h
  rw [← key, Submodule.map_top, LinearEquiv.range, φ.finrank_eq, ← hR] at h2
  exact h2

end Hodge

theorem exists_flag_model : Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (y₀ : Sp Ω ⟶ Xo.XF c) (b : ∀ s, Fin (labelRk D s) → 𝔐.Li) (Li₀ : Type) (_ : AddCommGroup Li₀) (_ : Module 𝔐.Ω₀ Li₀) (M₀ : LieModel Y.t.G 𝔐.ξ₀ Li₀) (j : Li₀ →+ 𝔐.Li) (V₀ : CMType H ⊕ CMType H → Submodule 𝔐.Ω₀ Li₀) (d : ℕ), 𝔐.ξ ≫ 𝔐.f = y₀ ≫ Y.j → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr E → p ∈ S) → (∀ p ∈ S, HT.HTFree 𝔐 p) → (∀ p ∈ S, ∃ ζ : Ω, IsPrimitiveRoot ζ (p ^ 𝔐.R p)) → (∀ s, Submodule.span Ω (Set.range (b s)) = 𝔐.Vgen s) → (∀ e, (𝔐.M.pt (j e)).left ≫ 𝔐.m.φ = spMap (dualMap 𝔐.fn) ≫ (M₀.pt e).left) → (∀ s e, e ∈ V₀ s ↔ j e ∈ 𝔐.Vgen s) → (letI := 𝔐.fn.toAlgebra; IsGenericFlag (Ω' := Ω) j V₀ b d) → ∃ (K' : Type) (_ : Fintype K') (J' : K' → Type) (_ : ∀ k, Fintype (J' k)) (y' : (Σ k, J' k) → Ω) (bk : K → K') (bx : ∀ k, J k ≃ J' (bk k)) (𝔐' : HodgeCpt Y S y') (g : 𝔐'.X ⟶ 𝔐.X) (Fl : 𝔐'.Flag) (xdeg : CMType H × Fin (D.p + D.q) → K' → ℤ) (e : CMType H × Fin (D.p + D.q) → Ω), Function.Injective bk ∧ (∀ k a, y' ⟨bk k, bx k a⟩ = y ⟨k, a⟩) ∧ GlobalTheory.CompanionTheory.Ar.Dominates 𝔐'.ξ 𝔐.ξ g (RingHom.id Ω) ∧ 𝔐'.f = g ≫ 𝔐.f ∧ 𝔐'.R = 𝔐.R ∧ 𝔐'.cst = 𝔐.cst ∧ (∀ p ∈ S, HT.HTFree 𝔐' p) ∧ Fl.deg = d ∧ (∀ s i, (𝔐'.M.pt (Fl.b s i)).left ≫ 𝔐'.m.φ = spMap (dualMap (RingHom.id Ω)) ≫ (𝔐.M.pt (b s i)).left ≫ 𝔐.m.φ) ∧ Fl.RootLines xdeg e ∧ (∀ s, (𝔐'.dR s).IsFlagVBOn Set.univ (Fl.b s)) ∧ ∀ q ∈ genFib 𝔐.ξ, (∀ s, (𝔐.V s).IsFlagVBOn {q} (b s)) → IsoAt 𝔐'.ξ g (RingHom.id Ω) q := by
  intro hW E _ _ _ H D l Xo c Y S Ω _ _ K _ J _ y 𝔐 y₀ b Li₀ _ _ M₀ j V₀ d hy hS hHT hζ hb hj hV₀ hgen
  classical
  have hli : ∀ s, LinearIndependent Ω (b s) := by
    obtain ⟨-, -, -, -, -, h, -⟩ := hgen
    exact h
  have hmem : ∀ s k, b s k ∈ 𝔐.Vgen s := fun s k => hb s ▸ Submodule.subset_span ⟨k, rfl⟩
  have hlat := (GlobalTheory.T.lie_omega_lattice_vector_bundle 𝔐.X Ω 𝔐.ξ 𝔐.t.G 𝔐.Li 𝔐.M 𝔐.tie.gen 𝔐.t.semi.smooth).1
  obtain ⟨κ', _, y₁, M', f, hd, hN, -, hfl, -, hnorm⟩ := GlobalTheory.T.FlagModelStatement_holds ℤ Ω _ _ (pmodel 𝔐) Empty (fun _ => Empty)
    (fun a => a.elim) ((CMType H ⊕ CMType H) × Bool) 𝔐.Li
    (fun σ => if σ.2 then 𝔐.V σ.1 else 𝔐.M.lat) (fun σ => if σ.2 then labelRk D σ.1 else Module.finrank Ω 𝔐.Li)
    (fun σ => labelRk D σ.1) (fun σ => if σ.2 then 𝔐.Vgen σ.1 else ⊤) (fun σ => b σ.1) (fun a => a.elim)
    (by rintro ⟨s, _ | _⟩; exacts [hlat, 𝔐.vb s]) (fun σ => hli σ.1)
    (by rintro ⟨s, _ | _⟩ k; exacts [Submodule.mem_top, hmem s k])
  change M'.X ⟶ 𝔐.X at f
  change GlobalTheory.CompanionTheory.Ar.Dominates M'.ξ 𝔐.ξ f (RingHom.id Ω) at hd
  obtain ⟨K₁, _, J₁, _, y₁, bk, bx, -, hbk, hbx, htie, -⟩ := GlobalTheory.T.segre_refine_line_bundles ℤ Ω κ' y₁ M' K J y Empty (fun a => a.elim)
    (fun p => by
      obtain ⟨c₀, h0, h1⟩ := 𝔐.tie.cover ⟨f p.1, LatModel.dominates_spec hd p⟩
      exact ⟨c₀, h0, fun c' => LatModel.dominates_regAt hd p _ (h1 c')⟩) (fun a => a.elim)
  obtain ⟨A, e, j₁, m, he, hf, hm, hcst, hR, hext, hpt, hHT', hV⟩ := GlobalTheory.T.hodge_cpt_field_extension E H D l Xo c _ _ Y S Ω Ω
    (RingHom.id Ω) K K₁ J J₁ y y₁ 𝔐 y₀ M'.X M'.ξ f hy hS (fun p hp => (hHT p hp).2) M'.all htie
    ((GlobalTheory.T.normal_cpt_iff_normal_scheme _ Ω M'.ξ M'.tie.gen M'.all).2.1 hN) hd
  have hd' : GlobalTheory.CompanionTheory.Ar.Dominates A.ξ 𝔐.ξ (e.hom ≫ f) (RingHom.id Ω) :=
    dom_iff.2 (by rw [← Category.assoc, he, dom_iff.1 hd])
  obtain ⟨-, hsurj, hlat'⟩ := GlobalTheory.T.lie_lattice_dominant_compat 𝔐.X A.X Ω Ω 𝔐.ξ A.ξ (e.hom ≫ f) (RingHom.id Ω) 𝔐.t.G A.t.G m.φ 𝔐.Li A.Li
    𝔐.M A.M j₁ 𝔐.tie.gen A.tie.gen hd' m.cart 𝔐.t.semi.smooth hpt
  let φ₀ : 𝔐.Li →ₗ[Ω] A.Li := { toFun := j₁, map_add' := j₁.map_add, map_smul' := hext.1 }
  have hinj : Function.Injective φ₀ := by
    refine (injective_iff_map_eq_zero φ₀).2 fun v hv => by_contra fun h0 => ?_
    exact (hext.2 1 (fun _ => v) (linearIndependent_unique_iff.2 h0)).ne_zero 0 hv
  have hsur : Function.Surjective φ₀ := by
    rw [← LinearMap.range_eq_top, ← Submodule.span_eq (LinearMap.range φ₀)]
    exact hsurj
  let φ : 𝔐.Li ≃ₗ[Ω] A.Li := LinearEquiv.ofBijective φ₀ ⟨hinj, hsur⟩
  have hVg : ∀ s, A.Vgen s = (𝔐.Vgen s).map φ₀ := fun s => by
    have h1 : (A.V s).IsVB (labelRk D s) (A.Vgen s) := A.vb s
    have h2 : (A.V s).IsVB (labelRk D s) ((𝔐.Vgen s).map φ₀) := by
      rw [hV]
      exact isVBOn_pull hd' φ₀ hinj (T := Set.univ) (fun _ _ => trivial) (𝔐.vb s)
    exact (span_of_isVB h1 ⟨genPt A.ξ, specializes_rfl⟩).symm.trans (span_of_isVB h2 _)
  have hflV : ∀ s, (A.V s).IsFlagVBOn Set.univ fun k => φ₀ (b s k) := fun s => by
    have h := flag_transfer e he hd φ₀ hinj (𝔐.V s) _ (hfl (s, true))
    rw [← V_inter A s, hVg, ← hb, hV]
    exact h
  have hflR : ∀ s, (A.dR s).IsFlagVBOn Set.univ fun k => φ₀ (b s k) := fun s => by
    have h := flag_transfer e he hd φ₀ hinj 𝔐.M.lat _ (hfl (s, false))
    show (A.M.lat.inter (A.Vgen s)).IsFlagVBOn _ _
    rw [hVg, ← hb, hlat']
    exact h
  have hpt' : ∀ v, (A.M.pt (φ₀ v)).left ≫ A.m.φ = (𝔐.M.pt v).left ≫ 𝔐.m.φ := fun v => by
    have h1 : dualMap (RingHom.id Ω) = RingHom.id _ := by
      ext a <;> simp [dualMap]
    have h2 := hpt v
    rw [h1, spMap, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp] at h2
    rw [hm, ← Category.assoc, ← h2]
    rfl
  let A₁ : HodgeCpt Y S y₁ :=
    { A with
      Ω₀ := 𝔐.Ω₀, fld₀ := 𝔐.fld₀, ξ₀ := 𝔐.ξ₀, gen₀ := 𝔐.gen₀, fn := 𝔐.fn
      fn_over := by
        have h := 𝔐.fn_over
        unfold GlobalTheory.CompanionTheory.Ar.Dominates at h ⊢
        rw [← h, hf, ← Category.assoc e.hom, ← Category.assoc, dom_iff.1 hd'] }
  let F₁ : A₁.Flag :=
    { b := fun s k => φ₀ (b s k)
      sub := hflV
      Li₀ := Li₀
      M₀ := M₀
      j := φ₀.toAddMonoidHom.comp j
      j_pt := fun v => (hpt' (j v)).trans (hj v)
      V₀ := V₀
      V₀_mem := fun s v => by
        rw [hV₀]
        show _ ↔ φ₀ (j v) ∈ A.Vgen s
        rw [hVg]
        exact ⟨fun h => ⟨_, h, rfl⟩, fun ⟨w, hw, h⟩ => hinj h ▸ hw⟩
      deg := d
      generic := by
        letI := 𝔐.fn.toAlgebra
        exact generic_map j V₀ b d φ₀ hinj hgen }
  obtain ⟨K', _, J', _, y', κ, v, tie', xdeg, e₀, hκ, hv, hroot⟩ := GlobalTheory.T.hodge_cpt_block_refinement E H D l Xo c _ _ Y S Ω K₁ J₁ y₁ A₁ F₁
  let A₂ : HodgeCpt Y S y' := { A₁ with tie := tie' }
  let F₂ : A₂.Flag := { F₁ with }
  refine ⟨K', inferInstance, J', inferInstance, y', κ ∘ bk, fun k => (bx k).trans (v (bk k)), A₂, e.hom ≫ f, F₂, xdeg,
    e₀, hκ.comp hbk, fun k a => (hv _ _).trans (hbx k a), hd', hf.trans (Category.assoc _ _ _).symm, hR, hcst,
    fun p hp => ⟨?_, hHT' p hp⟩, rfl, fun s i => ?_, hroot, hflR, fun q hq hfq => ?_⟩
  · exact omP_pull hW 𝔐 A (e.hom ≫ f) hd' (hf.trans (Category.assoc _ _ _).symm) hR m φ hpt y₀ hy p hp (hζ p hp)
      (hHT p hp).1
  · show (A.M.pt (j₁ (b s i))).left ≫ A.m.φ = _
    rw [hm, ← Category.assoc, hpt, Category.assoc]
  · refine isoAt_comp e he (GlobalTheory.T.normal_iso_of_integrally_closed _ Ω 𝔐.ξ _ M'.ξ f q (hnorm q (fun a => a.elim) ?_)
      ((GlobalTheory.T.normal_cpt_iff_normal_scheme _ Ω 𝔐.ξ 𝔐.tie.gen 𝔐.all).2.2 𝔐.normal q))
    rintro ⟨s, _ | _⟩ n
    exacts [(quot_free 𝔐 b hb q hq hfq s n).2, (quot_free 𝔐 b hb q hq hfq s n).1]

end GlobalTheory.CompanionTheory.Ar.HFlag
