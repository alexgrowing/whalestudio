import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExtHomInjective
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsGlobalOfFibLocNeZero
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsIsomMapOfEq
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AutSubApplyMem

open NumberField Module Filter

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.LIOrb

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
variable {V' : Type} [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] [Module (𝓞 K) V']
  [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

def MSet (S : VecSplit h h') (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) :
    Set (Submodule (𝓞 K) V) :=
  {M | (∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L) = M) ∧ S.x₀ ∈ M}

def IsMReps (S : VecSplit h h') (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F))
    (s : Finset (Submodule (𝓞 K) V')) (R : Finset (Submodule (𝓞 K) V)) : Prop :=
  (∀ M ∈ R, M ∈ MSet S L 𝔭 ∧ S.cut M ∈ s) ∧
  ∀ M ∈ MSet S L 𝔭, ∃! M₀, M₀ ∈ R ∧
    ∃ g' ∈ Formalism.HermitianLatticesTheory.isom h', Formalism.HermitianLatticesTheory.gmap (SplitBAux.extOf S g') M₀ = M

theorem mem_fib_iff (S : VecSplit h h') (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F))
    {T : Submodule (𝓞 K) V'} (hT : locF 𝔭 T = T) (Λ : Submodule (𝓞 K) V) :
    (locF 𝔭 Λ = Λ ∧ (∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L) = Λ) ∧ S.x₀ ∈ Λ ∧
      S.cut Λ = locF 𝔭 T) ↔ (Λ ∈ MSet S L 𝔭 ∧ S.cut Λ = T) := by
  constructor
  · rintro ⟨_, hg, hx, hc⟩
    exact ⟨⟨hg, hx⟩, hc.trans hT⟩
  · rintro ⟨⟨⟨g, hg, hgL⟩, hx⟩, hc⟩
    refine ⟨?_, ⟨g, hg, hgL⟩, hx, hc.trans hT.symm⟩
    rw [← hgL, LocalizedFibreSets.gmap_locF, LocalizedFibreSets.locF_idem]

theorem card_fib (S : VecSplit h h') (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F))
    {T : Submodule (𝓞 K) V'} (hT : locF 𝔭 T = T) :
    Nat.card {Λ // Λ ∈ MSet S L 𝔭 ∧ S.cut Λ = T} = fibLoc S L 𝔭 T := by
  unfold fibLoc
  exact Nat.card_congr (Equiv.subtypeEquivRight fun Λ => (mem_fib_iff S L 𝔭 hT Λ).symm)

theorem exists_mReps (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm) (hd : IsTotPosDef h)
    (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) (hx : h S.x₀ S.x₀ = algebraMap F K (n : F))
    {s : Finset (Submodule (𝓞 K) V')} (hsr : IsLocReps S L 𝔭 s) : ∃ R, IsMReps S L 𝔭 s R := by
  have hfin : {M | M ∈ MSet S L 𝔭 ∧ S.cut M ∈ s}.Finite := by
    have hsub : {M | M ∈ MSet S L 𝔭 ∧ S.cut M ∈ s} ⊆
        ⋃ T ∈ s, {M | M ∈ MSet S L 𝔭 ∧ S.cut M = T} := by
      rintro M ⟨h1, h2⟩
      exact Set.mem_biUnion h2 ⟨h1, rfl⟩
    refine (Set.Finite.biUnion s.finite_toSet fun T hT => ?_).subset hsub
    obtain ⟨hT1, -, hT3⟩ := hsr.1 T hT
    rw [← card_fib S L 𝔭 hT1] at hT3
    exact Nat.finite_of_card_ne_zero hT3
  have hcov : ∀ M ∈ MSet S L 𝔭, ∃ t ∈ {M | M ∈ MSet S L 𝔭 ∧ S.cut M ∈ s},
      ∃ g' ∈ Formalism.HermitianLatticesTheory.isom h', Formalism.HermitianLatticesTheory.gmap (SplitBAux.extOf S g') t = M := by
    intro M hM
    obtain ⟨⟨g, hg, rfl⟩, hxM⟩ := hM
    obtain ⟨a, b, c⟩ := OrbF.cut_props hK hF hs hd S hL hLi h𝔭 hg hxM
    obtain ⟨T₀, ⟨hT₀, g', hg', e⟩, -⟩ := hsr.2 _ a b c
    refine ⟨Formalism.HermitianLatticesTheory.gmap (SplitBAux.extOf S g'⁻¹) (Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L)),
      ⟨OrbF.through_smul hs S (inv_mem hg') ⟨⟨g, hg, rfl⟩, hxM⟩, ?_⟩, g', hg',
      OrbF.gmap_extOf_inv S g' _⟩
    rw [StabilizerLattices.cut_gmap_extOf, ← e, ← autSub_gmap_mul, inv_mul_cancel, autSub_gmap_one]
    exact hT₀
  exact OrbF.exists_reps _ (OrbF.orb_equiv S) (MSet S L 𝔭) _ hfin hcov

theorem nkCount_eq_sum (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm) (hd : IsTotPosDef h)
    (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) (hx : h S.x₀ S.x₀ = algebraMap F K (n : F))
    {s : Finset (Submodule (𝓞 K) V')} {R : Finset (Submodule (𝓞 K) V)} (hR : IsMReps S L 𝔭 s R) :
    ∀ᶠ J in atTop, ∀ᶠ k in atTop,
      nkCount h L 𝔭 k n = ∑ M ∈ R, cnt h M 𝔭 k n (tube (autSub h M) M 𝔭 J S.x₀) := by
  classical
  have hch : ∀ M : Submodule (𝓞 K) V, ∃ g : V ≃ₗ[K] V,
      M ∈ R → g ∈ Formalism.HermitianLatticesTheory.isom h ∧ Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L) = M := by
    intro M
    by_cases hM : M ∈ R
    · obtain ⟨⟨⟨g, hg, e⟩, -⟩, -⟩ := hR.1 M hM
      exact ⟨g, fun _ => ⟨hg, e⟩⟩
    · exact ⟨1, fun hM' => absurd hM' hM⟩
  choose γ hγ using hch
  obtain ⟨c₀, hc₀⟩ := exists_exact_near hK hF hs hd hL hLi h𝔭 hn ⟨S.x₀, hx⟩
  filter_upwards [eventually_ge_atTop (4 * vF 𝔭 n + eA h (locF 𝔭 L) 𝔭 + 1)] with J hJ
  filter_upwards [eventually_ge_atTop (c₀ + J)] with k hk
  have hterm : ∀ M ∈ R, cnt h M 𝔭 k n (tube (autSub h M) M 𝔭 J S.x₀) =
      cnt h (locF 𝔭 L) 𝔭 k n
        (tube (autSub h (locF 𝔭 L)) (locF 𝔭 L) 𝔭 J ((γ M).symm S.x₀)) := by
    intro M hM
    obtain ⟨hg, e⟩ := hγ M hM
    have h1 := cnt_gmap hg (locF 𝔭 L) 𝔭 k n
      (tube (autSub h (locF 𝔭 L)) (locF 𝔭 L) 𝔭 J ((γ M).symm S.x₀))
    rw [OrbF.image_tube hg, e] at h1
    exact h1
  have hst : ∀ M ∈ R, ∀ y ∈ tube (autSub h (locF 𝔭 L)) (locF 𝔭 L) 𝔭 J ((γ M).symm S.x₀),
      ∀ z ∈ ((extP K 𝔭) ^ k • locF 𝔭 L : Submodule (𝓞 K) V),
      y + z ∈ tube (autSub h (locF 𝔭 L)) (locF 𝔭 L) 𝔭 J ((γ M).symm S.x₀) :=
    fun M _ y hy z hz => OrbF.tube_add _ _ 𝔭 (by omega) _ hy hz
  have hdis : ∀ M ∈ R, ∀ M' ∈ R, M ≠ M' →
      Disjoint (tube (autSub h (locF 𝔭 L)) (locF 𝔭 L) 𝔭 J ((γ M).symm S.x₀))
        (tube (autSub h (locF 𝔭 L)) (locF 𝔭 L) 𝔭 J ((γ M').symm S.x₀)) := by
    intro M hM M' hM' hne
    rw [Set.disjoint_left]
    intro y h1 h2
    obtain ⟨hg, e⟩ := hγ M hM
    obtain ⟨hg', e'⟩ := hγ M' hM'
    have hxM := (hR.1 M hM).1.2
    have hxM' := (hR.1 M' hM').1.2
    obtain ⟨g', hg'', e''⟩ := OrbF.same_orbit hK hF hs hd S hL hLi h𝔭 hn hx hg hg'
      (by rw [e]; exact hxM) (by rw [e']; exact hxM') hJ h1 h2
    rw [e, e'] at e''
    exact hne ((hR.2 M' (hR.1 M' hM').1).unique ⟨hM, g', hg'', e''⟩
      ⟨hM', 1, one_mem _, by rw [OrbF.extOf_one, autSub_gmap_one]⟩)
  rw [Finset.sum_congr rfl hterm, ← cnt_biUnion h (locF 𝔭 L) 𝔭 k n (finite_quot hL h𝔭 k) R _ hst hdis,
    ← nkCount_locF hF h L 𝔭 h𝔭 k n]
  symm
  apply cnt_eq_nkCount
  intro y hy hyn
  obtain ⟨y', hy', hn', hclose⟩ := hc₀ k (by omega) y hy hyn
  have hy0 : y' ≠ 0 := by
    rintro rfl
    rw [map_zero] at hn'
    exact S.hx₀ (hx.trans hn'.symm)
  obtain ⟨g, hg, hgy⟩ := exists_isom_map_of_eq hK hs hd hy0 (hn'.trans hx.symm)
  have hMS : Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L) ∈ MSet S L 𝔭 := ⟨⟨g, hg, rfl⟩, ⟨y', hy', hgy⟩⟩
  obtain ⟨M₀, ⟨hM₀, g', hg', e⟩, -⟩ := hR.2 _ hMS
  obtain ⟨hγ₀, e₀⟩ := hγ M₀ hM₀
  rw [← e₀] at e
  obtain ⟨u, hu, hu'⟩ := OrbF.exists_on_orbit hs S hg hγ₀ hg' e hgy
  refine Set.mem_biUnion hM₀ ⟨u, hu, ?_⟩
  rw [hu', ← neg_sub]
  exact neg_mem (pow_smul_anti 𝔭 _ (by omega) hclose)

theorem sum_oM (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm) (hd : IsTotPosDef h)
    (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {s : Finset (Submodule (𝓞 K) V')} (hsr : IsLocReps S L 𝔭 s)
    {R : Finset (Submodule (𝓞 K) V)} (hR : IsMReps S L 𝔭 s R)
    (w : Submodule (𝓞 K) V' → ℝ) :
    ∑ M ∈ R, (oM S M : ℝ) * w (S.cut M) = ∑ T ∈ s, (fibLoc S L 𝔭 T : ℝ) * w T := by
  have key := @sum_relIndex_fibre (Formalism.HermitianLatticesTheory.isom h') _ _ _ (OrbF.actV S) (OrbF.actV' h') S.cut
    (fun g M => StabilizerLattices.cut_gmap_extOf S g.1 M) (MSet S L 𝔭)
    (fun g M hM => OrbF.through_smul hs S g.2 hM) R s hR.1
    (fun M hM => by
      obtain ⟨t, ⟨ht, g', hg', e⟩, huniq⟩ := hR.2 M hM
      exact ⟨t, ⟨ht, ⟨g', hg'⟩, e⟩, fun t' ht' => huniq t' ⟨ht'.1, ht'.2.choose.1, ht'.2.choose.2,
        ht'.2.choose_spec⟩⟩)
    (fun y hy y' hy' hg => by
      obtain ⟨g, e⟩ := hg
      obtain ⟨a, b, c⟩ := hsr.1 y' hy'
      exact (hsr.2 y' a b c).unique ⟨hy, g.1, g.2, e⟩ ⟨hy', 1, one_mem _, autSub_gmap_one _⟩)
    (fun M hM => by
      rw [OrbF.relIndex_stab hs]
      obtain ⟨⟨⟨g, hg, rfl⟩, hxM⟩, -⟩ := hR.1 M hM
      rw [LocalizedFibreSets.gmap_locF] at hxM ⊢
      exact oM_ne_zero hs S (LocalizedFibreSets.isLattice_gmap g hL) h𝔭 hxM) w
  calc ∑ M ∈ R, (oM S M : ℝ) * w (S.cut M) = _ :=
        Finset.sum_congr rfl fun M _ => by rw [← OrbF.relIndex_stab hs]
    _ = _ := key
    _ = _ := Finset.sum_congr rfl fun T hT => by rw [card_fib S L 𝔭 (hsr.1 T hT).1]

end Formalism.HermitianLattices.Ext.L3.LIOrb
