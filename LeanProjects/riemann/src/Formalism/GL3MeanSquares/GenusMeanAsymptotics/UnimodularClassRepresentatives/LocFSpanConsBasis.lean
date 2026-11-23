import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocFEqLocFAdjoinCut
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.EqBlockOfFix
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsExactLift
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.RedEqOfSubMem

open NumberField Module Matrix

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.PinB

open idealPowerSpanBounds integralBasisSpans

variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

omit [NumberField K] [FiniteDimensional K V] [FiniteDimensional K V'] in

def prodEquiv (S : VecSplit h h') : (K × V') ≃ₗ[K] V :=
  LinearEquiv.ofBijective ((LinearMap.toSpanSingleton K V S.x₀).coprod S.ι) (by
    constructor
    · rintro ⟨c, a⟩ ⟨c', a'⟩ e
      simp only [LinearMap.coprod_apply, LinearMap.toSpanSingleton_apply] at e
      obtain ⟨rfl, rfl⟩ := S.comb_eq_iff.1 e
      rfl
    · intro v
      obtain ⟨c, a, rfl⟩ := S.cover v
      exact ⟨(c, a), by simp only [LinearMap.coprod_apply, LinearMap.toSpanSingleton_apply]⟩)

omit [FiniteDimensional K V] [FiniteDimensional K V'] in
theorem prodEquiv_apply (S : VecSplit h h') (c : K) (a : V') :
    prodEquiv S (c, a) = c • S.x₀ + S.ι a := by
  show (LinearMap.toSpanSingleton K V S.x₀).coprod S.ι (c, a) = _
  rw [LinearMap.coprod_apply, LinearMap.toSpanSingleton_apply]

def consBasis (S : VecSplit h h') {κ : Type} (b' : Basis κ K V') : Basis (Unit ⊕ κ) K V :=
  ((Basis.singleton Unit K).prod b').map (prodEquiv S)

omit [FiniteDimensional K V] [FiniteDimensional K V'] in
theorem consBasis_inl (S : VecSplit h h') {κ : Type} (b' : Basis κ K V') (u : Unit) :
    consBasis S b' (Sum.inl u) = S.x₀ := by
  simp [consBasis, prodEquiv_apply]

omit [FiniteDimensional K V] [FiniteDimensional K V'] in
theorem consBasis_inr (S : VecSplit h h') {κ : Type} (b' : Basis κ K V') (i : κ) :
    consBasis S b' (Sum.inr i) = S.ι (b' i) := by
  simp [consBasis, prodEquiv_apply]

omit [FiniteDimensional K V] [FiniteDimensional K V'] in
theorem locF_span_consBasis (S : VecSplit h h') {κ : Type} (b' : Basis κ K V')
    {T : Submodule (𝓞 K) V'} (hbT : ∀ i, b' i ∈ T) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (hb' : locF 𝔭 (spanO b') = locF 𝔭 T) :
    locF 𝔭 (spanO (consBasis S b')) = locF 𝔭 (S.adjoin T) := by
  have key : ∀ {A B : Submodule (𝓞 K) V}, A ≤ locF 𝔭 B → B ≤ locF 𝔭 A →
      locF 𝔭 A = locF 𝔭 B := by
    intro A B hAB hBA
    apply le_antisymm
    · exact (Formalism.HermitianLatticesTheory.genusCovol_locS_mono _ hAB).trans (Formalism.HermitianLatticesTheory.genusCovol_locS_idem _ _)
    · exact (Formalism.HermitianLatticesTheory.genusCovol_locS_mono _ hBA).trans (Formalism.HermitianLatticesTheory.genusCovol_locS_idem _ _)
  unfold VecSplit.adjoin
  apply key
  · refine le_trans ?_ (Formalism.HermitianLatticesTheory.genusCovol_le_locS _ _)
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rcases j with u | i
    · rw [consBasis_inl]
      exact Submodule.mem_sup_left (Submodule.subset_span (Set.mem_singleton _))
    · rw [consBasis_inr]
      exact Submodule.mem_sup_right ⟨b' i, hbT i, rfl⟩
  · apply sup_le
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      apply Formalism.HermitianLatticesTheory.genusCovol_le_locS
      rw [← consBasis_inl S b' ()]
      exact Submodule.subset_span ⟨Sum.inl (), rfl⟩
    · rintro _ ⟨t, ht, rfl⟩
      have ht' : t ∈ locF 𝔭 (spanO b') := by
        rw [hb']
        exact Formalism.HermitianLatticesTheory.genusCovol_le_locS _ _ ht
      obtain ⟨s, hs, hst⟩ := (Formalism.HermitianLatticesTheory.genusCovol_mem_locS _ _ _).1 ht'
      have hmap : ∀ y ∈ spanO b', S.ι y ∈ spanO (consBasis S b') := by
        intro y hy
        refine Submodule.span_induction (p := fun y _ => S.ι y ∈ spanO (consBasis S b'))
          ?_ ?_ ?_ ?_ hy
        · rintro _ ⟨i, rfl⟩
          rw [← consBasis_inr S b' i]
          exact Submodule.subset_span ⟨Sum.inr i, rfl⟩
        · simp
        · intro x y _ _ hx hy
          rw [map_add]
          exact Submodule.add_mem _ hx hy
        · intro a x _ hx
          have e : S.ι (a • x) = a • S.ι x := (S.ι.restrictScalars (𝓞 K)).map_smul a x
          rw [e]
          exact Submodule.smul_mem _ a hx
      refine (Formalism.HermitianLatticesTheory.genusCovol_mem_locS _ _ _).2 ⟨s, hs, ?_⟩
      have e : S.ι (s • t) = s • S.ι t := (S.ι.restrictScalars (𝓞 K)).map_smul s t
      have := hmap _ hst
      rw [e] at this
      exact this

theorem akCount_split (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') (h1 : h S.x₀ S.x₀ = 1) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hx : S.x₀ ∈ L)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 ≤ 1) {k : ℕ} (hk : 1 ≤ k) :
    akCount h L 𝔭 k = nkCount h L 𝔭 k 1 * akCount h' (S.cut L) 𝔭 k := by
  classical
  haveI : 𝔭.IsPrime := h𝔭.isPrime
  haveI : Fact (IsFixF K F) := ⟨hF⟩

  obtain ⟨π, hπ⟩ : ∃ π : V →ₗ[K] V', ∀ v, π v = ((prodEquiv S).symm v).2 :=
    ⟨(LinearMap.snd K K V') ∘ₗ (prodEquiv S).symm.toLinearMap, fun v => rfl⟩
  have hdec : ∀ v : V, v = h S.x₀ v • S.x₀ + S.ι (π v) := by
    intro v
    obtain ⟨c, a, hv⟩ : ∃ c a, (prodEquiv S).symm v = (c, a) := ⟨_, _, rfl⟩
    have hv' : v = c • S.x₀ + S.ι a := by
      rw [← prodEquiv_apply, ← hv, LinearEquiv.apply_symm_apply]
    have hc : h S.x₀ v = c := by
      rw [hv', map_add, map_smul, h1, S.orth]
      simp
    have ha : π v = a := by rw [hπ, hv]
    rw [hc, ha]
    exact hv'
  have hπι : ∀ a, π (S.ι a) = a := by
    intro a
    have e := hdec (S.ι a)
    rw [S.orth, zero_smul, zero_add] at e
    exact (S.inj e).symm
  have hcutEq : S.cut L = L.map (π.restrictScalars (𝓞 K)) := by
    ext a
    constructor
    · intro ha
      exact ⟨S.ι a, ha, hπι a⟩
    · rintro ⟨v, hv, rfl⟩
      show S.ι (π v) ∈ L
      obtain ⟨c, hc⟩ := Submodule.mem_one.1 (hLi _ hx _ hv)
      have e : S.ι (π v) = v - h S.x₀ v • S.x₀ := by
        rw [eq_sub_iff_add_eq, add_comm]
        exact (hdec v).symm
      rw [e, ← hc, algebraMap_smul]
      exact L.sub_mem hv (L.smul_mem c hx)
  have hcutL : Submodule.IsLattice K (S.cut L) := by
    rw [hcutEq]
    refine ⟨hL.fg.map _, ?_⟩
    rw [Submodule.map_coe]
    change Submodule.span K (π '' (L : Set V)) = ⊤
    rw [Submodule.span_image, hL.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
    exact fun a => ⟨S.ι a, hπι a⟩

  obtain ⟨b', hb'L, hb'⟩ := Formalism.HermitianLattices.Ext.L3.LocalSpans.exists_basis_locF hcutL h𝔭
  have hm : ∀ i, S.ι (b' i) ∈ L := hb'L
  have hH'ex : ∀ i j, ∃ z : 𝓞 K, algebraMap (𝓞 K) K z = h' (b' i) (b' j) := by
    intro i j
    have e := hLi _ (hm i) _ (hm j)
    rw [S.isom] at e
    exact Submodule.mem_one.1 e
  obtain ⟨H', hH'⟩ : ∃ H' : Matrix (Fin (finrank K V')) (Fin (finrank K V')) (𝓞 K),
      ∀ i j, algebraMap (𝓞 K) K (H' i j) = h' (b' i) (b' j) :=
    ⟨Matrix.of fun i j => (hH'ex i j).choose, fun i j => (hH'ex i j).choose_spec⟩
  set bb := consBasis S b' with hbbdef
  have hbb : locF 𝔭 (spanO bb) = locF 𝔭 L :=
    (locF_span_consBasis S b' hb'L h𝔭 hb').trans
      (Formalism.HermitianLattices.Ext.L3.PinC.locF_eq_locF_adjoin_cut hK hF S h1 hLi h𝔭
        (Formalism.HermitianLattices.Ext.L3.LocF.le_locF 𝔭 L hx)).symm
  have hbbL : ∀ p, bb p ∈ L := by
    rintro (u | i)
    · rw [hbbdef, consBasis_inl]; exact hx
    · rw [hbbdef, consBasis_inr]; exact hm i
  have hHH : ∀ p q, algebraMap (𝓞 K) K (Formalism.HermitianLattices.Ext.L3.PinE.HH H' p q) = h (bb p) (bb q) := by
    rintro (u | i) (u' | j)
    · rw [hbbdef]
      simp only [consBasis_inl]
      rw [h1]
      simp [Formalism.HermitianLattices.Ext.L3.PinE.HH]
    · rw [hbbdef]
      simp only [consBasis_inl, consBasis_inr]
      rw [S.orth]
      simp [Formalism.HermitianLattices.Ext.L3.PinE.HH]
    · rw [hbbdef]
      simp only [consBasis_inl, consBasis_inr]
      have e : starRingEnd K (h S.x₀ (S.ι (b' i))) = h (S.ι (b' i)) S.x₀ := by
        first
          | exact hs S.x₀ (S.ι (b' i))
          | exact hs.eq S.x₀ (S.ι (b' i))
      rw [← e, S.orth]
      simp [Formalism.HermitianLattices.Ext.L3.PinE.HH]
    · rw [hbbdef]
      simp only [consBasis_inr]
      rw [S.isom]
      simp [Formalism.HermitianLattices.Ext.L3.PinE.HH, hH']
  have hmapHH : (Formalism.HermitianLattices.Ext.L3.PinE.HH H').map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) =
      Formalism.HermitianLattices.Ext.L3.PinE.HH (H'.map (Ideal.Quotient.mk (extP K 𝔭 ^ k))) := by
    ext p q
    rcases p with u | i <;> rcases q with u' | j <;>
      simp [Formalism.HermitianLattices.Ext.L3.PinE.HH, Matrix.one_apply]

  have htr : ∀ x : Unit ⊕ Fin (finrank K V') → 𝓞 K ⧸ extP K 𝔭 ^ k,
      star x ⬝ᵥ (Formalism.HermitianLattices.Ext.L3.PinE.HH (H'.map (Ideal.Quotient.mk (extP K 𝔭 ^ k))) *ᵥ x) = 1 →
      ∃ G G' : Matrix (Unit ⊕ Fin (finrank K V')) (Unit ⊕ Fin (finrank K V')) (𝓞 K ⧸ extP K 𝔭 ^ k),
        Gᴴ * Formalism.HermitianLattices.Ext.L3.PinE.HH (H'.map (Ideal.Quotient.mk (extP K 𝔭 ^ k))) * G =
          Formalism.HermitianLattices.Ext.L3.PinE.HH (H'.map (Ideal.Quotient.mk (extP K 𝔭 ^ k))) ∧
        G * G' = 1 ∧ G *ᵥ Formalism.HermitianLattices.Ext.L3.PinE.e₀ = x := by
    intro x hx1
    obtain ⟨c, hc⟩ : ∃ c : Unit ⊕ Fin (finrank K V') → 𝓞 K,
        ∀ p, Ideal.Quotient.mk (extP K 𝔭 ^ k) (c p) = x p :=
      ⟨fun p => (Ideal.Quotient.mk_surjective (x p)).choose,
        fun p => (Ideal.Quotient.mk_surjective (x p)).choose_spec⟩
    set w : ↥(locF 𝔭 (spanO bb)) := ∑ p, c p • Formalism.HermitianLattices.Ext.L3.PinG.bM bb 𝔭 p with hwdef
    have hred : Formalism.HermitianLattices.Ext.L3.PinG.red bb h𝔭 k w = x := by
      funext q
      simp [hwdef, map_sum, map_smul, Formalism.HermitianLattices.Ext.L3.PinG.red_bM, Pi.single_apply, hc,
        Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
      rcases q with ⟨⟩ | i <;> simp
    have hwL : (w : V) ∈ L := by
      rw [hwdef, Submodule.coe_sum]
      exact Submodule.sum_mem _ (fun p _ => by
        rw [Submodule.coe_smul]
        exact Submodule.smul_mem _ _ (hbbL p))
    obtain ⟨z, hz⟩ := Submodule.mem_one.1 (hLi _ hwL _ hwL)
    have hform := Formalism.HermitianLattices.Ext.L3.PinG.red_form h bb hHH h𝔭 k w w hz.symm
    rw [hred, hmapHH, hx1] at hform
    have hcong : CongrP 𝔭 k (h (w : V) (w : V)) 1 := by
      have e := (Formalism.HermitianLattices.Ext.L3.integralBasisSpans.congrP_int h𝔭 k z 1).2 (by rw [map_one]; exact hform.symm)
      rwa [map_one, hz] at e
    obtain ⟨z', hz'L, hz'1, hz'd⟩ :=
      Formalism.HermitianLattices.Ext.L3.PinF.exists_exact_lift hK hF hs hd hL hLi h𝔭 h1 hk hwL hcong
    obtain ⟨g, hg, hgx⟩ :=
      Formalism.HermitianLattices.Ext.L3.PinC.exists_aut_map hK hF hs hd S h1 hL hLi hx h𝔭 hv hz'L hz'1
    rw [← hbb] at hg
    obtain ⟨G, G', hGf, hGG, hGred⟩ := Formalism.HermitianLattices.Ext.L3.PinG.exists_matrix h bb hHH h𝔭 k hg
    refine ⟨G, G', by rw [← hmapHH]; exact hGf, hGG, ?_⟩
    have hz'm : z' ∈ locF 𝔭 (spanO bb) := by rw [hbb]; exact hz'L
    have e1 := hGred (Formalism.HermitianLattices.Ext.L3.PinG.bM bb 𝔭 (Sum.inl ())) ⟨z', hz'm⟩ (by
      show z' = g (bb (Sum.inl ()))
      rw [hbbdef, consBasis_inl, hgx])
    rw [Formalism.HermitianLattices.Ext.L3.PinG.red_bM] at e1
    have e2 : Formalism.HermitianLattices.Ext.L3.PinG.red bb h𝔭 k ⟨z', hz'm⟩ = Formalism.HermitianLattices.Ext.L3.PinG.red bb h𝔭 k w :=
      Formalism.HermitianLattices.Ext.L3.PinG.red_eq_of_sub_mem bb h𝔭 k _ _ (by
        have e := hz'd
        rw [← hbb] at e
        exact e)
    rw [← hred, ← e2, e1]
    rfl
  haveI : Finite (𝓞 K ⧸ extP K 𝔭 ^ k) := Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds.finite_quot (K := K) h𝔭 k
  rw [Formalism.HermitianLattices.Ext.L3.integralBasisSpans.akCount_eq h h𝔭 bb hbb hHH k, hmapHH,
    Formalism.HermitianLattices.Ext.L3.PinE.card_split _ htr,
    Formalism.HermitianLattices.Ext.L3.integralBasisSpans.nkCount_eq h h𝔭 bb hbb hHH k 1, hmapHH,
    Formalism.HermitianLattices.Ext.L3.integralBasisSpans.akCount_eq h' h𝔭 b' hb' hH' k]
  simp

end Formalism.HermitianLattices.Ext.L3.PinB
