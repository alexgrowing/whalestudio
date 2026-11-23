import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPreFamilyOfLatticeFamilyTwo
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualRevDualRev
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Num.HodgeModel
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

namespace GlobalTheory.CompanionTheory.Ar.TwoLevelLat

noncomputable section

section Forms

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem weight_blockWeight_apply (d : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight ι) d k = ∑ i, d ⟨k, i⟩ := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight,
    Pi.single_apply]
  rw [Fintype.sum_sigma]
  simp

theorem isMultiHomog_blocks {f : MvPolynomial (Σ k, ι k) ℤ} {b : K → ℕ}
    (h : GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog f b) : IsMultiHomog f b := by
  intro m hm k
  rw [← weight_blockWeight_apply, h (mem_support_iff.mp hm)]

theorem mConeMap_form (y : (Σ k, ι k) → Ω) {h : MRing ι} {d : K → ℕ} (hh : IsMultiHomog h d) :
    mConeMap y h = MvPolynomial.C (aeval y h) * ∏ k, (X k : MvPolynomial K Ω) ^ d k := by
  classical
  unfold mConeMap
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hX : ∏ p : Σ k, ι k, (X p.1 : MvPolynomial K Ω) ^ m p = ∏ k, X k ^ d k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    change ∏ i, (X k : MvPolynomial K Ω) ^ m ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hh m hm k]
  simp only [mul_pow, Finset.prod_mul_distrib, hX, map_mul, map_prod, map_pow, eq_intCast, map_intCast]
  simp [mul_assoc]

theorem aeval_ne_zero_of_notMem (y : (Σ k, ι k) → Ω) {f : MvPolynomial (Σ k, ι k) ℤ} {b : K → ℕ}
    (hf : GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog f b) (hP : f ∉ mCoordIdeal y) : aeval y f ≠ 0 := by
  intro h0
  apply hP
  show f ∈ RingHom.ker (mConeMap y)
  rw [RingHom.mem_ker, mConeMap_form y (isMultiHomog_blocks hf), h0]
  simp

end Forms

section Lines

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E]

theorem inv_mem_span_inv {R : Subring Ω} {a b : Ω} (hb : b ≠ 0)
    (h : Submodule.span R {a} = Submodule.span R {b}) : a⁻¹ ∈ Submodule.span R {b⁻¹} := by
  have hb' : b ∈ Submodule.span R {a} := by rw [h]; exact Submodule.mem_span_singleton_self b
  obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.mp hb'
  refine Submodule.mem_span_singleton.mpr ⟨u, ?_⟩
  rw [Subring.smul_def, smul_eq_mul] at hu ⊢
  have hu0 : (u : Ω) ≠ 0 := by
    rintro h0
    rw [h0, zero_mul] at hu
    exact hb hu.symm
  rw [← hu, mul_inv, ← mul_assoc, mul_inv_cancel₀ hu0, one_mul]

theorem span_inv_eq {R : Subring Ω} {a b : Ω} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : Submodule.span R {a} = Submodule.span R {b}) :
    Submodule.span R {a⁻¹} = Submodule.span R {b⁻¹} :=
  le_antisymm ((Submodule.span_singleton_le_iff_mem _ _).mpr (inv_mem_span_inv hb h))
    ((Submodule.span_singleton_le_iff_mem _ _).mpr (inv_mem_span_inv ha h.symm))

theorem isFlagVBOn_congr {L L' : Lat ξ E} {T T' : Set (Cpt ξ)} (hT : T ⊆ T') (h : ∀ q ∈ T, L q = L' q)
    {r : ℕ} (b : Fin r → E) (hL : L.IsFlagVBOn T' b) : L'.IsFlagVBOn T b := by
  intro p hp
  obtain ⟨U, hpU, b', hb', hfr⟩ := hL p (hT hp)
  refine ⟨U, hpU, b', hb', fun q hq hqU => ?_⟩
  obtain ⟨hli, hsp⟩ := hfr q (hT hq) hqU
  exact ⟨hli, (h q hq).symm.trans hsp⟩

theorem gr_congr {L L' : Lat ξ E} {q : Cpt ξ} (h : L q = L' q) {r : ℕ} (b : Fin r → E) (i : Fin r) :
    L.gr b i q = L'.gr b i q := by
  unfold Lat.gr
  rw [h]

theorem tens_one_le (Λ : Lat ξ Ω) (q : Cpt ξ) :
    Lat.tens (fun _ : Unit => Λ) (fun _ => (1 : ℤ)) q ≤ Λ q := by
  refine Submodule.span_le.mpr ?_
  rintro t ⟨s, hs, rfl⟩
  have h1 : Λ q = Submodule.span (regAt ξ q) {s ()} := (hs ()).2
  have hp : ∏ i : Unit, s i ^ (fun _ : Unit => (1 : ℤ)) i = s () := by simp
  rw [SetLike.mem_coe, hp]
  exact h1.symm.le (Submodule.mem_span_singleton_self _)

theorem tens_one_eq (Λ : Lat ξ Ω) (q : Cpt ξ) {g : Ω} (hg : g ≠ 0)
    (h : Lat.tens (fun _ : Unit => Λ) (fun _ => (1 : ℤ)) q = Submodule.span (regAt ξ q) {g}) :
    Λ q = Submodule.span (regAt ξ q) {g} := by
  rw [← h]
  refine le_antisymm ?_ (tens_one_le Λ q)
  by_cases hex : ∃ t, Λ.IsGenAt q t
  · obtain ⟨t, ht⟩ := hex
    rw [ht.2, Submodule.span_singleton_le_iff_mem]
    refine Submodule.subset_span ?_
    exact ⟨fun _ => t, fun _ => ht, by simp⟩
  · exfalso
    have hle : Lat.tens (fun _ : Unit => Λ) (fun _ => (1 : ℤ)) q ≤ ⊥ := by
      refine Submodule.span_le.mpr ?_
      rintro t ⟨s, hs, rfl⟩
      exact absurd ⟨s (), hs ()⟩ hex
    have hmem : g ∈ Lat.tens (fun _ : Unit => Λ) (fun _ => (1 : ℤ)) q := by
      rw [h]; exact Submodule.mem_span_singleton_self g
    exact hg ((Submodule.mem_bot _).mp (hle hmem))

theorem tens_neg_one_eq (Λ : Lat ξ Ω) (q : Cpt ξ) {g : Ω} (hg : g ≠ 0)
    (h : Lat.tens (fun _ : Unit => Λ) (fun _ => (-1 : ℤ)) q = Submodule.span (regAt ξ q) {g}) :
    Λ q = Submodule.span (regAt ξ q) {g⁻¹} := by
  by_cases hex : ∃ t, Λ.IsGenAt q t
  · obtain ⟨t, ht⟩ := hex
    have hT : Lat.tens (fun _ : Unit => Λ) (fun _ => (-1 : ℤ)) q = Submodule.span (regAt ξ q) {t⁻¹} := by
      refine le_antisymm (Submodule.span_le.mpr ?_) ?_
      · rintro u ⟨s, hs, rfl⟩
        have hp : ∏ i : Unit, s i ^ (fun _ : Unit => (-1 : ℤ)) i = (s ())⁻¹ := by simp
        rw [SetLike.mem_coe, hp]
        exact inv_mem_span_inv ht.1 ((hs ()).2.symm.trans ht.2)
      · rw [Submodule.span_singleton_le_iff_mem]
        refine Submodule.subset_span ?_
        exact ⟨fun _ => t, fun _ => ht, by simp⟩
    rw [ht.2]
    rw [hT] at h
    simpa using span_inv_eq (inv_ne_zero ht.1) hg h
  · exfalso
    have hle : Lat.tens (fun _ : Unit => Λ) (fun _ => (-1 : ℤ)) q ≤ ⊥ := by
      refine Submodule.span_le.mpr ?_
      rintro t ⟨s, hs, rfl⟩
      exact absurd ⟨s (), hs ()⟩ hex
    have hmem : g ∈ Lat.tens (fun _ : Unit => Λ) (fun _ => (-1 : ℤ)) q := by
      rw [h]; exact Submodule.mem_span_singleton_self g
    exact hg ((Submodule.mem_bot _).mp (hle hmem))

variable {K : Type} [Fintype K] {J : K → Type}

theorem chart_ne_zero {y : (Σ k, J k) → Ω} {c : ∀ k, J k} {q : Cpt ξ}
    (hc : InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c q) (a : K → ℤ) :
    (∏ k, y ⟨k, c k⟩ ^ a k) ≠ 0 := by
  have h0 : ∏ k, y ⟨k, c k⟩ ≠ 0 := hc.1
  rw [Finset.prod_ne_zero_iff] at h0 ⊢
  exact fun k hk => zpow_ne_zero _ (h0 k hk)

theorem isDegOn_of_tens_one {Λ Λ' : Lat ξ Ω} {T : Set (Cpt ξ)} (hΛ : ∀ q ∈ T, Λ' q = Λ q)
    {y : (Σ k, J k) → Ω} {a : K → ℤ} {e : Ω}
    (h : (Lat.tens (fun _ : Unit => Λ) fun _ => (1 : ℤ)).IsDegOn Set.univ y a e) : Λ'.IsDegOn T y a e :=
  ⟨h.1, fun q hq c hc =>
    (hΛ q hq).trans (tens_one_eq Λ q (smul_ne_zero (chart_ne_zero hc a) h.1) (h.2 q trivial c hc))⟩

theorem isDegOn_of_tens_neg_one {Λ Λ' : Lat ξ Ω} {T : Set (Cpt ξ)} (hΛ : ∀ q ∈ T, Λ' q = Λ q)
    {y : (Σ k, J k) → Ω} {a : K → ℤ} {e : Ω}
    (h : (Lat.tens (fun _ : Unit => Λ) fun _ => (-1 : ℤ)).IsDegOn Set.univ y a e) :
    Λ'.IsDegOn T y (-a) e⁻¹ :=
  ⟨inv_ne_zero h.1, fun q hq c hc => by
    rw [hΛ q hq, tens_neg_one_eq Λ q (smul_ne_zero (chart_ne_zero hc a) h.1) (h.2 q trivial c hc)]
    have hx : ((∏ k, y ⟨k, c k⟩ ^ a k) • e)⁻¹ = (∏ k, y ⟨k, c k⟩ ^ (-a) k) • e⁻¹ := by
      simp only [smul_eq_mul, Pi.neg_apply, zpow_neg, mul_inv, Finset.prod_inv_distrib]
    rw [hx]⟩

end Lines

end

end GlobalTheory.CompanionTheory.Ar.TwoLevelLat

namespace GlobalTheory.CompanionTheory.Ar.TwoLevelLat

theorem latFlagPair_of_twoLevels : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β)
    (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)]
    (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) [Fintype (CMType H)] [DecidableEq (CMType H)] (Fl : 𝔐.Flag)
    (S₀ : Finset ℕ) (T : LocPair J ℤ (CMType H × Fin (D.p + D.q))), Fl.TwoLevels S₀ T → ∀ p ∈ S, p ∉ S₀ →
    (∀ (s : CMType H ⊕ CMType H) (q : Cpt 𝔐.ξ), (∀ p' : ℕ, p'.Prime → ¬ InFibre 𝔐.ξ p' q) → 𝔐.HT p s q = 𝔐.dR s q) →
    ∀ s, IsLatFlagPair y (overPrime 𝔐.ξ p) (𝔐.dR s) (𝔐.HT p s) (Fl.b s) (labelPair D T s) := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 _ _ Fl S₀ T hTL p hpS hpS₀ hagree s
  obtain ⟨h, hvb, hsub, e₀, e, hR₀, hR, hfg, hvo⟩ := hTL
  have hVAt : ∀ q ∈ overPrime 𝔐.ξ p, ∀ s, 𝔐.VAt S₀ s q = 𝔐.dR s q := by
    intro q hq s
    have hq' : ∀ p' : ℕ, p'.Prime → p' ≠ p → ¬ InFibre 𝔐.ξ p' q := hq
    exact Lat.patch_of_not S₀ _ _ fun p' hp' hf =>
      hq' p' (𝔐.S_prime p' (h hp')) (fun he => hpS₀ (he ▸ hp')) hf
  have hV : ∀ q ∈ overPrime 𝔐.ξ p, ∀ s, 𝔐.V s q = 𝔐.HT p s q := by
    intro q hq s
    have hq' : ∀ p' : ℕ, p'.Prime → p' ≠ p → ¬ InFibre 𝔐.ξ p' q := hq
    by_cases hf : InFibre 𝔐.ξ p q
    · exact Lat.patch_of_unique S _ _ hpS hf fun p' hp' h' => by
        by_contra hne
        exact hq' p' (𝔐.S_prime p' hp') hne h'
    · have hnone : ∀ p' : ℕ, p'.Prime → ¬ InFibre 𝔐.ξ p' q := fun p' hp' h' => by
        by_cases hpp : p' = p
        · exact hf (hpp ▸ h')
        · exact hq' p' hp' hpp h'
      have h1 : 𝔐.V s q = 𝔐.dR s q :=
        Lat.patch_of_not S _ _ fun p' hp' => hnone p' (𝔐.S_prime p' hp')
      exact h1.trans (hagree s q hnone).symm
  have hR₀' : ∀ r, (Lat.tens (fun _ : Unit => (𝔐.VAt S₀ (HodgeCpt.rootIdx D r).1).gr
      (Fl.b (HodgeCpt.rootIdx D r).1) (HodgeCpt.rootIdx D r).2)
      fun _ => HodgeCpt.rootSgn D r).IsDegOn Set.univ y (T.x r) (e₀ r) := hR₀
  have hR' : ∀ r, (Lat.tens (fun _ : Unit => (𝔐.V (HodgeCpt.rootIdx D r).1).gr
      (Fl.b (HodgeCpt.rootIdx D r).1) (HodgeCpt.rootIdx D r).2)
      fun _ => HodgeCpt.rootSgn D r).IsDegOn Set.univ y (T.x' r) (e r) := hR
  rcases s with τ | τ
  · refine ⟨isFlagVBOn_congr (Set.subset_univ _) (fun q hq => hVAt q hq _) _ (hsub _),
      isFlagVBOn_congr (Set.subset_univ _) (fun q hq => hV q hq _) _ (Fl.sub _), fun i => ?_⟩
    have hlt : ((Fin.castAdd D.q i : Fin (D.p + D.q)) : ℕ) < D.p := i.isLt
    have hidx : HodgeCpt.rootIdx D (τ, Fin.castAdd D.q i) = ⟨.inl τ, i⟩ := by
      unfold HodgeCpt.rootIdx
      rw [dif_pos hlt]
      exact Sigma.ext rfl (heq_of_eq (Fin.ext rfl))
    have hsgn : HodgeCpt.rootSgn D (τ, Fin.castAdd D.q i) = 1 := by
      unfold HodgeCpt.rootSgn
      rw [if_pos hlt]
    have h0 := hR₀' (τ, Fin.castAdd D.q i)
    have h1 := hR' (τ, Fin.castAdd D.q i)
    rw [hidx, hsgn] at h0 h1
    obtain ⟨⟨bf, bg, hbf, hbg, hd⟩, -, hgP, -⟩ := hvo (τ, Fin.castAdd D.q i)
    exact ⟨e₀ (τ, Fin.castAdd D.q i), e (τ, Fin.castAdd D.q i),
      isDegOn_of_tens_one (fun q hq => gr_congr (hVAt q hq _).symm _ _) h0,
      isDegOn_of_tens_one (fun q hq => gr_congr (hV q hq _).symm _ _) h1, ⟨bf, bg, hbf, hbg, hd⟩,
      aeval_ne_zero_of_notMem y hbg hgP, hfg _⟩
  · refine ⟨isFlagVBOn_congr (Set.subset_univ _) (fun q hq => hVAt q hq _) _ (hsub _),
      isFlagVBOn_congr (Set.subset_univ _) (fun q hq => hV q hq _) _ (Fl.sub _), fun j => ?_⟩
    have hj : (j : ℕ) < D.q := j.isLt
    have hidx : HodgeCpt.rootIdx D (τ, Fin.natAdd D.p j.rev) = ⟨.inr τ, j⟩ := by
      unfold HodgeCpt.rootIdx
      rw [dif_neg (by simp)]
      refine Sigma.ext rfl (heq_of_eq (Fin.ext ?_))
      have e1 : ((Fin.natAdd D.p j.rev : Fin (D.p + D.q)) : ℕ) = D.p + ((j.rev : Fin (labelRk D (.inr τ))) : ℕ) := rfl
      have e2 : ((j.rev : Fin (labelRk D (.inr τ))) : ℕ) = labelRk D (.inr τ) - ((j : ℕ) + 1) := Fin.val_rev j
      have e3 : labelRk D (.inr τ) = D.q := rfl
      simp only at e1 e2 ⊢
      omega
    have hsgn : HodgeCpt.rootSgn D (τ, Fin.natAdd D.p j.rev) = -1 := by simp [HodgeCpt.rootSgn]
    have h0 := hR₀' (τ, Fin.natAdd D.p j.rev)
    have h1 := hR' (τ, Fin.natAdd D.p j.rev)
    rw [hidx, hsgn] at h0 h1
    obtain ⟨⟨bf, bg, hbf, hbg, hd⟩, hfP, -, -⟩ := hvo (τ, Fin.natAdd D.p j.rev)
    have he₀ : e₀ (τ, Fin.natAdd D.p j.rev) ≠ 0 := h0.1
    have he : e (τ, Fin.natAdd D.p j.rev) ≠ 0 := h1.1
    refine ⟨(e₀ (τ, Fin.natAdd D.p j.rev))⁻¹, (e (τ, Fin.natAdd D.p j.rev))⁻¹,
      isDegOn_of_tens_neg_one (fun q hq => gr_congr (hVAt q hq _).symm _ _) h0,
      isDegOn_of_tens_neg_one (fun q hq => gr_congr (hV q hq _).symm _ _) h1,
      ⟨bg, bf, hbg, hbf, ?_⟩, aeval_ne_zero_of_notMem y hbf hfP, ?_⟩
    · change (fun k => ((bg k : ℕ) : ℤ) - bf k) =
        -(T.x (τ, Fin.natAdd D.p j.rev)) - -(T.x' (τ, Fin.natAdd D.p j.rev))
      funext k
      have hk := congrFun hd k
      simp only [Pi.sub_apply, Pi.neg_apply] at hk ⊢
      linarith
    · change aeval y (T.g (τ, Fin.natAdd D.p j.rev)) =
        (e (τ, Fin.natAdd D.p j.rev))⁻¹ / (e₀ (τ, Fin.natAdd D.p j.rev))⁻¹ *
          aeval y (T.f (τ, Fin.natAdd D.p j.rev))
      rw [hfg]
      field_simp

end GlobalTheory.CompanionTheory.Ar.TwoLevelLat
