import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.IntegralRingEmbedding
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.ClosedPointWeilPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullbackValuationInvarianceOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj IsLocalRing NumberField

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.H1

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor

private theorem oneC_of_lemma {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (k : ℕ) (ζ : F) (s : Fam D F k) : Fam.IsSmul D F ζ s (ζ • s) := by
  intro α j
  rfl

private theorem oneC_of_lemma_2 {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (k : ℕ) (p : QkPt D F k) :
    ∃ w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k)), w.IsGen :=
  ClosedPointWeilPower.gen_local_linComb (V := F) D.P.L D.P.isLB _ _

private theorem oneC_of_lemma_3 (F : Type) [Field F] (c : (Γ(Sp F, ⊤))ˣ) : ∃ z : Fˣ, unitOn z = c :=
  ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom.toMonoidHom c, by
    ext
    simp [unitOn]⟩

private theorem oneC_of_lemma_4 {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (k : ℕ) (s s' : Fam D F k)
    (h : ∀ α j, (s.s α).f j = (s'.s α).f j) : s = s' := by
  obtain ⟨s, hs⟩ := s
  obtain ⟨s', hs'⟩ := s'
  have key : ∀ α, s α = s' α := by
    intro α
    have hab : (s α).f = (s' α).f := funext (h α)
    revert hab
    generalize s α = a
    generalize s' α = b
    cases a
    cases b
    intro hab
    cases hab
    rfl
  have e : s = s' := funext key
  subst e
  rfl

private theorem oneC_of_lemma_5 {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (k : ℕ) (ζ : F) (s s' : Fam D F k) (h : Fam.IsSmul D F ζ s s') :
    s' = ζ • s :=
  oneC_of_lemma_4 D F k s' (ζ • s) fun α j => (h α j).trans (oneC_of_lemma D F k ζ s α j).symm

private theorem oneC_of_lemma_6 (F : Type) [Field F] (z : Fˣ) (n : ℕ) (h : unitOn z ^ n = 1) :
    (z : F) ^ n = 1 := by
  have key : ∀ u : Fˣ,
      Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom.toMonoidHom (unitOn u) = u := by
    intro u
    ext
    simp [unitOn]
  have e := congrArg (Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom.toMonoidHom) h
  rw [map_pow, key, map_one] at e
  simpa using congrArg Units.val e

theorem oneC_of (hL : Laws) (hΦ : PhiFunStatement) (h1c : PositiveValuationMaximalIdeal) (h2 : PullbackValuationForwardBound)
    (h2f : DvrLevelFrame) (h3 : FiniteOrderValuationInvariance) (hU : UUStatement) (hE : FinOrdExistsStatement) (hB : AlphaBarEnumStatement)
    (hC : CanonLiftFixStatement) (hD : AlphaPairStatement) (hdim : DimSplitStatement) :
    OneCStatement := by
  intro E _ _ _ H V _ _ _ t P hT α N hN hαN hcop hNu ϖ hϖ Q hQ F _ _ _ v hv Dw I θ hθ hprim θα hpull s hs
  letI := H.starRing
  have hk : 1 ≤ 1 * N := by omega
  have hαN' : star α * α = (N : 𝓞 E) := by rw [_root_.mul_comm]; exact hαN

  have htor : ∀ (a b : 𝓞 E) (y : TFK (R := V) F ⟶ P.A.A), a * b = (N : 𝓞 E) →
      y ≫ P.oA.act b = 1 → y ^ (1 * N) = 1 := by
    intro a b y hab hy
    rw [_root_.one_mul, ← ClosedPointWeilPower.comp_act_nat P.oA.toRingAct y N hN, ← hab, P.oA.map_mul,
      ← Category.assoc, hy]
    exact ClosedPointWeilPower.one_comp_hom _ (P.oA.hom a)

  obtain ⟨p, x, hpx, hxα, hinj, -⟩ := hB E H V t P hT α N hN hαN hcop hNu F Dw I
  have hcop' : ∃ u u' : 𝓞 E, u * star α + u' * star (star α) = 1 := by
    obtain ⟨u, u', h⟩ := hcop
    exact ⟨u', u, by rw [star_star, _root_.add_comm]; exact h⟩
  obtain ⟨p', x', hpx', hxα', -, hsurj'⟩ :=
    hB E H V t P hT (star α) N hN (by rw [star_star]; exact hαN') hcop' hNu F Dw I
  have hxa : ∀ gm, x' gm ≫ P.oA.act α = 1 := fun gm => by simpa only [star_star] using hxα' gm
  obtain ⟨f, hfToA, -, -, -, -, hfW⟩ := hT F (1 * N) hk
  have hfp : ∀ i, x i = f (p i) := fun i => (hfToA (p i) (x i)).mp (hpx i)
  have hfq : ∀ gm, x' gm = f (p' gm) := fun gm => (hfToA (p' gm) (x' gm)).mp (hpx' gm)
  have htx : ∀ i, x i ^ (1 * N) = 1 := fun i => htor α (star α) (x i) hαN (hxα i)
  have htx' : ∀ gm, x' gm ^ (1 * N) = 1 := fun gm => htor (star α) α (x' gm) hαN' (hxa gm)

  have hw : ∀ b, ∃ w : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F (p b).g.b)
      (DegPre.lineε (1 * N))), w.IsGen := fun b => oneC_of_lemma_2 P.D.toPre F (1 * N) (p b)
  choose w hwg using hw
  have hz : ∀ b, ∃ ζ : F, ζ ≠ 0 ∧ FinOrd P.D F (1 * N) (p b) (w b) ζ :=
    fun b => hE V P.D F (1 * N) hk (p b) (w b) (hwg b)
  choose ζ hζ0 hfin using hz
  choose Φ hΦb using fun b => hΦ V (maximalIdeal V) P.D F (1 * N) hk (p b) (w b) (hwg b)
  choose wq hwqg hwq1 hfix using fun gm =>
    hC E H V t P hT α N hN hαN hcop hNu F θ θα hpull (p' gm) (x' gm) (hpx' gm) (hxa gm)
  choose Φq hΦq using fun gm => hΦ V (maximalIdeal V) P.D F (1 * N) hk (p' gm) (wq gm) (hwqg gm)

  have hWex : ∀ i gm, ∃ z : Fˣ, WeilIs P.A.A P.A.L ((1 * N : ℕ) : ℤ) (x' gm) (x i) (unitOn z) := by
    intro i gm
    obtain ⟨c, hc, -⟩ := (hL.weil _ P.A (1 * N) _).1 (x' gm) (x i) (htx' gm) (htx i)
    obtain ⟨z, rfl⟩ := oneC_of_lemma_3 F c
    exact ⟨z, hc⟩
  choose χz hχz using hWex
  have hEig : ∀ i gm, Φq gm (Φ i θα) = (χz i gm : F) • Φ i θα := by
    intro i gm
    apply oneC_of_lemma_5
    have hW' : WeilQkIs P.D.toPre F (1 * N) (p' gm) (p i) (χz i gm) :=
      (hfW (p' gm) (p i) (χz i gm)).mpr (by rw [← hfq gm, ← hfp i]; exact hχz i gm)
    exact hW' (wq gm) (w i) (hwqg gm) (hwg i) θα (Φ i θα) (Φq gm (Φ i θα)) θα (Φ i θα)
      ((hΦb i θα _).mpr rfl) ((hΦq gm (Φ i θα) _).mpr rfl) (hfix gm) ((hΦb i θα _).mpr rfl)

  have hvN : v (((1 * N : ℕ)) : F) = 0 := by
    have h := hv ((N : ℕ) : FractionRing V) 0 ⟨hNu.unit, by simp⟩
    simpa using h
  have hπ : ∃ π : F, 0 < v π := by
    refine ⟨algebraMap (FractionRing V) F (algebraMap V (FractionRing V) ϖ), ?_⟩
    rw [hv _ 1 ⟨1, by simp⟩]
    exact_mod_cast (show (0 : ℚ) < ((1 : ℤ) : ℚ) by norm_num)

  have hθα0 : NuGe P.D Q F v (1 * N) θα 0 :=
    h2 V ϖ hϖ P.D Q hQ F v hv (𝓞 E) P.oD H.w0 P.w0 α N hN hαN hαN' 1 le_rfl θ θα hpull 0 hθ
  have hsm1 : ∀ {k : ℕ} (u : Fam P.D.toPre F k), Fam.IsSmul P.D.toPre F 1 u u := by
    intro k u
    have h := oneC_of_lemma P.D.toPre F k 1 u
    rwa [one_smul] at h
  have hnotpos : ∀ r : ℚ, 0 < r → ¬ NuGe P.D Q F v (1 * N) θα r := by
    intro r hr h
    obtain ⟨σ, σF, hscal, hσ, hnd⟩ := hprim
    have hb := h2f V ϖ hϖ P.D Q hQ F v hv (𝓞 E) P.oD H.w0 P.w0 α N hN hαN 1 le_rfl θ θα hpull 0
      σ σF 1 hscal (fun j => by rw [← hσ j]; exact hsm1 θ 0 j) hnd r h
    rw [AddValuation.map_one, QForm.Q_zero (hϖ := hϖ) (D := P.D) (Q := Q) (hQ := hQ)] at hb
    have h' : ((r : ℚ) : WithTop ℚ) ≤ ((0 : ℚ) : WithTop ℚ) := by simpa using hb
    have := WithTop.coe_le_coe.mp h'
    linarith
  have hN3 : ∀ i r, NuGe P.D Q F v (1 * N) θα r ↔ NuGe P.D Q F v (1 * N) (ζ i • Φ i θα) r :=
    fun i r => h3 V ϖ hϖ P.D Q hQ F v hv (1 * N) hk (p i) (w i) (hwg i) (ζ i) (hζ0 i) (hfin i)
      θα (Φ i θα) (ζ i • Φ i θα) ((hΦb i θα _).mpr rfl) (oneC_of_lemma _ _ _ _ _) r

  obtain ⟨bb, hbli, -, hbspan⟩ := hU V ϖ hϖ P.D Q hQ F v hv (Or.inl inferInstance) (1 * N) hk
  have hcard : Fintype.card (Fin (N ^ P.A.g)) = (1 * N) ^ (P.D.toPre.rank + P.D.toPre.P.g) := by
    rw [Fintype.card_fin, hdim E H V t P, _root_.one_mul]
  obtain ⟨a, ha0, hsa⟩ := IntegralRingEmbedding.span_of_eigen (F := F) (v := v) (b := bb) (n := _)
    (fun u => NuGe P.D Q F v (1 * N) u 0) (fun u => ∃ r : ℚ, 0 < r ∧ NuGe P.D Q F v (1 * N) u r)
    hbli hbspan
    (fun s0 hs0 ζ0 s' hζ hs' he => (h1c V ϖ hϖ P.D Q hQ F v hv (1 * N) hk s0 hs0).mpr
      ⟨ζ0, s', hζ, hs', by rw [he]; exact oneC_of_lemma _ _ _ ζ0 s'⟩)
    hπ hcard (fun i => ζ i • Φ i θα) (fun i => (hN3 i 0).mp hθα0)
    (fun i hp => by
      obtain ⟨r, hr, hr'⟩ := hp
      exact hnotpos r hr ((hN3 i r).mpr hr'))
    Φq
    (fun gm s0 hs0 => (h3 V ϖ hϖ P.D Q hQ F v hv (1 * N) hk (p' gm) (wq gm) (hwqg gm) 1 one_ne_zero
      (hwq1 gm) s0 (Φq gm s0) (Φq gm s0) ((hΦq gm s0 _).mpr rfl) (hsm1 _) 0).mp hs0)
    hk hvN (fun i gm => (χz i gm : F))
    (fun i gm => oneC_of_lemma_6 F (χz i gm) (1 * N)
      (ClosedPointWeilPower.weil_pow_eq_one hL.weil P.A (1 * N) (x' gm) (x i) (htx' gm) (htx i) _ (hχz i gm)))
    (fun i gm => by
      show Φq gm (ζ i • Φ i θα) = (χz i gm : F) • (ζ i • Φ i θα)
      rw [map_smul, hEig i gm, smul_comm])
    (fun i j hij => by
      obtain ⟨z, hz, c, c', hc, hc', hne⟩ := hD E H V t P hT α N hN hαN hcop hNu F Dw I (x i) (x j)
        (hxα i) (hxα j) (fun h => hij (hinj h))
      obtain ⟨gm, rfl⟩ := hsurj' z (by rw [star_star]; exact hz)
      refine ⟨gm, fun heq => hne ?_⟩
      have hc1 : WeilIs P.A.A P.A.L ((1 * N : ℕ) : ℤ) (x' gm) (x i) c := by rw [_root_.one_mul]; exact hc
      have hc1' : WeilIs P.A.A P.A.L ((1 * N : ℕ) : ℤ) (x' gm) (x j) c' := by
        rw [_root_.one_mul]; exact hc'
      rw [ClosedPointWeilPower.weil_unique hL.weil P.A (1 * N) (x' gm) (x i) (htx' gm) (htx i) _ _ hc1 (hχz i gm),
        ClosedPointWeilPower.weil_unique hL.weil P.A (1 * N) (x' gm) (x j) (htx' gm) (htx j) _ _ hc1' (hχz j gm),
        Units.ext heq])
    s hs
  exact ⟨N ^ P.A.g, p, x, w, ζ, fun i => ζ i • Φ i θα, a, hpx, hxα, fun i => ⟨hwg i, hζ0 i, hfin i⟩,
    fun i => ⟨Φ i θα, (hΦb i θα _).mpr rfl, oneC_of_lemma _ _ _ _ _⟩, ha0, hsa⟩

end ReciprocityTheory.ChartRestriction.G.H1
