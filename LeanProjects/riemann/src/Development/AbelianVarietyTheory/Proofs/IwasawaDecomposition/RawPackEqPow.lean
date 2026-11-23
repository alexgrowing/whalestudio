import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnlocalizedSaturatedState
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HeightCounting.Rigid

theorem exists_frob (hc : GlobalTheory.TwSys.Cheb) (D : D7) (i : D.ntw.Tw) (Q : Finset (PlE D.host)) {p : ℕ} (hp : p ≠ 0)
    (γ : D.ntw.RCG i Q) :
    ∃ w, w ∉ Q ∧ w ∉ placesOver D.host.E p ∧ ∃ (B : ValuationSubring D.nd.Om) (σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om),
      Formalism.ConjugateSelfDual.IsPlaceOver B w ∧ Formalism.ConjugateSelfDual.IsFrob B (Formalism.ConjugateSelfDual.normV w) σ ∧ D.ntw.art i Q σ = γ := by
  classical
  obtain ⟨g, rfl⟩ := D.ntw.art_surj i Q γ
  obtain ⟨w, hwA, -, -, B, hB, -, σ, hσ, hU⟩ := hc D.host.E D.nd.Om (D.ntw.art i Q).ker (D.ntw.art_cont i Q) inferInstance g
    (Q ∪ (placesOver_finite_av D.host.E p hp).toFinset)
  refine ⟨w, fun h => hwA (Finset.mem_union_left _ h),
    fun h => hwA (Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).2 h)), B, σ, hB, hσ, ?_⟩
  rwa [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at hU

theorem pow_of_tied (hc : GlobalTheory.TwSys.Cheb) {D : D7} (cf : CharFrame D) (C : NChoice D) (tp : TupTied D cf C)
    (v : D.what₂.places.Pl) (ψ : D.ntw.RCG (C.twI v) (C.Q v) →* (D.ntw.Ok (C.twI v) (C.k' v))ˣ)
    (ι : TwChar.RootIso D (C.twI v) (C.k' v))
    (hF : TwChar.FrobPick (C.twI v) (C.Q v) (C.k' v) ψ ι (tp.psi v)) (hT : PsiChoiceCompatible D cf C tp)
    (htw : TwistedAt D v) (hk : 1 ≤ C.k' v)
    (hL : ∀ z : ℂ, z ^ D.what₂.places.resChar v ^ C.k' v = 1 → ∃ x : D.what₂.LL, D.what₂.embLL x = z) :
    ∃ a : ℕ, a.Coprime (D.ntw.l (C.twI v)) ∧ C.psi' v = ψ ^ a := by
  haveI : NeZero (D.ntw.l (C.twI v) ^ C.k' v) := ⟨pow_ne_zero _ (D.ntw.lPrime _).out.ne_zero⟩
  have hL' : ∀ z : ℂ, z ^ (D.ntw.l (C.twI v) ^ C.k' v) = 1 → ∃ x : D.what₂.LL, D.what₂.embLL x = z := fun z hz =>
    hL z (by rw [← C.twI_l v]; exact hz)
  let j : D.ntw.Ok (C.twI v) (C.k' v) →+* FractionRing (C.Oe v) :=
    (algebraMap (C.Oe v) (FractionRing (C.Oe v))).comp (algebraMap (D.ntw.Ok (C.twI v) (C.k' v)) (C.Oe v))
  have hj : Function.Injective j := (IsFractionRing.injective (C.Oe v) (FractionRing (C.Oe v))).comp (C.Oe_inj v)
  obtain ⟨a, ha, hax⟩ := TwChar.exists_exponent ι (D.ntw.zk_prim _ _) D.what₂.embLL hL' (C.embW v) j hj
  refine ⟨a, Nat.Coprime.coprime_dvd_right (dvd_pow_self _ (by omega)) ha, MonoidHom.ext fun γ => Units.ext ?_⟩
  have hp : D.what₂.places.resChar v ≠ 0 := by rw [← C.twI_l v]; exact (D.ntw.lPrime _).out.ne_zero
  obtain ⟨w, hwQ, hwl, B, σ, hB, hσ, rfl⟩ := exists_frob hc D (C.twI v) (C.Q v) hp γ
  obtain ⟨u, hu, hχ⟩ := hF w hwQ B hB σ hσ
  obtain ⟨x, hx⟩ := hL' ((ι u : ℂˣ) : ℂ) (by rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 (ι u).2, Units.val_one])
  have h1 := hT v htw w hwQ hwl B σ hB hσ x (by rw [hχ, inv_inv]; exact hx)
  have h2 := hax u x hx
  have h3 := hj (h1.symm.trans h2)
  rw [MonoidHom.pow_apply, ← hu]
  exact h3

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in

theorem transfer {D₁ D₂ : D7} (h : SameExport D₁ D₂) (p : TwPack D₁) (A : Finset (PlE D₁.host))
    (ι : TwChar.RootIso D₁ p.1 p.2.2.1) (χ : HChar D₁.host.E) (hO : BlochKatoReduction.Gen.PsiOk p.1 A p.2.1 p.2.2.1 p.2.2.2)
    (hF : TwChar.FrobPick p.1 p.2.1 p.2.2.1 p.2.2.2 ι χ) (i₂ : D₂.ntw.Tw) (Q₂ : Finset (PlE D₂.host)) (k₂ : ℕ)
    (χ₂ : HChar D₂.host.E) (hi : HEq i₂ p.1) (hQ : HEq Q₂ p.2.1) (hk : k₂ = p.2.2.1) (hχ : HEq χ₂ χ) :
    ∃ (ψ₂ : D₂.ntw.RCG i₂ Q₂ →* (D₂.ntw.Ok i₂ k₂)ˣ) (ι₂ : TwChar.RootIso D₂ i₂ k₂) (A₂ : Finset (PlE D₂.host)),
      BlochKatoReduction.Gen.PsiOk i₂ A₂ Q₂ k₂ ψ₂ ∧ TwChar.FrobPick i₂ Q₂ k₂ ψ₂ ι₂ χ₂ ∧ D₂.ntw.l i₂ = D₁.ntw.l p.1 ∧
      ∀ a : ℤ, HEq (⟨i₂, Q₂, k₂, ψ₂ ^ a⟩ : TwPack D₂) (GlobalTheory.HeightCounting.twPackPow D₁ a p) := by
  obtain ⟨h1, h2, -, -, -⟩ := h
  obtain ⟨i, Q, k, ψ⟩ := p
  dsimp only at hi hQ hk hO hF ι ⊢
  subst hk
  obtain ⟨a1, a2, a3, nOm, ninstOm, nalgOm, nplOm, nPlG⟩ := h1
  obtain ⟨xcc, xTw, xl, fixedFieldTransport_baseIntegerRing_heq, fixedFieldTransport_baseIntegerCommRing_heq, fixedFieldTransport_baseIntegerAlgebra_heq, fixedFieldTransport_baseIntegerTopology_heq, xO, xcrO, xalgO, xOk, xcrOk, xalgOk, xzk, xpD, xchi1, xSig, xfinSig, xjS, xside, xrhoS, fixedFieldTransport_initialPlaceSet_heq, xhEig, xLam, xsideL, xRCG, xgrpRCG, xfinRCG, xart, xth⟩ := h2
  cases D₁; cases D₂
  dsimp only at a1 a2 a3
  subst a1; subst a2; subst a3
  cases ‹NData _ _ _›; cases ‹NData _ _ _›
  dsimp only at nOm ninstOm nalgOm nplOm nPlG
  subst nOm; subst ninstOm; subst nalgOm; subst nplOm; subst nPlG
  cases ‹@NTw _ _ _ _ _ _ _›; cases ‹@NTw _ _ _ _ _ _ _›
  dsimp only at xcc xTw xl fixedFieldTransport_baseIntegerRing_heq fixedFieldTransport_baseIntegerCommRing_heq fixedFieldTransport_baseIntegerAlgebra_heq fixedFieldTransport_baseIntegerTopology_heq xO xcrO xalgO xOk xcrOk xalgOk xzk xpD xchi1 xSig xfinSig xjS xside xrhoS fixedFieldTransport_initialPlaceSet_heq xhEig xLam xsideL xRCG xgrpRCG xfinRCG xart xth
  subst xcc; subst xTw; subst xl; subst fixedFieldTransport_baseIntegerRing_heq; subst fixedFieldTransport_baseIntegerCommRing_heq; subst fixedFieldTransport_baseIntegerAlgebra_heq; subst fixedFieldTransport_baseIntegerTopology_heq; subst xO; subst xcrO; subst xalgO; subst xOk; subst xcrOk; subst xalgOk; subst xzk; subst xpD; subst xchi1; subst xSig; subst xfinSig; subst xjS; subst xside; subst xrhoS; subst fixedFieldTransport_initialPlaceSet_heq; subst xhEig; subst xLam; subst xsideL; subst xRCG; subst xgrpRCG; subst xfinRCG; subst xart; subst xth
  subst hi; subst hQ; subst hχ
  exact ⟨ψ, ι, A, hO, hF, rfl, fun _ => HEq.rfl⟩

theorem rawPack_eq_pow : PrN → ∀ (D₁ D₂ : D7) (p : TwPack D₁) (A : Finset (PlE D₁.host)) (ι : GlobalTheory.Mem.Top.TwChar.RootIso D₁ p.1 p.2.2.1) (χ : HChar D₁.host.E) (cf : CharFrame D₂) (C : NChoice D₂) (tp : TupTied D₂ cf C) (v : D₂.what₂.places.Pl), SameExport D₁ D₂ → BlochKatoReduction.Gen.PsiOk p.1 A p.2.1 p.2.2.1 p.2.2.2 → GlobalTheory.Mem.Top.TwChar.FrobPick p.1 p.2.1 p.2.2.1 p.2.2.2 ι χ → PsiChoiceCompatible D₂ cf C tp → TwistedAt D₂ v → HEq (C.twI v) p.1 → HEq (C.Q v) p.2.1 → C.k' v = p.2.2.1 → HEq (tp.psi v) χ → (∀ z : ℂ, z ^ D₂.what₂.places.resChar v ^ C.k' v = 1 → ∃ x : D₂.what₂.LL, D₂.what₂.embLL x = z) → ∃ a : ℤ, Nat.Coprime a.natAbs (D₁.ntw.l p.1) ∧ HEq (rawPack C v) (GlobalTheory.HeightCounting.twPackPow D₁ a p) := by
  intro hc D₁ D₂ p A ι χ cf C tp v h hO hF hT htw hi hQ hk hχ hL
  obtain ⟨ψ₂, ι₂, A₂, hO₂, hF₂, hl, hpow⟩ := transfer h p A ι χ hO hF (C.twI v) (C.Q v) (C.k' v) (tp.psi v) hi hQ hk hχ
  obtain ⟨a, ha, hψ⟩ := pow_of_tied hc.cheb cf C tp v ψ₂ ι₂ hF₂ hT htw hO₂.2.2.1 hL
  refine ⟨a, by rw [Int.natAbs_natCast, ← hl]; exact ha, ?_⟩
  have e : rawPack C v = (⟨C.twI v, C.Q v, C.k' v, ψ₂ ^ (a : ℤ)⟩ : TwPack D₂) := by
    rw [zpow_natCast, ← hψ]
    rfl
  rw [e]
  exact hpow a

end GlobalTheory.HeightCounting.Rigid
