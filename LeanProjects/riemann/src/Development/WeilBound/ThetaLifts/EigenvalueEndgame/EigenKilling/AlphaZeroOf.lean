import Development.WeilBound.ThetaLifts.EigenvalueEndgame.EigenKilling.ConeIntegralFactorisation
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.TowerCodimensionTwo
import Development.WeilBound.ThetaLifts.ConeHypotheses.PureEqPureA

noncomputable section

set_option linter.unusedSectionVars false

namespace PositivityTheory.ThKEnd.Comp

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open PositivityTheory.ThKCT PositivityTheory.ThKG PositivityTheory.ThKG.Tow PositivityTheory.ThKEst

theorem hasExp_div {τ : ∀ w : InfinitePlace F, EmbOver E w} {χ χ' : Chr F E} {m m' : InfinitePlace F → ℤ} (h : HasExp τ χ m)
    (h' : HasExp τ χ' m') : HasExp τ (χ / χ') (m - m') := fun z hz => by
  rw [MonoidHom.div_apply, Circle.coe_div, h z hz, h' z hz, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  have : piInf (τ w) (z : AE F E) ≠ 0 := (z.isUnit.map _).ne_zero
  rw [Pi.sub_apply, zpow_sub₀ (div_ne_zero this (by simpa using this))]

theorem law_cast {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H' : Plane E d d₁} {χ χ' : Chr F E} {x y : ℝ} {T : UA σ W.J → ℂ}
    (h : HasLaw W₁ H' χ x T) (e1 : χ = χ') (e2 : x = y) : HasLaw W₁ H' χ' y T := by subst e1 e2; exact h

variable {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
  {d₁ : ℕ} {W₁ : Spc F E d₁} {H' : Plane E (a + a') d₁} {i₀ i₁ : ℕ}

theorem comp_eq (hI : ThKEnd.Iwa) (hC : CTBasic) (hA : IAut) (hU : UnipEx) (hT : IsTriple B G X om om')
    (hH : H'.IsAdapted σ B G.W W₁ i₀ i₁) {Φ Φ'} (hΦ : Φ ∈ PolData B G.M) (hΦ' : Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁)
    {xa xb ya yb fa fb} (h1 : Split2 W₁ H' X (G.M.I om Φ) xa xb) (h2 : Split2 W₁ H' X (G.M'.I om' Φ') ya yb)
    (h : Split2 W₁ H' X (G.M.I om Φ - G.M'.I om' Φ') fa fb) : fa = xa - ya ∧ fb = xb - yb := by
  obtain ⟨a1, a2⟩ := hA F E σ B a a' G X om om' hT
  have hpl := (hI F E σ B _ _ _ _ H' _ _ _ _ hT.base hT.geo.hW hH).1
  have := (hC F E σ B _ _ _ _ H' _ _ hT.base hT.geo.hW hpl).1 _ _ _ _ 1 (a1 Φ hΦ) (a2 Φ' hΦ') h1.1 h2.1
  refine split_uniq hU hT hH h ⟨?_, by simpa using hasLaw_sub h1.2.1 h2.2.1 1, by simpa using hasLaw_sub h1.2.2 h2.2.2 1⟩
  simp only [one_smul] at this
  convert this using 1
  abel

theorem split_right {Φ Φ' fa fb} (h : Split2 W₁ H' X (G.M.I om Φ - G.M'.I om' Φ') fa fb) (k : UA σ G.W.J) :
    Split2 W₁ H' X (G.M.I om (om (1, k) Φ) - G.M'.I om' (om' (1, k) Φ')) (fun x => fa (x * k)) fun x => fb (x * k) := by
  rw [I_trans, I_trans]
  exact ⟨isCT_right h.1 k, hasLaw_right h.2.1 k, hasLaw_right h.2.2 k⟩

theorem small (hS : SmallAny) (hM : SoMove) (hZ : EvZero) (hP : TriplePair) (hT : IsTriple B G X om om')
    (hH : H'.IsAdapted σ B G.W W₁ i₀ i₁) {M₁ : Model σ G.V' W₁} {om₁ r₁ s₁}
    (hp₁ : IsPair B M₁ X.α (X.α / X.β) om₁ G.q (a' - G.q) r₁ s₁) (e1 : a + a' - (G.p + G.q) = r₁ + 1) (e2 : G.p + G.q = s₁ + 1)
    {Φ'} (hΦ' : Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) :
    ∃ ya yb, Split2 W₁ H' X (G.M'.I om' Φ') ya yb ∧ ∃ Ψ₁ ∈ PolData B M₁ ⊓ M₁.So B.ψ B.τ₁,
      ∀ h₁ l, IsLevi H' 1 h₁ l → ya l = M₁.I om₁ Ψ₁ h₁ := by
  obtain ⟨-, hp', -⟩ := hP F E σ B a a' G X om om' hT
  have hlt := hT.geo.lt
  have heB := hT.geo.eBig
  have haB := hT.geo.aBig
  obtain ⟨k, hk⟩ := hT.geo.even
  obtain ⟨⟨e₀, he₀⟩, hmap⟩ := hZ F E σ B _ _ G.V' G.W G.M' _ _ om' _ _ _ _ hp' d₁ G.V' W₁ H' i₀ i₁ M₁ rfl hH hp₁.good
  obtain ⟨Ψ, hΨ, hI, hso⟩ := hM F E σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hp₁ e₀ he₀ Φ' hΦ'
  obtain ⟨C₀, -, H0⟩ := hS F E σ B a' (a + a') d₁ G.V' G.W W₁ H' i₀ i₁ G.q (a' - G.q) r₁ s₁ G.M' M₁
    (by omega) ⟨(a - a') / 2 + 1, by omega, by omega⟩ hH e₀ he₀
  obtain ⟨A₀, A₁, c1, c2, c3, c4⟩ := H0 _ _ om' om₁ (IsPair.cast hp' rfl rfl e1 e2) hp₁ Ψ hΨ.1 (fun _ => hΨ.2)
  refine ⟨A₀, A₁, ⟨hI ▸ c1, c2, law_cast c3 (by simp) (by push_cast; ring)⟩, C₀ • e₀ Ψ,
    Submodule.smul_mem _ _ ⟨hmap e₀ he₀ ▸ Submodule.mem_map_of_mem hΨ.1, hso⟩, fun h₁ l hl => ?_⟩
  have := c4 h₁ l hl 1
  rw [show ((1 : UA σ G.V'.J), (1 : UA σ G.W.J)) = 1 from rfl, map_one, Module.End.one_apply, mul_one] at this
  rw [this fun _ => hso, ThKG.I_smul]

theorem alphaZero_of (hI : ThKEnd.Iwa) (hC : CTBasic) (hA : IAut) (hU : UnipEx) (hL : Low) (hPx : PairEx) (hP : TriplePair)
    (hZ : EvZero) (hAn : GenAniso) (hS : SmallAny) (hM : SoMove) (hSt : PolStab) (h0 : IZero) : AlphaZero := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT hp0 hq d₁ W₁ H' i₀ i₁ r s hH _ f hf fa fb hs
  obtain ⟨hp, hp', -⟩ := hP F E σ B a a' G X om om' hT
  obtain ⟨h1, h2, hW₁⟩ := (hL F E σ B _ _ G.W W₁ H' i₀ i₁ _ _ hT.base hH).2 hT.geo.hW
  have haB := hT.geo.aBig
  have hrk := hH.rank
  have hpl := (hI F E σ B _ _ _ _ H' _ _ _ _ hT.base hT.geo.hW hH).1
  refine comp_zero hI hT.base hT.geo.hW hH hs.2.1 (fun u hu h => ((hC F E σ B _ _ _ _ H' _ _ hT.base hT.geo.hW hpl).2 _ _ _ _ _ _ _
    (sig_isAut hA hT hf) (half_ne hT) hs.1 hs.2.1 hs.2.2 u hu h).1) fun h₁ l hl k hk => ?_
  obtain ⟨Φ, hΦ, Φ', hΦ', rfl⟩ := hf
  obtain ⟨s1, s2⟩ := hSt F E σ B a a' G X om om' hT k hk
  obtain ⟨⟨M₁, hM₁⟩, hW⟩ := hPx F E σ B hT.base _ _ G.V W₁ _ _ _ _ hT.geo.hV hW₁
  obtain ⟨om₁, hp₁⟩ := hW _ _ hp.hX hp.hW hp.resX (res_low hp.resW hH.rank) M₁ hM₁
  obtain ⟨⟨e₀, he₀⟩, -⟩ := hZ F E σ B _ _ G.V G.W G.M _ _ om _ _ _ _ hp d₁ G.V W₁ H' i₀ i₁ M₁ rfl hH hM₁
  obtain ⟨C, -, H0⟩ := hAn F E σ B a _ d₁ G.V G.W W₁ H' i₀ i₁ (a - G.p) G.p _ _ _ _ G.V G.M M₁ rfl (by omega) hH e₀ he₀
  obtain ⟨A₀, c1, c2, -⟩ := H0 _ _ om om₁ hp hp₁ _ (polData_le hp.good (s1 Φ hΦ))
  obtain ⟨⟨M₂, hM₂⟩, hW'⟩ := hPx F E σ B hT.base _ _ G.V' W₁ _ _ _ _ hT.geo.hV' hW₁
  obtain ⟨om₂, hp₂⟩ := hW' _ _ hp'.hX hp'.hW hp'.resX (res_low hp'.resW hH.rank) M₂ hM₂
  obtain ⟨ya, yb, hy, Ψ₁, hΨ₁, hv⟩ := small hS hM hZ hP hT hH hp₂ (by omega) (by omega) (s2 Φ' hΦ')
  have e := congrFun (comp_eq hI hC hA hU hT hH (s1 Φ hΦ) (s2 Φ' hΦ') (xa := 0) (xb := A₀)
    ⟨by rwa [zero_add], hasLaw_zero _ _, c2⟩ hy (split_right hs k)).1 l
  have z := (h0 F E σ B _ _ _ _ M₂ _ _ om₂ _ _ _ _ hp₂ _ (hasExp_div hT.chars.expα hT.chars.expβ) (fun w => by
    have := hT.geo.kappa w
    rw [Pi.sub_apply]
    refine lt_of_lt_of_le ?_ (le_abs_self _)
    omega) (by omega)).2 Ψ₁ hΨ₁.2
  simpa [hv h₁ l hl, z] using e

theorem betaZero_of (hI : ThKEnd.Iwa) (hC : CTBasic) (hA : IAut) (hU : UnipEx) (hL : Low) (hPx : PairEx) (hP : TriplePair)
    (hZ : EvZero) (hAn : GenAniso) (hB : BigAny) (h0 : IZero) : BetaZero := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT hq0 hp1 d₁ W₁ H' i₀ i₁ hH f hf fa fb hs
  obtain ⟨hp, hp', hw⟩ := hP F E σ B a a' G X om om' hT
  obtain ⟨h1, h2, hW₁⟩ := (hL F E σ B _ _ G.W W₁ H' i₀ i₁ _ _ hT.base hH).2 hT.geo.hW
  have hlt := hT.geo.lt
  have heB := hT.geo.eBig
  have haB := hT.geo.aBig
  obtain ⟨k, hk⟩ := hT.geo.even
  have hrk := hH.rank
  obtain ⟨Φ, hΦ, Φ', hΦ', rfl⟩ := hf
  obtain ⟨⟨M₁, hM₁⟩, hW⟩ := hPx F E σ B hT.base _ _ G.V W₁ _ _ _ _ hT.geo.hV hW₁
  obtain ⟨om₁, hp₁⟩ := hW _ _ hp.hX hp.hW hp.resX (res_low hp.resW hH.rank) M₁ hM₁
  obtain ⟨⟨e₀, he₀⟩, -⟩ := hZ F E σ B _ _ G.V G.W G.M _ _ om _ _ _ _ hp d₁ G.V W₁ H' i₀ i₁ M₁ rfl hH hM₁
  obtain ⟨C₀, -, H0⟩ := hB F E σ B a (a + a') d₁ G.V G.W W₁ H' i₀ i₁ (a - G.p) G.p _ _ G.M M₁
    (by omega) ⟨(a - a') / 2, by omega, by omega⟩ hH e₀ he₀
  obtain ⟨A₀, A₁, c1, c2, c3, c4⟩ := H0 _ _ om om₁ (IsPair.cast hp rfl rfl (by omega) (by omega)) hp₁ Φ hΦ (by simp)
  obtain ⟨⟨M₂, hM₂⟩, hW'⟩ := hPx F E σ B hT.base _ _ G.V' W₁ _ _ _ _ hT.geo.hV' hW₁
  obtain ⟨om₂, hp₂⟩ := hW' _ _ hp'.hX hp'.hW hp'.resX (res_low hp'.resW hH.rank) M₂ hM₂
  obtain ⟨⟨e₂, he₂⟩, -⟩ := hZ F E σ B _ _ G.V' G.W G.M' _ _ om' _ _ _ _ hp' d₁ G.V' W₁ H' i₀ i₁ M₂ rfl hH hM₂
  obtain ⟨C, -, H1⟩ := hAn F E σ B a' _ d₁ G.V' G.W W₁ H' i₀ i₁ G.q (a' - G.q) _ _ _ _ G.V' G.M' M₂ rfl (by omega) hH e₂ he₂
  obtain ⟨A, b1, b2, -⟩ := H1 _ _ om' om₂ hp' hp₂ _ (polData_le hp'.good hΦ'.1)
  have e := (comp_eq hI hC hA hU hT hH hΦ hΦ' (xa := A₁) (xb := A₀) (ya := A) (yb := 0)
    ⟨by rwa [add_comm A₁], law_cast c3 (by simp) (by push_cast; ring), c2⟩ ⟨by rwa [add_zero], b2, hasLaw_zero _ _⟩ hs).2
  have z := (h0 F E σ B _ _ _ _ M₁ _ _ om₁ _ _ _ _ hp₁ _ (hasExp_div hT.chars.expβ hT.chars.expα) (fun w => by
    have := hT.geo.kappa w
    rw [Pi.sub_apply]
    refine lt_of_lt_of_le ?_ (neg_le_abs _)
    omega) (by omega)).1 (by omega)
  rw [e, sub_zero]
  funext h
  have := c4 1 1 (isLevi_one H') h (by simp)
  rw [one_mul, z _ (he₀.maps _ (hp.weil.isUSplitting.pres _ _ (polData_le hp.good hΦ)))] at this
  simpa using this

theorem alphaLow_of (hI : ThKEnd.Iwa) (hC : CTBasic) (hA : IAut) (hU : UnipEx) (hPx : PairEx) (hP : TriplePair)
    (hZ : EvZero) (hCo : EvCone) (hSx : StabEx) (hIw : IwaEx) (hK : KFinData) (hB : GenBig) (hS : SmallAny) (hM : SoMove)
    (hSt : PolStab) (hCP : ConePol) : AlphaLow := by
  intro F E _ _ _ _ _ σ B b a' G G₁ X om om' om₁ om₁' H H' hT hT₁ hc hq f hf fa fb hs k hk
  obtain ⟨hp, hp', -⟩ := hP F E σ B _ a' G X om om' hT
  obtain ⟨hp₁, hp₁', -⟩ := hP F E σ B _ a' G₁ X om₁ om₁' hT₁
  have hlt := hT.geo.lt
  have heB := hT.geo.eBig
  have haB := hT.geo.aBig
  have e1 := hc.ep
  have e2 := hc.eq
  obtain ⟨j, hj⟩ := hT.geo.even
  obtain ⟨Φ, hΦ, Φ', hΦ', rfl⟩ := hf
  obtain ⟨s1, s2⟩ := hSt F E σ B _ a' G X om om' hT k hk
  obtain ⟨⟨e, he⟩, -⟩ := hCo F E σ B _ _ G.V G.W G.M _ _ om _ _ _ _ hp _ _ G₁.V G₁.W H H' _ _ _ _ G₁.M hc.hH hc.hH' hp₁.good
  obtain ⟨K, μK, μ, hK1, -, hμK, hμ⟩ := hSx F E σ B _ G.V _ _ hT.base hp.herm
  have hcp := hCP F E σ B b a' G G₁ H H' hc e he K μK μ hK1 hμK hμ X om om' om₁ om₁' hT hT₁ _ (s1 Φ hΦ)
  obtain ⟨⟨M₁, hM₁⟩, hW⟩ := hPx F E σ B hT.base _ _ G.V G₁.W _ _ _ _ hT.geo.hV hT₁.geo.hW
  obtain ⟨⟨e₀, he₀⟩, -⟩ := hZ F E σ B _ _ G.V G.W G.M _ _ om _ _ _ _ hp _ G.V G₁.W H' _ _ M₁ rfl hc.hH' hM₁
  obtain ⟨C₀, C₁, -, -, H0⟩ := hB F E σ B _ _ _ _ G.V G.W G₁.V G₁.W H H' _ _ _ _ (b - G₁.p) G₁.p (b + a' - (G₁.p + G₁.q))
    (G₁.p + G₁.q) G.M G₁.M hc.hH hc.hH' M₁ e₀ e hM₁ hT₁.geo.hM he₀ he ((b + 2 - a') / 2) ⟨by omega, by omega⟩ K μK μ
    (hIw F E σ B _ _ G.V _ _ H hT.base hT.geo.hV (adapted_x_ne hc.hH) hc.hH.xx K hK1) hμK hμ
  obtain ⟨om₂, hp₂⟩ := hW _ _ hp.hX hp.hW hp.resX hp₁.resW M₁ hM₁
  obtain ⟨hs1, hf⟩ := hK F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hp K hK1 _ (s1 Φ hΦ)
  obtain ⟨A₀, A₁, c1, c2, c3, c4⟩ := H0 _ _ om om₂ om₁ (IsPair.cast hp (by omega) (by omega) (by omega) (by omega))
    (IsPair.cast hp₂ (by omega) (by omega) rfl rfl) hp₁ _ hs1 hf
  obtain ⟨p₁, q₁, V₁, V₁', W₁, N₁, N₁'⟩ := G₁
  obtain ⟨eV, -, -, hH, hH'⟩ := hc
  dsimp only at eV e1 e2 hH hH' hp₁ hp₁' om₁ om₁'
  subst eV e2
  obtain ⟨ya, yb, hy, Ψ₁, hΨ₁, hv⟩ := small hS hM hZ hP hT hH' hp₁' (by omega) (by omega) (s2 Φ' hΦ')
  have e := (comp_eq hI hC hA hU hT hH' (s1 Φ hΦ) (s2 Φ' hΦ') (xa := A₁) (xb := A₀)
    ⟨by rwa [add_comm A₁], law_cast c3 (by simp) (by push_cast; ring), c2⟩ hy (split_right hs k)).1
  refine ⟨_, ⟨_, Submodule.smul_mem _ C₁ hcp, Ψ₁, hΨ₁, rfl⟩, fun h₁ l hl => ?_⟩
  have := (c4 h₁ l hl 1).1
  rw [show ((1 : UA σ G.V.J), (1 : UA σ G.W.J)) = 1 from rfl, map_one, Module.End.one_apply, mul_one, inv_div] at this
  have e' := congrFun e l
  simp only [Pi.sub_apply] at e' ⊢
  rw [e', this, hv h₁ l hl, ThKG.I_smul]
  rfl

theorem polStab_of (hR : KReal) (hF : KFin) (hM : MatchEx) (hS : MatchStab) : PolStab := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT k hk
  obtain ⟨R, hR⟩ := hR F E σ B a a' G X om om' hT
  obtain ⟨Rf, hF⟩ := hF F E σ B a a' G X om om' hT
  have hm : IsMatched B G X om om' R Rf := ⟨hT, hR, hF⟩
  obtain ⟨m1, m2, -⟩ := hM F E σ B a a' G X om om' R Rf hm
  refine ⟨fun Φ hΦ => ?_, fun Φ' hΦ' => ?_⟩
  · obtain ⟨Φ', h1, h2⟩ := m1 Φ hΦ
    exact (polMatch_mem (hS F E σ B a a' G X om om' R Rf hm k hk Φ Φ' h1 h2).2).1
  · obtain ⟨Φ, h2⟩ := m2 Φ' hΦ'.1
    obtain ⟨h3, h4⟩ := hS F E σ B a a' G X om om' R Rf hm k hk Φ Φ' hΦ'.2 h2
    exact ⟨(polMatch_mem h4).2, h3⟩

end PositivityTheory.ThKEnd.Comp

end
