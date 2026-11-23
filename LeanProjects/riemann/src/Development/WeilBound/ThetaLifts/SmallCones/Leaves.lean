import Development.WeilBound.ThetaLifts.SmallCones.ThetaUniq
import Development.WeilBound.ThetaLifts.SmallCones.ThetaKernelGeneralIdentity

noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem lawα {n d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H' : Plane E d d₁} {χ χ' : Chr F E} {x y : ℝ} {T : UA σ W.J → ℂ}
    (_n : n = n) (h : HasLaw W₁ H' χ x T) (e1 : χ = χ') (e2 : x = y) : HasLaw W₁ H' χ' y T := by subst e1 e2; exact h

theorem splitEx_of (hB : GenBig) (hSm : GenSmall) (hA : GenAniso) (hK : KFinData) (hS : StabEx) (hI : IwaEx) (hP : PairEx)
    (hPl : PlaneHerm) (hC : EvCone) (hZ : EvZero) (hU : UnipEx) (hL : Low) (hT : TriplePair) : SplitEx := by
  intro F E _ _ _ _ _ σ B a a' G X om om' h d₁ W₁ H' i₀ i₁ hH'
  obtain ⟨hp, hp', hw⟩ := hT F E σ B a a' G X om om' h
  obtain ⟨h1, h2, hW₁⟩ := (hL F E σ B _ _ G.W W₁ H' i₀ i₁ _ _ h.base hH').2 h.geo.hW
  have hlt := h.geo.lt
  have hev := h.geo.even
  have heB := h.geo.eBig
  have haB := h.geo.aBig
  obtain ⟨k, hk⟩ := hev
  have uniq : ∀ f fa fb, Split2 W₁ H' X f fa fb → ∃! x : (UA σ G.W.J → ℂ) × (UA σ G.W.J → ℂ), Split2 W₁ H' X f x.1 x.2 :=
    fun f fa fb hs => ⟨(fa, fb), hs, fun y hy => Prod.ext (split_uniq hU h hH' hy hs).1 (split_uniq hU h hH' hy hs).2⟩
  refine ⟨fun Φ hΦ => ?_, fun Φ hΦ => ?_⟩
  · obtain ⟨⟨M₁, hM₁⟩, hW⟩ := hP F E σ B h.base _ _ G.V W₁ _ _ _ _ h.geo.hV hW₁
    obtain ⟨om₁, hp₁⟩ := hW _ _ hp.hX hp.hW hp.resX (res_low hp.resW hH'.rank) M₁ hM₁
    obtain ⟨⟨e₀, he₀⟩, -⟩ := hZ F E σ B _ _ G.V G.W G.M _ _ om _ _ _ _ hp d₁ G.V W₁ H' i₀ i₁ M₁ rfl hH' hM₁
    obtain ⟨C₀, -, H0⟩ := anyBig hB hA hK hS hI hP hPl hC F E σ B a (a + a') d₁ G.V G.W W₁ H' i₀ i₁ (a - G.p) G.p _ _ G.M M₁
      (by omega) ⟨(a - a') / 2, by omega, by omega⟩ hH' e₀ he₀
    obtain ⟨A₀, A₁, c1, c2, c3, -⟩ := H0 _ _ om om₁ (IsPair.cast hp rfl rfl (by omega) (by omega)) hp₁ Φ hΦ (by simp)
    exact uniq _ A₁ A₀ ⟨by rwa [add_comm A₁], lawα (n := 0) rfl c3 (by simp) (by push_cast; ring), c2⟩
  · obtain ⟨⟨M₁, hM₁⟩, hW⟩ := hP F E σ B h.base _ _ G.V' W₁ _ _ _ _ h.geo.hV' hW₁
    obtain ⟨om₁, hp₁⟩ := hW _ _ hp'.hX hp'.hW hp'.resX (res_low hp'.resW hH'.rank) M₁ hM₁
    obtain ⟨⟨e₀, he₀⟩, -⟩ := hZ F E σ B _ _ G.V' G.W G.M' _ _ om' _ _ _ _ hp' d₁ G.V' W₁ H' i₀ i₁ M₁ rfl hH' hM₁
    obtain ⟨C₀, -, H0⟩ := anySmall hSm hA hK hS hI hP hPl hC F E σ B a' (a + a') d₁ G.V' G.W W₁ H' i₀ i₁ G.q (a' - G.q) _ _ G.M' M₁
      (by omega) ⟨(a - a') / 2 + 1, by omega, by omega⟩ hH' e₀ he₀
    obtain ⟨A₀, A₁, c1, c2, c3, -⟩ := H0 _ _ om' om₁ (IsPair.cast hp' rfl rfl (by omega) (by omega)) hp₁ Φ hΦ.1 (fun _ => hΦ.2)
    exact uniq _ A₀ A₁ ⟨c1, c2, lawα (n := 0) rfl c3 (by simp) (by push_cast; ring)⟩

theorem ctBigZero_of (hB : GenBig) (hA : GenAniso) (hK : KFinData) (hS : StabEx) (hI : IwaEx) (hP : PairEx)
    (hPl : PlaneHerm) (hC : EvCone) (hU : UnipEx) (hT : TriplePair) : CTBigZero := by
  intro F E _ _ _ _ _ σ B a b G G₁ H H' hc e he
  obtain ⟨p₁, q₁, V₁, V₁', W₁, M₁, M₁'⟩ := G₁
  obtain ⟨eV, ep, eq, hH, hH'⟩ := hc
  dsimp only at eV ep eq hH hH' he
  subst eV ep
  by_cases hex : ∃ X om om', IsTriple B G X om om'
  swap
  · exact ⟨1, one_ne_zero, fun X om om' _ _ h => absurd ⟨X, om, om', h⟩ hex⟩
  obtain ⟨X0, o, o', h0⟩ := hex
  have hlt := h0.geo.lt
  have heB := h0.geo.eBig
  have haB := h0.geo.aBig
  obtain ⟨k, hk⟩ := h0.geo.even
  obtain ⟨C₀, hC₀, H0⟩ := anyBig hB hA hK hS hI hP hPl hC F E σ B a (a + (b + 2)) (a + b) G.V G.W W₁ H' _ _ (a - G.p) G.p
    (a + b - (G.p + q₁)) (G.p + q₁) G.M M₁ (by omega) ⟨(a - (b + 2)) / 2, by omega, by omega⟩ hH' e he
  refine ⟨C₀, hC₀, fun X om om' om₁ om₁' h h₁ Φ hΦ fa fb hs g m hm x => ?_⟩
  obtain ⟨A₀, A₁, c1, c2, c3, c4⟩ := H0 _ _ om om₁ (IsPair.cast (hT F E σ B _ _ G X om om' h).1 rfl rfl (by omega) (by omega))
    (hT F E σ B _ _ _ X om₁ om₁' h₁).1 Φ hΦ (by simp)
  have := split_uniq hU h hH' hs (fa' := A₁) (fb' := A₀)
    ⟨by rwa [add_comm A₁], lawα (n := 0) rfl c3 (by simp) (by push_cast; ring), c2⟩
  rw [this.2]
  exact c4 g m hm x (by simp)

theorem ctSmallZero_of (hA : GenAniso) (hK : KFinData) (hS : StabEx) (hT : TriplePair) : CTSmallZero := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' hc e he
  obtain ⟨C, hC, H0⟩ := hA F E σ B a' _ _ G.V' G.W G₁.W H' _ _ G.q (a' - G.q) (b + 2 + a' - (G.p + G.q)) (G.p + G.q)
    (b + a' - (G₁.p + G₁.q)) (G₁.p + G₁.q) G₁.V' G.M' G₁.M' hc.eV (by rw [hc.q0]; simp) hc.hH' e he
  refine ⟨C, hC, fun X om om' om₁ om₁' h h₁ Φ hΦ => ?_⟩
  have hp := (hT F E σ B _ _ G X om om' h).2.1
  obtain ⟨K, μK, μ, hK1, -⟩ := hS F E σ B _ G.V' _ _ h.base hp.herm
  obtain ⟨A₀, c1, c2, c3⟩ := H0 _ _ om' om₁' hp
    (IsPair.cast (hT F E σ B _ _ G₁ X om₁ om₁' h₁).2.1 (by rw [hc.q0, hc.q1]) (by rw [hc.q0, hc.q1]) rfl rfl) Φ
    (hK F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hp K hK1 Φ hΦ).1
  exact ⟨A₀, ⟨by rwa [add_zero], c2, fun t m _ h => by simp⟩, c3⟩

theorem ctBigCone_of (hB : GenBig) (hK : KFinData) (hI : IwaEx) (hP : PairEx) (hZ : EvZero) (hU : UnipEx) (hT : TriplePair) :
    CTBigCone := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' hc e he K μK μ hK1 hμK hμ
  by_cases hex : ∃ X om om' om₁ om₁', IsTriple B G X om om' ∧ IsTriple B G₁ X om₁ om₁'
  swap
  · exact ⟨1, one_ne_zero, fun X om om' om₁ om₁' h h₁ => absurd ⟨X, om, om', om₁, om₁', h, h₁⟩ hex⟩
  obtain ⟨X0, o, o', o₁, o₁', h0, h1⟩ := hex
  have hlt := h0.geo.lt
  have heB := h0.geo.eBig
  have haB := h0.geo.aBig
  have e1 := hc.ep
  have e2 := hc.q0
  have e3 := hc.q1
  obtain ⟨k, hk⟩ := h0.geo.even
  obtain ⟨⟨M₁, hM₁⟩, hW⟩ := hP F E σ B h0.base _ _ G.V G₁.W _ _ _ _ h0.geo.hV h1.geo.hW
  obtain ⟨⟨e₀, he₀⟩, -⟩ := hZ F E σ B _ _ G.V G.W G.M _ _ o _ _ _ _ (hT F E σ B _ _ G X0 o o' h0).1 _ G.V G₁.W H' _ _ M₁ rfl hc.hH' hM₁
  obtain ⟨C₀, C₁, -, hC₁, H0⟩ := hB F E σ B _ _ _ _ G.V G.W G₁.V G₁.W H H' _ _ _ _ (b - G₁.p) G₁.p (b + a' - (G₁.p + G₁.q))
    (G₁.p + G₁.q) G.M G₁.M hc.hH hc.hH' M₁ e₀ e hM₁ h1.geo.hM he₀ he ((b + 2 - a') / 2) ⟨by omega, by omega⟩ K μK μ
    (hI F E σ B _ _ G.V _ _ H h0.base h0.geo.hV (adapted_x_ne hc.hH) hc.hH.xx K hK1) hμK hμ
  refine ⟨C₁, hC₁, fun X om om' om₁ om₁' h h₁ Φ hΦ fa fb hs g m hm x => ?_⟩
  have hp := (hT F E σ B _ _ G X om om' h).1
  have hp₁ := (hT F E σ B _ _ G₁ X om₁ om₁' h₁).1
  obtain ⟨om₂, hp₂⟩ := hW _ _ hp.hX hp.hW hp.resX hp₁.resW M₁ hM₁
  obtain ⟨hs1, hf⟩ := hK F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hp K hK1 Φ hΦ
  obtain ⟨A₀, A₁, c1, c2, c3, c4⟩ := H0 _ _ om om₂ om₁ (IsPair.cast hp (by omega) (by omega) (by omega) (by omega))
    (IsPair.cast hp₂ (by omega) (by omega) rfl rfl) hp₁ Φ hs1 hf
  have := split_uniq hU h hc.hH' hs (fa' := A₁) (fb' := A₀)
    ⟨by rwa [add_comm A₁], lawα (n := 0) rfl c3 (by simp) (by push_cast; ring), c2⟩
  rw [this.1, (c4 g m hm x).1, inv_div]
  rfl

theorem ctSmallCone_of (hB : GenSmall) (hK : KFinData) (hI : IwaEx) (hP : PairEx) (hZ : EvZero) (hU : UnipEx) (hT : TriplePair) :
    CTSmallCone := by
  intro F E _ _ _ _ _ σ B a b G G₁ H H' hc e he K μK μ hK1 hμK hμ
  by_cases hex : ∃ X om om' om₁ om₁', IsTriple B G X om om' ∧ IsTriple B G₁ X om₁ om₁'
  swap
  · exact ⟨1, one_ne_zero, fun X om om' om₁ om₁' h h₁ => absurd ⟨X, om, om', om₁, om₁', h, h₁⟩ hex⟩
  obtain ⟨X0, o, o', o₁, o₁', h0, h1⟩ := hex
  have hlt := h0.geo.lt
  have heB := h0.geo.eBig
  have haB := h0.geo.aBig
  have e1 := hc.ep
  have e2 := hc.eq
  obtain ⟨k, hk⟩ := h0.geo.even
  obtain ⟨⟨M₁, hM₁⟩, hW⟩ := hP F E σ B h0.base _ _ G.V' G₁.W _ _ _ _ h0.geo.hV' h1.geo.hW
  obtain ⟨⟨e₀, he₀⟩, -⟩ := hZ F E σ B _ _ G.V' G.W G.M' _ _ o' _ _ _ _ (hT F E σ B _ _ G X0 o o' h0).2.1 _ G.V' G₁.W H' _ _ M₁ rfl
    hc.hH' hM₁
  obtain ⟨C₀, C₁, -, hC₁, H0⟩ := hB F E σ B _ _ _ _ G.V' G.W G₁.V' G₁.W H H' _ _ _ _ G₁.q (b - G₁.q) (a + b - (G₁.p + G₁.q))
    (G₁.p + G₁.q) G.M' G₁.M' hc.hH hc.hH' M₁ e₀ e hM₁ h1.geo.hM' he₀ he ((a - (b + 2)) / 2 + 1) ⟨by omega, by omega⟩ K μK μ
    (hI F E σ B _ _ G.V' _ _ H h0.base h0.geo.hV' (adapted_x_ne hc.hH) hc.hH.xx K hK1) hμK hμ
  refine ⟨C₁, hC₁, fun X om om' om₁ om₁' h h₁ Φ hΦ fa fb hs g m hm x => ?_⟩
  have hp := (hT F E σ B _ _ G X om om' h).2.1
  have hp₁ := (hT F E σ B _ _ G₁ X om₁ om₁' h₁).2.1
  obtain ⟨om₂, hp₂⟩ := hW _ _ hp.hX hp.hW hp.resX hp₁.resW M₁ hM₁
  obtain ⟨-, hf⟩ := hK F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hp K hK1 Φ hΦ.1
  obtain ⟨A₀, A₁, c1, c2, c3, c4⟩ := H0 _ _ om' om₂ om₁' (IsPair.cast hp (by omega) (by omega) (by omega) (by omega))
    (IsPair.cast hp₂ (by omega) (by omega) rfl rfl) hp₁ Φ hΦ.2 hf
  have := split_uniq hU h hc.hH' hs (fa' := A₀) (fb' := A₁) ⟨c1, c2, lawα (n := 0) rfl c3 (by simp) (by push_cast; ring)⟩
  rw [this.2, (c4 g m hm x).1]
  rfl

end PositivityTheory.ThKCT

end
