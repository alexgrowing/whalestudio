import Development.WeilBound.ThetaLifts.LocalTheory.StepFacEq

noncomputable section

namespace PositivityTheory.ThKG.Loc

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open PositivityTheory.ThKF
open scoped Classical

theorem locB_of (H : Hyp) (J : Hyp2) (hC : ConeFacB) (hS : StdB) : LocB' := by
  obtain ⟨e₁, e₂, hC⟩ := hC
  obtain ⟨s, hS⟩ := hS
  refine ⟨e₁, e₂, s, fun F E _ _ _ _ _ σ B a b G G₁ H₀ H' cfg R R₁ e e' he he' K μK μ hK hμK hμ => ?_⟩
  by_cases ex : ¬ ∃ X om om', IsTriple B G X om om'
  · exact ⟨1, one_ne_zero, fun X om om' _ _ _ _ m => absurd ⟨X, om, om', m.triple⟩ ex⟩
  obtain ⟨X₀, om₀, om₀', t₀⟩ := not_not.1 ex
  obtain ⟨ms, hms⟩ := J.meas F E σ B _ G.V' _ _ t₀.base t₀.geo.hV' K hK
  obtain ⟨ei, ev, h1, h2, h3⟩ := he.loc
  have hl : IsEvLoc G.M G₁.M e ei ev := ⟨h1, h2, h3⟩
  obtain ⟨ei', ev', h1', h2', h3'⟩ := he'.loc
  have hl' : IsEvLoc G.M' G₁.M' e' ei' ev' := ⟨h1', h2', h3'⟩
  obtain ⟨κ, hκ, hC⟩ := hC F E σ B a b G G₁ H₀ H' cfg e' ei' ev' he' hl' K μK μ ms hK hμK hμ hms
  obtain ⟨C₁, hC₁, ct₁⟩ := J.ctBZ F E σ B a b G G₁ H₀ H' cfg e he
  obtain ⟨C₂, hC₂, ct₂⟩ := J.ctSC F E σ B a b G G₁ H₀ H' cfg e' he' K μK μ hK hμK hμ
  have key := one_const (ι := Chars F E × Rep σ G.V G.W × Rep σ G.V' G.W × FinMaps F a (b + 2) × Rep σ G₁.V G₁.W ×
      Rep σ G₁.V' G₁.W × FinMaps F a b)
    (fun i => IsMatched B G i.1 i.2.1 i.2.2.1 R i.2.2.2.1 ∧ IsMatched B G₁ i.1 i.2.2.2.2.1 i.2.2.2.2.2.1 R₁ i.2.2.2.2.2.2 ∧
      Below (G.p + G.q))
    (fun i L => IsConeI B G.M' i.2.2.1 ms ei' (shiftB σ H₀ H') i.1.ν ((a - (b + 2)) / 2 + 1) L)
    (fun L c => ∀ f ∈ G.M.Pol B.ψ B.emb, ∀ f' ∈ G.M'.Pol B.ψ B.emb, R.p f = R.p' f' → R₁.p' (L f') = c • R₁.p (ei f))
    (fun i c => ∀ Φ, ∀ Φ' ∈ G.M'.So B.ψ B.τ₁, PolMatch B G i.1 R i.2.2.2.1 Φ Φ' →
      cone B G.M' i.2.2.1 e' K μK μ (shiftB σ H₀ H') i.1.ν ((a - (b + 2)) / 2 + 1) Φ' ∈ G₁.M'.So B.ψ B.τ₁ ∧
        PolMatch B G₁ i.1 R₁ i.2.2.2.2.2.2 ((κ * c * stepFac B i.1 e₁ e₂ s H₀.𝔟 H'.𝔟 (-(((a - (b + 2)) / 2 : ℕ) : ℤ)) *
          charL i.1.ν (i.1.S₀ : Set (Pl F)) ((((a - (b + 2)) / 2 : ℕ) : ℂ) + 1)) • e Φ)
          (cone B G.M' i.2.2.1 e' K μK μ (shiftB σ H₀ H') i.1.ν ((a - (b + 2)) / 2 + 1) Φ')) ?_ ?_ ?_
  · obtain ⟨c, hc, k⟩ := key
    exact ⟨κ * c, mul_ne_zero hκ hc, fun X om om' Rf om₁ om₁' Rf₁ m m₁ bl => k (X, om, om', Rf, om₁, om₁', Rf₁) ⟨m, m₁, bl⟩⟩
  rotate_left
  · rintro ⟨X, om, om', Rf, om₁, om₁', Rf₁⟩ ⟨X', on, on', Rf', on₁, on₁', Rf₁'⟩ L L' ⟨m, -⟩ ⟨m', -⟩ a₁ a₂
    exact coneI_eq (J.runiq F E σ B _ _ _ _ G.M' _ _ _ _ om' on' _ _ _ _ _ (pairV' m.triple) (pairV' m'.triple)
      (hasExp_div m.triple.chars.expα m.triple.chars.expβ) (hasExp_div m'.triple.chars.expα m'.triple.chars.expβ))
      (nu_eq m.triple.chars m'.triple.chars) a₁ a₂
  · rintro ⟨X, om, om', Rf, om₁, om₁', Rf₁⟩ ⟨m, m₁, -⟩ L c c' r r'
    haveI := m₁.real.nontriv
    obtain ⟨f₁, hf₁, n₁⟩ := ex_p_ne m₁.real.quot.onto
    obtain ⟨f, hf, rfl⟩ := (ev_pol hl m.triple.geo.hM m₁.triple.geo.hM ((H.ev0 F E σ B _ _ _ _ G.M _ _ om _ _ _ _ (pairV m.triple) _ G₁.V G₁.W
      H' _ _ G₁.M cfg.eV cfg.hH' m₁.triple.geo.hM).2 e he)).2 f₁ hf₁
    obtain ⟨f', hf', ef⟩ := (sideSo H m).ontoI (R.p f)
    exact smul_left_injective ℂ n₁ ((r f hf f' hf' ef.symm).symm.trans (r' f hf f' hf' ef.symm))
  rintro ⟨X, om, om', Rf, om₁, om₁', Rf₁⟩ ⟨m, m₁, bl⟩
  dsimp only at m m₁ ⊢
  have t := m.triple
  have t₁ := m₁.triple
  have nz : NZ B G₁ om₁ om₁' := (bl F E σ B _ _ G₁ X om₁ om₁' R₁ Rf₁ m₁ (by have := cfg.ep; have := cfg.eq; omega)).2
  have inj := H.inj F E σ B _ _ G₁ X om₁ om₁' R₁ Rf₁ m₁ nz
  have j₁ : Inj B G₁.M om₁ R₁.p Rf₁.p fun _ => SB _ := fun f hf φ a => inj.1 f hf φ a.1 a.2
  have j₂ : Inj B G₁.M' om₁' R₁.p' Rf₁.p' (SS B G₁.M') := fun f hf φ a =>
    inj.2 f hf φ (fun v => SS_le v (a.1 v)) a.2 (Or.inr (SS_self (B := B) (M := G₁.M') ▸ a.1 B.v₁))
  have lev := H.levi F E σ B _ _ G.W G₁.W H' _ _ _ _ t.base t.geo.hW cfg.hH'
  have sp := H.split F E σ B _ _ G X om om' t _ G₁.W H' _ _ cfg.hH'
  have si := H.sinv F E σ B _ _ G X om om' t _ G₁.W H' _ _ cfg.hH'
  have ep := ev_pol hl t.geo.hM t₁.geo.hM ((H.ev0 F E σ B _ _ _ _ G.M _ _ om _ _ _ _ (pairV t) _ G₁.V G₁.W
      H' _ _ G₁.M cfg.eV cfg.hH' t₁.geo.hM).2 e he)
  have evS : ∀ v, ∀ x ∈ SB _, ev v x ∈ SB _ := fun v x hx => (h2 v).2 ▸ Submodule.mem_map_of_mem hx
  have b₁ : Br B G.M om G₁.M om₁ H' X.β ((a : ℝ) / 2) (fun _ => SB _) (fun _ => SB _) e ei ev :=
    br_of lev ep.1 evS (fac_ev hl (fun _ => le_rfl) evS) hC₁ fun f hf φ ad => by
      have hp := mem_polData hf (fun _ => le_rfl) ad
      obtain ⟨⟨fa, fb⟩, h, -⟩ := sp.1 _ hp
      have i := si _ (Or.inl ⟨_, hp, rfl⟩) fa fb h
      exact ⟨fb, h.2.2, fun u hu g => (i.1 u hu g).2, fun z => (i.2 z).2, ct₁ X om om' om₁ om₁' t t₁ _ hp fa fb h⟩
  obtain ⟨L, Λ, u, cI, Lpol, hΛ, hu, cadd, cfac⟩ := hC X om om' om₁ om₁' t t₁
  have fl := J.floc F E σ B a b G G₁ H₀ H' cfg e' ei' ev' he' hl' K ms hK hms X om om' om₁ om₁' t t₁
  have fn := H.fac F E σ B _ _ G X om om' t e₁ e₂ s H₀.𝔟 H'.𝔟 (-(((a - (b + 2)) / 2 : ℕ) : ℤ))
  have hk : κ * ((idealVal X.ν H₀.𝔟 ^ (e₁ : ℤ) * idealVal X.ν H'.𝔟 ^ (e₂ : ℤ) : ℂˣ) : ℂ) *
      charL X.ν (X.S₀ : Set (Pl F)) ((((a - (b + 2)) / 2 + 1) : ℕ) : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hκ (Units.ne_zero _)) (fn.2 _ (by have := t.geo.eBig; omega))
  have v₁T : B.v₁ ∉ X.T := t.chars.good.1
  have ΛS : ∀ v, ∀ x ∈ SS B G.M' v, Λ v x ∈ SS B G₁.M' v := fun v x hx => by
    by_cases ev₁ : v = B.v₁
    · subst ev₁
      rw [SS_self] at hx ⊢
      refine (Submodule.map_span_le (Λ B.v₁) _ _).2 (fun y hy => Submodule.subset_span ?_) (Submodule.mem_map_of_mem hx)
      rw [(hΛ _ y hy.1).1]; exact fl.2 y hy
    · rw [SS_ne ev₁] at hx ⊢; exact (hΛ v x hx).2
  have hvac : ∀ v, G.M'.vac v ∈ SS B G.M' v → G₁.M'.vac v ∈ SS B G₁.M' v := fun v hv => by
    by_cases ev₁ : v = B.v₁
    · subst ev₁
      have := ΛS _ _ hv
      rw [(hu _ v₁T).2] at this
      exact (Submodule.smul_mem_iff _ (hu _ v₁T).1).1 this
    · rw [SS_ne ev₁]; exact vac_sb t₁.geo.hM' v
  have cf := fac_cone hk hu SS_le ΛS hvac cfac
  have b₂ : Br B G.M' om' G₁.M' om₁' H' X.β ((a : ℝ) / 2) (SS B G.M') (SS B G₁.M') _ L Λ :=
    br_of lev Lpol ΛS cf hC₂ fun f hf φ ad => by
      have hp := mem_polData hf SS_le ad
      have hs := pure_mem_so t.geo.hM' f ad
      obtain ⟨⟨fa, fb⟩, h, -⟩ := sp.2 _ ⟨hp, hs⟩
      have i := si _ (Or.inr ⟨_, hp, Or.inl hs, rfl⟩) fa fb h
      exact ⟨fb, h.2.2, fun u hu g => (i.1 u hu g).2, fun z => (i.2 z).2, ct₂ X om om' om₁ om₁' t t₁ _ ⟨hp, hs⟩ fa fb h⟩
  have co := (H.coinv F E σ B _ _ G X om om' R Rf m).1 _ t.chars.good
  have aug : ∀ x ∈ SB _, ∀ y ∈ SB _, Rf.p' B.v₁ x = Rf.p' B.v₁ y → Rf₁.p' B.v₁ (Λ B.v₁ x) = Rf₁.p' B.v₁ (Λ B.v₁ y) := by
    intro x hx y hy exy
    have : augAt om' B.v₁ ≤ LinearMap.ker (Rf₁.p' B.v₁ ∘ₗ Λ B.v₁) := Submodule.span_le.2 (by
      rintro _ ⟨g, hg, φ, hφ, φ₁, hφ₁, ac, rfl⟩
      show Rf₁.p' B.v₁ (Λ B.v₁ (φ₁ - φ)) = 0
      refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun l => ?_
      have := fl.1 g hg φ hφ φ₁ hφ₁ ac (l ∘ₗ Rf₁.p' B.v₁) fun z hz => by
        show l (Rf₁.p' B.v₁ z) = 0
        rw [(m₁.fin.inv' B.v₁ hz : Rf₁.p' B.v₁ z = 0), map_zero]
      rw [← (hΛ _ _ hφ).1, ← (hΛ _ _ hφ₁).1] at this
      rw [map_sub, map_sub, map_sub]; exact sub_eq_zero.2 this)
    have z : Rf₁.p' B.v₁ (Λ B.v₁ (x - y)) = 0 := this ((co.2.1 _ (sub_mem hx hy)).1 (by rw [map_sub, exy, sub_self]))
    rwa [map_sub, map_sub, sub_eq_zero] at z
  have sph₁ : ∀ v ∉ X.T, Rf₁.p' v (G₁.M'.vac v) ≠ 0 := fun v hv => (m₁.fin.sph v hv).1 ▸ (m₁.fin.sph v hv).2
  have std := fun v (hv : v ∈ X.T) => hS F E σ B a b G G₁ H₀ H' cfg e ei ev e' ei' ev' he hl he' hl' K ms hK hms X om om' R Rf om₁ om₁'
    R₁ Rf₁ m m₁ ⟨v, t.chars.sub hv⟩ hv
  have wne : ∀ v ∈ X.T, wT B X s (-(((a - (b + 2)) / 2 : ℕ) : ℤ)) v ≠ 0 := by
    have := fn.1
    rw [stepFac_eq t.chars.sub] at this
    exact Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul this)
  have std' : ∀ v ∈ X.T, ∃ φ ∈ SB _, ∃ φ' ∈ SB _, Rf.p v φ = Rf.p' v φ' ∧ Rf₁.p v (ev v φ) ≠ 0 ∧
      Rf₁.p' v (Λ v φ') = wT B X s (-(((a - (b + 2)) / 2 : ℕ) : ℤ)) v • Rf₁.p v (ev v φ) := fun v hv => by
    obtain ⟨φ, hφ, φ', hφ', x, y, z⟩ := std v hv
    exact ⟨φ, hφ, φ', hφ', x, y, by rw [(hΛ v _ hφ').1, wT, dif_pos (t.chars.sub hv)]; exact z⟩
  haveI := m₁.real.nontriv
  have pt₁ : Pt B G.M (fun _ => SB _) R₁.p Rf₁.p ei ev := by
    refine pt_of ?_ X.T (fun v hv => ?_) fun v hv => ⟨vac_sb t.geo.hM v, by rw [(h2 v).1]; exact (m₁.fin.sph v hv).2⟩
    · obtain ⟨f₁, hf₁, n₁⟩ := ex_p_ne m₁.real.quot.onto
      obtain ⟨f, hf, rfl⟩ := ep.2 f₁ hf₁
      exact ⟨f, hf, n₁⟩
    · obtain ⟨φ, hφ, -, -, -, y, -⟩ := std' v hv
      exact ⟨φ, hφ, y⟩
  have pt₂ : Pt B G.M' (SS B G.M') R₁.p' Rf₁.p' L Λ := by
    refine pt_of ?_ (insert B.v₁ X.T) (fun v hv => ?_) fun v hv => ?_
    · obtain ⟨Φ, hΦ, n0⟩ := nz.2
      refine bump_pt H (pairV' t₁) (sideSo H m₁) (H.dense F E σ B _ _ _ _ _ _ _ om' _ _ _ _ (pairV' t)) Lpol
        (nz_pure (sideSo H m₁) _ ?_ hΦ.2 n0)
        (J.bumpB F E σ B a b G G₁ H₀ H' cfg e' ei' ev' he' hl' K ms hK hms X om om' om₁ om₁' t t₁ L cI)
      rintro _ ⟨f, φ, x, y, z, rfl⟩
      refine ⟨f, φ, ⟨fun v => ?_, y⟩, rfl⟩
      by_cases ev₁ : v = B.v₁
      · subst ev₁; rw [SS_self]; exact Submodule.subset_span z
      · rw [SS_ne ev₁]; exact x v
    · rcases Finset.mem_insert.1 hv with rfl | hv
      · obtain ⟨x, hx, ex⟩ := co.2.2.1 B.τ₁ (Rf.p' _ (G.M'.vac B.v₁))
        refine ⟨x, by rw [SS_self]; exact Submodule.subset_span hx, ?_⟩
        rw [aug x hx.1 _ (vac_sb t.geo.hM' _) ex, (hu _ v₁T).2, map_smul]
        exact smul_ne_zero (hu _ v₁T).1 (sph₁ _ v₁T)
      · obtain ⟨φ, -, φ', hφ', -, y, z⟩ := std' v hv
        exact ⟨φ', by rwa [SS_ne fun e => v₁T (e ▸ hv)], z ▸ smul_ne_zero (wne v hv) y⟩
    · rw [Finset.mem_insert, not_or] at hv
      refine ⟨by rw [SS_ne hv.1]; exact vac_sb t.geo.hM' v, ?_⟩
      rw [(hu _ hv.2).2, map_smul]
      exact smul_ne_zero (hu _ hv.2).1 (sph₁ _ hv.2)
  obtain ⟨li, lf, e1, e2, i1, i2⟩ := lams (sideV H m) (sideV H m₁) b₁ j₁ pt₁ (sideV H m).cross (sideV H m₁).cross cfg.hH' t₁.geo.hW
  obtain ⟨li', lf', e1', e2', i1', i2'⟩ := lams (sideSo H m) (sideSo H m₁) b₂ j₂ pt₂ (crossM m) (crossM m₁) cfg.hH' t₁.geo.hW
  have e3 : ∀ v, ∀ x ∈ SB _, lf' v (Rf.p' v x) = Rf₁.p' v (Λ v x) := fun v x hx => by
    by_cases ev₁ : v = B.v₁
    · subst ev₁
      obtain ⟨y, hy, ey⟩ := (sideSo H m).onto _ (Rf.p' _ x)
      rw [← ey, e2' _ y hy, aug y (SS_le _ hy) x hx ey]
    · exact e2' v x (by rwa [SS_ne ev₁])
  have ty : StepTy G G₁ X X.β ((a : ℝ) / 2) := Or.inl ⟨rfl, rfl, cfg.ep, cfg.eq, rfl, rfl⟩
  obtain ⟨c, hc⟩ := J.inf F E σ B _ _ _ _ G G₁ X om om' om₁ om₁' R Rf R₁ Rf₁ H' _ _ _ _ m m₁ ty cfg.hH' li li' i1 i1' (by
    obtain ⟨f, hf, -, -, n, -⟩ := pt₁
    rintro rfl
    exact n (e1 f hf).symm)
  have hw : ∀ v, lf' v = (if v ∈ X.T then wT B X s (-(((a - (b + 2)) / 2 : ℕ) : ℤ)) v else u v) • lf v := fun v => by
    split_ifs with hv
    · obtain ⟨φ, hφ, φ', hφ', x, y, z⟩ := std' v hv
      obtain ⟨k, hk⟩ := J.ram F E σ B _ _ _ _ G G₁ X om om' om₁ om₁' R Rf R₁ Rf₁ H' _ _ _ _ m m₁ ty cfg.hH' v hv _ _ (i2 v) (i2' v)
        fun h => y (by rw [← e2 v φ hφ, h]; rfl)
      have := e3 v φ' hφ'
      rw [z, hk, ← x, LinearMap.smul_apply, e2 v φ hφ] at this
      rw [hk, smul_left_injective ℂ y this]
    · refine J.unr F E σ B _ _ _ _ G G₁ X om om' om₁ om₁' R Rf R₁ Rf₁ H' _ _ _ _ m m₁ ty cfg.hH' v hv _ _ (i2 v) (i2' v) _ ?_
      rw [e2 v _ (vac_sb t.geo.hM v), (m.fin.sph v hv).1, e3 v _ (vac_sb t.geo.hM' v), (hu v hv).2, map_smul, (h2 v).1,
        (m₁.fin.sph v hv).1]
  refine ⟨L, c, ?_, cI, fun f hf f' hf' x => by rw [← e1' f' hf', hc, ← x, LinearMap.smul_apply, e1 f hf], fun Φ Φ' hΦ' pm => ⟨?_, ?_⟩⟩
  · obtain ⟨f, hf, -, -, n, -⟩ := pt₂
    rintro rfl
    exact n (by rw [← e1' f hf, hc, zero_smul]; rfl)
  · clear pm
    induction hΦ' using Submodule.span_induction with
    | mem _ h =>
      obtain ⟨f, φ, x, y, z, rfl⟩ := h
      have ad : admitted G.M' (SS B G.M') φ := ⟨fun v => by
        by_cases ev₁ : v = B.v₁
        · subst ev₁; rw [SS_self]; exact Submodule.subset_span z
        · rw [SS_ne ev₁]; exact x v, y⟩
      obtain ⟨k, ψ, -, aψ, -, w⟩ := cf φ ad B.v₁
      have := w f _ (ad.1 _)
      rw [Function.update_eq_self] at this
      rw [this]
      exact Submodule.smul_mem _ _ (pure_mem_so t₁.geo.hM' _ (aψ.upd (ΛS _ _ (ad.1 _))))
    | zero =>
      have := cadd 0 (zero_mem _) 0 (zero_mem _) 1
      simp only [smul_zero, add_zero, one_smul, left_eq_add] at this
      rw [this]; exact zero_mem _
    | add x y hx hy ix iy =>
      have := cadd x (so_le t.geo.hM' hx) y (so_le t.geo.hM' hy) 1
      rw [one_smul, one_smul] at this
      rw [this]; exact add_mem ix iy
    | smul k x hx ix =>
      have z := cadd 0 (zero_mem _) 0 (zero_mem _) 1
      simp only [smul_zero, add_zero, one_smul, left_eq_add] at z
      have := cadd 0 (zero_mem _) x (so_le t.geo.hM' hx) k
      rw [zero_add, z, zero_add] at this
      rw [this]; exact Submodule.smul_mem _ _ ix
  · obtain ⟨T, hT, n, n', f, φ, f', φ', a1, a2, rfl, rfl, tm⟩ := pm
    have pne : (∏ v ∈ T \ X.T, u v) ≠ 0 := Finset.prod_ne_zero_iff.2 fun v hv => (hu v (Finset.mem_sdiff.1 hv).2).1
    set k₀ := κ * ((idealVal X.ν H₀.𝔟 ^ (e₁ : ℤ) * idealVal X.ν H'.𝔟 ^ (e₂ : ℤ) : ℂˣ) : ℂ) *
      charL X.ν (X.S₀ : Set (Pl F)) ((((a - (b + 2)) / 2 + 1) : ℕ) : ℂ) with hk₀
    set K₀ := κ * c * stepFac B X e₁ e₂ s H₀.𝔟 H'.𝔟 (-(((a - (b + 2)) / 2 : ℕ) : ℤ)) *
      charL X.ν (X.S₀ : Set (Pl F)) ((((a - (b + 2)) / 2 : ℕ) : ℂ) + 1) with hK₀
    refine ⟨T, hT, n, n', fun i => K₀ • ei (f i), fun i v => ev v (φ i v), fun j => ((∏ v ∈ T \ X.T, u v)⁻¹ * k₀) • L (f' j),
      fun j v => if v ∈ T then Λ v (φ' j v) else G₁.M'.vac v,
      fun i => ⟨Submodule.smul_mem _ _ (ep.1 _ (a1 i).1), fun v => evS v _ ((a1 i).2.1 v), fun v hv => by beta_reduce; rw [(a1 i).2.2 v hv, (h2 v).1]⟩,
      fun j => ⟨Submodule.smul_mem _ _ (Lpol _ (a2 j).1), fun v => ?_, fun v hv => if_neg hv⟩, ?_, ?_, ?_⟩
    · beta_reduce
      split_ifs
      exacts [(hΛ v _ ((a2 j).2.1 v)).2, vac_sb t₁.geo.hM' v]
    · rw [map_sum, Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [h3 _ _ (a1 i).2.1 (ev_of_off (a1 i).2.2), pure_smul]
    · rw [cone_sum cadd _ fun j => admissible_pure_tensor_schwartz t.geo.hM' _ ⟨(a2 j).2.1, ev_of_off (a2 j).2.2⟩]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [pure_smul, mul_smul, ← cfac T hT _ _ (a2 j).2.1 (a2 j).2.2, inv_smul_smul₀ pne]
    · have := tens_step li lf c (fun v => if v ∈ X.T then wT B X s (-(((a - (b + 2)) / 2 : ℕ) : ℤ)) v else u v) _
        (fun i v => Rf.p v (φ i v)) _ (fun j v => Rf.p' v (φ' j v)) tm ((∏ v ∈ T \ X.T, u v)⁻¹ * k₀)
      have ek : (∏ v ∈ T \ X.T, u v)⁻¹ * k₀ * c *
          ∏ v ∈ T, (if v ∈ X.T then wT B X s (-(((a - (b + 2)) / 2 : ℕ) : ℤ)) v else u v) = K₀ := by
        rw [prod_w hT, hK₀, hk₀, stepFac_eq t.chars.sub]
        push_cast
        field_simp
      rw [ek] at this
      refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (this.trans (Finset.sum_congr rfl fun j _ => ?_))
      · rw [map_smul, e1 _ (a1 i).1]
        congr 2; funext v; exact (e2 v _ ((a1 i).2.1 v)).symm
      · rw [map_smul, ← e1' _ (a2 j).1, hc, LinearMap.smul_apply]
        congr 2; funext v
        beta_reduce
        rw [if_pos v.2, ← e3 v _ ((a2 j).2.1 v), hw v, LinearMap.smul_apply]

end PositivityTheory.ThKG.Loc

end
