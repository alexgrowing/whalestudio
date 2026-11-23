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

theorem locA_of (H : Hyp) (J : Hyp2) (hC : ConeFacA) (hS : StdA) : LocA' := by
  obtain ⟨e₁, e₂, hC⟩ := hC
  obtain ⟨s, hS⟩ := hS
  refine ⟨e₁, e₂, s, fun F E _ _ _ _ _ σ B b a' G G₁ H₀ H' cfg R R₁ e e' he he' K μK μ hK hμK hμ => ?_⟩
  by_cases ex : ¬ ∃ X om om', IsTriple B G X om om'
  · exact ⟨1, one_ne_zero, fun X om om' _ _ _ _ m => absurd ⟨X, om, om', m.triple⟩ ex⟩
  obtain ⟨X₀, om₀, om₀', t₀⟩ := not_not.1 ex
  obtain ⟨ms, hms⟩ := J.meas F E σ B _ G.V _ _ t₀.base t₀.geo.hV K hK
  obtain ⟨ei, ev, h1, h2, h3⟩ := he.loc
  have hl : IsEvLoc G.M G₁.M e ei ev := ⟨h1, h2, h3⟩
  obtain ⟨ei', ev', h1', h2', h3'⟩ := he'.loc
  have hl' : IsEvLoc G.M' G₁.M' e' ei' ev' := ⟨h1', h2', h3'⟩
  obtain ⟨κ, hκ, hC⟩ := hC F E σ B b a' G G₁ H₀ H' cfg e ei ev he hl K μK μ ms hK hμK hμ hms
  obtain ⟨C₁, hC₁, ct₁⟩ := J.ctSZ F E σ B b a' G G₁ H₀ H' cfg e' he'
  obtain ⟨C₂, hC₂, ct₂⟩ := J.ctBC F E σ B b a' G G₁ H₀ H' cfg e he K μK μ hK hμK hμ
  have key := one_const (ι := Chars F E × Rep σ G.V G.W × Rep σ G.V' G.W × FinMaps F (b + 2) a' × Rep σ G₁.V G₁.W ×
      Rep σ G₁.V' G₁.W × FinMaps F b a')
    (fun i => IsMatched B G i.1 i.2.1 i.2.2.1 R i.2.2.2.1 ∧ IsMatched B G₁ i.1 i.2.2.2.2.1 i.2.2.2.2.2.1 R₁ i.2.2.2.2.2.2 ∧
      Below (G.p + G.q))
    (fun i L => IsConeI B G.M i.2.1 ms ei (shiftA H₀ H') i.1.ν ((b + 2 - a') / 2) L)
    (fun L c => ∀ f ∈ G.M.Pol B.ψ B.emb, ∀ f' ∈ G.M'.Pol B.ψ B.emb, R.p f = R.p' f' → R₁.p (L f) = c • R₁.p' (ei' f'))
    (fun i c => ∀ Φ Φ', PolMatch B G i.1 R i.2.2.2.1 Φ Φ' →
        PolMatch B G₁ i.1 R₁ i.2.2.2.2.2.2 (cone B G.M i.2.1 e K μK μ (shiftA H₀ H') i.1.ν ((b + 2 - a') / 2) Φ)
          ((κ * c * stepFac B i.1 e₁ e₂ s H₀.𝔟 H'.𝔟 (1 - (((b + 2 - a') / 2 : ℕ) : ℤ)) *
          charL i.1.ν (i.1.S₀ : Set (Pl F)) ((((b + 2 - a') / 2) : ℕ) : ℂ)) • e' Φ')) ?_ ?_ ?_
  · obtain ⟨c, hc, k⟩ := key
    exact ⟨κ * c, mul_ne_zero hκ hc, fun X om om' Rf om₁ om₁' Rf₁ m m₁ bl => k (X, om, om', Rf, om₁, om₁', Rf₁) ⟨m, m₁, bl⟩⟩
  rotate_left
  · rintro ⟨X, om, om', Rf, om₁, om₁', Rf₁⟩ ⟨X', on, on', Rf', on₁, on₁', Rf₁'⟩ L L' ⟨m, -⟩ ⟨m', -⟩ a₁ a₂
    exact coneI_eq (J.runiq F E σ B _ _ _ _ G.M _ _ _ _ om on _ _ _ _ _ (pairV m.triple) (pairV m'.triple)
      (hasExp_div m.triple.chars.expβ m.triple.chars.expα) (hasExp_div m'.triple.chars.expβ m'.triple.chars.expα))
      (nu_eq m.triple.chars m'.triple.chars) a₁ a₂
  · rintro ⟨X, om, om', Rf, om₁, om₁', Rf₁⟩ ⟨m, m₁, -⟩ L c c' r r'
    haveI := m₁.real.nontriv
    obtain ⟨f₁, hf₁, n₁⟩ := ex_p_ne m₁.real.quot'.onto
    obtain ⟨f, hf, rfl⟩ := (ev_pol hl' m.triple.geo.hM' m₁.triple.geo.hM' ((H.ev0 F E σ B _ _ _ _ G.M' _ _ om' _ _ _ _ (pairV' m.triple) _
      G₁.V' G₁.W H' _ _ G₁.M' cfg.eV cfg.hH' m₁.triple.geo.hM').2 e' he')).2 f₁ hf₁
    obtain ⟨f', hf', ef⟩ := (sideV H m).ontoI (R.p' f)
    exact smul_left_injective ℂ n₁ ((r f' hf' f hf ef).symm.trans (r' f' hf' f hf ef))
  rintro ⟨X, om, om', Rf, om₁, om₁', Rf₁⟩ ⟨m, m₁, bl⟩
  dsimp only at m m₁ ⊢
  have t := m.triple
  have t₁ := m₁.triple
  have nz : NZ B G₁ om₁ om₁' :=
    (bl F E σ B _ _ G₁ X om₁ om₁' R₁ Rf₁ m₁ (by have := cfg.ep; have := cfg.q0; have := cfg.q1; omega)).2
  have inj := H.inj F E σ B _ _ G₁ X om₁ om₁' R₁ Rf₁ m₁ nz
  have j₂ : Inj B G₁.M om₁ R₁.p Rf₁.p fun _ => SB _ := fun f hf φ a => inj.1 f hf φ a.1 a.2
  have j₁ : Inj B G₁.M' om₁' R₁.p' Rf₁.p' fun _ => SB _ := fun f hf φ a => inj.2 f hf φ a.1 a.2 (Or.inl cfg.q1)
  have lev := H.levi F E σ B _ _ G.W G₁.W H' _ _ _ _ t.base t.geo.hW cfg.hH'
  have sp := H.split F E σ B _ _ G X om om' t _ G₁.W H' _ _ cfg.hH'
  have si := H.sinv F E σ B _ _ G X om om' t _ G₁.W H' _ _ cfg.hH'
  have ep := ev_pol hl' t.geo.hM' t₁.geo.hM' ((H.ev0 F E σ B _ _ _ _ G.M' _ _ om' _ _ _ _ (pairV' t) _ G₁.V' G₁.W
      H' _ _ G₁.M' cfg.eV cfg.hH' t₁.geo.hM').2 e' he')
  have evS : ∀ v, ∀ x ∈ SB _, ev' v x ∈ SB _ := fun v x hx => (h2' v).2 ▸ Submodule.mem_map_of_mem hx
  have b₁ : Br B G.M' om' G₁.M' om₁' H' X.α ((a' : ℝ) / 2) (fun _ => SB _) (fun _ => SB _) e' ei' ev' :=
    br_of lev ep.1 evS (fac_ev hl' (fun _ => le_rfl) evS) hC₁ fun f hf φ ad => by
      have hp := mem_polData hf (fun _ => le_rfl) ad
      obtain ⟨fa, h, h'⟩ := ct₁ X om om' om₁ om₁' t t₁ _ hp
      have i := si _ (Or.inr ⟨_, hp, Or.inr cfg.q0, rfl⟩) fa 0 h
      exact ⟨fa, h.2.1, fun u hu g => (i.1 u hu g).1, fun z => (i.2 z).1, h'⟩
  obtain ⟨L, Λ, u, cI, Lpol, hΛ, hu, cadd, cfac⟩ := hC X om om' om₁ om₁' t t₁
  have fn := H.fac F E σ B _ _ G X om om' t e₁ e₂ s H₀.𝔟 H'.𝔟 (1 - (((b + 2 - a') / 2 : ℕ) : ℤ))
  have hk : κ * ((idealVal X.ν H₀.𝔟 ^ (e₁ : ℤ) * idealVal X.ν H'.𝔟 ^ (e₂ : ℤ) : ℂˣ) : ℂ) *
      charL X.ν (X.S₀ : Set (Pl F)) ((((b + 2 - a') / 2) : ℕ) : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hκ (Units.ne_zero _)) (fn.2 _ (by have := t.geo.eBig; have := cfg.ep; omega))
  have ΛS : ∀ v, ∀ x ∈ SB _, Λ v x ∈ SB _ := fun v x hx => (hΛ v x hx).2
  have cf := fac_cone (S := fun _ => SB _) (S₁ := fun _ => SB _) hk hu (fun _ => le_rfl) ΛS (fun v _ => vac_sb t₁.geo.hM v) cfac
  have b₂ : Br B G.M om G₁.M om₁ H' X.α ((a' : ℝ) / 2) (fun _ => SB _) (fun _ => SB _) _ L Λ :=
    br_of lev Lpol ΛS cf hC₂ fun f hf φ ad => by
      have hp := mem_polData hf (fun _ => le_rfl) ad
      obtain ⟨⟨fa, fb⟩, h, -⟩ := sp.1 _ hp
      have i := si _ (Or.inl ⟨_, hp, rfl⟩) fa fb h
      exact ⟨fa, h.2.1, fun u hu g => (i.1 u hu g).1, fun z => (i.2 z).1, ct₂ X om om' om₁ om₁' t t₁ _ hp fa fb h⟩
  have std := fun v (hv : v ∈ X.T) => hS F E σ B b a' G G₁ H₀ H' cfg e ei ev e' ei' ev' he hl he' hl' K ms hK hms X om om' R Rf om₁ om₁'
    R₁ Rf₁ m m₁ ⟨v, t.chars.sub hv⟩ hv
  have wne : ∀ v ∈ X.T, wT B X s (1 - (((b + 2 - a') / 2 : ℕ) : ℤ)) v ≠ 0 := by
    have := fn.1
    rw [stepFac_eq t.chars.sub] at this
    exact Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul this)
  have std' : ∀ v ∈ X.T, ∃ φ ∈ SB _, ∃ φ' ∈ SB _, Rf.p v φ = Rf.p' v φ' ∧ Rf₁.p' v (ev' v φ') ≠ 0 ∧
      Rf₁.p v (Λ v φ) = wT B X s (1 - (((b + 2 - a') / 2 : ℕ) : ℤ)) v • Rf₁.p' v (ev' v φ') := fun v hv => by
    obtain ⟨φ, hφ, φ', hφ', x, y, z⟩ := std v hv
    exact ⟨φ, hφ, φ', hφ', x, y, by rw [(hΛ v _ hφ).1, wT, dif_pos (t.chars.sub hv)]; exact z⟩
  haveI := m₁.real.nontriv
  have pt₁ : Pt B G.M' (fun _ => SB _) R₁.p' Rf₁.p' ei' ev' := by
    refine pt_of ?_ X.T (fun v hv => ?_) fun v hv => ⟨vac_sb t.geo.hM' v, by
      rw [(h2' v).1, ← (m₁.fin.sph v hv).1]; exact (m₁.fin.sph v hv).2⟩
    · obtain ⟨f₁, hf₁, n₁⟩ := ex_p_ne m₁.real.quot'.onto
      obtain ⟨f, hf, rfl⟩ := ep.2 f₁ hf₁
      exact ⟨f, hf, n₁⟩
    · obtain ⟨-, -, φ, hφ, -, y, -⟩ := std' v hv
      exact ⟨φ, hφ, y⟩
  have pt₂ : Pt B G.M (fun _ => SB _) R₁.p Rf₁.p L Λ := by
    refine pt_of ?_ X.T (fun v hv => ?_) fun v hv => ⟨vac_sb t.geo.hM v, ?_⟩
    · obtain ⟨Φ, hΦ, n0⟩ := nz.1
      refine bump_pt H (pairV t₁) (sideV H m₁) (H.dense F E σ B _ _ _ _ _ _ _ om _ _ _ _ (pairV t)) Lpol
        (nz_pure (sideV H m₁) _ ?_ hΦ n0)
        (J.bumpA F E σ B b a' G G₁ H₀ H' cfg e ei ev he hl K ms hK hms X om om' om₁ om₁' t t₁ L cI)
      rintro _ ⟨f, -, φ, x, y, rfl⟩
      exact ⟨f, φ, ⟨x, y⟩, rfl⟩
    · obtain ⟨φ, hφ, φ', -, -, y, z⟩ := std' v hv
      exact ⟨φ, hφ, z ▸ smul_ne_zero (wne v hv) y⟩
    · rw [(hu _ hv).2, map_smul]
      exact smul_ne_zero (hu _ hv).1 (m₁.fin.sph v hv).2
  obtain ⟨li, lf, e1, e2, i1, i2⟩ := lams (side_condition_vanishing H m cfg.q0) (side_condition_vanishing H m₁ cfg.q1) b₁ j₁ pt₁ (crossM m) (crossM m₁) cfg.hH' t₁.geo.hW
  obtain ⟨li', lf', e1', e3, i1', i2'⟩ := lams (sideV H m) (sideV H m₁) b₂ j₂ pt₂ (sideV H m).cross (sideV H m₁).cross cfg.hH' t₁.geo.hW
  have ty : StepTy G G₁ X X.α ((a' : ℝ) / 2) := Or.inr ⟨rfl, rfl, cfg.ep, cfg.q1.trans cfg.q0.symm, rfl, rfl⟩
  obtain ⟨c, hc⟩ := J.inf F E σ B _ _ _ _ G G₁ X om om' om₁ om₁' R Rf R₁ Rf₁ H' _ _ _ _ m m₁ ty cfg.hH' li li' i1 i1' (by
    obtain ⟨f, hf, -, -, n, -⟩ := pt₁
    rintro rfl
    exact n (e1 f hf).symm)
  have hw : ∀ v, lf' v = (if v ∈ X.T then wT B X s (1 - (((b + 2 - a') / 2 : ℕ) : ℤ)) v else u v) • lf v := fun v => by
    split_ifs with hv
    · obtain ⟨φ, hφ, φ', hφ', x, y, z⟩ := std' v hv
      obtain ⟨k, hk⟩ := J.ram F E σ B _ _ _ _ G G₁ X om om' om₁ om₁' R Rf R₁ Rf₁ H' _ _ _ _ m m₁ ty cfg.hH' v hv _ _ (i2 v) (i2' v)
        fun h => y (by rw [← e2 v φ' hφ', h]; rfl)
      have := e3 v φ hφ
      rw [z, hk, x, LinearMap.smul_apply, e2 v φ' hφ'] at this
      rw [hk, smul_left_injective ℂ y this]
    · refine J.unr F E σ B _ _ _ _ G G₁ X om om' om₁ om₁' R Rf R₁ Rf₁ H' _ _ _ _ m m₁ ty cfg.hH' v hv _ _ (i2 v) (i2' v) _ ?_
      rw [e3 v _ (vac_sb t.geo.hM v), (m.fin.sph v hv).1, e2 v _ (vac_sb t.geo.hM' v), (hu v hv).2, map_smul, (h2' v).1,
        (m₁.fin.sph v hv).1]
  refine ⟨L, c, ?_, cI, fun f hf f' hf' x => by rw [← e1' f hf, hc, x, LinearMap.smul_apply, e1 f' hf'], fun Φ Φ' pm => ?_⟩
  · obtain ⟨f, hf, -, -, n, -⟩ := pt₂
    rintro rfl
    exact n (by rw [← e1' f hf, hc, zero_smul]; rfl)
  · obtain ⟨T, hT, n, n', f, φ, f', φ', a1, a2, rfl, rfl, tm⟩ := pm
    have pne : (∏ v ∈ T \ X.T, u v) ≠ 0 := Finset.prod_ne_zero_iff.2 fun v hv => (hu v (Finset.mem_sdiff.1 hv).2).1
    set k₀ := κ * ((idealVal X.ν H₀.𝔟 ^ (e₁ : ℤ) * idealVal X.ν H'.𝔟 ^ (e₂ : ℤ) : ℂˣ) : ℂ) *
      charL X.ν (X.S₀ : Set (Pl F)) ((((b + 2 - a') / 2) : ℕ) : ℂ) with hk₀
    set K₀ := κ * c * stepFac B X e₁ e₂ s H₀.𝔟 H'.𝔟 (1 - (((b + 2 - a') / 2 : ℕ) : ℤ)) * charL X.ν (X.S₀ : Set (Pl F)) ((((b + 2 - a') / 2) : ℕ) : ℂ) with hK₀
    refine ⟨T, hT, n, n', fun j => ((∏ v ∈ T \ X.T, u v)⁻¹ * k₀) • L (f j),
      fun j v => if v ∈ T then Λ v (φ j v) else G₁.M.vac v, fun i => K₀ • ei' (f' i), fun i v => ev' v (φ' i v),
      fun j => ⟨Submodule.smul_mem _ _ (Lpol _ (a1 j).1), fun v => ?_, fun v hv => if_neg hv⟩,
      fun i => ⟨Submodule.smul_mem _ _ (ep.1 _ (a2 i).1), fun v => evS v _ ((a2 i).2.1 v), fun v hv => by beta_reduce; rw [(a2 i).2.2 v hv, (h2' v).1]⟩,
      ?_, ?_, ?_⟩
    · beta_reduce
      split_ifs
      exacts [(hΛ v _ ((a1 j).2.1 v)).2, vac_sb t₁.geo.hM v]
    · rw [cone_sum cadd _ fun j => admissible_pure_tensor_schwartz t.geo.hM _ ⟨(a1 j).2.1, ev_of_off (a1 j).2.2⟩]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [pure_smul, mul_smul, ← cfac T hT _ _ (a1 j).2.1 (a1 j).2.2, inv_smul_smul₀ pne]
    · rw [map_sum, Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [h3' _ _ (a2 i).2.1 (ev_of_off (a2 i).2.2), pure_smul]
    · have := tens_step li lf c (fun v => if v ∈ X.T then wT B X s (1 - (((b + 2 - a') / 2 : ℕ) : ℤ)) v else u v) _
        (fun j v => Rf.p' v (φ' j v)) _ (fun i v => Rf.p v (φ i v)) tm.symm ((∏ v ∈ T \ X.T, u v)⁻¹ * k₀)
      have ek : (∏ v ∈ T \ X.T, u v)⁻¹ * k₀ * c * ∏ v ∈ T, (if v ∈ X.T then wT B X s (1 - (((b + 2 - a') / 2 : ℕ) : ℤ)) v else u v) = K₀ := by
        rw [prod_w hT, hK₀, hk₀, stepFac_eq t.chars.sub]
        field_simp
      rw [ek] at this
      refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (this.symm.trans (Finset.sum_congr rfl fun j _ => ?_))
      · rw [map_smul, ← e1' _ (a1 i).1, hc, LinearMap.smul_apply]
        congr 2; funext v
        beta_reduce
        rw [if_pos v.2, ← e3 v _ ((a1 i).2.1 v), hw v, LinearMap.smul_apply]
      · rw [map_smul, e1 _ (a2 j).1]
        congr 2; funext v; exact e2 v _ ((a2 j).2.1 v)

end PositivityTheory.ThKG.Loc

end
