import Development.WeilBound.ThetaLifts.LatticeBasics.ThConstMatch
import Development.WeilBound.ThetaLifts.LatticeBasics.ThConstAn
import Development.WeilBound.ThetaLifts.FrameEstimates.SquareIntegrableWeilRange
import Development.WeilBound.ThetaLifts.CartanFactorisation.CartanConj

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

open PositivityTheory.ThKEst (GrpTop EpsOf FinVolU)
open PositivityTheory.ThKF (Unimod)
open PositivityTheory.KCo (SoSt)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n n' d : ℕ}

namespace TC

theorem chrW_div {v : Pl F} (χ χ' : Chr F E) (t : E →ₐ[F] Fv F v) (x : (Fv F v)ˣ) : chrW (χ / χ') t x = chrW χ t x / chrW χ' t x :=
  map_div Circle.toUnits _ _

theorem chrW_norm {v : Pl F} (χ : Chr F E) (t : E →ₐ[F] Fv F v) (x : (Fv F v)ˣ) : ‖(chrW χ t x : ℂ)‖ = 1 := Circle.norm_coe _

theorem const_of (hL : LocDist) (hC : ConstOfGood) (hT : ThetaBasic) (h1 : GrpTop) (h2 : EpsOf) (h3 : FinVolU) (h4 : Unimod)
    (hS : SplitModel) {B : Base F E} {X : Spc F E n} {X' : Spc F E n'} {W : Spc F E d} {M : Model σ X W} {M' : Model σ X' W}
    {om : Rep σ X W} {om' : Rep σ X' W} {χ χ' χ₂ : Chr F E} {r s r₁ s₁ r' s' : ℕ} (p : IsPair B M χ (χ / χ') om r s r' s')
    (p' : IsPair B M' χ' χ₂ om' r₁ s₁ r' s') (e : Fin n ⊕ Fin n' ≃ Fin d) (hn : 2 ≤ n) (T : Finset (Pl F))
    (hne : ∀ v ∉ T, SplitsFully E v → ∃ t : E →ₐ[F] Fv F v, chrW (χ / χ') t (unifAt v) ≠ 1)
    (C : Fn F n' d →ₗ[ℂ] (UA σ W.J → ℂ)) (hr : ∀ Φ ∈ PolData B M', IsRapid (C Φ))
    (he : ∀ v (_ : E →ₐ[F] Fv F v), ∀ h ∈ UAt σ W (evFin F v), ∀ Φ ∈ PolData B M', om' (1, h) Φ ∈ PolData B M' ∧ C (om' (1, h) Φ) = fun x => C Φ (x * h))
    {μ : Measure (UA σ W.J)} {D : Set (UA σ W.J)} (hμ : μ.IsHaarMeasure) (hD : IsFundamentalDomain (ratU σ W.J) D μ) :
    ∀ Φ ∈ PolData B M', ∀ Ψ ∈ schA F _, ∀ g, th om μ D (C Φ) Ψ g = th om μ D (C Φ) Ψ 1 := by
  intro Φ hΦ Ψ hΨ
  have hB := p.base
  have eW := (h2 F E σ B hB d W r' s' (.inr p.skew)).1
  obtain ⟨a1, a2, -, -, -, -, -, a5⟩ := h1 F E σ hB.cm n X.J (h2 F E σ B hB n X r s (.inl p.herm)).1
  obtain ⟨u0, -, u2⟩ := h4 F E σ hB.cm d W.J (-1) (fun i j => by simp [p.skew.skew]) eW.2
  have := u2 μ hμ
  have : FirstCountableTopology (UA σ X.J) := TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _
  have fin := h3 F E σ hB.cm d W.J eW μ D hμ hD
  have hk : ∀ Ψ ∈ schA F (Fin n × Fin d), Ker (theta om Ψ) := (hT F E σ B n d X W M _ _ om _ _ _ _ p).1
  have hp := p.weil.isUSplitting.pres
  refine hC F E σ B n X r s hB p.herm hn T _ ((hk Ψ hΨ).cont a5 (hr Φ hΦ) fin) (fun γ hγ g => ?_) fun v hv hs u hu g => ?_
  · have : theta om Ψ (γ * g) = theta om Ψ g := funext fun h => by
      rw [← (hk Ψ hΨ).2.1 γ hγ 1 (one_mem _) g h, one_mul]
    rw [th, th, this]
  obtain ⟨t, ht⟩ := hne v hv hs
  obtain ⟨s1, ι, b, l1, r1⟩ := hS F E σ B n d X W M _ _ om _ _ _ _ p v t
  obtain ⟨-, ι', b', -, r2⟩ := hS F E σ B n' d X' W M' _ _ om' _ _ _ _ p' v t
  obtain ⟨L, hl⟩ := exists_form hp hk fin (PolData B M') C hr g
  obtain ⟨g₀, hg⟩ := l1 u hu
  have key := inv_loc hL e p'.good b b' (chrW_norm _ t) (chrW_norm _ t) (chrW_div χ χ' t) ht L (fun h₀ => by
    obtain ⟨h, hh, e0⟩ := s1 h₀
    refine ⟨h, r1 h hh h₀ e0, r2 h hh h₀ e0, fun Φ hΦ Ψ hΨ => ?_⟩
    rw [hl _ (he v t h hh Φ hΦ).1 _ (hp _ _ hΨ), hl _ hΦ _ hΨ, (he v t h hh Φ hΦ).2, th_right hD (hk Ψ hΨ) (hr Φ hΦ)]) hg Φ hΦ Ψ hΨ
  rw [hl _ hΦ _ (hp _ _ hΨ), hl _ hΦ _ hΨ] at key
  rw [← key, th, th]
  congr 1
  funext x
  rw [theta_act, mul_one]

variable {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
  {R : RealMaps F a a'} {Rf : FinMaps F a a'}

theorem pol_mem {Φ Φ'} (h : PolMatch B G X R Rf Φ Φ') : Φ ∈ PolData B G.M ∧ Φ' ∈ PolData B G.M' := by
  obtain ⟨T, -, m, m', f, φ, f', φ', h1, h2, rfl, rfl, -⟩ := h
  exact ⟨Submodule.sum_mem _ fun i _ => Submodule.subset_span
      ⟨f i, (h1 i).1, φ i, (h1 i).2.1, T.eventually_cofinite_notMem.mono (h1 i).2.2, rfl⟩,
    Submodule.sum_mem _ fun i _ => Submodule.subset_span
      ⟨f' i, (h2 i).1, φ' i, (h2 i).2.1, T.eventually_cofinite_notMem.mono (h2 i).2.2, rfl⟩⟩

theorem pol_le {Y : Spc F E n} {W : Spc F E d} {M : Model σ Y W} (hM : M.IsGood B.ψ) : PolData B M ≤ schA F _ := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, -, φ, h1, h2, rfl⟩
  exact PositivityTheory.KCo.pure_mem_schA f φ h1 ((h2.and hM.std).mono fun _ h => h.1.trans h.2)

theorem I_add {Y : Spc F E n} {W : Spc F E d} {M : Model σ Y W} {o : Rep σ Y W}
    (hp : ∀ x, ∀ Ψ ∈ schA F (Fin n × Fin d), o x Ψ ∈ schA F _) {Φ Ψ : Fn F n d} (hΦ : Φ ∈ schA F _) (hΨ : Ψ ∈ schA F _)
    (c1 : M.Conv o Φ) (c2 : M.Conv o Ψ) : M.I o (Φ + Ψ) = M.I o Φ + M.I o Ψ := funext fun h => by
  simp only [Model.I, theta_add hp hΦ hΨ]
  exact integral_add (c1 h) (c2 h)

theorem I_smul {Y : Spc F E n} {W : Spc F E d} (M : Model σ Y W) (o : Rep σ Y W) (c : ℂ) (Φ : Fn F n d) :
    M.I o (c • Φ) = c • M.I o Φ := funext fun h => by
  simp only [Model.I, theta_smul, integral_const_mul, Pi.smul_apply, smul_eq_mul]

theorem I_zero {Y : Spc F E n} {W : Spc F E d} (M : Model σ Y W) (o : Rep σ Y W) : M.I o 0 = 0 := by
  simpa using I_smul M o 0 0

def matched (hm : IsMatched B G X om om' R Rf) : Submodule ℂ (Fn F a (a + a') × Fn F a' (a + a')) where
  carrier := {y | PolMatch B G X R Rf y.1 y.2}
  zero_mem' := pm_zero
  add_mem' h h' := by simpa using pm_add hm 1 h h'
  smul_mem' c _ h := by simpa using pm_add hm c h pm_zero

theorem exists_maps (hD : KDecay) (hF : Factor) (hm : IsMatched B G X om om' R Rf) (s t : ℂ) :
    ∃ (C : Fn F a (a + a') →ₗ[ℂ] (UA σ G.W.J → ℂ)) (C' : Fn F a' (a + a') →ₗ[ℂ] (UA σ G.W.J → ℂ)),
      (∀ y ∈ pairs B G X R Rf, C y.1 = comb G om om' s t y) ∧ ∀ Φ Φ', PolMatch B G X R Rf Φ Φ' → C' Φ' = C Φ := by
  obtain ⟨d1, d2⟩ := hD F E σ B a a' G X om om' hm.triple
  obtain ⟨f1, f2⟩ := hF F E σ B a a' G X om om' R Rf hm
  let P := (G.M'.So B.ψ B.τ₁).comap (LinearMap.snd ℂ _ _) ⊓ matched hm
  have m1 : ∀ y : P, y.1.1 ∈ schA F _ := fun y => pol_le hm.triple.geo.hM (pol_mem y.2.2).1
  have m2 : ∀ y : P, y.1.2 ∈ schA F _ := fun y => pol_le hm.triple.geo.hM' (pol_mem y.2.2).2
  let c : P →ₗ[ℂ] (UA σ G.W.J → ℂ) :=
    { toFun := fun y => comb G om om' s t y.1
      map_add' := fun y z => by
        simp only [comb, Submodule.coe_add, Prod.fst_add, Prod.snd_add]
        rw [I_add hm.triple.weil.isUSplitting.pres (m1 y) (m1 z) (d1 _ (m1 y)) (d1 _ (m1 z)),
          I_add hm.triple.weil'.isUSplitting.pres (m2 y) (m2 z) (d2 _ y.2.1).2.1 (d2 _ z.2.1).2.1]
        module
      map_smul' := fun x y => by
        simp only [comb, Submodule.coe_smul, Prod.smul_fst, Prod.smul_snd, I_smul, RingHom.id_apply]
        module }
  obtain ⟨C, hC⟩ := exists_fac (LinearMap.fst ℂ _ _ ∘ₗ P.subtype) c fun y h => by
    have h0 : y.1.1 = 0 := h
    have h1 : PolMatch B G X R Rf y.1.1 y.1.2 := y.2.2
    change comb G om om' s t y.1 = 0
    rw [comb, f2 y.1.2 y.2.1 (h0 ▸ h1), h0, I_zero, smul_zero, smul_zero, add_zero]
  have k : ∀ y ∈ pairs B G X R Rf, C y.1 = comb G om om' s t y := fun y hy => hC ⟨y, hy⟩
  obtain ⟨C', hC'⟩ := exists_fac (LinearMap.snd ℂ _ _ ∘ₗ (matched hm).subtype) (C ∘ₗ LinearMap.fst ℂ _ _ ∘ₗ (matched hm).subtype)
    fun y h => by
      have h0 : y.1.2 = 0 := h
      have h1 : PolMatch B G X R Rf y.1.1 y.1.2 := y.2
      change C y.1.1 = 0
      rw [k y.1 ⟨h0 ▸ zero_mem _, h1⟩, comb, f1 _ (h0 ▸ h1), h0, I_zero, smul_zero, smul_zero, add_zero]
  exact ⟨C, C', k, fun Φ Φ' h => hC' ⟨(Φ, Φ'), h⟩⟩

end TC

open TC in
theorem thConst_of (hL : LocDist) (hG : GoodNe) (hC : ConstOfGood) (hF : Factor) (hM : MatchEx) (hT : ThetaBasic) (hD : KDecay)
    (h1 : GrpTop) (h2 : EpsOf) (h3 : FinVolU) (h4 : Unimod) (hS : SplitModel) (hO : SoSt) : ThConst := by
  intro F E _ _ _ _ _ σ B a a' G X om om' R Rf hm s t hr μ D hμ hD' y hy
  obtain ⟨C, C', c1, c2⟩ := exists_maps hD hF hm s t
  obtain ⟨m1, m2, -⟩ := hM F E σ B a a' G X om om' R Rf hm
  have hg := hG F E σ B a a' G X om om' hm.triple
  have r1 : ∀ Φ ∈ PolData B G.M, IsRapid (C Φ) := fun Φ hΦ => by
    obtain ⟨Φ', h, h'⟩ := m1 Φ hΦ
    exact c1 (Φ, Φ') ⟨h, h'⟩ ▸ hr (Φ, Φ') ⟨h, h'⟩
  have e1 : ∀ v (_ : E →ₐ[F] Fv F v), ∀ h ∈ UAt σ G.W (evFin F v), ∀ Φ ∈ PolData B G.M,
      om (1, h) Φ ∈ PolData B G.M ∧ C (om (1, h) Φ) = fun x => C Φ (x * h) := fun v w h hh Φ hΦ => by
    obtain ⟨Φ', k, k'⟩ := m1 Φ hΦ
    have k2 := pm_fin hS hm w hh k'
    refine ⟨(pol_mem k2).1, ?_⟩
    rw [c1 (_, _) ⟨hO F E σ B a a' G X om om' hm.triple _ _ k, k2⟩, c1 (Φ, Φ') ⟨k, k'⟩]
    funext x
    simp only [comb, Model.I, Pi.add_apply, Pi.smul_apply, theta_act, mul_one]
  have l1 := hm.triple.geo.lt
  have l2 := hm.triple.geo.aBig
  rw [← c1 y hy]
  refine ⟨c2 _ _ hy.2 ▸ const_of hL hC hT h1 h2 h3 h4 hS (pairV hm.triple) (pairV' hm.triple) finSumFinEquiv (by omega) X.T
    (fun v hv hs => ?_) C' (fun Φ' h => ?_) (fun v w h hh Φ' hΦ => ?_) hμ hD' _ (pol_mem hy.2).2,
    const_of hL hC hT h1 h2 h3 h4 hS (pairV' hm.triple) (pairV hm.triple) ((Equiv.sumComm _ _).trans finSumFinEquiv) (by omega) X.T
    (fun v hv hs => ?_) C r1 e1 hμ hD' _ (pol_mem hy.2).1⟩
  · obtain ⟨⟨t⟩, h⟩ := hg v ⟨hv, hs⟩
    refine ⟨t, fun h' => h t ?_⟩
    rw [chrW_div, div_eq_one] at h'
    rw [Chars.ν, chrW_div, h', div_self']
  · obtain ⟨Φ, k⟩ := m2 Φ' h
    exact c2 _ _ k ▸ r1 Φ (pol_mem k).1
  · obtain ⟨Φ, k⟩ := m2 Φ' hΦ
    have k2 := pm_fin hS hm w hh k
    exact ⟨(pol_mem k2).2, by rw [c2 _ _ k2, c2 _ _ k, (e1 v w h hh Φ (pol_mem k).1).2]⟩
  · obtain ⟨⟨t⟩, h⟩ := hg v ⟨hv, hs⟩
    exact ⟨t, h t⟩

end GlobalTheory.ThK.Dbl

end
