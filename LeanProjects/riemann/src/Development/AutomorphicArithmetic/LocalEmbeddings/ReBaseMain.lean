import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ReBaseUniq
import Development.AutomorphicArithmetic.LocalEmbeddings.ReBaseReal
import Development.AutomorphicArithmetic.LocalEmbeddings.ReBaseArch
import Development.AutomorphicArithmetic.LocalEmbeddings.ReBaseZeta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedDataRestrictionUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedLocalIsomorphismScalars
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceCharacterComponentSmoothUnitaryConductStatement

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ReBase

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {V : Spc F E a} {V' : Spc F E a'} {Z : Spc F E (a + a')}

theorem polMatch_iso {R R₃ : RealMaps F a a'} {Rf Rf₃ : FinMaps F a a'} {ψ₀ : R.Pi ≃ₗ[ℂ] R₃.Pi} {l₀ : ℂ}
    {ψ : ∀ v, Rf.Pi v ≃ₗ[ℂ] Rf₃.Pi v} {l : Pl F → ℂ} (hl1 : ∀ v ∉ X.T, l v = 1)
    (hR : ∀ f ∈ G.M.Pol B.ψ B.emb, R₃.p f = ψ₀ (R.p f)) (hR' : ∀ f ∈ G.M'.Pol B.ψ B.emb, R₃.p' f = l₀ • ψ₀ (R.p' f))
    (hRf : ∀ v, ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), Rf₃.p v φ = ψ v (Rf.p v φ))
    (hRf' : ∀ v, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Rf₃.p' v φ = l v • ψ v (Rf.p' v φ))
    {Φ Φ'} (hM : PolMatch B G X R Rf Φ Φ') : PolMatch B G X R₃ Rf₃ ((l₀ * ∏ v ∈ X.T, l v) • Φ) Φ' := by
  set Λ : ℂ := l₀ * ∏ v ∈ X.T, l v with hΛdef
  obtain ⟨T, hT, m, m', f, φ, f', φ', hf, hf', hΦ, hΦ', heq⟩ := hM
  have hΛT : l₀ * ∏ v ∈ T, l v = Λ := by
    rw [hΛdef, Finset.prod_subset hT (fun v _ hv => hl1 v hv)]
  refine ⟨T, hT, m, m', fun i => Λ • f i, φ, f', φ', fun i => ⟨Submodule.smul_mem _ _ (hf i).1, (hf i).2⟩, hf', ?_, hΦ', ?_⟩
  · rw [hΦ, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    funext x
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]
  · let L := TensorProduct.map ψ₀.toLinearMap (PiTensorProduct.map fun v : T => (ψ v).toLinearMap)
    have h1 := congrArg L heq
    simp only [map_sum, L, TensorProduct.map_tmul, PiTensorProduct.map_tprod, LinearEquiv.coe_coe] at h1
    have lhs : ∀ i, R₃.p (Λ • f i) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => Rf₃.p v (φ i v)) =
        Λ • (ψ₀ (R.p (f i)) ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ fun v : T => ψ v (Rf.p v (φ i v))) := by
      intro i
      have e : (fun v : T => Rf₃.p v (φ i v)) = fun v : T => ψ v (Rf.p v (φ i v)) :=
        funext fun v => hRf v _ ((hf i).2.1 v)
      rw [e, map_smul, hR _ (hf i).1, ← TensorProduct.smul_tmul']
    have rhs : ∀ j, R₃.p' (f' j) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => Rf₃.p' v (φ' j v)) =
        Λ • (ψ₀ (R.p' (f' j)) ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ fun v : T => ψ v (Rf.p' v (φ' j v))) := by
      intro j
      have e : (fun v : T => Rf₃.p' v (φ' j v)) = fun v : T => l v • ψ v (Rf.p' v (φ' j v)) :=
        funext fun v => hRf' v _ ((hf' j).2.1 v)
      rw [e, MultilinearMap.map_smul_univ, hR' _ (hf' j).1, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul,
        Finset.prod_coe_sort, hΛT]
    simp only [lhs, rhs, ← Finset.smul_sum, h1]

variable (B G V V' Z) in

def kapId : (AE F E)ˣ :=
  ∏ v : B.P, locIdele F (splitPrime (B.τ v))
    (Units.map (complMap (splitPrime_under (B.τ v))).toMonoidHom (kap G V V' Z v.1))

theorem chr_kapId (χ : Chr F E) :
    (χ (kapId B G V V' Z) : ℂ) = ∏ v : B.P, (chrW χ (B.τ v) (kap G V V' Z v.1) : ℂ) := by
  rw [kapId, map_prod]
  exact map_prod Circle.coeHom _ _

variable {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in

theorem fin_scalar (hP : GlobalTheory.FunPr.Hypotheses₂) {R R₂ : RealMaps F a a'} {Rf S : FinMaps F a a'}
    (hM : IsMatched B G X om om' R Rf) (hM₂ : IsMatched B (reG G V V' Z) X om om' R₂ S) :
    ∃ (ψ : ∀ v, Rf.Pi v ≃ₗ[ℂ] S.Pi v) (l : Pl F → ℂ), (∀ v ∉ X.T, l v = 1) ∧
      (∀ v, ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), S.p v φ = ψ v (Rf.p v φ)) ∧
      (∀ v, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), S.p' v φ = l v • ψ v (Rf.p' v φ)) ∧
      ∏ v ∈ X.T, l v = X.ν (kapId B G V V' Z) := by
  choose ψ l hl h3 h4 h5 using finMaps_unique hP F E σ B a a' G X om om' R Rf hM V V' Z S hM₂.fin
  refine ⟨ψ, l, h5, h3, h4, ?_⟩
  have hc := hM.triple.chars
  have key : ∀ v : B.P, l v.1 = (chrW X.ν (B.τ v) (kap G V V' Z v.1) : ℂ) := by
    intro v
    by_cases hv : v.1 ∈ X.T
    · haveI := hM.fin.nontriv v.1
      obtain ⟨y, hy⟩ := exists_ne (0 : Rf.Pi v.1)
      obtain ⟨φ, hφ, e⟩ : y ∈ (SB _).map (Rf.p v.1) := by rw [hM.fin.onto]; trivial
      obtain ⟨φ', hφ', e'⟩ : y ∈ (SB _).map (Rf.p' v.1) := by rw [hM.fin.onto']; trivial
      have h := zeta_rel hM.triple.base hM.triple.geo hM₂.triple.geo (hM.fin.zeta v hv) (hM₂.fin.zeta v hv) hφ hφ'
        (e.trans e'.symm)
      rw [map_smul, h3 _ _ hφ, h4 _ _ hφ', e, e'] at h
      exact (smul_left_injective ℂ ((LinearEquiv.map_ne_zero_iff (ψ v.1)).2 hy) h).symm
    · have hw : splitPrime (B.τ v) ∉ above E (X.T : Set (Pl F)) := fun h => hv (by
        have h' : (splitPrime (B.τ v)).under (𝓞 F) ∈ (X.T : Set (Pl F)) := h
        rwa [splitPrime_under] at h')
      have hk := valuation_kap hM.triple.geo hM₂.triple.geo v
      have h1 := (GlobalTheory.T.splitPlaceCharacterComponent_smooth_unitary_conductor F E X.α hc.heckeα v.1 (B.τ v)).2.2.2 (hc.unrα _ hw) _ hk
      have h2 := (GlobalTheory.T.splitPlaceCharacterComponent_smooth_unitary_conductor F E X.β hc.heckeβ v.1 (B.τ v)).2.2.2 (hc.unrβ _ hw) _ hk
      have h0 : chrW X.ν (B.τ v) (kap G V V' Z v.1) =
          chrW X.α (B.τ v) (kap G V V' Z v.1) / chrW X.β (B.τ v) (kap G V V' Z v.1) := by
        simp only [Chars.ν, chrW, locChar, MonoidHom.comp_apply, MonoidHom.div_apply, map_div]
      rw [h5 _ hv, h0, h1, h2, div_one, Units.val_one]
  rw [chr_kapId, Finset.prod_subset hc.sub (fun v _ hv => h5 v hv), ← Finset.prod_coe_sort B.P l]
  exact Finset.prod_congr rfl fun v _ => key v

theorem acts_pureA {κ : Type} [Fintype κ] {T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ} {f f₁ : SInf F κ}
    (h : Acts (evI F) T f f₁) {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) : T (pureA F f g) = pureA F f₁ g := by
  refine h (fun x => g fun i => (x i).2) ⟨fun x z hz => ?_, Submodule.subset_span ⟨f, g, hg, rfl⟩⟩
  show g (fun i => (x i + z i).2) = g (fun i => (x i).2)
  congr 1
  funext i
  show (x i).2 + (z i).2 = (x i).2
  rw [GlobalTheory.RealLift.fin_eq_zero_of_at hz i, add_zero]

theorem pureA_smul {κ : Type} [Fintype κ] (c : ℂ) (f : SInf F κ) (g : (κ → Af F) → ℂ) :
    pureA F (⇑(c • f)) g = c • pureA F f g := by
  funext x
  simp only [pureA, SchwartzMap.smul_apply, smul_eq_mul, Pi.smul_apply, mul_assoc]

theorem const_eq (hP : GlobalTheory.FunPr.Hypotheses₂) (hK : ThetaIntegralsAgree) {R R₂ : RealMaps F a a'} {Rf S : FinMaps F a a'}
    (hM : IsMatched B G X om om' R Rf) (hM₂ : IsMatched B (reG G V V' Z) X om om' R₂ S)
    {g : UA σ G.V.J} (hg : g ∈ UAt σ G.V (evI F)) {g' : UA σ G.V'.J} (hg' : g' ∈ UAt σ G.V' (evI F))
    {h : UA σ G.W.J} (hh : h ∈ UAt σ G.W (evI F))
    (hθ : ∀ w, (mat g).map (piInf (B.emb w)) * G.V.θ w = V.θ w * (mat g).map (piInf (B.emb w)))
    (hθ' : ∀ w, (mat g').map (piInf (B.emb w)) * G.V'.θ w = V'.θ w * (mat g').map (piInf (B.emb w)))
    (hθW : ∀ w, (mat h).map (piInf (B.emb w)) * G.W.θ w = Z.θ w * (mat h).map (piInf (B.emb w)))
    {T : SInf F (Fin a × Fin (a + a')) ≃ₗ[ℂ] SInf F (Fin a × Fin (a + a'))}
    {T' : SInf F (Fin a' × Fin (a + a')) ≃ₗ[ℂ] SInf F (Fin a' × Fin (a + a'))} (hTc : Continuous T) (hTc' : Continuous T')
    (hT1 : ∀ f : SInf F (Fin a × Fin (a + a')), Acts (evI F) (om (g, h)) f (T f))
    (hT2 : ∀ f : SInf F (Fin a × Fin (a + a')), Acts (evI F) (om (g⁻¹, h⁻¹)) f (T.symm f))
    (hT1' : ∀ f : SInf F (Fin a' × Fin (a + a')), Acts (evI F) (om' (g', h)) f (T' f))
    (hT2' : ∀ f : SInf F (Fin a' × Fin (a + a')), Acts (evI F) (om' (g'⁻¹, h⁻¹)) f (T'.symm f))
    {ψ₀ : R.Pi ≃ₗ[ℂ] (reR R₂ T T').Pi} {l₀ : ℂ} (hl₀ : l₀ ≠ 0)
    (hR : ∀ f ∈ G.M.Pol B.ψ B.emb, (reR R₂ T T').p f = ψ₀ (R.p f))
    (hR' : ∀ f ∈ G.M'.Pol B.ψ B.emb, (reR R₂ T T').p' f = l₀ • ψ₀ (R.p' f))
    {c d : ℂ} (hc : IsConst B G X om om' R Rf c) (hd : IsConst B (reG G V V' Z) X om om' R₂ S d) :
    d = l₀ * X.ν (kapId B G V V' Z) * c := by
  obtain ⟨ψ, l, hl1, h3, h4, hl⟩ := fin_scalar hP hM hM₂
  obtain ⟨⟨-, hu, -⟩, -, hso⟩ := (hK.1 F E σ B a a' G X om om' hM.triple).2 R Rf hM
  have hT := hM.triple
  set Λ : ℂ := l₀ * X.ν (kapId B G V V' Z) with hΛ
  have hΛ0 : Λ ≠ 0 := mul_ne_zero hl₀ (Circle.coe_ne_zero _)
  have pm : ∀ Φ Φ', PolMatch B G X R Rf Φ Φ' →
      PolMatch B (reG G V V' Z) X R₂ S (om (g, h) (Λ • Φ)) (om' (g', h) Φ') := fun Φ Φ' hm => by
    have := polMatch_iso hl1 hR hR' h3 h4 hm
    rw [hl] at this
    exact polMatch_transport hT R₂ hg hg' hh hθ hθ' hθW hT1 hT2 hT1' hT2' S this
  have so : ∀ Φ' ∈ G.M'.So B.ψ B.τ₁, om' (g', h) Φ' ∈ (reG G V V' Z).M'.So B.ψ B.τ₁ := fun Φ' hΦ' =>
    (GlobalTheory.ThKRealConj.so_reG' G V V' Z B.ψ B.τ₁).symm ▸ hso (g', h) Φ' hΦ'
  have hc' : IsConst B G X om om' R Rf (d / Λ) := by
    rintro Φ Φ' ⟨hSo, m, m', r, f, s, r', f', s', hr, hr', hΦ, hΦ', hk⟩ y
    have e1 : ∀ u : Fin m → SInf F (Fin a × Fin (a + a')),
        om (g, h) (Λ • ∑ i, pureA F (u i) (r i)) = ∑ i, pureA F (⇑(Λ • T (u i))) (r i) := fun u => by
      rw [map_smul, map_sum, Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [acts_pureA (hT1 (u i)) (hr i).1, pureA_smul]
    have e2 : ∀ u : Fin m' → SInf F (Fin a' × Fin (a + a')),
        om' (g', h) (∑ i, pureA F (u i) (r' i)) = ∑ i, pureA F (T' (u i)) (r' i) := fun u => by
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => acts_pureA (hT1' (u i)) (hr' i).1
    have hm : Match B (reG G V V' Z) X R₂ S (om (g, h) (Λ • Φ)) (om' (g', h) Φ') := by
      refine ⟨so _ hSo, m, m', r, fun i => Λ • T (f i), fun k i => Λ • T (s k i), r', fun i => T' (f' i),
        fun k i => T' (s' k i), fun i => ⟨(hr i).1, ((hTc.tendsto _).comp (hr i).2).const_smul Λ⟩,
        fun i => ⟨(hr' i).1, (hTc'.tendsto _).comp (hr' i).2⟩, by rw [hΦ, e1], by rw [hΦ', e2], fun k => ?_⟩
      have h1 := so _ (hk k).1
      have h2 := pm _ _ (hk k).2
      rw [e2] at h1
      rw [e1, e2] at h2
      exact ⟨h1, h2⟩
    have sΦ : Λ • Φ ∈ schA F (Fin a × Fin (a + a')) := by
      rw [hΦ]
      exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨f i, r i, (hr i).1, rfl⟩)
    have sΦ' : Φ' ∈ schA F (Fin a' × Fin (a + a')) := by
      rw [hΦ']
      exact Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨f' i, r' i, (hr' i).1, rfl⟩
    have key := hd _ _ hm (y * h⁻¹)
    have i1 := GlobalTheory.T.theta_integral_archimedean_invariant hP F E σ B a (a + a') G.V G.W G.M _ _ om _ _ _ _ (GlobalTheory.ThK.RealUniq.isPair_V hT) g hg h _ sΦ
      (y * h⁻¹)
    have i2 := GlobalTheory.T.theta_integral_archimedean_invariant hP F E σ B a' (a + a') G.V' G.W G.M' _ _ om' _ _ _ _ (GlobalTheory.ThK.RealUniq.isPair_V' hT) g' hg' h _
      sΦ' (y * h⁻¹)
    rw [inv_mul_cancel_right] at i1 i2
    change G.M.I om (om (g, h) (Λ • Φ)) (y * h⁻¹) = d * G.M'.I om' (om' (g', h) Φ') (y * h⁻¹) at key
    rw [i1, i2, GlobalTheory.PolIso.modelI_smul] at key
    rw [div_mul_eq_mul_div, eq_div_iff hΛ0, ← key, mul_comm]
  rw [hu.unique hc hc']
  field_simp

theorem acts_congr {κ : Type} [Fintype κ] {T T₁ : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ} (e : ∀ Φ ∈ schA F κ, T Φ = T₁ Φ)
    {f f₁ : (κ → mixedEmbedding.mixedSpace F) → ℂ} (h : Acts (evI F) T f f₁) : Acts (evI F) T₁ f f₁ :=
  fun r hr => (e _ hr.2).symm.trans (h r hr)

theorem ratio_reG (hP : GlobalTheory.FunPr.Hypotheses₂) (hK : ThetaIntegralsAgree) {Xa Xb : Chars F E} {R R₂ : RealMaps F a a'}
    {oa ob : Rep σ G.V G.W} {oa' ob' : Rep σ G.V' G.W} {Ra Rb Sa Sb : FinMaps F a a'} {ca cb da db : ℂ}
    (m1 : IsMatched B G Xa oa oa' R Ra) (m2 : IsMatched B G Xb ob ob' R Rb)
    (n1 : IsMatched B (reG G V V' Z) Xa oa oa' R₂ Sa) (n2 : IsMatched B (reG G V V' Z) Xb ob ob' R₂ Sb)
    (k1 : IsConst B G Xa oa oa' R Ra ca) (k2 : IsConst B G Xb ob ob' R Rb cb)
    (l1 : IsConst B (reG G V V' Z) Xa oa oa' R₂ Sa da) (l2 : IsConst B (reG G V V' Z) Xb ob ob' R₂ Sb db) :
    ∃ k : (AE F E)ˣ, da * cb = ((Xa.ν k / Xb.ν k : Circle) : ℂ) * (db * ca) := by
  have ta := m1.triple
  have tb := m2.triple
  have hB := ta.base
  obtain ⟨g, hg, eg⟩ := GlobalTheory.T.cartan_involution_systems_conj_archimedean_unitary F E σ B a _ _ G.V V hB ta.geo.hV n1.triple.geo.hV
  obtain ⟨g', hg', eg'⟩ := GlobalTheory.T.cartan_involution_systems_conj_archimedean_unitary F E σ B a' _ _ G.V' V' hB ta.geo.hV' n1.triple.geo.hV'
  obtain ⟨h, hh, eh⟩ := GlobalTheory.T.skewHermitian_cartanInvolutionSystems_conjugate_archimedean F E σ B (a + a') _ _ G.W Z hB ta.geo.hW n1.triple.geo.hW
  obtain ⟨T, hTc, hT1, hT2⟩ := exists_op hB.std ta.weil hg hh
  obtain ⟨T', hTc', hT1', hT2'⟩ := exists_op hB.std ta.weil' hg' hh
  have hR₃ := realMaps_transport hP ta R₂ hg hg' hh eg eg' eh hT1 hT2 hT1' hT2' n1.triple n1.real
  obtain ⟨ψ₀, l₀, hl₀, hR, hR'⟩ := realMaps_unique hP F E σ B a a' G Xa oa oa' R Ra m1 _ hR₃
  have eα : ∀ z : (AE F E)ˣ, At (evI F) ((z : AE F E) - 1) → Xa.α z = Xb.α z := fun z hz =>
    Circle.ext ((ta.chars.expα z hz).trans (tb.chars.expα z hz).symm)
  have eβ : ∀ z : (AE F E)ˣ, At (evI F) ((z : AE F E) - 1) → Xa.β z = Xb.β z := fun z hz =>
    Circle.ext ((ta.chars.expβ z hz).trans (tb.chars.expβ z hz).symm)
  have eV := fun g hg h hh => weil_arch_eq (g := g) (k := h) hB.cm hB.std ta.geo.hV.herm
    (GlobalTheory.FinUniq.det_ne_zero_herm ta.geo.hV) ta.geo.hW.skew (GlobalTheory.FinUniq.det_ne_zero_skew ta.geo.hW) eβ
    (fun z hz => by rw [MonoidHom.div_apply, MonoidHom.div_apply, eα z hz, eβ z hz]) ta.weil tb.weil hg hh
  have eV' := fun g hg h hh => weil_arch_eq (g := g) (k := h) hB.cm hB.std ta.geo.hV'.herm
    (GlobalTheory.FinUniq.det_ne_zero_herm ta.geo.hV') ta.geo.hW.skew (GlobalTheory.FinUniq.det_ne_zero_skew ta.geo.hW) eα
    (fun z hz => by rw [MonoidHom.div_apply, MonoidHom.div_apply, eα z hz, eβ z hz]) ta.weil' tb.weil' hg hh
  have hhi := GlobalTheory.MajTransport.uat_inv hh
  have ha := const_eq hP hK m1 n1 hg hg' hh eg eg' eh hTc hTc' hT1 hT2 hT1' hT2' hl₀ hR hR' k1 l1
  have hb := const_eq hP hK m2 n2 hg hg' hh eg eg' eh hTc hTc' (fun f => acts_congr (eV g hg h hh) (hT1 f))
    (fun f => acts_congr (eV _ (GlobalTheory.MajTransport.uat_inv hg) _ hhi) (hT2 f))
    (fun f => acts_congr (eV' g' hg' h hh) (hT1' f))
    (fun f => acts_congr (eV' _ (GlobalTheory.MajTransport.uat_inv hg') _ hhi) (hT2' f)) hl₀ hR hR' k2 l2
  refine ⟨kapId B G V V' Z, ?_⟩
  have h0 : (Xb.ν (kapId B G V V' Z) : ℂ) ≠ 0 := Circle.coe_ne_zero _
  rw [ha, hb, Circle.coe_div]
  field_simp

end GlobalTheory.ReBase

end
