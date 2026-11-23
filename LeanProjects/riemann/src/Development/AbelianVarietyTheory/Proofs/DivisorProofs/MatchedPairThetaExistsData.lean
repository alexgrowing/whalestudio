import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleArchimedeanComponentsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SoTypeStableArchimedeanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleLocalActionAtSpecialPlaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactUnitaryPreservesPolynomialFockStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftLeftInvariant
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Matrix

noncomputable section

open scoped Classical

namespace GlobalTheory.ThKDataStab

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem det_ne_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let A' : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have h1 : A'ᵀ * M * A'.map star = (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm := by
    rw [← hA]; ext i j; simp [A', Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.map_apply]
  have h2 : (A'ᵀ * M * A'.map star).det ≠ 0 := by
    rw [h1, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
    simp [Matrix.det_neg]
  intro h0
  apply h2
  rw [Matrix.det_mul, Matrix.det_mul, h0]; simp

theorem det_ne_of_sig_map {n r s : ℕ} {J : Matrix (Fin n) (Fin n) E} (τ : E →+* ℂ) (c : ℂ)
    (h : HasSig (c • J.map τ) r s) : J.det ≠ 0 := by
  intro h0
  apply det_ne_of_hasSig h
  have e := RingHom.map_det τ J
  rw [RingHom.mapMatrix_apply] at e
  rw [Matrix.det_smul, ← e, h0, map_zero, mul_zero]

theorem evFin_eq_zero_of_atI {z : AF F} (hz : At (evI F) z) (v : Pl F) : evFin F v z = 0 := by
  let u : AF F := ((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F))
  have hu : evI F u = 0 := show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0 from map_zero _
  have h1 : evFin F v u = 1 := by
    show evalV F v (sndA F u) = 1
    have : sndA F u = 1 := rfl
    rw [this, map_one]
  have h0 : u • z = 0 := hz u hu
  have h2 := congrArg (evFin F v) h0
  rw [smul_eq_mul, map_mul, h1, one_mul, map_zero] at h2
  exact h2

theorem acts_pure {κ : Type} [Fintype κ] (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ) (f f₁ : SInf F κ)
    (hT : Acts (evI F) T f f₁) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) (hSB : ∀ v, φ v ∈ SB _)
    (hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) :
    T (pure f φ) = pure f₁ φ := by
  refine hT (fun x => ∏ᶠ v, φ v fun i => evFin F v (x i)) ⟨?_, ?_⟩
  · intro x z hz
    have hzi : ∀ i, At (evI F) (z i) := fun i u hu => congrFun (hz u hu) i
    simp only [Pi.add_apply, map_add, evFin_eq_zero_of_atI (hzi _), add_zero]
  · exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd

theorem one_mem_uAt {n : ℕ} (X : Spc F E n) {R : Type} [Zero R] (ev : AF F → R) : (1 : UA σ X.J) ∈ UAt σ X ev := by
  intro u _
  show u • (mat (1 : UA σ X.J) - 1) = 0
  have : mat (1 : UA σ X.J) = 1 := rfl
  rw [this, sub_self, smul_zero]

variable {a a' : ℕ}

theorem isPair' {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
    (hT : IsTriple B G X om om') :
    IsPair B G.M' X.α (X.α / X.β) om' G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) :=
  { base := hT.base, herm := hT.geo.hV', skew := hT.geo.hW, good := hT.geo.hM', hX := hT.chars.heckeα,
    hW := GlobalTheory.ThKRatInv.isHecke_div hT.chars.heckeα hT.chars.heckeβ, resX := hT.chars.resα,
    resW := by rw [add_comm a a']; exact GlobalTheory.ThKRatInv.resEtaPow_div hT.chars.resα hT.chars.resβ, weil := hT.weil' }

theorem so_fin (hK : KP) (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (hT : IsTriple B G X om om') (v : Pl F) (h : UA σ G.W.J) (hh : h ∈ UAt σ G.W (evFin F v))
    (Φ : Fn F a' (a + a')) (hΦ : Φ ∈ G.M'.So B.ψ B.τ₁) : om' (1, h) Φ ∈ G.M'.So B.ψ B.τ₁ := by
  have hP := isPair' hT
  have hA := GlobalTheory.T.theta_action_exists hK.base
  induction hΦ using Submodule.span_induction with
  | mem Ψ hΨ =>
    obtain ⟨f, φ, hSB, hev, hv₁, rfl⟩ := hΨ
    have hstd : ∀ᶠ w in Filter.cofinite, φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 :=
      (hev.and hP.good.std).mono fun w hw => hw.1.trans hw.2
    obtain ⟨φ₁, ⟨hφ₁, hact⟩, -⟩ :=
      (hA F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _ hP v).1 1 (one_mem_uAt G.V' _) h hh (φ v) (hSB v)
    obtain ⟨ρ, hρ, hρt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ hstd
    have hpure : tens (evFin F v) (φ v) ρ = pure f φ := by
      rw [hρt, Function.update_eq_self]
    have hRest : Rest (evFin F v) (φ v) ρ := ⟨hρ, by rw [hpure]; exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd⟩
    have hmap : om' (1, h) (pure f φ) = pure f (Function.update φ v φ₁) := by
      rw [← hpure, hact ρ hRest, hρt]
    rw [hmap]
    refine Submodule.subset_span ⟨f, Function.update φ v φ₁, fun w => ?_, ?_, ?_, rfl⟩
    · by_cases hw : w = v
      · subst hw; rw [Function.update_self]; exact hφ₁
      · rw [Function.update_of_ne hw]; exact hSB w
    · filter_upwards [hev, Filter.eventually_cofinite_ne v] with w hw hne
      rw [Function.update_of_ne hne]; exact hw
    · by_cases hv : B.v₁ = v
      · subst hv
        rw [Function.update_self]
        exact GlobalTheory.T.triple_local_action_at_special_place hK F E σ B a a' G X om om' hT h hh (φ B.v₁) hv₁ φ₁ hφ₁ hact
      · rw [Function.update_of_ne hv]; exact hv₁
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem polData_cpt (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (hT : IsTriple B G X om om') (k : UA σ G.W.J) (hk : k ∈ KInf σ G.W B.emb)
    (Φ : Fn F a' (a + a')) (hΦ : Φ ∈ PolData B G.M') : om' (1, k) Φ ∈ PolData B G.M' := by
  have hg := hT.geo
  have hc := hT.chars
  obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have dV' : G.V'.J.det ≠ 0 := det_ne_of_sig_map (B.emb w₀).1 1 (by rw [one_smul]; exact hg.hV'.sig w₀)
  have dW : G.W.J.det ≠ 0 := det_ne_of_sig_map (B.emb w₀).1 Complex.I (hg.hW.sig w₀)
  have hres := (isPair' hT).resW
  have hhk := (isPair' hT).hW
  have hCpt := GlobalTheory.T.compactUnitary_preserves_polynomialFock F E σ hT.base.cm a' (a + a') G.V' G.W G.M' B.ψ X.α (X.α / X.β) om' hT.base.std
    hg.hV'.herm dV' hg.hW.skew dW hc.resα hres hc.heckeα hhk hT.weil' B.emb hg.hV'.cartan hg.hW.cartan
  induction hΦ using Submodule.span_induction with
  | mem Ψ hΨ =>
    obtain ⟨f, hf, φ, hSB, hev, rfl⟩ := hΨ
    have hstd : ∀ᶠ w in Filter.cofinite, φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 :=
      (hev.and hg.hM'.std).mono fun w hw => hw.1.trans hw.2
    obtain ⟨f₁, hact⟩ := (hCpt k hk f hf).1
    rw [acts_pure (om' (1, k)) f f₁ hact φ hSB hstd]
    exact Submodule.subset_span ⟨f₁, (hCpt k hk f hf).2 f₁ hact, φ, hSB, hev, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

end GlobalTheory.ThKDataStab

namespace GlobalTheory.ThK

open GlobalTheory.ThKDataStab in

theorem polSo_stable : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → (∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, ∀ h ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ G.W (evFin F v), ∀ Φ ∈ (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), om' (1, h) Φ ∈ (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁)) ∧ ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ G.W B.emb, ∀ Φ ∈ (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), om' (1, k) Φ ∈ (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' R Rf hM
  have hT := hM.triple
  refine ⟨fun v h hh Φ hΦ => ?_, fun k hk Φ hΦ => ?_⟩
  · obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hΦ
    exact Submodule.mem_inf.2 ⟨GlobalTheory.T.matched_triple_archimedean_components hK F E σ B a a' G X om om' R Rf hM v h hh Φ h1,
      so_fin hK B G X om om' hT v h hh Φ h2⟩
  · obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hΦ
    exact Submodule.mem_inf.2 ⟨polData_cpt B G X om om' hT k hk Φ h1,
      GlobalTheory.T.so_type_stable_archimedean hK F E σ B a a' G X om om' hT 1 (one_mem_uAt G.V' _) k hk.1 Φ h2⟩

end GlobalTheory.ThK
