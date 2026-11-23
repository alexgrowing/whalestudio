import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffPartLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchOperatorCompactUnitaryWStatement
import Formalism.LocalRingCardinality.DataTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdaptedFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBMatchedThetaLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowIrreducibleEigenspaceSup

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)
open GlobalTheory.RealLift Formalism.BasicNotions.TH GlobalTheory.FockBridge GlobalTheory.FockBottom

namespace GlobalTheory.FockTopA

section Poly

open MvPolynomial

theorem coeff_pderiv_eq {σ : Type} (s : σ) (γ : σ →₀ ℕ) (f : MvPolynomial σ ℂ) :
    coeff γ (pderiv s f) = ((γ s : ℂ) + 1) * coeff (γ + Finsupp.single s 1) f := by
  rw [coeff_pderiv, mul_comm]

theorem col_le {σ I K : Type} [Fintype I] [Fintype K] (e : I × K → σ) (he : Function.Injective e) (f : MvPolynomial σ ℂ)
    (k : ℕ) (c₀ : K) (hrow : ∀ α, coeff α f ≠ 0 → ∀ i, α (e (i, c₀)) ≤ k)
    (hE : ∀ i i', i ≠ i' → ∑ c, X (e (i, c)) * pderiv (e (i', c)) f = 0) (α₀ : σ →₀ ℕ) (hα₀ : coeff α₀ f ≠ 0) :
    ∑ i, α₀ (e (i, c₀)) ≤ k := by
  by_contra hlt
  push Not at hlt
  set n := ∑ i, α₀ (e (i, c₀)) with hn
  obtain ⟨i₀, -, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ) (f := fun i => α₀ (e (i, c₀))) (by omega)
  obtain ⟨α, hα, hmax⟩ := Finset.exists_max_image (f.support.filter fun γ => ∑ i, γ (e (i, c₀)) = n)
    (fun γ => γ (e (i₀, c₀))) ⟨α₀, by simp [hα₀, hn]⟩
  simp only [Finset.mem_filter, mem_support_iff] at hα hmax
  obtain ⟨i, hi, hi0⟩ : ∃ i, i ≠ i₀ ∧ α (e (i, c₀)) ≠ 0 := by
    by_contra hc
    push Not at hc
    have := hα.2
    rw [Finset.sum_eq_single i₀ (fun j _ hj => hc j hj) (by simp)] at this
    have := hrow α hα.1 i₀
    omega
  have hsg : ∀ (j j' : I) (c c' : K), (Finsupp.single (e (j, c)) 1 : σ →₀ ℕ) (e (j', c')) = if j = j' ∧ c = c' then 1 else 0 := by
    intro j j' c c'
    simp [Finsupp.single_apply, he.eq_iff]
  let δ : σ →₀ ℕ := α - Finsupp.single (e (i, c₀)) 1
  have hδ : δ + Finsupp.single (e (i, c₀)) 1 = α := by
    ext s
    by_cases hs : s = e (i, c₀)
    · subst hs; simp [δ]; omega
    · simp [δ, Finsupp.single_apply, Ne.symm hs]
  have h := congrArg (coeff (Finsupp.single (e (i₀, c₀)) 1 + δ)) (hE i₀ i hi.symm)
  rw [coeff_sum, coeff_zero, Finset.sum_eq_single c₀, coeff_X_mul, coeff_pderiv_eq, hδ] at h
  · refine hα.1 ((mul_eq_zero.1 h).resolve_left ?_)
    exact Nat.cast_add_one_ne_zero _
  · intro c _ hc
    rw [coeff_X_mul']
    split_ifs
    · rw [coeff_pderiv_eq]
      refine mul_eq_zero_of_right _ ?_
      by_contra h0
      have hv : ∀ j, (Finsupp.single (e (i₀, c₀)) 1 + δ - Finsupp.single (e (i₀, c)) 1 + Finsupp.single (e (i, c)) 1 : σ →₀ ℕ)
          (e (j, c₀)) = (if i₀ = j then 1 else 0) + δ (e (j, c₀)) := by
        intro j
        simp only [Finsupp.add_apply, Finsupp.tsub_apply, hsg, hc, and_false, if_false, and_true, Nat.sub_zero, add_zero]
      have hαv : ∀ j, α (e (j, c₀)) = δ (e (j, c₀)) + (if i = j then 1 else 0) := by
        intro j
        rw [← hδ, Finsupp.add_apply, hsg]; simp
      have h1 := hmax _ ⟨h0, by
        rw [← hα.2]
        simp only [hv, hαv, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
        ring⟩
      rw [hv, hαv, if_pos rfl, if_neg hi] at h1
      omega
    · rfl
  · simp

theorem omE_off {P Q R S : ℕ} {a b : Ix P Q} (hab : a ≠ b) (c : Ix R S) (f : Formalism.BasicNotions.TH.Pol P Q R S) :
    (linePos (a, c) = true → linePos (b, c) = true → omE (a, c) (b, c) f = X (a, c) * pderiv (b, c) f) ∧
    (linePos (a, c) = false → linePos (b, c) = false → (∀ α, coeff α f ≠ 0 → α (a, c) = 0) → omE (a, c) (b, c) f = 0) := by
  have hne : (a, c) ≠ (b, c) := fun h => hab (Prod.ext_iff.1 h).1
  refine ⟨fun h1 h2 => ?_, fun h1 h2 h0 => ?_⟩
  · simp [omE, raiB, lowB, h1, h2, hne]
  · have hd : pderiv (a, c) f = 0 := by
      ext γ
      rw [coeff_pderiv_eq, coeff_zero]
      refine mul_eq_zero_of_right _ ?_
      by_contra h
      simpa using h0 _ h
    simp [omE, raiB, lowB, h1, h2, hne, hd, pderiv_X_of_ne hne.symm]

theorem trace_Eab_off {P Q : ℕ} {a b : Ix P Q} (hab : a ≠ b) : (Eab a b : Mat P Q).trace = 0 := by
  simp [Eab, Matrix.trace_single_eq_of_ne _ _ _ hab]

theorem lowOne_le_top {P Q R S : ℕ} (x : ℚ) (k k' : ℕ) (hk : x - cPair R S = k) (hk' : x + cPair R S = k')
    (r : Fin R) (s : Fin S) : GlobalTheory.KFixIrr.lowOne P Q R S x (P * k + Q * k') ≤ ⨆ n : ℕ × ℕ,
      Module.End.eigenspace (fockAct2 P Q R S (Eab (.inl r) (.inl r))) (((P : ℂ) - Q) / 2 + k - n.1) ⊓
      Module.End.eigenspace (fockAct2 P Q R S (Eab (.inr s) (.inr s))) (-(((P : ℂ) - Q) / 2) + k' - n.2) := by
  intro f hf
  have hun := GlobalTheory.FockLowWt.support_unmixed x k k' hk hk' f hf
  rw [GlobalTheory.KFixIrr.mem_lowOne, GlobalTheory.KFixIrr.mem_chiOne] at hf
  have hval : ∀ α, coeff α f ≠ 0 → ∀ a : Ix P Q, GlobalTheory.FockLowDeg.cartanVal a α = (x : ℂ) := by
    intro α hα a
    have h := congrArg (coeff α) (hf.1 _ (GlobalTheory.FockLowDeg.isKC_Eab_diag a))
    rw [GlobalTheory.FockLowDeg.coeff_cartan, GlobalTheory.FockLowDeg.trace_Eab_diag, mul_one, coeff_smul, smul_eq_mul] at h
    exact mul_right_cancel₀ hα h
  have hkC : (x : ℂ) - ((R : ℂ) - S) / 2 = k := by
    have := congrArg (fun t : ℚ => (t : ℂ)) hk
    simpa [cPair] using this
  have hk'C : (x : ℂ) + ((R : ℂ) - S) / 2 = k' := by
    have := congrArg (fun t : ℚ => (t : ℂ)) hk'
    simpa [cPair] using this
  have hP : ∀ α, coeff α f ≠ 0 → ∀ i : Fin P, α (Sum.inl i, Sum.inl r) ≤ k := by
    intro α hα i
    have h := hval α hα (Sum.inl i)
    simp only [GlobalTheory.FockLowDeg.cartanVal, Fintype.sum_sum_type, lineSign, one_mul, neg_one_mul, (hun α hα).1,
      Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_const, Finset.card_univ, Nat.cast_zero, zero_add,
      Fintype.card_fin, nsmul_eq_mul] at h
    have e : ((∑ c : Fin R, α (Sum.inl i, Sum.inl c) : ℕ) : ℂ) = (k : ℂ) := by
      push_cast
      linear_combination h + hkC
    rw [← Nat.cast_injective e]
    exact Finset.single_le_sum (f := fun c => α (Sum.inl i, Sum.inl c)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)
  have hQ : ∀ α, coeff α f ≠ 0 → ∀ j : Fin Q, α (Sum.inr j, Sum.inr s) ≤ k' := by
    intro α hα j
    have h := hval α hα (Sum.inr j)
    simp only [GlobalTheory.FockLowDeg.cartanVal, Fintype.sum_sum_type, lineSign, one_mul, neg_one_mul, (hun α hα).2,
      Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_const, Finset.card_univ, Nat.cast_zero, zero_add,
      Fintype.card_fin, nsmul_eq_mul] at h
    have e : ((∑ c : Fin S, α (Sum.inr j, Sum.inr c) : ℕ) : ℂ) = (k' : ℂ) := by
      push_cast
      linear_combination h + hk'C
    rw [← Nat.cast_injective e]
    exact Finset.single_le_sum (f := fun c => α (Sum.inr j, Sum.inr c)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ s)
  have hoff : ∀ a b : Ix P Q, a ≠ b → sameBlock a b → ∑ c, omE (a, c) (b, c) f = 0 := by
    intro a b hab hs
    have := hf.1 _ (isKC_Eab hs)
    rwa [trace_Eab_off hab, mul_zero, zero_smul, fockAct1_Eab, LinearMap.sum_apply] at this
  have cP := col_le (fun p : Fin P × Fin R => ((Sum.inl p.1, Sum.inl p.2) : Ln P Q R S))
    (fun p p' h => by simpa [Prod.ext_iff] using h) f k r hP fun i i' hii => by
      have hne : (Sum.inl i : Ix P Q) ≠ Sum.inl i' := by simpa using hii
      have := hoff _ _ hne trivial
      rw [Fintype.sum_sum_type, Finset.sum_eq_zero (s := (Finset.univ : Finset (Fin S))) fun c _ =>
        (omE_off hne _ f).2 rfl rfl fun α hα => (hun α hα).1 i c, add_zero] at this
      rw [← this]
      exact Finset.sum_congr rfl fun c _ => ((omE_off hne _ f).1 rfl rfl).symm
  have cQ := col_le (fun p : Fin Q × Fin S => ((Sum.inr p.1, Sum.inr p.2) : Ln P Q R S))
    (fun p p' h => by simpa [Prod.ext_iff] using h) f k' s hQ fun i i' hii => by
      have hne : (Sum.inr i : Ix P Q) ≠ Sum.inr i' := by simpa using hii
      have := hoff _ _ hne trivial
      rw [Fintype.sum_sum_type, Finset.sum_eq_zero (s := (Finset.univ : Finset (Fin R))) fun c _ =>
        (omE_off hne _ f).2 rfl rfl fun α hα => (hun α hα).2 i c, zero_add] at this
      rw [← this]
      exact Finset.sum_congr rfl fun c _ => ((omE_off hne _ f).1 rfl rfl).symm
  rw [← MvPolynomial.support_sum_monomial_coeff f]
  refine Submodule.sum_mem _ fun α hα => ?_
  have hα' := mem_support_iff.mp hα
  have e : (monomial α (coeff α f) : Formalism.BasicNotions.TH.Pol P Q R S) = coeff α f • monomial α 1 := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [e]
  refine Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem
    (k - ∑ i : Fin P, α (Sum.inl i, Sum.inl r), k' - ∑ j : Fin Q, α (Sum.inr j, Sum.inr s)) ?_)
  have h := GlobalTheory.FockLowWt.monomial_mem_eig α (hun α hα').1 (hun α hα').2 r s
  have h1 := cP α hα'
  have h2 := cQ α hα'
  simp only at h1 h2
  rw [Nat.cast_sub h1, Nat.cast_sub h2]
  convert h using 3 <;> ring

end Poly

section Alg

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem top_of_sum (D₁ D₂ : Module.End ℂ V) (a b : ℂ) {v : V}
    (hv : v ∈ ⨆ n : ℕ × ℕ, D₁.eigenspace (a - n.1) ⊓ D₂.eigenspace (b - n.2)) (h0 : D₁ v + D₂ v = (a + b) • v) :
    D₁ v = a • v ∧ D₂ v = b • v := by
  have h := bottom_of_sum (a • 1 - D₁) (b • 1 - D₂) 0 (v := v) (SetLike.le_def.1 (iSup_mono fun n => ?_) hv) ?_
  · simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, neg_zero, zero_smul, sub_eq_zero] at h
    exact ⟨h.1.symm, h.2.symm⟩
  · rintro x ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff] at h1 ⊢
      rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, h1, ← sub_smul]
      congr 1; ring
    · rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff] at h2 ⊢
      rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, h2, ← sub_smul]
      congr 1; ring
  · simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    rw [sub_add_sub_comm, h0, add_smul, sub_self]

theorem eq_zero_of_above (D : Module.End ℂ V) (a : ℂ) {ι : Type} (f : ι → ℕ) (N : ι → Submodule ℂ V)
    (hN : ∀ i, N i ≤ D.eigenspace (a - f i)) {v : V} (hv : v ∈ ⨆ i, N i) (h : D v = (a + 1) • v) : v = 0 := by
  refine eq_zero_of_below (-D) (-a) f N (fun i x hx => ?_) hv ?_
  · have := Module.End.mem_eigenspace_iff.1 (hN i hx)
    rw [Module.End.mem_eigenspace_iff, LinearMap.neg_apply, this, ← neg_smul]
    congr 1; ring
  · rw [LinearMap.neg_apply, h, ← neg_smul]
    congr 1; ring

end Alg

section Weights

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {B : Base F E}
  {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} {Rm : RealMaps F a a'}
  {Rf : FinMaps F a a'} {A : InfinitePlace F → Matrix (Fin a) (Ix (a - G.p) G.p) ℂ}
  {C : InfinitePlace F → Matrix (Fin (a + a')) (Ix (a + a' - (G.p + G.q)) (G.p + G.q)) ℂ}
  {Φ : Tens F (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) →ₗ[ℂ] SInf F (Fin a × Fin (a + a'))}

open GlobalTheory.KFixIrr in

theorem top_weights (hKP : KP) (hM : IsMatched B G X om om' Rm Rf) (hD : IsFockData B G.M A C Φ) :
    ∃ x₁ y₁ : InfinitePlace F → ℂ, (∀ w, x₁ w + y₁ w = (B.mα w : ℂ) - B.mβ w) ∧
    ∀ (w : InfinitePlace F) (r : Fin (a + a' - (G.p + G.q))) (s : Fin (G.p + G.q)),
    lowPartInf B G.M Rm.p ≤ ⨆ n : ℕ × ℕ,
      (fockOp (Rm.p ∘ₗ Φ) w (Eab (.inl r) (.inl r))).eigenspace (x₁ w - n.1) ⊓
      (fockOp (Rm.p ∘ₗ Φ) w (Eab (.inr s) (.inr s))).eigenspace (y₁ w - n.2) := by
  obtain ⟨hb, hg, hc, hw, hw'⟩ := hM.triple
  have hwp : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V.J) (incM F G.W.J) G.M.co X.β (X.β / X.α) om := hw
  obtain ⟨d, hd, hB1⟩ := hwp.2.1
  have hW1 := Main.i_liefirst (lieSecond hKP) F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co d 1 Complex.I A C Φ _ _ _ hb.cm hb.std
    hD.1.1 hD.2 hd hB1 (Main.hasExp_div B.emb hc.expβ hc.expα)
  let c : InfinitePlace F → ℚ := fun w => ((B.mα w - B.mβ w : ℤ) : ℚ) / 2
  have ec : (fun w => -((c w : ℚ) : ℂ)) = fun w => ((B.mβ w - B.mα w : ℤ) : ℂ) / 2 := by
    funext w; simp only [c]; push_cast; ring
  have hW1' : ActsBy B.emb A (om.comp (MonoidHom.inl _ _)) Φ (fockAct1 _ _ _ _) (fun w => -((c w : ℚ) : ℂ)) := by
    rw [ec]; exact hW1
  have hinj : Function.Injective Φ := hD.2.1
  have L1 := GlobalTheory.T.archimedean_theta_polynomial_lift_exists Main.i_actslaws Main.i_derex (Main.i_vacline Main.i_derex) F E σ _ _ _ _ _ _ G.V G.W G.M B.ψ B.emb
    A C Φ hb.cm hb.std hD.1.1 hD.1.2.1 hD.1.2.2 hD.2
  have L2 := GlobalTheory.T.archimedean_polynomial_tensor_character Main.i_actslaws Main.i_lineex (Main.i_kline Main.i_lineex) F E σ B _ _ _ _ _ _ G.V G.W om A Φ c
    hb.cm hD.1.1.2.1 hD.1.2.1 hinj hW1' (admissible_weil_action hM.triple)
  have key : ∀ k, fixPart B G.M om k = (chiPart (InfinitePlace F) _ _ _ _ c ⊓ degLE (InfinitePlace F) _ _ _ _ k).map Φ := by
    intro k
    have hs : {f | f ∈ fockDeg G.M B.ψ B.emb k ∧ IsKFix B om f} =
        Φ '' ((chiPart (InfinitePlace F) (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) c ⊓
          degLE (InfinitePlace F) (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) k : Submodule ℂ _) : Set _) := by
      ext f
      constructor
      · rintro ⟨hf, hfix⟩
        rw [L1 k] at hf
        obtain ⟨T, hT, rfl⟩ := hf
        exact ⟨T, ⟨(L2 T).1 hfix, hT⟩, rfl⟩
      · rintro ⟨T, ⟨h1, h2⟩, rfl⟩
        exact ⟨by rw [L1 k]; exact ⟨T, h2, rfl⟩, (L2 T).2 h1⟩
    rw [fixPart, hs, Submodule.span_image, Submodule.span_eq]
  have bot : ∀ k < fixDeg B G.M om, chiPart (InfinitePlace F) (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) c ⊓
      degLE (InfinitePlace F) _ _ _ _ k = ⊥ := by
    intro k hk
    have h0 := fixPart_eq_bot_of_lt B G.M om hk
    rw [key] at h0
    rw [← Submodule.comap_map_eq_of_injective hinj (_ ⊓ _), h0, Submodule.comap_bot, LinearMap.ker_eq_bot.2 hinj]
  have hPR : a - G.p ≤ a + a' - (G.p + G.q) := by have := hg.aBig; omega
  have hQS : G.p ≤ G.p + G.q := Nat.le_add_right _ _
  have hnum : ∀ w, ∃ k k' : ℕ, 0 < k ∧ 0 < k' ∧ c w - cPair (a + a' - (G.p + G.q)) (G.p + G.q) = k ∧
      c w + cPair (a + a' - (G.p + G.q)) (G.p + G.q) = k' := by
    intro w
    have hk := hg.kappa w
    obtain ⟨j, hj⟩ := Main.i_parity F E σ B a a' G X om om' hM.triple w
    obtain ⟨i, hi⟩ := hg.even
    have h1 := hg.eBig
    have h2 := hg.aBig
    have hle : G.p + G.q ≤ a + a' := by omega
    have hR : ((a + a' - (G.p + G.q) : ℕ) : ℚ) = (i : ℚ) + i - ((G.p : ℚ) + G.q) := by
      rw [Nat.cast_sub hle, hi]; push_cast; ring
    refine ⟨(j - i + (G.p + G.q : ℕ)).toNat, (j + i - (G.p + G.q : ℕ)).toNat, by omega, by omega, ?_, ?_⟩
    · rw [show (((j - i + (G.p + G.q : ℕ)).toNat : ℕ) : ℚ) = ((j - i + (G.p + G.q : ℕ) : ℤ) : ℚ) from by
        exact_mod_cast Int.toNat_of_nonneg (by omega)]
      simp only [c, cPair, hj, hR]; push_cast; ring
    · rw [show (((j + i - (G.p + G.q : ℕ)).toNat : ℕ) : ℚ) = ((j + i - (G.p + G.q : ℕ) : ℤ) : ℚ) from by
        exact_mod_cast Int.toNat_of_nonneg (by omega)]
      simp only [c, cPair, hj, hR]; push_cast; ring
  choose k k' hk hk' ek ek' using hnum
  refine ⟨fun w => (((a - G.p : ℕ) : ℂ) - G.p) / 2 + k w, fun w => -((((a - G.p : ℕ) : ℂ) - G.p) / 2) + k' w,
    fun w => ?_, fun w r s => ?_⟩
  · have h : ((k w : ℚ) + k' w) = (B.mα w : ℚ) - B.mβ w := by
      rw [← ek, ← ek']; simp only [c]; push_cast; ring
    have h' : ((k w : ℂ) + k' w) = (B.mα w : ℂ) - B.mβ w := by exact_mod_cast h
    linear_combination h'
  have hdeg := GlobalTheory.T.low_degree_le_fixed_degree hKP F E σ B a a' G X om om' Rm Rf hM
  refine (GlobalTheory.T.low_part_le_fixed_part_image hKP F E σ B a a' G X om om' Rm Rf hM).trans ?_
  rw [key, ← Submodule.map_comp, Submodule.map_le_iff_le_comap]
  refine (chi_le_tensSpan c hPR hQS k k' hk hk' ek ek' _ fun m' hm' => bot m' (hm'.trans_le hdeg)).trans ?_
  rw [tensSpan, Submodule.span_le]
  rintro _ ⟨g, hg', rfl⟩
  have hwt := lowOne_le_top (c w) (k w) (k' w) (ek w) (ek' w) r s (hg' w)
  let ℓ := (Rm.p ∘ₗ Φ) ∘ₗ (PiTensorProduct.tprod ℂ).toLinearMap g w
  have hℓ : ∀ Z f, fockOp (Rm.p ∘ₗ Φ) w Z (ℓ f) = ℓ (fockAct2 _ _ _ _ Z f) := fun Z f => by
    simp only [ℓ, LinearMap.comp_apply _ ((PiTensorProduct.tprod ℂ).toLinearMap g w), MultilinearMap.toLinearMap_apply]
    rw [fockOp_apply (surj_q hM hD) (keeps_q hKP hM hD w), GlobalTheory.TensIrr.atPl_tprod]
    simp
  have e : (Rm.p ∘ₗ Φ) (PiTensorProduct.tprod ℂ g) = ℓ (g w) := by simp [ℓ]
  rw [SetLike.mem_coe, Submodule.mem_comap, e]
  have h2 := Submodule.mem_map_of_mem (f := ℓ) hwt
  rw [Submodule.map_iSup] at h2
  refine SetLike.le_def.1 (iSup_mono fun n => ?_) h2
  rintro _ ⟨f, ⟨h1, h2⟩, rfl⟩
  refine ⟨?_, ?_⟩
  · rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff] at h1 ⊢
    rw [hℓ, h1, map_smul]
  · rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff] at h2 ⊢
    rw [hℓ, h2, map_smul]

end Weights

theorem eab_lie_up {R S : ℕ} {a b : Ix R S} (h : b ≠ a) : Eab a a * Eab a b - Eab a b * Eab a a = Eab a b := by
  simp [Eab, Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne _ _ _ _ h]

theorem _root_.GlobalTheory.T.configuration_a_global_zeta_identity : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b)
    (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F (b + 2) a') (Rf : FinMaps F (b + 2) a')
      (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W) (R₁ : RealMaps F b a') (Rf₁ : FinMaps F b a'),
      IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      ∀ (A : InfinitePlace F → Matrix (Fin (b + 2)) (Formalism.BasicNotions.TH.Ix (b + 2 - G.p) G.p) ℂ) (C : InfinitePlace F → Matrix (Fin (b + 2 + a')) (Formalism.BasicNotions.TH.Ix (b + 2 + a' - (G.p + G.q)) (G.p + G.q)) ℂ) (r₀ : Fin (b + 2 + a' - (G.p + G.q))) (s₀ : Fin (G.p + G.q)) (Φ : GlobalTheory.RealLift.Tens F (b + 2 - G.p) G.p (b + 2 + a' - (G.p + G.q)) (G.p + G.q) →ₗ[ℂ] SInf F (Fin (b + 2) × Fin (b + 2 + a'))), IsFockData B G.M A C Φ → IsAdaptedFrame B H' C r₀ s₀ →
      ∃ c c' : InfinitePlace F → ℂ, (∀ v, v ∈ twPart B G.M om R.p G₁.W H' X.α ((a' : ℝ) / 2) (lowPartInf B G.M R.p) ↔ v ∈ lowPartInf B G.M R.p ∧
        ∀ w, fockOp (R.p ∘ₗ Φ) w (Formalism.BasicNotions.TH.Eab (.inl r₀) (.inl r₀)) v = c w • v ∧ fockOp (R.p ∘ₗ Φ) w (Formalism.BasicNotions.TH.Eab (.inr s₀) (.inr s₀)) v = c' w • v) ∧
      ((∀ v ∈ twPart B G.M om R.p G₁.W H' X.α ((a' : ℝ) / 2) (lowPartInf B G.M R.p), ∀ w, (∀ i, i ≠ r₀ → fockOp (R.p ∘ₗ Φ) w (Formalism.BasicNotions.TH.Eab (.inl r₀) (.inl i)) v = 0) ∧
        ∀ j, j ≠ s₀ → fockOp (R.p ∘ₗ Φ) w (Formalism.BasicNotions.TH.Eab (.inr s₀) (.inr j)) v = 0) ∨
      (∀ v ∈ twPart B G.M om R.p G₁.W H' X.α ((a' : ℝ) / 2) (lowPartInf B G.M R.p), ∀ w, (∀ i, i ≠ r₀ → fockOp (R.p ∘ₗ Φ) w (Formalism.BasicNotions.TH.Eab (.inl i) (.inl r₀)) v = 0) ∧
        ∀ j, j ≠ s₀ → fockOp (R.p ∘ₗ Φ) w (Formalism.BasicNotions.TH.Eab (.inr j) (.inr s₀)) v = 0)) := by
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' hCfg X om om' Rm Rf om₁ om₁' R₁ Rf₁ hM hM₁ A C r₀ s₀ Φ hD hAd
  have hb := hM.triple.base
  have hg := hM.triple.geo
  have hg₁ := hM₁.triple.geo
  have hq := surj_q hM hD
  have hK := keeps_q hKP hM hD
  obtain ⟨x₁, y₁, hxy, hwt⟩ := top_weights hKP hM hD
  set q := Rm.p ∘ₗ Φ with hqdef
  have htw : ∀ v, v ∈ twPart B G.M om Rm.p G₁.W H' X.α ((a' : ℝ) / 2) (lowPartInf B G.M Rm.p) ↔ v ∈ lowPartInf B G.M Rm.p ∧
      ∀ w, fockOp q w (Eab (.inl r₀) (.inl r₀)) v = x₁ w • v ∧ fockOp q w (Eab (.inr s₀) (.inr s₀)) v = y₁ w • v := by
    have hs : {x | x ∈ lowPartInf B G.M Rm.p ∧ IsTwEig B G.M om Rm.p G₁.W H' X.α ((a' : ℝ) / 2) x} =
        ((lowPartInf B G.M Rm.p ⊓ ⨅ w, (fockOp q w (cen r₀ s₀)).eigenspace (x₁ w + y₁ w) : Submodule ℂ Rm.Pi) : Set Rm.Pi) := by
      ext x
      simp only [Set.mem_setOf_eq, SetLike.mem_coe, Submodule.mem_inf, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
      rw [isTwEig_iff hb hg.hW hg₁.hW hCfg.hH' hD.1.1.2.2 hD.1.2.2 hAd (actsBy_second hKP hM.triple hD) (admissible_weil_action hM.triple)
        (range_eq hM.triple hD) hq hK hM.triple.chars.expα]
      simp only [mul_div_cancel₀ _ (two_ne_zero (α := ℂ)), hxy]
      rfl
    intro v
    rw [twPart, hs, Submodule.span_eq]
    simp only [Submodule.mem_inf, Submodule.mem_iInf, Module.End.mem_eigenspace_iff, cen, map_add, LinearMap.add_apply]
    refine and_congr_right fun hv => forall_congr' fun w => ⟨fun h => ?_, fun h => ?_⟩
    · exact top_of_sum _ _ _ _ (hwt w r₀ s₀ hv) h
    · rw [h.1, h.2, add_smul]
  have hup : ∀ w (i j : Ix _ _) (μ : ℂ) (v : Rm.Pi), j ≠ i → fockOp q w (Eab i i) v = μ • v →
      fockOp q w (Eab i i) (fockOp q w (Eab i j) v) = (μ + 1) • fockOp q w (Eab i j) v := by
    intro w i j μ v hji hv
    have := LinearMap.congr_fun (fockOp_lie hq (hK w) (Eab i i) (Eab i j)) v
    rw [eab_lie_up hji, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, hv,
      map_smul, eq_sub_iff_add_eq] at this
    rw [← this, add_smul, one_smul]
    exact add_comm _ _
  refine ⟨x₁, y₁, htw, Or.inl fun v hv w => ⟨fun i hi => ?_, fun j hj => ?_⟩⟩
  · obtain ⟨hv1, hv2⟩ := (htw v).1 hv
    exact eq_zero_of_above _ (x₁ w) Prod.fst _ (fun _ => inf_le_left)
      (hwt w r₀ s₀ (low_stab hKP hM hD w _ (isKC_Eab (by trivial)) hv1))
      (hup w _ _ _ v (by simpa using hi) (hv2 w).1)
  · obtain ⟨hv1, hv2⟩ := (htw v).1 hv
    exact eq_zero_of_above _ (y₁ w) Prod.snd _ (fun _ => inf_le_right)
      (hwt w r₀ s₀ (low_stab hKP hM hD w _ (isKC_Eab (by trivial)) hv1))
      (hup w _ _ _ v (by simpa using hj) (hv2 w).2)

end GlobalTheory.FockTopA

end
