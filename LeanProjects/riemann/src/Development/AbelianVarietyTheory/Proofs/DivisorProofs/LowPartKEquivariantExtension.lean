import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KEqOnId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixPartEqBotOfLt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodMemDegLE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorIrreducibleModules
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanPolynomialTensorWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanThetaPolynomialLiftExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTensSpanOfKilled

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

open scoped Classical

open GlobalTheory.RealLift GlobalTheory.RealLift.Main Formalism.BasicNotions.TH GlobalTheory.KFixIrr

namespace GlobalTheory.DegKeep

theorem locFin_prod {V : Type} [AddCommGroup V] [Module ℂ V] {L : Module.End ℂ V} (h : LocFin L) :
    LocFin (L.prodMap L : Module.End ℂ (V × V)) := by
  rintro ⟨x, y⟩
  obtain ⟨N, fN, hx, sN⟩ := h x
  obtain ⟨N', fN', hy, sN'⟩ := h y
  refine ⟨N.map (LinearMap.inl ℂ V V) ⊔ N'.map (LinearMap.inr ℂ V V), inferInstance, ?_, ?_⟩
  · rw [← LinearMap.prod_eq_sup_map]; exact ⟨hx, hy⟩
  · rw [← LinearMap.prod_eq_sup_map]
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    exact ⟨sN a ha, sN' b hb⟩

theorem isExp_prod {V : Type} [AddCommGroup V] [Module ℂ V] {L U : Module.End ℂ V} (c : ℂ) (h : IsExp (c • L) U) :
    IsExp (c • (L.prodMap L : Module.End ℂ (V × V))) (U.prodMap U) := by
  rintro ⟨x, y⟩ l
  have hp : ∀ n : ℕ, ((c • (L.prodMap L : Module.End ℂ (V × V))) ^ n) (x, y) = (((c • L) ^ n) x, ((c • L) ^ n) y) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ', pow_succ', Module.End.mul_apply, ih]; simp
  have h1 := (h x (l ∘ₗ LinearMap.inl ℂ V V)).add (h y (l ∘ₗ LinearMap.inr ℂ V V))
  simp only [LinearMap.comp_apply, ← mul_add, ← map_add, LinearMap.inl_apply, LinearMap.inr_apply, Prod.mk_add_mk,
    add_zero, zero_add] at h1
  simp only [hp]
  exact h1

def graphOf {V Z : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup Z] [Module ℂ Z] (q : V →ₗ[ℂ] Z) (A : Z →ₗ[ℂ] Z) :
    Submodule ℂ (V × V) :=
  LinearMap.eqLocus (A ∘ₗ q ∘ₗ LinearMap.fst ℂ V V) (q ∘ₗ LinearMap.snd ℂ V V)

theorem mem_graphOf {V Z : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup Z] [Module ℂ Z] {q : V →ₗ[ℂ] Z} {A : Z →ₗ[ℂ] Z}
    {T T' : V} : (T, T') ∈ graphOf q A ↔ A (q T) = q T' := Iff.rfl

section Pair

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {B : Base F E}
  {n d P Q R S : ℕ} {X : Spc F E n} {W : Spc F E d} {om : Rep σ X W}
  {C : InfinitePlace F → Matrix (Fin d) (Formalism.BasicNotions.TH.Ix R S) ℂ} {Φ : Tens F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d)}
  {c : InfinitePlace F → ℂ}

set_option maxHeartbeats 1000000 in

theorem pair_skew (hcm : IsCMExt F E σ)
    (hC : ∀ w, IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) (C w))
    (hθ : ∀ w, W.θ w * C w = C w * Formalism.BasicNotions.TH.Jm R S)
    (hact : ActsBy B.emb C (om.comp (MonoidHom.inr _ _)) Φ (fockAct2 P Q R S) c)
    (hadm : ∀ g, ∀ l ∈ (adeleClass F).adm (Fin n × Fin d), l ∘ₗ om g ∈ (adeleClass F).adm (Fin n × Fin d))
    (N : Submodule ℂ (Tens F P Q R S × Tens F P Q R S)) (T T' : Tens F P Q R S) (hT : (T, T') ∈ N)
    (hN : ∀ k ∈ KInf σ W B.emb, ∀ T₁ T₁', Acts (evI F) (om (1, k)) (Φ T) (Φ T₁) → Acts (evI F) (om (1, k)) (Φ T') (Φ T₁') →
      (T₁, T₁') ∈ N) (w : InfinitePlace F) (Y : Mat R S) (hY : IsKC Y) (hYs : Yᴴ = -Y) :
    (actAt (fockAct2 P Q R S) w Y T, actAt (fockAct2 P Q R S) w Y T') ∈ N := by
  set L0 : Module.End ℂ (Tens F P Q R S) :=
    atPl (V := fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol P Q R S) w (fockAct2 P Q R S Y + (c w * Y.trace) • 1) with hL0
  set Ys : ℝ → InfinitePlace F → Mat R S := fun s w' => if w' = w then (s : ℂ) • Y else 0 with hYsdef
  have hYsKC : ∀ s w', IsKC (Ys s w') := by
    intro s w'; by_cases h : w' = w
    · simp only [hYsdef, if_pos h]; exact GlobalTheory.FockKStab.isKC_smul hY _
    · simp only [hYsdef, if_neg h]; exact GlobalTheory.FockKStab.isKC_zero R S
  have hYsU : ∀ s w', Ys s w' ∈ upq R S := by
    intro s w'; apply GlobalTheory.FockKStab.mem_upq (hYsKC s w'); by_cases h : w' = w
    · simp [hYsdef, h, Matrix.conjTranspose_smul, hYs]
    · simp [hYsdef, h]
  have hsum : ∀ s : ℝ, sumPl (V := fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol P Q R S)
      (fun w' => fockAct2 P Q R S (Ys s w') + (c w' * (Ys s w').trace) • 1) = (s : ℂ) • L0 := by
    intro s
    unfold sumPl
    rw [Finset.sum_eq_single w]
    · rw [hL0, ← atPl_smul]
      congr 1
      simp only [hYsdef, if_pos rfl, map_smul, Matrix.trace_smul, smul_add, smul_smul, smul_eq_mul]
      congr 2; ring
    · intro w' _ hw'; simp [hYsdef, hw', atPl_zero]
    · simp
  have hloc : ∀ s : ℝ, LocFin (sumPl (V := fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol P Q R S)
      (fun w' => fockAct2 P Q R S (Ys s w') + (c w' * (Ys s w').trace) • 1)) := fun s =>
    i_locfin _ _ _ (fun w' => locFin_fock2 P Q R S _ (hYsKC s w') _)
  have hexp : ∀ s : ℝ, ∃ U : Module.End ℂ (Tens F P Q R S × Tens F P Q R S),
      IsExp ((s : ℂ) • (L0.prodMap L0 : Module.End ℂ (Tens F P Q R S × Tens F P Q R S))) U ∧ U (T, T') ∈ N := by
    intro s
    obtain ⟨γ, hγ, hgen⟩ := i_lineex F E σ (Fin d) R S B.emb (incM F W.J) Complex.I C hcm hC (Ys s) (hYsU s)
    obtain ⟨U, hU, hSA⟩ := i_expact F (Fin n × Fin d) _ Φ _
      ((om.comp (MonoidHom.inr _ _)).comp γ) (hloc s) (fun t l hl => hadm _ l hl) (fun T => hact γ hγ (Ys s) hgen T)
    refine ⟨U.prodMap U, isExp_prod _ (hsum s ▸ hU), ?_⟩
    have h1 := (i_actslaws F _ (Φ T) (Φ (U T)) (Φ (U T))).2.1 _ (map_zero _) (hSA T)
    have h1' := (i_actslaws F _ (Φ T') (Φ (U T')) (Φ (U T'))).2.1 _ (map_zero _) (hSA T')
    have hk : γ (Multiplicative.ofAdd 1) ∈ KInf σ W B.emb := by
      refine ⟨hγ.2 _, fun w' => ?_⟩
      obtain ⟨A', hA'⟩ := (hC w').2
      exact GlobalTheory.FockKStab.commute_of_frame hA' (GlobalTheory.FockKStab.frame_inv (hC w') hA') (hgen 1 w') (hθ w')
        (Commute.exp_left (Commute.smul_left (GlobalTheory.FockKStab.commute_jm (hYsKC s w')) _))
    exact hN _ hk _ _ h1 h1'
  have hL0loc : LocFin L0 := by
    have := hloc 1
    rwa [hsum 1, Complex.ofReal_one, one_smul] at this
  have hmem := GlobalTheory.FockKStab.mem_of_exp _ (locFin_prod hL0loc) N (T, T') hexp
  have e : ∀ T, L0 T = actAt (fockAct2 P Q R S) w Y T + (c w * Y.trace) • T := fun T => by
    simp [hL0, atPl_add, atPl_smul, atPl_one, actAt_apply]
  have h2 := N.sub_mem hmem (N.smul_mem (c w * Y.trace) hT)
  rw [LinearMap.prodMap_apply, e, e] at h2
  simpa using h2

theorem pair_stable (hcm : IsCMExt F E σ)
    (hC : ∀ w, IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) (C w))
    (hθ : ∀ w, W.θ w * C w = C w * Formalism.BasicNotions.TH.Jm R S)
    (hact : ActsBy B.emb C (om.comp (MonoidHom.inr _ _)) Φ (fockAct2 P Q R S) c)
    (hadm : ∀ g, ∀ l ∈ (adeleClass F).adm (Fin n × Fin d), l ∘ₗ om g ∈ (adeleClass F).adm (Fin n × Fin d))
    (N : Submodule ℂ (Tens F P Q R S × Tens F P Q R S)) (T T' : Tens F P Q R S) (hT : (T, T') ∈ N)
    (hN : ∀ k ∈ KInf σ W B.emb, ∀ T₁ T₁', Acts (evI F) (om (1, k)) (Φ T) (Φ T₁) → Acts (evI F) (om (1, k)) (Φ T') (Φ T₁') →
      (T₁, T₁') ∈ N) (w : InfinitePlace F) (Z : Mat R S) (hZ : IsKC Z) :
    (actAt (fockAct2 P Q R S) w Z T, actAt (fockAct2 P Q R S) w Z T') ∈ N := by
  have key := pair_skew hcm hC hθ hact hadm N T T' hT hN w
  obtain ⟨Y1, hY1⟩ : ∃ Y1 : Mat R S, Y1 = (1 / 2 : ℂ) • (Z - Zᴴ) := ⟨_, rfl⟩
  obtain ⟨Y2, hY2⟩ : ∃ Y2 : Mat R S, Y2 = (1 / (2 * Complex.I)) • (Z + Zᴴ) := ⟨_, rfl⟩
  have hZ' : Z = Y1 + Complex.I • Y2 := by
    rw [hY1, hY2, smul_smul, show Complex.I * (1 / (2 * Complex.I)) = 1 / 2 by field_simp, ← smul_add]
    rw [show Z - Zᴴ + (Z + Zᴴ) = (2 : ℂ) • Z by rw [two_smul]; abel, smul_smul]; norm_num
  have hZh : IsKC Zᴴ := GlobalTheory.FockKStab.isKC_conjTranspose hZ
  have k1 : IsKC Y1 := hY1 ▸ GlobalTheory.FockKStab.isKC_smul (by
    rw [sub_eq_add_neg]; exact GlobalTheory.FockKStab.isKC_add hZ (by simpa using GlobalTheory.FockKStab.isKC_smul hZh (-1))) _
  have k2 : IsKC Y2 := hY2 ▸ GlobalTheory.FockKStab.isKC_smul (GlobalTheory.FockKStab.isKC_add hZ hZh) _
  have s1 : Y1ᴴ = -Y1 := by
    rw [hY1, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose]
    rw [show star (1 / 2 : ℂ) = 1 / 2 by simp, ← smul_neg, neg_sub]
  have s2 : Y2ᴴ = -Y2 := by
    rw [hY2, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose]
    rw [show star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) by simp, neg_smul, add_comm]
  have := N.add_mem (key Y1 k1 s1) (N.smul_mem Complex.I (key Y2 k2 s2))
  rw [hZ', map_add, map_smul]
  exact this

set_option maxHeartbeats 1000000 in

theorem kill_noncompact {M : Model σ X W} {A : InfinitePlace F → Matrix (Fin n) (Formalism.BasicNotions.TH.Ix P Q) ℂ} (hcm : IsCMExt F E σ)
    (hA : ∀ w, IsFrame ((1 : ℂ) • (incM F X.J).map (piInf (B.emb w))) (A w))
    (hact : ActsBy B.emb A (om.comp (MonoidHom.inl _ _)) Φ (fockAct1 P Q R S) c)
    (hr : LinearMap.range Φ = M.Pol B.ψ B.emb) {Z : Type} [AddCommGroup Z] [Module ℂ Z]
    {p : SInf F (Fin n × Fin d) →ₗ[ℂ] Z} (hp : RealQuot B M om p) (w : InfinitePlace F) (Y : Mat P Q) (hY : IsPC Y)
    (T : Tens F P Q R S) : p (Φ (actAt (fockAct1 P Q R S) w Y T)) = 0 := by
  have key : ∀ Y ∈ upq P Q, p (Φ (actAt (fockAct1 P Q R S) w Y T)) + (c w * Y.trace) • p (Φ T) = 0 := by
    intro Y hY
    set Ys : InfinitePlace F → Mat P Q := fun w' => if w' = w then Y else 0 with hYsdef
    have hYsU : ∀ w', Ys w' ∈ upq P Q := by
      intro w'; by_cases h : w' = w
      · simpa [hYsdef, h] using hY
      · simpa [hYsdef, h] using zero_mem_upq P Q
    obtain ⟨γ, hγ, hgen⟩ := i_lineex F E σ (Fin n) P Q B.emb (incM F X.J) 1 A hcm hA Ys hYsU
    have hsum : sumPl (V := fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol P Q R S)
        (fun w' => fockAct1 P Q R S (Ys w') + (c w' * (Ys w').trace) • 1) =
        actAt (fockAct1 P Q R S) w Y + (c w * Y.trace) • 1 := by
      unfold sumPl
      rw [Finset.sum_eq_single w]
      · simp [hYsdef, atPl_add, atPl_smul, atPl_one, actAt_apply]
      · intro w' _ hw'; simp [hYsdef, hw', atPl_zero]
      · simp
    have hsd := hact γ hγ Ys hgen T
    have h1 := (i_actslaws F _ (Φ T) _ (Φ T)).1 _ (fun t => map_zero _) hsd
    have h2 := hp.lie γ hγ (Φ T) (hr ▸ LinearMap.mem_range_self Φ T) _ h1
    rw [hsum] at h2
    simpa using h2
  obtain ⟨Y1, h1, Y2, h2, e⟩ := GlobalTheory.TensIrr.upq_decomp Y
  have ht : Y1.trace + Complex.I * Y2.trace = 0 := by
    have := GlobalTheory.HarmLift.trace_PC hY
    rwa [e, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul] at this
  have k1 := key Y1 h1
  have k2 := key Y2 h2
  rw [e, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, map_add, map_add, map_smul, map_smul,
    eq_neg_of_add_eq_zero_left k1, eq_neg_of_add_eq_zero_left k2, smul_neg, smul_smul, ← neg_add, ← add_smul,
    show c w * Y1.trace + Complex.I * (c w * Y2.trace) = c w * (Y1.trace + Complex.I * Y2.trace) by ring, ht]
  simp

end Pair

set_option maxHeartbeats 1000000 in

theorem map_lowPartInf_mem : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf →
      ∀ S : R.Pi →ₗ[ℂ] R.Pi, KEqOn B G.M om R.p (lowPartInf B G.M R.p) S →
        ∀ x ∈ lowPartInf B G.M R.p, S x ∈ lowPartInf B G.M R.p := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM S hS
  obtain ⟨hb, hg, hc, hw, hw'⟩ := hM.triple
  choose A hA hAθ using fun w => i_frameex _ _ _ _ _ (hg.hV.sig w) (hg.hV.cartan w)
  choose C hC hCθ using fun w => i_frameex _ _ _ _ _ (hg.hW.sig w) (hg.hW.cartan w)
  have hA1 : ∀ w, IsFrame ((1 : ℂ) • (incM F G.V.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [incM_map_piInf, one_smul]; exact hA w
  have hC1 : ∀ w, IsFrame (Complex.I • (incM F G.W.J).map (piInf (B.emb w))) (C w) := fun w => by
    rw [incM_map_piInf]; exact hC w
  have fr : Framed B.emb (incM F G.V.J) (incM F G.W.J) 1 Complex.I A C := ⟨one_mul _, hA1, hC1⟩
  have hvl := i_vacline i_derex
  have hfe := i_fockex i_derex
  have hsec := i_liesecond hKP.base i_derex hfe hvl (i_liescalar hKP.base i_derex hvl)
  have hfst := i_liefirst hsec
  obtain ⟨Φ, hΦ⟩ := hfe F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co 1 Complex.I A C hb.cm hb.std fr
  have hr := i_polrange i_actslaws i_derex hvl F E σ _ _ _ _ _ _ G.V G.W G.M B.ψ B.emb A C Φ hb.cm hb.std fr hAθ hCθ hΦ
  have hwp : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V.J) (incM F G.W.J) G.M.co X.β (X.β / X.α) om := hw
  have hW2 := hsec F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co 1 Complex.I A C Φ _ X.β B.mβ hb.cm hb.std fr hΦ hwp.1 hc.expβ
  obtain ⟨d, hd, hB1⟩ := hwp.2.1
  have hW1 := hfst F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co d 1 Complex.I A C Φ _ _ _ hb.cm hb.std fr hΦ hd hB1
    (hasExp_div B.emb hc.expβ hc.expα)
  have hadm := fun g => (hwp.isUSplitting).adm g
  have L1 := GlobalTheory.T.archimedean_theta_polynomial_lift_exists i_actslaws i_derex hvl F E σ _ _ _ _ _ _ G.V G.W G.M B.ψ B.emb A C Φ hb.cm hb.std fr hAθ hCθ hΦ
  have hpol : ∀ T, Φ T ∈ G.M.Pol B.ψ B.emb := fun T => hr ▸ LinearMap.mem_range_self Φ T
  have hq : Function.Surjective (R.p ∘ₗ Φ) := by
    rw [← LinearMap.range_eq_top, LinearMap.range_comp, hr]; exact hM.real.quot.onto
  have elow : lowPartInf B G.M R.p = (degLE (InfinitePlace F) _ _ _ _ (lowDegInf B G.M R.p)).map (R.p ∘ₗ Φ) := by
    rw [lowPartInf, L1, Submodule.map_comp]
  have main := map_mem_degLE (R.p ∘ₗ Φ) hq (fun w Y hY T => kill_noncompact hb.cm hA1 hW1 hr hM.real.quot w Y hY T)
    (fun w Y hY T hT => by
      have := pair_stable hb.cm hC1 hCθ hW2 hadm ((LinearMap.ker (R.p ∘ₗ Φ)).prod ⊤) T T ⟨hT, trivial⟩
        (fun k hk T₁ _ h _ => ⟨?_, trivial⟩) w Y hY
      · exact this.1
      · have h0 : Acts (evI F) (om' (1, k)) (0 : SInf F (Fin a' × Fin (a + a'))) (0 : SInf F (Fin a' × Fin (a + a'))) := by
          intro r _
          have : tens (evI F) (0 : SInf F (Fin a' × Fin (a + a'))) r = 0 := by funext x; simp [tens]
          rw [this, map_zero]
        have := hM.real.cpt k hk _ (hpol T) 0 (Submodule.zero_mem _) _ 0 h h0 (by rw [map_zero]; exact hT)
        rw [map_zero] at this
        exact this)
    (lowDegInf B G.M R.p) S (fun w Y hY T hT T' e => by
      have := pair_stable hb.cm hC1 hCθ hW2 hadm
        (graphOf (R.p ∘ₗ Φ) S) T T'
        (mem_graphOf.2 e) (fun k hk T₁ T₁' h h' => mem_graphOf.2
          (hS k hk _ (hpol T) _ h (elow ▸ ⟨T, hT, rfl⟩) _ (hpol T') _ h' e)) w Y hY
      exact mem_graphOf.1 this)
  rw [elow]
  rintro _ ⟨T, hT, rfl⟩
  exact main T hT

theorem map_mem_fockDeg_of_lie : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf →
      ∀ j : ℕ, ∀ S : R.Pi →ₗ[ℂ] R.Pi, KEqOn B G.M om R.p (lowPartInf B G.M R.p) S →
        (∀ x ∈ lowPartInf B G.M R.p, S x ∈ (fockDeg G.M B.ψ B.emb (lowDegInf B G.M R.p + 2 * j)).map R.p ⊔
          Submodule.span ℂ {x : R.Pi | ∃ γ ∈ Lines σ G.W, ∃ f ∈ fockDeg G.M B.ψ B.emb (lowDegInf B G.M R.p + 2 * j),
            ∃ f₁ : SInf F (Fin a × Fin (a + a')), ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ ∧ x = R.p f₁}) →
        ∀ x ∈ lowPartInf B G.M R.p, S x ∈ (fockDeg G.M B.ψ B.emb (lowDegInf B G.M R.p + 2 * j)).map R.p := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM j S hS _ x hx
  exact Submodule.map_mono (fockDeg_mono G.M B.ψ B.emb (Nat.le_add_right _ _))
    (map_lowPartInf_mem hKP F E σ B a a' G X om om' R Rf hM S hS x hx)

end GlobalTheory.DegKeep

end
