import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SameFns
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormalFormActualOperatorsAlgebraicHypothesesStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.RadialPairConstantsPointwiseAdjointBounded
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DoubleCosetOfZetaEq
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ProjRaisingProjEqSmul
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.VanishAbstract
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PairAtTAdjCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentLevelZeroEqOne

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
open scoped ComplexConjugate InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.HatNF.RaiseAdj

open Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB

section gen

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Q.Mx k r → (Wp →L[ℂ] Wp)} {π' : Q.Mx k r → (Wq →L[ℂ] Wq)}

def Van (c : Fin r → ℂ) (K : Set (Q.Mx k r)) (Φ : Q.RadSp k r z z' π π') : Prop :=
  ∀ g ∈ Q.Glev k r (Fin.last r), g ∉ K → (Φ : Q.Fn k r (Wq →L[ℂ] Wp)) c g = 0

theorem int_left {μ : Measure (Mt k r)} (hμ : B.IsHaarOn (Q.Glev k r (Fin.last r)) μ) {c : Fin r → ℂ}
    (hc : c ∈ OmX r) {K : Set (Q.Mx k r)} (hKc : IsCompact K) (hKG : K ⊆ {g | 0 < Q.GGl k r z z' g})
    (Φ Ψ : Q.RadSp k r z z' π π') (hΦ : Van c K Φ) :
    Integrable (fun x : Mt k r => B.hsInner ((Φ : Q.Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x))
      ((Ψ : Q.Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x))) μ := by
  simp only [hsInner_eq_sum]
  exact integrable_finsetSum _ fun m _ => int_cpt_gen μ hμ Φ Ψ c _ K hKc hKG hc _ (Or.inr rfl) hΦ

theorem int_right {μ : Measure (Mt k r)} (hμ : B.IsHaarOn (Q.Glev k r (Fin.last r)) μ) {c : Fin r → ℂ}
    (hc : c ∈ OmX r) {K : Set (Q.Mx k r)} (hKc : IsCompact K) (hKG : K ⊆ {g | 0 < Q.GGl k r z z' g})
    (Φ Ψ : Q.RadSp k r z z' π π') (hΨ : Van c K Ψ) :
    Integrable (fun x : Mt k r => B.hsInner ((Φ : Q.Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x))
      ((Ψ : Q.Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x))) μ := by
  simp only [hsInner_eq_sum]
  exact integrable_finsetSum _ fun m _ => int_cpt_gen μ hμ Ψ Φ c _ K hKc hKG hc _ (Or.inl rfl) hΨ

def adjSub {μ : Measure (Mt k r)} (hμ : B.IsHaarOn (Q.Glev k r (Fin.last r)) μ) {c : Fin r → ℂ}
    (hc : c ∈ OmX r) {K : Set (Q.Mx k r)} (hKc : IsCompact K) (hKG : K ⊆ {g | 0 < Q.GGl k r z z' g})
    (Φ Ψ : Q.RadSp k r z z' π π') (hΦ : Van c K Φ) (hΨ : Van c K Ψ) :
    Submodule ℂ (Q.Pr (Q.RadSp k r z z' π π')) where
  carrier := {b | pairAt μ (b.1 Φ) Ψ c = pairAt μ Φ ((star b).1 Ψ) c}
  zero_mem' := by
    show pairAt μ 0 Ψ c = pairAt μ Φ 0 c
    have h1 := pairAt_smul_left μ (0 : Q.RadSp k r z z' π π') Ψ c 0
    have h2 := pairAt_smul_right μ Φ (0 : Q.RadSp k r z z' π π') c 0
    simp only [zero_smul, zero_mul, map_zero] at h1 h2
    rw [h1, h2]
  add_mem' := by
    intro a b ha hb
    show pairAt μ (a.1 Φ + b.1 Φ) Ψ c = pairAt μ Φ ((star a).1 Ψ + (star b).1 Ψ) c
    have h1 := pairAt_add_smul_left μ (a.1 Φ) (b.1 Φ) Ψ c 1 (int_right hμ hc hKc hKG _ _ hΨ)
      (int_right hμ hc hKc hKG _ _ hΨ)
    have h2 := pairAt_add_smul_left μ ((star a).1 Ψ) ((star b).1 Ψ) Φ c 1 (int_right hμ hc hKc hKG _ _ hΦ)
      (int_right hμ hc hKc hKG _ _ hΦ)
    simp only [one_smul, one_mul] at h1 h2
    rw [h1, pairAt_swap μ _ Φ, h2, map_add, ← pairAt_swap, ← pairAt_swap]
    exact congrArg₂ _ ha hb
  smul_mem' := by
    intro s b hb
    show pairAt μ ((s • b).1 Φ) Ψ c = pairAt μ Φ ((star (s • b)).1 Ψ) c
    rw [star_smul, Formalism.FourierDecayAlt.P.NFx4.NO.fst_smul, Formalism.FourierDecayAlt.P.NFx4.NO.fst_smul, LinearMap.smul_apply, LinearMap.smul_apply,
      pairAt_smul_left, pairAt_smul_right]
    have hb' : pairAt μ (b.1 Φ) Ψ c = pairAt μ Φ ((star b).1 Ψ) c := hb
    rw [hb']
    simp

theorem exists_compact (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z')
    {S : Set ℂ} (hS : IsCompact S) (hS' : S ⊆ {ζ | Tz k r z * Tz k r z' < Complex.normSq ζ}) :
    ∃ K : Set (Q.Mx k r), IsCompact K ∧ K ⊆ {g | 0 < Q.GGl k r z z' g} ∧
      ∀ g ∈ Q.Glev k r (Fin.last r), g ∉ K → Q.zetaL k r z z' (Fin.last r) g ∉ S := by
  obtain ⟨ε, hε, h1⟩ := hS.exists_forall_le' (f := fun ζ => Complex.normSq ζ - Tz k r z * Tz k r z') (a := 0)
    (Complex.continuous_normSq.sub continuous_const).continuousOn (fun b hb => sub_pos.2 (hS' hb))
  obtain ⟨R, hR⟩ := hS.isBounded.exists_norm_le
  exact ⟨_, isCompact_zeta_le z z' hz hz' hT hT' ε R, fun g hg => lt_of_lt_of_le hε hg.2.1,
    fun g hg hgK h => hgK ⟨hg, h1 _ h, hR _ h⟩⟩

theorem van_mulZ {W : Module.End ℂ (Q.RadSp k r z z' π π')} {φ : ℂ → ℝ} (hW : NF.IsMulZ W fun ζ => (φ ζ : ℂ))
    {S : Set ℂ} (hS : tsupport φ ⊆ S) {K : Set (Q.Mx k r)}
    (hK : ∀ g ∈ Q.Glev k r (Fin.last r), g ∉ K → Q.zetaL k r z z' (Fin.last r) g ∉ S) (c : Fin r → ℂ)
    (Φ : Q.RadSp k r z z' π π') : Van c K (W Φ) := by
  intro g hg hgK
  rw [Formalism.FourierDecayAlt.P.NFx4.mulZ_apply hW, image_eq_zero_of_notMem_tsupport (fun h => hK g hg hgK (hS h))]
  simp

theorem contOn_hs (Φ Ψ : Q.RadSp k r z z' π π') (c : Fin r → ℂ) :
    ContinuousOn (fun g : Q.Mx k r => B.hsInner ((Φ : Q.Fn k r (Wq →L[ℂ] Wp)) c g)
      ((Ψ : Q.Fn k r (Wq →L[ℂ] Wp)) c g)) {g | (c, g) ∈ Q.DomR k r z z'} := by
  have hA : ∀ (Ξ : Q.RadSp k r z z' π π') (v : Wq), ContinuousOn
      (fun g : Q.Mx k r => (Ξ : Q.Fn k r (Wq →L[ℂ] Wp)) c g v) {g | (c, g) ∈ Q.DomR k r z z'} := by
    intro Ξ v
    have h1 := (radSp_continuousOn Ξ).comp
      ((continuous_const.prodMk continuous_id : Continuous fun g : Q.Mx k r => (c, g)).continuousOn :
        ContinuousOn _ {g | (c, g) ∈ Q.DomR k r z z'}) (fun x hx => hx)
    exact h1.clm_apply continuousOn_const
  simp only [hsInner_eq_sum]
  exact continuousOn_finsetSum _ fun m _ => (hA Ψ _).inner (hA Φ _)

end gen

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}
  {Bs : B.RealPlaceData P.k P.r Wp Wq}

theorem pairAt_of_ptAdj {b : RA P Bs} (hb : PtAdj P Bs b) (μ : Measure (Mt P.k P.r))
    (Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (c : Fin P.r → ℂ) :
    pairAt μ (b.1 Φ) Ψ c = pairAt μ Φ ((star b).1 Ψ) c := by
  unfold pairAt
  congr 1
  funext x
  by_cases hx : (c, Matrix.of x) ∈ Q.DomR P.k P.r Bs.z Bs.z'
  · exact hb Φ Ψ _ hx
  · rw [radSp_zero_off (b.1 Φ) hx, radSp_zero_off Φ hx, hsInner_zero_left, hsInner_zero_left]

theorem hs_inv (Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (c : Fin P.r → ℂ) (g g' : Q.Mx P.k P.r)
    (hg : (c, g) ∈ Q.DomR P.k P.r Bs.z Bs.z') (hg' : (c, g') ∈ Q.DomR P.k P.r Bs.z Bs.z')
    (hζ : P5.zeta P.k P.r Bs.z Bs.z' g = P5.zeta P.k P.r Bs.z Bs.z' g') :
    B.hsInner ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c g) ((Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c g) =
      B.hsInner ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c g') ((Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c g') := by
  obtain ⟨h, hh, h', hh', rfl⟩ := GlobalTheory.HatNF.doubleCoset_of_zeta_eq Wp Wq P Bs c g g' hg hg' hζ
  have e1 := Φ.2.2.2 (c, g) hg h hh h' hh'
  have e2 := Ψ.2.2.2 (c, g) hg h hh h' hh'
  simp only at e1 e2
  rw [e1, e2, Formalism.FourierDecayAlt.P.PBI.hsInner_comp_left _ (Bs.π_unitary _ hh),
    Formalism.FourierDecayAlt.P.PBI.hsInner_comp_right _ (Bs.π'_unitary _ hh')]

theorem triple (μ : Measure (Mt P.k P.r)) (c : Fin P.r → ℂ) (a t b : RA P Bs) (ha : PtAdj P Bs a)
    (hb : PtAdj P Bs b) (Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')
    (ht : pairAt μ (t.1 (b.1 Φ)) ((star a).1 Ψ) c = pairAt μ (b.1 Φ) ((star t).1 ((star a).1 Ψ)) c) :
    pairAt μ ((a * t * b).1 Φ) Ψ c = pairAt μ Φ ((star (a * t * b)).1 Ψ) c :=
  ((pairAt_of_ptAdj ha μ (t.1 (b.1 Φ)) Ψ c).trans ht).trans (pairAt_of_ptAdj hb μ Φ _ c)

theorem ptAdj_SS : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ l ∈ Finset.Icc 1 (P.k - 1), PtAdj P Bs (d.SS l) := by
  intro Wp Wq _ _ _ _ _ _ P Bs X μ L st l0 d hD hNF l hl
  have hP := hD.1
  have hμ := hD.2.1
  have hH := (GlobalTheory.T.normalForm_actualOperators_algebraicHypotheses Wp Wq P Bs X μ L st l0 d hD hNF).1
  have hκ := fun f => (GlobalTheory.HatNF.kappa_ptAdj_ptB Wp Wq P Bs X μ L st l0 d hD hNF f).1
  obtain ⟨co, hco⟩ := GlobalTheory.HatNF.RaiseFormula.ss_formula P _ d hH l hl Complex.I
    (fun ρ => Formalism.FourierDecayAlt.P.NFx4.SX.xC_ne ρ _ (by simp))

  have hmul : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → ∃ W : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'),
      NF.IsMulZ W (fun ζ => (φ ζ : ℂ)) ∧ (∀ g, Commute (d.κ g).1 W) ∧ Commute (d.SS l).1 W ∧
        Commute (star (d.SS l)).1 W := by
    intro φ hφ
    have hf : ContDiff ℝ ∞ (fun ζ => (φ ζ : ℂ)) := Complex.ofRealCLM.contDiff.comp hφ
    obtain ⟨W, hW⟩ := Formalism.FourierDecayAlt.P.multiplication_zeta_exists Wp Wq P _ _ _ _ hP _ hf.contDiffOn
    obtain ⟨W1, hW1⟩ := Formalism.FourierDecayAlt.P.multiplication_zeta_exists Wp Wq P _ _ _ _ hP _ (dZ_contDiff hf).contDiffOn
    obtain ⟨W2, hW2⟩ := Formalism.FourierDecayAlt.P.multiplication_zeta_exists Wp Wq P _ _ _ _ hP _ (dZb_contDiff hf).contDiffOn
    have h := Formalism.FourierDecayAlt.P.normal_form_order_zero Wp Wq P _ _ _ _ hP X d hNF.1 hNF.2.1 hNF.2.2.1 hNF.2.2.2 _
      hf.contDiffOn W W1 W2 hW hW1 hW2
    exact ⟨W, hW, h.1, (h.2.1 l hl).1, (h.2.1 l hl).2⟩
  rintro Φ Ψ ⟨c, g0⟩ hx
  have hc : c ∈ OmX P.r := hx.1
  have hO : IsOpen {ζ : ℂ | Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ} :=
    isOpen_lt continuous_const Complex.continuous_normSq
  obtain ⟨ψ, hψS, hψc, hψd, -, hψ1⟩ := exists_contDiff_tsupport_subset (n := ⊤)
    (x := P5.zeta P.k P.r Bs.z Bs.z' g0) (hO.mem_nhds (sub_pos.1 hx.2.2))
  obtain ⟨V, hV, hVκ, hVS, hVS'⟩ := hmul ψ hψd
  have key := GlobalTheory.HatNF.ZetaVanish.zeta_vanish Wp Wq P Bs μ c (fun g =>
    B.hsInner (((d.SS l).1 Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c g) ((V Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c g) -
    B.hsInner ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c g)
      (((star (d.SS l)).1 (V Ψ) : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c g)) hμ
    ((contOn_hs _ _ c).sub (contOn_hs _ _ c))
    (fun g g' hg hg' hζ => by rw [hs_inv _ _ c g g' hg hg' hζ, hs_inv Φ _ c g g' hg hg' hζ]) ?_ g0 hx
  · have e : (star (d.SS l)).1 (V Ψ) = V ((star (d.SS l)).1 Ψ) := LinearMap.congr_fun hVS'.eq Ψ
    rw [e, Formalism.FourierDecayAlt.P.NFx4.mulZ_apply hV, Formalism.FourierDecayAlt.P.NFx4.mulZ_apply hV] at key
    unfold P5.zeta at hψ1
    rw [hψ1, Complex.ofReal_one, one_smul, one_smul] at key
    exact sub_eq_zero.1 key
  intro φ hφd hφc hφS
  obtain ⟨W, hW, hWκ, hWS, hWS'⟩ := hmul φ hφd
  obtain ⟨K, hKc, hKG, hK⟩ := exists_compact Bs.z_mem Bs.z'_mem Bs.T_pos Bs.T'_pos
    (hφc.isCompact.union hψc.isCompact) (Set.union_subset hφS hψS)
  have vW := van_mulZ hW Set.subset_union_left hK c
  have vV := van_mulZ hV Set.subset_union_right hK c
  have hmem : d.SS l ∈ adjSub hμ hc hKc hKG (W Φ) (V Ψ) (vW Φ) (vV Ψ) := by
    rw [hco]
    refine Submodule.sum_mem _ fun ρ _ => Submodule.sum_mem _ fun ρ' _ => Submodule.smul_mem _ _ ?_
    rw [← hNF.2.2.2]
    refine triple μ c _ _ _ (hκ _) (hκ _) _ _ ?_
    refine pairAt_t_adj_cpt' P _ _ _ _ hP X μ hμ _ _ c hc ⟨K, hKc, hKG, fun g hg hgK => ⟨?_, ?_⟩⟩ Complex.I 1 0
    · have e := LinearMap.congr_fun (hWκ fun ρ' => if ρ' = ρ then 1 else 0).eq Φ
      simp only [Module.End.mul_apply] at e
      rw [e]
      exact vW _ g hg hgK
    · rw [hNF.2.2.1.1]
      have e := LinearMap.congr_fun (hVκ fun ρ => star (if ρ = ρ' then (1 : ℂ) else 0)).eq Ψ
      simp only [Module.End.mul_apply] at e
      rw [e]
      exact vV _ g hg hgK
  have hm : pairAt μ ((d.SS l).1 (W Φ)) (V Ψ) c = pairAt μ (W Φ) ((star (d.SS l)).1 (V Ψ)) c := hmem
  have e : (d.SS l).1 (W Φ) = W ((d.SS l).1 Φ) := LinearMap.congr_fun hWS.eq Φ
  rw [e] at hm
  have hs := integral_sub (int_left hμ hc hKc hKG (W ((d.SS l).1 Φ)) (V Ψ) (vW _))
    (int_left hμ hc hKc hKG (W Φ) ((star (d.SS l)).1 (V Ψ)) (vW _))
  unfold pairAt at hm
  rw [hm, sub_self] at hs
  rw [← hs]
  congr 1
  funext y
  rw [Formalism.FourierDecayAlt.P.NFx4.mulZ_apply hW, Formalism.FourierDecayAlt.P.NFx4.mulZ_apply hW, hsInner_smul_left', hsInner_smul_left', mul_sub]
  rfl

end GlobalTheory.HatNF.RaiseAdj
