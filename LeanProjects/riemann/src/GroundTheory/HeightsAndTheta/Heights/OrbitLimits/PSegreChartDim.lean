import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSegreChartDim
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsSmoothMetricOfIsSmoothHerm
import ReciprocityTheory.AnalyticForms.RegularLocalRings.ConeChart
import ReciprocityTheory.AnalyticForms.RegularLocalRings.BaseChangeC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgDim
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar mcPts segre)

namespace SegreChartDim

theorem minimalPrimes_transfer {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (g : B →+* A)
    (I : Ideal A) (I' : Ideal B) (hf : I ≤ I'.comap f) (hg : I' ≤ I.comap g)
    (hgf : ∀ a, g (f a) - a ∈ I) (hfg : ∀ b, f (g b) - b ∈ I') (J : Ideal A) (hJ : J ∈ I.minimalPrimes) :
    J.comap g ∈ I'.minimalPrimes ∧ ringKrullDim (A ⧸ J) = ringKrullDim (B ⧸ J.comap g) := by
  have hJp : J.IsPrime := hJ.1.1
  have hIJ : I ≤ J := hJ.1.2
  have hfJ : ∀ a ∈ J, f a ∈ J.comap g := fun a ha => by
    rw [Ideal.mem_comap]
    have := hIJ (hgf a)
    simpa using J.add_mem this ha
  refine ⟨⟨⟨Ideal.comap_isPrime g J, fun b hb => hIJ (hg hb)⟩, fun Z ⟨hZp, hIZ⟩ hZJ => ?_⟩, ?_⟩
  · have hle : Z.comap f ≤ J := fun a ha => by
      have h1 : g (f a) ∈ J := hZJ ha
      have := J.sub_mem h1 (hIJ (hgf a))
      simpa using this
    have hJZ := hJ.2 ⟨Ideal.comap_isPrime f Z, fun a ha => hIZ (hf ha)⟩ hle
    intro b hb
    have h1 : f (g b) ∈ Z := hJZ hb
    have := Z.sub_mem h1 (hIZ (hfg b))
    simpa using this
  · let φ : A ⧸ J →+* B ⧸ J.comap g :=
      Ideal.Quotient.lift J ((Ideal.Quotient.mk _).comp f) fun a ha =>
        Ideal.Quotient.eq_zero_iff_mem.mpr (hfJ a ha)
    let ψ : B ⧸ J.comap g →+* A ⧸ J :=
      Ideal.Quotient.lift _ ((Ideal.Quotient.mk J).comp g) fun b hb =>
        Ideal.Quotient.eq_zero_iff_mem.mpr hb
    refine ringKrullDim_eq_of_ringEquiv (RingEquiv.ofRingHom φ ψ ?_ ?_)
    · refine Ideal.Quotient.ringHom_ext (RingHom.ext fun b => ?_)
      show Ideal.Quotient.mk (J.comap g) (f (g b)) = Ideal.Quotient.mk (J.comap g) b
      exact Ideal.Quotient.eq.mpr (hIJ (hg (hfg b)))
    · refine Ideal.Quotient.ringHom_ext (RingHom.ext fun a => ?_)
      show Ideal.Quotient.mk J (g (f a)) = Ideal.Quotient.mk J a
      exact Ideal.Quotient.eq.mpr (hIJ (hgf a))

theorem ringKrullDim_le_of_mem_minimalPrimes_sup_span {F : Type} [Field F] {τ : Type} [Fintype τ]
    (s : Finset (MvPolynomial τ F)) :
    ∀ (V W : Ideal (MvPolynomial τ F)), V.IsPrime → W ∈ (V ⊔ Ideal.span (s : Set (MvPolynomial τ F))).minimalPrimes →
      ringKrullDim (MvPolynomial τ F ⧸ V) ≤ ringKrullDim (MvPolynomial τ F ⧸ W) + (s.card : WithBot ℕ∞) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro V W hV hW
    simp only [Finset.coe_empty, Ideal.span_empty, sup_bot_eq] at hW
    rw [Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_singleton_iff] at hW
    subst hW
    simp
  | insert a s ha ih =>
    intro V W hV hW
    have hWp : W.IsPrime := hW.1.1
    have hsplit : V ⊔ Ideal.span (↑(insert a s) : Set (MvPolynomial τ F)) =
        (V ⊔ Ideal.span (s : Set (MvPolynomial τ F))) ⊔ Ideal.span {a} := by
      rw [Finset.coe_insert, Ideal.span_insert, sup_comm (Ideal.span {a}), sup_assoc]
    rw [hsplit] at hW
    obtain ⟨W', hW', hW'W⟩ := Ideal.exists_minimalPrimes_le (le_sup_left.trans hW.1.2)
    have hW'p : W'.IsPrime := hW'.1.1
    have hmin : W ∈ (W' ⊔ Ideal.span {a}).minimalPrimes := by
      refine ⟨⟨hWp, sup_le hW'W (le_sup_right.trans hW.1.2)⟩, fun Z ⟨hZp, hZ⟩ hZW => ?_⟩
      exact hW.2 ⟨hZp, sup_le (hW'.1.2.trans (le_sup_left.trans hZ)) (le_sup_right.trans hZ)⟩ hZW
    have h1 := ih V W' hV hW'
    rw [Finset.card_insert_of_notMem ha, Nat.cast_succ]
    by_cases haW' : a ∈ W'
    · have heq : W' ⊔ Ideal.span {a} = W' := sup_eq_left.mpr ((Ideal.span_singleton_le_iff_mem _).mpr haW')
      rw [heq, Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_singleton_iff] at hmin
      subst hmin
      exact h1.trans (add_le_add le_rfl
        (show (s.card : WithBot ℕ∞) ≤ (s.card : WithBot ℕ∞) + 1 by exact_mod_cast Nat.le_succ s.card))
    · have h2 := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.dimPIT F τ W' W a hW'p haW' hmin
      rw [← h2] at h1
      calc ringKrullDim (MvPolynomial τ F ⧸ V) ≤ ringKrullDim (MvPolynomial τ F ⧸ W) + 1 + (s.card : WithBot ℕ∞) := h1
        _ = ringKrullDim (MvPolynomial τ F ⧸ W) + ((s.card : WithBot ℕ∞) + 1) := by rw [add_assoc, add_comm 1]

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

open ReciprocityTheory.AnForm.R (chartIdeal conePts affCoord) in

theorem ringKrullDim_of_mem_minimalPrimes_chartIdeal {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)}
    (hP : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal P) (e : ℕ)
    (hdim : ∀ Q ∈ P.minimalPrimes,
      ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ Q) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞))
    (p : (k : K) → ι k) {𝔮 : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (h𝔮 : 𝔮 ∈ (chartIdeal P p).minimalPrimes) :
    ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) = e := by
  classical
  have : 𝔮.IsPrime := h𝔮.1.1
  have hup := ReciprocityTheory.AnForm.R.ringKrullDim_quotient_le_of_chartIdeal_le hP e hdim p 𝔮 h𝔮.1.2
  obtain ⟨Q, hQ, hQ𝔮⟩ := Ideal.exists_minimalPrimes_le (le_sup_left.trans h𝔮.1.2)
  have hQp : Q.IsPrime := hQ.1.1
  let s : Finset (MvPolynomial (Σ k, ι k) ℂ) := Finset.univ.image fun k => X ⟨k, p k⟩ - 1
  have hs : (s : Set (MvPolynomial (Σ k, ι k) ℂ)) = Set.range fun k => X ⟨k, p k⟩ - 1 := by
    simp [s]
  have hmin : 𝔮 ∈ (Q ⊔ Ideal.span (s : Set (MvPolynomial (Σ k, ι k) ℂ))).minimalPrimes := by
    rw [hs]
    refine ⟨⟨‹_›, sup_le hQ𝔮 (le_sup_right.trans h𝔮.1.2)⟩, fun Z ⟨hZp, hZ⟩ hZ𝔮 => ?_⟩
    exact h𝔮.2 ⟨hZp, sup_le (hQ.1.2.trans (le_sup_left.trans hZ)) (le_sup_right.trans hZ)⟩ hZ𝔮
  have hlow := ringKrullDim_le_of_mem_minimalPrimes_sup_span s Q 𝔮 hQp hmin
  rw [hdim Q hQ] at hlow
  have hcard : s.card ≤ Fintype.card K := Finset.card_image_le.trans (by simp)
  have hne : ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) ≠ ⊥ := by
    have : Nontrivial (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) := Ideal.Quotient.nontrivial_iff.mpr this.ne_top
    exact ne_bot_of_le_ne_bot (by simp) ringKrullDim_nonneg_of_nontrivial
  refine le_antisymm hup ?_
  generalize ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) = d at hup hlow hne
  induction d using WithBot.recBotCoe with
  | bot => exact absurd rfl hne
  | coe d =>
    induction d using ENat.recTopCoe with
    | top => exact absurd hup (by exact_mod_cast (show ¬ ((⊤ : ℕ∞) ≤ (e : ℕ∞)) by simp))
    | coe d =>
      have h1 : e + Fintype.card K ≤ d + s.card := by exact_mod_cast hlow
      exact_mod_cast (show e ≤ d by omega)

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem mem_mcPts_iff {P : Ideal (MRing ι)} (z : (Σ k, ι k) → ℂ) :
    z ∈ mcPts P ↔ z ∈ ReciprocityTheory.AnForm.R.conePts (P.map (MvPolynomial.map (Int.castRingHom ℂ))) := by
  refine and_congr_right fun _ => ⟨fun h f hf => ?_, fun h f hf => h _ (Ideal.mem_map_of_mem _ hf)⟩
  have hle : P.map (MvPolynomial.map (Int.castRingHom ℂ)) ≤ RingHom.ker (MvPolynomial.eval z) := by
    rw [Ideal.map_le_iff_le_comap]
    intro g hg
    exact h g hg
  exact hle hf

end SegreChartDim

open SegreChartDim

theorem SegreChartDim.proof : SegreChartDim.Statement := by
  classical
  intro K _ ι _ P e m σ i hP J hJ

  set PQ : Ideal (MvPolynomial (Σ k, ι k) ℚ) := P.map (MvPolynomial.map (Int.castRingHom ℚ)) with hPQ
  have hvar := GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.isProjVarQ_of_isArithVar hP
  have : PQ.IsPrime := hvar.1.isPrime
  set PC : Ideal (MvPolynomial (Σ k, ι k) ℂ) := P.map (MvPolynomial.map (Int.castRingHom ℂ)) with hPC
  have hext : ReciprocityTheory.AnForm.R.extC PQ = PC := by
    rw [ReciprocityTheory.AnForm.R.extC, hPQ, hPC, Ideal.map_map]
    congr 1
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun q => ?_)
    · simp only [RingHom.comp_apply, MvPolynomial.map_C]
      congr 1
    · simp
  have hdim : ∀ Q ∈ PC.minimalPrimes,
      ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ Q) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    intro Q hQ
    rw [← hext] at hQ
    rw [ReciprocityTheory.AnForm.R.ringKrullDim_of_mem_minimalPrimes_extC PQ Q hQ]
    exact hvar.2
  have hPCh : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal PC := by
    obtain ⟨S, hS, hPS⟩ := hP.2.1.2.1
    refine ⟨MvPolynomial.map (Int.castRingHom ℂ) '' S, ?_, by rw [hPC, hPS, Ideal.map_span]⟩
    rintro _ ⟨f, hf, rfl⟩
    obtain ⟨a, ha⟩ := hS f hf
    exact ⟨a, fun d hd k => ha d (MvPolynomial.support_map_subset _ _ hd) k⟩

  set T : Set ((Σ k, ι k) → ℂ) := MvPolynomial.zeroLocus ℂ (ReciprocityTheory.AnForm.R.chartIdeal PC i) with hT
  set S := segreChartSet P σ i with hS
  have hTmem : ∀ y, y ∈ T ↔ ∀ h ∈ ReciprocityTheory.AnForm.R.chartIdeal PC i, eval y h = 0 := fun y => by
    simp [hT, MvPolynomial.mem_zeroLocus_iff]
  have hsegT : ∀ y ∈ T, (fun a => segre y (σ a)) ∈ S := by
    intro y hy
    obtain ⟨hc, h1, -⟩ := ReciprocityTheory.AnForm.R.conePts_of_chartIdeal hPCh i y ((hTmem y).1 hy)
    exact ⟨y, (mem_mcPts_iff y).2 hc, by simp [segre, h1], rfl⟩
  have hlift_apply : ∀ z : (Σ k, ι k) → ℂ, segre z i = 1 →
      chartLift σ i (fun a => segre z (σ a)) = ReciprocityTheory.AnForm.R.affCoord i z := by
    intro z hz
    funext q
    rw [chartLift_segre_apply σ i z hz q.1 q.2]
    simp [ReciprocityTheory.AnForm.R.affCoord, div_eq_mul_inv]
  have hliftS : ∀ x ∈ S, chartLift σ i x ∈ T := by
    rintro _ ⟨z, hz, hzi, rfl⟩
    have hne : ∀ k, z ⟨k, i k⟩ ≠ 0 := fun k h0 => by
      have : segre z i = 0 := Finset.prod_eq_zero (Finset.mem_univ k) h0
      rw [hzi] at this
      exact one_ne_zero this
    rw [hTmem, hlift_apply z hzi]
    exact (ReciprocityTheory.AnForm.R.mem_conePts_iff_chartIdeal hPCh i z hne).1 ((mem_mcPts_iff z).1 hz)
  have hsegLift : ∀ x ∈ S, (fun a => segre (chartLift σ i x) (σ a)) = x := by
    rintro _ ⟨z, -, hzi, rfl⟩
    rw [segre_chartLift σ i z hzi]
  have hliftSeg : ∀ y ∈ T, chartLift σ i (fun a => segre y (σ a)) = y := by
    intro y hy
    obtain ⟨-, h1, -⟩ := ReciprocityTheory.AnForm.R.conePts_of_chartIdeal hPCh i y ((hTmem y).1 hy)
    have hyi : segre y i = 1 := by simp [segre, h1]
    funext q
    rw [chartLift_segre_apply σ i y hyi q.1 q.2, h1, inv_one, mul_one]

  let α : MvPolynomial (Fin m) ℂ →ₐ[ℂ] MvPolynomial (Σ k, ι k) ℂ :=
    aeval fun a => ∏ k, X ⟨k, σ a k⟩
  let β : MvPolynomial (Σ k, ι k) ℂ →ₐ[ℂ] MvPolynomial (Fin m) ℂ :=
    aeval fun q => X (σ.symm (Function.update i q.1 q.2))
  have hα : ∀ (y : (Σ k, ι k) → ℂ) f, eval y (α f) = eval (fun a => segre y (σ a)) f := by
    intro y f
    induction f using MvPolynomial.induction_on with
    | C c => simp [α]
    | add f g hf hg => simp [hf, hg]
    | mul_X f a hf =>
      rw [map_mul, map_mul, map_mul, hf]
      simp [α, segre, map_prod]
  have hβ : ∀ (x : Fin m → ℂ) g, eval x (β g) = eval (chartLift σ i x) g := by
    intro x g
    induction g using MvPolynomial.induction_on with
    | C c => simp [β]
    | add f g hf hg => simp [hf, hg]
    | mul_X f q hf =>
      rw [map_mul, map_mul, map_mul, hf]
      simp [β, chartLift]
  have hvanS : ∀ f, f ∈ segreChartIdeal P σ i ↔ ∀ x ∈ S, eval x f = 0 := fun f => by
    simp [segreChartIdeal, hS, MvPolynomial.mem_vanishingIdeal_iff]
  have hvanT : ∀ g, g ∈ MvPolynomial.vanishingIdeal ℂ T ↔ ∀ y ∈ T, eval y g = 0 := fun g => by
    simp [MvPolynomial.mem_vanishingIdeal_iff]
  have htr := minimalPrimes_transfer α.toRingHom β.toRingHom (segreChartIdeal P σ i)
    (MvPolynomial.vanishingIdeal ℂ T)
    (fun f hf => by
      rw [Ideal.mem_comap, hvanT]
      intro y hy
      show eval y (α f) = 0
      rw [hα]
      exact (hvanS f).1 hf _ (hsegT y hy))
    (fun g hg => by
      rw [Ideal.mem_comap, hvanS]
      intro x hx
      show eval x (β g) = 0
      rw [hβ]
      exact (hvanT g).1 hg _ (hliftS x hx))
    (fun f => by
      rw [hvanS]
      intro x hx
      show eval x (β (α f) - f) = 0
      rw [map_sub, hβ, hα, hsegLift x hx, sub_self])
    (fun g => by
      rw [hvanT]
      intro y hy
      show eval y (α (β g) - g) = 0
      rw [map_sub, hα, hβ, hliftSeg y hy, sub_self])
    J (mem_segreChartComponents.1 hJ)
  obtain ⟨hmin, hd⟩ := htr
  rw [hd]
  rw [hT, MvPolynomial.vanishingIdeal_zeroLocus_eq_radical, Ideal.radical_minimalPrimes] at hmin
  exact ringKrullDim_of_mem_minimalPrimes_chartIdeal hPCh e hdim i hmin

end GroundTheory.Heights₂.Heights
