import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAll
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AbsNormEqOfSplit
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NotDvdDifferent
import Development.AutomorphicArithmetic.CyclotomicBounds.SmallFacts
import Formalism.LocalToGlobal.Columns.BaseLemmas
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormPadicEmbeddingLeOneOfMemInverseHalfDifferent
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AbsNormSpanInvol
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsNormSubEqOne
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PerLatticeFacts
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteQuotDivLatMulLatHomAt
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PeriodLatticeHalfLatticeInclusionsSplitPrime
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AddSubgroupRepsExistenceCardSum
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsRepsSupOfFiniteQuot
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AlgebraicNumbersPadicPlacesFacts
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AbsNormSplitPlace
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocPAAAndPrimesNe
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RatIntOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousToZModComp
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NegOneZpowRound
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MomentCompanion
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RelDetCompanion
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsPrimeUnder
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RelIndexPerDvd
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ApplyMemLocP
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RelIndexNeZeroOfSmul
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MomentsCosetSum

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.MomT

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable

section abelian₂

variable {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p])

theorem lamC_of_mem {x : ℂ} (h : x ∈ TaylorLogMetric.Qbar) : TaylorLogMetric.lamC lam x = lam ⟨x, h⟩ := dif_pos h

theorem lamC_mul {x y : ℂ} (hx : x ∈ TaylorLogMetric.Qbar) (hy : y ∈ TaylorLogMetric.Qbar) :
    TaylorLogMetric.lamC lam (x * y) = TaylorLogMetric.lamC lam x * TaylorLogMetric.lamC lam y := by
  rw [lamC_of_mem lam hx, lamC_of_mem lam hy, lamC_of_mem lam (mul_mem hx hy), ← map_mul]; rfl

theorem lamC_zpow {x : ℂ} (hx : x ∈ TaylorLogMetric.Qbar) (n : ℤ) : TaylorLogMetric.lamC lam (x ^ n) = TaylorLogMetric.lamC lam x ^ n := by
  rw [lamC_of_mem lam hx, lamC_of_mem lam (zpow_mem hx n), ← map_zpow₀]; rfl

theorem lamC_sum {κ : Type} (T : Finset κ) (f : κ → ℂ) (h : ∀ i ∈ T, f i ∈ TaylorLogMetric.Qbar) :
    TaylorLogMetric.lamC lam (∑ i ∈ T, f i) = ∑ i ∈ T, TaylorLogMetric.lamC lam (f i) := by
  classical
  induction T using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, lamC_of_mem lam (zero_mem _)]; exact map_zero lam
  | insert i T hi ih =>
    have h1 := h i (Finset.mem_insert_self _ _)
    have h2 : ∀ j ∈ T, f j ∈ TaylorLogMetric.Qbar := fun j hj => h j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih h2, lamC_of_mem lam h1, lamC_of_mem lam (sum_mem h2),
      lamC_of_mem lam (add_mem h1 (sum_mem h2)), ← map_add]
    rfl

end abelian₂

section Asm

variable {X : Fields} (A : Amb X) {a b : ℕ} (S : Finset (HeightOneSpectrum (𝓞 X.E)))
  (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))

theorem thInd_add (c : ℕ) (x y : HomE X.E a b) (hy : y ∈ mulLat c (homAt S N N')) :
    A.thInd S N N' c (x + y) = A.thInd S N N' c x := by
  have : A.IsLift S N N' c (x + y) = A.IsLift S N N' c x := by
    funext t
    unfold Amb.IsLift
    have e : t - x = (t - (x + y)) + y := by abel
    rw [e, add_mem_cancel_right hy]
  unfold Amb.thInd Amb.liftW
  rw [this]

theorem mulLat_le_divLat {H : Type} [AddCommGroup H] [Module (𝓞 X.E) H] (c c' : ℕ) (M : Submodule (𝓞 X.E) H) :
    mulLat c M ≤ divLat c' M := by
  rintro _ ⟨y, hy, rfl⟩
  exact M.smul_mem _ (M.smul_mem _ hy)

theorem assemble {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : X.K →+* ℂ_[p])
    (hlam : ∀ k, A.σ₀ k ∈ TaylorLogMetric.Qbar ∧ TaylorLogMetric.lamC lam (A.σ₀ k) = ι k) (cA c : ℕ) (hcA : 0 < cA) (hc : 0 < c)
    (hN : IsSdLat N) (hN' : IsSdLat N') (Ξ : HomE X.E a b → X.K)
    (hχ : A.chiF a b N N' ∈ TaylorLogMetric.Qbar) (hχ1 : ‖TaylorLogMetric.lamC lam (A.chiF a b N N')‖ = 1)
    (C : AddSubgroup (HomE X.E a b)) (hC : C ≤ (divLat cA (homAt S N N')).toAddSubgroup) (J : Finset (HomE X.E a b))
    (hJ : IsReps (mulLat c (homAt S N N')).toAddSubgroup C J)
    (h0 : ∀ x ∈ divLat cA (homAt S N N'), ∀ y ∈ mulLat c (homAt S N N'), Ξ (x + y) = Ξ x)
    (h1 : ∀ x ∈ divLat cA (homAt S N N'), ∀ y ∈ C, Ξ (x + y) = Ξ x)
    (h2 : ∀ x ∈ divLat cA (homAt S N N'), ‖ι (Ξ x)‖ ≤ 1)
    (Sup : Set (HomE X.E a b)) (tab : HomE X.E a b → (DVar X.Tau a b →₀ ℕ) → ℂ_[p])
    (h3 : ∀ x ∈ divLat cA (homAt S N N'), Ξ x ≠ 0 → InIntClosure Sup tab Set.univ
      fun m => TaylorLogMetric.lamC lam (∑ j ∈ J, jetC A.cD (A.thInd S N N' c (x + j)) m)) :
    InIntClosure Sup tab (RatIdx A S cA c N N' Ξ) fun m => ι (jetSum A S cA c N N' Ξ m) := by
  classical
  obtain ⟨R, hR, hsum⟩ := _root_.GlobalTheory.latSum_eq_sum_sum_reps X.E _ (divLat cA (homAt S N N')) (mulLat c (homAt S N N')) C J
    (mulLat_le_divLat _ _ _) hC (_root_.GlobalTheory.MomT.finite_quot_divLat_mulLat_homAt X.E a b S N N' cA c hN.1 hN'.1 hcA hc) hJ
  have hχ0 : A.chiF a b N N' ≠ 0 := by
    intro h
    rw [h, lamC_of_mem lam (zero_mem _)] at hχ1
    have : lam ⟨0, zero_mem _⟩ = 0 := map_zero lam
    rw [this, norm_zero] at hχ1
    exact zero_ne_one hχ1
  have hinv : TaylorLogMetric.lamC lam (A.chiF a b N N')⁻¹ = (TaylorLogMetric.lamC lam (A.chiF a b N N'))⁻¹ := by
    simpa using lamC_zpow lam hχ (-1)
  refine clo_congr (clo_sum R (fun x m => if Ξ x = 0 then 0 else ι (Ξ x) * TaylorLogMetric.lamC lam (A.chiF a b N N')⁻¹ *
      TaylorLogMetric.lamC lam (∑ j ∈ J, jetC A.cD (A.thInd S N N' c (x + j)) m)) (M := Set.univ) fun x hx => ?_)
    subset_rfl (Set.subset_univ _) fun m hm => ?_
  · by_cases h : Ξ x = 0
    · simpa [h] using clo_zero Sup tab Set.univ
    · simp only [if_neg h]
      refine clo_mul (h3 x (hR x hx) h) _ ?_
      rw [norm_mul, hinv, norm_inv, hχ1, inv_one, mul_one]
      exact h2 x (hR x hx)
  · unfold jetSum
    rw [hsum X.K _ (fun x hx y hy => by rw [h0 x hx y hy]; unfold Amb.jetK; rw [thInd_add A S N N' c x y hy]), map_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hj : ∀ j ∈ J, Ξ (x + j) = Ξ x := fun j hj => h1 x (hR x hx) j (hJ.1 j hj)
    rw [Finset.sum_congr rfl fun j hj' => by rw [hj j hj'], ← Finset.mul_sum]
    split_ifs with h
    · simp [h]
    have hk : ∀ j ∈ J, A.σ₀ (A.jetK S N N' c (x + j) m) =
        (A.chiF a b N N')⁻¹ * jetC A.cD (A.thInd S N N' c (x + j)) m := by
      intro j hj'
      have := hm (x + j) (add_mem (hR x hx) (hC (hJ.1 j hj'))) (by rw [hj j hj']; exact h)
      unfold Amb.jetK desc
      rw [dif_pos this]
      exact this.choose_spec
    have e : A.σ₀ (∑ j ∈ J, A.jetK S N N' c (x + j) m) =
        (A.chiF a b N N')⁻¹ * ∑ j ∈ J, jetC A.cD (A.thInd S N N' c (x + j)) m := by
      rw [map_sum, Finset.mul_sum]; exact Finset.sum_congr rfl hk
    have hq : ∑ j ∈ J, jetC A.cD (A.thInd S N N' c (x + j)) m ∈ TaylorLogMetric.Qbar := by
      have := mul_mem hχ (hlam (∑ j ∈ J, A.jetK S N N' c (x + j) m)).1
      rwa [e, mul_inv_cancel_left₀ hχ0] at this
    rw [map_mul, ← (hlam (∑ j ∈ J, A.jetK S N N' c (x + j) m)).2, e, lamC_mul lam (inv_mem hχ) hq, mul_assoc]

end Asm

section Phi

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ} {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))}

theorem suppBar_add {d : Deco E a ST SG} {d' : Deco E b ST SG'} (hd' : d'.Ok) {x y : HomE E a b} (hx : x ∈ suppBar d d')
    (hy : ∀ P : ST, ∀ v ∈ d.at P.1, y v ∈ d'.at P.1 ∧ d'.f P (y v) = 0) : x + y ∈ suppBar d d' := by
  intro P v hv
  refine ⟨add_mem (hx P v hv).1 (hy P v hv).1, ?_⟩
  rw [LinearMap.add_apply, hd'.f_add P _ (hx P v hv).1 _ (hy P v hv).1, (hy P v hv).2, add_zero, (hx P v hv).2]

theorem phiT_add (K : Type) [Field K] {d : Deco E a ST SG} {d' : Deco E b ST SG'} (hd' : d'.Ok) (x : HomE E a b)
    {y : HomE E a b} (hy : ∀ P : ST, ∀ v ∈ d.at P.1, y v ∈ d'.at P.1 ∧ d'.f P (y v) = 0) :
    phiT K d d' (x + y) = phiT K d d' x := by
  have h : x + y ∈ suppBar d d' ↔ x ∈ suppBar d d' := by
    refine ⟨fun h => ?_, fun h => suppBar_add hd' h hy⟩
    have := suppBar_add hd' (y := -y) h fun P v hv => ⟨neg_mem (hy P v hv).1, by
      have := hd'.f_smul P (-1) _ (hy P v hv).1
      rw [(hy P v hv).2, mul_zero, neg_one_smul] at this
      exact this⟩
    simpa using this
  unfold phiT
  by_cases hx : x ∈ suppBar d d'
  · exact (if_pos (h.2 hx)).trans (if_pos hx).symm
  · exact (if_neg fun h' => hx (h.1 h')).trans (if_neg hx).symm

theorem ker_of_mulLat {d : Deco E a ST SG} {d' : Deco E b ST SG'} (hd' : d'.Ok) {S : Finset (HeightOneSpectrum (𝓞 E))}
    (hS : ST ⊆ S) {c : ℕ} (hc : ∀ P ∈ ST, (c : 𝓞 E) ∈ P.asIdeal) {y : HomE E a b} (hy : y ∈ mulLat c (homAt S d.N d'.N)) :
    ∀ P : ST, ∀ v ∈ d.at P.1, y v ∈ d'.at P.1 ∧ d'.f P (y v) = 0 := by
  obtain ⟨y, hy, rfl⟩ := hy
  intro P v hv
  have h1 : y v ∈ d'.at P.1 := hy P.1 (hS P.2) v hv
  refine ⟨Submodule.smul_mem _ (c : 𝓞 E) h1, ?_⟩
  have := hd'.f_smul P (c : 𝓞 E) _ h1
  rw [Ideal.Quotient.eq_zero_iff_mem.2 (hc P.1 P.2), zero_mul] at this
  exact this

theorem homAt_mono {S S' : Finset (HeightOneSpectrum (𝓞 E))} (h : S ⊆ S') (N : Submodule (𝓞 E) (Sp E a))
    (N' : Submodule (𝓞 E) (Sp E b)) : homAt S' N N' ≤ homAt S N N' := fun _ hx P hP => hx P (h hP)

theorem norm_phiT_le {K : Type} [Field K] {p : ℕ} [Fact p.Prime] (ι : K →+* ℂ_[p]) (d : Deco E a ST SG) (d' : Deco E b ST SG')
    (x : HomE E a b) : ‖ι (phiT K d d' x)‖ ≤ 1 := by
  unfold phiT
  split_ifs <;> simp

theorem mem_suppBar_of_ne {K : Type} [Field K] {d : Deco E a ST SG} {d' : Deco E b ST SG'} {x : HomE E a b}
    (h : phiT K d d' x ≠ 0) : x ∈ suppBar d d' := by
  unfold phiT at h
  split_ifs at h with h'
  exacts [h', absurd rfl h]

end Phi

section Types

variable {X : Fields} {A : Amb X} {a b : ℕ} {S SG SG₁ SG₂ : Finset (HeightOneSpectrum (𝓞 X.E))} {ϖ : 𝓞 X.E} {p g cA : ℕ}
  [Fact p.Prime] {lam : TaylorLogMetric.Qbar →+* ℂ_[p]} {ι : X.K →+* ℂ_[p]} {un : X.Tau → ℂ_[p]} {w : HeightOneSpectrum (𝓞 X.K)}

theorem conjO_conjO (x : 𝓞 X.E) : X.conjO (X.conjO x) = x := by
  ext
  exact star_star (x : X.E)

omit [Fact p.Prime] in
theorem Ctx.ne_zero (h : Ctx A a b S SG ϖ p g cA) : ϖ ≠ 0 := by
  rintro rfl
  have := h.2.2.2.2.2.1
  rw [zero_mul] at this
  exact h.2.2.2.2.1.ne_zero (by exact_mod_cast this.symm)

omit [Fact p.Prime] in
theorem Ctx.sub (h : Ctx A a b S SG ϖ p g cA) : divs ϖ ⊆ S ∧ SG ⊆ S ∧ (∀ P ∈ divs ϖ, (p : 𝓞 X.E) ∈ P.asIdeal) ∧
    0 < cA ∧ 0 < p * g := by
  obtain ⟨-, -, -, -, hp, hn, -, hS, -, hg, hA⟩ := id h
  refine ⟨fun P hP => (hS P).2 (Or.inl ((mem_divs h.ne_zero P).1 hP)), fun P hP => (hS P).2 (Or.inr hP),
    fun P hP => hn ▸ Ideal.mul_mem_right _ _ ((mem_divs h.ne_zero P).1 hP), Nat.pos_of_ne_zero ?_,
    Nat.mul_pos hp.pos (Nat.pos_of_ne_zero ?_)⟩
  · rintro rfl
    exact hp.ne_one (by simpa using hA)
  · rintro rfl
    exact hp.ne_one (by simpa using hg)

theorem assemble_phi (h : Ctx A a b S SG ϖ p g cA) (hlam : ∀ k, A.σ₀ k ∈ TaylorLogMetric.Qbar ∧ TaylorLogMetric.lamC lam (A.σ₀ k) = ι k)
    (hw : Induces ι w) (d : DecoSet X.E a (divs ϖ) SG₁) (d' : DecoSet X.E b (divs ϖ) SG₂)
    (hχ : A.chiF a b d.1.N d'.1.N ∈ TaylorLogMetric.Qbar) (hχ1 : ‖TaylorLogMetric.lamC lam (A.chiF a b d.1.N d'.1.N)‖ = 1)
    (Ξ₀ : HomE X.E a b → X.K) (hΞ : OffDatum cA (p * g) d.1.N d'.1.N SG w Ξ₀)
    (C : AddSubgroup (HomE X.E a b)) (hC : ∀ y ∈ C, y ∈ homAt S d.1.N d'.1.N ∧ y ∈ mulLat (p * g) (homAt SG d.1.N d'.1.N) ∧
      ∀ P : ↥(divs ϖ), ∀ v ∈ d.1.at P.1, y v ∈ d'.1.at P.1 ∧ d'.1.f P (y v) = 0)
    (J : Finset (HomE X.E a b)) (hJ : IsReps (mulLat (p * g) (homAt S d.1.N d'.1.N)).toAddSubgroup C J)
    (Sup : Set (HomE X.E a b)) (tab : HomE X.E a b → (DVar X.Tau a b →₀ ℕ) → ℂ_[p])
    (h3 : ∀ x ∈ divLat cA (homAt S d.1.N d'.1.N), x ∈ suppBar d.1 d'.1 → InIntClosure Sup tab Set.univ
      fun m => TaylorLogMetric.lamC lam (∑ j ∈ J, jetC A.cD (A.thInd S d.1.N d'.1.N (p * g) (x + j)) m)) :
    InIntClosure Sup tab (RatIdx A S cA (p * g) d.1.N d'.1.N fun x => phiT X.K d.1 d'.1 x * Ξ₀ x)
      fun m => ι (jetSum A S cA (p * g) d.1.N d'.1.N (fun x => phiT X.K d.1 d'.1 x * Ξ₀ x) m) := by
  obtain ⟨s1, s2, s3, s4, s5⟩ := h.sub
  have hd : ∀ x ∈ divLat cA (homAt S d.1.N d'.1.N), x ∈ divLat cA (homAt SG d.1.N d'.1.N) :=
    fun x hx => homAt_mono s2 _ _ hx
  refine assemble A S d.1.N d'.1.N lam ι hlam cA (p * g) s4 s5 ⟨d.2.lat, d.2.uni⟩ ⟨d'.2.lat, d'.2.uni⟩ _ hχ hχ1 C
    (fun y hy => Submodule.smul_mem (homAt S d.1.N d'.1.N) (cA : 𝓞 X.E) (hC y hy).1) J hJ (fun x hx y hy => ?_)
    (fun x hx y hy => ?_) (fun x hx => ?_) Sup tab fun x hx h0 => h3 x hx (mem_suppBar_of_ne (left_ne_zero_of_mul h0))
  · rw [phiT_add X.K d'.2 x (ker_of_mulLat d'.2 s1 (fun P hP => ?_) hy),
      (hΞ x (hd x hx)).2 y (Submodule.map_mono (homAt_mono s2 _ _) hy)]
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (s3 P hP)
  · rw [phiT_add X.K d'.2 x (hC y hy).2.2, (hΞ x (hd x hx)).2 y (hC y hy).2.1]
  · rw [map_mul, norm_mul]
    exact mul_le_one₀ (norm_phiT_le ι _ _ x) (norm_nonneg _)
      ((_root_.GlobalTheory.MomPlace.places X.K p A.σ₀ ι).2.1 w hw _ (hΞ x (hd x hx)).1)

theorem type_bar (h : Ctx A a b S SG ϖ p g cA) (hlam : ∀ k, A.σ₀ k ∈ TaylorLogMetric.Qbar ∧ TaylorLogMetric.lamC lam (A.σ₀ k) = ι k)
    (hw : Induces ι w) (d : DecoSet X.E a (divs ϖ) SG₁) (d' : DecoSet X.E b (divs ϖ) SG₂)
    (hχ : A.chiF a b d.1.N d'.1.N ∈ TaylorLogMetric.Qbar) (hχ1 : ‖TaylorLogMetric.lamC lam (A.chiF a b d.1.N d'.1.N)‖ = 1)
    (Ξ₀ : HomE X.E a b → X.K) (hΞ : OffDatum cA (p * g) d.1.N d'.1.N SG w Ξ₀)
    (hm : PtMom A a b lam ι un ((ϖ : X.E) / star (ϖ : X.E))) :
    InIntClosure (suppBar d.1 d'.1) (ptTab ι un)
      (RatIdx A S cA (p * g) d.1.N d'.1.N fun x => phiT X.K d.1 d'.1 x * Ξ₀ x)
      fun m => ι (jetSum A S cA (p * g) d.1.N d'.1.N (fun x => phiT X.K d.1 d'.1 x * Ξ₀ x) m) := by
  refine assemble_phi h hlam hw d d' hχ hχ1 Ξ₀ hΞ ⊥ (fun y hy => ?_) {0} ⟨by simp, by simp, by simp⟩ _ _ fun x hx hs => ?_
  · rw [AddSubgroup.mem_bot.1 hy]
    refine ⟨zero_mem _, zero_mem _, fun P v _ => ⟨zero_mem _, ?_⟩⟩
    have := d'.2.f_smul P 0 0 (zero_mem _)
    simpa using this
  · have := (_root_.GlobalTheory.MomT.CosetBar.moments_thInd X A a b S SG ϖ p g cA d.1.N d'.1.N lam ι un h ⟨d.2.lat, d.2.uni⟩ ⟨d'.2.lat, d'.2.uni⟩ hm x hx
      fun P hP v hv => (hs ⟨P, hP⟩ v hv).1).2
    refine clo_congr this (fun t ht => ?_) subset_rfl fun m _ => by simp
    have := suppBar_add d'.2 hs (ker_of_mulLat d'.2 subset_rfl h.sub.2.2.1 ht)
    simpa using this

theorem type_p (h : Ctx A a b S SG ϖ p g cA) (hlam : ∀ k, A.σ₀ k ∈ TaylorLogMetric.Qbar ∧ TaylorLogMetric.lamC lam (A.σ₀ k) = ι k)
    (hw : Induces ι w) (d : DecoSet X.E a (divs ϖ) SG₁) (d' : DecoSet X.E b (divs ϖ) SG₂) (hstd : StdAtT d.1)
    (hχ : A.chiF a b d.1.N d'.1.N ∈ TaylorLogMetric.Qbar) (hχ1 : ‖TaylorLogMetric.lamC lam (A.chiF a b d.1.N d'.1.N)‖ = 1)
    (Ξ₀ : HomE X.E a b → X.K) (hΞ : OffDatum cA (p * g) d.1.N d'.1.N SG w Ξ₀)
    (hm : PtMom A a b lam ι un (star (ϖ : X.E) / (ϖ : X.E))) (hnorm : ∀ P ∈ divs ϖ, Ideal.absNorm P.asIdeal = p)
    (N'' : Submodule (𝓞 X.E) (Sp X.E b)) (hN'' : IsSdLat N'')
    (hc : (∀ y ∈ d'.1.N, (ϖ : X.E) • y ∈ N'') ∧ (∀ y ∈ N'', star (ϖ : X.E) • y ∈ d'.1.N) ∧
      ∀ (P : ↥(divs ϖ)) (y : Sp X.E b), y ∈ localization₂ P.1.asIdeal N'' ↔ y ∈ d'.1.at P.1 ∧ d'.1.f P y = 0)
    (κ : ℂ) (hκ : κ ∈ TaylorLogMetric.Qbar) (hκ1 : ‖TaylorLogMetric.lamC lam κ‖ ^ 2 ≤ (p : ℝ) ^ ((divs ϖ).card * a))
    (hmove : ∀ R : Finset (HomE X.E a b), IsReps (per A d.1.N d'.1.N).toAddSubgroup (per A d.1.N N'').toAddSubgroup R →
      ∀ z, ∑ y ∈ R, Wx A y (A.e a b d.1.N d'.1.N) z = ((Real.sqrt (R.card : ℝ) : ℝ) : ℂ) * κ * A.e a b d.1.N N'' z) :
    InIntClosure (suppP d.1 d'.1) (fun x m => ((p : ℂ_[p]) ^ ((divs ϖ).card * a))⁻¹ * ptTab ι un x m)
      (RatIdx A S cA (p * g) d.1.N d'.1.N fun x => phiT X.K d.1 d'.1 x * Ξ₀ x)
      fun m => ι (jetSum A S cA (p * g) d.1.N d'.1.N (fun x => phiT X.K d.1 d'.1 x * Ξ₀ x) m) := by
  obtain ⟨s1, s2, s3, s4, s5⟩ := h.sub
  have hN : IsSdLat d.1.N := ⟨d.2.lat, d.2.uni⟩
  have hN' : IsSdLat d'.1.N := ⟨d'.2.lat, d'.2.uni⟩
  obtain ⟨hAA, -, -, -, l4, -⟩ := _root_.GlobalTheory.MomT.HalfIncl.half_inclusions X A a b S SG ϖ p g cA d.1.N d'.1.N h hN hN'
  have hFG : A.AA.FG := h.2.1.2.2.2.2.1
  have hU : A.AAUnit S := h.2.1.2.2.2.1
  set r : X.E := ((cA * g : ℕ) : X.E) * star (ϖ : X.E) with hr
  have hrO : ∀ (W : Type) [AddCommGroup W] [Module X.E W] [Module (𝓞 X.E) W] [IsScalarTower (𝓞 X.E) X.E W] (y : W),
      r • y = (((cA * g : ℕ) : 𝓞 X.E) * X.conjO ϖ) • y := by
    intro W _ _ _ _ y
    rw [← algebraMap_smul X.E (((cA * g : ℕ) : 𝓞 X.E) * X.conjO ϖ) y, map_mul, map_natCast]
    rfl
  have hC : ∀ y ∈ (smulLat r (per A d.1.N d'.1.N ⊓ per A d.1.N N'')).toAddSubgroup,
      y ∈ homAt S d.1.N d'.1.N ∧ y ∈ mulLat (p * g) (homAt SG d.1.N d'.1.N) ∧
      ∀ P : ↥(divs ϖ), ∀ v ∈ d.1.at P.1, y v ∈ d'.1.at P.1 ∧ d'.1.f P (y v) = 0 := by
    intro y hy
    obtain ⟨m, hm', rfl⟩ := (mem_smulLat _ _ _).1 hy
    refine ⟨?_, (l4 m hm'.1).2.2.1, fun P v hv => (hc.2.2 P _).1 ?_⟩
    · rw [hrO]; exact Submodule.smul_mem _ _ (l4 m hm'.1).1
    · rw [LinearMap.smul_apply, hrO]
      exact Submodule.smul_mem _ _
        (((_root_.GlobalTheory.MomT.LatFin.per_lattice_facts X A a b d.1.N N'' hFG hAA hN hN'').2.2.2 P.1 (hU P.1 (s1 P.2)) m).1 (le_locP _ _ hm'.2) v hv)
  obtain ⟨J, hJ⟩ := (_root_.GlobalTheory.RepsMod.reps_facts (HomE X.E a b)).1 (mulLat (p * g) (homAt S d.1.N d'.1.N)).toAddSubgroup
    (smulLat r (per A d.1.N d'.1.N ⊓ per A d.1.N N'')).toAddSubgroup (by
      have hf := _root_.GlobalTheory.MomT.finite_quot_divLat_mulLat_homAt X.E a b S d.1.N d'.1.N cA (p * g) hN.1 hN'.1 s4 s5
      have h1 : (mulLat (p * g) (homAt S d.1.N d'.1.N)).toAddSubgroup.relIndex
          (divLat cA (homAt S d.1.N d'.1.N)).toAddSubgroup ≠ 0 := @AddSubgroup.index_ne_zero_of_finite _ _ _ hf
      intro h0
      exact h1 (AddSubgroup.relIndex_eq_zero_of_le_right
        (fun y hy => Submodule.smul_mem (homAt S d.1.N d'.1.N) (cA : 𝓞 X.E) (hC y hy).1) h0))
  refine assemble_phi h hlam hw d d' hχ hχ1 Ξ₀ hΞ _ hC J hJ _ _ fun x hx hs => ?_
  refine clo_congr (_root_.GlobalTheory.MomT.CosetSum.moments_coset_sum X A a b S SG ϖ p g cA d.1.N d'.1.N N'' lam ι un κ _ h hN hN' hN'' hc.1 hc.2.1 hm hκ hκ1
    (_root_.GlobalTheory.MomT.IdxBound.relIndex_per_dvd X A a b SG₂ ϖ p d.1.N d' N'' hFG hAA (fun P hP => hU P (s1 hP)) h.ne_zero hnorm hN hN''
      (fun P hP => hstd ⟨P, hP⟩) hc) hmove J hJ x hx fun P hP v hv => (hs ⟨P, hP⟩ v hv).1)
    (fun t ht P y hy hf => ?_) subset_rfl fun _ _ => rfl
  refine _root_.GlobalTheory.AdjMem.adj_per_mem X A a b d.1.N N'' P.1 hN hN'' (h.2.2.1 _ ?_) t ht y ((hc.2.2 P y).2 ⟨hy, hf⟩)
  have h0 : X.conjO ϖ ≠ 0 := by
    intro h0
    have := h.2.2.2.2.2.1
    rw [h0, mul_zero] at this
    exact h.2.2.2.2.1.ne_zero (by exact_mod_cast this.symm)
  rw [mem_divs h0, mem_conjP]
  have : cO X.E (X.conjO ϖ) = ϖ := conjO_conjO ϖ
  rw [this]
  exact (mem_divs h.ne_zero _).1 P.2

end Types

section Main

theorem norm_ratio_le {X : Fields} {p : ℕ} [Fact p.Prime] (ρ : X.E →+* ℂ_[p]) {ϖ : 𝓞 X.E}
    (h : ϖ * X.conjO ϖ = (p : 𝓞 X.E)) : ‖(ρ ((ϖ : X.E) / star (ϖ : X.E)))⁻¹‖ ≤ p := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have h1 : ‖ρ (ϖ : X.E)‖ * ‖ρ (star (ϖ : X.E))‖ = (p : ℝ)⁻¹ := by
    have e : (ϖ : X.E) * star (ϖ : X.E) = (p : X.E) := by
      have := congrArg (algebraMap (𝓞 X.E) X.E) h
      rwa [map_mul, map_natCast] at this
    rw [← norm_mul, ← map_mul, e, map_natCast, ← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap', Padic.norm_p]
  have h2 : ‖ρ (star (ϖ : X.E))‖ ≤ 1 :=
    GlobalTheory.SplitEmbSep.norm_le_one_of_isIntegral (map_isIntegral_int ρ (X.conjO ϖ).isIntegral_coe)
  have h0 : ‖ρ (ϖ : X.E)‖ ≠ 0 := left_ne_zero_of_mul (h1 ▸ (inv_pos.2 hp).ne')
  have h3 : ‖ρ (star (ϖ : X.E))‖ / ‖ρ (ϖ : X.E)‖ = ‖ρ (star (ϖ : X.E))‖ ^ 2 * p := by
    have : (p : ℝ) * (‖ρ (ϖ : X.E)‖ * ‖ρ (star (ϖ : X.E))‖) = 1 := by rw [h1, mul_inv_cancel₀ hp.ne']
    rw [div_eq_iff h0]
    linear_combination (-‖ρ (star (ϖ : X.E))‖) * this
  rw [map_div₀, inv_div, norm_div, h3]
  exact mul_le_of_le_one_left hp.le (pow_le_one₀ (norm_nonneg _) h2)

theorem jetMoments_of (hM : TranslateMomentsAll) (hE : MovesAll) (hL : LatticeFactsAll) : JetMoments := by
  intro D hD H s cc δ B χ cD ⟨hs, _, hcc, hδ, hχ, hcD⟩ u _ hcop w ι hw
  classical
  obtain ⟨lam, hlam⟩ := (_root_.GlobalTheory.MomPlace.places D.X.K (D.Pr.T u) s.σ₀ ι).1
  obtain ⟨⟨hTs, hTq⟩, -⟩ : (D.Pr.T u ∉ H.host.small ∧ D.Pr.T u ≠ H.host.q) ∧
      ∀ i, D.Pr.g i ∉ H.host.small ∧ D.Pr.g i ≠ H.host.q :=
    ⟨(_root_.GlobalTheory.AAUnitAway.locP_AA_and_primes_ne.2 D H s hD).1 u, (_root_.GlobalTheory.AAUnitAway.locP_AA_and_primes_ne.2 D H s hD).2⟩
  have hT2 : D.Pr.T u ≠ 2 := UpperTheory.Small.ne_two H.host hTs
  have hP := hD.primes
  have hp := hP.T_prime u
  have hn := hP.piT_norm u
  obtain ⟨Ω, hΩ, hmom⟩ := hM H cc δ B χ hcc hδ hχ (D.Pr.T u) lam
    (Or.inr ((_root_.GlobalTheory.MomT.SplitK.splitk H D.X s (D.Pr.piT u) _ hs (hP.piT_Kq u)).2 hp hT2 hn (hP.piT_cop u))) hcop
  obtain ⟨M, _, hMe, hMs⟩ := hcD
  have hcQ : ∀ τ, cD τ ∈ TaylorLogMetric.Qbar := by
    intro τ
    obtain ⟨x, hx, -⟩ := hMs τ
    rw [← hx]
    exact mem_algebraicClosure_iff.2
      ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom (algebraMap M ℂ).toRatAlgHom)
  refine ⟨fun τ => TaylorLogMetric.lamC lam (cD (s.iT τ)) / Ω, fun τ => ?_, ?_⟩
  · obtain ⟨x, hx, hx'⟩ := hMs (s.iT τ)
    rw [norm_div, hΩ.1, div_one, ← hx]
    exact GlobalTheory.EigenGenerator.norm_generator_eq_one H _ lam hTs hTq M hMe _ x hx'
  intro sel S mu cst hsel hS hcq i b _ hb SG SG' d d' hd hd' Ξ₀ hΞ
  have hev : ∀ j, Even (D.R.N j) := fun j => D.R.k_even.add ((D.R.t_odd.add_one).mul_left j)
  have ha := hev i
  have hb' : Even b := hb ▸ hev _
  obtain ⟨hla, hsm⟩ := hL H D.X s cc δ B χ cD hD.fields hs hcc hδ hχ _ _ ha hb'
  have hπ0 : D.Pr.piT u ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hn
    exact hp.ne_zero (by exact_mod_cast hn.symm)
  have hπ0' : D.X.conjO (D.Pr.piT u) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hn
    exact hp.ne_zero (by exact_mod_cast hn.symm)
  obtain ⟨hfree, hrow⟩ := _root_.GlobalTheory.Proof.AbsNormSplitPlace.main D u sel S mu hD hsel (hS (Or.inr ⟨u, rfl⟩))
    (fun k => hS (Or.inl (by fin_cases k <;> simp)))
  have hUT : ∀ P : HeightOneSpectrum (𝓞 D.X.E), ((D.Pr.T u : ℕ) : 𝓞 D.X.E) ∈ P.asIdeal →
      localization₂ P.asIdeal (ambOf s B χ cD).AA = localization₂ P.asIdeal (1 : Submodule (𝓞 D.X.E) D.X.E) :=
    fun P h => _root_.GlobalTheory.AAUnitAway.locP_AA_and_primes_ne.1 H D.X s cc δ B χ cD P _ hp hTs hTq h hcop
  have hmemS : ∀ P, P ∈ Sall sel mu u ↔ D.Pr.piT u ∈ P.asIdeal ∨ P ∈ rowSG D.Pr sel mu := by
    intro P
    unfold Sall
    rw [Finset.mem_union, Primes.vT, mem_divs hπ0]
  have hU : (ambOf s B χ cD).AAUnit (Sall sel mu u) := by
    intro P hPS
    rcases (hmemS P).1 hPS with h | h
    · exact hUT P (hn ▸ Ideal.mul_mem_right _ _ h)
    · have bad := _root_.GlobalTheory.ThetaMove.BadPrimes.bad_primes D.X D.Pr sel S mu u hD.fields hP hsel (hS (Or.inr ⟨u, rfl⟩))
        (fun k => hS (Or.inl (by fin_cases k <;> simp))) P hPS
      exact _root_.GlobalTheory.PeriodIdealUnit.locP_AA_eq_one D.X H s cc δ B χ cD P bad.2.1 bad.2.2.1 (hcq P h)
  have hG : Nat.Coprime (∏ P : rowSG D.Pr sel mu, Formalism.L2.Col.qOf P.1) (D.Pr.T u) :=
    Nat.Coprime.prod_left fun P _ => (Nat.coprime_primes (hrow P.1 P.2).1 hp).2 (hrow P.1 P.2).2.1
  have hctx : Ctx (ambOf s B χ cD) (D.R.N i) b (Sall sel mu u) (rowSG D.Pr sel mu) (D.Pr.piT u) (D.Pr.T u)
      ((∏ P : rowSG D.Pr sel mu, Formalism.L2.Col.qOf P.1) ^ cst.B) (cAof sel mu cst) :=
    ⟨hD.fields, ⟨hla.1, hla.2.1, hfree, hU, hla.2.2.2.2⟩,
      fun P h => hUT P (hn ▸ Ideal.mul_mem_left _ _ ((mem_divs hπ0' P).1 h)), hsm, hp, hn, hP.piT_cop u, hmemS,
      fun P h => (hrow P h).2.2.1, hG.pow_left _, hG.pow_left _⟩
  have hN : IsSdLat d.1.N := ⟨d.2.lat, d.2.uni⟩
  have hN' : IsSdLat d'.1.N := ⟨d'.2.lat, d'.2.uni⟩
  obtain ⟨c1, c1'⟩ := _root_.GlobalTheory.MomT.ChiUnit.chi_det_unit H D.X s χ _ lam (D.Pr.piT u) _ d.1.N hD.fields hs hχ hn hN
    fun P h => hd ⟨P, (mem_divs hπ0 P).2 h⟩
  obtain ⟨c2, c2'⟩ := _root_.GlobalTheory.MomT.ChiUnit.chi_det_unit H D.X s χ _ lam (D.Pr.piT u) _ d'.1.N hD.fields hs hχ hn hN'
    fun P h => hd' ⟨P, (mem_divs hπ0 P).2 h⟩
  have hF : (ambOf s B χ cD).chiF (D.R.N i) b d.1.N d'.1.N ∈ TaylorLogMetric.Qbar := mul_mem (zpow_mem c1 _) (zpow_mem c2 _)
  have hF1 : ‖TaylorLogMetric.lamC lam ((ambOf s B χ cD).chiF (D.R.N i) b d.1.N d'.1.N)‖ = 1 := by
    refine (congrArg norm (lamC_mul lam (zpow_mem c1 _) (zpow_mem c2 _))).trans ?_
    rw [lamC_zpow lam c1, lamC_zpow lam c2, norm_mul, norm_zpow, norm_zpow, c1', c2', one_zpow, one_zpow, one_mul]
  refine ⟨fun hseen => ?_, fun hseen => ?_⟩
  · refine type_bar hctx hlam hw d d' hF hF1 Ξ₀ hΞ ?_
    have := _root_.GlobalTheory.MomT.PtMoments.ptMom H D.X s cc δ B χ cD _ lam ι Ω (D.X.conjO (D.Pr.piT u)) (D.R.N i) b hD.fields hs hcc hT2 hcop
      (fun k => (hlam k).2) hcQ (fun τ τ' => ?_) (by rw [conjO_conjO, mul_comm, hn])
      (by rw [conjO_conjO]; exact (hP.piT_cop u).symm) (fun τ => (hw _).1 (hseen τ)) ha hb' hla hsm hmom
    · have e : ((D.X.conjO (D.Pr.piT u) : 𝓞 D.X.E) : D.X.E) = star ((D.Pr.piT u : 𝓞 D.X.E) : D.X.E) := rfl
      rwa [e, star_star] at this
    · have e : ((D.X.conjO (D.Pr.piT u) : 𝓞 D.X.E) : D.X.E) = star ((D.Pr.piT u : 𝓞 D.X.E) : D.X.E) := rfl
      rw [e, hD.fields.emb_star, hD.fields.emb_star, hP.piT_Kq u τ τ']
  · have hsq : ∀ P ∈ divs (D.Pr.piT u), D.Pr.piT u ∉ P.asIdeal ^ 2 := by
      intro P hPm h2
      refine GlobalTheory.SplitUnram.natCast_notMem_sq D.X.E D.X.conjO (D.Pr.piT u) _ conjO_conjO hp hn (hP.piT_cop u) ?_
        (hP.vT_norm u) P hPm (hn ▸ Ideal.mul_mem_right _ _ h2)
      have h1 : (divs (D.Pr.piT u)).card = Module.finrank ℚ D.X.F := (hP.vT_card u).trans hD.fields.card_Tau
      rw [h1, ← Module.finrank_mul_finrank ℚ D.X.F D.X.E, hD.fields.rankE, mul_comm]
    obtain ⟨N'', hN'', hc⟩ := _root_.GlobalTheory.MomT.MomentCompanion.companion D.X b SG' (D.Pr.piT u) d' hD.fields hπ0 (hP.piT_cop u) hsq
    have hval := _root_.GlobalTheory.MomT.ChiMove.chi_move H D.X s χ b SG' (D.Pr.piT u) d' N'' hD.fields hs hχ hπ0 (hP.piT_cop u) hsq hN'' hc
    set k : D.X.K := ∏ τ, (D.X.emb τ (((D.Pr.piT u : 𝓞 D.X.E) : D.X.E) / star ((D.Pr.piT u : 𝓞 D.X.E) : D.X.E)))⁻¹ with hk
    have hval' : χ (TaylorLogMetric.detId H (s.lat d'.1.N) (s.lat N'')) = s.σ₀ k := by
      rw [hval, hk, map_prod]
      exact Finset.prod_congr rfl fun τ _ => (map_inv₀ _ _).symm
    have hk0 : k ≠ 0 := by
      have h0 : ((D.Pr.piT u : 𝓞 D.X.E) : D.X.E) ≠ 0 := by exact_mod_cast hπ0
      exact Finset.prod_ne_zero_iff.2 fun τ _ => inv_ne_zero ((map_ne_zero _).2 (div_ne_zero h0 (star_ne_zero.2 h0)))
    have hkn : ‖ι k‖ ≤ (D.Pr.T u : ℝ) ^ D.X.f := by
      rw [hk, map_prod, norm_prod]
      refine (Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun τ _ => ?_).trans_eq
        (Finset.prod_const (D.Pr.T u : ℝ))
      rw [map_inv₀]
      exact norm_ratio_le (ι.comp (D.X.emb τ)) hn
    have hcard : (divs (D.Pr.piT u)).card = D.X.f := hP.vT_card u
    have key := type_p hctx hlam hw d d' hd hF hF1 Ξ₀ hΞ
      (_root_.GlobalTheory.MomT.PtMoments.ptMom H D.X s cc δ B χ cD _ lam ι Ω (D.Pr.piT u) (D.R.N i) b hD.fields hs hcc hT2 hcop
        (fun k => (hlam k).2) hcQ (hP.piT_Kq u) hn (hP.piT_cop u) (fun τ => (hw _).1 (hseen τ)) ha hb' hla hsm hmom)
      (hP.vT_norm u) N'' hN'' hc (s.σ₀ (k ^ (D.R.N i / 2))) (hlam _).1 ?_ ?_
    · rw [hcard] at key
      exact key
    · rw [(hlam _).2, map_pow, norm_pow, ← pow_mul, Nat.div_two_mul_two_of_even ha, hcard, pow_mul]
      exact pow_le_pow_left₀ (norm_nonneg _) hkn _
    · intro R hR z
      have hmv := _root_.GlobalTheory.MomT.Move.move H D.X s cc δ B χ cD _ b d.1.N d'.1.N N'' hD.fields hs (hE H cc δ B χ hcc hδ hχ) ha hb' hla
        hN hN' hN'' R hR z
      have hR0 : ((Real.sqrt (R.card : ℝ) : ℝ) : ℂ) ≠ 0 := by
        obtain ⟨x, hx, -⟩ := hR.2.2 0 (zero_mem _)
        have : (0 : ℝ) < R.card := by exact_mod_cast Finset.card_pos.2 ⟨x, hx⟩
        exact_mod_cast (Real.sqrt_pos.2 this).ne'
      have hσ : s.σ₀ k ≠ 0 := (map_ne_zero _).2 hk0
      rw [hmv, hval', map_pow, zpow_neg, zpow_natCast]
      field_simp

end Main

end GlobalTheory.MomT
