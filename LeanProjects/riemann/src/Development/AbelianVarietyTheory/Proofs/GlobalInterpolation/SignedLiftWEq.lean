import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.IndexExponentDegree
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralDensEqZero
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PerOComponents
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SmulMemLocPPerO
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsSdLatTwOExpS

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

namespace GlobalTheory.ThetaMove.LiftTranslate

theorem signed_eq {V : Type} [AddCommGroup V] [Module ℂ V] {H : Sesq V} {α : V → ℂ} (hH : IsHerm H) (hα : ∀ x, α (-x) = α x)
    {A B : AddSubgroup V} (hd : IsSelfDual H A) (hs : IsSemiChar H A α) {θ : V → ℂ} (hθ : θ ∈ fixedBy H α B)
    {s u : V} (h1 : s ∈ A) (h2 : u ∈ A) (h3 : u - s ∈ B) (z : V) :
    α s * opU H (-s) θ z = α u * opU H (-u) θ z := by
  have h := GlobalTheory.ThetaInter.alpha_opU_add hH hd hs (A.neg_mem h2) (A.sub_mem h2 h1) θ z
  rw [show -u + (u - s) = -s by abel, hα, hα, ← GlobalTheory.ThetaInter.opU_mul (-u) (α (u - s)),
    show (fun w => α (u - s) * opU H (u - s) θ w) = θ from funext (hθ _ h3)] at h
  exact h

theorem alV_neg {ι : Type} [Fintype ι] {a b : ℕ} (d : ℕ) (sc : ℝ) (x : VV ι a b) : alV d sc (-x) = alV d sc x := by
  simp [alV, alphaQ, Formalism.L2.Th1.H.qOf]

section Loc

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}

omit [StarRing E] in
theorem nat_smul_mem {M : Submodule (𝓞 E) (HomE E a b)} (c : ℕ) {y : HomE E a b} (hy : y ∈ M) : (c : E) • y ∈ M := by
  rw [Nat.cast_smul_eq_nsmul]
  exact M.toAddSubgroup.nsmul_mem hy c

theorem off_le (S : Finset (HeightOneSpectrum (𝓞 E))) (M : Submodule (𝓞 E) (HomE E a b)) {c c' : ℕ} (hc : 0 < c) (hc' : 0 < c')
    {Q : HeightOneSpectrum (𝓞 E)} (hQ : Q ∉ S) {y : HomE E a b} (hy : y ∈ localization₂ Q.asIdeal (halfAO S M c')) :
    y ∈ localization₂ Q.asIdeal (twist₂ M c (expS S)) := by
  have hcE : (c' : E) ≠ 0 := by exact_mod_cast hc'.ne'
  rw [halfAO, mem_localization_twist M hc' (fun Q => by have := expS_bound S Q; omega)] at hy
  rw [mem_localization_twist M hc (expS_bound S)]
  unfold expS at hy ⊢
  rw [if_neg hQ] at hy ⊢
  split_ifs at hy ⊢
  · have h1 := nat_smul_mem c' hy
    rw [neg_neg, zpow_one, smul_smul, mul_inv_cancel₀ hcE, one_smul] at h1
    rw [zpow_neg, inv_inv, zpow_one]
    exact nat_smul_mem c h1
  · simpa using hy

theorem mem_mulLat_iff (S : Finset (HeightOneSpectrum (𝓞 E))) (AA : Submodule (𝓞 E) E) (N : Submodule (𝓞 E) (Sp E a))
    (N' : Submodule (𝓞 E) (Sp E b)) (hN : N.FG) (hAA : ∀ P ∈ S, localization₂ P.asIdeal AA = localization₂ P.asIdeal (1 : Submodule (𝓞 E) E))
    {c : ℕ} (hc : 0 < c) (y : HomE E a b) :
    y ∈ mulLat c (homAt S N N') ↔ ∀ P ∈ S, y ∈ localization₂ P.asIdeal (twist₂ (perO AA N N') c (expS S)) := by
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  have key : ∀ P ∈ S, (y ∈ localization₂ P.asIdeal (twist₂ (perO AA N N') c (expS S)) ↔ (c : E)⁻¹ • y ∈ homAt {P} N N') := by
    intro P hP
    rw [mem_localization_twist _ hc (expS_bound S), (GlobalTheory.ThetaMove.PeriodComp.perO_components E a b AA).2.1 P N N' hN (hAA P hP), expS,
      if_pos hP, zpow_one]
  have hsm : ∀ w : HomE E a b, (c : 𝓞 E) • w = (c : E) • w := fun w => by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  constructor
  · rintro ⟨w, hw, rfl⟩ P hP
    rw [key P hP, LinearMap.smul_apply, LinearMap.id_apply, hsm, smul_smul, inv_mul_cancel₀ hcE, one_smul]
    intro P' hP'
    rw [Finset.mem_singleton.1 hP']
    exact hw P hP
  · intro h
    refine ⟨(c : E)⁻¹ • y, fun P hP => (key P hP).1 (h P hP) P (Finset.mem_singleton_self P), ?_⟩
    rw [LinearMap.smul_apply, LinearMap.id_apply, hsm, smul_smul, mul_inv_cancel₀ hcE, one_smul]

end Loc

theorem signed_liftW_eq : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (N G : Submodule (𝓞 X.E) (Sp X.E a)) (N' G' : Submodule (𝓞 X.E) (Sp X.E b)) (c : ℕ) (x t : HomE X.E a b) (θ : VCx X.Tau a b → ℂ), Moves A a b → (∀ P ∈ S, conjPrime₂ P ∉ S) → A.AAUnit S → IsSdLat N → IsSdLat N' → IsSdLat G → IsSdLat G' → 0 < c → Dom S (perO A.AA G G') (perO A.AA N (twist₂ N' c (expS S))) → t ∈ perO A.AA G G' → t - x ∈ mulLat c (homAt S N N') → θ ∈ fixedBy (Formalism.L2.Ker.HV A.sc) (alV A.d A.sc) (lam A N (twist₂ N' c (expS S))) → ∀ z, (alV A.d A.sc) ((embH (X.embC A.σ₀) A.δ) (A.liftW S N N' c x)) * opU (Formalism.L2.Ker.HV A.sc) (-((embH (X.embC A.σ₀) A.δ) (A.liftW S N N' c x))) θ z = (alV A.d A.sc) ((embH (X.embC A.σ₀) A.δ) t) * opU (Formalism.L2.Ker.HV A.sc) (-((embH (X.embC A.σ₀) A.δ) t)) θ z := by
  intro X A a b S N G N' G' c x t θ hM hS hAA hN hN' hG hG' hc hD ht htx hθ z
  obtain ⟨hδ, -, -, hA0, hLa, -⟩ := hM
  have hfg : N.FG := hN.1.fg
  have per := GlobalTheory.ThetaMove.PeriodComp.perO_components X.E a b A.AA
  have eB : twist₂ (perO A.AA N N') c (expS S) = perO A.AA N (twist₂ N' c (expS S)) :=
    GlobalTheory.ThetaMove.PeriodTwist.twO_perO X.E a b A.AA N N' c _ hfg hc (expS_bound S)
  have eA : ∀ c' : ℕ, 0 < c' → halfAO S (perO A.AA N N') c' = perO A.AA N (twist₂ N' c' fun Q => -expS S Q) := fun c' hc' =>
    GlobalTheory.ThetaMove.PeriodTwist.twO_perO X.E a b A.AA N N' c' _ hfg hc' (fun Q => by have := expS_bound S Q; omega)
  have sdB := (GlobalTheory.ThetaMove.TwistSd.isSdLat_twO_expS X.E b N' c S hS hN' hc).1
  have sdA := fun c' (hc' : 0 < c') => (GlobalTheory.ThetaMove.TwistSd.isSdLat_twO_expS X.E b N' c' S hS hN' hc').2
  have fB : Full (twist₂ (perO A.AA N N') c (expS S)) := eB ▸ per.2.2 N _ hfg sdB.1 hA0
  have fA : ∀ c' : ℕ, 0 < c' → Full (halfAO S (perO A.AA N N') c') := fun c' hc' => by
    rw [eA c' hc']; exact per.2.2 N _ hfg (sdA c' hc').1 hA0
  have fG : Full (perO A.AA G G') := per.2.2 G G' hG.1.fg hG'.1 hA0
  have hmul := mem_mulLat_iff S A.AA N N' hfg hAA hc
  have hex : ∃ s, A.IsLift S N N' c x s := by
    obtain ⟨c', hc', hx⟩ := per.2.2 N N' hfg hN'.1 hA0 x
    obtain ⟨s, h1, h2⟩ := ((fA c' hc').inf fB).approx S x
    simp only [localization_inf, Submodule.mem_inf] at h1 h2
    refine ⟨s, ⟨c', hc', mem_of_locP fun Q => ?_⟩, (hmul _).2 fun P hP => (h1 P hP).2⟩
    by_cases hQ : Q ∈ S
    · have h3 : x ∈ localization₂ Q.asIdeal (halfAO S (perO A.AA N N') c') := by
        rw [halfAO, mem_localization_twist _ hc' (fun Q => by have := expS_bound S Q; omega), expS, if_pos hQ, zpow_neg, inv_inv, zpow_one,
          Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul (𝓞 X.E)]
        exact mem_localization_of_mem Q hx
      simpa using add_mem (h1 Q hQ).1 h3
    · exact (h2 Q hQ).1
  obtain ⟨⟨c₁, hc₁, hs⟩, hsx⟩ : A.IsLift S N N' c x (A.liftW S N N' c x) := Classical.epsilon_spec hex
  generalize A.liftW S N N' c x = s at hs hsx ⊢
  rw [hmul] at hsx htx
  rw [← eB] at hD
  obtain ⟨u, h1, h2⟩ := (((fA c₁ hc₁).inf fG).inf fB).approx S s
  simp only [localization_inf, Submodule.mem_inf] at h1 h2
  have huA : u ∈ halfAO S (perO A.AA N N') c₁ := mem_of_locP fun Q => by
    by_cases hQ : Q ∈ S
    · simpa using add_mem (h1 Q hQ).1.1 (mem_localization_of_mem Q hs)
    · exact (h2 Q hQ).1.1
  have hus : u - s ∈ twist₂ (perO A.AA N N') c (expS S) := mem_of_locP fun Q => by
    by_cases hQ : Q ∈ S
    · exact (h1 Q hQ).2
    · exact sub_mem (h2 Q hQ).2 (off_le S _ hc hc₁ hQ (mem_localization_of_mem Q hs))
  have hut : u - t ∈ twist₂ (perO A.AA N N') c (expS S) := mem_of_locP fun Q => by
    by_cases hQ : Q ∈ S
    · rw [show u - t = (u - s) + (s - x) - (t - x) by abel]
      exact sub_mem (add_mem (h1 Q hQ).2 (hsx Q hQ)) (htx Q hQ)
    · exact sub_mem (h2 Q hQ).2 (hD.2 Q hQ (mem_localization_of_mem Q ht))
  have huG : u ∈ perO A.AA G G' := mem_of_locP fun Q => by
    by_cases hQ : Q ∈ S
    · simpa using add_mem (hD.1 Q hQ (mem_localization_of_mem Q hut)) (mem_localization_of_mem Q ht)
    · exact (h2 Q hQ).1.2
  rw [eB] at hus hut
  rw [eA c₁ hc₁] at hs huA
  have L1 := (hLa N _ hN (sdA c₁ hc₁)).2.2
  have L2 := (hLa G G' hG hG').2.2
  have im : ∀ {M : Submodule (𝓞 X.E) (HomE X.E a b)} {y}, y ∈ M → embH (X.embC A.σ₀) A.δ y ∈ laV (X.embC A.σ₀) A.δ M :=
    fun hy => ⟨_, hy, rfl⟩
  rw [signed_eq (isHerm_HV A.sc) (alV_neg A.d A.sc) L1.1 L1.2 hθ (im hs) (im huA) (by rw [← map_sub]; exact im hus),
    signed_eq (isHerm_HV A.sc) (alV_neg A.d A.sc) L2.1 L2.2 hθ (im ht) (im huG) (by rw [← map_sub]; exact im hut)]

end GlobalTheory.ThetaMove.LiftTranslate
