import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsZetaTW
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamFROfIsLamF
import Development.AbelianVarietyTheory.Definitions.Foundations.LiftApplyOfMemAdmissibleSubalgebra
import Development.AbelianVarietyTheory.Definitions.Foundations.ThNSpec
import Development.AbelianVarietyTheory.Definitions.Foundations.OpLDOneSubMemTriv
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamFR2
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ApplyPolyOfStable
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerBettiModuleFreeFinite
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowerSeriesRingHomPadicAlgCl
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.CyclotomicQExpansion GlobalTheory.KummerEisensteinGalois GlobalTheory.K4
open scoped TensorProduct MatrixGroups Matrix
open GlobalTheory.LambdaValuationPowers

noncomputable section

namespace GlobalTheory.AdmProj

theorem tmul_mem_VB {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (N l w : ℕ) [Fact l.Prime]
    {b : X.Fn l} (hb : b ∈ X.B N l w) : (1 : Qbar l) ⊗ₜ[ℤ_[l]] b ∈ X.VB N l w (Qbar l) :=
  LinearMap.mem_range.2 ⟨(1 : Qbar l) ⊗ₜ[ℤ_[l]] (⟨b, hb⟩ : X.B N l w), by simp⟩

theorem fixIc_mono {l : ℕ} [Fact l.Prime] {c c' : Coef l} (h : c.O ≤ c'.O) {x : Qbar l} (hx : FixIc c x) : FixIc c' x :=
  fun σ h1 h2 => hx σ (fun y hy => h1 y (h hy)) h2

theorem fixIc_l_pow_mul {l : ℕ} [Fact l.Prime] {c : Coef l} (a : ℕ) {x : Qbar l} (hx : FixIc c x) :
    FixIc c (((l : ℕ) : Qbar l) ^ a * x) := fun σ h1 h2 => by
  rw [map_mul, map_pow, map_natCast, hx σ h1 h2]

theorem exists_admissible_hecke_projection_nonvanishing_alt : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ)
  [Fact l.Prime] (e : ℕ) (S : Finset Pl) (W : R2 Ω l) (ψ : ZMod l → Qbar l) (ι : Qbar l ≃+* ℂ) (gN : Newform (2 * e + 1))
  (j : Ω →+* Qbar l),
  Nf e S A W → 1 ≤ e →
  (∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) → (l : Ω) ∈ A.nonunits → l ≠ 2 → ¬ l ∣ N → 5 ≤ N →
  (∀ x ∈ A, ‖j x‖ ≤ 1) →
  ∀ (ev : Letter → Qbar l) (ρ : (Ω ≃ₐ[ℚ] Ω) →* GL (Fin 2) (Qbar l)) (F : Finset Ω),
  (∀ s, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) = rhoK W e ψ s) →
  (∀ s ∈ Dec (F := ℚ) A, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 0 = 0) →
  (∀ s ∈ Ine (F := ℚ) A, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 1 = 1) →
  (∀ s ∈ Ine (F := ℚ) A, (∀ y ∈ F, s y = y) →
    (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 0 0 = ((cycZ ℚ Ω l s : ℤ_[l]) : Qbar l) ^ (2 * e - 1 + 1)) →
  (∀ q : ℕ, q.Prime → ¬ q ∣ l * N → ev (Letter.T q) = ι.symm (gN.a q)) →
  ∀ (χ : ℕ → ℤ_[l]), (∀ d : ℕ, Nat.Coprime d N → ev (Letter.D d) = ((χ d : ℤ_[l]) : Qbar l)) →
  ∀ (m : ℕ) (π : Fin m → (Qbar l ⊗[ℤ_[l]] X.Fn l) →ₗ[Qbar l] (Fin 2 → Qbar l))
    (σ : Fin m → (Fin 2 → Qbar l) →ₗ[Qbar l] (Qbar l ⊗[ℤ_[l]] X.Fn l)) (P : FreeAlgebra (Qbar l) Letter),
  P ∈ admissibleLettersSubalgebra (Qbar l) N l → FreeAlgebra.lift (Qbar l) ev P = 1 → (∀ i v, σ i v ∈ X.VB N l (2 * e - 1) (Qbar l)) →
  (∀ i s, ∀ x ∈ X.VB N l (2 * e - 1) (Qbar l), π i (X.galV l (Qbar l) s x) = (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) *ᵥ π i x) →
  (∀ i s v, X.galV l (Qbar l) s (σ i v) = σ i ((ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) *ᵥ v)) →
  (∀ i (T : Letter) v, GlobalTheory.KZ.admitted N l T → X.opV N l (Qbar l) T (σ i v) = ev T • σ i v) →
  (∀ i (T : Letter), GlobalTheory.KZ.admitted N l T → ∀ x ∈ X.VB N l (2 * e - 1) (Qbar l), π i (X.opV N l (Qbar l) T x) = ev T • π i x) →
  (∀ i i' v, π i (σ i' v) = if i = i' then v else 0) →
  (∀ x ∈ X.VB N l (2 * e - 1) (Qbar l), FreeAlgebra.lift (Qbar l) (X.opV N l (Qbar l)) P x = ∑ i, σ i (π i x)) →
  ∀ (c : Coef l) (lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l), FinSupp lam → (∀ i : ℕ, FixIc c (lam (Pi.single i 1))) →
  (∃ c₂ : ℕ, ∀ (n : ℕ), c₂ ≤ n → ∀ (T : Letter) (b : X.Fn l), GlobalTheory.KZ.admitted N l T → InChi X N (2 * e - 1) χ b →
    Cg (n - c₂) (lam (seqN 1 j (thN X A N l n 1 (X.op N l T b)))) (ev T * lam (seqN 1 j (thN X A N l n 1 b)))) →
  ∃ (pr : X.Fn l → Fin 2 → Qbar l) (a : ℕ) (cf : Coef l),
    c.O ≤ cf.O ∧ (∀ s i k, mat W s i k ∈ cf.O) ∧
    (∀ b b', pr (b + b') = pr b + pr b') ∧
    (∀ (z : ℤ_[l]) b, pr (z • b) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]) • pr b) ∧
    (∀ b ∈ X.B N l (2 * e - 1), ∀ i, pr b i ∈ cf.O) ∧
    (∀ (s : Ω ≃ₐ[ℚ] Ω) b, b ∈ X.B N l (2 * e - 1) → pr (X.galB l s b) = rhoK W e ψ s *ᵥ pr b) ∧
    (∀ q : ℕ, q.Prime → ¬ q ∣ l * N → ∀ b, b ∈ X.B N l (2 * e - 1) → pr (X.heckeT N l q b) = ι.symm (gN.a q) • pr b) ∧
    (∀ d : ℕ, Nat.Coprime d N → ∀ b, b ∈ X.B N l (2 * e - 1) → pr (X.diam N l d b) = ((χ d : ℤ_[l]) : Qbar l) • pr b) ∧
    (∀ b ∈ X.B N l (2 * e - 1), pr (X.heckeU l b) = ev Letter.U • pr b) ∧
    IsLamFR2 X A N (2 * e - 1) χ j pr cf ((((l : ℕ) : Qbar l) ^ a) • lam) := by
  intro Ω _ _ _ ε X A N l _ e S W ψ ι gN j hNf he hφ hlA hl2 hlN hN5 hj ev ρ F hρ hDec hIne hIne0 hev χ hχ m π σ P hPadm hPev
    hσV hπgal hσgal hσT heig hπσ hPx c lam hlamF hlamI hlamE
  classical
  have hodd : Odd (2 * e - 1) := ⟨e - 1, by omega⟩
  have hinj : Function.Injective ε := ε.injective
  have hφ' : ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero) := by
    obtain ⟨φ, h1, h2⟩ := hφ; exact ⟨φ, h2, h1⟩
  have hcop : Nat.Coprime N l := ((Nat.Prime.coprime_iff_not_dvd (Fact.out : l.Prime)).2 hlN).symm
  obtain ⟨pr0, ⟨κ, hκ⟩, hLam⟩ := GlobalTheory.LamChi.exists_pr_isLamFR ε X A N l (2 * e - 1) j hφ hlA hl2 hlN hN5 hodd hj ev ρ F hDec hIne hIne0
    m π σ P hPadm hPev hσV hπgal hσgal hσT hπσ hPx χ c lam hlamF hlamI hlamE

  have hadd0 : ∀ b b', pr0 (b + b') = pr0 b + pr0 b' := by
    intro b b'
    simp only [hκ, TensorProduct.tmul_add, map_add, smul_add, Finset.sum_add_distrib]
  have hsmul0 : ∀ (z : ℤ_[l]) b, pr0 (z • b) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]) • pr0 b := by
    intro z b
    rw [hκ, hκ, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [TensorProduct.tmul_smul, ← algebraMap_smul (Qbar l) z, map_smul, smul_comm]
    rfl
  have hgal0 : ∀ (s : Ω ≃ₐ[ℚ] Ω) b, b ∈ X.B N l (2 * e - 1) → pr0 (X.galB l s b) = rhoK W e ψ s *ᵥ pr0 b := by
    intro s b hb
    rw [hκ, hκ, Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e1 : (1 : Qbar l) ⊗ₜ[ℤ_[l]] X.galB l s b = X.galV l (Qbar l) s ((1 : Qbar l) ⊗ₜ[ℤ_[l]] b) := by
      simp [Tower.galV]
    rw [e1, hπgal i s _ (tmul_mem_VB X N l (2 * e - 1) hb), hρ s, Matrix.mulVec_smul]
  have hop0 : ∀ T : Letter, GlobalTheory.KZ.admitted N l T → ∀ b, b ∈ X.B N l (2 * e - 1) → pr0 (X.op N l T b) = ev T • pr0 b := by
    intro T hT b hb
    rw [hκ, hκ, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e1 : (1 : Qbar l) ⊗ₜ[ℤ_[l]] X.op N l T b = X.opV N l (Qbar l) T ((1 : Qbar l) ⊗ₜ[ℤ_[l]] b) := by
      simp [Tower.opV]
    rw [e1, heig i T hT _ (tmul_mem_VB X N l (2 * e - 1) hb), smul_comm]

  obtain ⟨c1, hc1⟩ := hNf.int
  obtain ⟨c0, hcc0, hc10⟩ := (UpperTheory.V.HV.coefSup l).1 c c1
  have hfree := GlobalTheory.KZ.B_free_finite ε X hinj hφ' N l (2 * e - 1) hl2 hN5 hcop hodd
  haveI := hfree.1
  haveI := hfree.2
  let bs := Module.Free.chooseBasis ℤ_[l] (X.B N l (2 * e - 1))
  obtain ⟨a, ha⟩ := exists_le_l_pow l
    (∑ p : Module.Free.ChooseBasisIndex ℤ_[l] (X.B N l (2 * e - 1)) × Fin 2, ‖pr0 (bs p.1) p.2‖)
  have hsmall : ∀ p : Module.Free.ChooseBasisIndex ℤ_[l] (X.B N l (2 * e - 1)) × Fin 2,
      ‖((l : ℕ) : Qbar l) ^ a * pr0 (bs p.1) p.2‖ ≤ 1 := by
    intro p
    have h1 : ‖pr0 (bs p.1) p.2‖ ≤ (l : ℝ) ^ a :=
      le_trans (Finset.single_le_sum
        (f := fun p : Module.Free.ChooseBasisIndex ℤ_[l] (X.B N l (2 * e - 1)) × Fin 2 => ‖pr0 (bs p.1) p.2‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_univ p)) ha
    have hl0 : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
    rw [norm_mul, norm_l_pow]
    calc ((l : ℝ)⁻¹) ^ a * ‖pr0 (bs p.1) p.2‖ ≤ ((l : ℝ)⁻¹) ^ a * (l : ℝ) ^ a :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 1 := by rw [← mul_pow, inv_mul_cancel₀ hl0.ne', one_pow]
  obtain ⟨cf, hcf, hs⟩ := GlobalTheory.PowerSeriesEvalAlgCl.exists_coef_ge_finset c0
    (Finset.univ.image fun p : Module.Free.ChooseBasisIndex ℤ_[l] (X.B N l (2 * e - 1)) × Fin 2 =>
      ((l : ℕ) : Qbar l) ^ a * pr0 (bs p.1) p.2)
    (fun y hy => by
      obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hy
      exact (GlobalTheory.PowerSeriesEvalAlgCl.isIntegral_iff_norm_le_one _).2 (hsmall p))

  obtain ⟨pr, hpr⟩ : ∃ pr : X.Fn l → Fin 2 → Qbar l, ∀ b, pr b = ((l : ℕ) : Qbar l) ^ a • pr0 b := ⟨_, fun _ => rfl⟩
  have hadd : ∀ b b', pr (b + b') = pr b + pr b' := by
    intro b b'; rw [hpr, hpr, hpr, hadd0, smul_add]
  have hsmul : ∀ (z : ℤ_[l]) b, pr (z • b) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]) • pr b := by
    intro z b; rw [hpr, hpr, hsmul0, smul_comm]
  have hint : ∀ b ∈ X.B N l (2 * e - 1), ∀ i, pr b i ∈ cf.O := by
    intro b hb i
    let g : X.B N l (2 * e - 1) →ₗ[ℤ_[l]] Qbar l :=
      { toFun := fun y => pr y.1 i
        map_add' := fun y y' => by
          simp only [Submodule.coe_add, hadd, Pi.add_apply]
        map_smul' := fun z y => by
          simp only [SetLike.val_smul, hsmul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Algebra.smul_def]
          rfl }
    have hle : Submodule.span ℤ_[l] (Set.range bs) ≤ (Subalgebra.toSubmodule cf.O).comap g := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      have := hs _ (Finset.mem_image.2 ⟨(k, i), Finset.mem_univ _, rfl⟩)
      simpa [g, hpr] using this
    rw [bs.span_eq] at hle
    exact hle (Submodule.mem_top (x := (⟨b, hb⟩ : X.B N l (2 * e - 1))))
  have hgal : ∀ (s : Ω ≃ₐ[ℚ] Ω) b, b ∈ X.B N l (2 * e - 1) → pr (X.galB l s b) = rhoK W e ψ s *ᵥ pr b := by
    intro s b hb; rw [hpr, hpr, hgal0 s b hb, Matrix.mulVec_smul]
  have hhecke : ∀ q : ℕ, q.Prime → ¬ q ∣ l * N → ∀ b, b ∈ X.B N l (2 * e - 1) →
      pr (X.heckeT N l q b) = ι.symm (gN.a q) • pr b := by
    intro q hq hqd b hb
    have hT : GlobalTheory.KZ.admitted N l (Letter.T q) := ⟨hq, fun h => hqd (by rwa [mul_comm] at h)⟩
    have := hop0 _ hT b hb
    rw [hpr, hpr, show X.heckeT N l q b = X.op N l (Letter.T q) b from rfl, this, hev q hq hqd, smul_comm]
  have hdiam : ∀ d : ℕ, Nat.Coprime d N → ∀ b, b ∈ X.B N l (2 * e - 1) →
      pr (X.diam N l d b) = ((χ d : ℤ_[l]) : Qbar l) • pr b := by
    intro d hd b hb
    have := hop0 (Letter.D d) hd b hb
    rw [hpr, hpr, show X.diam N l d b = X.op N l (Letter.D d) b from rfl, this, hχ d hd, smul_comm]
  have hU : ∀ b ∈ X.B N l (2 * e - 1), pr (X.heckeU l b) = ev Letter.U • pr b := by
    intro b hb
    have := hop0 Letter.U trivial b hb
    rw [hpr, hpr, show X.heckeU l b = X.op N l Letter.U b from rfl, this, smul_comm]
  have hnorm : ‖((l : ℕ) : Qbar l) ^ a‖ ≤ 1 := by
    rw [norm_l_pow]
    have h1 : (1 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).one_le
    exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ h1)
  have hccf : c.O ≤ cf.O := hcc0.trans hcf
  have hlam : IsLamFR X A N (2 * e - 1) χ j pr cf ((((l : ℕ) : Qbar l) ^ a) • lam) := by
    obtain ⟨hf, hw, cL, per, hper, hc⟩ := hLam
    refine ⟨hf.smul _, fun i => fixIc_l_pow_mul a (fixIc_mono hccf (hw i)), cL, per,
      fun n => ⟨(hper n).1, (hper n).2.1, fixIc_mono hccf (hper n).2.2⟩, fun n hn b hb φ hφ => ?_⟩
    have h := hc n hn b hb φ hφ
    unfold GlobalTheory.Ord2.Cg at h ⊢
    rw [hpr, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    calc ‖((l : ℕ) : Qbar l) ^ a * lam (seqN 1 j φ) - per n * (((l : ℕ) : Qbar l) ^ a * pr0 b 1)‖
        = ‖((l : ℕ) : Qbar l) ^ a‖ * ‖lam (seqN 1 j φ) - per n * pr0 b 1‖ := by
          rw [← norm_mul]; congr 1; ring
      _ ≤ 1 * ‖((l : ℕ) : Qbar l) ^ (n - cL)‖ := mul_le_mul hnorm h (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  exact ⟨pr, a, cf, hccf, fun s i k => hcf (hc10 (hc1 s i k)), hadd, hsmul, hint, hgal, hhecke, hdiam, hU, hdiam, hlam⟩

end GlobalTheory.AdmProj

end
