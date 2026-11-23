import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FracIdExistsTotPos
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AbelianVarietyTorsionCardEqPowProof
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleIffVeryAmpleBy
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.VeryAmpleByPw
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FiniteMonotoneGrowth
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FinrankSecPullSandwich
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FinrankEqCardKernelPointsOfEtale
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionPointsAbelianVariety
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfQuasiAffine
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealMultPullbackPolarizationClassStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealMultIsogenyFiniteEtaleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankSectionsMonoTensorEffectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPowerNonvanishingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeOfEventualPolynomialGrowthStatement

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
open GlobalTheory.AbLaw GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.RealMultKernel

theorem cls_diag_add {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S : Scheme.{0}} (X : Obj F 𝔠 S) (c c' : 𝔠.elt) :
    cls (X.diag (c + c')) (pull_isLB (X.isLB _) _) =
      cls (X.diag c) (pull_isLB (X.isLB _) _) + cls (X.diag c') (pull_isLB (X.isLB _) _) := by
  have e : cls (X.P c') (X.isLB c') = cls (X.P (c + c')) (X.isLB _) - cls (X.P c) (X.isLB c) := by
    rw [← cls_div (X.isLB _) (X.isLB _) (LB.isLB_div (X.isLB _) (X.isLB _))]
    exact (cls_eq_iff _ _).2 (X.add c c')
  show CechPic.pull _ (cls (X.P (c + c')) (X.isLB _)) =
    CechPic.pull _ (cls (X.P c) (X.isLB c)) + CechPic.pull _ (cls (X.P c') (X.isLB c'))
  rw [e, map_sub]; abel

theorem cls_diag_natCast_smul {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S : Scheme.{0}} (X : Obj F 𝔠 S)
    (c : 𝔠.elt) (n : ℕ) :
    cls (X.diag ((n : 𝓞 F) • c)) (pull_isLB (X.isLB _) _) = n • cls (X.diag c) (pull_isLB (X.isLB _) _) := by
  induction n with
  | zero =>
    have h := cls_diag_add X 0 0
    simp only [add_zero] at h
    simp only [Nat.cast_zero, zero_smul]
    exact left_eq_add.1 h
  | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, cls_diag_add, ih, succ_nsmul]

theorem card_ker_act_le : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (X : Obj F 𝔠 (Sp Ω)), ∃ C : ℕ, ∀ (b : 𝓞 F) (k : ℕ), ((Algebra.norm ℤ b : ℤ) : Ω) ≠ 0 →
      IsTotPos (((k : F)) ^ 2 - (b : F) ^ 2) →
      Finite {y : 𝟙_ (Over (Sp Ω)) ⟶ X.A // y ≫ X.rm.act b = 1} ∧
      Nat.card {y : 𝟙_ (Over (Sp Ω)) ⟶ X.A // y ≫ X.rm.act b = 1} ≤ C * k ^ (2 * Module.finrank ℚ F) := by
  intro F _ _ _ 𝔠 Ω _ _ X
  have hB := X.ab
  haveI := hB.smooth
  haveI := hB.proper
  haveI : GeometricallyIntegral X.A.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hB.smooth hB.geomConnected
  haveI : IsIntegral X.A.left := GeometricallyIntegral.isIntegral_of_subsingleton X.A.hom
  obtain ⟨c, hc⟩ := fracId_exists_totPos F 𝔠
  have hLc : (X.diag c).IsLB := pull_isLB (X.isLB c) _
  obtain ⟨m, hm, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy Ω X.A (X.diag c) hLc).1 (X.pos c hc)
  have hH : (pw (X.diag c) m).IsLB := isLB_pw hLc _
  obtain ⟨hfin, -, c₀, C₀, -, hgrow⟩ :=
    GlobalTheory.VeryAmpleGrowth.finite_monotone_growth Ω X.A.left X.A.hom _ X.dim _ n s hH hs
  refine ⟨c₀ * C₀, fun b k hb hpos => ?_⟩
  obtain ⟨hfinφ, hetφ, hker⟩ := GlobalTheory.T.real_mult_isogeny_finite_etale X b hb
  refine ⟨hker, ?_⟩
  have hcard := GlobalTheory.finrank_eq_card_kernel_points_of_etale Ω X.A hB (X.rm.act b)
  have hk : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · exfalso
      obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
      have h0 := hpos (v.embedding_of_isReal (IsTotallyReal.isReal v))
      simp at h0
      nlinarith [sq_nonneg ((v.embedding_of_isReal (IsTotallyReal.isReal v)) (b : F))]
    · exact h
  set e : 𝓞 F := (k : 𝓞 F) ^ 2 - b ^ 2 with he
  have hce : IsTotPos (((e • c : 𝔠.elt)) : F) := by
    intro τ
    have h1 := hpos τ
    have h2 := hc τ
    have h3 : (((e • c : 𝔠.elt)) : F) = ((k : F) ^ 2 - (b : F) ^ 2) * (c : F) := by
      rw [Submodule.coe_smul, Algebra.smul_def, he]
      first | simp | (push_cast; norm_cast) | (congr 1; simp)
    rw [h3, map_mul]
    exact mul_pos h1 h2
  have hDe : (X.diag (e • c)).IsLB := pull_isLB (X.isLB _) _
  obtain ⟨m', hm', n', s', hs'⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy Ω X.A _ hDe).1 (X.pos _ hce)
  obtain ⟨x₀⟩ : Nonempty X.A.left := inferInstance
  obtain ⟨i₀, hi₀⟩ := TopologicalSpace.Opens.mem_iSup.1
    (show x₀ ∈ ⨆ i, Out.nonzeroLocus (s' i) by rw [hs'.1]; trivial)
  obtain ⟨n'', s'', hs''⟩ := GlobalTheory.AbLaw.veryAmpleBy_pw Ω X.A.left X.A.hom _ n s hH hs m' hm'
  have hsum : cls (X.diag ((b * b) • c)) (pull_isLB (X.isLB _) _) + cls (X.diag (e • c)) (pull_isLB (X.isLB _) _) =
      (k ^ 2 : ℕ) • cls (X.diag c) (pull_isLB (X.isLB _) _) := by
    rw [← cls_diag_add, ← add_smul, ← cls_diag_natCast_smul]
    congr 3
    rw [he]; push_cast; ring
  have hφ : (X.rm.act b).left ≫ X.A.hom = X.A.hom := Over.w _
  have key : ∀ t : ℕ,
      Module.Finite Ω (SecOnR ((X.rm.act b).left ≫ X.A.hom)
        ((pw (pw (pw (X.diag c) m) m') t).pull (X.rm.act b).left) ⊤) ∧
      Module.finrank Ω (SecOnR ((X.rm.act b).left ≫ X.A.hom)
        ((pw (pw (pw (X.diag c) m) m') t).pull (X.rm.act b).left) ⊤) ≤
        Module.finrank Ω (SecOnR X.A.hom (pw (pw (X.diag c) m) ((k ^ 2 * (m' * t) : ℕ) : ℤ)) ⊤) := by
    intro t
    rw [hφ]
    obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_section_power_nonvanishing s' i₀ hi₀ (m * t)
    have hLp : ((pw (pw (pw (X.diag c) m) m') t).pull (X.rm.act b).left).IsLB :=
      pull_isLB (isLB_pw (isLB_pw hH _) _) _
    have hD2 : (pw (pw (X.diag (e • c)) m') ((m * t : ℕ) : ℤ)).IsLB := isLB_pw (isLB_pw hDe _) _
    have hT : (pw (pw (X.diag c) m) ((k ^ 2 * (m' * t) : ℕ) : ℤ)).IsLB := isLB_pw hH _
    have hiso : LBIso (tens ((pw (pw (pw (X.diag c) m) m') t).pull (X.rm.act b).left)
        (pw (pw (X.diag (e • c)) m') ((m * t : ℕ) : ℤ))) (pw (pw (X.diag c) m) ((k ^ 2 * (m' * t) : ℕ) : ℤ)) := by
      rw [← cls_eq_iff (isLB_tens hLp hD2) hT, cls_tens hLp hD2,
        cls_pull (isLB_pw (isLB_pw hH _) _), GlobalTheory.AmpleStabFinite.cls_pw (isLB_pw hH _),
        GlobalTheory.AmpleStabFinite.cls_pw hH, GlobalTheory.AmpleStabFinite.cls_pw hLc, GlobalTheory.AmpleStabFinite.cls_pw (isLB_pw hDe _),
        GlobalTheory.AmpleStabFinite.cls_pw hDe, GlobalTheory.AmpleStabFinite.cls_pw hH, GlobalTheory.AmpleStabFinite.cls_pw hLc,
        map_zsmul, map_zsmul, map_zsmul, GlobalTheory.T.real_mult_pullback_polarization_class,
        eq_sub_of_add_eq hsum]
      push_cast
      module
    obtain ⟨w, hw⟩ := hiso
    have eqv := SecOnR.linEquiv X.A.hom (SecOn.congr (isLB_tens hLp hD2) hT w hw ⊤)
    haveI := hfin (k ^ 2 * (m' * t))
    haveI : Module.Finite Ω (SecOnR X.A.hom (tens ((pw (pw (pw (X.diag c) m) m') t).pull (X.rm.act b).left)
        (pw (pw (X.diag (e • c)) m') ((m * t : ℕ) : ℤ))) ⊤) := Module.Finite.equiv eqv.symm
    obtain ⟨h1, h2⟩ := GlobalTheory.T.finrank_sections_mono_tensor_effective X.A.hom hLp hD2 σ hσ inferInstance
    exact ⟨h1, h2.trans eqv.finrank_eq.le⟩
  have hpw : ∀ t : ℕ, pw (pw (pw (X.diag c) m) m') (t : ℤ) = pw (pw (X.diag c) m) ((m' * t : ℕ) : ℤ) := fun t => by
    rw [GlobalTheory.UU.TorsionCount.pw_pw, Nat.cast_mul]
  obtain ⟨a, ha⟩ := GlobalTheory.finrank_sec_pull_sandwich Ω X.A.left X.A.left X.A.hom (X.rm.act b).left
    (pw (pw (X.diag c) m) m') n'' s'' (isLB_pw hH _) hs'' _ hcard (fun t => by rw [hpw]; exact hfin _)
    (fun t => (key t).1)
  refine GlobalTheory.T.le_of_eventual_polynomial_growth _ _ a (Module.finrank ℚ F) fun N => ⟨max N 1, le_max_left _ _, ?_⟩
  set s₁ := max N 1 with hs₁
  have hs1 : 1 ≤ s₁ := le_max_right _ _
  have g1 := (hgrow (m' * s₁) (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)))).1
  have g2 := (ha s₁).1
  rw [hpw] at g2
  have g3 := (key (s₁ + a)).2
  have g4 := (hgrow (k ^ 2 * (m' * (s₁ + a)))
    (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by positivity) (Nat.mul_ne_zero (by omega) (by omega))))).2
  have hm'f : 0 < m' ^ Module.finrank ℚ F := by positivity
  refine Nat.le_of_mul_le_mul_right ?_ hm'f
  calc Nat.card {y : 𝟙_ (Over (Sp Ω)) ⟶ X.A // y ≫ X.rm.act b = 1} * s₁ ^ Module.finrank ℚ F * m' ^ Module.finrank ℚ F
      = Nat.card {y : 𝟙_ (Over (Sp Ω)) ⟶ X.A // y ≫ X.rm.act b = 1} * (m' * s₁) ^ Module.finrank ℚ F := by ring
    _ ≤ Nat.card {y : 𝟙_ (Over (Sp Ω)) ⟶ X.A // y ≫ X.rm.act b = 1} *
        (c₀ * Module.finrank Ω (SecOnR X.A.hom (pw (pw (X.diag c) m) ((m' * s₁ : ℕ) : ℤ)) ⊤)) := Nat.mul_le_mul_left _ g1
    _ = c₀ * (Nat.card {y : 𝟙_ (Over (Sp Ω)) ⟶ X.A // y ≫ X.rm.act b = 1} *
        Module.finrank Ω (SecOnR X.A.hom (pw (pw (X.diag c) m) ((m' * s₁ : ℕ) : ℤ)) ⊤)) := by ring
    _ ≤ c₀ * (C₀ * (k ^ 2 * (m' * (s₁ + a))) ^ Module.finrank ℚ F) :=
        Nat.mul_le_mul_left _ ((g2.trans g3).trans g4)
    _ = c₀ * C₀ * k ^ (2 * Module.finrank ℚ F) * (s₁ + a) ^ Module.finrank ℚ F * m' ^ Module.finrank ℚ F := by
        rw [mul_pow, mul_pow, ← pow_mul]; ring

end GlobalTheory.RealMultKernel
