import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.DualRef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsComb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumLifts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsCompModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSmoothFunctionCInfAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetricStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArTopOfInduced
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsDualBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsPullbackAlongCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverRefinementGenericDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometricOfSameNormsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommonRefinementOfCoverAndModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedOfPositiveNormsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularMetricConjugationInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalModelForRootMetricsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CombinedAdelicMetricIdentityStatement

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArSelfObj

section Generic

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ArInt ReciprocityTheory.AnForm.M

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

theorem π_genericPoint (V : Cover Y) : V.π (genericPoint V.G) = genericPoint Y.X := by
  have h := (genericPoint_spec V.G).image V.π.continuous
  rw [Set.image_univ, V.π.surjective.range_eq, closure_univ] at h
  exact h.eq (genericPoint_spec Y.X)

theorem selfInter_eq (hA : GlobalTheory.Published.ArCalc) (V : Cover Y) (M : TrueGeo.Model Y)
    (hM : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.X) {N : HermLB V.p} {N₀ : HermLB M.p} {f : Y.X → Y.Fn}
    {a : ∀ σ : F →+* ℂ, Pts Y σ → ℝ} {l : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ}
    (h : Norms V N f a l) (h₀ : Norms (Cover.ofModel M hM) N₀ f a l) {s t : ℝ} (hs : N.IsSelfInter s)
    (ht : haveI := M.ar.isIntegral; N₀.IsSelfInter t) : s = V.deg * t := by
  have := M.ar.isIntegral
  obtain ⟨V', α, g, β, hα, hβ, e₁, e₂, e₃, e₄⟩ := GlobalTheory.T.common_refinement_of_cover_and_model F Y V M
  have hg₀ : V'.π ≫ (Cover.ofModel M hM).π = V'.π := Category.comp_id _
  have n₁ := GlobalTheory.T.norms_pullback_along_cover F Y V V' α hα g e₁ e₂ e₃ N f a l h
  have n₂ := GlobalTheory.T.norms_pullback_along_cover F Y (Cover.ofModel M hM) V' β hβ V'.π e₄ hg₀ (π_genericPoint V') N₀ f a l h₀
  obtain ⟨g₁, d₁⟩ := GlobalTheory.T.cover_refinement_generic_degree F Y V V' α hα g e₁ e₂ e₃
  obtain ⟨g₂, d₂⟩ := GlobalTheory.T.cover_refinement_generic_degree F Y (Cover.ofModel M hM) V' β hβ V'.π e₄ hg₀ (π_genericPoint V')
  rw [Cover.deg_ofModel, mul_one] at d₂
  have hd := V'.deg_pos
  have p₁ : α.residueDegree (genericPoint V'.X) ≠ 0 := fun e => by rw [e, zero_mul] at d₁; omega
  have p₂ : β.residueDegree (genericPoint V'.X) ≠ 0 := fun e => hd.ne' (d₂.symm.trans e)
  have s₁ := (hA.arProj _ V.X V'.X V.p V'.p _ V.ar V'.ar α hα g₁ p₁).1 N s hs
  have s₂ := (hA.arProj _ M.X V'.X M.p V'.p _ M.ar V'.ar β hβ g₂ p₂).1 N₀ t ht
  obtain ⟨η, hη, e⟩ := s₁
  have s₃ : (N₀.pull β hβ).IsSelfInter _ :=
    ⟨η, (hA.arIso _ V'.X V'.p _ V'.ar).1 _ _ η (GlobalTheory.T.isometric_of_same_norms F Y V' _ _ f a l n₁ n₂) hη, e⟩
  have key := HermLB.IsSelfInter.unique V'.ar s₃ s₂
  have d₃ : ((β.residueDegree (genericPoint V'.X) : ℕ) : ℝ) = (α.residueDegree (genericPoint V'.X) : ℕ) * V.deg := by
    rw [← Nat.cast_mul, d₁]; exact congrArg _ d₂
  rw [d₃, mul_assoc] at key
  exact mul_left_cancel₀ (Nat.cast_ne_zero.2 p₁) key

variable {e : ℕ} {M : Man e} {I : ManIs M Y} {V : Cover Y}
  {ε : (𝓞 F →+* ℂ) → Fin (M.n + 1)} {π : ∀ σ, CxPts V.p σ → M.X (ε σ)}

theorem down_eq (hd : V.IsDown I ε π) {σ : 𝓞 F →+* ℂ} (y' : CxPts V.p σ) {z : Sp ℂ ⟶ V.G} (h : y'.1 = z ≫ V.j) :
    (I.pt _ (π σ y')).1 = z ≫ V.π := by
  have := CoverHt.isPreimmersion_j V
  obtain ⟨w, h₁, h₂⟩ := (hd σ).2 y'
  have h₃ : w = z := by rw [← cancel_mono V.j, h₁, h]
  rw [← h₂, h₃]

omit [NumberField F] in

theorem val_congr (g : ∀ σ : F →+* ℂ, Pts Y σ → ℝ) {σ σ' : F →+* ℂ} {y : Pts Y σ} {y' : Pts Y σ'} (h : y.1 = y'.1) :
    g σ y = g σ' y' := by
  have h₁ : spMap σ = spMap σ' := by rw [← y.2, ← y'.2, h]
  obtain rfl : σ = σ' := congrArg CommRingCat.Hom.hom (Spec.map_injective h₁)
  rw [Subtype.ext h]

theorem pull_eq (hd : V.IsDown I ε π) {u : M.Fun} {g : ∀ σ : F →+* ℂ, Pts Y σ → ℝ}
    (hu : ∀ a x, u a x = g _ (I.pt a x)) (σ : F →+* ℂ) (z : CxPts (V.π ≫ Y.str) σ) (y : Pts Y σ)
    (y' : CxPts V.p (σ.comp (algebraMap (𝓞 F) F))) (h₁ : y.1 = z.1 ≫ V.π) (h₂ : y'.1 = z.1 ≫ V.j) :
    M.pull ε π ((2 : ℝ) • u) _ y' = 2 * g σ y := by
  change 2 * u _ _ = _
  rw [hu, val_congr g ((down_eq hd y' h₂).trans h₁.symm)]

theorem pull_conj (hd : V.IsDown I ε π) {u : M.Fun} {g : ∀ σ : F →+* ℂ, Pts Y σ → ℝ}
    (hu : ∀ a x, u a x = g _ (I.pt a x))
    (hg : ∀ σ σ' (y : Pts Y σ) (y' : Pts Y σ'), y'.1 = spMap (starRingEnd ℂ) ≫ y.1 → g σ' y' = g σ y) (σ σ' : 𝓞 F →+* ℂ) :
    (Weight.ofFun (M.pull ε π ((2 : ℝ) • u) σ)).IsConj (Weight.ofFun (M.pull ε π ((2 : ℝ) • u) σ')) := by
  intro _ z z' h _
  obtain ⟨w, h₁, h₂⟩ := (hd σ).2 z
  change 2 * u _ _ = 2 * u _ _
  rw [hu, hu, hg _ _ _ _ ((down_eq hd z' (z := spMap (starRingEnd ℂ) ≫ w) (by rw [h, Category.assoc, h₁])).trans
    (by rw [Category.assoc, h₂]))]

theorem top_smul (K : Calc M) (c : ℝ) (v : K.V) : K.top (c • v) = c ^ (e + 1) * K.top v := by
  have := K.num.map_smul_univ (fun _ => c) fun _ => v
  simpa [Calc.top] using this

theorem arTop_eq (hA : GlobalTheory.Published.ArCalc) (hD : GlobalTheory.Published.ArDegree) (hdim : Y.dim = e) (hd : V.IsDown I ε π)
    {B : Adl (cxSt F) Y} {ι : Type} [Fintype ι] {ρ : ι → Adl (cxSt F) Y} {t : ι → ℝ} {g : ∀ σ : F →+* ℂ, Pts Y σ → ℝ}
    (hB : IsComb B ρ t g)
    (hg : ∀ σ σ' (y : Pts Y σ) (y' : Pts Y σ'), y'.1 = spMap (starRingEnd ℂ) ≫ y.1 → g σ' y' = g σ y)
    {u : M.Fun} (hs : M.Smooth u) (hu : ∀ a x, u a x = g _ (I.pt a x))
    (P : TrueGeo.Model Y) (hP : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme P.X) (L₀ : ι → HermLB P.p) (m : ℕ+)
    (h₀ : ∀ i, (ρ i).Induced P (L₀ i) m 0) (L : ι → HermLB V.p) (x c : ι → ℤ) (k : ℕ) (hk : 0 < k)
    (hx : ∀ i, c i * x i = k)
    (hL : ∀ i, Norms V (L i) (fun y => genAt (ρ i).D y ^ x i) (fun σ y => x i * lnAdl (ρ i) σ y)
      fun v w y => x i * (ρ i).lg v w y)
    (K : Calc M) (v : ι → K.V) (hK : K.NumOn ε π V.ν L v) :
    B.arTop = K.top (∑ i, (t i / (x i * ((ρ i).n : ℕ))) • v i + K.ar u) := by
  subst hdim
  have := P.ar.isIntegral
  obtain ⟨q, b, hq, hb, h₁, h₂, h₃⟩ := hB
  have hs2 : M.Smooth ((2 : ℝ) • u) := fun σ j => (hs σ j).const_smul (2 : ℝ)
  obtain ⟨ε₀, π₀, hd₀⟩ := (Cover.ofModel P hP).exists_isDown I
  have n₀ := GlobalTheory.T.combined_adelic_metric_identity F Y (Cover.ofModel P hP) B ι ρ g q b hq h₁ h₂ h₃ (m * k) (fun _ => ((m : ℕ) : ℤ))
    (fun i => k * b i) (fun i => by push_cast; ring) L₀
    (fun i => (norms_of_induces (Cover.induces_ofModel hP (h₀ i))).congr (fun _ => (zpow_natCast _ _).symm)
      (fun _ _ => by rw [Int.cast_natCast]) fun _ _ _ => by rw [Int.cast_natCast])
    _ (OnModelCInf.cInfAt_pull F Y _ _ M I ε₀ π₀ hd₀ _ hs2) (pull_conj hd₀ hu hg) (pull_eq hd₀ hu)
  have n₁ := GlobalTheory.T.combined_adelic_metric_identity F Y V B ι ρ g q b hq h₁ h₂ h₃ (m * k) x
    (fun i => (m : ℕ) * c i * b i) (fun i => by push_cast; rw [← hx i]; ring) L hL
    _ (OnModelCInf.cInfAt_pull F Y _ _ M I ε π hd _ hs2) (pull_conj hd hu hg) (pull_eq hd hu)
  let κ : ℕ+ := ⟨m * k * q, Nat.mul_pos (Nat.mul_pos m.2 hk) hq⟩
  have hI := GlobalTheory.T.induced_of_positive_norms F _ Y B P hP _ κ (fun σ z => (h₂ σ z).1) n₀
  obtain ⟨η, hη⟩ := (hA.arExists _ P.X P.p Y.dim P.ar).1 _
  have e₀ := (arTop_of_induced hA hD F _ Y B P _ κ 0 hI).2 _ ⟨η, hη, rfl⟩
  obtain ⟨Φ, hΦ⟩ := ((hA.arExists _ V.X V.p Y.dim V.ar).2 _ fun o : Option ι => o.elim (fnB (M.pull ε π ((2 : ℝ) • u))
    (OnModelCInf.cInfAt_pull F Y _ _ M I ε π hd _ hs2) (pull_conj hd hu hg)) L).1
  have e₁ := selfInter_eq hA V P hP n₁ n₀ (hΦ.1 _) ⟨η, hη, rfl⟩
  rw [hK u hs _ _ Φ hΦ] at e₁
  have hx' (i) : (c i : ℝ) * x i = k := by exact_mod_cast hx i
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have e₂ : ∑ i, ((((m : ℕ) : ℤ) * c i * b i : ℤ) : ℝ) • v i + (((m * k * q * (B.n : ℕ) : ℕ) : ℤ) : ℝ) • K.ar u =
      (((κ : ℕ) : ℝ) * (B.n : ℕ)) • (∑ i, (t i / (x i * ((ρ i).n : ℕ))) • v i + K.ar u) := by
    rw [smul_add, Finset.smul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul]
      congr 1
      have hn : (((ρ i).n : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (ρ i).n.ne_zero
      have hxi : (x i : ℝ) ≠ 0 := fun h => hk' (by rw [← hx' i, h, mul_zero])
      change _ = ((m * k * q : ℕ) : ℝ) * _ * _
      push_cast
      field_simp
      linear_combination (-(k : ℝ)) * hb i + (b i : ℝ) * ((ρ i).n : ℕ) * hx' i
    · change _ = (((m * k * q : ℕ) : ℝ) * _) • _
      push_cast
      rfl
  simp only [Option.elim] at e₁
  rw [e₂, top_smul, Cover.ν] at e₁
  have hκ : (((κ : ℕ) : ℝ) * (B.n : ℕ)) ^ (Y.dim + 1) ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero (Nat.cast_ne_zero.2 κ.ne_zero) (Nat.cast_ne_zero.2 B.n.ne_zero))
  have hF : (Module.finrank ℚ F : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have hV : (V.deg : ℝ) ≠ 0 := Nat.cast_ne_zero.2 V.deg_pos.ne'
  rw [e₀]
  simp only [Pi.zero_apply, finsum_zero, mul_zero, add_zero]
  rw [div_div, div_eq_iff (mul_ne_zero hκ hF)]
  apply mul_left_cancel₀ hV
  rw [← e₁]
  ring

end Generic

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.FlagPoly GlobalTheory.FlagAr

theorem sum_single {D : D7} {Y : ShimX D.what₂.Tau} (T : Real0 Y) (B : ℝ) (c : Y.Comp) (w : Wt Y) :
    ∑ x : D.what₂.Tau × Fin Y.N, w x.1 x.2 • T.L B c (Pi.single x.1 (Pi.single x.2 1)) = T.L B c w := by
  simp_rw [← map_smul]
  rw [← map_sum]
  congr 1
  ext σ i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single σ, Finset.sum_eq_single i]
  · simp
  · intro b _ hb; simp [hb.symm]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · simp

theorem arSelf_onObj : Hypotheses2 → HypothesesH → OnObj fun _ O A T _ _ => ∀ B : ℝ, 2 ≤ B → ∀ (u : Wt O.Y) (s : ℚ), IsRat O.Y u → 0 < s → Dominant O.Y (A.sh u s) → (∀ c, (T.M c).Smooth ((T.F c).phS (A.sh u s) s)) → ∀ c, O.Y.arSelfC (O.Y.Mbar B u s) c = (T.K B c).top (T.L B c (A.sh u s) + (s : ℝ) • T.a B c + (T.K B c).ar ((T.F c).phS (A.sh u s) s)) := by
  intro hP hH D O hO _ A T H h B hB u s hu hs hdom hsm c
  have hsh : A.sh u s = fun τ i => u τ i - s * O.met.dir τ i := by
    rw [← h.aux.dir]; rfl
  have hc := hO.mbIs B hB u s hu hs (A.sh u s) hsh hdom c
  obtain ⟨P, hP₀, L₀, m, h₀⟩ := GlobalTheory.T.normal_model_for_root_metrics D O hO B hB c
  obtain ⟨W, hW⟩ : ∃ W : O.LatModel (FlagAr.setB O.Y B) c, O.NumIs (h.man c) B W := ⟨_, h.num B hB c⟩
  obtain ⟨ε, π, hd⟩ := W.V.exists_isDown (h.man c)
  have key := arTop_eq hP.p4 hH.deg ((O.dim_eq c).trans rfl : (O.var c).dim = dimY O.Y) hd hc
    (fun σ σ' y y' e => congrArg (· / 2) (GlobalTheory.T.regular_metric_conjugation_invariant D O hO c σ σ' _ _ y y' e)) (hsm c)
    ((h.an c).phS _ _ (by exact_mod_cast hs)) P hP₀ L₀ m h₀ (W.gens (FlagAr.setB O.Y B))
    (fun o => o.elim (W.k : ℤ) fun _ => -1) (fun o => o.elim 1 fun _ => -(W.k : ℤ)) W.k W.k_pos
    (by rintro (_ | x) <;> simp)
    (by
      rintro (_ | x)
      · exact (CoverNorm.norms_of_induces W.amp_spec).congr (fun _ => (zpow_natCast _ _).symm)
          (fun _ _ => by simp) fun _ _ _ => by simp
      · exact (GlobalTheory.T.norms_dual_bundle _ _ _ _ _ _ _ (CoverNorm.norms_of_induces
          (GlobalTheory.T.lattice_model_induces_root_metric D O hO.dualRef _ c W _ subset_rfl x))).congr (fun _ => by simp)
          (fun _ _ => by simp) fun _ _ _ => by simp)
    (T.K B c) (T.gen B c W.mult) (hW ε π hd)
  refine key.trans ?_
  congr 2
  rw [Fintype.sum_option, add_comm]
  congr 1
  · rw [← sum_single T B c (A.sh u s)]
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 1
    change -A.sh u s x.1 x.2 / (((-1 : ℤ) : ℝ) * ((1 : ℕ) : ℝ)) = _
    simp
  · have hn : (((O.met.ab c).n : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (O.met.ab c).n.ne_zero
    have hk : (W.k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 W.k_pos.ne'
    simp only [Option.elim, Real0.gen, Setup.LatModel.mult, smul_smul]
    congr 1
    push_cast
    field_simp

end GlobalTheory.ArSelfObj
