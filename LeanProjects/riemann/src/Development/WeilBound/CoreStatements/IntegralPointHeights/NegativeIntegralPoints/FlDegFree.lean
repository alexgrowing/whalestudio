import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.RefLinked
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Exists
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GenFibreExists
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagDegreeWeightFormula
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LogIntegralMultilinearStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagHeightPolynomialWeightFormStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagVarietyBoundaryDimensionDropStatement
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverDegreeOneRealisationStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagVarietyArithmeticStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagVarietyModelBaseMetricStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticDataUniformisedStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RealisationPotentialDegreeCompatibilityStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.UniformisedDegreePolynomialAntisymmetricStatement
import Development.WeilBound.CoreStatements.PluriharmonicCharts.XCFlAn
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ExistsUnique
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SamePotBlock
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PLiftGraphFactor
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IsChainFirst
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IsBlockMapDrop
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagChainArithVarietyStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GenericFibreLinearEquationsStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FieldIntersectionLinearDegreeOneStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagChainUnitLogIntegralStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.SymmetricFormPolynomialCoeffStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.WeightMapInjectiveStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.WeightGapDeltaEqAntisymmetricStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RhoCoeffGapDeltaOneStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RhoFactorialProductEqStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.IndefiniteRowSideFullHecke.FlDegC

open GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Top.FlDeg
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.LowerBoundFree

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} {K : Type}

theorem arith [Fintype K] [Nonempty K] (j : K → FlBlock Ψ N) (hj : IsChain j) :
    IsArithVar (PPart j) (cellDim j + 1) := GlobalTheory.T.flag_chain_arith_variety Ψ N K j hj

theorem fibreLin [Fintype K] [DecidableEq K] (j : K → FlBlock Ψ N) (hj : IsChain j) (k₀ : K)
    (hmax : ∀ k, ((j k).2 : ℕ) ≤ (j k₀).2) (hne : ∃ k, k ≠ k₀) :
    ∃ G : GenFibre (dropV j k₀) (PPart j), ∃ S : Set (MRingOver G.Φ (fibreIdx (PIdx j) (Subtype.val : {k // k ≠ k₀} → K))),
      (∀ f ∈ S, IsMultiHomog f fun _ => 1) ∧ fibreIdeal (Subtype.val : {k // k ≠ k₀} → K) G = Ideal.span S :=
  GlobalTheory.T.generic_fibre_linear_equations Ψ N K j hj k₀ hmax hne

theorem linDeg {F : Type} [Field F] {K : Type} [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (k₀ : K)
    (hK : ∀ a : K, a = k₀) (J : IFamily F ι) (hJ : IsFieldIntersection J) (S : Set (MRingOver F ι))
    (hS : ∀ f ∈ S, IsMultiHomog f fun _ => 1) (r : ℕ) (hV : IsProjVarF (Ideal.span S) r) :
    J (Ideal.span S) r (fun _ _ => 1) = 1 := GlobalTheory.T.field_intersection_linear_degree_one F K ι k₀ hK J hJ S hS r hV

theorem base (II : IntersectionSystem) (hII : IsFullIntersectionSystem II) [Fintype K] [DecidableEq K] (k₀ : K)
    (hK : ∀ a : K, a = k₀) (j : K → FlBlock Ψ N) (hj : IsChain j) :
    ptsIntegral (PPart j) (pot fun _ : Fin (N - 1) => unitLine j k₀) (fun _ => 1) = 1 :=
  GlobalTheory.T.flag_chain_unit_log_integral Ψ N K II hII k₀ hK j hj

theorem coeff_formPoly_sym {σ : Type} [Fintype σ] [DecidableEq σ] (n : ℕ) (a : (Fin n → σ) → ℝ)
    (hsym : ∀ (π : Equiv.Perm (Fin n)) (w : Fin n → σ), a (w ∘ π) = a w) (w₀ : Fin n → σ) (m : σ →₀ ℕ)
    (hm : ∀ p, m p = (Finset.univ.filter fun r => w₀ r = p).card) :
    coeff m (PB.formPoly n a) * ∏ p, ((m p).factorial : ℝ) = (n.factorial : ℝ) * a w₀ :=
  GlobalTheory.T.symmetric_form_polynomial_coeff σ n a hsym w₀ m hm

theorem toWt_injective (Ψ : Type) (N : ℕ) :
    Function.Injective (PB.toWt : MvPolynomial (Ψ × Fin N) ℝ →ₐ[ℝ] MvPolynomial (Ψ × Fin N) ℝ) := GlobalTheory.T.weight_map_injective Ψ N

theorem toWt_gapDelta (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) :
    PB.toWt (gapDelta Ψ N) = GroundTheory.Heights₂.Heights.antisymDelta Ψ N := GlobalTheory.T.weight_gap_delta_eq_antisymmetric Ψ N

theorem coeff_gapDelta (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) : coeff (rhoM Ψ N) (gapDelta Ψ N) = 1 :=
  GlobalTheory.T.rho_coeff_gap_delta_one Ψ N

theorem prod_rhoM (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) :
    ∏ p, (((rhoM Ψ N) p).factorial : ℝ) =
      ∏ _τ : Ψ, ∏ i : Fin N, ∏ k : Fin N, (if i < k then ((k : ℝ) - (i : ℝ)) else 1) := GlobalTheory.T.rho_factorial_product_eq Ψ N

theorem fsHerm_smooth {K : Type} [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (a : K → ℤ) :
    IsSmoothHerm (fsHerm ι a) := by
  refine ContDiffOn.congr (GroundTheory.Heights₂.Heights.Targets.LiftGraphFactor.isSmoothHerm_fsLineZ (ι := ι) a) ?_
  intro z _
  show refNorm a z = ∏ k, GroundTheory.Heights₂.Heights.Targets.LiftGraphFactor.blkNorm z k ^ a k
  unfold refNorm GroundTheory.Heights₂.Heights.Targets.LiftGraphFactor.blkNorm
  refine Finset.prod_congr rfl fun k _ => ?_
  have h0 : 0 ≤ ∑ i, ‖z ⟨k, i⟩‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  rw [← sq_rpow_half (Real.sqrt_nonneg _), Real.sq_sqrt h0]

theorem constLine_smooth {K : Type} [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] :
    IsSmoothHerm (constLine ι) := by
  show ContDiffOn ℝ _ (fun _ => Real.exp (-(-1))) _
  exact contDiffOn_const

theorem ptsIntegral_neg_one {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) {e : ℕ}
    (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) :
    ptsIntegral P φ (fun _ => -1) = -ptsIntegral P φ (fun _ => 1) := by
  classical
  unfold ptsIntegral
  split_ifs with h
  · simp only [ptsIntegralAt]
    rw [← MeasureTheory.integral_neg]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show ∑ᶠ w ∈ fibre P h.choose y, sheetDensity P h.choose φ (fun _ => -1) y w =
      -∑ᶠ w ∈ fibre P h.choose y, sheetDensity P h.choose φ (fun _ => 1) y w
    rw [← finsum_neg_distrib]
    refine finsum_congr fun w => ?_
    rw [← finsum_neg_distrib]
    refine finsum_congr fun _ => ?_
    unfold sheetDensity
    split_ifs <;> simp
  · simp

theorem tie (II : IntersectionSystem) (hII : IsIntersectionSystem II) {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ) (L : Fin e → HermLine ι) (hP : IsArithVar P (e + 1))
    (hL : ∀ j, IsSmoothHerm (L j)) :
    II K ι P (e + 1) (Fin.cons (constLine ι) L) = ptsIntegral P (pot L) (fun _ => 1) := by
  obtain ⟨hs, -, hR⟩ := hII K ι
  have hT := constLine_smooth ι
  have hsm : ∀ i, IsSmoothHerm ((Fin.snoc L (constLine ι) : Fin (e + 1) → HermLine ι) i) := by
    intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simpa using hT
    · simpa using hL i
  have h1 : (1 : MRing ι) ∉ P := fun h => hP.2.1.1.ne_top ((Ideal.eq_top_iff_one P).2 h)
  have hsec := hR P e L (constLine ι) 1 (fun _ => 0) hP hL hT (fun k => by simp [constLine, HermLine.ofWeight])
    (fun m hm k => by
      classical
      have : m = 0 := by
        by_contra h0
        simp [MvPolynomial.support_one, h0] at hm
      simp [this]) h1
  have hperm := hs P (e + 1) (Fin.snoc L (constLine ι)) (finRotate (e + 1)).symm hP hsm
  have hc : (Fin.snoc L (constLine ι) : Fin (e + 1) → HermLine ι) ∘ (finRotate (e + 1)).symm =
      (Fin.cons (constLine ι) L : Fin (e + 1) → HermLine ι) := by
    rw [Fin.snoc_eq_cons_rotate]
    funext i
    simp
  rw [hc] at hperm
  rw [hperm, hsec]
  have hd : divSupp P (1 : MRing ι) = ∅ := by
    ext W
    simp only [divSupp, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hW
    have : (P ⊔ Ideal.span {(1 : MRing ι)}) = ⊤ := by simp
    rw [this] at hW
    exact absurd (hW.1.2 ) (by
      intro h
      exact hW.1.1.ne_top (top_le_iff.1 h))
  have hlog : logNorm (constLine ι) (1 : MRing ι) = fun _ => -1 := by
    funext z
    simp [logNorm, constLine, HermLine.ofWeight]
  have hz : recR (II K ι) P L (constLine ι) 1 = -arInt P 1 (constLine ι) L := by
    unfold recR
    rw [hd]
    simp
  rw [hz]
  unfold arInt
  rw [hlog]
  show -ptsIntegral P (pot L) (fun _ => -1) = _
  rw [ptsIntegral_neg_one, neg_neg]

theorem unitLine_smooth [Fintype K] [DecidableEq K] (j : K → FlBlock Ψ N) (k : K) : IsSmoothHerm (unitLine j k) :=
  fsHerm_smooth _ _

theorem isPull_unit [Fintype K] [DecidableEq K] (j : K → FlBlock Ψ N) (k₀ : K) (k : {k // k ≠ k₀}) :
    IsPullHerm (Subtype.val : {k // k ≠ k₀} → K) (dropV j k₀) (unitLine (dropJ j k₀) k) (unitLine j k.1) := by
  constructor
  · funext k'
    show (if k' = k.1 then (1 : ℤ) else 0) = Function.extend _ _ _ k'
    by_cases h : k' = k₀
    · subst h
      rw [Function.extend_apply' _ _ _ (by rintro ⟨x, hx⟩; exact x.2 hx), if_neg (Ne.symm k.2)]
      rfl
    · rw [show k' = ((⟨k', h⟩ : {k // k ≠ k₀}) : K) from rfl, Subtype.val_injective.extend_apply]
      show _ = if (⟨k', h⟩ : {k // k ≠ k₀}) = k then (1 : ℤ) else 0
      simp only [Subtype.ext_iff]
  · intro z
    have h1 := GlobalTheory.CompanionTheory.Ar.PB.FA.BlockPot.refNorm_block (isBlockMap_drop j k₀)
      (a := fun k' => if k' = k.1 then (1 : ℤ) else 0) (by
      intro k' hk'
      have : k' ≠ k.1 := fun h => hk' ⟨k, h.symm⟩
      simp [this]) z
    have h2 : (fun k' : {k // k ≠ k₀} => if k'.1 = k.1 then (1 : ℤ) else 0) = fun k' => if k' = k then 1 else 0 := by
      funext k'
      simp [Subtype.ext_iff]
    rw [h2] at h1
    exact h1

theorem isPull_const [Fintype K] [DecidableEq K] (j : K → FlBlock Ψ N) (k₀ : K) :
    IsPullHerm (Subtype.val : {k // k ≠ k₀} → K) (dropV j k₀) (constLine (PIdx (dropJ j k₀))) (constLine (PIdx j)) := by
  constructor
  · funext k'
    show (0 : ℤ) = Function.extend _ _ _ k'
    by_cases h : k' ∈ Set.range (Subtype.val : {k // k ≠ k₀} → K)
    · obtain ⟨x, rfl⟩ := h
      rw [Subtype.val_injective.extend_apply]
      rfl
    · rw [Function.extend_apply' _ _ _ (by simpa using h)]
      rfl
  · intro _
    rfl

theorem cellDim_drop [Fintype K] [DecidableEq K] (j : K → FlBlock Ψ N) (k₀ : K) :
    cellDim j = cellDim (dropJ j k₀) + (N - 1 - ((j k₀).2 : ℕ)) := by
  unfold cellDim dropJ
  rw [Fintype.sum_eq_add_sum_subtype_ne _ k₀, add_comm]

theorem isChain_drop (j : K → FlBlock Ψ N) (hj : IsChain j) (k₀ : K) (hmax : ∀ k, ((j k).2 : ℕ) ≤ (j k₀).2) :
    IsChain (dropJ j k₀) := by
  refine ⟨fun a b h => Subtype.ext (hj.inj h), fun k q h1 h2 => ?_⟩
  obtain ⟨k', rfl⟩ := hj.down k.1 q h1 h2
  have hne : k' ≠ k₀ := by
    rintro rfl
    apply k.2
    apply hj.inj
    have e : ((j k.1).2 : ℕ) = (j k').2 := le_antisymm (hmax _) h2
    exact Prod.ext h1.symm (Fin.ext e)
  exact ⟨⟨k', hne⟩, rfl⟩

theorem append_cons_eq {α : Type*} {a b : ℕ} (x : α) (u : Fin a → α) (v : Fin b → α) :
    (Fin.append (Fin.cons x u : Fin (a + 1) → α) v) =
      (Fin.cons x (Fin.append u v) : Fin (a + b + 1) → α) ∘ Fin.cast (by omega) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · rw [Fin.append_left]
    refine Fin.cases ?_ (fun i => ?_) i
    · have : Fin.cast (by omega : a + 1 + b = a + b + 1) (Fin.castAdd b (0 : Fin (a + 1))) = 0 := by
        ext; simp
      simp [this]
    · have : Fin.cast (by omega : a + 1 + b = a + b + 1) (Fin.castAdd b i.succ) = ((Fin.castAdd b i).succ) := by
        ext; simp
      simp only [Function.comp_apply, this, Fin.cons_succ, Fin.append_left]
  · have : Fin.cast (by omega : a + 1 + b = a + b + 1) (Fin.natAdd (a + 1) i) = ((Fin.natAdd a i).succ) := by
      ext; simp; omega
    simp only [Fin.append_right, Function.comp_apply, this, Fin.cons_succ]

theorem step (hIn : PB.Inputs) (II : IntersectionSystem) (hII : IsFullIntersectionSystem II) [Fintype K] [DecidableEq K]
    (j : K → FlBlock Ψ N) (hj : IsChain j) (k₀ : K) (hmax : ∀ k, ((j k).2 : ℕ) ≤ (j k₀).2) (hne : ∃ k, k ≠ k₀)
    (e₀ : ℕ) (w₀ : Fin e₀ → {k // k ≠ k₀}) (r : ℕ) (he : e₀ = cellDim (dropJ j k₀)) (hr : r = N - 1 - ((j k₀).2 : ℕ)) :
    ptsIntegral (PPart j) (pot (Fin.append (fun i => unitLine j (w₀ i).1) (fun _ : Fin r => unitLine j k₀)))
        (fun _ => 1) =
      ptsIntegral (PPart (dropJ j k₀)) (pot fun i => unitLine (dropJ j k₀) (w₀ i)) (fun _ => 1) := by
  classical
  have hc₀ := isChain_drop j hj k₀ hmax
  obtain ⟨k₁, hk₁⟩ := hne
  haveI : Nonempty {k // k ≠ k₀} := ⟨⟨k₁, hk₁⟩⟩
  haveI : Nonempty K := ⟨k₀⟩
  have hA₀ : IsArithVar (PPart (dropJ j k₀)) (e₀ + 1) := he ▸ arith _ hc₀
  have hAe : IsArithVar (PPart j) (e₀ + r + 1) := by
    have := arith j hj
    rwa [cellDim_drop j k₀, ← he, ← hr] at this
  have hA : IsArithVar (PPart j) (e₀ + 1 + r) := by
    rw [show e₀ + 1 + r = e₀ + r + 1 by omega]; exact hAe
  have hImg := imageZ_drop j k₀
  have hB := isBlockMap_drop j k₀
  obtain ⟨G, S, hS, hG⟩ := fibreLin j hj k₀ hmax ⟨k₁, hk₁⟩
  obtain ⟨J, hJ, -⟩ := GroundTheory.Heights₂.Heights.Targets.ExistsUnique.full G.Φ
    (fibreIdx (PIdx j) (Subtype.val : {k // k ≠ k₀} → K))
  have hsm₀ : ∀ i, IsSmoothHerm ((Fin.cons (constLine _) (fun i => unitLine (dropJ j k₀) (w₀ i)) :
      Fin (e₀ + 1) → HermLine (PIdx (dropJ j k₀))) i) := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa using constLine_smooth _
    · simpa using unitLine_smooth _ _
  have hpl : ∀ i, IsPullHerm (Subtype.val : {k // k ≠ k₀} → K) (dropV j k₀)
      ((Fin.cons (constLine _) (fun i => unitLine (dropJ j k₀) (w₀ i)) :
        Fin (e₀ + 1) → HermLine (PIdx (dropJ j k₀))) i)
      ((Fin.cons (constLine _) (fun i => unitLine j (w₀ i).1) : Fin (e₀ + 1) → HermLine (PIdx j)) i) := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa using isPull_const j k₀
    · simpa using isPull_unit j k₀ (w₀ i)
  have hPF := hIn.projFormula II hII.1 {k // k ≠ k₀} (PIdx (dropJ j k₀)) K (PIdx j) Subtype.val (dropV j k₀)
    (PPart j) (e₀ + 1) r G _ _ _ (fun _ => unitLine j k₀) hB hA (hImg ▸ hA₀) hJ hsm₀ hpl
    (fun _ => unitLine_smooth _ _)
  have hV := hIn.fibreDim {k // k ≠ k₀} (PIdx (dropJ j k₀)) K (PIdx j) Subtype.val (dropV j k₀)
    (PPart j) (e₀ + 1) r G hB hA (hImg ▸ hA₀)
  have hone : ∃ b : FibreBlock (Subtype.val : {k // k ≠ k₀} → K), ∀ a, a = b := by
    refine ⟨⟨k₀, by rintro ⟨x, hx⟩; exact x.2 hx⟩, fun a => Subtype.ext ?_⟩
    by_contra h
    exact a.2 ⟨⟨a.1, h⟩, rfl⟩
  obtain ⟨b, hb⟩ := hone
  have hdeg : (fun _ : Fin r => fibreDeg (Subtype.val : {k // k ≠ k₀} → K) (unitLine j k₀).a) = fun _ _ => 1 := by
    funext _ a
    have ha : a.1 = k₀ := by
      by_contra h
      exact a.2 ⟨⟨a.1, h⟩, rfl⟩
    show (if a.1 = k₀ then (1 : ℤ) else 0) = 1
    simp [ha]
  rw [hG] at hV
  have hval := linDeg _ b hb _ hJ S hS r hV
  rw [hdeg, hG, hval, hImg] at hPF
  have hT₀ := tie II hII.1 (PPart (dropJ j k₀)) e₀ (fun i => unitLine (dropJ j k₀) (w₀ i)) hA₀
    (fun _ => unitLine_smooth _ _)
  have hT := tie II hII.1 (PPart j) (e₀ + r)
    (Fin.append (fun i => unitLine j (w₀ i).1) (fun _ : Fin r => unitLine j k₀)) hAe (by
      intro i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa using unitLine_smooth _ _
      · simpa using unitLine_smooth _ _)
  rw [← hT₀, ← hT]
  have hcast : ∀ {n m : ℕ} (h : n = m) (M : Fin m → HermLine (PIdx j)),
      II K (PIdx j) (PPart j) n (M ∘ Fin.cast h) = II K (PIdx j) (PPart j) m M := by
    intro n m h M
    subst h
    rfl
  rw [← hcast (by omega : e₀ + 1 + r = e₀ + r + 1), ← append_cons_eq, hPF]
  simp

theorem count_append {α : Type} [DecidableEq α] {a b : ℕ} (u : Fin a → α) (v : Fin b → α) (k : α) :
    (Finset.univ.filter fun r => Fin.append u v r = k).card =
      (Finset.univ.filter fun r => u r = k).card + (Finset.univ.filter fun r => v r = k).card := by
  simp only [Finset.card_filter]
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]

theorem len_eq_cellDim [Fintype K] [DecidableEq K] (j : K → FlBlock Ψ N) {e : ℕ} (w : Fin e → K)
    (h : ∀ k, (Finset.univ.filter fun r => w r = k).card = N - 1 - ((j k).2 : ℕ)) : e = cellDim j := by
  have := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin e))) (t := (Finset.univ : Finset K))
    (f := w) (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
  simp only [Finset.card_univ, Fintype.card_fin] at this
  rw [this]
  exact Finset.sum_congr rfl fun k _ => h k

theorem tower (hIn : PB.Inputs) (II : IntersectionSystem) (hII : IsFullIntersectionSystem II) :
    ∀ (n : ℕ) (K : Type) [Fintype K] [DecidableEq K], Fintype.card K = n + 1 → ∀ j : K → FlBlock Ψ N, IsChain j →
      ∃ (e : ℕ) (w : Fin e → K), (∀ k, (Finset.univ.filter fun r => w r = k).card = N - 1 - ((j k).2 : ℕ)) ∧
        ptsIntegral (PPart j) (pot fun r => unitLine j (w r)) (fun _ => 1) = 1 := by
  intro n
  induction n with
  | zero =>
    intro K _ _ hc j hj
    obtain ⟨k₀, hk⟩ := Fintype.card_eq_one_iff.1 hc
    have h0 : ((j k₀).2 : ℕ) = 0 := by
      obtain ⟨k, hk'⟩ := hj.down k₀ ((j k₀).1, ⟨0, by have := (j k₀).2.2; omega⟩) rfl (by simp)
      rw [hk k] at hk'
      rw [hk']
    refine ⟨N - 1, fun _ => k₀, fun k => ?_, base II hII k₀ hk j hj⟩
    rw [hk k, h0]
    simp
  | succ n ih =>
    intro K _ _ hc j hj
    haveI : Nonempty K := Fintype.card_pos_iff.1 (by omega)
    obtain ⟨k₀, hmax⟩ := Finite.exists_max (fun k => ((j k).2 : ℕ))
    have hcard : Fintype.card {k // k ≠ k₀} = n + 1 := by
      have h := Fintype.card_subtype_compl (α := K) (fun k => k = k₀)
      rw [Fintype.card_subtype_eq] at h
      have h' : Fintype.card {k // k ≠ k₀} = Fintype.card K - 1 := by convert h
      omega
    obtain ⟨e₀, w₀, hcnt, hval⟩ := ih {k // k ≠ k₀} hcard (dropJ j k₀) (isChain_drop j hj k₀ hmax)
    have hne : ∃ k, k ≠ k₀ := by
      obtain ⟨x⟩ : Nonempty {k // k ≠ k₀} := Fintype.card_pos_iff.1 (by omega)
      exact ⟨x.1, x.2⟩
    have he := len_eq_cellDim (dropJ j k₀) w₀ hcnt
    refine ⟨e₀ + (N - 1 - ((j k₀).2 : ℕ)), Fin.append (fun i => (w₀ i).1) (fun _ => k₀), fun k => ?_, ?_⟩
    · rw [count_append]
      by_cases hk : k = k₀
      · subst hk
        have h1 : (Finset.univ.filter fun r => (w₀ r).1 = k) = ∅ := by
          ext r
          simpa using (w₀ r).2
        rw [h1]
        simp
      · have h1 : (Finset.univ.filter fun r => (w₀ r).1 = k) = Finset.univ.filter fun r => w₀ r = ⟨k, hk⟩ := by
          ext r
          simp [Subtype.ext_iff]
        have h2 : (Finset.univ.filter fun _ : Fin (N - 1 - ((j k₀).2 : ℕ)) => k₀ = k) = ∅ :=
          Finset.filter_false_of_mem fun _ _ => Ne.symm hk
        rw [h1, h2, hcnt ⟨k, hk⟩]
        simp [dropJ]
    · have hs := step hIn II hII j hj k₀ hmax hne e₀ w₀ _ he rfl
      rw [hval] at hs
      have hfun : (fun r => unitLine j (Fin.append (fun i => (w₀ i).1) (fun _ : Fin (N - 1 - ((j k₀).2 : ℕ)) => k₀) r)) =
          Fin.append (fun i => unitLine j (w₀ i).1) (fun _ : Fin (N - 1 - ((j k₀).2 : ℕ)) => unitLine j k₀) := by
        funext i
        refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp
      rw [hfun]
      exact hs

theorem alg_const (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (D : ℕ)
    (a : (Fin D → Ψ × Fin N) → ℝ) (c : ℝ) (w₀ : Fin D → Ψ × Fin N)
    (hcnt : ∀ p : Ψ × Fin N, (Finset.univ.filter fun r => w₀ r = p).card = N - 1 - (p.2 : ℕ))
    (hsym : ∀ (π : Equiv.Perm (Fin D)) (w : Fin D → Ψ × Fin N), a (w ∘ π) = a w) (h1 : a w₀ = 1)
    (h : PB.toWt (PB.formPoly D a) = C c * GroundTheory.Heights₂.Heights.antisymDelta Ψ N) :
    c * ∏ _τ : Ψ, ∏ i : Fin N, ∏ k : Fin N, (if i < k then ((k : ℝ) - (i : ℝ)) else 1) = (D.factorial : ℝ) := by
  have hG : PB.formPoly D a = C c * gapDelta Ψ N := by
    apply toWt_injective Ψ N
    rw [h, map_mul, toWt_gapDelta]
    simp [PB.toWt]
  have h2 := coeff_formPoly_sym D a hsym w₀ (rhoM Ψ N) (fun p => by
    rw [hcnt p]
    rfl)
  rw [hG, coeff_C_mul, coeff_gapDelta, h1, prod_rhoM] at h2
  simpa using h2

open GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights in
theorem degFl_vand (hIn : PB.Inputs) (II : IntersectionSystem) (hII : IsFullIntersectionSystem II) (Ψ : Type) [Fintype Ψ]
    [DecidableEq Ψ] [Nonempty Ψ] (N : ℕ) (hN : 2 ≤ N) : ∃ c : ℝ, degFlPoly Ψ N = C c * antisymDelta Ψ N := by
  obtain ⟨M, BM, hhom, hfs, hbd⟩ := GlobalTheory.T.flag_variety_model_base_metric Ψ N hN
  have hpos : 1 ≤ antisymDegree Ψ N := Nat.mul_pos Fintype.card_pos (Nat.choose_pos hN)
  obtain ⟨d, hd⟩ : ∃ d, d + 1 = antisymDegree Ψ N := ⟨antisymDegree Ψ N - 1, by omega⟩
  have harith : IsArithVar (mCoordIdeal (yFl Ψ N)) (d + 2) := by
    have := GlobalTheory.T.flag_variety_arithmetic Ψ N hN
    rw [← hd] at this
    exact this
  have hdim : d + 1 = 0 + Fintype.card Ψ * (N.choose 2 + (N - N).choose 2) := by
    simpa [antisymDegree] using hd
  obtain ⟨FA, -⟩ := PositivityTheory.Xgp.t_c_fl_an _ _ _ (yFl Ψ N) Ψ N N M 0 d BM harith hdim hbd
    (fun p => (hhom p).trans (hfs p).symm)
  obtain ⟨Cv, CR, hdeg, href, -⟩ := GlobalTheory.T.flag_cover_degree_one_realisation _ _ _ (yFl Ψ N) Ψ N N M 0 d BM FA
  have hU := GlobalTheory.T.flag_analytic_data_uniformised _ _ _ (yFl Ψ N) Ψ N N M 0 d BM FA (by simp) hd
  have hdeg1 : CR.Re.deg = 1 := by rw [CR.deg_eq, hdeg]
  have href1 : ∀ p, CR.Re.ref p = yLineFl Ψ N p := fun p => by rw [href, FA.ref_some, hfs]
  have hP := (GlobalTheory.T.flag_variety_boundary_dimension_drop Ψ N hN).1
  have hR := GlobalTheory.T.realisation_potential_degree_compatibility hIn.2.1.1 _ _ _ _ (FA.S.comap some) _ CR.Re
  have hw : ∀ w : Fin (d + 1) → Ψ × Fin N,
      ptsIntegral (PFl Ψ N) (pot fun r => yLineFl Ψ N (w r)) (fun _ => 1) = (FA.S.comap some).degNum w := by
    intro w
    have := hR.2.1 w
    simp only [href1, hdeg1] at this
    simpa [PFl] using this
  obtain ⟨c, -, hc'⟩ := GlobalTheory.T.uniformised_degree_polynomial_antisymmetric hIn Ψ N N (d + 1) (FA.S.comap some) le_rfl hd hU
  refine ⟨c, Eq.trans ?_ hc'⟩
  rw [(GlobalTheory.T.flag_height_polynomial_weight_form hIn II hII Ψ N hN hP).2, AnSys.degPoly]
  congr 1
  rw [← hd]
  congr 1
  funext w
  exact hw w

end GlobalTheory.CompanionTheory.Ar.IndefiniteRowSideFullHecke.FlDegC

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Top.FlDeg GlobalTheory.CompanionTheory.Ar.IndefiniteRowSideFullHecke.FlDegC

namespace GlobalTheory.CompanionTheory.Ar.IndefiniteRowSideFullHecke

theorem degFlPoly_eval' : PB.Inputs → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) [Nonempty Ψ] (lam : Wt Ψ N), 2 ≤ N → eval (fun x => lam x.1 x.2) (PB.degFlPoly Ψ N) = flagDeg lam := by
  intro hIn II hII Ψ _ _ N _ lam hN
  obtain ⟨c, hC⟩ := degFl_vand hIn II hII Ψ N hN
  have hAr := (GlobalTheory.T.flag_variety_boundary_dimension_drop Ψ N hN).1
  have hL := (GlobalTheory.T.flag_height_polynomial_weight_form hIn II hII Ψ N hN hAr).2
  have hchain : IsChain (id : FlBlock Ψ N → FlBlock Ψ N) := ⟨Function.injective_id, fun _ q _ _ => ⟨q, rfl⟩⟩
  haveI hK : Nonempty (FlBlock Ψ N) := ⟨(Classical.arbitrary Ψ, ⟨0, by omega⟩)⟩
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card (FlBlock Ψ N) = n + 1 :=
    ⟨Fintype.card (FlBlock Ψ N) - 1, by have := Fintype.card_pos (α := FlBlock Ψ N); omega⟩
  obtain ⟨e, w, hcnt, hval⟩ := tower hIn II hII n (FlBlock Ψ N) hn id hchain
  have he : e = antisymDegree Ψ N := by
    have h1 := (arith (id : FlBlock Ψ N → FlBlock Ψ N) hchain).2.2.2
    have h2 := hAr.2.2.2
    have h3 : ringKrullDim (MRing (FlIdx Ψ N) ⧸ PFl Ψ N) = ((cellDim (id : FlBlock Ψ N → FlBlock Ψ N) + 1 + Fintype.card (FlBlock Ψ N) : ℕ) : WithBot ℕ∞) := h1
    rw [h3] at h2
    have h4 : cellDim (id : FlBlock Ψ N → FlBlock Ψ N) + 1 + Fintype.card (FlBlock Ψ N) = antisymDegree Ψ N + 1 + Fintype.card (FlBlock Ψ N) := by
      exact_mod_cast h2
    rw [len_eq_cellDim id w hcnt]
    omega
  subst he
  let pr : FlBlock Ψ N → Ψ × Fin N := fun q => (q.1, ⟨q.2, by have := q.2.2; omega⟩)
  have hpr : ∀ q, PB.yLineFl Ψ N (pr q) = unitLine (id : FlBlock Ψ N → FlBlock Ψ N) q := by
    intro q
    show fsHerm _ _ = fsHerm _ _
    congr 1
    funext q'
    simp [pr, Prod.ext_iff, Fin.ext_iff]
  let a : (Fin (antisymDegree Ψ N) → Ψ × Fin N) → ℝ := fun w' =>
    ptsIntegral (PFl Ψ N) (pot fun r => PB.yLineFl Ψ N (w' r)) fun _ => 1
  have ha : a (fun r => pr (w r)) = 1 := by
    show ptsIntegral (PFl Ψ N) (pot fun r => PB.yLineFl Ψ N (pr (w r))) (fun _ => 1) = 1
    simp only [hpr]
    exact hval
  have hsmY : ∀ p, IsSmoothHerm (PB.yLineFl Ψ N p) := fun p => fsHerm_smooth _ _
  have hsym : ∀ (π : Equiv.Perm (Fin (antisymDegree Ψ N))) (w' : Fin (antisymDegree Ψ N) → Ψ × Fin N),
      a (w' ∘ π) = a w' := by
    intro π w'
    have := (GlobalTheory.T.log_integral_multilinear II hII (FlBlock Ψ N) (FlIdx Ψ N) (PFl Ψ N) (antisymDegree Ψ N) Unit
      (fun _ => fsHerm (FlIdx Ψ N) 0) (fun _ _ => 0) hAr (fun _ => fsHerm_smooth _ _)).2
      (fun r => PB.yLineFl Ψ N (w' r)) (fun r => PB.yLineFl Ψ N (w' (π r))) π (fun _ => hsmY _) (fun _ => hsmY _)
      (fun _ => rfl)
    exact this
  have hcnt' : ∀ p : Ψ × Fin N, (Finset.univ.filter fun r => pr (w r) = p).card = N - 1 - (p.2 : ℕ) := by
    rintro ⟨τ, i⟩
    by_cases hi : (i : ℕ) < N - 1
    · have : (Finset.univ.filter fun r => pr (w r) = (τ, i)) = Finset.univ.filter fun r => w r = (τ, ⟨i, hi⟩) := by
        ext r
        simp [pr, Prod.ext_iff, Fin.ext_iff]
      rw [this, hcnt]
      rfl
    · have : (Finset.univ.filter fun r => pr (w r) = (τ, i)) = ∅ := by
        ext r
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        intro h
        have h2 := congrArg (fun x : Ψ × Fin N => (x.2 : ℕ)) h
        have := (w r).2.2
        simp only [pr] at h2
        omega
      rw [this]
      simp
      omega
  have hcst := alg_const Ψ N (antisymDegree Ψ N) a c (fun r => pr (w r)) hcnt' hsym ha (hL ▸ hC)
  obtain ⟨hW, -, -⟩ := flagDeg_eq_weyl Ψ N lam
  have hdim : Top.dimFl Ψ N = antisymDegree Ψ N := by
    simp [Top.dimFl, antisymDegree, Nat.choose_two_right]
  have hΔ : eval (fun x : Ψ × Fin N => lam x.1 x.2) (antisymDelta Ψ N) =
      ∏ τ, ∏ a : Fin N, ∏ b ∈ Finset.Ioi a, (lam τ a - lam τ b) := by
    simp [antisymDelta, map_prod]
  have hsplit : ∏ τ, ∏ i : Fin N, ∏ k : Fin N, (if i < k then (lam τ i - lam τ k) / ((k : ℝ) - (i : ℝ)) else 1) =
      (∏ τ, ∏ a : Fin N, ∏ b ∈ Finset.Ioi a, (lam τ a - lam τ b)) /
        ∏ _τ : Ψ, ∏ i : Fin N, ∏ k : Fin N, (if i < k then ((k : ℝ) - (i : ℝ)) else 1) := by
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hI : Finset.Ioi i = Finset.univ.filter fun k => i < k := by
      ext k
      simp
    rw [hI, Finset.prod_filter, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    split_ifs <;> simp
  rw [hC, map_mul, eval_C, hW, hdim, hsplit, hΔ]
  have hPr : (∏ _τ : Ψ, ∏ i : Fin N, ∏ k : Fin N, (if i < k then ((k : ℝ) - (i : ℝ)) else 1)) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hcst
    exact (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)) hcst.symm
  rw [← hcst]
  field_simp

end GlobalTheory.CompanionTheory.Ar.IndefiniteRowSideFullHecke
