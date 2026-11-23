import Formalism.SharpRestriction.LevelLetterCocycles.AdmBoundsBOfAdm
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcGamLiftCore
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.InIOfMemPi0Lattice

noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln17

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Module
open Formalism.MainNotions.N.FrobeniusPowerSeries
open Formalism.MainNotions.N.Ln17.PCutBoundRep Formalism.MainNotions.N.Ln17.PCutBoundRho Formalism.MainNotions.N.Ln17.PCutBoundGal

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

theorem arc_length_bound_theorem [Fintype (K →ₐ[Qp] LL)] (W : LocWach PD LL O v n)
    (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hl : 5 ≤ PD.p) (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x))
    (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x) (hinj : Function.Injective (algebraMap O LL))
    (hRelay : RelayCore W) (hArc : ArcCore W) (hNN : UnivNNCore W) (hUniv : UnivCore PD W)
    (hKLev : KillerLevCore W) (hKMod : KillerModCore W)
    (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u)
    (A : ArcP n) (hA : A.OK) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (hsur : Formalism.MainNotions.LiftingTheory.Sur W F) (hW₁ : Win W A T₁) (hW₂ : Win W A T₂) (m : ℕ)
    (hm : ∀ i, (A.ty i).thick → Formalism.MainNotions.TruncatedSeriesCountingBounds.lowCount W T₂ i A.η ≤ m)
    (c : ZMod n) (hc : c ∈ A.cuts) (e₁ : ℕ) (he₁ : A.σ PD.p ≤ e₁)
    (hARC : ∀ (d : ℕ) (bb : Fin d → W.DD T₂) (sol : Fin d → ℕ → Fin d → LL),
      IsHor W T₂ (c - ((A.len c : ℕ) : ZMod n)) bb sol → ∀ k₀, InLpp W A T₂ c bb k₀ →
      ∀ f, InFF W A c f → LiftsAt W A F c bb sol k₀ f e₁) :
    ∃ Zc : Finset (LatticeCohomology T₂.L), Zc.card ≤ m * Formalism.MainNotions.LocalTheoryWindows.ro A.ty A.len c * (A.len c + 1) ∧
      (∀ z ∈ Zc, z ∈ latticeFiniteCohomology PD T₂.L) ∧
      ∀ (w : W.DD T₂) (x : LatticeCohomology T₂.L), InI W T₂ c w →
        InFP W T₂ (c - ((A.len c : ℕ) : ZMod n)) (A.len c) 1 (abelian₂ W A c (A.len c) • w) →
        (∀ (d : ℕ) (bb : Fin d → W.DD T₂) (sol : Fin d → ℕ → Fin d → LL),
          IsHor W T₂ (c - ((A.len c : ℕ) : ZMod n)) bb sol → PoleOK W A T₂ c bb sol w) →
        IsRho W A T₂ c w x →
        (((PD.p : ℕ) : O) ^ (A.σ PD.p + kapC PD.p A c + e₁)) • x ∈
          (latticeFiniteCohomology PD T₁.L).map F.H1map ⊔ Submodule.span O (Zc : Set (LatticeCohomology T₂.L)) := by
  classical
  have hjle : A.j ≤ A.len c := hA.2.2.2.1 c hc
  have hcrys₂ : IsCrys PD T₂.ρ := hW₂.1
  have hR : GS.RD W := by
    have hfr : Module.finrank K₀ K = 1 := by
      have e : K₀ ≃ₗ[K₀] K := LinearEquiv.ofBijective (Algebra.linearMap K₀ K) hcase.1
      rw [← e.finrank_eq, Module.finrank_self]
    exact GS.rd_of W ((hP9 T₂ hcrys₂ hcase.2.1 hcase.2.2).2.2 hfr).1
  have hΛγ := γ_Lam hR A c (A.len c)
  have hAc := hArc hcase hl A hA c hc (A.len c) hjle le_rfl
  simp only [sub_add_cancel] at hAc
  obtain ⟨hJJ, hAT⟩ := hAc
  obtain ⟨hPN, hNP, -, hfr⟩ := hAT T₂ hW₂
  have hM : ∃ u ∈ W.AΔ, ((W.φA ^ A.len c) W.π₀) ^ A.M PD.p = W.π₀ * abelian₂ W A c (A.len c) ^ 2 * u := by
    obtain ⟨u, hu, hue⟩ := hJJ
    have h2 : 2 * A.G₀ ≤ (PD.p - 1) * A.M PD.p := by
      have hGh : A.G₀ ≤ A.h := hA.2.2.2.2.2.1
      have hp1 : 0 < PD.p - 1 := by omega
      have h3 := Nat.lt_mul_div_succ (2 * A.h) hp1
      show 2 * A.G₀ ≤ (PD.p - 1) * (2 * A.h / (PD.p - 1) + 1)
      exact le_trans (by omega : 2 * A.G₀ ≤ 2 * A.h) h3.le
    obtain ⟨t, ht, hte⟩ := φpow_π₀_JJ hR A.j (A.M PD.p) A.G₀ h2
    refine ⟨u * (W.φA ^ (A.len c - A.j)) t, W.AΔ.mul_mem hu (TypesA.φA_pow_mem W ht _), ?_⟩
    have hsplit : (W.φA ^ A.len c) W.π₀ = (W.φA ^ (A.len c - A.j)) ((W.φA ^ A.j) W.π₀) := by
      rw [← AlgHom.mul_apply, ← pow_add, Nat.sub_add_cancel hjle]
    rw [hsplit, ← map_pow, hte, map_mul, hue]
    ring
  obtain ⟨d, b, sol, Rst, hb, -, hLpp, -, hWcl, ⟨g₀, J, hg₀, hJ, hJspan⟩, hlift⟩ :=
    hUniv hcase hl A m hA T₂ hW₂ hm c hc
  obtain ⟨-, -, -, -, hNLx, h0, -⟩ := hfr d b sol hb
  have hRT := (hRelay hcase hl A hA c hc).1 T₂ hW₂
  have hΛPs : abelian₂ W A c (A.len c) ∈ Ps W := by
    unfold abelian₂
    exact prod_mem fun s _ => pow_mem (by unfold Ps; exact Submonoid.subset_closure (Set.mem_range_self s)) _
  have rAdd : ∀ {w₁ w₂ : W.DD T₂} {x₁ x₂ : LatticeCohomology T₂.L}, InI W T₂ c w₁ → InI W T₂ c w₂ →
      IsRho W A T₂ c w₁ x₁ → IsRho W A T₂ c w₂ x₂ → IsRho W A T₂ c (w₁ + w₂) (x₁ + x₂) :=
    fun h1 h2 h3 h4 => rho_add hRelay hcase hl hA hc hW₂ h1 h2 h3 h4
  have rSmul : ∀ {w₁ : W.DD T₂} {x₁ : LatticeCohomology T₂.L}, InI W T₂ c w₁ → IsRho W A T₂ c w₁ x₁ → ∀ o : O,
      IsRho W A T₂ c (o • w₁) (o • x₁) :=
    fun h1 h2 o => rho_smul hRelay hcase hl hA hc hW₂ h1 h2 o
  have rZero : ∀ {w₁ : W.DD T₂}, InI W T₂ c w₁ → InFNc W T₂ c W.π₀ w₁ → IsRho W A T₂ c w₁ 0 :=
    fun h1 h2 => isRho_zero_of_pi0 hRelay hcase hl hA hc hW₂ h1 h2

  have hZ : ∀ i, ∃ u, InI W T₂ c u ∧
      InFP W T₂ (c - ((A.len c : ℕ) : ZMod n)) (A.len c) 1 (abelian₂ W A c (A.len c) • u) ∧
      RepVV W T₂ (c - ((A.len c : ℕ) : ZMod n)) (A.len c) (A.M PD.p) (abelian₂ W A c (A.len c)) b sol u
        (fun k => lE W (A.σ PD.p) * J i k) := fun i => hlift (J i) (hJ i).1 (hJ i).2.2
  choose uJ huJI huJP huJR using hZ
  have hxJ : ∀ i, ∃ x, IsRho W A T₂ c (uJ i) x := fun i => rho_ex hRelay hcase hl hA hc hW₂ (huJI i)
  choose xJ hxJ using hxJ
  have hxJf : ∀ i, xJ i ∈ latticeFiniteCohomology PD T₂.L := by
    intro i
    obtain ⟨y, hy, hyΛ⟩ := huJP i
    refine (hRT.2.1 _ (huJI i)).2.2.2.2.2.2 (abelian₂ W A c (A.len c) * abelian₂ W A c (A.len c)) _
      (mul_mem hΛPs hΛPs) ?_ (hxJ i)
    rw [mul_smul, hyΛ, one_smul]
    exact hPN y hy
  refine ⟨Finset.univ.image xJ, ?_, ?_, ?_⟩
  · refine Finset.card_image_le.trans ?_
    rw [Finset.card_univ, Fintype.card_fin]
    exact hg₀
  · intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hz
    exact hxJf i
  intro w x hI hP hPole hρ
  obtain ⟨f, hfΛ, hfR, hfn, hInv'', hInvr⟩ := hWcl w hI hP (hPole d b sol hb)
  have h00 := RepVV_zero W hfR

  have hLift : ∀ k ∈ Finset.univ.filter (fun k => k ∉ Rst),
      LV W A F c b sol (fun k' => if k' = k then PPγ W (A.len c) (A.JS c) (f k) else 0) e₁ := by
    intro k hk
    have hk' : k ∉ Rst := (Finset.mem_filter.1 hk).2
    exact LV_of_lifts (hARC d b sol hb k (hLpp k hk') _ ⟨(hfn k hk').2.2.2.1, (hfn k hk').2.2.2.2⟩)
  have hLV : LV W A F c b sol (fun k => if k ∈ Rst then 0 else PPγ W (A.len c) (A.JS c) (f k)) e₁ :=
    LV_congr (LV_sum h00 _ _ hLift) fun k' => by
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, ite_not]
  have hf''Fr : ∀ k, InFr W c 1 (abelian₂ W A c (A.len c))
      (if k ∈ Rst then 0 else PPγ W (A.len c) (A.JS c) (f k)) := by
    intro k
    split_ifs
    · exact InFr_zero W
    · exact InFr_aeval W hR A (hfΛ k) _
  have hfrFr : ∀ k, InFr W c 1 (abelian₂ W A c (A.len c))
      (if k ∈ Rst then PPγ W (A.len c) (A.JS c) (f k) else 0) := by
    intro k
    split_ifs
    · exact InFr_aeval W hR A (hfΛ k) _
    · exact InFr_zero W
  obtain ⟨u'', hu''I, hu''P, hu''R⟩ := hlift _ hf''Fr hInv''
  obtain ⟨ur, hurI, hurP, hurR⟩ := hlift _ hfrFr hInvr
  obtain ⟨x'', hx''⟩ := rho_ex hRelay hcase hl hA hc hW₂ hu''I
  obtain ⟨x₁, hx₁f, hx₁⟩ := LV_galois hA hc hRelay hArc hcase hl hW₁ hW₂ hb he₁ hLV u'' hu''I hu''P hu''R
    x'' hx''

  obtain ⟨o, g, hgNL, hog⟩ := hJspan _ hfrFr (fun k hk => if_neg hk) hInvr
  obtain ⟨x₀, hx₀N, hx₀R⟩ := hNLx g hgNL
  have hsumI : InI W T₂ c (∑ i, o i • uJ i) := InI_sum W _ _ fun i _ => InI_smulO W _ (huJI i)
  have hsumR := RepVV_sum W h00 Finset.univ (fun i => o i • uJ i)
    (fun i k => algebraMap O W.EE (o i) * (lE W (A.σ PD.p) * J i k)) fun i _ => RepVV_smulO W (o i) (huJR i)
  have hsumρ : IsRho W A T₂ c (∑ i, o i • uJ i) (∑ i, o i • xJ i) :=
    rho_sum hRelay hcase hl hA hc hW₂ _ _ _ (fun i _ => InI_smulO W _ (huJI i))
      fun i _ => rSmul (huJI i) (hxJ i) (o i)
  have hπx₀ : InFNc W T₂ c W.π₀ (W.π₀ • x₀) := by
    obtain ⟨y, hy, hyc, rfl⟩ := hx₀N
    exact ⟨y, hy, hyc, by rw [one_smul]⟩
  have hπx₀I : InI W T₂ c (W.π₀ • x₀) := inI_of_mem_pi0_lattice W hcrys₂ hP2 hpi0 hπx₀
  have hDR : RepVV W T₂ (c - ((A.len c : ℕ) : ZMod n)) (A.len c) (A.M PD.p) (abelian₂ W A c (A.len c)) b sol
      (ur - ∑ i, o i • uJ i - W.π₀ • x₀) 0 := by
    refine TypesA.RepVV_congr W (TypesA.RepVV_add W (TypesA.RepVV_add W hurR (TypesA.RepVV_neg W hsumR))
      (TypesA.RepVV_neg W (RepVV_smulA W (TypesA.pi0_mem_ADelta W) hx₀R))) (by abel) fun k => ?_
    rw [Pi.zero_apply]
    have h2 : ∑ i, algebraMap O W.EE (o i) * (lE W (A.σ PD.p) * J i k) =
        lE W (A.σ PD.p) * ∑ i, algebraMap O W.EE (o i) * J i k := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h2]
    linear_combination (lE W (A.σ PD.p)) * hog k
  have hDP : InFP W T₂ (c - ((A.len c : ℕ) : ZMod n)) (A.len c) 1
      (abelian₂ W A c (A.len c) • (ur - ∑ i, o i • uJ i - W.π₀ • x₀)) := by
    rw [smul_sub, smul_sub, Finset.smul_sum]
    refine TypesA.inMultiple_sub W (TypesA.inMultiple_sub W hurP (inMultiple_sum W _ _ fun i _ => ?_)) ?_
    · rw [← algebraMap_smul (LetA O n) (o i) (uJ i), smul_comm]
      exact TypesA.inMultiple_smul W (W.AΔ.algebraMap_mem _) (huJP i)
    · rw [smul_comm]
      exact TypesA.inMultiple_smul W (TypesA.pi0_mem_ADelta W) (hNP x₀ hx₀N)
  obtain ⟨yD, hyD, hDy⟩ := h0 _ hDP hDR
  obtain ⟨yD', hyD', hycD, hΛyD⟩ := hPN yD hyD
  have hDπ : InFNc W T₂ c W.π₀ (ur - ∑ i, o i • uJ i - W.π₀ • x₀) :=
    ⟨yD', hyD', hycD, by rw [hDy, mul_smul, hΛyD, one_smul]⟩
  have hDI := inI_of_mem_pi0_lattice W hcrys₂ hP2 hpi0 hDπ
  have hurρ : IsRho W A T₂ c ur (∑ i, o i • xJ i) := by
    have h1 := rAdd (TypesA.InI_add W hDI hsumI) hπx₀I (rAdd hDI hsumI (rZero hDI hDπ) hsumρ)
      (rZero hπx₀I hπx₀)
    have e : ur - ∑ i, o i • uJ i - W.π₀ • x₀ + ∑ i, o i • uJ i + W.π₀ • x₀ = ur := by abel
    rwa [e, zero_add, add_zero] at h1

  have hwI' : InI W T₂ c (lA W ^ A.σ PD.p • w) :=
    InI_smulA W (TypesA.lA_pow_mem W _) (γA_lA W _) hI
  have hwρ' : IsRho W A T₂ c (lA W ^ A.σ PD.p • w) (((PD.p : ℕ) : O) ^ A.σ PD.p • x) := by
    have h1 := rSmul hI hρ (((PD.p : ℕ) : O) ^ A.σ PD.p)
    rwa [TypesA.pO_smul] at h1
  have hPγI : InI W T₂ c (Polynomial.aeval (W.γ T₂) (PPO W (A.len c) (A.JS c)) (lA W ^ A.σ PD.p • w)) :=
    InI_aeval W hcrys₂ hP2 hpi0 hwI' _
  have hPγR : RepVV W T₂ (c - ((A.len c : ℕ) : ZMod n)) (A.len c) (A.M PD.p) (abelian₂ W A c (A.len c)) b sol
      (Polynomial.aeval (W.γ T₂) (PPO W (A.len c) (A.JS c)) (lA W ^ A.σ PD.p • w))
      (fun k => PPγ W (A.len c) (A.JS c) (f k)) :=
    RepVV_aeval W hcrys₂ hP2 hpi0 hb hΛγ hM hfR _
  have hKM := hKMod hcase T₂ c (A.len c) (A.JS c) _ hcrys₂ hwI'.1 hwI'.2.2
  have hP1I : InI W T₂ c ((PPO W (A.len c) (A.JS c)).eval 1 • (lA W ^ A.σ PD.p • w)) := InI_smulO W _ hwI'
  have hdI : InI W T₂ c (Polynomial.aeval (W.γ T₂) (PPO W (A.len c) (A.JS c)) (lA W ^ A.σ PD.p • w) -
      (PPO W (A.len c) (A.JS c)).eval 1 • (lA W ^ A.σ PD.p • w)) := by
    rw [sub_eq_add_neg]
    exact TypesA.InI_add W hPγI (TypesA.InI_neg W hP1I)
  have hPγρ : IsRho W A T₂ c (Polynomial.aeval (W.γ T₂) (PPO W (A.len c) (A.JS c)) (lA W ^ A.σ PD.p • w))
      ((PPO W (A.len c) (A.JS c)).eval 1 • (((PD.p : ℕ) : O) ^ A.σ PD.p • x)) := by
    have h1 := rAdd hdI hP1I (rZero hdI hKM) (rSmul hwI' hwρ' _)
    rwa [sub_add_cancel, zero_add] at h1
  have hσPγI := InI_smulA W (TypesA.lA_pow_mem W (A.σ PD.p)) (γA_lA W _) hPγI
  have hσPγρ : IsRho W A T₂ c (lA W ^ A.σ PD.p •
      Polynomial.aeval (W.γ T₂) (PPO W (A.len c) (A.JS c)) (lA W ^ A.σ PD.p • w))
      (((PD.p : ℕ) : O) ^ A.σ PD.p • ((PPO W (A.len c) (A.JS c)).eval 1 • (((PD.p : ℕ) : O) ^ A.σ PD.p • x))) := by
    have h1 := rSmul hPγI hPγρ (((PD.p : ℕ) : O) ^ A.σ PD.p)
    rwa [TypesA.pO_smul] at h1

  have hD2R : RepVV W T₂ (c - ((A.len c : ℕ) : ZMod n)) (A.len c) (A.M PD.p) (abelian₂ W A c (A.len c)) b sol
      (lA W ^ A.σ PD.p • Polynomial.aeval (W.γ T₂) (PPO W (A.len c) (A.JS c)) (lA W ^ A.σ PD.p • w) - u'' - ur)
      0 := by
    refine TypesA.RepVV_congr W (TypesA.RepVV_add W (TypesA.RepVV_add W
      (RepVV_smulA W (TypesA.lA_pow_mem W (A.σ PD.p)) hPγR) (TypesA.RepVV_neg W hu''R))
      (TypesA.RepVV_neg W hurR)) (by abel) fun k => ?_
    rw [Pi.zero_apply]
    have hlE : algebraMap (LetA O n) W.EE (lA W ^ A.σ PD.p) = lE W (A.σ PD.p) := by
      simp [lA, lE]
    rw [hlE]
    split_ifs <;> ring
  have hD2P : InFP W T₂ (c - ((A.len c : ℕ) : ZMod n)) (A.len c) 1 (abelian₂ W A c (A.len c) •
      (lA W ^ A.σ PD.p • Polynomial.aeval (W.γ T₂) (PPO W (A.len c) (A.JS c)) (lA W ^ A.σ PD.p • w) - u'' - ur)) := by
    have hwP : InFP W T₂ (c - ((A.len c : ℕ) : ZMod n)) (A.len c) 1
        (abelian₂ W A c (A.len c) • (lA W ^ A.σ PD.p • w)) := by
      rw [smul_comm]
      exact TypesA.inMultiple_smul W (TypesA.lA_pow_mem W _) hP
    have hPγP := InFPΛ_aeval W hcrys₂ hP2 hΛγ hwP (PPO W (A.len c) (A.JS c))
    rw [smul_sub, smul_sub, smul_comm (abelian₂ W A c (A.len c)) (lA W ^ A.σ PD.p)]
    exact TypesA.inMultiple_sub W (TypesA.inMultiple_sub W (TypesA.inMultiple_smul W (TypesA.lA_pow_mem W _) hPγP) hu''P) hurP
  obtain ⟨y2, hy2, hD2y⟩ := h0 _ hD2P hD2R
  obtain ⟨y2', hy2', hyc2, hΛy2⟩ := hPN y2 hy2
  have hD2π : InFNc W T₂ c W.π₀
      (lA W ^ A.σ PD.p • Polynomial.aeval (W.γ T₂) (PPO W (A.len c) (A.JS c)) (lA W ^ A.σ PD.p • w) - u'' - ur) :=
    ⟨y2', hy2', hyc2, by rw [hD2y, mul_smul, hΛy2, one_smul]⟩
  have hD2I := inI_of_mem_pi0_lattice W hcrys₂ hP2 hpi0 hD2π
  have hsum2 := rAdd (TypesA.InI_add W hD2I hu''I) hurI (rAdd hD2I hu''I (rZero hD2I hD2π) hx'') hurρ
  have e2 : ∀ a₁ a₂ a₃ : W.DD T₂, a₁ - a₂ - a₃ + a₂ + a₃ = a₁ := fun _ _ _ => by abel
  rw [e2] at hsum2
  have hEq := rho_uniq hRelay hcase hl hA hc hW₂ hσPγI hσPγρ hsum2

  obtain ⟨yk, hyk⟩ := pk_eq W hOv hinj (kapC PD.p A c) ((PPO W (A.len c) (A.JS c)).eval 1)
    (hKLev hcase (A.len c) (A.JS c)).1
  have hexp : (((PD.p : ℕ) : O) ^ (A.σ PD.p + kapC PD.p A c + e₁)) • x =
      yk • ((((PD.p : ℕ) : O) ^ (e₁ - A.σ PD.p)) • (((PD.p : ℕ) : O) ^ A.σ PD.p •
        ((PPO W (A.len c) (A.JS c)).eval 1 • (((PD.p : ℕ) : O) ^ A.σ PD.p • x)))) := by
    rw [smul_smul, smul_smul, smul_smul, smul_smul]
    congr 1
    have he : A.σ PD.p + kapC PD.p A c + e₁ = kapC PD.p A c + (e₁ - A.σ PD.p) + A.σ PD.p + A.σ PD.p := by
      omega
    rw [he, pow_add, pow_add, pow_add, hyk]
    ring
  rw [hexp, hEq]
  refine Submodule.smul_mem _ _ ?_
  rw [smul_add, smul_add, smul_zero, zero_add]
  refine Submodule.add_mem _ (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right ?_)
  · rw [← hx₁]
    exact Submodule.mem_map_of_mem hx₁f
  · refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_))
    exact Finset.mem_coe.2 (Finset.mem_image_of_mem xJ (Finset.mem_univ i))

end Core

end Formalism.MainNotions.N.Ln17
