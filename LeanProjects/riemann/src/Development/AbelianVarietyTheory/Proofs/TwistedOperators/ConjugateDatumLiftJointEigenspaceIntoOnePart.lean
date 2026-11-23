import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ConjScalarThm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsExistRow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFormEigenMemSinglePartStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateThetaLiftMatchedHeckeCombinationStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateSplittingUnramifiedHyperspecialFixStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalThetaCorrespondenceInertPlaceOfHoweStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaVacuumHeckeIdentitySplitPlace
import Formalism.LocalToGlobal.JointCharacters.LocEMulLocE
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardKerSubspacesAndHeckePolyOfConvolution

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjScalar.LiftPart
open GlobalTheory.Hk3

theorem tri_solve {X : Type} [AddCommGroup X] [Module ℂ X] (z : ℕ → ℕ → ℂ) (α : ℕ → ℂ) (hz : ∀ k, z k k ≠ 0) (m : ℕ) :
    ∃ β : ℕ → ℂ, ∀ (F : X) (T : ℕ → X), (∀ k, k < m → ∑ j ∈ Finset.range (k + 1), z k j • T j = α k • F) →
      ∀ k, k < m → T k = β k • F := by
  induction m with
  | zero => exact ⟨0, fun _ _ _ k hk => absurd hk (Nat.not_lt_zero _)⟩
  | succ m ih =>
    obtain ⟨β, hβ⟩ := ih
    refine ⟨Function.update β m ((z m m)⁻¹ * (α m - ∑ j ∈ Finset.range m, z m j * β j)), fun F T h k hk => ?_⟩
    have hlow : ∀ k, k < m → T k = β k • F := hβ F T fun k hk => h k (by omega)
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · rw [Function.update_of_ne (by omega)]
      exact hlow k hk
    · rw [Function.update_self]
      have e := h k (by omega)
      rw [Finset.sum_range_succ] at e
      have e2 : ∑ j ∈ Finset.range k, z k j • T j = (∑ j ∈ Finset.range k, z k j * β j) • F := by
        rw [Finset.sum_smul]
        exact Finset.sum_congr rfl fun j hj => by rw [hlow j (Finset.mem_range.1 hj), smul_smul]
      rw [e2] at e
      have e3 : z k k • T k = (α k - ∑ j ∈ Finset.range k, z k j * β j) • F := by
        rw [sub_smul, ← e]; abel
      rw [mul_smul, ← e3, smul_smul, inv_mul_cancel₀ (hz k), one_smul]

variable {D : D7}

theorem rep_of_not {V : HSp D} {P : Pl D.host.E} {d : List ℤ} (h : ¬ IsLab V P d) : GlobalTheory.Hk3.rep V P d = ∅ := by
  unfold GlobalTheory.Hk3.rep; rw [dif_neg h]

theorem hkF_evC (V : HSp D) {W : Type} [AddCommGroup W] [Module ℂ W] (P : Pl D.host.E) (a : List ℤ → ℂ)
    (Φ : Bridge.Gf V → W) (h : ∀ d, IsLab V P d → hkF V P (Finsupp.single d 1) Φ = a d • Φ) (c : List ℤ →₀ ℂ) :
    hkF V P c Φ = evC V P a c • Φ := by
  classical
  funext g
  have e : ∀ d, ∑ γ ∈ GlobalTheory.Hk3.rep V P d, Φ (g * (finHom V).rangeRestrict γ) = (if IsLab V P d then a d else 0) • Φ g := by
    intro d
    by_cases hd : IsLab V P d
    · have := congrFun (h d hd) g
      unfold hkF at this
      rw [Finsupp.sum_single_index (by simp), one_smul] at this
      rw [if_pos hd, this]; rfl
    · rw [if_neg hd, rep_of_not hd, Finset.sum_empty, zero_smul]
  simp only [hkF, evC, Finsupp.sum, Pi.smul_apply, Finset.sum_smul, e, smul_smul]
  refine Finset.sum_congr rfl fun d _ => ?_
  split_ifs <;> simp

theorem hk_splitC (V : HSp D) (P : Pl D.host.E) (n : ℕ) (z : ℕ → ℂ) :
    hk V P (splitC n z) = ∑ j ∈ Finset.range (n + 1), z j • hk V P (Finsupp.single (splitLab n j) 1) := by
  unfold splitC hk
  rw [← Finsupp.sum_finsetSum_index (by simp) (by simp [add_smul])]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp), one_smul]

theorem postOn_sum {V : HSp D} {S : _} (M : DSModel V S) (s : Finset ℕ) (w : ℕ → ℂ)
    (L : ℕ → (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (T : MMap M) :
    postOn M (∑ j ∈ s, w j • L j) T = ∑ j ∈ s, w j • postOn M (L j) T := by
  ext v
  simp [postOn]

theorem tri_solve' {X : Type} [AddCommGroup X] [Module ℂ X] (n : ℕ) (z : ℕ → ℕ → ℂ) (α : ℕ → ℂ) (hz : ∀ k, z k k ≠ 0) :
    ∃ β : ℕ → ℂ, ∀ (F : X) (T : ℕ → X),
      (∀ k, k ≤ n → α k • F = ∑ j ∈ Finset.range (n + 1), (if j ≤ k then z k j else 0) • T j) →
      ∀ k, k ≤ n → T k = β k • F := by
  obtain ⟨β, hβ⟩ := tri_solve (X := X) z α hz (n + 1)
  refine ⟨β, fun F T h k hk => hβ F T (fun k' hk' => ?_) k (by omega)⟩
  rw [h k' (by omega)]
  refine (Finset.sum_congr rfl fun j hj => ?_).trans
    (Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun j hj hj' => ?_)
  · rw [Finset.mem_range] at hj
    rw [if_pos (by omega)]
  · rw [Finset.mem_range] at hj hj'
    rw [if_neg (by omega), zero_smul]

theorem exists_split_data {P : Pl D.host.E} (hc : Formalism.DivisionValues.conjPl P ≠ P) : ∃ (e : AE D) (ϖ : 𝓞 D.host.E) (x : (AE D)ˣ),
    Formalism.L2.NTheta.IsIdemAt e P ∧ ϖ ∈ P.asIdeal ∧ ϖ ∉ P.asIdeal ^ 2 ∧ (x : AE D) = e * incA D (ϖ : D.host.E) + (1 - e) := by
  obtain ⟨e, he⟩ := GlobalTheory.Hk3.SplitMatch.exists_isIdemAt hc
  obtain ⟨ϖ, h1, h2⟩ : ∃ ϖ ∈ P.asIdeal, ϖ ∉ P.asIdeal ^ 2 :=
    SetLike.exists_of_lt (Ideal.pow_lt_self _ P.ne_bot P.isPrime.ne_top 2 le_rfl)
  have h0 : (ϖ : D.host.E) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.2 fun h => h2 (h ▸ zero_mem _)
  exact ⟨e, ϖ, Formalism.L2.JoinChr.locU he.1.1 (Units.mk0 _ h0), he, h1, h2, by
    rw [Formalism.L2.JoinChr.locU_val, Formalism.L2.JoinChr.locE, Units.val_mk0]; ring⟩

theorem diag_ne_zero (P : Pl D.host.E) (χS χT : (AE D)ˣ →* Circle) (x : (AE D)ˣ) (nS nT t k : ℕ) :
    (Ideal.absNorm P.asIdeal : ℂ) ^ ((nT - k) * (k - k)) * (Formalism.L2.Col.gaussBin (Ideal.absNorm P.asIdeal) t (k - k) : ℂ) *
      ((χT x : ℂ) * (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) ^ nT)⁻¹ ^ k *
      ((χS x : ℂ) * (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) ^ nS) ^ k ≠ 0 := by
  have hq0 : Ideal.absNorm P.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact P.ne_bot
  have hs0 : (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.sqrt_ne_zero'.2 (by exact_mod_cast Nat.pos_of_ne_zero hq0))
  have hT : (χT x : ℂ) ≠ 0 := Circle.coe_ne_zero _
  have hS : (χS x : ℂ) ≠ 0 := Circle.coe_ne_zero _
  rw [Nat.sub_self, mul_zero, pow_zero, one_mul, GlobalTheory.KerRangeCount.gaussBin_zero_right, Nat.cast_one, one_mul]
  exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero (mul_ne_zero hT (pow_ne_zero _ hs0))))
    (pow_ne_zero _ (mul_ne_zero hS (pow_ne_zero _ hs0)))

theorem dualC_dualC' (c : List ℤ →₀ ℂ) : dualC (dualC c) = c := by
  unfold dualC
  rw [← Finsupp.mapDomain_comp]
  have : dualLab ∘ dualLab = id := by
    funext d
    simp [dualLab, List.map_reverse]
  rw [this, Finsupp.mapDomain_id]

section Loc

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks]
  [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) {c : CoefA (Vc D i)}
  {H : HMod (Bridge.Gf (Vc D i) → c.W)} (th : H.H →ₗ[ℂ] (R.HW i σ).H) (μ' η' : (AE D)ˣ →* Circle)
  (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)) (P : Pl D.host.E)
  (a : Pl D.host.E → List ℤ → ℂ)

set_option maxHeartbeats 2000000 in

theorem loc_inert (hHowe : HoweUnram) (hW : IsWeilDatumO R.ψ (Vc D i) (Wc D i) μ' (μ' * η'⁻¹) ω) (hP : Good R A.μ0 P)
    (hvac : VacFix R.ψ ω P) (hc : Formalism.DivisionValues.conjPl P = P)
    (step : ∀ cV cW, Match R.ψ ω P (dualC cV) cW → ∀ y y' : H.H, H.e y' = hkF (Vc D i) P cV (H.e y) →
      (R.HW i σ).e (th y') = postOn (R.MW i σ) (hk (Wc D i) P cW) ((R.HW i σ).e (th y))) (d : List ℤ) :
    ∃ z : ℂ, ∀ u : H.H, EigF R i a (H.e u) →
      postOn (R.MW i σ) (hk (Wc D i) P (Finsupp.single d 1)) ((R.HW i σ).e (th u)) = z • (R.HW i σ).e (th u) := by
  have hsc := GlobalTheory.T.sphericalThetaCorrespondence_inertPlace_of_howe hHowe R.ψ (Vc D i) (Wc D i) μ' (μ' * η'⁻¹) ω P hW hc hvac
  have hcorr := hsc.2.1
  obtain ⟨cS, hM⟩ := hcorr (Finsupp.single d 1)
  refine ⟨evC (Vc D i) P (a P) (dualC cS), fun u hu => ?_⟩
  have hM' : Match R.ψ ω P (dualC (dualC cS)) (Finsupp.single d 1) := by rwa [dualC_dualC']
  have hy : H.e (evC (Vc D i) P (a P) (dualC cS) • u) = hkF (Vc D i) P (dualC cS) (H.e u) := by
    rw [map_smul, hkF_evC (Vc D i) P (a P) (H.e u) (fun d' hd' => hu P d' hP (Or.inr ⟨hc, hd'⟩))]
  have := step (dualC cS) (Finsupp.single d 1) hM' u _ hy
  rw [map_smul, map_smul] at this
  exact this.symm

set_option maxHeartbeats 2000000 in

theorem loc_split (hW : IsWeilDatumO R.ψ (Vc D i) (Wc D i) μ' (μ' * η'⁻¹) ω) (hP : Good R A.μ0 P)
    (hu1 : UnrPl P μ') (hu2 : UnrPl P (μ' * η'⁻¹)) (hc : Formalism.DivisionValues.conjPl P ≠ P)
    (step : ∀ cV cW, Match R.ψ ω P (dualC cV) cW → ∀ y y' : H.H, H.e y' = hkF (Vc D i) P cV (H.e y) →
      (R.HW i σ).e (th y') = postOn (R.MW i σ) (hk (Wc D i) P cW) ((R.HW i σ).e (th y))) (d : List ℤ)
    (hd : RelLab (Wc D i) P d) :
    ∃ z : ℂ, ∀ u : H.H, EigF R i a (H.e u) →
      postOn (R.MW i σ) (hk (Wc D i) P (Finsupp.single d 1)) ((R.HW i σ).e (th u)) = z • (R.HW i σ).e (th u) := by
  have hd' : ∃ k, k ≤ (Wc D i).rank ∧ d = splitLab (Wc D i).rank k := by
    rcases hd with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h hc
  obtain ⟨k, hkr, rfl⟩ := hd'
  have hdat := exists_split_data hc
  obtain ⟨e, ϖ, x, he, h1, h2, hx⟩ := hdat
  have hrk : (Vc D i).rank = (Wc D i).rank + D.R.t := by
    rw [D.sp.V_rank _ (Nat.le_add_left _ _) i.2, rank_Wc]; rfl
  have hms0 := GlobalTheory.Hk3.SplitMatch.match_split R.ψ (Vc D i) (Wc D i) μ' (μ' * η'⁻¹) ω P hW hc hu1 hu2
  have hms := (hms0.2 e ϖ x D.R.t he h1 h2 hx).2 hrk
  have htri := tri_solve' (X := MMap (R.MW i σ)) (Wc D i).rank
    (fun k j => (Ideal.absNorm P.asIdeal : ℂ) ^ (((Wc D i).rank - j) * (k - j)) *
      (Formalism.L2.Col.gaussBin (Ideal.absNorm P.asIdeal) D.R.t (k - j) : ℂ) *
      ((((μ' * η'⁻¹) x : Circle) : ℂ) * (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) ^ (Wc D i).rank)⁻¹ ^ k *
      (((μ' x : Circle) : ℂ) * (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) ^ (Vc D i).rank) ^ j)
    (fun k => a P (splitLab (Vc D i).rank k))
    (fun k => diag_ne_zero P μ' (μ' * η'⁻¹) x (Vc D i).rank (Wc D i).rank D.R.t k)
  obtain ⟨β, hβ⟩ := htri
  refine ⟨β k, fun u hu => hβ ((R.HW i σ).e (th u))
    (fun j => postOn (R.MW i σ) (hk (Wc D i) P (Finsupp.single (splitLab (Wc D i).rank j) 1)) ((R.HW i σ).e (th u)))
    (fun k' hk' => ?_) k hkr⟩
  have hy : H.e (a P (splitLab (Vc D i).rank k') • u) =
      hkF (Vc D i) P (Finsupp.single (splitLab (Vc D i).rank k') 1) (H.e u) := by
    rw [map_smul, hu P _ hP (Or.inl ⟨hc, k', by omega, rfl⟩)]
  have := step _ _ (hms k' (by omega)) u _ hy
  rw [map_smul, map_smul, hk_splitC, postOn_sum] at this
  exact this

end Loc

set_option maxHeartbeats 4000000 in

theorem lift_eig_mem_part : GlobalTheory.Hk3.HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ gramR c0R c0L, GlobalTheory.GalLift.Comparison₂ R gramR c0R c0L → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ → ∀ (μ' η' : (AE D)ˣ →* Circle) (th : H.H →ₗ[ℂ] (R.HW i σ).H), GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsConjDatum R i σ (c0L i) μ' η' c c₁ H j th → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.HypConj R i σ μ' η' → ∀ a : Pl D.host.E → List ℤ → ℂ, ∃ ev, ∀ u : H.H, GlobalTheory.ConjScalar.EigF R i a (H.e u) → th u ∈ GlobalTheory.LiftLower.partH R i σ ev := by
  intro hHowe D G _ _ Pl0 T0 A Ks _ _ _ R F hC gramR c0R c0L tie i σ c c₁ H j hK μ' η' th hD hyp a
  have hforms := hD.2.2.1
  have hlift := hD.2.2.2
  have h2 := (GlobalTheory.GalLift.isConjLift_iff R i σ μ' η' c H th).1 hlift
  obtain ⟨ω, f₀, f, B, io, thP, hh⟩ := h2
  have hLD := hh.1
  have hproj := hh.2
  have hW : IsWeilDatumO R.ψ (Vc D i) (Wc D i) μ' (μ' * η'⁻¹) ω := hLD.1
  have hVec : GlobalTheory.GalLift.VecData R i σ f₀ f B := hLD.2.1
  have loc : ∀ P, Good R A.μ0 P → ∀ d, RelLab (Wc D i) P d → ∃ z : ℂ, ∀ u : H.H, EigF R i a (H.e u) →
      postOn (R.MW i σ) (hk (Wc D i) P (Finsupp.single d 1)) ((R.HW i σ).e (th u)) = z • (R.HW i σ).e (th u) := by
    intro P hP d hd
    have h38 := GlobalTheory.T.conjugateSplitting_unramified_hyperspecial_fix R F hC i σ μ' η' hyp ω hW f₀ f B hVec P hP
    obtain ⟨hu1, hu2, hvac⟩ := h38
    have step : ∀ cV cW, Match R.ψ ω P (dualC cV) cW → ∀ y y' : H.H, H.e y' = hkF (Vc D i) P cV (H.e y) →
        (R.HW i σ).e (th y') = postOn (R.MW i σ) (hk (Wc D i) P cW) ((R.HW i σ).e (th y)) :=
      GlobalTheory.T.conjugate_theta_lift_matched_hecke_combination R F hC gramR c0R c0L tie i σ c c₁ H j hK hforms μ' η' th ω f₀ f B io thP hLD hproj P hP hvac
    by_cases hc : Formalism.DivisionValues.conjPl P = P
    · exact loc_inert R i σ th μ' η' ω P a hHowe hW hP hvac hc step d
    · exact loc_split R i σ th μ' η' ω P a hW hP hu1 hu2 hc step d hd
  classical
  let b : Pl D.host.E → List ℤ → ℂ := fun P d =>
    if h : Good R A.μ0 P ∧ RelLab (Wc D i) P d then (loc P h.1 d h.2).choose else 0
  obtain ⟨ev, hev⟩ := GlobalTheory.T.thetaForm_eigen_mem_single_part R hC.lev hC.models.HW i σ b
  refine ⟨ev, fun u hu => hev (th u) fun P d hP hd => ?_⟩
  simp only [b, dif_pos (And.intro hP hd)]
  exact (loc P hP d hd).choose_spec u hu

end GlobalTheory.ConjScalar.LiftPart
