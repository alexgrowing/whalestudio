import Mathlib
import Formalism.LocalToGlobal.GroupLattices.DownNaturalLevelZero
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.BaseMatrixGlApply
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiPinnedWithFinIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstVertexIteratedLevelChainInFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymmetricPositionLevelShapeOnParabolic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceIdempotentUnderEqOfLiesOver
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnifUnit
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelPrimeSplitsCompletelyInCmField
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdeleCharacterEqOneIntegralUnitsUnramifiedAdelic

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LatPair GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (CharUnramAt)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (colGroup colChar)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.LevelTest

variable {D : D7} {u : D.what₂.Word} {a : XPart D u} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] {ι : Type} (o : OffX a k ι) (G : ∀ PP : a.c.Pg, GX a o.ζ₀ PP.1)

theorem trace_iff {ζ₀ : Fin a.Lz.rank → D.host.E} {PP : Formalism.L2.DIV.Pl D.host.E} (H : GX a ζ₀ PP)
    (g : GL (XIx (Fin D.R.k) (Fin D.R.t) 0) H.k) :
    embX (H.s + 1) g ∈ H.lev0.J ↔ g ∈ colGroup H.k D.R.k (Fin D.R.t) := by
  obtain ⟨h1, h2, -⟩ := GlobalTheory.FirstVertexFrame.firstVertex_typeChain H.k H.S.ψ H.S.ϖ H.s (Fin D.R.t) D.R.k H.S.P
    (GlobalTheory.SymShape.sym_shape _ _ _ _ _ _ _ H.S.sym) H.S.μ H.S.tame (H.s + 1) (Nat.zero_add _)
  refine ⟨fun h => ?_, fun h => (h2 g h).1⟩
  rw [← h1]
  refine ⟨1, one_mem _, mem_Cgrp.2 ⟨?_, ?_⟩⟩
  · rw [one_mul]
    exact (le_sup_left : (embX (H.s + 1)).range ≤ R H.k _ (H.s + 1) 1) ⟨g, rfl⟩
  · rw [inv_one, one_mul, mul_one, one_mul]
    exact h

theorem inLev0_iff_unip (κ : GA D (D.sp.X 0)) : InLev0 o G κ ↔
    GlobalTheory.FinPl.Moves (D.sp.X 0) κ (a.x 0).L (a.x 0).L (fun _ => True) ∧ (∀ i, o.mat0 i κ • o.Q 0 i = o.Q 0 i) ∧
      ∀ PP, (G PP).mat0 κ ∈ colGroup (G PP).k D.R.k (Fin D.R.t) := by
  simp only [inLev0_iff, trace_iff]

theorem under_auto {ζ₀ : Fin a.Lz.rank → D.host.E} {PP : Formalism.L2.DIV.Pl D.host.E} (H : GX a ζ₀ PP) :
    H.q.v = PP.under (𝓞 D.host.F) := by
  obtain ⟨ε, hε, he⟩ := H.q.above
  exact (GlobalTheory.IdemUnder.under_eq_of_isIdemAt D _ PP _ ε H.idem hε he).symm

theorem val_lt_one_iff {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (q : GlobalTheory.FinPl.SplitPt D K) {PP : Formalism.L2.DIV.Pl D.host.E} (h : Formalism.L2.NTheta.IsIdemAt q.e PP) (x : 𝓞 D.host.E) :
    valuation K (q.pr (incA D (x : D.host.E))) < 1 ↔ x ∈ PP.asIdeal := by
  by_cases hx : x = 0
  · subst hx; simp
  have h0 : (q.pr.comp (incA D)) (x : D.host.E) ≠ 0 := (map_ne_zero _).2 (RingOfIntegers.coe_ne_zero_iff.2 hx)
  rw [h.2 x hx, ← q.sec_pr, ← q.int_iff]
  change valuation K ((q.pr.comp (incA D)) x) < 1 ↔ ¬ valuation K ((q.pr.comp (incA D)) (x : D.host.E)⁻¹) ≤ 1
  rw [map_inv₀, map_inv₀, not_le, one_lt_inv₀ (zero_lt_iff.2 ((map_ne_zero _).2 h0))]

theorem oneG_iff {ζ₀ : Fin a.Lz.rank → D.host.E} {PP : Formalism.L2.DIV.Pl D.host.E} (H : GX a ζ₀ PP) (T : ℕ) :
    valuation H.k (H.q.pr (incA D ((T : ℕ) : D.host.E)) - 1) < 1 ↔ ((T : 𝓞 D.host.E) - 1) ∈ PP.asIdeal := by
  rw [← val_lt_one_iff H.q H.idem]
  simp

variable {o G} in

theorem mem_of_arith (h : Arith o G) (PP : a.c.Pg) : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.1.asIdeal := by
  rw [← val_lt_one_iff (G PP).q (G PP).idem]
  have h1 := h.unifG PP
  have h2 := ((G PP).S.unif _).2 le_rfl
  rw [← h1] at h2
  simpa using h2

theorem T_sub_one (B : D7) (v : B.what₂.Word) (P : Ideal (𝓞 B.host.E)) (hP : ((B.host.g 0 * B.host.g 1 : ℕ) : 𝓞 B.host.E) ∈ P) :
    (((B.mem v).A.T : ℕ) : 𝓞 B.host.E) - 1 ∈ P := by
  obtain ⟨π, -, hn, hc⟩ := B.T_norm v
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hc
  let σ : 𝓞 B.host.E →+* 𝓞 B.host.E := RingOfIntegers.mapRingHom (B.host.conj : B.host.E →+* B.host.E)
  have h1 : π * σ π = ((B.mem v).A.T : ℕ) := by
    apply RingOfIntegers.ext
    simpa [σ] using hn
  have h2 : π = 1 + c * ((B.host.QS * B.host.q * B.host.d * (B.host.g 0 * B.host.g 1) ^ 2 : ℕ) : 𝓞 B.host.E) := by
    rw [hc]; ring
  have hN : ((B.host.QS * B.host.q * B.host.d * (B.host.g 0 * B.host.g 1) ^ 2 : ℕ) : 𝓞 B.host.E) ∈ P := by
    rw [Nat.cast_mul, Nat.cast_pow]
    exact P.mul_mem_left _ (P.pow_mem_of_mem hP 2 two_pos)
  generalize (B.host.QS * B.host.q * B.host.d * (B.host.g 0 * B.host.g 1) ^ 2 : ℕ) = N at h2 hN
  have h3 : σ π = 1 + σ c * N := by rw [h2]; simp
  have : (((B.mem v).A.T : ℕ) : 𝓞 B.host.E) - 1 = (c + σ c + c * σ c * N) * N := by
    rw [← h1, h3, h2]; ring
  rw [this]
  exact P.mul_mem_left _ hN

section Unif

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (q : GlobalTheory.FinPl.SplitPt D K) {PP : Formalism.L2.DIV.Pl D.host.E}

theorem val_le_one (x : 𝓞 D.host.E) : valuation K (q.pr (incA D (x : D.host.E))) ≤ 1 := by
  have := GlobalTheory.FinPl.SplitApprox.val_le q 1 one_pos (incA D (x : D.host.E)) (finPart D (incA D (x : D.host.E)))
    (GlobalTheory.FinPl.SplitApprox.tmul_mem (a := 1) (fun v => by rw [map_one]; exact one_mem _) x.2) (by simp)
  simpa using this

theorem val_le_one_of (h : Formalism.L2.NTheta.IsIdemAt q.e PP) {y : D.host.E} (hy : PP.valuation D.host.E y ≤ 1) :
    valuation K (q.pr (incA D y)) ≤ 1 := by
  obtain ⟨n, d, e⟩ := PP.exists_primeCompl_mul_eq_of_integer y hy
  have hd : valuation K (q.pr (incA D ((d : 𝓞 D.host.E) : D.host.E))) = 1 :=
    le_antisymm (val_le_one q _) (not_lt.1 fun h' => d.2 ((val_lt_one_iff q h _).1 h'))
  have := val_le_one q n
  rw [show (n : D.host.E) = y * ((d : 𝓞 D.host.E) : D.host.E) from e.symm, map_mul, map_mul, map_mul, hd, mul_one] at this
  exact this

theorem val_eq_unif (h : Formalism.L2.NTheta.IsIdemAt q.e PP) (ϖ : Unif K) {x : 𝓞 D.host.E} (h1 : x ∈ PP.asIdeal)
    (h2 : x ∉ PP.asIdeal ^ 2) : valuation K (q.pr (incA D (x : D.host.E))) = valuation K ((ϖ.1 : 𝒪[K]) : K) := by
  obtain ⟨c, hc, -⟩ := GlobalTheory.FinPl.SplitApprox.exists_unif_unit D K q ϖ
  have hq := (GlobalTheory.FinPl.SplitApprox.exists_nat ϖ).1
  have hx0 : (x : D.host.E) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.2 fun h0 => h2 (h0 ▸ zero_mem _)
  refine le_antisymm ?_ ?_
  · have hm : (⟨_, val_le_one q x⟩ : 𝒪[K]) ∈ maximalIdeal 𝒪[K] :=
      Valuation.Integer.not_isUnit_iff_valuation_lt_one.2 ((val_lt_one_iff q h x).2 h1)
    obtain ⟨r, hr⟩ := ϖ.mem_max_iff.1 hm
    have hr' : q.pr (incA D (x : D.host.E)) = ((ϖ.1 : 𝒪[K]) : K) * r := congrArg (fun x : 𝒪[K] => (x : K)) hr
    rw [hr', map_mul]; exact mul_le_of_le_one_right' r.2
  · have hc0 : c ≠ 0 := by
      rintro rfl
      exact ϖ.ne_zero (by simpa using hc.symm)
    have hc1 : PP.valuation D.host.E c < 1 := by
      by_contra hge
      have := val_le_one_of q h (y := c⁻¹) (by rw [map_inv₀]; exact inv_le_one_of_one_le₀ (not_lt.1 hge))
      have h3 : valuation K (q.pr (incA D c)) * valuation K (q.pr (incA D c⁻¹)) = 1 := by
        rw [← map_mul, ← map_mul, ← map_mul, mul_inv_cancel₀ hc0]; simp
      have h4 : valuation K (q.pr (incA D c)) * valuation K (q.pr (incA D c⁻¹)) < 1 :=
        (mul_le_of_le_one_right' this).trans_lt (hc ▸ hq)
      exact h4.ne h3
    have hx : WithZero.exp (-1 : ℤ) ≤ PP.valuation D.host.E (x : D.host.E) := by
      have h5 : ¬ PP.intValuation x ≤ WithZero.exp (-(2 : ℕ) : ℤ) := fun h' =>
        h2 ((PP.intValuation_le_pow_iff_mem x 2).1 h')
      rw [show (x : D.host.E) = algebraMap _ _ x from rfl, HeightOneSpectrum.valuation_of_algebraMap]
      have hne : PP.intValuation x ≠ 0 := PP.intValuation_ne_zero _ fun h0 => h2 (h0 ▸ zero_mem _)
      rw [← WithZero.exp_log hne, WithZero.exp_le_exp] at h5 ⊢
      omega
    have hc2 : PP.valuation D.host.E c ≤ WithZero.exp (-1 : ℤ) := by
      have hne : PP.valuation D.host.E c ≠ 0 := (map_ne_zero _).2 hc0
      rw [← WithZero.exp_log hne, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hc1
      rw [← WithZero.exp_log hne, WithZero.exp_le_exp]
      omega
    have h6 := val_le_one_of q h (y := c / x) (by
      rw [map_div₀]; exact div_le_one_of_le₀ (hc2.trans hx) zero_le')
    rw [← hc, show c = (x : D.host.E) * (c / x) by field_simp, map_mul, map_mul, map_mul]
    exact mul_le_of_le_one_right' h6

theorem unif_val (ϖ : Unif K) {π : Kˣ} (h : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif π) : valuation K ((ϖ.1 : 𝒪[K]) : K) = valuation K (π : K) := by
  have hq := (GlobalTheory.FinPl.SplitApprox.exists_nat ϖ).1
  refine le_antisymm ((h _).1 hq) ?_
  have h1 := (h _).2 le_rfl
  have hm : (⟨(π : K), h1.le⟩ : 𝒪[K]) ∈ maximalIdeal 𝒪[K] := Valuation.Integer.not_isUnit_iff_valuation_lt_one.2 h1
  obtain ⟨r, hr⟩ := ϖ.mem_max_iff.1 hm
  have hr' : (π : K) = ((ϖ.1 : 𝒪[K]) : K) * r := congrArg (fun x : 𝒪[K] => (x : K)) hr
  rw [hr', map_mul]; exact mul_le_of_le_one_right' r.2

end Unif

theorem unifG_of {ζ₀ : Fin a.Lz.rank → D.host.E} {PP : Formalism.L2.DIV.Pl D.host.E} (H : GX a ζ₀ PP)
    (h1 : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal)
    (h2 : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal ^ 2) :
    valuation H.k (H.q.pr (incA D ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E))) = valuation H.k ((H.S.ϖ : H.kˣ) : H.k) := by
  obtain ⟨ϖ⟩ : Nonempty (Unif H.k) := inferInstance
  rw [← unif_val ϖ H.S.unif, ← val_eq_unif H.q H.idem ϖ h1 h2]
  simp

theorem exists_prime {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (q : GlobalTheory.FinPl.SplitPt D K) : ∃ PP : Formalism.L2.DIV.Pl D.host.E, Formalism.L2.NTheta.IsIdemAt q.e PP := by
  let φ : 𝓞 D.host.E →+* 𝒪[K] :=
    ((q.pr.comp (incA D)).comp (algebraMap (𝓞 D.host.E) D.host.E)).codRestrict 𝒪[K] fun x => val_le_one q x
  have hφ : ∀ x, x ∈ (maximalIdeal 𝒪[K]).comap φ ↔ valuation K (q.pr (incA D (x : D.host.E))) < 1 := fun x =>
    Valuation.Integer.not_isUnit_iff_valuation_lt_one
  obtain ⟨ϖ⟩ : Nonempty (Unif K) := inferInstance
  obtain ⟨hq, N, hN, hNq⟩ := GlobalTheory.FinPl.SplitApprox.exists_nat ϖ
  refine ⟨⟨(maximalIdeal 𝒪[K]).comap φ, Ideal.comap_isPrime _ _, fun h0 => ?_⟩, q.split, fun x hx => ?_⟩
  · have : (N : 𝓞 D.host.E) ∈ (maximalIdeal 𝒪[K]).comap φ := (hφ _).2 (by simpa using hNq.trans hq)
    rw [h0, Ideal.mem_bot] at this
    exact hN.ne' (by exact_mod_cast this)
  · have h0 : (q.pr.comp (incA D)) (x : D.host.E) ≠ 0 := (map_ne_zero _).2 (RingOfIntegers.coe_ne_zero_iff.2 hx)
    refine (hφ x).trans ?_
    rw [← q.sec_pr, ← q.int_iff]
    change valuation K ((q.pr.comp (incA D)) x) < 1 ↔ ¬ valuation K ((q.pr.comp (incA D)) (x : D.host.E)⁻¹) ≤ 1
    rw [map_inv₀, map_inv₀, not_le, one_lt_inv₀ (zero_lt_iff.2 ((map_ne_zero _).2 h0))]

theorem notMem_sq {p : ℕ} (h : GlobalTheory.IndefiniteRowSideFullHecke.SplitColumnClasses.SplitsCompletely D.host.E p) (P : HeightOneSpectrum (𝓞 D.host.E))
    (hP : (p : 𝓞 D.host.E) ∈ P.asIdeal) : (p : 𝓞 D.host.E) ∉ P.asIdeal ^ 2 := by
  obtain ⟨hp, h⟩ := h
  rw [GlobalTheory.HostSplit.ncard_placesOver _ hp] at h
  haveI := P.isPrime
  exact (GlobalTheory.LocSplit.split_prime hp h P.asIdeal hP).1

theorem unifT_of (p : GlobalTheory.FinPl.SplitPt D k) (ϖ : Unif k) (h : (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ p.v.asIdeal) :
    valuation k (p.pr (incA D (((D.mem u).A.T : ℕ) : D.host.E))) = valuation k ((ϖ.1 : 𝒪[k]) : k) := by
  obtain ⟨PP, hPP⟩ := exists_prime p
  obtain ⟨ε, hε, he⟩ := p.above
  have hv := GlobalTheory.IdemUnder.under_eq_of_isIdemAt D _ PP _ ε hPP hε he
  have h1 : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    rw [← hv] at h
    simpa using (Ideal.mem_comap.1 h)
  rw [← val_eq_unif p hPP ϖ h1 (notMem_sq (GlobalTheory.ColClassCompare.levelPrime_splitsCompletely_in_cmField D u) PP h1)]
  simp

theorem g_notMem_sq (P : HeightOneSpectrum (𝓞 D.host.E)) : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ^ 2 := by
  have key : ∀ i j : Fin 2, D.host.g i ≠ D.host.g j → ((D.host.g i : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal →
      ((D.host.g i : ℕ) : 𝓞 D.host.E) * (D.host.g j : ℕ) ∉ P.asIdeal ^ 2 := fun i j hij hi h => by
    have hc := (Nat.coprime_primes (D.host.g_prime i) (D.host.g_prime j)).2 hij
    obtain ⟨x, y, hxy⟩ := (Nat.Coprime.cast (R := 𝓞 D.host.E) hc)
    refine notMem_sq (GlobalTheory.IndefiniteRowSideFullHecke.SplitColumnClasses.splitsCompletely_g D i) P hi ?_
    have e : ((D.host.g i : ℕ) : 𝓞 D.host.E) = x * (((D.host.g i : ℕ) : 𝓞 D.host.E) * (D.host.g i : ℕ)) +
        y * (((D.host.g i : ℕ) : 𝓞 D.host.E) * (D.host.g j : ℕ)) := by linear_combination (-((D.host.g i : ℕ) : 𝓞 D.host.E)) * hxy
    rw [e]
    exact add_mem (Ideal.mul_mem_left _ _ (by rw [pow_two]; exact Ideal.mul_mem_mul hi hi)) (Ideal.mul_mem_left _ _ h)
  intro h
  rw [Nat.cast_mul] at h
  rcases P.isPrime.mem_or_mem (Ideal.pow_le_self two_ne_zero h) with h0 | h1
  · exact key 0 1 D.host.g_ne h0 h
  · exact key 1 0 D.host.g_ne.symm h1 (by rwa [mul_comm])

theorem arith_iff (hT : ∀ i, (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ (o.p i).v.asIdeal)
    (hG : ∀ PP ∈ a.c.Pg, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) :
    Arith o G ↔ (∀ v, v ∉ a.c.S → CharUnramAt D a.c.η v ∧ ∀ j, 1 ≤ j → j ≤ D.R.m → CharUnramAt D (a.c.μ j) v) ∧
      a.Lz.SigOK ∧ a.Lz.IsPosDef :=
  ⟨fun h => ⟨h.unr, h.lz⟩, fun h => Arith.of_local o G (fun i => unifT_of _ _ (hT i))
    (fun PP => (oneG_iff _ _).2 (T_sub_one D u _ (hG _ PP.2))) (fun PP => unifG_of _ (hG _ PP.2) (g_notMem_sq _))
    (fun PP => under_auto _) h.1 h.2⟩

theorem comp_map {F E : Type} [Field F] [Field E] [Algebra F E] {R R' R'' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R']
    [CommRing R''] [Algebra F R''] (φ : R →ₐ[F] R') (ψ : R' →ₐ[F] R'') (z : R ⊗[F] E) :
    Algebra.TensorProduct.map (ψ.comp φ) (AlgHom.id F E) z =
      Algebra.TensorProduct.map ψ (AlgHom.id F E) (Algebra.TensorProduct.map φ (AlgHom.id F E) z) := by
  rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id]

set_option maxHeartbeats 1000000 in

theorem charUnramAt_of {χ : (AE D)ˣ →* Circle} {v : HeightOneSpectrum (𝓞 D.host.F)}
    (h : ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → GlobalTheory.LFun.UnrAt χ w) : CharUnramAt D χ v := by
  have kf : ∀ w (z : AE D), GlobalTheory.AdelicU.compFin D.host.F D.host.E w z = GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w (finPart D z) :=
    fun w z => comp_map _ _ z
  have ki : ∀ w (z : AE D), infPart D z = 1 → GlobalTheory.AdelicU.compInf D.host.F D.host.E w z = 1 := fun w z hz =>
    (comp_map _ _ z).trans ((congrArg (Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id D.host.F D.host.E)) hz).trans
      (map_one _))
  have kint : ∀ y ∈ intAE D, GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v y ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v := fun y hy => by
    induction hy using AddSubgroup.closure_induction with
    | mem y hy => obtain ⟨α, hα, x, rfl⟩ := hy; exact GlobalTheory.AdelicU.tmul_mem_intLoc (hα v) x
    | zero => rw [RingHom.map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [RingHom.map_add]; exact add_mem hy hz
    | neg y _ hy => rw [RingHom.map_neg]; exact neg_mem hy
  have kin : ∀ z : (AE D)ˣ, finPart D (z : AE D) ∈ intAE D →
      (GlobalTheory.Doubling.unitFin D.host.F D.host.E v z).val ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v := fun z hz =>
    Set.mem_of_eq_of_mem (s := GlobalTheory.AdelicU.intLoc D.host.F D.host.E v) (kf v z) (kint _ hz)
  intro x h1 h2 h3 h4
  have hx : x = GlobalTheory.Doubling.ideleAt D.host.F D.host.E v (GlobalTheory.Doubling.unitFin D.host.F D.host.E v x) := by
    refine GlobalTheory.Doubling.idele_ext (fun w => ?_) fun w => ?_
    · rw [GlobalTheory.Doubling.unitInf_ideleAt]
      exact Units.ext (ki w x h1)
    · by_cases hw : w = v
      · subst hw; rw [GlobalTheory.Doubling.unitFin_ideleAt_self]
      · rw [GlobalTheory.Doubling.unitFin_ideleAt_ne hw]
        exact Units.ext ((kf w x).trans (h2 w hw))
  rw [hx]
  refine GlobalTheory.LFun.charAt_eq_one_of_unrAt_datum D χ v _ ?_ ?_ h
  · exact kin x h3
  · rw [← map_inv]
    exact kin x⁻¹ h4

theorem arith_of_pins (hc : a.c.Is) (hP : GlobalTheory.Core.Mi.IsTypePlaces a.c.Pg) (ho : PinOffX o) (hL : a.Lz.SigOK ∧ a.Lz.IsPosDef) :
    Arith o G := by
  refine (arith_iff o G (fun i => (ho.overT _).1 ⟨i, rfl⟩) hP.1).2 ⟨fun v hv => ⟨fun x h1 _ h3 h4 => hc.chars.2.1 x h1 h3 h4,
    fun j h1 h2 => charUnramAt_of fun w hw => ?_⟩, hL⟩
  have := hc.unr ⟨j - 1, by omega⟩ w (fun h => hv (hw ▸ h))
  rwa [show j - 1 + 1 = j by omega] at this

end GlobalTheory.SeeSaw.LevelTest

section
open Formalism.UG Formalism.L2.Forms

namespace GlobalTheory.SeeSaw.BaseLatTest

theorem lat_not_selfDual {D : D7} {u : D.what₂.Word} (F : Forms0 D u)
    (L : Submodule (𝓞 D.host.E) (Fin (D.sp.X 0).rank → D.host.E)) (sd : IsSelfDualC (D.sp.X 0) L)
    (lat : ∀ z : Fin (D.sp.X 0).rank → D.host.E, z ∈ L ↔
      (fun i => z (Fin.cast (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)).symm i)) ∈ F.cls0.lev.Lb) : False := by
  have hr := Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)
  have hle : Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) F.cls0.lev.Lb)
      ≤ F.cls0.lev.Lb := by
    refine Submodule.span_le.2 fun y hy => ?_
    have : (fun j => y (Fin.cast hr j)) ∈ L := by
      refine (sd.2 _).2 fun x hx => ?_
      obtain ⟨b, hb⟩ := hy _ ((lat x).1 hx)
      refine ⟨b, ?_⟩
      refine hb.trans ?_
      simp only [hform, gramN, dotProduct, mulVec, Finset.mul_sum]
      refine (Fintype.sum_equiv (finCongr hr) _ _ fun i => ?_).symm
      refine Fintype.sum_equiv (finCongr hr) _ _ fun j => ?_
      simp [mul_assoc]
      exact Or.inl rfl
    exact (lat _).1 this
  have h1 := F.cls0.lev.Lb_index
  rw [AddSubgroup.relIndex_eq_one.2 (by exact hle)] at h1
  have hf : 0 < D.R.f := by unfold Ranks.f Ranks.n; positivity
  have := Nat.one_lt_pow (n := 2 * D.R.f) (by omega) (D.mem u).A.T_prime.one_lt
  omega

end GlobalTheory.SeeSaw.BaseLatTest

end

end
