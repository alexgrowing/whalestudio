import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EmbeddingColumnLatticeIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeRowMulVecMemModulusScaledCompletion
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PadOneMemSecondBlockTriangular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DependenceFixed
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceHermitianFrameProperties
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UpImageIntegralMatrixMemCompletedHomLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceFrameLatticeOfMovedLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitIdealCompletionAtPlaceEqIntegralAdelesAtPlac
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TmulOneMemIntAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationEqUniformizerAndUnitAtPrime
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FunctionalValuesIntegralVectorsOfIntegerVectors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AuxiliaryVectorDecompositionEqZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel

noncomputable section

namespace GlobalTheory.DepthColumn

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sec_mul_right (p : GlobalTheory.FinPl.SplitPt D k) (x : k) (b : AE D) : p.sec x * b = p.sec (x * p.pr b) := by
  have h1 : p.sec x = p.e * p.sec x := by
    have := p.sec_pr (p.sec x)
    rwa [p.pr_sec] at this
  have h2 := p.sec_pr (p.sec x * b)
  rw [map_mul, p.pr_sec, ← mul_assoc, ← h1] at h2
  exact h2.symm

theorem sec_mem_idV (p : GlobalTheory.FinPl.SplitPt D k) {I : GlobalTheory.SeeSaw.FI D} {a : D.host.E} (ha : a ∈ I) (ha0 : a ≠ 0) {c : k}
    (hc : valuation k c ≤ valuation k (p.pr (incA D a))) : p.sec c ∈ GlobalTheory.SeeSaw.idV I p.v := by
  have h0 : p.pr (incA D a) ≠ 0 := (map_ne_zero_iff (p.pr.comp (incA D)) (p.pr.comp (incA D)).injective).2 ha0
  have key : ∀ y ∈ GlobalTheory.SeeSaw.idV (1 : GlobalTheory.SeeSaw.FI D) p.v, incA D a * y ∈ GlobalTheory.SeeSaw.idV I p.v := by
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨α, hα, hαv, b, hb, rfl⟩ := hy
      rw [GlobalTheory.SeeSaw.IdVMul.incA_mul_tmul]
      refine AddSubgroup.subset_closure ⟨α, hα, hαv, _, ?_, rfl⟩
      have := FractionalIdeal.mul_mem_mul (S := (𝓞 D.host.E)⁰) ha hb
      rwa [mul_one] at this
    | zero => rw [mul_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
    | neg a _ ha => rw [mul_neg]; exact neg_mem ha
  have hint : c / p.pr (incA D a) ∈ 𝒪[k] := by
    rw [Valuation.mem_integer_iff, map_div₀]
    exact div_le_one_of_le₀ hc zero_le'
  have h1 := key _ ((GlobalTheory.SeeSaw.idV_one_eq_intAt D p.v _).2 ⟨p.sec_mem_idAt _, (p.int_iff _).1 hint⟩)
  rwa [mul_comm, sec_mul_right, div_mul_cancel₀ _ h0] at h1

def prInt (p : GlobalTheory.FinPl.SplitPt D k) {PP : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt p.e PP) :
    𝓞 D.host.E →+* 𝒪[k] :=
  ((p.pr.comp (incA D)).comp (algebraMap (𝓞 D.host.E) D.host.E)).codRestrict 𝒪[k] fun x => p.pr_incA_int_mem he x

theorem coe_prInt (p : GlobalTheory.FinPl.SplitPt D k) {PP : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt p.e PP)
    (x : 𝓞 D.host.E) : (prInt p he x : k) = p.pr (incA D (x : D.host.E)) := rfl

theorem mem_iff_lt (p : GlobalTheory.FinPl.SplitPt D k) {PP : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt p.e PP)
    (x : 𝓞 D.host.E) : x ∈ PP.asIdeal ↔ valuation k (p.pr (incA D (x : D.host.E))) < 1 := by
  rw [p.mem_iff_val_lt he, ← p.prF_toEAf he]
  rfl

theorem val_eq_one (p : GlobalTheory.FinPl.SplitPt D k) {PP : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt p.e PP)
    {x : 𝓞 D.host.E} (hx : x ∉ PP.asIdeal) : valuation k (p.pr (incA D (x : D.host.E))) = 1 :=
  le_antisymm (p.pr_incA_int_mem he x) (not_lt.1 fun h => hx ((mem_iff_lt p he x).2 h))

theorem prInt_mem_pow (p : GlobalTheory.FinPl.SplitPt D k) {PP : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt p.e PP)
    (n : ℕ) {x : 𝓞 D.host.E} (hx : x ∈ PP.asIdeal ^ n) : prInt p he x ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ n := by
  have h1 : PP.asIdeal.map (prInt p he) ≤ IsLocalRing.maximalIdeal 𝒪[k] :=
    Ideal.map_le_iff_le_comap.2 fun y hy => Ideal.mem_comap.2
      ((GlobalTheory.FinPl.SplitPt.mem_max_iff_val_lt_one _).2 ((mem_iff_lt p he y).1 hy))
  have h2 := Ideal.mem_map_of_mem (prInt p he) hx
  rw [Ideal.map_pow] at h2
  exact Ideal.pow_right_mono h1 n h2

theorem coord_mem_pow (p : GlobalTheory.FinPl.SplitPt D k) {PP : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt p.e PP)
    {S : HSp D} {ι : Type} [Fintype ι] [DecidableEq ι] (β : GlobalTheory.FinPl.Frame p S ι) {L : Lat S}
    (hL : β.IsLat L (Submodule.pi Set.univ fun _ => (1 : Submodule 𝒪[k] k))) {𝔪 : Ideal (𝓞 D.host.E)} {n : ℕ}
    (h𝔪 : 𝔪 ≤ PP.asIdeal ^ n) {Y : Fin S.rank → AE D}
    (hY : Y ∈ GlobalTheory.FinPl.latMul S {a | a ∈ ((𝔪 : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)} L (· = p.v)) (r : ι) :
    ∃ z ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ n, (z : k) = (β.b' *ᵥ fun j => p.pr (Y j)) r := by
  induction hY using AddSubgroup.closure_induction with
  | mem Y hY =>
    obtain ⟨α, hα, hαv, a, ha, x, hx, rfl⟩ := hY
    obtain ⟨m, hm, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 ha
    set Y₀ : Fin S.rank → AE D := fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x i) with hY₀
    have h0 : Y₀ ∈ latV S L (· = p.v) := AddSubgroup.subset_closure ⟨α, hα, hαv, 1, rfl, x, hx, rfl⟩
    have h1 := GlobalTheory.UpMem.smul_mem_latMul S {1} L (· = p.v) p.e (GlobalTheory.UpMem.finPart_e_int p) _ h0
    have h2 : (β.b' *ᵥ fun j => p.pr (Y₀ j)) ∈ Submodule.pi Set.univ fun _ : ι => (1 : Submodule 𝒪[k] k) := by
      rw [hL, Matrix.mulVec_mulVec, β.bb', Matrix.one_mulVec]
      simp only [p.sec_pr]
      exact h1
    obtain ⟨o, ho⟩ := Submodule.mem_one.1 (h2 r (Set.mem_univ r))
    refine ⟨prInt p he m * o, Ideal.mul_mem_right _ _ (prInt_mem_pow p he n (h𝔪 hm)), ?_⟩
    have e : (fun j => p.pr (pairA D.host.F 0 α ⊗ₜ[D.host.F] (algebraMap (𝓞 D.host.E) D.host.E m * x j))) =
        (prInt p he m : k) • fun j => p.pr (Y₀ j) := by
      funext j
      rw [Pi.smul_apply, smul_eq_mul, coe_prInt, ← map_mul, hY₀, GlobalTheory.SeeSaw.IdVMul.incA_mul_tmul, one_mul]
    rw [e, Matrix.mulVec_smul, Pi.smul_apply, ← ho, smul_eq_mul]
    rfl
  | zero => exact ⟨0, zero_mem _, by simp [Matrix.mulVec, dotProduct]⟩
  | add Y Y' _ _ h h' =>
    obtain ⟨z, hz, e⟩ := h
    obtain ⟨z', hz', e'⟩ := h'
    refine ⟨z + z', add_mem hz hz', ?_⟩
    push_cast
    rw [e, e', ← Pi.add_apply, ← Matrix.mulVec_add]
    congr 2
    funext j
    simp
  | neg Y _ h =>
    obtain ⟨z, hz, e⟩ := h
    refine ⟨-z, neg_mem hz, ?_⟩
    push_cast
    rw [e, ← Pi.neg_apply, ← Matrix.mulVec_neg]
    congr 2
    funext j
    simp

theorem pow_mem_pow_fr {I : GlobalTheory.SeeSaw.FI D} {a : D.host.E} (ha : a ∈ I) (n : ℕ) : a ^ n ∈ I ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact FractionalIdeal.one_mem_one _
  | succ n ih => rw [pow_succ, pow_succ]; exact FractionalIdeal.mul_mem_mul ih ha

variable {T : Type} {L : LevCh D T} {sc : Consts}

theorem exists_mem_modul (P : Places L) {v : GlobalTheory.FinPl.Pl D} (hv : v ∈ P.S0) (p : GlobalTheory.FinPl.SplitPt D k)
    (he : Formalism.L2.NTheta.IsIdemAt p.e (P.w v)) {ϖ : k} (hϖ : valuation k ϖ < 1) :
    ∃ m ∈ P.modul sc, m ≠ 0 ∧ valuation k ϖ ^ P.depth sc v ≤ valuation k (p.pr (incA D (m : D.host.E))) := by
  classical
  have hex : ∀ u ∈ P.S0, ∃ t ∈ (P.w u).asIdeal, t ≠ 0 ∧
      (if u = v then valuation k ϖ else 1) ≤ valuation k (p.pr (incA D (t : D.host.E))) := by
    intro u hu
    split_ifs with h
    · subst h
      obtain ⟨t, ht, ht2⟩ := SetLike.exists_of_lt (Ideal.pow_lt_self (P.w u).asIdeal (P.w u).ne_bot (P.w u).isPrime.ne_top 2 le_rfl)
      obtain ⟨⟨q, hq⟩, -⟩ := GlobalTheory.FinPl.SplitPt.val_eq_unif_and_unit D k p _ he t 1 ht ht2
        fun h1 => (P.w u).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
      refine ⟨t, ht, fun h0 => ht2 (h0 ▸ zero_mem _), ?_⟩
      rw [hq]
      exact GlobalTheory.FinPl.SplitPt.val_le_unif q hϖ
    · have hne : P.w u ≠ P.w v := fun e => h (by rw [← P.under_w hu, e, P.under_w hv])
      obtain ⟨t, ht, ht'⟩ := Set.not_subset.1 fun hle : ((P.w u).asIdeal : Set (𝓞 D.host.E)) ⊆ (P.w v).asIdeal =>
        hne (GlobalTheory.IdemSupport.eq_of_le hle)
      exact ⟨t, ht, fun h0 => ht' (h0 ▸ zero_mem _), (val_eq_one p he ht').ge⟩
  choose! t ht ht0 htv using hex
  refine ⟨∏ u ∈ P.S0, t u ^ P.depth sc u, Ideal.prod_mem_prod fun u hu => Ideal.pow_mem_pow (ht u hu) _,
    Finset.prod_ne_zero_iff.2 fun u hu => pow_ne_zero _ (ht0 u hu), ?_⟩
  rw [← coe_prInt p he, map_prod]
  push_cast
  rw [map_prod]
  calc valuation k ϖ ^ P.depth sc v = ∏ u ∈ P.S0, (if u = v then valuation k ϖ else 1) ^ P.depth sc u := by
        rw [Finset.prod_eq_single_of_mem v hv fun u _ h => by rw [if_neg h, one_pow], if_pos rfl]
    _ ≤ _ := Finset.prod_le_prod' fun u hu => by
        rw [map_pow, SubmonoidClass.coe_pow, map_pow, coe_prInt]
        exact pow_le_pow_left' (htv u hu) _

theorem sec_mem_stairId {μ0 : T} (hq : OffQ D) (hL : L.Is μ0) (G : GridData L sc) {v : GlobalTheory.FinPl.Pl D} (hv : v ∈ G.pl.S0)
    (p : GlobalTheory.FinPl.SplitPt D k) (hpv : p.v = v) (he : Formalism.L2.NTheta.IsIdemAt p.e (G.pl.w v)) {ϖ : k} (hϖ : valuation k ϖ < 1)
    (c : ℕ) (q : Fin c) :
    p.sec (ϖ ^ (G.pl.depth sc v * (q.1 + 1))) ∈ GlobalTheory.SeeSaw.idV (stairId (G.pl.stA sc) (G.pl.stAbar sc) c q) v := by
  classical
  have hw : G.pl.w v ∈ G.pl.W0 := (GlobalTheory.DepthFix.mem_orthogonal_frame_iff G).2 ⟨v, hv, rfl⟩
  have hb := Good.badInt_notMem hL (G := G) (t := μ0) hq (fun P hP => absurd
    (show (L.xiH μ0).UnrAt P by rw [hL.xi_base]; exact fun x _ => rfl) ((hL.Q_ram μ0 P).2 (Or.inl hP)))
    (Finset.mem_union_left _ hw)
  have h2q : ((D.host.QS * D.host.q : ℕ) : 𝓞 D.host.E) ∉ (G.pl.w v).asIdeal :=
    fun h => hb (GlobalTheory.HalfCompare.mem_of_dvd h (Dvd.intro _ rfl))
  have hN : ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ (G.pl.w v).asIdeal :=
    fun h => hb (GlobalTheory.HalfCompare.mem_of_dvd h (Dvd.intro_left _ rfl))
  have hn : ((Ideal.absNorm D.host.𝔟 : ℕ) : 𝓞 D.host.E) ∉ (G.pl.w v).asIdeal := fun hm => by
    obtain ⟨l, hl, hP⟩ := GlobalTheory.HalfCompare.exists_prime_under (G.pl.w v)
    exact h2q ((hP _).2 ((GlobalTheory.HalfCompare.prime_dvd_absNorm_halfDifferent D hl).1 ((hP _).1 hm)))
  obtain ⟨m, hm, hm0, hmv⟩ := exists_mem_modul (sc := sc) G.pl hv p he hϖ
  have h1 := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).1
  have h2 := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).2 T L G.pl sc
  have hAb : (D.host.AAbar : GlobalTheory.SeeSaw.FI D) ≠ 0 := ne_zero_of_conj h1.1 h1.2
  have hmb : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D) ≠ 0 := by
    intro h
    have h4 := h2.1
    rw [Places.stA, h, _root_.inv_zero, mul_zero] at h4
    exact h4 rfl
  set N : 𝓞 D.host.E := ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) with hNdef
  set n : 𝓞 D.host.E := ((Ideal.absNorm D.host.𝔟 : ℕ) : 𝓞 D.host.E) with hndef
  have hA : (N : D.host.E) ∈ G.pl.stA sc := by
    have e1 : (1 : D.host.E) ∈ ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹ :=
      (FractionalIdeal.mem_inv_iff hmb).2 fun y hy => by
        rw [one_mul]; exact FractionalIdeal.coeIdeal_le_one hy
    have := FractionalIdeal.mul_mem_mul (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.normCc_mem_AA D) e1
    rw [mul_one] at this
    simpa [hNdef, Places.stA] using this
  have hB : ((n * m : 𝓞 D.host.E) : D.host.E) ∈ (G.pl.stAbar sc)⁻¹ := by
    have e1 : (n : D.host.E) ∈ (D.host.AAbar : GlobalTheory.SeeSaw.FI D)⁻¹ :=
      (FractionalIdeal.mem_inv_iff hAb).2 fun y hy => by
        obtain ⟨o, ho⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.int_of_mem_b D (Ideal.absNorm_mem _) ((h1.2 y).1 hy)
        refine (FractionalIdeal.mem_one_iff _).2 ⟨GlobalTheory.IdemSupport.cO D o, ?_⟩
        change star (algebraMap _ D.host.E o) = _
        rw [ho, star_mul', star_star, star_natCast, mul_comm]
        simp [hndef]
    rw [Places.stAbar, mul_inv, inv_inv]
    push_cast
    exact FractionalIdeal.mul_mem_mul e1 (FractionalIdeal.mem_coeIdeal_of_mem _ hm)
  have ha : ((N ^ (c - q.1) * (n * m) ^ (q.1 + 1) : 𝓞 D.host.E) : D.host.E) ∈
      stairId (G.pl.stA sc) (G.pl.stAbar sc) c q := by
    rw [stairId, ← inv_pow, RingOfIntegers.coe_eq_algebraMap, map_mul, map_pow, map_pow]
    exact FractionalIdeal.mul_mem_mul (pow_mem_pow_fr hA _) (pow_mem_pow_fr hB _)
  have hN0 : N ≠ 0 := fun h => hN (h ▸ zero_mem _)
  have hn0 : n ≠ 0 := fun h => hn (h ▸ zero_mem _)
  subst hpv
  refine sec_mem_idV p ha (fun h => ?_) ?_
  · exact mul_ne_zero (pow_ne_zero _ hN0) (pow_ne_zero _ (mul_ne_zero hn0 hm0)) (RingOfIntegers.coe_eq_zero_iff.1 h)
  · rw [← coe_prInt p he]
    simp only [map_mul, map_pow, MulMemClass.coe_mul, SubmonoidClass.coe_pow, coe_prInt, val_eq_one p he hN,
      val_eq_one p he hn, one_pow, one_mul, pow_mul]
    exact pow_le_pow_left' hmv _

theorem col_eq {S S₀ U : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (x : Mx D U.rank ρ) (q : Fin ρ) :
    (fun j => x j q) = d.extX U x *ᵥ fun i => d.jX i q := by
  rw [HypDec.extX_apply, ← Matrix.mulVec_mulVec]
  have e : (d.pX *ᵥ fun i => d.jX i q) = fun i => (d.pX * d.jX) i q := rfl
  rw [e, HypDec.pX_jX]
  funext j
  simp [Matrix.mulVec, dotProduct, Matrix.one_apply]

theorem col_mem_depth : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ v ∈ G.pl.S0,
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.FinPl.SplitPt D k)
    (β : GlobalTheory.FinPl.Frame p (G.V (.grid (2 * σ + 2) 0)) (Fin (G.V (.grid (2 * σ + 2) 0)).rank)) (ϖ : 𝒪[k]),
  p.v = v → Formalism.L2.NTheta.IsIdemAt p.e (G.pl.w v) →
  β.IsLat (G.Λ (.grid (2 * σ + 2) 0)) (Submodule.pi Set.univ fun _ => (1 : Submodule 𝒪[k] k)) →
  IsLocalRing.maximalIdeal 𝒪[k] = Ideal.span {ϖ} →
  ∀ a ∈ (pcFB W F σ h h').A₁, ∀ (q : Fin (σ + 1)) i, ∃ z ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ G.pl.depth sc v,
    (z : k) = (ϖ : k) ^ (G.pl.depth sc v * (q.1 + 1)) * (p.pr (incA D (-D.host.xi0)))⁻¹ ^ (q.1 + 1) *
      (β.b' *ᵥ fun j => p.pr (a j q)) i := by
  intro D hq T L μ0 hL sc G W M _ F hF σ h h' v hv k _ _ _ _ p β ϖ hpv he hlat hmax a ha q i
  obtain ⟨e, hE, -⟩ := W.cosVec_is
  obtain ⟨hc, hJ, -⟩ := hF.hJ (σ + 1) h
  have hw : G.pl.w v ∈ G.pl.W0 := (GlobalTheory.DepthFix.mem_orthogonal_frame_iff G).2 ⟨v, hv, rfl⟩
  have hpe : p.pr e = 1 := by
    have := congrArg p.pr (GlobalTheory.DiagLiftFix.idemSum_mul hE hw he)
    rwa [map_mul, GlobalTheory.FrameAt.pr_e, mul_one] at this
  have hϖ : valuation k (ϖ : k) < 1 :=
    (GlobalTheory.FinPl.SplitPt.mem_max_iff_val_lt_one _).1 (hmax ▸ Ideal.mem_span_singleton_self ϖ)
  have hξ : p.pr (incA D (-D.host.xi0)) ≠ 0 :=
    (map_ne_zero_iff (p.pr.comp (incA D)) (p.pr.comp (incA D)).injective).2 (neg_ne_zero.2 GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero)
  set s : k := (ϖ : k) ^ (G.pl.depth sc v * (q.1 + 1)) * (p.pr (incA D (-D.host.xi0)))⁻¹ ^ (q.1 + 1) with hs
  have hy : p.sec s • (fun j => (F.dJ (σ + 1) h).jX j q) =
      fun j => p.sec ((ϖ : k) ^ (G.pl.depth sc v * (q.1 + 1))) *
        incA D ((G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a j ⟨q.1, by omega⟩) := by
    funext j
    have e1 : p.sec s * incA D ((-D.host.xi0) ^ (q.1 + 1)) = p.sec ((ϖ : k) ^ (G.pl.depth sc v * (q.1 + 1))) := by
      rw [sec_mul_right, map_pow, map_pow, hs, mul_assoc, ← mul_pow, inv_mul_cancel₀ hξ, one_pow, mul_one]
    simp only [Pi.smul_apply, smul_eq_mul, HypDec.jX, GlobalTheory.MixModel.rat, hJ, colsOf, Matrix.map_apply, map_mul]
    rw [← mul_assoc, e1]
    rfl
  have hΛ : G.Λ (.grid (2 * σ + 2 + 1) 0) = (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).lat
      (G.Λ (.core (2 * (σ + 1) + 1))) (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * (σ + 1) + 1 - 1)) :=
    G.sp.colLat _ _ _
  have hmem : p.sec s • (fun j => (F.dJ (σ + 1) h).jX j q) ∈
      latV (G.V (.grid (2 * σ + 2 + 1) 0)) (G.Λ (.grid (2 * σ + 2 + 1) 0)) (· = v) := by
    rw [hy, hΛ]
    exact (GlobalTheory.AscFin.UnitaryEmbeddingLine.embedding_line_mem_lattice_iff _ (neg_ne_zero.2 one_ne_zero) _ _ _ v _).1.2
      (sec_mem_stairId hq hL G hv p hpv he hϖ _ _)
  have hu : (F.dJ (σ + 1) h).extX (G.V (.grid (2 * σ + 2) 0)) a ∈ latRow G (2 * σ + 2) := ha
  have hY := GlobalTheory.DepthRowLem.mulVec_mem_latMul _ (hu.2 e hE) hmem
  have hle : G.pl.modul sc ≤ (G.pl.w v).asIdeal ^ G.pl.depth sc v := Ideal.prod_le_inf.trans (Finset.inf_le hv)
  subst hpv
  obtain ⟨z, hz, hz'⟩ := coord_mem_pow p he β hlat hle hY i
  refine ⟨z, hz, hz'.trans ?_⟩
  have e2 := col_eq (U := G.V (.grid (2 * σ + 2) 0)) (F.dJ (σ + 1) h) a q
  have e4 : s * (β.b' *ᵥ fun j => p.pr (a j q)) i = (β.b' *ᵥ (s • fun j => p.pr (a j q))) i := by
    rw [Matrix.mulVec_smul]
    rfl
  rw [e4]
  refine congrArg (fun y => (β.b' *ᵥ y) i) (funext fun j => ?_)
  have e3 : ((e • (F.dJ (σ + 1) h).extX (G.V (.grid (2 * σ + 2) 0)) a) *ᵥ (p.sec s • fun j => (F.dJ (σ + 1) h).jX j q)) j =
      e * (p.sec s * a j q) := by
    rw [Matrix.smul_mulVec, Matrix.mulVec_smul, ← e2]
    rfl
  refine (congrArg p.pr e3).trans ?_
  rw [map_mul, map_mul, hpe, p.pr_sec, one_mul]
  rfl

end GlobalTheory.DepthColumn

end
