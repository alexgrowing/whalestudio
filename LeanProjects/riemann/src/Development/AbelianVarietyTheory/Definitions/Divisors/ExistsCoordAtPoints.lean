import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecHeightSmulAlgebraMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFinrankLineBundleSectionsFiniteEtale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryOfFrameNormConj

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers

namespace GlobalTheory.HSCore

variable {K : Type} [Field K] [NumberField K]

abbrev RatPt (G : Geo K) (s : Fin G.D → Fin G.N → K) : Type := PtsOver K ((G.ideal s).subschemeι ≫ G.str)

namespace RatPt

variable {G : Geo K} {s : Fin G.D → Fin G.N → K} (x : RatPt G s)

def pt : G.Pt K := ⟨x.1 ≫ (G.ideal s).subschemeι, (Category.assoc _ _ _).trans x.2⟩

def along {Ω : Type} [Field Ω] (φ : K →+* Ω) : Points.PtsOver ((G.ideal s).subschemeι ≫ G.str) (spMap φ) :=
  ⟨spMap φ ≫ x.1, by rw [Category.assoc, x.2, spMap, spMap, ← Spec.map_comp]; rfl⟩

def nrm (j : ℕ) (τ : K →+* ℂ) (g : G.SecOn s j) : ℝ :=
  Real.sqrt ((Geo.weightOn s j τ).nsq (cval τ g) (x.along τ))

def gen (k : Fin G.n) : K := ∑ j, G.w j k * G.coords x.pt.1 j

def c₁ (τ : K →+* ℂ) : ℝ := archSize (G.A τ) fun j => τ (G.coords x.pt.1 j)

def c₂ (τ : K →+* ℂ) : ℝ := archSize (G.A₂ τ) fun j => τ (G.second.coords x.pt.1 j)

def ht : ℝ := vecHt x.gen x.c₁

theorem le_chart (j : ℤ) : ⊤ ≤ (x.1 ≫ (G.ideal s).subschemeι) ⁻¹ᵁ (tw G.L₂ G.L j).U
    (twIdx j (G.second.chartAt (ptOf x.pt.1)) (G.chartAt (ptOf x.pt.1))) :=
  fun _ hw => mem_tw_U.2 ⟨G.second.le_chartAt x.pt.1 hw, G.le_chartAt x.pt.1 hw⟩

def val (j : ℕ) : G.SecOn s j →ₗ[K] K where
  toFun g := valOn x.1 _ (x.le_chart j) g
  map_add' f g := map_add _ f g
  map_smul' c g := valOn_smul x.1 x.2 _ _ c g

theorem c₁_pos (τ : K →+* ℂ) : 0 < x.c₁ τ := archSize_pos (G.herm τ) fun h =>
  G.geom.alg.bpf.coords_ne_zero x.pt.1 (funext fun k => (map_eq_zero τ).1 (congrFun h k))

theorem c₂_pos (τ : K →+* ℂ) : 0 < x.c₂ τ := archSize_pos (G.herm₂ τ) fun h =>
  G.alg₂.bpf.coords_ne_zero x.pt.1 (funext fun k => (map_eq_zero τ).1 (congrFun h k))

theorem ht_eq_pointHeight : x.ht = pointHeight G.w G.A (G.coords x.pt.1) := rfl

theorem ht_eq_ptHeight : x.ht = G.ptHeight x.pt := by
  have := vecHeight_smul_algebraMap K K _ _ G.w G.A G.geom.alg.spans G.herm K (G.coords x.pt.1) 1
    (G.geom.alg.bpf.coords_ne_zero _) one_ne_zero
  rw [one_smul] at this
  exact this.symm

theorem c₂_conj (τ : K →+* ℂ) : x.c₂ ((starRingEnd ℂ).comp τ) = x.c₂ τ := by
  let w (σ : K →+* ℂ) : CxPts G.str σ := Points.PtsOver.map (G.ideal s).subschemeι rfl (spMap σ) (x.along σ)
  have e (σ : K →+* ℂ) : (G.φ₂ σ).φ (G.second.chartAt (ptOf x.pt.1)) (w σ) = Real.log (x.c₂ σ ^ 2) := by
    refine (G.second.weight_φ _ _ σ _ (w σ)).trans (congrArg (fun y => Real.log (archSize _ y ^ 2)) (funext fun k => ?_))
    exact Points.valR_spMap_comp σ x.pt.1 _ (G.second.le_chartAt x.pt.1) _
  have h := G.isConj_φ₂ τ (G.second.chartAt (ptOf x.pt.1)) (w τ) (w _) (by
    change (spMap _ ≫ x.1) ≫ _ = spMap _ ≫ (spMap τ ≫ x.1) ≫ _
    rw [← Category.assoc (spMap (starRingEnd ℂ)), ← Category.assoc (spMap (starRingEnd ℂ)), ← Spec.map_comp]
    rfl) fun _ _ => G.second.le_chartAt x.pt.1 (Set.mem_univ _)
  have p := x.c₂_pos τ
  have p' := x.c₂_pos ((starRingEnd ℂ).comp τ)
  exact (pow_left_inj₀ p'.le p.le two_ne_zero).1
    (Real.log_injOn_pos (pow_pos p' 2) (pow_pos p 2) ((e _).symm.trans (h.trans (e τ))))

theorem exp_neg_weight (j : ℕ) (τ : K →+* ℂ) :
    Real.exp (-(Geo.weightOn s j τ).φ (fun _ => twIdx j (G.second.chartAt (ptOf x.pt.1)) (G.chartAt (ptOf x.pt.1)))
      (x.along τ)) = ((x.c₂ τ * x.c₁ τ ^ j) ^ 2)⁻¹ := by
  have e : (Geo.weightOn s j τ).φ (fun _ => twIdx j (G.second.chartAt (ptOf x.pt.1)) (G.chartAt (ptOf x.pt.1)))
      (x.along τ) = Real.log (x.c₂ τ ^ 2) + j * Real.log (x.c₁ τ ^ 2) := by
    simp only [Geo.weightOn, Weight.pull, Weight.linComb, Geo.φTw, Weight.tens, Weight.zpow, Geo.φ, Geo.φ₂,
      HermSys.weight_φ]
    have a₁ : ∀ k, secVal G.str τ (G.b k) (G.chartAt (ptOf x.pt.1))
        (Points.PtsOver.map (G.ideal s).subschemeι rfl (spMap τ) (x.along τ)) = τ (G.coords x.pt.1 k) :=
      fun k => Points.valR_spMap_comp τ x.pt.1 _ (G.le_chartAt x.pt.1) _
    have a₂ : ∀ k, secVal G.str τ (G.b₂ k) (G.second.chartAt (ptOf x.pt.1))
        (Points.PtsOver.map (G.ideal s).subschemeι rfl (spMap τ) (x.along τ)) = τ (G.second.coords x.pt.1 k) :=
      fun k => Points.valR_spMap_comp τ x.pt.1 _ (G.second.le_chartAt x.pt.1) _
    simp only [id, a₁, a₂, Finset.univ_unique, Finset.sum_singleton, Int.cast_one, one_mul, Int.cast_natCast, c₁, c₂]
  have p₁ := x.c₁_pos τ
  have p₂ := x.c₂_pos τ
  rw [e, Real.exp_neg, Real.exp_add, ← Real.log_pow, Real.exp_log (by positivity), Real.exp_log (by positivity), mul_pow,
    ← pow_mul, ← pow_mul, mul_comm 2 j]

theorem nsq_eq (j : ℕ) (τ : K →+* ℂ) {ι : Type} [Fintype ι] (c : ι → ℂ) (g : ι → G.SecOn s j) :
    (Geo.weightOn s j τ).nsq (∑ i, c i • cval τ (g i)) (x.along τ) =
      ‖∑ i, c i * τ (x.val j (g i))‖ ^ 2 / (x.c₂ τ * x.c₁ τ ^ j) ^ 2 := by
  have hw : x.along τ ∈ ptsIn ((G.ideal s).subschemeι ≫ G.str) τ (((tw G.L₂ G.L j).pull (G.ideal s).subschemeι).U
      fun _ => twIdx j (G.second.chartAt (ptOf x.pt.1)) (G.chartAt (ptOf x.pt.1))) :=
    fun _ _ => mem_pull.2 (x.le_chart j (Set.mem_univ _))
  rw [Weight.nsq_eq _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (cval_mem τ (g i))) hw, exp_neg_weight,
    div_eq_mul_inv]
  refine congrArg (fun r => ‖r‖ ^ 2 * _) ?_
  refine ((congrFun (Finset.sum_apply _ _ _) _).trans (Finset.sum_apply _ _ _)).trans ?_
  exact Finset.sum_congr rfl fun i _ => congrArg (c i * ·)
    ((cval_eq_val τ _ _ _ mem_ptsIn_top hw).trans (evalPt_spMap_comp τ x.1 _ _ _ _))

theorem nrm_eq (j : ℕ) (τ : K →+* ℂ) (g : G.SecOn s j) :
    x.nrm j τ g = ‖τ (x.val j g)‖ / (x.c₂ τ * x.c₁ τ ^ j) := by
  have := x.nsq_eq j τ (fun _ : Unit => 1) fun _ => g
  simp only [Finset.univ_unique, Finset.sum_singleton, one_smul, one_mul] at this
  have p₁ := x.c₁_pos τ
  have p₂ := x.c₂_pos τ
  rw [nrm, this, ← div_pow, Real.sqrt_sq (by positivity)]

theorem val_mulSecOn (j : ℕ) (u : Fin G.N → K) (g : G.SecOn s j) :
    x.val (j + 1) (mulSecOn G.isLB₂ G.isLB (G.comb u) (Nat.cast_succ j).symm g) =
      (∑ k, u k * G.coords x.pt.1 k) * x.val j g := by
  refine (valOn_mulSecOn G.isLB₂ G.isLB (G.comb u) _ g x.1 _ _ (G.le_chartAt x.pt.1) (x.le_chart j)
    (x.le_chart _)).trans (congrArg (· * _) ?_)
  refine (Points.valR_eq _ _ (G.le_chartAt x.pt.1) _).symm.trans ((G.val_comb x.pt.1 u).trans ?_)
  rw [LinSys.baseHom_ptOver]
  rfl

theorem along_injective (hs : G.IsGood s) {Ω : Type} [Field Ω] (φ : K →+* Ω) :
    Function.Injective fun x : RatPt G s => x.along φ := fun x x' h => by
  have := hs.finite
  have : IsAffine (G.ideal s).subscheme := isAffine_of_isAffineHom ((G.ideal s).subschemeι ≫ G.str)
  have e : spMap φ ≫ x.1 = spMap φ ≫ x'.1 := congrArg Subtype.val h
  refine Subtype.ext (ext_evalPt (isAffineOpen_top _) le_top le_top (RingHom.ext fun f => φ.injective ?_))
  rw [← evalPt_spMap_comp φ x.1 ⊤ le_top le_top, ← evalPt_spMap_comp φ x'.1 ⊤ le_top le_top]
  simp only [e]

end RatPt

variable {G : Geo K} {s : Fin G.D → Fin G.N → K}

def Coord.AtPoints {hs : G.IsGood s} {δ : ℕ} (Co : Coord G hs δ) (x : Fin δ ≃ RatPt G s) : Prop :=
  ∀ p, (∀ j g, Co.ev j g p = (x p).val j g) ∧ Co.y p = G.coords (x p).pt.1 ∧ ∀ τ, Co.c₂ τ p = (x p).c₂ τ

theorem RatPt.along_bijective (hs : G.IsGood s)
    (h : Function.Surjective fun x : RatPt G s => x.along (algebraMap K (AlgebraicClosure K)))
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] (φ : K →+* Ω) : Function.Bijective fun x : RatPt G s => x.along φ := by
  have := hs.finite
  have := hs.etale
  letI := φ.toAlgebra
  have hB := isLB_tw G.isLB₂ G.isLB 0
  have : Finite (Points.PtsOver ((G.ideal s).subschemeι ≫ G.str) (spMap φ)) := finite_ptsOver _ Ω
  refine (RatPt.along_injective hs φ).bijective_of_nat_card_le (le_of_eq ?_)
  exact (finrank_H0On (p := G.str) (I := G.ideal s) hB Ω).symm.trans
    ((finrank_H0On hB (AlgebraicClosure K)).trans (Nat.card_eq_of_bijective _ ⟨RatPt.along_injective hs _, h⟩).symm)

theorem exists_coord_atPoints (hs : G.IsGood s)
    (h : Function.Surjective fun x : RatPt G s => x.along (algebraMap K (AlgebraicClosure K)))
    {δ : ℕ} (x : Fin δ ≃ RatPt G s) : ∃ Co : Coord G hs δ, Co.AtPoints x := by
  have := hs.finite
  have := hs.etale
  let φ (j : ℕ) : G.SecOn s j →ₗ[K] (Fin δ → K) := LinearMap.pi fun p => (x p).val j
  have bij (j : ℕ) : Function.Bijective (φ j) := by
    have hB := isLB_tw G.isLB₂ G.isLB (j : ℤ)
    choose r hr using h
    have inj : Function.Injective (φ j) := (injective_iff_map_eq_zero _).2 fun g hg => by
      have hr' (w : PtsOver (AlgebraicClosure K) ((G.ideal s).subschemeι ≫ G.str)) :
          w.1 = spMap (algebraMap K (AlgebraicClosure K)) ≫ (r w).1 := (congrArg Subtype.val (hr w)).symm
      refine eq_zero_of_forall_valOn_eq_zero (Ω := AlgebraicClosure K) hB
        (fun w => twIdx j (G.second.chartAt (ptOf (r w).pt.1)) (G.chartAt (ptOf (r w).pt.1)))
        (fun w => by rw [hr' w]; exact fun _ _ => (r w).le_chart j (Set.mem_univ _)) fun w => ?_
      have e : (r w).val j g = 0 := by simpa [φ] using congrFun hg (x.symm (r w))
      have key : ∀ (z : Sp (AlgebraicClosure K) ⟶ (G.ideal s).subscheme) (hz),
          z = spMap (algebraMap K (AlgebraicClosure K)) ≫ (r w).1 →
          valOn z (twIdx j (G.second.chartAt (ptOf (r w).pt.1)) (G.chartAt (ptOf (r w).pt.1))) hz g = 0 := by
        rintro _ hz rfl
        exact (evalPt_spMap_comp _ (r w).1 _ _ _ _).trans ((congrArg _ e).trans (map_zero _))
      exact key _ _ (hr' w)
    have := finite_H0On (p := G.str) (I := G.ideal s) hB
    refine ⟨inj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 inj⟩
    rw [finrank_H0On hB (AlgebraicClosure K), Module.finrank_fin_fun, ← Nat.card_fin δ, Nat.card_congr x]
    exact (Nat.card_eq_of_bijective _ ⟨RatPt.along_injective hs _, fun w => ⟨r w, hr w⟩⟩).symm
  refine ⟨⟨fun j => LinearEquiv.ofBijective (φ j) (bij j), fun p => G.coords (x p).pt.1, fun σ p => (x p).c₂ σ,
    fun _ => G.geom.alg.bpf.coords_ne_zero _, fun σ p => (x p).c₂_pos σ, fun σ p => (x p).c₂_conj σ,
    fun j u g => funext fun p => (x p).val_mulSecOn j u g, fun j σ m c g => ?_⟩, fun p => ⟨fun _ _ => rfl, rfl, fun _ => rfl⟩⟩
  refine (csq_pointHerm _ _ _ σ c g).trans ?_
  rw [← finsum_comp_equiv (x.trans (Equiv.ofBijective _ (RatPt.along_bijective hs h σ))), finsum_eq_sum_of_fintype]
  exact Finset.sum_congr rfl fun p _ => (x p).nsq_eq j σ c g

theorem Coord.AtPoints.norm_ev {hs : G.IsGood s} {δ : ℕ} {Co : Coord G hs δ} {x : Fin δ ≃ RatPt G s} (h : Co.AtPoints x)
    (p : Fin δ) (τ : K →+* ℂ) (g : G.SecOn s 0) : ‖τ (Co.ev 0 g p)‖ / Co.c₂ τ p = (x p).nrm 0 τ g := by
  rw [RatPt.nrm_eq, (h p).1, (h p).2.2, pow_zero, mul_one]

theorem Coord.AtPoints.vecHt_eq {hs : G.IsGood s} {δ : ℕ} {Co : Coord G hs δ} {x : Fin δ ≃ RatPt G s} (h : Co.AtPoints x)
    (p : Fin δ) : vecHt (fun k => Co.gen k p) (fun τ => Co.c₁ τ p) = (x p).ht := by
  simp only [Coord.gen, Coord.c₁, (h p).2.1]
  rfl

theorem nrm_normOn_sq_eq (hs : G.IsGood s)
    (h : Function.Surjective fun x : RatPt G s => x.along (algebraMap K (AlgebraicClosure K))) (j : ℕ) (τ : K →+* ℂ)
    (g : G.SecOn s j) : (hs.normOn j).nrm τ g ^ 2 = ∑ᶠ x : RatPt G s, x.nrm j τ g ^ 2 := by
  rw [hs.nrm_normOn_sq, ← finsum_comp_equiv (Equiv.ofBijective _ (RatPt.along_bijective hs h τ))]
  exact finsum_congr fun x => (Real.sq_sqrt (Weight.nsq_nonneg _ _ _)).symm

section Split

variable {F : Type} [Field F] [NumberField F] (G : Geo F) (E : Type) [Field E] [NumberField E] [Algebra F E]
  (s : Fin G.D → Fin G.N → E)

def RatPt.geomPt (x : RatPt (G.baseChange E) s) : (G.toLinSys.baseChange E).Pt (AlgebraicClosure E) :=
  Points.PtsOver.map ((G.baseChange E).ideal s).subschemeι rfl _ (x.along (algebraMap E (AlgebraicClosure E)))

variable {G E s}

theorem RatPt.ptHeight_geomPt (x : RatPt (G.baseChange E) s) :
    haveI : Algebra.IsAlgebraic F (AlgebraicClosure E) := Algebra.IsAlgebraic.trans F E _
    G.ptHeight (LinSys.toBase (RatPt.geomPt G E s x)) = x.ht := by
  haveI : Algebra.IsAlgebraic F (AlgebraicClosure E) := Algebra.IsAlgebraic.trans F E _
  obtain ⟨c, hc, e⟩ := G.exists_coords_baseChange E x.pt.1
  have h₀ := G.geom.alg.bpf.coords_ne_zero (x.pt.1 ≫ G.bcFst E)
  have h₁ := vecHeight_smul_algebraMap F E _ _ G.w G.A G.geom.alg.spans G.herm (AlgebraicClosure E) _ 1 h₀ one_ne_zero
  have h₃ := vecHeight_smul_algebraMap F E _ _ G.w G.A G.geom.alg.spans G.herm E _ c h₀ hc
  have h₄ := vecHeight_smul_algebraMap F E _ _ G.w G.A G.geom.alg.spans G.herm E _ 1 (smul_ne_zero hc h₀) one_ne_zero
  rw [one_smul] at h₁ h₄
  have h₅ : G.coords (LinSys.toBase (RatPt.geomPt G E s x)).1 =
      fun j => algebraMap E (AlgebraicClosure E) (G.coords (x.pt.1 ≫ G.bcFst E) j) := by
    rw [← LinSys.coords_spMap_comp]
    exact congrArg G.coords ((congrArg (· ≫ G.bcFst E) (Category.assoc _ _ _)).trans (Category.assoc _ _ _))
  rw [HermSys.ptHeight, h₅, h₁]
  exact (h₃.symm.trans h₄).trans (congrArg (pointHeight G.w G.A) e.symm)

theorem Split.along_surjective (h : Split G.toTuple E s) :
    Function.Surjective fun x : RatPt (G.baseChange E) s => x.along (algebraMap E (AlgebraicClosure E)) := fun w => by
  obtain ⟨x₀, e⟩ := h w.1 w.2
  refine ⟨⟨x₀, ?_⟩, Subtype.ext e.symm⟩
  have h₁ := (G.baseChange E).comp_str (x₀ ≫ ((G.baseChange E).ideal s).subschemeι)
  have h₃ := (Category.assoc _ _ _).symm.trans h₁
  have h₂ := (Spec.map_comp _ _).trans ((congrArg (spMap (algebraMap E (AlgebraicClosure E)) ≫ ·) h₃).symm.trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e).symm.trans w.2)))
  refine h₃.trans (congrArg spMap (RingHom.ext fun a => (algebraMap E (AlgebraicClosure E)).injective ?_))
  exact congrArg (fun f => f.hom a) (Spec.map_injective h₂)

theorem Split.geomPts_eq (h : Split G.toTuple E s) :
    G.geomPts E (G.linSection E s) = Set.range (RatPt.geomPt G E s) := by
  refine Set.ext fun y => ⟨fun ⟨z, hz⟩ => ?_, fun ⟨x, hx⟩ => ⟨_, congrArg Subtype.val hx⟩⟩
  obtain ⟨x, hx⟩ := h.along_surjective ⟨z, (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hz).trans y.2)⟩
  exact ⟨x, Subtype.ext ((congrArg (fun t => t.1 ≫ _) hx).trans hz)⟩

theorem RatPt.geomPt_injective (hs : (G.baseChange E).IsGood s) : Function.Injective (RatPt.geomPt G E s) :=
  fun _ _ h => RatPt.along_injective hs _ (Subtype.ext ((cancel_mono ((G.baseChange E).ideal s).subschemeι).1
    (congrArg Subtype.val h)))

theorem Split.exists_coord (h : Split G.toTuple E s) (hs : (G.baseChange E).IsGood s) :
    ∃ (x : Fin (G.geomPts E (G.linSection E s)).ncard ≃ RatPt (G.baseChange E) s)
      (Co : Coord (G.baseChange E) hs (G.geomPts E (G.linSection E s)).ncard),
      Co.AtPoints x ∧ G.cycleHeight E (G.linSection E s) = ∑ p, (x p).ht := by
  have hfin := (Geo.isGood_baseChange_iff.1 hs).finite_geomPts
  have : Finite (RatPt (G.baseChange E) s) :=
    (Set.finite_range_iff (RatPt.geomPt_injective hs)).1 (h.geomPts_eq ▸ hfin)
  have e : Nat.card (RatPt (G.baseChange E) s) = (G.geomPts E (G.linSection E s)).ncard := by
    rw [h.geomPts_eq, Set.ncard_range_of_injective (RatPt.geomPt_injective hs)]
  let x := (Finite.equivFinOfCardEq e).symm
  obtain ⟨Co, hCo⟩ := exists_coord_atPoints hs h.along_surjective x
  refine ⟨x, Co, hCo, ?_⟩
  rw [HermSys.cycleHeight]
  refine (finsum_mem_congr h.geomPts_eq fun _ _ => rfl).trans ?_
  rw [finsum_mem_range (RatPt.geomPt_injective hs), ← finsum_comp_equiv x, finsum_eq_sum_of_fintype]
  exact Finset.sum_congr rfl fun p _ => (x p).ptHeight_geomPt

end Split

end GlobalTheory.HSCore
