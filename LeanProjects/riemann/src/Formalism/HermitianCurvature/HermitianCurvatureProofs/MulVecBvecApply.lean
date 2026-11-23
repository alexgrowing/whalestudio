import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeisenbergLeviConjugationMeasure
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwoByOneBlock

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBM

open Formalism.FourierDecayAlt.P.Dx2.Tower

section lev

variable {k : ℕ}

theorem hpk_levPos_gen (o ρ : ℕ) (i j : Fin (2 * ρ + k + 1)) :
    Hpk k (o + ρ) (levPos k o ρ i) (levPos k o ρ j) = Hpk k ρ i j := by
  have e1 : (levPos k o ρ i = levPos k o ρ j) ↔ i.val = j.val := by
    simp only [levPos, Fin.ext_iff]; omega
  have e2 : (i = j) ↔ i.val = j.val := Fin.ext_iff
  have hi : (levPos k o ρ i).val = i.val + o := rfl
  have hj : (levPos k o ρ j).val = j.val + o := rfl
  have := i.isLt; have := j.isLt
  unfold Hpk
  simp only [e1, e2, hi, hj]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem herm_lift_gen (o ρ : ℕ) (y y' : Fin (2 * ρ + k + 1) → ℂ) :
    herm (Hpk k (o + ρ)) (liftVec k o ρ y) (liftVec k o ρ y') = herm (Hpk k ρ) y y' := by
  simp only [herm, dotProduct, mulVec, Pi.star_apply]
  rw [sum_lift_gen o ρ _ (fun p hp => by rw [liftVec_out_gen o ρ y' p hp, star_zero, zero_mul])]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [liftVec_levPos_gen]
  congr 1
  rw [sum_lift_gen o ρ _ (fun q hq => by rw [liftVec_out_gen o ρ y q hq, mul_zero])]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [hpk_levPos_gen, liftVec_levPos_gen]

theorem liftVec_inj (o ρ : ℕ) {v w : Fin (2 * ρ + k + 1) → ℂ} (h : liftVec k o ρ v = liftVec k o ρ w) : v = w := by
  funext p
  have hp := p.isLt
  have h1 := congrFun h (levPos k o ρ p)
  have hp' : (p : ℕ) ≤ 2 * ρ + k := by omega
  simpa [liftVec, levPos, hp'] using h1

theorem mulVec_bvec_apply {m : ℕ} (G : Matrix (Fin m) (Fin m) ℂ) (q p : Fin m) : (G *ᵥ bvec q) p = G p q := by
  simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem herm_bvec_r {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (v : Fin m → ℂ) (p : Fin m) :
    herm H v (bvec p) = ∑ x, H p x * v x := by
  simp only [herm, bvec, Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single p]
  · simp
  · intro b _ hb
    simp [Pi.single_apply, hb]
  · simp

theorem hpk_esI_row {r : ℕ} (b : Fin r) (x : Fin (2 * r + k + 1)) :
    Hpk k r (esI k r b) x = if x = eI k r b then 1 else 0 := by
  have hb := b.isLt
  rcases x with ⟨x, hx⟩
  simp only [Hpk, esI, eI, Fin.mk.injEq]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hpk_eI_row {r : ℕ} (b : Fin r) (x : Fin (2 * r + k + 1)) :
    Hpk k r (eI k r b) x = if x = esI k r b then 1 else 0 := by
  have hb := b.isLt
  rcases x with ⟨x, hx⟩
  simp only [Hpk, esI, eI, Fin.mk.injEq]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem herm_bvec_esI' {r : ℕ} (v : Fin (2 * r + k + 1) → ℂ) (b : Fin r) :
    herm (Hpk k r) v (bvec (esI k r b)) = v (eI k r b) := by
  rw [herm_bvec_r]
  simp only [hpk_esI_row, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

theorem herm_bvec_eI' {r : ℕ} (v : Fin (2 * r + k + 1) → ℂ) (b : Fin r) :
    herm (Hpk k r) v (bvec (eI k r b)) = v (esI k r b) := by
  rw [herm_bvec_r]
  simp only [hpk_eI_row, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

def midB (o ρ : ℕ) (G : B.Mat k (o + ρ)) : B.Mat k ρ := fun a b => G (levPos k o ρ a) (levPos k o ρ b)

theorem midB_lev (o ρ : ℕ) (y : B.Mat k ρ) : midB o ρ (ιLev k o ρ y) = y := by
  ext a b; exact lev_levPos o ρ y a b

theorem midB_cont (o ρ : ℕ) : Continuous (midB (k := k) o ρ) := by
  unfold midB
  exact continuous_pi fun a => continuous_pi fun b =>
    (continuous_apply (levPos k o ρ b)).comp (continuous_apply (levPos k o ρ a))

theorem uw_block (o ρ : ℕ) (z : Fin (2 * ρ + k + 1) → ℂ) (G : B.Mat k (o + ρ))
    (hG : G ∈ UWset k (o + ρ) (liftVec k o ρ z)) : ιLev k o ρ (midB o ρ G) = G := by
  have hfix : ∀ q : Fin (2 * (o + ρ) + k + 1), ¬ (o ≤ q.val ∧ q.val < 2 * ρ + k + 1 + o) → G *ᵥ bvec q = bvec q := by
    intro q hq
    by_cases h1 : q.val < o
    · have e : q = eI k (o + ρ) ⟨q.val, by omega⟩ := by ext; simp [eI]
      rw [e]; exact (hG.2.1 _).1
    · have e : q = esI k (o + ρ) ⟨2 * (o + ρ) + k - q.val, by omega⟩ := by ext; simp [esI]; omega
      rw [e]; exact (hG.2.1 _).2
  ext p q
  by_cases hq : o ≤ q.val ∧ q.val < 2 * ρ + k + 1 + o
  · by_cases hp : o ≤ p.val ∧ p.val < 2 * ρ + k + 1 + o
    · have ep : p = levPos k o ρ ⟨p.val - o, by omega⟩ := by ext; simp [levPos]; omega
      have eq : q = levPos k o ρ ⟨q.val - o, by omega⟩ := by ext; simp [levPos]; omega
      rw [ep, eq, lev_levPos]; rfl
    · rw [lev_out_row o ρ _ p q hp, if_neg (by intro h; rw [h] at hp; exact hp hq)]
      rw [show G p q = (G *ᵥ bvec q) p from (mulVec_bvec_apply G q p).symm]
      have hqne : ∀ c : Fin (2 * (o + ρ) + k + 1), ¬ (o ≤ c.val ∧ c.val < 2 * ρ + k + 1 + o) → bvec q c = 0 := by
        intro c hc
        simp only [bvec, Pi.single_apply]
        rw [if_neg]; intro h; rw [h] at hc; exact hc hq
      by_cases h1 : p.val < o
      · have e : p = eI k (o + ρ) ⟨p.val, by omega⟩ := by ext; simp [eI]
        rw [e, ← herm_bvec_esI' (G *ᵥ bvec q), ← (hG.2.1 _).2, TwoByOneBlock.herm_UH hG.1, herm_bvec_esI']
        refine (hqne _ ?_).symm
        simp [eI]; omega
      · have e : p = esI k (o + ρ) ⟨2 * (o + ρ) + k - p.val, by omega⟩ := by ext; simp [esI]; omega
        rw [e, ← herm_bvec_eI' (G *ᵥ bvec q), ← (hG.2.1 _).1, TwoByOneBlock.herm_UH hG.1, herm_bvec_eI']
        refine (hqne _ ?_).symm
        simp [esI]; omega
  · rw [lev_out_col o ρ _ p q hq, show G p q = (G *ᵥ bvec q) p from (mulVec_bvec_apply G q p).symm, hfix q hq]
    simp [bvec, Pi.single_apply]

theorem uw_mid (o ρ : ℕ) (z : Fin (2 * ρ + k + 1) → ℂ) (G : B.Mat k (o + ρ))
    (hG : G ∈ UWset k (o + ρ) (liftVec k o ρ z)) : midB o ρ G ∈ UWset k ρ z := by
  have hb := uw_block o ρ z G hG
  have hlift : ∀ v, liftVec k o ρ (midB o ρ G *ᵥ v) = G *ᵥ liftVec k o ρ v := by
    intro v; rw [← lev_mulVec_lift, hb]
  refine ⟨TwoByOneBlock.mem_UH_of_herm fun x x' => ?_, fun a => ⟨?_, ?_⟩, ?_⟩
  · rw [← herm_lift_gen o ρ, hlift, hlift, TwoByOneBlock.herm_UH hG.1, herm_lift_gen]
  · apply liftVec_inj o ρ
    rw [hlift, ← bvec_levPos]
    have e : levPos k o ρ (eI k ρ a) = eI k (o + ρ) ⟨a.val + o, by omega⟩ := by ext; simp [levPos, eI]
    rw [e]; exact (hG.2.1 _).1
  · apply liftVec_inj o ρ
    rw [hlift, ← bvec_levPos]
    have e : levPos k o ρ (esI k ρ a) = esI k (o + ρ) ⟨a.val + o, by omega⟩ := by
      have := a.isLt; ext; simp [levPos, esI]; omega
    rw [e]; exact (hG.2.1 _).2
  · apply liftVec_inj o ρ
    rw [hlift]; exact hG.2.2

def levMt {r : ℕ} (o ρ : ℕ) (h : o + ρ = r) (x : Mt k ρ) : Mt k r :=
  Matrix.of.symm (D.castM h (ιLev k o ρ (Matrix.of x)))

def midMt {r : ℕ} (o ρ : ℕ) (h : o + ρ = r) (x : Mt k r) : Mt k ρ :=
  Matrix.of.symm (midB o ρ (D.castM h.symm (Matrix.of x)))

theorem midMt_levMt {r : ℕ} (o ρ : ℕ) (h : o + ρ = r) (x : Mt k ρ) : midMt o ρ h (levMt o ρ h x) = x := by
  subst h
  simp only [midMt, levMt, Equiv.apply_symm_apply, Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]
  rw [midB_lev]; rfl

theorem levMt_cont {r : ℕ} (o ρ : ℕ) (h : o + ρ = r) : Continuous (levMt (k := k) o ρ h) := by
  subst h
  have e : levMt (k := k) o ρ rfl = fun x => ιLev k o ρ (Matrix.of x) := by
    funext x; simp only [levMt, Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]; rfl
  rw [e]; exact lev_cont o ρ

theorem midMt_cont {r : ℕ} (o ρ : ℕ) (h : o + ρ = r) : Continuous (midMt (k := k) o ρ h) := by
  subst h
  have e : midMt (k := k) o ρ rfl = fun x => midB o ρ (Matrix.of x) := by
    funext x; simp only [midMt, Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]; rfl
  rw [e]; exact midB_cont o ρ

theorem levMt_emb {r : ℕ} (o ρ : ℕ) (h : o + ρ = r) : MeasurableEmbedding (levMt (k := k) o ρ h) :=
  (Function.LeftInverse.isClosedEmbedding (midMt_levMt o ρ h) (midMt_cont o ρ h) (levMt_cont o ρ h)).measurableEmbedding

theorem levMt_mem {r : ℕ} (o ρ : ℕ) (h : o + ρ = r) (z : Fin (2 * ρ + k + 1) → ℂ) (x : Mt k ρ)
    (hx : Matrix.of x ∈ UWset k ρ z) :
    Matrix.of (levMt o ρ h x) ∈ UWset k r (D.castV h (liftVec k o ρ z)) := by
  subst h
  simp only [levMt, Equiv.apply_symm_apply, Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl, castV_rfl]
  exact lev_UW o ρ z _ hx

theorem levMt_surj {r : ℕ} (o ρ : ℕ) (h : o + ρ = r) (z : Fin (2 * ρ + k + 1) → ℂ) (G : B.Mat k r)
    (hG : G ∈ UWset k r (D.castV h (liftVec k o ρ z))) :
    ∃ y : B.Mat k ρ, y ∈ UWset k ρ z ∧ D.castM h (ιLev k o ρ y) = G := by
  subst h
  rw [castV_rfl] at hG
  exact ⟨midB o ρ G, uw_mid o ρ z G hG, by rw [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl, uw_block o ρ z G hG]⟩

theorem haar_lev {r : ℕ} (o ρ : ℕ) (h : o + ρ = r) (z : Fin (2 * ρ + k + 1) → ℂ) (Z : Fin (2 * r + k + 1) → ℂ)
    (hZ : D.castV h (liftVec k o ρ z) = Z) (μ : Measure (Mt k r)) (ν : Measure (Mt k ρ))
    (hμ : B.IsHaarOn (UWset k r Z) μ) (hν : B.IsHaarOn (UWset k ρ z) ν) (hμ1 : μ Set.univ = 1)
    (hν1 : ν Set.univ = 1) : μ = ν.map (levMt o ρ h) := by
  subst hZ
  have hm : Measurable (levMt (k := k) o ρ h) := (levMt_cont o ρ h).measurable
  have hcl := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r (D.castV h (liftVec k o ρ z))
  have hconc : (ν.map (levMt o ρ h)) (UWset k r (D.castV h (liftVec k o ρ z)))ᶜ = 0 := by
    have hms : @MeasurableSet (Mt k r) _ (UWset k r (D.castV h (liftVec k o ρ z))) :=
      IsClosed.measurableSet (α := Mt k r) hcl.closed
    rw [Measure.map_apply hm hms.compl]
    refine measure_mono_null (fun x hx => ?_) hν.conc
    intro hx'; exact hx (levMt_mem o ρ h z x hx')
  have hleft : ∀ a ∈ UWset k r (D.castV h (liftVec k o ρ z)),
      (ν.map (levMt o ρ h)).map (lmulM a) = ν.map (levMt o ρ h) := by
    intro a ha
    obtain ⟨y, hy, rfl⟩ := levMt_surj o ρ h z a ha
    rw [Measure.map_map (B2x5.measurable_lmulM _) hm]
    have e : lmulM (D.castM h (ιLev k o ρ y)) ∘ levMt o ρ h = levMt o ρ h ∘ lmulM y := by
      funext x
      subst h
      simp only [Function.comp, levMt, lmulM, Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl, Equiv.apply_symm_apply]
      show ιLev k o ρ y * ιLev k o ρ (Matrix.of x) = ιLev k o ρ (y * Matrix.of x)
      rw [lev_mul]
    rw [e, ← Measure.map_map hm (B2x5.measurable_lmulM _), hν.left y hy]
  have hfin : ∀ K : Set (Mt k r), IsCompact K → (ν.map (levMt o ρ h)) K < ⊤ := by
    intro K _
    calc (ν.map (levMt o ρ h)) K ≤ (ν.map (levMt o ρ h)) Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := by rw [Measure.map_apply hm MeasurableSet.univ, Set.preimage_univ, hν1]
      _ < ⊤ := ENNReal.one_lt_top
  obtain ⟨c, hc⟩ := Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar k r _ μ (ν.map (levMt o ρ h)) hcl hμ hconc hleft hfin
  have h1 : (ν.map (levMt o ρ h)) Set.univ = 1 := by
    rw [Measure.map_apply hm MeasurableSet.univ, Set.preimage_univ, hν1]
  rw [hc, Measure.smul_apply, hμ1] at h1
  have hc1 : c = 1 := by
    have h2 : ((c : ENNReal)) = 1 := by simpa [ENNReal.smul_def] using h1
    exact_mod_cast h2
  rw [hc, hc1, one_smul]

end lev

section tower

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem tower_haarW (T : D.LevTower k r Wp Wq) (hT : D.TowerNormalised T) (i : ℕ) (hi : i ≤ r)
    (h : i + (r - i) = r) : T.base.μW = (T.bs i).μW.map (levMt i (r - i) h) :=
  haar_lev i (r - i) h (T.bs i).z T.base.z (T.z_lev i hi) T.base.μW (T.bs i).μW T.base.haarW (T.bs i).haarW
    (hT 0 (Nat.zero_le r)).1 (hT i hi).1

theorem tower_haarW' (T : D.LevTower k r Wp Wq) (hT : D.TowerNormalised T) (i : ℕ) (hi : i ≤ r)
    (h : i + (r - i) = r) : T.base.μW' = (T.bs i).μW'.map (levMt i (r - i) h) :=
  haar_lev i (r - i) h (T.bs i).z' T.base.z' (T.z'_lev i hi) T.base.μW' (T.bs i).μW' T.base.haarW' (T.bs i).haarW'
    (hT 0 (Nat.zero_le r)).2.1 (hT i hi).2.1

theorem tower_intW {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (T : D.LevTower k r Wp Wq)
    (hT : D.TowerNormalised T) (i : ℕ) (hi : i ≤ r) (h : i + (r - i) = r) (f : Mt k r → E) :
    ∫ x, f x ∂T.base.μW = ∫ y, f (levMt i (r - i) h y) ∂(T.bs i).μW := by
  rw [tower_haarW T hT i hi h]
  exact (levMt_emb i (r - i) h).integral_map _

theorem tower_intW' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (T : D.LevTower k r Wp Wq)
    (hT : D.TowerNormalised T) (i : ℕ) (hi : i ≤ r) (h : i + (r - i) = r) (f : Mt k r → E) :
    ∫ x, f x ∂T.base.μW' = ∫ y, f (levMt i (r - i) h y) ∂(T.bs i).μW' := by
  rw [tower_haarW' T hT i hi h]
  exact (levMt_emb i (r - i) h).integral_map _

theorem tower_haarWW' (T : D.LevTower k r Wp Wq) (hT : D.TowerNormalised T) (i : ℕ) (hi : i ≤ r)
    (h : i + (r - i) = r) :
    T.base.μW.prod T.base.μW' =
      ((T.bs i).μW.prod (T.bs i).μW').map (Prod.map (levMt i (r - i) h) (levMt i (r - i) h)) := by
  have : IsFiniteMeasure (T.bs i).μW := ⟨by rw [(hT i hi).1]; exact ENNReal.one_lt_top⟩
  have : IsFiniteMeasure (T.bs i).μW' := ⟨by rw [(hT i hi).2.1]; exact ENNReal.one_lt_top⟩
  have hm : Measurable (levMt (k := k) i (r - i) h) := (levMt_cont i (r - i) h).measurable
  rw [tower_haarW T hT i hi h, tower_haarW' T hT i hi h, Measure.map_prod_map _ _ hm hm]

theorem tower_intWW' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (T : D.LevTower k r Wp Wq)
    (hT : D.TowerNormalised T) (i : ℕ) (hi : i ≤ r) (h : i + (r - i) = r) (f : Mt k r × Mt k r → E) :
    ∫ p, f p ∂(T.base.μW.prod T.base.μW') =
      ∫ q, f (levMt i (r - i) h q.1, levMt i (r - i) h q.2) ∂((T.bs i).μW.prod (T.bs i).μW') := by
  rw [tower_haarWW' T hT i hi h]
  exact ((levMt_emb i (r - i) h).prodMap (levMt_emb i (r - i) h)).integral_map _

theorem tower_π (T : D.LevTower k r Wp Wq) (i : ℕ) (hi : i ≤ r) (h : i + (r - i) = r) (y : Mt k (r - i)) :
    (T.bs i).π (Matrix.of y) = T.base.π (Matrix.of (levMt i (r - i) h y)) := by
  rw [T.π_lev i hi]; rfl

theorem tower_π' (T : D.LevTower k r Wp Wq) (i : ℕ) (hi : i ≤ r) (h : i + (r - i) = r) (y : Mt k (r - i)) :
    (T.bs i).π' (Matrix.of y) = T.base.π' (Matrix.of (levMt i (r - i) h y)) := by
  rw [T.π'_lev i hi]; rfl

theorem tower_mem (T : D.LevTower k r Wp Wq) (i : ℕ) (hi : i ≤ r) (h : i + (r - i) = r) (x : Mt k (r - i))
    (hx : Matrix.of x ∈ UWset k (r - i) (T.bs i).z) : Matrix.of (levMt i (r - i) h x) ∈ UWset k r T.base.z := by
  have := levMt_mem i (r - i) h (T.bs i).z x hx
  rwa [T.z_lev i hi] at this

theorem tower_mem' (T : D.LevTower k r Wp Wq) (i : ℕ) (hi : i ≤ r) (h : i + (r - i) = r) (x : Mt k (r - i))
    (hx : Matrix.of x ∈ UWset k (r - i) (T.bs i).z') : Matrix.of (levMt i (r - i) h x) ∈ UWset k r T.base.z' := by
  have := levMt_mem i (r - i) h (T.bs i).z' x hx
  rwa [T.z'_lev i hi] at this

end tower

section conj

variable {k j ρ : ℕ}

def rnAct (a : B.Mat k ρ) (x : U.RC k j ρ) : U.RC k j ρ := (Matrix.of.symm (a * Matrix.of x.1), x.2)

theorem embG_inv (y : B.Mat k ρ) (hy : IsUnit y.det) : (U.embG k j ρ y)⁻¹ = U.embG k j ρ y⁻¹ := by
  refine Matrix.inv_eq_right_inv ?_
  rw [← lev_eq_embG, ← lev_eq_embG, ← lev_mul, Matrix.mul_nonsing_inv _ hy, lev_one]

theorem embG_conj_Rn (y : B.Mat k ρ) (hy : y ∈ B.GV k ρ) (x : U.RC k j ρ) :
    (U.embG k j ρ y)⁻¹ * U.Rn k j ρ x * U.embG k j ρ y = U.Rn k j ρ (rnAct y⁻¹ x) := by
  have hu : IsUnit y.det := by
    have := B2x5.normSq_det_GV hy
    refine isUnit_iff_ne_zero.2 fun h0 => ?_
    rw [h0, Complex.normSq_zero] at this; exact zero_ne_one this
  have hy' : yᴴ * Hpk k ρ * y = Hpk k ρ := hy
  have ha : (y⁻¹)ᴴ * Hpk k ρ = Hpk k ρ * y := by
    have e : (y⁻¹)ᴴ * yᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hu, Matrix.conjTranspose_one]
    calc (y⁻¹)ᴴ * Hpk k ρ = (y⁻¹)ᴴ * (yᴴ * Hpk k ρ * y) := by rw [hy']
      _ = ((y⁻¹)ᴴ * yᴴ) * Hpk k ρ * y := by simp only [Matrix.mul_assoc]
      _ = Hpk k ρ * y := by rw [e, Matrix.one_mul]
  have haa : (y⁻¹)ᴴ * Hpk k ρ * y⁻¹ = Hpk k ρ := by
    rw [ha, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
  have hq : ∀ c : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ,
      (y⁻¹ * c)ᴴ * Hpk k ρ * (y⁻¹ * c) = cᴴ * Hpk k ρ * c := by
    intro c
    rw [Matrix.conjTranspose_mul]
    calc cᴴ * (y⁻¹)ᴴ * Hpk k ρ * (y⁻¹ * c) = cᴴ * ((y⁻¹)ᴴ * Hpk k ρ * y⁻¹) * c := by
          simp only [Matrix.mul_assoc]
      _ = cᴴ * Hpk k ρ * c := by rw [haa]
  have hp : ∀ c : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ,
      -(G.wMat j * cᴴ * Hpk k ρ) * y = -(G.wMat j * (y⁻¹ * c)ᴴ * Hpk k ρ) := by
    intro c
    rw [Matrix.conjTranspose_mul, Matrix.neg_mul]
    congr 1
    simp only [Matrix.mul_assoc]
    rw [ha]
  rw [embG_inv y hu, Ux3.rn_eq, Ux3.rn_eq, U.embG, U.embG, Ux3.block3_mul, Ux3.block3_mul]
  refine Ux2.block3_congr ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp
  · simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, rnAct,
      Equiv.apply_symm_apply]
    exact hp _
  · simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, rnAct,
      Equiv.apply_symm_apply]
    rw [hq]
  · simp
  · simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
    exact Matrix.nonsing_inv_mul _ hu
  · simp [rnAct]
  · simp
  · simp
  · simp

theorem embG_conj_mMap (y y' : B.Mat k ρ) (hy : IsUnit y.det) (Z : Matrix (Fin j) (Fin j) ℂ) (γ : B.Mat k ρ) :
    (U.embG k j ρ y)⁻¹ * U.mMap k j ρ Z γ * U.embG k j ρ y' = U.mMap k j ρ Z (y⁻¹ * γ * y') := by
  rw [embG_inv y hy, Ux4.embG_mul_mMap, Ux4.mMap_mul_embG]

theorem mulLeft_mp (a : B.Mat k ρ) (ha : Complex.normSq a.det = 1) :
    MeasurePreserving (fun y : Fin (2 * ρ + k + 1) → Fin j → ℂ => Matrix.of.symm (a * Matrix.of y)) volume volume := by
  have h1 := Dx2.SL.swap_mp (2 * ρ + k + 1) j
  have h2 : MeasurePreserving (fun (y : Fin j → Fin (2 * ρ + k + 1) → ℂ) (i : Fin j) => Matrix.vecMul (y i) aᵀ)
      volume volume :=
    measurePreserving_pi (fun _ => volume) (fun _ => volume) (f := fun _ x => Matrix.vecMul x aᵀ)
      (fun _ => Dx2.SL.row_mp aᵀ (by rw [Matrix.det_transpose]; exact ha))
  have h3 := Dx2.SL.swap_mp j (2 * ρ + k + 1)
  have e : (fun y : Fin (2 * ρ + k + 1) → Fin j → ℂ => Matrix.of.symm (a * Matrix.of y)) =
      (fun (y : Fin j → Fin (2 * ρ + k + 1) → ℂ) (p : Fin (2 * ρ + k + 1)) (i : Fin j) => y i p) ∘
        (fun (y : Fin j → Fin (2 * ρ + k + 1) → ℂ) (i : Fin j) => Matrix.vecMul (y i) aᵀ) ∘
          (fun (y : Fin (2 * ρ + k + 1) → Fin j → ℂ) (i : Fin j) (p : Fin (2 * ρ + k + 1)) => y p i) := by
    funext y p i
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, mul_comm]
  rw [e]; exact h3.comp (h2.comp h1)

theorem rnAct_mp (a : B.Mat k ρ) (ha : a ∈ B.GV k ρ) :
    MeasurePreserving (rnAct (j := j) a) (U.muRC k j ρ) (U.muRC k j ρ) := by
  have h1 := mulLeft_mp (j := j) a (B2x5.normSq_det_GV ha)
  have h2 := h1.prod (MeasurePreserving.id (volume : Measure ((G.UT j → ℂ) × (Fin j → ℝ))))
  exact h2

theorem GV_inv_mem (y : B.Mat k ρ) (hy : y ∈ B.GV k ρ) : y⁻¹ ∈ B.GV k ρ :=
  (Formalism.FourierDecayAlt.P.unitary_group_closed k ρ).inv_mem y hy

theorem uw_inv_mulVec_eI {r : ℕ} (Z : Fin (2 * r + k + 1) → ℂ) (E : B.Mat k r) (hE : E ∈ UWset k r Z)
    (w : Fin (2 * r + k + 1) → ℂ) (a : Fin r) : (E⁻¹ *ᵥ w) (eI k r a) = w (eI k r a) := by
  have hu : IsUnit E.det := by
    have := B2x5.normSq_det_GV hE.1
    refine isUnit_iff_ne_zero.2 fun h0 => ?_
    rw [h0, Complex.normSq_zero] at this; exact zero_ne_one this
  rw [← herm_bvec_esI' (E⁻¹ *ᵥ w), ← herm_bvec_esI' w, ← TwoByOneBlock.herm_UH hE.1, (hE.2.1 a).2, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]

theorem ell_conj_UW {r : ℕ} (Z : Fin (2 * r + k + 1) → ℂ) (E : B.Mat k r) (hE : E ∈ UWset k r Z)
    (g : B.Mat k r) : ell k r Z (E⁻¹ * g * E) = ell k r Z g := by
  unfold ell
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs with h
  · rw [show (E⁻¹ * g * E) (eI k r a) (eI k r ⟨a.val + 1, h⟩) =
        ((E⁻¹ * g * E) *ᵥ bvec (eI k r ⟨a.val + 1, h⟩)) (eI k r a) from (mulVec_bvec_apply _ _ _).symm,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, (hE.2.1 _).1, uw_inv_mulVec_eI Z E hE, mulVec_bvec_apply]
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hE.2.2, uw_inv_mulVec_eI Z E hE]

theorem psi_conj_UW {r : ℕ} (Z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (E : B.Mat k r) (hE : E ∈ UWset k r Z)
    (g : B.Mat k r) : psi k r Z c (E⁻¹ * g * E) = psi k r Z c g := by
  unfold psi; rw [ell_conj_UW Z E hE]

theorem psi_rnAct (z0 : Fin (2 * ρ + k + 1) → ℂ) (c : ℂ) (y : B.Mat k ρ) (hy : y ∈ UWset k ρ z0)
    (x : U.RC k j ρ) :
    psi k (j + ρ) (liftVec k j ρ z0) c (U.Rn k j ρ (rnAct y⁻¹ x)) = psi k (j + ρ) (liftVec k j ρ z0) c (U.Rn k j ρ x) := by
  have hE : U.embG k j ρ y ∈ UWset k (j + ρ) (liftVec k j ρ z0) := by
    rw [← lev_eq_embG]; exact lev_UW j ρ z0 y hy
  rw [← embG_conj_Rn y hy.1 x, psi_conj_UW _ c _ hE]

end conj

end Formalism.FourierDecayAlt.P.PBM
