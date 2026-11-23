import Mathlib
import GroundTheory.AutomorphicForms.NormDetDiagUnitsPosRealToUnits
import GroundTheory.AutomorphicForms.ReductionSplitting
import GroundTheory.AutomorphicForms.ReductionMeasure
import GroundTheory.AutomorphicForms.ReductionLocalVolume

open NumberField IsDedekindDomain Topology Filter Set Matrix
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory.Global GroundTheory.Global.IdeleGroup
open MeasureTheory
open scoped Pointwise ENNReal

namespace GroundTheory.Automorphic

noncomputable section

namespace Reduction

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem exists_pos_bounds {X : Type*} [TopologicalSpace X] {C : Set X} (hC : IsCompact C)
    {f : X → ℝ} (hf : Continuous f) (hpos : ∀ x ∈ C, 0 < f x) :
    ∃ m M : ℝ, 0 < m ∧ m ≤ M ∧ ∀ x ∈ C, m ≤ f x ∧ f x ≤ M := by
  rcases C.eq_empty_or_nonempty with he | hne
  · exact ⟨1, 1, one_pos, le_rfl, fun x hx => by rw [he] at hx; exact hx.elim⟩
  obtain ⟨x₀, hx₀, hmin⟩ := hC.exists_isMinOn hne hf.continuousOn
  obtain ⟨x₁, hx₁, hmax⟩ := hC.exists_isMaxOn hne hf.continuousOn
  exact ⟨f x₀, f x₁, hpos x₀ hx₀, hmin hx₁, fun x hx => ⟨hmin hx, hmax hx⟩⟩

theorem det_mul_mul (b a k : AdelicGLn.AdelicGL K n) :
    (ideleModule K (AdelicGLn.det K n (b * a * k)) : ℝ) =
      (ideleModule K (AdelicGLn.det K n b) : ℝ) * (ideleModule K (AdelicGLn.det K n a) : ℝ) *
        (ideleModule K (AdelicGLn.det K n k) : ℝ) := by
  rw [map_mul, map_mul, map_mul, map_mul, Positive.val_mul, Positive.val_mul]

theorem ideleModule_det_diagUnits_posIdele (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) :
    (ideleModule K (AdelicGLn.det K n (diagUnits n fun i => posIdele (K := K) (r i) (hr i))) : ℝ) =
      (∏ i, r i) ^ Module.finrank ℚ K := by
  rw [det_diagUnits, map_prod, coe_finset_prod_pos]
  simp only [ideleModule_posIdele]
  rw [Finset.prod_pow]

theorem exists_norm_det_infAt_bounds {ω : Set (AdelicGLn.AdelicGL K n)} (hω : IsCompact ω)
    (t : ℝ) (w : InfinitePlace K) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ ∀ g ∈ siegelSet n ω t,
      1 ≤ (ideleModule K (AdelicGLn.det K n g) : ℝ) →
        (ideleModule K (AdelicGLn.det K n g) : ℝ) ≤ Real.exp 1 →
          c₁ ≤ ‖(infAt w g : Matrix (Fin n) (Fin n) w.Completion).det‖ ∧
            ‖(infAt w g : Matrix (Fin n) (Fin n) w.Completion).det‖ ≤ c₂ := by
  obtain ⟨B₁, B₂, hB₁, hB₁₂, hB⟩ := exists_pos_bounds hω (f := fun b => (ideleModule K (AdelicGLn.det K n b) : ℝ))
    (continuous_subtype_val.comp (continuous_ideleModule.comp (AdelicGLn.continuous_det K n)))
    (fun b _ => (ideleModule K (AdelicGLn.det K n b)).2)
  obtain ⟨m, M, hm, hmM', hmM⟩ := exists_pos_bounds hω
    (f := fun b => ‖(infAt w b : Matrix (Fin n) (Fin n) w.Completion).det‖)
    ((continuous_normDet w).comp (continuous_infAt w))
    (fun b _ => (normDet w (infAt w b)).2)
  set d := Module.finrank ℚ K
  have hd0 : 0 < d := Module.finrank_pos
  set X₁ : ℝ := min 1 B₂⁻¹
  set X₂ : ℝ := max 1 (Real.exp 1 / B₁)
  have hB₂ : 0 < B₂ := hB₁.trans_le hB₁₂
  have hX₁ : 0 < X₁ := lt_min one_pos (inv_pos.2 hB₂)
  refine ⟨m * X₁, M * X₂, mul_pos hm hX₁, ?_⟩
  rintro _ ⟨b, hbω, _, ⟨r, hr, -, rfl⟩, k, hk, rfl⟩ h1 h2
  have hdet := det_mul_mul b (diagUnits n fun i => posIdele (K := K) (r i) (hr i)) k
  rw [ideleModule_det_diagUnits_posIdele r hr, mem_normOneGL.1 (maxCompact_le_normOneGL hk),
    mul_one] at hdet
  set X : ℝ := ∏ i, r i with hX
  have hXpos : 0 < X := Finset.prod_pos fun i _ => hr i
  have hb := hB b hbω
  have hXd1 : X ^ d ≤ Real.exp 1 / B₁ := by
    rw [le_div_iff₀ hB₁]
    calc X ^ d * B₁ ≤ X ^ d * (ideleModule K (AdelicGLn.det K n b) : ℝ) :=
          mul_le_mul_of_nonneg_left hb.1 (pow_nonneg hXpos.le _)
      _ = _ := by rw [mul_comm, ← hdet]
      _ ≤ Real.exp 1 := h2
  have hXd2 : B₂⁻¹ ≤ X ^ d := by
    rw [inv_le_iff_one_le_mul₀' hB₂]
    calc (1 : ℝ) ≤ _ := h1
      _ = (ideleModule K (AdelicGLn.det K n b) : ℝ) * X ^ d := hdet
      _ ≤ B₂ * X ^ d := mul_le_mul_of_nonneg_right hb.2 (pow_nonneg hXpos.le _)
  have hXlow : X₁ ≤ X := by
    rcases le_or_gt 1 X with h | h
    · exact (min_le_left _ _).trans h
    · exact (min_le_right _ _).trans (hXd2.trans (pow_le_of_le_one hXpos.le h.le hd0.ne'))
  have hXup : X ≤ X₂ := by
    rcases le_or_gt X 1 with h | h
    · exact h.trans (le_max_left _ _)
    · exact (le_self_pow₀ h.le hd0.ne').trans (hXd1.trans (le_max_right _ _))
  have hloc : ‖(infAt w (b * diagUnits n (fun i => posIdele (K := K) (r i) (hr i)) * k) :
      Matrix (Fin n) (Fin n) w.Completion).det‖ =
      ‖(infAt w b : Matrix (Fin n) (Fin n) w.Completion).det‖ * X := by
    rw [infAt_mul, infAt_mul, Units.val_mul, Units.val_mul, det_mul, det_mul, norm_mul, norm_mul,
      infAt_diagUnits_posIdele w r hr, norm_det_diagUnits_posRealToUnits w r hr,
      norm_det_infAt_of_mem_maxCompact hk, mul_one]
  rw [hloc]
  have hbw := hmM b hbω
  exact ⟨mul_le_mul hbw.1 hXlow hX₁.le (hm.le.trans hbw.1),
    mul_le_mul hbw.2 hXup hXpos.le (hm.le.trans hmM')⟩

theorem posIdele_mul {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) :
    posIdele (K := K) r hr * posIdele ρ hρ = posIdele (r * ρ) (mul_pos hr hρ) := by
  have h := map_mul (posIdeleHom K) ⟨r, hr⟩ ⟨ρ, hρ⟩
  rw [posIdeleHom_apply, posIdeleHom_apply, posIdeleHom_apply] at h
  exact h.symm

theorem mul_centralSection_mem_siegelSet {ω : Set (AdelicGLn.AdelicGL K n)} {t : ℝ}
    {g : AdelicGLn.AdelicGL K n} (hg : g ∈ siegelSet n ω t) (s : {r : ℝ // 0 < r}) :
    g * centralSection K n s ∈ siegelSet n ω t := by
  obtain ⟨b, hb, _, ⟨r, hr, hratio, rfl⟩, k, hk, rfl⟩ := hg
  set ρ : {r : ℝ // 0 < r} := rpowHom ((n * Module.finrank ℚ K : ℝ))⁻¹ s with hρ
  have hz : centralSection K n s = diagUnits n fun _ => posIdele (K := K) ρ.1 ρ.2 := rfl
  refine ⟨b, hb, diagUnits n (fun i => posIdele (K := K) (r i * ρ.1) (mul_pos (hr i) ρ.2)),
    ⟨fun i => r i * ρ.1, fun i => mul_pos (hr i) ρ.2, fun i j hij => ?_, rfl⟩, k, hk, ?_⟩
  · rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hratio i j hij) ρ.2.le
  · rw [mul_assoc _ k, ← centralSection_mul_comm s k, ← mul_assoc, mul_assoc b, hz, ← map_mul]
    congr 3
    funext i
    rw [Pi.mul_apply]
    exact posIdele_mul (hr i) ρ.2

theorem isCompact_siegelSet_part {ω : Set (AdelicGLn.AdelicGL K n)} (hω : IsCompact ω) (t : ℝ)
    (N : ℕ) :
    IsCompact ((fun p : AdelicGLn.AdelicGL K n × (Fin n → {r : ℝ // 0 < r}) × AdelicGLn.AdelicGL K n =>
      p.1 * diagUnits n (fun i => posIdele (K := K) (p.2.1 i).1 (p.2.1 i).2) * p.2.2) ''
        (ω ×ˢ ({r | (∀ i j : Fin n, (j : ℕ) = i + 1 → t * (r j).1 ≤ (r i).1)} ∩
          Set.pi univ fun _ => {r : {r : ℝ // 0 < r} | r.1 ∈ Icc ((N : ℝ) + 1)⁻¹ ((N : ℝ) + 1)}) ×ˢ
            (maxCompact (K := K) (n := n) : Set (AdelicGLn.AdelicGL K n)))) := by
  refine IsCompact.image (hω.prod (IsCompact.prod ?_ isCompact_maxCompact)) ?_
  · refine IsCompact.inter_left (isCompact_univ_pi fun _ => ?_) ?_
    · rw [Subtype.isCompact_iff]
      have : Subtype.val '' {r : {r : ℝ // 0 < r} | r.1 ∈ Icc ((N : ℝ) + 1)⁻¹ ((N : ℝ) + 1)} =
          Icc ((N : ℝ) + 1)⁻¹ ((N : ℝ) + 1) := by
        ext x
        exact ⟨fun ⟨y, hy, hyx⟩ => hyx ▸ hy,
          fun hx => ⟨⟨x, lt_of_lt_of_le (by positivity) hx.1⟩, hx, rfl⟩⟩
      rw [this]
      exact isCompact_Icc
    · simp only [Set.ofPred_forall]
      exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
        isClosed_le (continuous_const.mul (continuous_subtype_val.comp (continuous_apply j)))
          (continuous_subtype_val.comp (continuous_apply i))
  · exact (continuous_fst.mul ((continuous_diagUnits n).comp (continuous_pi fun i =>
      continuous_posIdele_subtype.comp ((continuous_apply i).comp (continuous_fst.comp continuous_snd))))).mul
      (continuous_snd.comp continuous_snd)

theorem measurableSet_siegelSet {ω : Set (AdelicGLn.AdelicGL K n)} (hω : IsCompact ω) (t : ℝ) :
    MeasurableSet (siegelSet n ω t) := by
  have h : siegelSet n ω t = ⋃ N : ℕ,
      (fun p : AdelicGLn.AdelicGL K n × (Fin n → {r : ℝ // 0 < r}) × AdelicGLn.AdelicGL K n =>
        p.1 * diagUnits n (fun i => posIdele (K := K) (p.2.1 i).1 (p.2.1 i).2) * p.2.2) ''
        (ω ×ˢ ({r | (∀ i j : Fin n, (j : ℕ) = i + 1 → t * (r j).1 ≤ (r i).1)} ∩
          Set.pi univ fun _ => {r : {r : ℝ // 0 < r} | r.1 ∈ Icc ((N : ℝ) + 1)⁻¹ ((N : ℝ) + 1)}) ×ˢ
            (maxCompact (K := K) (n := n) : Set (AdelicGLn.AdelicGL K n))) := by
    ext g
    constructor
    · rintro ⟨b, hb, _, ⟨r, hr, hratio, rfl⟩, k, hk, rfl⟩

      obtain ⟨N, hN⟩ := exists_nat_ge (∑ i, (r i + (r i)⁻¹))
      refine mem_iUnion.2 ⟨N, (b, fun i => ⟨r i, hr i⟩, k), ⟨hb, ⟨hratio, fun i _ => ⟨?_, ?_⟩⟩, hk⟩, rfl⟩
      · have h1 : (r i)⁻¹ ≤ N := le_trans (le_add_of_nonneg_left (hr i).le)
          ((Finset.single_le_sum (f := fun i => r i + (r i)⁻¹)
            (fun j _ => add_nonneg (hr j).le (inv_pos.2 (hr j)).le) (Finset.mem_univ i)).trans hN)
        rw [inv_le_comm₀ (by positivity) (hr i)]
        linarith
      · have h1 : r i ≤ N := le_trans (le_add_of_nonneg_right (inv_pos.2 (hr i)).le)
          ((Finset.single_le_sum (f := fun i => r i + (r i)⁻¹)
            (fun j _ => add_nonneg (hr j).le (inv_pos.2 (hr j)).le) (Finset.mem_univ i)).trans hN)
        show r i ≤ (N : ℝ) + 1
        linarith
    · intro hg
      obtain ⟨N, p, ⟨hb, ⟨hratio, -⟩, hk⟩, rfl⟩ := mem_iUnion.1 hg
      exact ⟨p.1, hb, _, ⟨fun i => (p.2.1 i).1, fun i => (p.2.1 i).2, hratio, rfl⟩, p.2.2, hk, rfl⟩
  rw [h]
  exact MeasurableSet.iUnion fun N => (isCompact_siegelSet_part hω t N).isClosed.measurableSet

instance secondCountableTopology_normOneGL : SecondCountableTopology (normOneGL K n) :=
  TopologicalSpace.Subtype.secondCountableTopology _

theorem infAt_isUpperTriangular {w : InfinitePlace K} {b : AdelicGLn.AdelicGL K n}
    (hb : b ∈ adelicBorel) : (infAt w b : Matrix (Fin n) (Fin n) w.Completion).IsUpperTriangular :=
  fun i j hij => by
    rw [infAt_apply, show (b : Matrix (Fin n) (Fin n) 𝔸[K]) i j = 0 from hb hij]
    rfl

theorem isFiniteMeasure_quotientMeasure (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] :
    IsFiniteMeasure (RightCosetSpace.quotientMeasure (rationalGLOne K n) μ) := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : Subsingleton (normOneGL K 0) :=
      ⟨fun x y => Subtype.ext (Units.ext (Subsingleton.elim _ _))⟩
    have : Subsingleton (RightCosetSpace (rationalGLOne K 0)) :=
      ⟨fun p q => by
        obtain ⟨x, rfl⟩ := RightCosetSpace.mk_surjective _ p
        obtain ⟨y, rfl⟩ := RightCosetSpace.mk_surjective _ q
        rw [Subsingleton.elim x y]⟩
    have : CompactSpace (RightCosetSpace (rationalGLOne K 0)) := Finite.compactSpace
    infer_instance
  obtain ⟨ω, hω, hωB, t, ht, hsieg⟩ := exists_siegelSet (K := K) n
  set D : Set (normOneGL K n) := Subtype.val ⁻¹' siegelSet n ω t with hDdef
  have hDm : MeasurableSet D := measurable_subtype_coe (measurableSet_siegelSet hω t)
  have hcover : RightCosetSpace.mk (rationalGLOne K n) '' D = univ := by
    refine eq_univ_of_forall fun q => ?_
    obtain ⟨x, rfl⟩ := RightCosetSpace.mk_surjective _ q
    obtain ⟨γ, hγ⟩ := hsieg x
    have hγ1 : AdelicGLn.diagonal K n γ ∈ normOneGL K n := rationalGL_le_normOneGL ⟨γ, rfl⟩
    exact ⟨⟨_, mul_mem hγ1 x.2⟩, hγ,
      (RightCosetSpace.mk_eq_mk_iff).2 ⟨⟨⟨_, hγ1⟩, ⟨γ, rfl⟩⟩, rfl⟩⟩
  obtain ⟨c, hc, hμ⟩ := exists_measure_eq_mul_measure_image hn μ
    (Measure.haar : Measure (AdelicGLn.AdelicGL K n))
  choose c₁ c₂ hc₁ hbd using fun w => exists_norm_det_infAt_bounds (K := K) hω t w
  set S : ∀ w : InfinitePlace K, Set (GL (Fin n) w.Completion) :=
    fun w => localSiegel w (infAt w '' ω) t (c₁ w) (c₂ w) with hSdef
  have hS : ∀ w, (Measure.haar : Measure (GL (Fin n) w.Completion)) (S w) < ⊤ := fun w =>
    measure_localSiegel_lt_top w _ (hω.image (continuous_infAt w))
      (by rintro _ ⟨b, hb, rfl⟩; exact infAt_isUpperTriangular (hωB hb)) ht (hc₁ w)
  set p2 : AdelicGLn.AdelicGL K n → AdelicGLn.FiniteAdelicGL K n :=
    fun g => (AdelicGLn.prodEquiv K n g).2 with hp2
  have hp2c : Continuous p2 := continuous_snd.comp (AdelicGLn.prodEquiv K n).continuous
  set F : Set (AdelicGLn.FiniteAdelicGL K n) :=
    (p2 '' ω) * (p2 '' (maxCompact (K := K) (n := n) : Set (AdelicGLn.AdelicGL K n))) with hFdef
  have hF : IsCompact F := (hω.image hp2c).mul (isCompact_maxCompact.image hp2c)
  set E : Set (AdelicGLn.AdelicGL K n) := {g | g ∈ siegelSet n ω t ∧
    1 ≤ (ideleModule K (AdelicGLn.det K n g) : ℝ) ∧
      (ideleModule K (AdelicGLn.det K n g) : ℝ) ≤ Real.exp 1} with hEdef
  have hE : (Measure.haar : Measure (AdelicGLn.AdelicGL K n)) E < ⊤ := by
    refine measure_lt_top_of_forall_mem _ S hS hF fun g hg => ⟨fun w => ?_, ?_⟩
    · obtain ⟨hgs, h1, h2⟩ := hg
      have hb := hbd w g hgs h1 h2
      obtain ⟨b, hbω, _, ⟨r, hr, hratio, rfl⟩, k, hk, rfl⟩ := hgs
      refine ⟨hb.1, hb.2, infAt w b, ⟨b, hbω, rfl⟩, r, hr, hratio, infAt w k, hk.1 w, ?_⟩
      rw [infAt_mul, infAt_mul, infAt_diagUnits_posIdele w r hr]
    · obtain ⟨⟨b, hbω, _, ⟨r, hr, -, rfl⟩, k, hk, rfl⟩, -, -⟩ := hg
      refine ⟨p2 b, ⟨b, hbω, rfl⟩, p2 k, ⟨k, hk, rfl⟩, ?_⟩
      simp only [hp2, map_mul, Prod.snd_mul, prodEquiv_diagUnits_posIdele_snd r hr, mul_one]
  have himage : (fun p : normOneGL K n × {r : ℝ // 0 < r} =>
      (p.1 : AdelicGLn.AdelicGL K n) * centralSection K n p.2) '' (D ×ˢ posRealUnitInterval) ⊆ E := by
    rintro _ ⟨⟨x, s⟩, ⟨hx, hs⟩, rfl⟩
    refine ⟨mul_centralSection_mem_siegelSet hx s, ?_⟩
    have hdet : (ideleModule K (AdelicGLn.det K n ((x : AdelicGLn.AdelicGL K n) *
        centralSection K n s)) : ℝ) = s := by
      have h1 := detModule_centralSection (K := K) hn s
      have h2 := (mem_normOneGL_iff_detModule (K := K) (n := n)).1 x.2
      change (detModule K n ((x : AdelicGLn.AdelicGL K n) * centralSection K n s) : ℝ) = s
      rw [map_mul, h1, h2, one_mul]
    rw [hdet]
    exact hs
  refine ⟨?_⟩
  rw [← hcover]
  calc RightCosetSpace.quotientMeasure (rationalGLOne K n) μ
        (RightCosetSpace.mk (rationalGLOne K n) '' D)
      ≤ μ D := RightCosetSpace.quotientMeasure_mk_image_le μ (by rw [hcover]; exact MeasurableSet.univ)
    _ = c * (Measure.haar : Measure (AdelicGLn.AdelicGL K n)) _ := hμ D hDm
    _ ≤ c * (Measure.haar : Measure (AdelicGLn.AdelicGL K n)) E := by
        gcongr
    _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hc) hE

end Reduction

end

end GroundTheory.Automorphic
