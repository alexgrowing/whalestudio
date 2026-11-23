import Formalism.HermitianCurvature.HermitianCurvatureProofs.RightStabilizerMem
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MeasMOfCont
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormRankZeroApply

namespace Formalism.FourierDecayAlt.P.StabilizerDisintegration.OF

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.StabilizerDisintegration.OD Formalism.FourierDecayAlt.P.StabilizerDisintegration.MM
open scoped ComplexConjugate

noncomputable section

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem measM_lowP {X : Type*} [MeasurableSpace X] {m : ℕ} (w : Equiv.Perm (Fin m)) {y : X → C2.LPidx w → ℂ}
    (hy : Measurable y) : MeasM (fun x => lowP w (y x)) := by
  rw [measM_iff]
  intro i j
  simp only [lowP, C2.lowOf, Matrix.add_apply, Matrix.of_apply]
  refine measurable_const.add (Finset.measurable_sum _ fun q _ => ?_)
  split_ifs
  · exact (measurable_pi_apply q).comp hy
  · exact measurable_const

theorem measM_upper {X : Type*} [MeasurableSpace X] {m : ℕ} {u : X → G.UT m → ℂ} (hu : Measurable u) :
    MeasM (fun x => G.upper (u x)) := by
  rw [measM_iff]
  intro i j
  simp only [G.upper, G.strictUpper, Matrix.add_apply, Matrix.of_apply]
  refine measurable_const.add ?_
  split_ifs with h
  · exact (measurable_pi_apply _).comp hu
  · exact measurable_const

theorem measM_uMap {X : Type*} [MeasurableSpace X] (z : Fin (2 * r + k + 1) → ℂ) {A : X → B.Mat k r}
    (hA : MeasM A) : MeasM (fun x => C2.uMap k r z (A x)) := by
  have h := measM_of_cont
    (f := fun y : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ => C2.uMap k r z (Matrix.of y)) ?_ hA
  · simpa using h
  · refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [C2.uMap, herm, Matrix.of_symm_apply]
    split_ifs
    · simp only [dotProduct, Matrix.mulVec, Matrix.of_apply]
      fun_prop
    · simp only [dotProduct, Matrix.mulVec, Matrix.of_apply]
      fun_prop

theorem meas_utc {X : Type*} [MeasurableSpace X] {m : ℕ} {A : X → Matrix (Fin m) (Fin m) ℂ} (hA : MeasM A) :
    Measurable fun x => utc (A x) := by
  rw [measM_iff] at hA
  exact measurable_pi_lambda _ fun q => hA q.1.1 q.1.2

section main

variable (S : B.RealPlaceData k r Wp Wq) {γ : B.Mat k r} (hγ : γ ∈ B.GV k r) {w : Equiv.Perm (Fin (r + 1))}
  {d : Fin (r + 1) → ℂ} (hd : ∀ a, d a ≠ 0) (hZw : Zhat k r S.z S.z' γ = C2.monoP w d)
  (hpos : 0 < Gf k r S.z S.z' γ)
  (e : ((C2.Lstidx w → ℂ) × (C2.LPidx w → ℂ)) ≃ᵐ (G.UT (r + 1) → ℂ))
  (he : ∀ p, G.upper (e p) = (lowS w p.1)ᴴ * (lowP w p.2)ᴴ)

include hγ hd hZw hpos in
theorem measM_rhoX {X : Type*} [MeasurableSpace X] {x : X → C2.Lstidx w → ℂ} (hx : Measurable x) :
    MeasM (fun t => rhoX S γ w (x t)) := by
  have hg : Dx2.Rad.Good S γ w d := by
    first
    | exact good S hγ hd hZw hpos
    | exact good S hγ hd hZw
    | exact good S hγ hZw hd
  obtain ⟨-, hinj, -⟩ := hg
  have hs : ∀ x, rhoX S γ w x ∈ C6.Rset γ ∧ C2.uMap k r S.z (rhoX S γ w x) = (lowS w x)ᴴ := fun x => by
    first
    | exact rhoX_spec S hγ hd hZw hpos x
    | exact rhoX_spec S hγ hd hZw x

  have hR : IsClosed (C6.Rset γ) := by
    have hN : IsClosed (Nset k r) := (Formalism.FourierDecayAlt.P.B2x2.closedN k r).closed
    have hc : Continuous fun ρ : B.Mat k r => γ⁻¹ * ρ * γ :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    have h2 : IsClosed ((fun ρ : B.Mat k r => γ⁻¹ * ρ * γ) ⁻¹' Nset k r) := hN.preimage hc
    have h3 : C6.Rset γ = Nset k r ∩ ((fun ρ : B.Mat k r => γ⁻¹ * ρ * γ) ⁻¹' Nset k r) := by
      ext ρ
      simp only [C6.Rset, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage]
    rw [h3]
    exact hN.inter h2
  set R' : Set (Mt k r) := {y | Matrix.of y ∈ C6.Rset γ} with hR'def
  have hR' : IsClosed R' := hR.preimage continuous_id
  set F : Mt k r → Fin (r + 1) → Fin (r + 1) → ℂ := fun y => Matrix.of.symm (C2.uMap k r S.z (Matrix.of y))
    with hFdef
  have hF : Continuous F := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [hFdef, C2.uMap, herm, Matrix.of_symm_apply]
    split_ifs
    · simp only [dotProduct, Matrix.mulVec, Matrix.of_apply]
      fun_prop
    · simp only [dotProduct, Matrix.mulVec, Matrix.of_apply]
      fun_prop
  set H : (C2.Lstidx w → ℂ) → Fin (r + 1) → Fin (r + 1) → ℂ := fun x => Matrix.of.symm ((lowS w x)ᴴ) with hHdef
  have hlow : MeasM (fun x : C2.Lstidx w → ℂ => lowS w x) := by
    rw [measM_iff]
    intro i j
    simp only [lowS, C2.lowOf, Matrix.add_apply, Matrix.of_apply]
    refine measurable_const.add (Finset.measurable_sum _ fun q _ => ?_)
    split_ifs
    · exact measurable_pi_apply q
    · exact measurable_const
  have hH : Measurable H := measM_star hlow
  have hΦ : Measurable fun x : C2.Lstidx w → ℂ => (Matrix.of.symm (rhoX S γ w x) : Mt k r) := by
    intro B hB
    have hset : (fun x : C2.Lstidx w → ℂ => (Matrix.of.symm (rhoX S γ w x) : Mt k r)) ⁻¹' B =
        H ⁻¹' (F '' (B ∩ R')) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_image, Set.mem_inter_iff]
      constructor
      · intro hx
        refine ⟨Matrix.of.symm (rhoX S γ w x), ⟨hx, ?_⟩, ?_⟩
        · simpa [hR'def] using (hs x).1
        · simp only [hFdef, hHdef, Equiv.apply_symm_apply, (hs x).2]
      · rintro ⟨y, ⟨hyB, hyR⟩, hFy⟩
        have hyR2 : Matrix.of y ∈ C6.Rset γ := hyR
        have hu : C2.uMap k r S.z (Matrix.of y) = C2.uMap k r S.z (rhoX S γ w x) := by
          rw [(hs x).2]
          exact Matrix.of.symm.injective hFy
        have := hinj hyR2 (hs x).1 hu
        rw [← this]
        simpa using hyB
    rw [hset]
    exact hH (MeasurableSet.image_of_continuousOn_injOn (hB.inter hR'.measurableSet) hF.continuousOn
      (fun a ha b hb hab => by
        have h1 : Matrix.of a ∈ C6.Rset γ := ha.2
        have h2 : Matrix.of b ∈ C6.Rset γ := hb.2
        have := hinj h1 h2 (Matrix.of.symm.injective hab)
        simpa using this))
  exact hΦ.comp hx

include hγ hd hZw hpos in
theorem measM_rhoP {X : Type*} [MeasurableSpace X] {x : X → C2.Lstidx w → ℂ} (hx : Measurable x) :
    MeasM (fun t => rhoP S γ w (x t)) := by
  simp only [rhoP]
  exact measM_mul (measM_mul (measM_const _) (measM_inv (measM_rhoX S hγ hd hZw hpos hx))) (measM_const _)

include hγ hd hZw hpos in
theorem measM_m0L {X : Type*} [MeasurableSpace X] {x : X → C2.Lstidx w → ℂ} (hx : Measurable x)
    {y : X → C2.LPidx w → ℂ} (hy : Measurable y) : MeasM (fun t => m0L S γ w e (x t) (y t)) := by
  simp only [m0L]
  have hxy : Measurable fun t => (x t, y t) := hx.prodMk hy
  exact measM_mul (measM_mul (measM_inv (measM_tau _ (measM_star (measM_lowP w hy))))
    (measM_inv (measM_rhoX S hγ hd hZw hpos hx))) (measM_tau _ (measM_upper (e.measurable.comp hxy)))

include hγ hd hZw hpos in
theorem measM_m0R {X : Type*} [MeasurableSpace X] {x : X → C2.Lstidx w → ℂ} (hx : Measurable x)
    {u : X → G.UT (r + 1) → ℂ} (hu : Measurable u) : MeasM (fun t => m0R S γ w (x t) (u t)) := by
  simp only [m0R]
  have hP := measM_rhoP S hγ hd hZw hpos hx
  exact measM_mul (measM_mul (measM_inv (measM_tau _ (measM_mul (measM_uMap _ hP) (measM_upper hu)))) hP)
    (measM_tau _ (measM_upper hu))

include hγ hd hZw hpos in
theorem meas_Tx : Measurable fun p : (C2.Lstidx w → ℂ) × RR k r w => Tx S γ w e p.1 p.2 := by
  have h1 : Measurable fun p : (C2.Lstidx w → ℂ) × RR k r w => p.1 := measurable_fst
  have hy : Measurable fun p : (C2.Lstidx w → ℂ) × RR k r w => p.2.1.2.1 := by fun_prop
  have hu : Measurable fun p : (C2.Lstidx w → ℂ) × RR k r w => p.2.2.2.1 := by fun_prop
  have hM : MeasM fun p : (C2.Lstidx w → ℂ) × RR k r w => Matrix.of p.2.1.2.2 := by
    unfold MeasM
    simp only [Equiv.symm_apply_apply]
    fun_prop
  have hM' : MeasM fun p : (C2.Lstidx w → ℂ) × RR k r w => Matrix.of p.2.2.2.2 := by
    unfold MeasM
    simp only [Equiv.symm_apply_apply]
    fun_prop
  have hA : Measurable fun p : (C2.Lstidx w → ℂ) × RR k r w =>
      Matrix.of.symm (m0L S γ w e p.1 p.2.1.2.1 * Matrix.of p.2.1.2.2) :=
    measM_mul (measM_m0L S hγ hd hZw hpos e h1 hy) hM
  have hB : Measurable fun p : (C2.Lstidx w → ℂ) × RR k r w =>
      utc (C2.uMap k r S.z' (rhoP S γ w p.1) * G.upper p.2.2.2.1) :=
    meas_utc (measM_mul (measM_uMap _ (measM_rhoP S hγ hd hZw hpos h1)) (measM_upper hu))
  have hC : Measurable fun p : (C2.Lstidx w → ℂ) × RR k r w =>
      Matrix.of.symm (m0R S γ w p.1 p.2.2.2.1 * Matrix.of p.2.2.2.2) :=
    measM_mul (measM_m0R S hγ hd hZw hpos h1 hu) hM'
  have ha : Measurable fun p : (C2.Lstidx w → ℂ) × RR k r w => p.2.1.1 := by fun_prop
  have hb : Measurable fun p : (C2.Lstidx w → ℂ) × RR k r w => p.2.2.1 := by fun_prop
  exact (ha.prodMk (hy.prodMk hA)).prodMk (hb.prodMk ((hB.prodMk hC)))

include hγ hd hZw hpos in
theorem upperUnipotent_mem_upperTriangular (x : C2.Lstidx w → ℂ) : C2.uMap k r S.z' (rhoP S γ w x) ∈ C2.UTset (r + 1) := by
  have h := (by apply uP_UT <;> assumption :
    C2.uMap k r S.z' (rhoP S γ w x) * G.upper (0 : G.UT (r + 1) → ℂ) ∈ C2.UTset (r + 1))
  have h0 : G.upper (0 : G.UT (r + 1) → ℂ) = 1 := by
    ext i j
    simp [G.upper, G.strictUpper]
  rwa [h0, mul_one] at h

variable {μ0 μ0' : Measure (Mt k r)} (hμ0 : B.IsHaarOn (C2.N0set k r S.z) μ0)
  (hμ0' : B.IsHaarOn (C2.N0set k r S.z') μ0')

include hγ hd hZw hpos he hμ0 hμ0' in
theorem mp_Tx (x : C2.Lstidx w → ℂ) : MeasurePreserving (Tx S γ w e x) (nuR S w μ0 μ0') (nuR S w μ0 μ0') := by
  have sf : ∀ {U : Set (B.Mat k r)} {μ : Measure (Mt k r)}, B.IsHaarOn U μ → SigmaFinite μ := by
    intro U μ h
    haveI : IsFiniteMeasureOnCompacts μ := ⟨h.finite_compact⟩
    infer_instance
  haveI := sf hμ0
  haveI := sf hμ0'
  haveI := sf S.haarW
  haveI := sf S.haarW'
  have hL : MeasurePreserving
      (fun p : (C2.LPidx w → ℂ) × Mt k r => (id p.1, lmulM (m0L S γ w e x p.1) p.2))
      ((volume : Measure (C2.LPidx w → ℂ)).prod μ0) ((volume : Measure (C2.LPidx w → ℂ)).prod μ0) := by
    refine MeasurePreserving.skew_product (μc := μ0) (μd := μ0)
      (g := fun y M => lmulM (m0L S γ w e x y) M) (MeasurePreserving.id (volume : Measure (C2.LPidx w → ℂ))) ?_
      (Filter.Eventually.of_forall fun y => ?_)
    · have h := measM_mul (measM_m0L S hγ hd hZw hpos e (measurable_const (a := x)) measurable_fst)
        (show MeasM fun p : (C2.LPidx w → ℂ) × Mt k r => Matrix.of p.2 by
          unfold MeasM
          simp only [Equiv.symm_apply_apply]
          fun_prop)
      exact h
    · exact hμ0.left _ (by apply left_stabilizer_mem <;> assumption)
  have hR : MeasurePreserving
      (fun p : (G.UT (r + 1) → ℂ) × Mt k r =>
        (utc (C2.uMap k r S.z' (rhoP S γ w x) * G.upper p.1), lmulM (m0R S γ w x p.1) p.2))
      ((volume : Measure (G.UT (r + 1) → ℂ)).prod μ0') ((volume : Measure (G.UT (r + 1) → ℂ)).prod μ0') := by
    refine MeasurePreserving.skew_product (μc := μ0') (μd := μ0')
      (g := fun u M => lmulM (m0R S γ w x u) M) (Formalism.FourierDecayAlt.P.StabilizerDisintegration.HC.mp_UTleft (upperUnipotent_mem_upperTriangular S hγ hd hZw hpos x)) ?_

      (Filter.Eventually.of_forall fun u => ?_)
    · have h := measM_mul (measM_m0R S hγ hd hZw hpos (measurable_const (a := x)) measurable_fst)
        (show MeasM fun p : (G.UT (r + 1) → ℂ) × Mt k r => Matrix.of p.2 by
          unfold MeasM
          simp only [Equiv.symm_apply_apply]
          fun_prop)
      exact h
    · exact hμ0'.left _ (by apply right_stabilizer_mem <;> assumption)
  have hall := ((MeasurePreserving.id S.μW).prod hL).prod ((MeasurePreserving.id S.μW').prod hR)
  exact hall

include hγ hd hZw hpos he hμ0 hμ0' in
theorem mp_Tt : MeasurePreserving (Tt S γ w e) ((volume : Measure (C2.Lstidx w → ℂ)).prod (nuR S w μ0 μ0'))
    ((volume : Measure (C2.Lstidx w → ℂ)).prod (nuR S w μ0 μ0')) := by
  have sf : ∀ {U : Set (B.Mat k r)} {μ : Measure (Mt k r)}, B.IsHaarOn U μ → SigmaFinite μ := by
    intro U μ h
    haveI : IsFiniteMeasureOnCompacts μ := ⟨h.finite_compact⟩
    infer_instance
  haveI := sf hμ0
  haveI := sf hμ0'
  haveI := sf S.haarW
  haveI := sf S.haarW'
  haveI : SFinite (nuR S w μ0 μ0') := by
    unfold nuR
    infer_instance
  have h := MeasurePreserving.skew_product (μc := nuR S w μ0 μ0') (μd := nuR S w μ0 μ0')
    (g := fun x q => Tx S γ w e x q) (MeasurePreserving.id (volume : Measure (C2.Lstidx w → ℂ)))
    (meas_Tx S hγ hd hZw hpos e)
    (Filter.Eventually.of_forall fun x => (mp_Tx S hγ hd hZw hpos e he hμ0 hμ0' x).map_eq)
  exact h

include hγ hd hZw hpos he in
theorem inj_Tt : Function.Injective (Tt S γ w e) := by
  rintro ⟨x, ⟨a, y, M⟩, ⟨b, u, M'⟩⟩ ⟨x', ⟨a', y', N⟩, ⟨b', u', N'⟩⟩ h
  simp only [Tt, Tx, Prod.mk.injEq] at h
  obtain ⟨rfl, ⟨rfl, rfl, hM⟩, rfl, hu, hM'⟩ := h
  have hc : C2.uMap k r S.z' (rhoP S γ w x) ∈ C2.UTset (r + 1) := upperUnipotent_mem_upperTriangular S hγ hd hZw hpos x
  have hcu : IsUnit (C2.uMap k r S.z' (rhoP S γ w x)) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    have hdet : (C2.uMap k r S.z' (rhoP S γ w x)).det = 1 := by
      rw [Matrix.det_of_upperTriangular (fun i j hij => hc.1 i j hij)]
      simp [hc.2]
    rw [hdet]
    exact isUnit_one
  have hU : ∀ v : G.UT (r + 1) → ℂ, C2.uMap k r S.z' (rhoP S γ w x) * G.upper v ∈ C2.UTset (r + 1) :=
    fun v => by apply uP_UT <;> assumption
  have huu : u = u' := by
    have hmat : C2.uMap k r S.z' (rhoP S γ w x) * G.upper u = C2.uMap k r S.z' (rhoP S γ w x) * G.upper u' := by
      ext i j
      rcases lt_trichotomy i j with hij | rfl | hij
      · simpa [utc] using congrFun hu ⟨(i, j), hij⟩
      · rw [(hU u).2 i, (hU u').2 i]
      · rw [(hU u).1 i j hij, (hU u').1 i j hij]
    have hup := hcu.mul_left_cancel hmat
    rw [← Formalism.FourierDecayAlt.P.StabilizerDisintegration.HC.utc_upper u, ← Formalism.FourierDecayAlt.P.StabilizerDisintegration.HC.utc_upper u', hup]
  subst huu
  have hL : IsUnit (m0L S γ w e x y) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact (Formalism.FourierDecayAlt.P.B2x2.closedN k r).unit _ (by apply left_stabilizer_mem <;> assumption : m0L S γ w e x y ∈ C2.N0set k r S.z).1
  have hR : IsUnit (m0R S γ w x u) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact (Formalism.FourierDecayAlt.P.B2x2.closedN k r).unit _ (by apply right_stabilizer_mem <;> assumption : m0R S γ w x u ∈ C2.N0set k r S.z').1
  have e1 : Matrix.of M = Matrix.of N := hL.mul_left_cancel (Matrix.of.symm.injective hM)
  have e2 : Matrix.of M' = Matrix.of N' := hR.mul_left_cancel (Matrix.of.symm.injective hM')
  simp only [EmbeddingLike.apply_eq_iff_eq] at e1 e2
  subst e1
  subst e2
  rfl

set_option synthInstance.maxHeartbeats 400000 in
include hγ hd hZw hpos he in
theorem emb_Tt : MeasurableEmbedding (Tt S γ w e) := set_option maxHeartbeats 800000 in by
  have hm : Measurable (Tt S γ w e) := by
    unfold Tt
    exact measurable_fst.prodMk (meas_Tx S hγ hd hZw hpos e)
  have hi : Function.Injective (Tt S γ w e) := inj_Tt S hγ hd hZw hpos e he
  haveI i1 : StandardBorelSpace (C2.Lstidx w → ℂ) := inferInstance
  haveI i2 : StandardBorelSpace (Mt k r) := inferInstance
  haveI i3 : StandardBorelSpace (G.UT (r + 1) → ℂ) := inferInstance
  haveI i4 : StandardBorelSpace (C2.LPidx w → ℂ) := inferInstance
  haveI i5 : StandardBorelSpace (RR k r w) := inferInstance
  haveI i6 : StandardBorelSpace ((C2.Lstidx w → ℂ) × RR k r w) := inferInstance
  exact hm.measurableEmbedding hi

end main

end

end Formalism.FourierDecayAlt.P.StabilizerDisintegration.OF
