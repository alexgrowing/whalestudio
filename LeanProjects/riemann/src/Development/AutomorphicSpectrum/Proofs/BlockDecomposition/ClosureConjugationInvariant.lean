import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion

noncomputable section

namespace GlobalTheory.CompanionTheory.PlaneSA.MemConj

variable {F : Type} [Field F] [NumberField F] {d β : F}

theorem denseRange_algebraMap_Kp (u : Pl F) : DenseRange (algebraMap F (Kp u)) := by
  cases u with
  | inl w =>
    exact (Function.surjective_eval w).denseRange.comp (InfiniteAdeleRing.denseRange_algebraMap F)
      (continuous_apply w)
  | inr v => exact HeightOneSpectrum.denseRange_algebraMap (K := F) v

def qinv {K : Type} [Field K] [Algebra F K] (e : Q d β K) : Q d β K :=
  algebraMap K (Q d β K) (qn e)⁻¹ * star e

theorem mul_qinv {K : Type} [Field K] [Algebra F K] {e : Q d β K} (h : qn e ≠ 0) :
    e * qinv e = 1 := by
  have h1 : e * algebraMap K (Q d β K) (qn e)⁻¹ = algebraMap K (Q d β K) (qn e)⁻¹ * e :=
    (Algebra.commutes _ _).symm
  rw [qinv, ← mul_assoc, h1, mul_assoc, mul_star_eq, ← map_mul, inv_mul_cancel₀ h, map_one]

theorem qinv_mul {K : Type} [Field K] [Algebra F K] {e : Q d β K} (h : qn e ≠ 0) :
    qinv e * e = 1 := by
  rw [qinv, mul_assoc, star_mul_eq, ← map_mul, inv_mul_cancel₀ h, map_one]

theorem qinv_unique {K : Type} [Field K] [Algebra F K] {e e' : Q d β K} (h : qn e ≠ 0)
    (h' : e' * e = 1) : qinv e = e' := by
  calc qinv e = (e' * e) * qinv e := by rw [h', one_mul]
    _ = e' := by rw [mul_assoc, mul_qinv h, mul_one]

theorem conj_mem_SuppAt {T : Set (Pl F)} {p q h : Q d β (AF F)} (hpq : p * q = 1)
    (hh : h ∈ SuppAt d β T) : p * h * q ∈ SuppAt d β T := by
  refine ⟨?_, fun u hu => ?_⟩
  · rw [qn_mul, qn_mul, hh.1, mul_one, ← qn_mul, hpq, qn_one]
  · rw [map_mul, map_mul, hh.2 u hu, mul_one, ← map_mul, hpq, map_one]

theorem conj_mem_SAQ (s : Pl F) {δ δ' : Q d β F} (h1 : δ * δ' = 1) (h2 : δ' * δ = 1)
    {x : Q d β (AF F)} (hx : x ∈ SAQ d β s) :
    (rat δ : Q d β (AF F)) * x * rat δ' ∈ SAQ d β s := by
  obtain ⟨γ, hγ, h, hh, rfl⟩ := hx
  have r1 : (rat δ : Q d β (AF F)) * rat δ' = 1 := by rw [← map_mul, h1, map_one]
  have r2 : (rat δ' : Q d β (AF F)) * rat δ = 1 := by rw [← map_mul, h2, map_one]
  refine ⟨δ * γ * δ', ?_, rat δ * h * rat δ', conj_mem_SuppAt r1 hh, ?_⟩
  · rw [qn_mul, qn_mul, hγ, mul_one, ← qn_mul, h1, qn_one]
  · rw [map_mul, map_mul]
    calc (rat δ : Q d β (AF F)) * (rat γ * h) * rat δ'
        = rat δ * rat γ * (rat δ' * rat δ) * h * rat δ' := by
          rw [r2, mul_one]; simp only [mul_assoc]
      _ = rat δ * rat γ * rat δ' * (rat δ * h * rat δ') := by simp only [mul_assoc]

theorem conj_mem_closure (s : Pl F) {δ δ' : Q d β F} (h1 : δ * δ' = 1) (h2 : δ' * δ = 1)
    {x : Q d β (AF F)} (hx : x ∈ closure (SAQ d β s)) :
    (rat δ : Q d β (AF F)) * x * rat δ' ∈ closure (SAQ d β s) := by
  have hc : Continuous fun y : Q d β (AF F) => (rat δ : Q d β (AF F)) * y * rat δ' :=
    (continuous_const.mul continuous_id).mul continuous_const
  have hsub : closure (SAQ d β s) ⊆
      (fun y : Q d β (AF F) => (rat δ : Q d β (AF F)) * y * rat δ') ⁻¹' closure (SAQ d β s) := by
    refine closure_minimal (fun y hy => subset_closure ?_) (isClosed_closure.preimage hc)
    exact conj_mem_SAQ s h1 h2 hy
  exact hsub hx

def psi (w : Pl F) (y : Q d β (Kp w)) : Q d β (AF F) :=
  ⟨1 + inc w (y.re - 1), inc w y.imI, inc w y.imJ, inc w y.imK⟩

theorem continuous_psi (w : Pl F) : Continuous (psi (d := d) (β := β) w) := by
  rw [continuous_q_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact continuous_const.add ((continuous_inc w).comp (continuous_re.sub continuous_const))
  · exact (continuous_inc w).comp continuous_imI
  · exact (continuous_inc w).comp continuous_imJ
  · exact (continuous_inc w).comp continuous_imK

theorem psi_proj {w : Pl F} {x : Q d β (AF F)} (hx : x ∈ SuppAt d β {w}) :
    psi w (qmap (proj w) x) = x := by
  have key : ∀ u, u ≠ w → qmap (proj u) x = 1 := fun u hu => hx.2 u (by simpa using hu)
  ext
  · refine adele_ext fun u => ?_
    by_cases h : u = w
    · subst h; simp [psi, qmap, proj_inc_same]
    · have := congrArg (fun z => z.re) (key u h)
      simp only [qmap] at this
      simpa [psi, qmap, proj_inc_ne h] using this.symm
  · refine adele_ext fun u => ?_
    by_cases h : u = w
    · subst h; simp [psi, qmap, proj_inc_same]
    · have := congrArg (fun z => z.imI) (key u h)
      simp only [qmap] at this
      simpa [psi, qmap, proj_inc_ne h] using this.symm
  · refine adele_ext fun u => ?_
    by_cases h : u = w
    · subst h; simp [psi, qmap, proj_inc_same]
    · have := congrArg (fun z => z.imJ) (key u h)
      simp only [qmap] at this
      simpa [psi, qmap, proj_inc_ne h] using this.symm
  · refine adele_ext fun u => ?_
    by_cases h : u = w
    · subst h; simp [psi, qmap, proj_inc_same]
    · have := congrArg (fun z => z.imK) (key u h)
      simp only [qmap] at this
      simpa [psi, qmap, proj_inc_ne h] using this.symm

theorem qmap_proj_rat (w : Pl F) (δ : Q d β F) :
    qmap (proj w) (rat δ : Q d β (AF F)) = rat δ := by
  ext <;> simp [rat, qmap]

theorem continuous_qn {K : Type} [CommRing K] [Algebra F K] [TopologicalSpace K]
    [IsTopologicalRing K] : Continuous (qn : Q d β K → K) := by
  have h1 := continuous_re (d := d) (β := β) (R := K)
  have h2 := continuous_imI (d := d) (β := β) (R := K)
  have h3 := continuous_imJ (d := d) (β := β) (R := K)
  have h4 := continuous_imK (d := d) (β := β) (R := K)
  unfold qn
  fun_prop

theorem continuous_star_q {K : Type} [CommRing K] [Algebra F K] [TopologicalSpace K]
    [IsTopologicalRing K] : Continuous (star : Q d β K → Q d β K) := by
  rw [continuous_q_iff]
  simp only [QuaternionAlgebra.re_star, QuaternionAlgebra.imI_star, QuaternionAlgebra.imJ_star,
    QuaternionAlgebra.imK_star]
  have h1 := continuous_re (d := d) (β := β) (R := K)
  have h2 := continuous_imI (d := d) (β := β) (R := K)
  have h3 := continuous_imJ (d := d) (β := β) (R := K)
  have h4 := continuous_imK (d := d) (β := β) (R := K)
  exact ⟨h1.add (continuous_const.mul h2), h2.neg, h3.neg, h4.neg⟩

theorem continuous_algebraMap_q {K : Type} [CommRing K] [Algebra F K] [TopologicalSpace K]
    [IsTopologicalRing K] : Continuous (algebraMap K (Q d β K)) := by
  rw [continuous_q_iff]
  simp only [QuaternionAlgebra.algebraMap_eq]
  exact ⟨continuous_id, continuous_const, continuous_const, continuous_const⟩

theorem continuousAt_qinv {K : Type} [Field K] [Algebra F K] [TopologicalSpace K]
    [IsTopologicalDivisionRing K] {e : Q d β K} (h : qn e ≠ 0) : ContinuousAt qinv e := by
  have h1 : ContinuousAt (fun x : Q d β K => (qn x)⁻¹) e :=
    continuous_qn.continuousAt.inv₀ h
  have h2 : ContinuousAt (fun x : Q d β K => algebraMap K (Q d β K) (qn x)⁻¹) e :=
    continuous_algebraMap_q.continuousAt.comp h1
  exact h2.mul continuous_star_q.continuousAt

theorem denseRange_rat (w : Pl F) : DenseRange (rat : Q d β F → Q d β (Kp w)) := by
  have D := denseRange_algebraMap_Kp (F := F) w
  have h := D.prodMap (D.prodMap (D.prodMap D))
  have h2 := ((qHomeo (d := d) (β := β) (R := Kp w)).symm.surjective.denseRange).comp h
    (qHomeo (d := d) (β := β) (R := Kp w)).symm.continuous
  refine Dense.mono ?_ h2
  rintro _ ⟨⟨a, b, c, e⟩, rfl⟩
  exact ⟨⟨a, b, c, e⟩, rfl⟩

theorem mem_closure_of_conj_mem : ∀ {F : Type} [Field F] [NumberField F] (d β : F), (∀ x : Q d β F, qn x = 0 → x = 0) →
    ∀ s w : Pl F, ∀ a ∈ SuppAt d β {w}, ∀ c : (Q d β (AF F))ˣ,
      ((c⁻¹ : (Q d β (AF F))ˣ) : Q d β (AF F)) * a * (c : Q d β (AF F)) ∈ closure (SAQ d β s) →
      a ∈ closure (SAQ d β s) := by
  intro F _ _ d β _ s w a ha c hc
  have ha' : ((c⁻¹ : (Q d β (AF F))ˣ) : Q d β (AF F)) * a * (c : Q d β (AF F)) ∈ SuppAt d β {w} :=
    conj_mem_SuppAt c.inv_mul ha
  obtain ⟨a', ea'⟩ : ∃ a' : Q d β (AF F),
      a' = ((c⁻¹ : (Q d β (AF F))ˣ) : Q d β (AF F)) * a * (c : Q d β (AF F)) := ⟨_, rfl⟩
  rw [← ea'] at ha' hc
  obtain ⟨y, ey⟩ : ∃ y : Q d β (Kp w), y = qmap (proj w) a' := ⟨_, rfl⟩
  obtain ⟨cw, ecw⟩ : ∃ cw : Q d β (Kp w), cw = qmap (proj w) (c : Q d β (AF F)) := ⟨_, rfl⟩
  obtain ⟨cw', ecw'⟩ : ∃ cw' : Q d β (Kp w),
      cw' = qmap (proj w) ((c⁻¹ : (Q d β (AF F))ˣ) : Q d β (AF F)) := ⟨_, rfl⟩
  have h1 : cw * cw' = 1 := by rw [ecw, ecw', ← map_mul, c.mul_inv, map_one]
  have h2 : cw' * cw = 1 := by rw [ecw, ecw', ← map_mul, c.inv_mul, map_one]
  have hq : qn cw ≠ 0 := by
    intro h0
    have := congrArg qn h1
    rw [qn_mul, h0, zero_mul, qn_one] at this
    exact zero_ne_one this
  have hinv : qinv cw = cw' := qinv_unique hq h2
  have hy : y = cw' * qmap (proj w) a * cw := by rw [ey, ea', map_mul, map_mul, ecw, ecw']
  have hga : psi w (cw * y * qinv cw) = a := by
    have : cw * y * qinv cw = qmap (proj w) a := by
      rw [hinv, hy]
      calc cw * (cw' * qmap (proj w) a * cw) * cw'
          = (cw * cw') * qmap (proj w) a * (cw * cw') := by simp only [mul_assoc]
        _ = qmap (proj w) a := by rw [h1, one_mul, mul_one]
    rw [this, psi_proj ha]
  have hcont : ContinuousAt (fun e : Q d β (Kp w) => psi w (e * y * qinv e)) cw :=
    (continuous_psi w).continuousAt.comp
      ((continuousAt_id.mul continuousAt_const).mul (continuousAt_qinv hq))
  have hcl : cw ∈ closure (Set.range (rat : Q d β F → Q d β (Kp w))) := denseRange_rat w cw
  haveI : (𝓝[Set.range (rat : Q d β F → Q d β (Kp w))] cw).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.1 hcl
  have htend : Filter.Tendsto (fun e : Q d β (Kp w) => psi w (e * y * qinv e))
      (𝓝[Set.range (rat : Q d β F → Q d β (Kp w))] cw) (𝓝 a) := by
    have := hcont.tendsto
    rw [hga] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hopen : IsOpen {e : Q d β (Kp w) | qn e ≠ 0} :=
    isOpen_ne.preimage continuous_qn
  rw [← closure_closure]
  refine mem_closure_of_tendsto htend ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hopen.mem_nhds hq)] with e he he0
  obtain ⟨δ, rfl⟩ := he
  have hδ : qn δ ≠ 0 := by
    intro h0
    apply he0
    rw [rat, qn_qmap, h0, map_zero]
  have i1 : δ * qinv δ = 1 := mul_qinv hδ
  have i2 : qinv δ * δ = 1 := qinv_mul hδ
  have r1 : (rat δ : Q d β (AF F)) * rat (qinv δ) = 1 := by rw [← map_mul, i1, map_one]
  have hmem := conj_mem_closure s i1 i2 hc
  have hsupp := conj_mem_SuppAt r1 ha'
  have hw : (qinv (rat δ : Q d β (Kp w))) = rat (qinv δ) :=
    qinv_unique he0 (by rw [← map_mul, i2, map_one])
  have : psi w ((rat δ : Q d β (Kp w)) * y * qinv (rat δ : Q d β (Kp w))) =
      (rat δ : Q d β (AF F)) * a' * rat (qinv δ) := by
    rw [hw, ey, ← qmap_proj_rat w δ, ← qmap_proj_rat w (qinv δ), ← map_mul, ← map_mul]
    exact psi_proj hsupp
  rw [this]
  exact hmem

end GlobalTheory.CompanionTheory.PlaneSA.MemConj
