import Formalism.LocalToGlobal.GlobalTheory.BlockActions.FormsOfLatticeExtension
import Formalism.LocalToGlobal.GlobalTheory.BlockActions.InJSymRestrict

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

section GenE

theorem ext_mem_gen {A S : Type} [CommRing A] [Ring S] {n N : ℕ} [Module S (Fin N → A)] [Module S (Fin n → A)]
    (Λm Λd : Submodule S (Fin N → A)) (Λp : Submodule S (Fin n → A)) (hmd : Λm ≤ Λd)
    (I : Matrix (Fin N) (Fin n) A) (P : Matrix (Fin n) (Fin N) A) (k : Matrix (Fin n) (Fin n) A)
    (G : Matrix (Fin N) (Fin N) A) (hPI : P * I = 1) (hG : G = I * k * P + (1 - I * P))
    (hk : ∀ x, x ∈ Λp ↔ k *ᵥ x ∈ Λp) (hI : ∀ x ∈ Λp, I *ᵥ x ∈ Λm) (hO : ∀ x ∈ Λd, P *ᵥ x ∈ Λp)
    (x : Fin N → A) : (x ∈ Λd ↔ G *ᵥ x ∈ Λd) ∧ (x ∈ Λd → G *ᵥ x - x ∈ Λm) := by
  have hGx : G *ᵥ x - x = I *ᵥ (k *ᵥ (P *ᵥ x)) - I *ᵥ (P *ᵥ x) := by
    simp only [hG, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
    abel
  have hPIv : ∀ y, P *ᵥ (I *ᵥ y) = y := fun y => by rw [Matrix.mulVec_mulVec, hPI, Matrix.one_mulVec]
  have e : G *ᵥ x = x + (I *ᵥ (k *ᵥ (P *ᵥ x)) - I *ᵥ (P *ᵥ x)) := by rw [← hGx]; abel
  have hPG : P *ᵥ (G *ᵥ x) = k *ᵥ (P *ᵥ x) := by
    rw [e, Matrix.mulVec_add, Matrix.mulVec_sub, hPIv, hPIv]; abel
  have hdiff : P *ᵥ x ∈ Λp → G *ᵥ x - x ∈ Λm := fun h => by
    rw [hGx]; exact sub_mem (hI _ ((hk _).1 h)) (hI _ h)
  refine ⟨⟨fun hx => ?_, fun hx => ?_⟩, fun hx => hdiff (hO x hx)⟩
  · have e2 : G *ᵥ x = x + (G *ᵥ x - x) := by abel
    rw [e2]; exact add_mem hx (hmd (hdiff (hO x hx)))
  · have h1 : P *ᵥ x ∈ Λp := (hk _).2 (by rw [← hPG]; exact hO _ hx)
    have e2 : x = G *ᵥ x - (G *ᵥ x - x) := by abel
    rw [e2]; exact sub_mem hx (hmd (hdiff h1))

theorem stabFun_gen {A R M : Type} [CommRing A] [CommRing R] [Algebra R A] [AddCommGroup M] [Module R M] {N : ℕ}
    (Λ Λm : Submodule R (Fin N → A)) (f : Λ →ₗ[R] M) (g : GL (Fin N) A)
    (hst : ∀ x, x ∈ Λ ↔ (g : Matrix (Fin N) (Fin N) A) *ᵥ x ∈ Λ)
    (hd : ∀ x ∈ Λ, (g : Matrix (Fin N) (Fin N) A) *ᵥ x - x ∈ Λm) (hm : Λm ≤ Λ)
    (hf : ∀ y : Λ, y.1 ∈ Λm → f y = 0) : g ∈ stabFun Λ f := by
  refine ⟨hst, fun x => ?_⟩
  have e : (⟨(g : Matrix (Fin N) (Fin N) A) *ᵥ (x : Fin N → A), (hst x).1 x.2⟩ : Λ) = x + ⟨_, hm (hd x.1 x.2)⟩ :=
    Subtype.ext (by simp)
  rw [e, map_add, hf ⟨_, hm (hd x.1 x.2)⟩ (hd x.1 x.2), add_zero]

end GenE

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

theorem proj_dual (Tf : FormsTiedSym D u Ch chOf) (P : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m)) D.host.E)
    (hP1 : P * iXm D = 1) (hPz : P *ᵥ Tf.til.z0 = 0) :
    ∀ y ∈ Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl)
      (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.Lb), P *ᵥ y ∈ Tf.clsP.lev.Lb := by
  have hiX : ∀ x, iXm D *ᵥ x = iXc D x := fun x => by simp only [iXm, LinearMap.toMatrix'_mulVec]
  obtain ⟨a0, ha0⟩ := Tf.til.lastCoordinateUniformizerVector_spans_orthogonal_line
  have ha : a0 ≠ 0 := by
    rintro rfl
    have hT : ((D.mem u).A.T : D.host.E) ≠ 0 := Nat.cast_ne_zero.mpr (D.mem u).A.T_prime.ne_zero
    have h := Tf.til.hermitianForm_lastCoordinateUniformizerVector_self
    rw [ha0, zero_smul] at h
    simp [Formalism.UG.hform] at h
    exact hT h.symm
  have hPzc : P *ᵥ zc D = 0 := by
    rw [ha0, Matrix.mulVec_smul] at hPz
    exact (smul_eq_zero.mp hPz).resolve_left ha
  have hin := (lat_in_out Tf P hP1 hPz).1
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, s, rfl⟩ := span_iXc_zc D y
    have e : P *ᵥ (iXc D x + s • zc D) = x := by
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, hPzc, smul_zero, add_zero, ← hiX, Matrix.mulVec_mulVec, hP1,
        Matrix.one_mulVec]
    rw [e]
    have hd : x ∈ dualSet (sigD D : D.host.E →+* D.host.E) (gramP D) Tf.clsP.lev.Lb := by
      intro x' hx'
      have h := hy (iXc D x') (by rw [← hiX]; exact hin x' hx')
      rwa [hform_add_right, hform_smul_rightB, hform_iXc, hform_iXc_zc, mul_zero, add_zero] at h
    have := Tf.clsP.lev.Lb_dual x hd
    simpa using this
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
  | smul a x _ hx =>
    rw [← algebraMap_smul D.host.E a x, Matrix.mulVec_smul, algebraMap_smul]
    exact Submodule.smul_mem _ a hx

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem extV_lat (Tf : FormsTiedSym D u Ch chOf) (κ : Tf.clsP.lev.U)
    (G : GL (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))
    (hE : IsExt D Tf.til.z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) κ.1.1 G.1)
    (v : HeightOneSpectrum (𝓞 D.host.F)) (P : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m)) D.host.E)
    (hP1 : P * iXm D = 1) (hPz : P *ᵥ Tf.til.z0 = 0)
    (Λd : Submodule (intV D.host.E v) (Fin (D.R.N D.R.m) → D.host.E ⊗[D.host.F] v.adicCompletion D.host.F))
    (hmd : latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v) (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.Lb ≤ Λd)
    (hO : ∀ x ∈ Λd, (P.map (inclE (F := D.host.F) (v.adicCompletion D.host.F))) *ᵥ x ∈
      latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v) Tf.clsP.lev.Lb)
    (x : Fin (D.R.N D.R.m) → D.host.E ⊗[D.host.F] v.adicCompletion D.host.F) :
    (x ∈ Λd ↔ G.1.map (prV (E := D.host.E) v) *ᵥ x ∈ Λd) ∧
      (x ∈ Λd → G.1.map (prV (E := D.host.E) v) *ᵥ x - x ∈
        latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v) (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.Lb) := by
  have hκv : bc (prV (E := D.host.E) v) κ.1 ∈ Tf.clsP.lev.Uloc v := ((Tf.clsP.lev.U_eq κ.1).1 κ.2).2 v
  have hκst := (Subgroup.mem_inf.mp (Tf.clsP.lev.Uloc_lev v hκv)).2
  have hin := (lat_in_out Tf P hP1 hPz).1
  have hI := latS_mulVec (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v) (iXm D) _ _ hin
  have hform := ext_form Tf (inclE (F := D.host.F) (v.adicCompletion D.host.F)) P hP1 hPz _ _ (isExt_prV v hE)
  rw [Matrix.map_mul] at hform
  have hPI : (P.map (inclE (F := D.host.F) (v.adicCompletion D.host.F))) *
      ((iXm D).map (inclE (F := D.host.F) (v.adicCompletion D.host.F))) = 1 := by
    rw [← Matrix.map_mul, hP1, Matrix.map_one _ (map_zero _) (map_one _)]
  exact ext_mem_gen _ Λd _ hmd _ _ (κ.1.1.map (prV (E := D.host.E) v)) _ hPI hform (fun y => hκst y) hI hO x

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem extV_unit (Tf : FormsTiedSym D u Ch chOf) (κ : Tf.clsP.lev.U)
    (G : GL (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))
    (hE : IsExt D Tf.til.z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) κ.1.1 G.1)
    (v : HeightOneSpectrum (𝓞 D.host.F)) :
    bc (prV (E := D.host.E) v) G ∈ UJ (sigR (sigD D) (v.adicCompletion D.host.F))
      ((gramN D D.R.m le_rfl).map (inclE (F := D.host.F) (v.adicCompletion D.host.F))) := by
  have hκv : bc (prV (E := D.host.E) v) κ.1 ∈ Tf.clsP.lev.Uloc v := ((Tf.clsP.lev.U_eq κ.1).1 κ.2).2 v
  have hκU0 := Tf.clsP.lev.Uloc_le v hκv
  have hκU : cT (sigR (sigD D) (v.adicCompletion D.host.F)) (κ.1.1.map (prV (E := D.host.E) v)) *
      (gramP D).map (inclE (F := D.host.F) (v.adicCompletion D.host.F)) * κ.1.1.map (prV (E := D.host.E) v) =
      (gramP D).map (inclE (F := D.host.F) (v.adicCompletion D.host.F)) := hκU0
  show cT (sigR (sigD D) (v.adicCompletion D.host.F)) (G.1.map (prV (E := D.host.E) v)) *
      (gramN D D.R.m le_rfl).map (inclE (F := D.host.F) (v.adicCompletion D.host.F)) * G.1.map (prV (E := D.host.E) v) =
      (gramN D D.R.m le_rfl).map (inclE (F := D.host.F) (v.adicCompletion D.host.F))
  exact extUR Tf _ hκU _ (isExt_prV v hE)

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem extV_stabL (Tf : FormsTiedSym D u Ch chOf) (κ : Tf.clsP.lev.U)
    (G : GL (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))
    (hE : IsExt D Tf.til.z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) κ.1.1 G.1)
    (v : HeightOneSpectrum (𝓞 D.host.F)) :
    bc (prV (E := D.host.E) v) G ∈ stabGL (latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v)
      (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.Lb) := by
  obtain ⟨P, hP1, hPz⟩ := exists_projP Tf
  have hout := (lat_in_out Tf P hP1 hPz).2
  have hO := latS_mulVec (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v) P _ _ hout
  intro x
  exact (extV_lat Tf κ G hE v P hP1 hPz _ le_rfl hO x).1

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem extV_level (Tf : FormsTiedSym D u Ch chOf) (κ : Tf.clsP.lev.U)
    (G : GL (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))
    (hE : IsExt D Tf.til.z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) κ.1.1 G.1)
    (v : HeightOneSpectrum (𝓞 D.host.F)) :
    bc (prV (E := D.host.E) v) G ∈ levelVL (sigD D) (gramN D D.R.m le_rfl) v (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.Lb :=
  Subgroup.mem_inf.mpr ⟨extV_unit Tf κ G hE v, extV_stabL Tf κ G hE v⟩

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem extV_fT (Tf : FormsTiedSym D u Ch chOf) (κ : Tf.clsP.lev.U)
    (G : GL (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))
    (hE : IsExt D Tf.til.z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) κ.1.1 G.1)
    (v : HeightOneSpectrum (𝓞 D.host.F)) (hT : ((D.mem u).A.T : 𝓞 D.host.F) ∈ v.asIdeal) :
    bc (prV (E := D.host.E) v) G ∈ stabFun _ ((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.fT v hT) := by
  obtain ⟨P, hP1, hPz⟩ := exists_projP Tf
  have hOd := latS_mulVec (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v) P _ _ (proj_dual Tf P hP1 hPz)
  have hmd : latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v) (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.Lb ≤
      latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v)
        (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl)
          (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.Lb)) :=
    Submodule.span_mono (Set.image_mono fun y hy =>
      Submodule.subset_span ((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.Lb_int y hy))
  exact stabFun_gen _ _ _ (bc (prV (E := D.host.E) v) G)
    (fun x => (extV_lat Tf κ G hE v P hP1 hPz _ hmd hOd x).1)
    (fun x hx => (extV_lat Tf κ G hE v P hP1 hPz _ hmd hOd x).2 hx) hmd
    (fun y hy => (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.fT_L v hT y hy)

end Formalism.L2.GlobalTheoryTheory.Br
