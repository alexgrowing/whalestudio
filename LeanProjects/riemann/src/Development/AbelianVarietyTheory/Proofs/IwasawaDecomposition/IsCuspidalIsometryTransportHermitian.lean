import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix Formalism.IndefR.Datum
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Isom.IsoMat

open Formalism.UG (cT cT_mul cT_one)

section Gen

variable {A : Type} [CommRing A] {k n m : ℕ}

theorem conj_right_zero {r : ℕ} {aP : Matrix (Fin m) (Fin n) A} {aQ : Matrix (Fin n) (Fin m) A} (hQP : aQ * aP = 1)
    {x : Matrix (Fin n) (Fin n) A} {c : Matrix (Fin n) (Fin r) A} (h : x * c = 0) : aP * x * aQ * (aP * c) = 0 := by
  calc _ = aP * (x * ((aQ * aP) * c)) := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hQP, Matrix.one_mul, h, Matrix.mul_zero]

theorem conj_left_zero {aP : Matrix (Fin m) (Fin n) A} {aQ : Matrix (Fin n) (Fin m) A} (hQP : aQ * aP = 1)
    {x : Matrix (Fin n) (Fin n) A} {y : Matrix (Fin k) (Fin n) A} (h : y * x = 0) : y * aQ * (aP * x * aQ) = 0 := by
  calc _ = (y * ((aQ * aP) * x)) * aQ := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hQP, Matrix.one_mul, h, Matrix.zero_mul]

theorem conj_mulVec {r : ℕ} (aP : Matrix (Fin m) (Fin n) A) (aQ : Matrix (Fin n) (Fin m) A)
    (x : Matrix (Fin n) (Fin n) A) (c : Matrix (Fin n) (Fin r) A) (v : Fin m → A) (a : Fin r → A)
    (h : x.mulVec (aQ.mulVec v) = c.mulVec a) : (aP * x * aQ).mulVec v = (aP * c).mulVec a := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_mulVec]

theorem conj_sub_one {aP : Matrix (Fin m) (Fin n) A} {aQ : Matrix (Fin n) (Fin m) A} (hPQ : aP * aQ = 1)
    (x : Matrix (Fin n) (Fin n) A) : aP * x * aQ - 1 = aP * (x - 1) * aQ := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hPQ]

end Gen

variable {D : D7} {V V' : HSp D} (I : IsoMat V V')

theorem cT_P_gram : cT (D.sp.cm.sig : D.host.E →+* D.host.E) I.P * V'.gram = V.gram * I.Q := by
  rw [← I.gram, Matrix.mul_assoc _ I.P, I.PQ, Matrix.mul_one]

theorem mat_kap_sub (g : GA D V) :
    (matHom V' (I.kap g)).1 - 1 = HMul.hMul (HMul.hMul I.aP ((matHom V g).1 - 1)) I.aQ :=
  conj_sub_one I.aP_aQ _

theorem kap_mem_NI {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) {x : GA D V} (hx : x ∈ NI V C) :
    I.kap x ∈ NI V' (I.P * C) := by
  have key : NI V C ≤ (NI V' (I.P * C)).comap I.kap.toMonoidHom := by
    refine (Subgroup.closure_le _).2 ?_
    intro g hg
    show I.kap g ∈ NI V' (I.P * C)
    obtain ⟨h1, h2, h3⟩ := hg
    refine Subgroup.subset_closure ?_
    have hm := I.mat_kap_sub g
    have hPC : (I.P * C).map (incA D) = I.aP * C.map (incA D) := Matrix.map_mul
    have hG : cT (D.sp.cm.sig : D.host.E →+* D.host.E) (I.P * C) * V'.gram =
        cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * V.gram * I.Q := by
      rw [cT_mul, Matrix.mul_assoc, I.cT_P_gram, Matrix.mul_assoc]
    have hGm : (cT (D.sp.cm.sig : D.host.E →+* D.host.E) (I.P * C) * V'.gram).map (incA D) =
        (cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * V.gram).map (incA D) * I.aQ := by
      rw [hG, Matrix.map_mul]; rfl
    refine ⟨?_, ?_, fun x' hx' => ?_⟩
    · show HMul.hMul ((matHom V' (I.kap g)).1 - 1) ((I.P * C).map (incA D)) = 0
      rw [hm, hPC]
      exact conj_right_zero I.aQ_aP h1
    · show HMul.hMul ((cT (D.sp.cm.sig : D.host.E →+* D.host.E) (I.P * C) * V'.gram).map (incA D))
        ((matHom V' (I.kap g)).1 - 1) = 0
      rw [hGm, hm]
      exact conj_left_zero I.aQ_aP h2
    · have hx : (cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * V.gram).mulVec (I.Q.mulVec x') = 0 := by
        rw [Matrix.mulVec_mulVec, ← hG]
        exact hx'
      obtain ⟨a, ha⟩ := h3 _ hx
      refine ⟨a, ?_⟩
      have hQx : I.aQ.mulVec (fun i => incA D (x' i)) = fun i => incA D (I.Q.mulVec x' i) :=
        funext fun i => (RingHom.map_mulVec (incA D) I.Q x' i).symm
      show ((matHom V' (I.kap g)).1 - 1).mulVec (fun i => incA D (x' i)) = ((I.P * C).map (incA D)).mulVec a
      rw [hm, hPC]
      refine conj_mulVec _ _ _ _ _ _ ?_
      rw [hQx]
      exact ha
  exact key hx

theorem isIsoFrame_Q {r : ℕ} {C' : Matrix (Fin V'.rank) (Fin r) D.host.E} (h : IsIsoFrame V' C') :
    IsIsoFrame V (I.Q * C') := by
  obtain ⟨hr, hli, hiso⟩ := h
  refine ⟨hr, ?_, ?_⟩
  · have e : (I.Q * C').transpose = (Matrix.mulVecLin I.Q) ∘ C'.transpose := by
      funext i j
      rfl
    rw [e]
    refine hli.map' _ (LinearMap.ker_eq_bot.2 fun a b hab => ?_)
    have := congrArg I.P.mulVec hab
    simpa [Matrix.mulVec_mulVec, I.PQ] using this
  · have hg : cT (D.sp.cm.sig : D.host.E →+* D.host.E) I.Q * V.gram * I.Q = V'.gram := I.symm.gram
    rw [cT_mul]
    calc _ = cT (D.sp.cm.sig : D.host.E →+* D.host.E) C' *
          (cT (D.sp.cm.sig : D.host.E →+* D.host.E) I.Q * V.gram * I.Q) * C' := by
          simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hg]; exact hiso

theorem kap_mem_NI' {r : ℕ} {C' : Matrix (Fin V'.rank) (Fin r) D.host.E} {x : GA D V} (hx : x ∈ NI V (I.Q * C')) :
    I.kap x ∈ NI V' C' := by
  have := I.kap_mem_NI (I.Q * C') hx
  rwa [← Matrix.mul_assoc, I.PQ, Matrix.one_mul] at this

theorem kap_symm_mem_NI {r : ℕ} {C' : Matrix (Fin V'.rank) (Fin r) D.host.E} {y : GA D V'} (hy : y ∈ NI V' C') :
    I.kap.symm y ∈ NI V (I.Q * C') :=
  I.symm.kap_mem_NI C' hy

end GlobalTheory.Mem.Isom.IsoMat

open GlobalTheory.Mem.Isom GlobalTheory.Mem.Isom.IsoMat in

theorem GlobalTheory.Mem.Isom.isCuspFun_tr : ∀ (D : D7) (V V' : HSp D) (I : GlobalTheory.Mem.Isom.IsoMat V V') (φ : GA D V → ℂ),
    IsCuspFun V φ → IsCuspFun V' (I.tr φ) := by
  intro D V V' I φ hφ r C' hC' μ 𝓕 hμ h𝓕 g
  haveI := GlobalTheory.AutFunCounterexample.borel_NI D V (I.Q * C')
  haveI := GlobalTheory.AutFunCounterexample.borel_NI D V' C'
  haveI := GlobalTheory.AutFunCounterexample.topGroup_GA D V
  haveI := GlobalTheory.AutFunCounterexample.topGroup_GA D V'
  let T : NI V (I.Q * C') ≃ₜ* NI V' C' :=
    { toFun := fun x => ⟨I.kap (x : GA D V), I.kap_mem_NI' x.2⟩
      invFun := fun y => ⟨I.kap.symm (y : GA D V'), I.kap_symm_mem_NI y.2⟩
      left_inv := fun x => Subtype.ext (I.kap.symm_apply_apply (x : GA D V))
      right_inv := fun y => Subtype.ext (I.kap.apply_symm_apply (y : GA D V'))
      map_mul' := fun x y => Subtype.ext (map_mul I.kap (x : GA D V) (y : GA D V))
      continuous_toFun := (I.continuous_kap.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (I.continuous_kap_symm.comp continuous_subtype_val).subtype_mk _ }
  let e : NI V (I.Q * C') ≃ᵐ NI V' C' := T.toHomeomorph.toMeasurableEquiv
  have hp : MeasurePreserving e (μ.map e.symm) μ :=
    (MeasurePreserving.symm e.symm ⟨e.symm.measurable, rfl⟩ :)
  have hH : (μ.map e.symm).IsHaarMeasure := T.symm.isHaarMeasure_map μ
  have hF : IsFundamentalDomain (NIQ V (I.Q * C')) (e ⁻¹' 𝓕) (μ.map e.symm) := by
    refine h𝓕.preimage_of_equiv hp.quasiMeasurePreserving
      (e := fun γ => ⟨T.symm γ, I.symm.kap_mem_GQ γ.2⟩) ⟨fun a b hab => ?_, fun b => ?_⟩ fun γ x => ?_
    · exact Subtype.ext (T.symm.injective (congrArg Subtype.val hab))
    · exact ⟨⟨T b.1, I.kap_mem_GQ b.2⟩, Subtype.ext (T.symm_apply_apply _)⟩
    · change T (T.symm γ * x) = γ * T x
      rw [map_mul, T.apply_symm_apply]
  have key := hφ r (I.Q * C') (I.isIsoFrame_Q hC') (μ.map e.symm) (e ⁻¹' 𝓕) hH hF (I.kap.symm g)
  rw [← hp.setIntegral_preimage_emb e.measurableEmbedding (fun n : NI V' C' => I.tr φ ((n : GA D V') * g)) 𝓕]
  refine Eq.trans ?_ key
  congr 1
  funext x
  show φ (I.kap.symm (I.kap (x : GA D V) * g)) = φ ((x : GA D V) * I.kap.symm g)
  rw [map_mul, MulEquiv.symm_apply_apply]
