import Formalism.LocalToGlobal.GlobalTheory.BlockActions.TilEqLevel
import Formalism.LocalToGlobal.GlobalTheory.BlockActions.DefNOfFact
import Formalism.LocalToGlobal.GlobalTheory.BlockActions.ExistsOnOfPosDef
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.RationalPointsLeHolds
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AfsplitB

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.L2.Forms NumberField Formalism.UG Matrix
open scoped TensorProduct
open IsDedekindDomain

section Gen

theorem exists_proj {E : Type} [Field E] {N n : ℕ} (hN : n + 1 = N) (A : Matrix (Fin N) (Fin n) E) (z : Fin N → E)
    (hA : Function.Injective A.mulVec) (hz : ∀ x, A *ᵥ x ≠ z) :
    ∃ P : Matrix (Fin n) (Fin N) E, P * A = 1 ∧ P *ᵥ z = 0 := by
  subst hN
  have hB := isUnit_det_cols rfl A z hA hz
  set B : Matrix (Fin (n + 1)) (Fin (n + 1)) E :=
    Matrix.of (fun a (b : Fin (n + 1)) => if hb : (b : ℕ) < n then A a ⟨b, hb⟩ else z a) with hBdef
  have h := nonsing_inv_mul B hB
  refine ⟨Matrix.of fun a j => B⁻¹ (Fin.castSucc a) j, ?_, ?_⟩
  · ext a b
    have e := congrFun (congrFun h (Fin.castSucc a)) (Fin.castSucc b)
    simp only [mul_apply, hBdef, of_apply, Fin.val_castSucc, Fin.is_lt, dif_pos, Fin.eta, one_apply,
      Fin.castSucc_inj] at e
    simpa [mul_apply, one_apply] using e
  · funext a
    have e := congrFun (congrFun h (Fin.castSucc a)) (Fin.last n)
    simp only [mul_apply, hBdef, of_apply, Fin.val_last, lt_irrefl, dif_neg, not_false_eq_true, one_apply] at e
    simpa [mulVec, dotProduct, (Fin.castSucc_lt_last a).ne] using e

theorem cT_ext_unitary {A : Type} [CommRing A] (τ : A →+* A) {N n : ℕ} (I : Matrix (Fin N) (Fin n) A)
    (J : Matrix (Fin N) (Fin N) A) (G : Matrix (Fin N) (Fin N) A) (k : Matrix (Fin n) (Fin n) A)
    (hG : cT τ G * J * G = J) (hE : G * I = I * k) :
    cT τ k * (cT τ I * J * I) * k = cT τ I * J * I := by
  calc cT τ k * (cT τ I * J * I) * k = cT τ (I * k) * J * (I * k) := by rw [cT_mul]; simp only [Matrix.mul_assoc]
    _ = cT τ (G * I) * J * (G * I) := by rw [hE]
    _ = cT τ I * (cT τ G * J * G) * I := by rw [cT_mul]; simp only [Matrix.mul_assoc]
    _ = cT τ I * J * I := by rw [hG]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem latS_mulVec (R : Type) [CommRing R] [Algebra F R] (S : Subring (E ⊗[F] R)) {n N : ℕ}
    (M : Matrix (Fin N) (Fin n) E) (Λ' : Submodule (𝓞 E) (Fin n → E)) (Λ : Submodule (𝓞 E) (Fin N → E))
    (hM : ∀ x ∈ Λ', M *ᵥ x ∈ Λ) :
    ∀ x ∈ latS (F := F) R S Λ', (M.map (inclE (F := F) R)) *ᵥ x ∈ latS (F := F) R S Λ := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x0, hx0, rfl⟩ := hy
    apply Submodule.subset_span
    refine ⟨M *ᵥ x0, hM x0 hx0, ?_⟩
    funext i
    simp only [mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
  | zero => rw [mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mulVec_add]; exact add_mem hx hy
  | smul a x _ hx =>
    have e : (M.map (inclE (F := F) R)) *ᵥ (a • x) = a • ((M.map (inclE (F := F) R)) *ᵥ x) := by
      rw [Subring.smul_def, Subring.smul_def, mulVec_smul]
    rw [e]; exact Submodule.smul_mem _ a hx

end Gen

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

theorem exists_projP (Tf : FormsTiedSym D u Ch chOf) :
    ∃ P : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m)) D.host.E, P * iXm D = 1 ∧ P *ᵥ Tf.til.z0 = 0 := by
  obtain ⟨P, h1, h2⟩ := exists_proj (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ D.R) (iXm D) (fun i => Tf.til.z0 i / ((D.mem u).A.T : D.host.E))
    (iXm_mulVec_injective D) (quotient_not_in_range_symmetric Tf)
  refine ⟨P, h1, ?_⟩
  have hT : ((D.mem u).A.T : D.host.E) ≠ 0 := Nat.cast_ne_zero.mpr (D.mem u).A.T_prime.ne_zero
  have e : Tf.til.z0 = ((D.mem u).A.T : D.host.E) • (fun i => Tf.til.z0 i / ((D.mem u).A.T : D.host.E)) := by
    funext i; simp only [Pi.smul_apply, smul_eq_mul]; field_simp
  rw [e, mulVec_smul, h2, smul_zero]

theorem lat_in_out (Tf : FormsTiedSym D u Ch chOf) (P : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m)) D.host.E)
    (hP1 : P * iXm D = 1) (hPz : P *ᵥ Tf.til.z0 = 0) :
    (∀ x ∈ Tf.clsP.lev.Lb, iXm D *ᵥ x ∈ (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.Lb) ∧
    (∀ y ∈ (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.Lb, P *ᵥ y ∈ Tf.clsP.lev.Lb) := by
  have hL : (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.Lb =
      Tf.clsP.lev.Lb.map ((iXc D).restrictScalars (𝓞 D.host.E)) ⊔ Submodule.span (𝓞 D.host.E) {Tf.til.z0} := Tf.tilLat
  have hiX : ∀ x, iXm D *ᵥ x = iXc D x := fun x => by simp only [iXm, LinearMap.toMatrix'_mulVec]
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · rw [hL, hiX]
    exact Submodule.mem_sup_left (Submodule.mem_map_of_mem hx)
  · rw [hL] at hy
    obtain ⟨y1, hy1, y2, hy2, rfl⟩ := Submodule.mem_sup.mp hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy1
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy2
    have e1 : P *ᵥ ((iXc D).restrictScalars (𝓞 D.host.E) x) = x := by
      show P *ᵥ (iXc D x) = x
      rw [← hiX, mulVec_mulVec, hP1, one_mulVec]
    have e2 : P *ᵥ (a • Tf.til.z0) = 0 := by
      rw [← algebraMap_smul D.host.E a Tf.til.z0, mulVec_smul, hPz, smul_zero]
    rw [mulVec_add, e1, e2, add_zero]
    exact hx

theorem isExt_prV {z0 : Fin (D.R.N D.R.m) → D.host.E} (v : HeightOneSpectrum (𝓞 D.host.F))
    {k : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)}
    {G : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)}
    (h : IsExt D z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) k G) :
    IsExt D z0 (inclE (F := D.host.F) (v.adicCompletion D.host.F)) (k.map (prV (E := D.host.E) v)) (G.map (prV (E := D.host.E) v)) := by
  obtain ⟨h1, h2⟩ := h
  have hc : (prV (E := D.host.E) v).comp (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) =
      inclE (F := D.host.F) (v.adicCompletion D.host.F) := RingHom.ext fun e => rfl
  refine ⟨?_, ?_⟩
  · have := congrArg (fun M => M.map (prV (E := D.host.E) v)) h1
    simp only [Matrix.map_mul, Matrix.map_map] at this
    rw [← RingHom.coe_comp, hc] at this
    exact this
  · funext i
    have := congrArg (fun w => prV (E := D.host.E) v (w i)) h2
    simp only at this
    exact (RingHom.map_mulVec _ _ _ _).symm.trans this

set_option maxHeartbeats 4000000 in

theorem lev_lat (Tf : FormsTiedSym D u Ch chOf)
    (k : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (G : GL (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hE : IsExt D Tf.til.z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) k G.1)
    (hG : G ∈ (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.U) (v : HeightOneSpectrum (𝓞 D.host.F))
    (x : Fin (D.R.N D.R.m - 1) → D.host.E ⊗[D.host.F] v.adicCompletion D.host.F) :
    x ∈ latS (F := D.host.F) (v.adicCompletion D.host.F)
      (tensInt (F := D.host.F) (v.adicCompletion D.host.F) (intOE D.host.E) (v.adicCompletionIntegers D.host.F).toSubring) Tf.clsP.lev.Lb ↔
    (k.map (prV (E := D.host.E) v)) *ᵥ x ∈ latS (F := D.host.F) (v.adicCompletion D.host.F)
      (tensInt (F := D.host.F) (v.adicCompletion D.host.F) (intOE D.host.E) (v.adicCompletionIntegers D.host.F).toSubring) Tf.clsP.lev.Lb := by
  set S := tensInt (F := D.host.F) (v.adicCompletion D.host.F) (intOE D.host.E) (v.adicCompletionIntegers D.host.F).toSubring
  set Km := (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev
  have hGv : bc (prV (E := D.host.E) v) G ∈ levelVL (sigD D) (gramN D D.R.m le_rfl) v Km.Lb :=
    Km.Uloc_lev v (((Km.U_eq G).1 hG).2 v)
  have hst := (Subgroup.mem_inf.mp hGv).2
  have hGm : ((bc (prV (E := D.host.E) v) G : GL _ _) : Matrix _ _ _) = G.1.map (prV (E := D.host.E) v) := rfl
  obtain ⟨hEv, -⟩ := isExt_prV v hE
  obtain ⟨P, hP1, hPz⟩ := exists_projP Tf
  obtain ⟨hin, hout⟩ := lat_in_out Tf P hP1 hPz
  have hI := latS_mulVec (F := D.host.F) (v.adicCompletion D.host.F) S (iXm D) _ _ hin
  have hO := latS_mulVec (F := D.host.F) (v.adicCompletion D.host.F) S P _ _ hout
  have hPI : (P.map (inclE (F := D.host.F) (v.adicCompletion D.host.F))) * ((iXm D).map (inclE (F := D.host.F) (v.adicCompletion D.host.F))) = 1 := by
    rw [← Matrix.map_mul, hP1, Matrix.map_one _ (map_zero _) (map_one _)]
  have hback : ∀ y, y = (P.map (inclE (F := D.host.F) (v.adicCompletion D.host.F))) *ᵥ
      (((iXm D).map (inclE (F := D.host.F) (v.adicCompletion D.host.F))) *ᵥ y) := fun y => by
    rw [mulVec_mulVec, hPI, one_mulVec]
  have hcomm : ∀ y, G.1.map (prV (E := D.host.E) v) *ᵥ (((iXm D).map (inclE (F := D.host.F) (v.adicCompletion D.host.F))) *ᵥ y) =
      ((iXm D).map (inclE (F := D.host.F) (v.adicCompletion D.host.F))) *ᵥ ((k.map (prV (E := D.host.E) v)) *ᵥ y) := fun y => by
    rw [mulVec_mulVec, hEv, ← mulVec_mulVec]
  have hs : ∀ y, y ∈ latS (F := D.host.F) (v.adicCompletion D.host.F) S Km.Lb ↔
      G.1.map (prV (E := D.host.E) v) *ᵥ y ∈ latS (F := D.host.F) (v.adicCompletion D.host.F) S Km.Lb := fun y => by
    rw [← hGm]; exact hst y
  constructor
  · intro hx
    have h1 := (hs _).1 (hI x hx)
    rw [hcomm] at h1
    rw [hback ((k.map (prV (E := D.host.E) v)) *ᵥ x)]
    exact hO _ h1
  · intro hx
    have h1 := hI _ hx
    rw [← hcomm] at h1
    rw [hback x]
    exact hO _ ((hs _).2 h1)

theorem lev_unit (Tf : FormsTiedSym D u Ch chOf)
    (k : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (G : GL (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hE : IsExt D Tf.til.z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) k G.1)
    (hG : G ∈ (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.U) :
    cT (sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) k *
      (gramP D).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) * k =
      (gramP D).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
  set Km := (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev
  have hU : G ∈ UPts (sigD D) (gramN D D.R.m le_rfl) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := ((Km.U_eq G).1 hG).1
  have hc : (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)).comp (sigD D : D.host.E →+* D.host.E) =
      (sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)).comp (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
    ext e
    simp [sigR, inclE, Algebra.TensorProduct.includeLeftRingHom_apply]
  have hJ : (gramP D).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) =
      cT (sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ((iXm D).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))) *
        (gramN D D.R.m le_rfl).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) *
        (iXm D).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
    rw [Formalism.UG.P.cT_map _ _ _ hc, ← Matrix.map_mul, ← Matrix.map_mul, gramP_eq]
    rfl
  rw [hJ]
  exact cT_ext_unitary _ _ _ _ _ hU hE.1

theorem lev_isUnit (Tf : FormsTiedSym D u Ch chOf)
    (k : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (G : GL (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hE : IsExt D Tf.til.z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) k G.1) :
    IsUnit k.det := by
  obtain ⟨P, hP1, -⟩ := exists_projP Tf
  obtain ⟨Gi, hGi⟩ : ∃ Gi : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F),
      Gi * G.1 = 1 := ⟨(G⁻¹ : GL _ _).1, by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]⟩
  have hQ : HMul.hMul (HMul.hMul Gi ((iXm D).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))) k = (iXm D).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
    rw [Matrix.mul_assoc, ← hE.1, ← Matrix.mul_assoc, hGi, Matrix.one_mul]
  have hl : HMul.hMul (HMul.hMul (P.map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))) (HMul.hMul Gi ((iXm D).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))))) k = 1 := by
    rw [Matrix.mul_assoc, hQ, ← Matrix.map_mul, hP1, Matrix.map_one _ (map_zero _) (map_one _)]
  exact Matrix.isUnit_det_of_left_inverse hl

end Formalism.L2.GlobalTheoryTheory.Br
