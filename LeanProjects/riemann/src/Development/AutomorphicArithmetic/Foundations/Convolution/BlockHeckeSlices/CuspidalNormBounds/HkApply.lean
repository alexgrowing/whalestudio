import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.SliceShift
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommuteRtOfMemZalg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CapCommuteRtInfGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EquivOfISupRange
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeVecMemFixed

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG GroundTheory.Automorphic UpperTheory.V.Cm

namespace UpperTheory.ConvolutionTheory.BW

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ}

private theorem tj_mem (w : Pl E) (j : ℕ) :
    Tj ℂ n (Ov E w) (exists_isUnifV w).choose j ∈ Hecke ℂ (KGL w n) := Tj_mem_hecke (exists_isUnifV w).choose_spec j

private theorem hk_apply (w : Pl E) (j : ℕ) (φ : Sm E n) :
    hk n w j φ = (qc w ^ (((j : ℂ) * ((n : ℂ) - j)) / 2))⁻¹ •
      heckeVec (rw n w) (KGL w n) (Tj ℂ n (Ov E w) (exists_isUnifV w).choose j) φ := by
  unfold hk
  rw [LinearMap.smul_apply]
  congr 1
  have hf : (Function.support fun c : GL (Fin n) (w.adicCompletion E) ⧸ KGL w n =>
      Tj ℂ n (Ov E w) (exists_isUnifV w).choose j c.out • rw n w c.out).Finite :=
    (Formalism.UG.P.finite_support_cosets (Final.GLintComm E w n) (tj_mem w j).2).subset fun c hc h0 => hc (by simp [h0])
  exact (LinearMap.applyₗ (R := ℂ) φ).toAddMonoidHom.map_finsum hf

private theorem hk_comm (w : Pl E) (j : ℕ) (A : Module.End ℂ (Sm E n)) (hA : ∀ g, Commute A (rw n w g)) :
    Commute A (hk n w j) := by
  refine LinearMap.ext fun φ => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, hk_apply, hk_apply, map_smul,
    map_heckeVec (Final.GLintComm E w n) (tj_mem w j) (ρ' := rw n w) A fun g y => LinearMap.congr_fun (hA g).eq y]

private theorem uC_fin (u : UC E n) (k : GL (Fin n) (Af E)) : Commute (uC E n u) (rt E n (finGL E n k)) := by
  let P := (Subalgebra.centralizer ℂ {rt E n (finGL E n k)}).comap (uC E n)
  have h1 : ∀ X, ιC E n X ∈ P := fun X => by
    rw [Subalgebra.mem_comap, uC_ιC]
    rintro _ rfl
    exact (lie_rt_fin _ _).symm
  have h : Algebra.adjoin ℂ {x : UC E n | ∃ τ i j, x = genC τ i j} ≤ P :=
    Algebra.adjoin_le (by
      rintro _ ⟨τ, i, j, rfl⟩
      rw [genC, UpperTheory.V.AlgRepEndIrreducible.eL]
      exact P.smul_mem (P.sub_mem (h1 _) (P.smul_mem (h1 _) _)) _)
  have hu : u ∈ P := h (adjoin_genC (E := E) (a := n) ▸ Algebra.mem_top)
  exact (hu _ rfl).symm

omit [IsTotallyComplex E] in
private theorem kgl_eq (w : Pl E) : GLnLocal.integralGL (w.adicCompletion E) n = KGL w n := by
  have h : ∀ O : Subring (w.adicCompletion E), O = (ValuativeRel.valuation (w.adicCompletion E)).integer →
      GLnLocal.integralGL (w.adicCompletion E) n = GLint (Fin n) O := by
    rintro _ rfl
    rfl
  exact h _ (Subring.ext fun x => (GroundTheory.Global.mem_valuationInteger_iff w x).symm)

private theorem split_k (w : Pl E) (k : KA E n) : ∃ k' : GA E n, (∀ g, Commute (rt E n k') (rw n w g)) ∧
    ∃ kw ∈ KGL w n, rt E n k = rt E n k' * rw n w kw := by
  set kf := GeneralLinearGroup.map (pFin E) (k : GA E n) with hkf
  set kw := GeneralLinearGroup.map (pLoc E w) kf with hkw
  have hmem : kw ∈ KGL w n := by
    rw [← kgl_eq]
    have e : kw = Reduction.finAt w (k : GA E n) := by
      ext i j : 2
      rfl
    rw [e]
    exact k.2.2 w
  set u := kf * (locGL E n w kw)⁻¹ with hu
  have hu1 : GeneralLinearGroup.map (pLoc E w) u = 1 := by
    rw [hu, map_mul, map_inv, pLoc_locGL, mul_inv_cancel]
  refine ⟨infGL E n (GeneralLinearGroup.map (pInf E) (k : GA E n)) * finGL E n u, fun g => ?_, kw, hmem, ?_⟩
  · refine Commute.map (f := rt E n) (y := finGL E n (locGL E n w g)) (Commute.mul_left (infGL_comm _ _) ?_)
    exact Commute.map (LocUniq.comm_locGL w hu1 g) (finGL E n)
  · change _ = _ * rt E n (finGL E n (locGL E n w kw))
    rw [← map_mul, mul_assoc, ← map_mul, hu, inv_mul_cancel_right, infGL_mul_finGL]

private theorem rw_comm {w w' : Pl E} (e : w ≠ w') (g : GL (Fin n) (w'.adicCompletion E))
    (k : GL (Fin n) (w.adicCompletion E)) : Commute (rw n w' g) (rw n w k) :=
  Commute.map (LocUniq.comm_locGL w (pLoc_locGL_of_ne e g) k) (finRep E n)

private theorem hk_fixed (w : Pl E) (j : ℕ) {φ : Sm E n} (h : ∀ k ∈ KGL w n, rw n w k φ = φ) :
    ∀ k ∈ KGL w n, rw n w k (hk n w j φ) = hk n w j φ := fun k hk' => by
  rw [hk_apply, map_smul, GlobalTheory.LGrp.mem_fixed.1
    (SatCompare.heckeVec_mem_fixed (Final.GLintComm E w n) (tj_mem w j) (GlobalTheory.LGrp.mem_fixed.2 h)) k hk']

private theorem hk_zero (w : Pl E) {φ : Sm E n} (h : ∀ k ∈ KGL w n, rw n w k φ = φ) : hk n w 0 φ = φ := by
  have e : Tj ℂ n (Ov E w) (exists_isUnifV w).choose 0 = dosetInd ℂ (KGL w n) 1 := by
    have d : diagJ n (exists_isUnifV w).choose 0 = 1 := by simp [diagJ]
    unfold Tj dosetInd
    congr 1
    ext g
    simp only [d, Set.mem_setOf_eq, DoubleCoset.mem_doubleCoset, mul_one, SetLike.mem_coe, ← Units.val_mul, Units.val_inj]
  rw [hk_apply, e, SatCompare.heckeVec_one (Final.GLintComm E w n) (GlobalTheory.LGrp.mem_fixed.2 h)]
  simp

end UpperTheory.ConvolutionTheory.BW

open UpperTheory.ConvolutionTheory.BW in
theorem UpperTheory.ConvolutionTheory.BW.hkOps :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.HkOps E := by
  intro E _ _ _ n w j
  refine ⟨hk_apply w j, fun u => hk_comm w j _ fun g => uC_fin u _, fun y => hk_comm w j _ fun g => ?_,
    fun S φ hw hφ => ⟨fun w' hw' k hk' => ?_, hk_zero w (hφ w hw), fun k => ⟨fun w' hw' x hx => ?_, ?_⟩, fun w' hw' j' => ?_⟩⟩
  · exact Commute.map (f := rt E n) (y := finGL E n (locGL E n w g)) (infGL_comm _ _)
  · by_cases e : w = w'
    · subst e
      exact hk_fixed w j (hφ w hw) k hk'
    · rw [← Module.End.mul_apply, (hk_comm w j _ (rw_comm e k)).eq, Module.End.mul_apply, hφ w' hw' k hk']
  · obtain ⟨k', h1, kw, h2, h3⟩ := split_k w' k
    rw [h3, Module.End.mul_apply, hφ w' hw' kw h2, ← Module.End.mul_apply, ← (h1 x).eq, Module.End.mul_apply, hφ w' hw' x hx]
  · obtain ⟨k', h1, kw, h2, h3⟩ := split_k w k
    rw [h3, Module.End.mul_apply, Module.End.mul_apply, hφ w hw kw h2, hk_fixed w j (hφ w hw) kw h2,
      ← Module.End.mul_apply, (hk_comm w j _ h1).eq, Module.End.mul_apply]
  · by_cases e : w = w'
    · subst e
      have hK := Final.GLintComm E w n
      have hf := GlobalTheory.LGrp.mem_fixed.2 (hφ w hw)
      simp only [hk_apply, SatCompare.heckeVec_smul hK (tj_mem w _)]
      rw [← SatCompare.heckeVec_conv hK (tj_mem w _) (tj_mem w _) hf, ← SatCompare.heckeVec_conv hK (tj_mem w _) (tj_mem w _) hf,
        Final.HeckeCommGL E w n ℂ _ (tj_mem w j) _ (tj_mem w j'), smul_comm]
    · exact LinearMap.congr_fun (hk_comm w' j' _ fun g => (hk_comm w j _ (rw_comm e g)).symm).eq φ
