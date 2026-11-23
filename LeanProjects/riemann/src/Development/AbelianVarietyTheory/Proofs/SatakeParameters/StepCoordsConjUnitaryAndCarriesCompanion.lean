import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompanionLatticeEqPointLatticeOverCompanionStatement
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsSpan
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsApprox
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
open Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ConjCarry

theorem mem_hatL_latAd_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {N : ℕ}
    (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (Lb : Submodule (𝓞 E) (Fin N → E))
    (hfin : Module.Finite (𝓞 E) Lb) (hspan : Submodule.span E (Lb : Set (Fin N → E)) = ⊤)
    (u : Fin N → E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    u ∈ Formalism.L2.Herm.hatL (F := F) (latAd x Lb) ↔
      ((x⁻¹ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin N) (Fin N) _) *ᵥ u ∈ Formalism.L2.Herm.hatL (F := F) Lb := by
  have hrec := Formalism.UG.P.span_recovery_of_integral_adelic_approx Formalism.UG.P.integral_adele_approximation_holds F E (Fin N) Lb hfin hspan x u
  have hlat : latAd x Lb = Formalism.UG.CS.globLat x Lb := Submodule.span_eq (Formalism.UG.CS.globLat x Lb)
  rw [hlat]
  exact hrec

theorem carries_conj {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {N : ℕ}
    (C y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (M : Submodule (𝓞 E) (Fin N → E))
    (hfin : Module.Finite (𝓞 E) M) (hspan : Submodule.span E (M : Set (Fin N → E)) = ⊤) :
    Formalism.L2.Herm.Carries (F := F) (C * y * C⁻¹) (latAd C M) (latAd (C * y) M) := by
  intro x
  rw [mem_hatL_latAd_iff (C * y) M hfin hspan, mem_hatL_latAd_iff C M hfin hspan, Matrix.mulVec_mulVec, ← Units.val_mul]
  have e : C⁻¹ * (C * y * C⁻¹)⁻¹ = (C * y)⁻¹ := by group
  rw [e]

theorem cT_map_incl {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] {N : ℕ}
    (σ : E →ₐ[F] E) (M : Matrix (Fin N) (Fin N) E) :
    cT (sigR σ R) (M.map (inclE (F := F) R)) = (cT (σ : E →+* E) M).map (inclE (F := F) R) := by
  ext a b
  simp [cT, sigR, inclE]

end GlobalTheory.ConjCarry

namespace GlobalTheory.ConjCarry

theorem conj_mem_std {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    (σ : E →ₐ[F] E) (J : Matrix (Fin N) (Fin N) E) (co : GL (Fin N) E)
    (hco : cT (σ : E →+* E) co.1 * co.1 = J) (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (hy : y ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
    ratA F co * y * (ratA F co)⁻¹ ∈ UPts σ (1 : Matrix (Fin N) (Fin N) E) (FiniteAdeleRing (𝓞 F) F) := by
  set R := FiniteAdeleRing (𝓞 F) F
  set s := sigR σ R
  set Cm : Matrix (Fin N) (Fin N) (E ⊗[F] R) := ((ratA F co : GL (Fin N) (E ⊗[F] R)) : Matrix (Fin N) (Fin N) (E ⊗[F] R)) with hCm
  set Ci : Matrix (Fin N) (Fin N) (E ⊗[F] R) := (((ratA F co)⁻¹ : GL (Fin N) (E ⊗[F] R)) : Matrix (Fin N) (Fin N) (E ⊗[F] R)) with hCi
  set Y : Matrix (Fin N) (Fin N) (E ⊗[F] R) := (y : Matrix (Fin N) (Fin N) (E ⊗[F] R)) with hY
  have hCm' : Cm = co.1.map (inclE (F := F) R) := rfl
  have hJ : cT s Cm * Cm = J.map (inclE (F := F) R) := by
    rw [hCm', cT_map_incl, ← Matrix.map_mul, hco]
  have hy' : cT s Y * J.map (inclE (F := F) R) * Y = J.map (inclE (F := F) R) := hy
  have hCC : Cm * Ci = 1 := by
    rw [hCm, hCi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h1 : (1 : Matrix (Fin N) (Fin N) E).map (inclE (F := F) R) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  show cT s ((ratA F co * y * (ratA F co)⁻¹ : GL (Fin N) (E ⊗[F] R)) : Matrix (Fin N) (Fin N) (E ⊗[F] R)) *
      (1 : Matrix (Fin N) (Fin N) E).map (inclE (F := F) R) * ((ratA F co * y * (ratA F co)⁻¹ : GL (Fin N) (E ⊗[F] R)) : Matrix (Fin N) (Fin N) (E ⊗[F] R)) =
      (1 : Matrix (Fin N) (Fin N) E).map (inclE (F := F) R)
  rw [h1, Units.val_mul, Units.val_mul, ← hCm, ← hCi, ← hY, Matrix.mul_one, cT_mul, cT_mul]
  calc cT s Ci * (cT s Y * cT s Cm) * (Cm * Y * Ci)
      = cT s Ci * (cT s Y * (cT s Cm * Cm) * Y) * Ci := by simp only [Matrix.mul_assoc]
    _ = cT s Ci * (cT s Cm * Cm) * Ci := by rw [hJ, hy']
    _ = cT s (Cm * Ci) * (Cm * Ci) := by rw [cT_mul]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hCC, cT_one, Matrix.one_mul]

end GlobalTheory.ConjCarry

namespace GlobalTheory.ConjCarry

theorem exists_stdUnitaryPoint_det_eq_unitaryPoint_det {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    (σ : E →ₐ[F] E) (J : Matrix (Fin N) (Fin N) E) (co : GL (Fin N) E)
    (hco : cT (σ : E →+* E) co.1 * co.1 = J) (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (hy : y ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
    ∃ d : GL (Fin 1) (E ⊗[F] FiniteAdeleRing (𝓞 F) F), d ∈ UPts σ (1 : Matrix (Fin 1) (Fin 1) E) (FiniteAdeleRing (𝓞 F) F) ∧
      Matrix.GeneralLinearGroup.det d = Matrix.GeneralLinearGroup.det y := by
  set R := FiniteAdeleRing (𝓞 F) F
  set s := sigR σ R
  set u := Matrix.GeneralLinearGroup.det y with hu
  refine ⟨Units.map (Matrix.scalar (Fin 1) : E ⊗[F] R →+* Matrix (Fin 1) (Fin 1) (E ⊗[F] R)).toMonoidHom u, ?_, ?_⟩
  ·
    have hy' : cT s (y : Matrix (Fin N) (Fin N) (E ⊗[F] R)) * J.map (inclE (F := F) R) * (y : Matrix (Fin N) (Fin N) (E ⊗[F] R)) =
        J.map (inclE (F := F) R) := hy
    have hdet := congrArg Matrix.det hy'
    rw [Matrix.det_mul, Matrix.det_mul] at hdet
    have hcT : ∀ M : Matrix (Fin N) (Fin N) (E ⊗[F] R), (cT s M).det = s M.det := by
      intro M
      unfold cT
      rw [Matrix.det_transpose, RingHom.map_det]
      rfl
    have hJu : IsUnit (J.map (inclE (F := F) R)).det := by
      show IsUnit ((inclE (F := F) R).mapMatrix J).det
      rw [← RingHom.map_det]
      refine IsUnit.map _ ?_
      have hco' : IsUnit (co : Matrix (Fin N) (Fin N) E).det := by
        rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.isUnit _
      rw [← hco, Matrix.det_mul]
      refine IsUnit.mul ?_ hco'
      unfold cT
      rw [Matrix.det_transpose]
      show IsUnit (((σ : E →+* E)).mapMatrix (co : Matrix (Fin N) (Fin N) E)).det
      rw [← RingHom.map_det]
      exact hco'.map _
    rw [hcT] at hdet
    have hn : s (u : E ⊗[F] R) * (u : E ⊗[F] R) = 1 := by
      have h2 : (s (u : E ⊗[F] R) * (u : E ⊗[F] R)) * (J.map (inclE (F := F) R)).det = 1 * (J.map (inclE (F := F) R)).det := by
        calc (s (u : E ⊗[F] R) * (u : E ⊗[F] R)) * (J.map (inclE (F := F) R)).det
            = s (u : E ⊗[F] R) * (J.map (inclE (F := F) R)).det * (u : E ⊗[F] R) := by ring
          _ = (J.map (inclE (F := F) R)).det := by rw [hu, Matrix.GeneralLinearGroup.val_det_apply]; exact hdet
          _ = 1 * (J.map (inclE (F := F) R)).det := (one_mul _).symm
      exact hJu.mul_right_cancel h2
    have h1 : (1 : Matrix (Fin 1) (Fin 1) E).map (inclE (F := F) R) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
    show cT s _ * (1 : Matrix (Fin 1) (Fin 1) E).map (inclE (F := F) R) * _ = (1 : Matrix (Fin 1) (Fin 1) E).map (inclE (F := F) R)
    rw [h1, Matrix.mul_one]
    ext a b
    fin_cases a; fin_cases b
    simp [cT, Matrix.mul_apply, hn]
  · ext
    simp [Matrix.GeneralLinearGroup.det, Matrix.det_fin_one]

theorem det_conj {R : Type} [CommRing R] {N : ℕ} (C y : GL (Fin N) R) :
    Matrix.GeneralLinearGroup.det (C * y * C⁻¹) = Matrix.GeneralLinearGroup.det y := by
  rw [map_mul, map_mul, map_inv, mul_right_comm, mul_inv_cancel, one_mul]

end GlobalTheory.ConjCarry

namespace GlobalTheory.TwV

open GlobalTheory.ConjCarry in

theorem conj_crd_unitary_carries : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i (hi : i ≤ D.R.m) β (y : UA D i hi), ratA D.host.F (A.crd i hi) * y.1 * (ratA D.host.F (A.crd i hi))⁻¹ ∈ Formalism.L2.Herm.UstdAf D.sp.cm (D.R.N i) ∧ Formalism.L2.Herm.Carries (ratA D.host.F (A.crd i hi) * y.1 * (ratA D.host.F (A.crd i hi))⁻¹) (latCo D.sp (gramN D i hi) (A.crd i hi) a 1 ((St i hi).K β).lev.Lb) (latCo D.sp (gramN D i hi) (A.crd i hi) a y.1 ((St i hi).K β).lev.Lb) ∧ ∃ d : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, Matrix.GeneralLinearGroup.det d.1 = Matrix.GeneralLinearGroup.det y.1 ∧ Formalism.L2.Herm.IsDetOf D.sp.cm d (ratA D.host.F (A.crd i hi) * y.1 * (ratA D.host.F (A.crd i hi))⁻¹)) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPins hTie i hi β y
  have hco := hPins.crd_orth i hi
  have hLbf := ((St i hi).K β).lev.Lb_fin
  have hLbs := ((St i hi).K β).lev.Lb_span
  obtain ⟨e1, hCf, hCs⟩ := GlobalTheory.T.companion_lattice_eq_point_lattice_over_companion D i hi (A.crd i hi) hco a 1 _ hLbf hLbs
  have e2 := (GlobalTheory.T.companion_lattice_eq_point_lattice_over_companion D i hi (A.crd i hi) hco a y _ hLbf hLbs).1
  have e1' : latCo D.sp (gramN D i hi) (A.crd i hi) a 1 ((St i hi).K β).lev.Lb =
      latAd (ratA D.host.F (A.crd i hi)) (compan (sp := D.sp) (gramN D i hi) a ((St i hi).K β).lev.Lb) := by
    have := e1
    simp only [OneMemClass.coe_one, mul_one] at this
    exact this
  refine ⟨conj_mem_std (sigD D) (gramN D i hi) (A.crd i hi) hco y.1 y.2, ?_, ?_⟩
  · rw [e1', e2]
    exact carries_conj _ _ _ hCf hCs
  · obtain ⟨d, hd, hdd⟩ := exists_stdUnitaryPoint_det_eq_unitaryPoint_det (sigD D) (gramN D i hi) (A.crd i hi) hco y.1 y.2
    refine ⟨⟨d, hd⟩, hdd, ?_⟩
    exact hdd.trans (GlobalTheory.ConjCarry.det_conj (ratA D.host.F (A.crd i hi)) y.1).symm

end GlobalTheory.TwV
