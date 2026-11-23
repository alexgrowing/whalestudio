import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield

noncomputable section

namespace GlobalTheory.Mem

open Formalism.BasicNotions NumberField IsDedekindDomain

structure Cols0 (B : Pre) where
  mem : ∀ u : B.Word, Member B.R (Tau B.R) (B.hcW u)
  A_T : ∀ u, (mem u).A.T = B.T u
  A_duStar : ∀ u, (mem u).A.duStar = B.duStar u
  A_Dstar : ∀ u, (mem u).A.Dstar = B.Dstar
  A_GamP : ∀ u, (mem u).A.GamP = B.GamP
  clsLat : letI := B.host.cmStar; ∀ u i, (mem u).C.cls i → Submodule (𝓞 B.host.E) (B.sp.X i).V
  clsLat_lat : letI := B.host.cmStar; ∀ u i c, Submodule.IsLattice B.host.E (clsLat u i c)

  Tup : Type
  mu0 : Tup
  muStar : Tup
  muStar' : Tup

  chTw : ∀ u, Tup → ColumnChain B.R (Tau B.R) (B.hcW u)
  memberColumns_twistedChain_base : ∀ u, chTw u mu0 = (mem u).C
  e0Tw : ∀ u μ, ((mem u).C.cls 0 → (mem u).C.Y 0 → ℂ) ≃ₗ[ℂ] ((chTw u μ).cls 0 → (chTw u μ).Y 0 → ℂ)
  PTw : ∀ u μ, PeriodMap B.R (chTw u μ)

  Dt : Type
  [instDt : CommGroup Dt]
  detCls : ∀ u i, (mem u).C.cls i → Dt
  muTil : ℕ → Dt →* ℂˣ
  chiD : Dt →* ℂˣ
  UO : Subgroup Dt
  chiD_UO : ∀ x ∈ UO, chiD x = 1
  e1Dt : letI := B.host.cmStar; unitary B.host.E →* Dt
  rest_detCharacter_on_unitary_eq : letI := B.host.cmStar; ∀ z : unitary B.host.E,
    ((chiD (e1Dt z) : ℂˣ) : ℂ) = ∏ τ : (Tau B.R), (B.host.emb ((τ : B.R.Psi) : B.R.GG) (z : B.host.E))⁻¹
  relDet : letI := B.host.cmStar; ∀ N, SDLat B.host.E N → SDLat B.host.E N → Dt ⧸ UO
  relDet_self : letI := B.host.cmStar; ∀ N L, relDet N L L = 1
  relDet_mul : letI := B.host.cmStar; ∀ N L L' L'', relDet N L L' * relDet N L' L'' = relDet N L L''
  relDet_smul : letI := B.host.cmStar; ∀ N (L L' : SDLat B.host.E N) (γ : Matrix.unitaryGroup (Fin N) B.host.E),
    L'.1 = SDLat.smulLat (γ : Matrix (Fin N) (Fin N) B.host.E) L.1 → relDet N L L' = QuotientGroup.mk (e1Dt ⟨(γ : Matrix (Fin N) (Fin N) B.host.E).det, Matrix.det_of_mem_unitary γ.2⟩)
  rhoDet_eq_inv_muTilde_chiD_pow : ∀ u i (c : (mem u).C.cls i),
    (mem u).C.rhoDet i c = (((muTil (i + 1) (detCls u i c))⁻¹ *
      (chiD (detCls u i c)) ^ (-(((B.R.N (i + 1)) / 2 : ℕ) : ℤ)) : ℂˣ) : ℂ)
  rhoDetPrime_eq_muTilde_mul_chi_pow : ∀ u i (c : (mem u).C.cls (i + 1)),
    (mem u).C.rhoDet' i c = ((muTil (i + 1) (detCls u (i + 1) c) *
      (chiD (detCls u (i + 1) c)) ^ ((((B.R.N i) / 2 : ℕ) : ℤ)) : ℂˣ) : ℂ)

attribute [instance] Cols0.instDt

structure Cols (B : Base) extends Cols0 B.toPre where
  fm : ∀ u, MemberForms B.LL B.embLL B.places (Tau B.R) (B.hcW u) (mem u).C (mem u).A (mem u).P

end GlobalTheory.Mem

end
