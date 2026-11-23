import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GridTestLatticeLargestSlopeBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteClPlusAndExistsCoords

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV Formalism.UG Formalism.IndefR
open GlobalTheory.ChiGrid GlobalTheory.TestLat GlobalTheory.CoefModel
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder

namespace GlobalTheory.FunObj.TestLatModel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc}

theorem finE_rat (γ : GQ (Xp G)) (γE : UR D.sp.cm (Xp G).gram) (h : Bridge.IsRatMat (Xp G) γ γE.1) :
    Formalism.IndefR.Lev.finE (Xp G) γ = ratIn G γE := by
  have h' : matHom (Xp G) γ = bc (incA D) γE.1 := h
  apply Units.ext
  show ((matHom (Xp G) γ).1.map _).map _ = γE.1.1.map _
  rw [h']
  ext i j
  rfl

theorem map_rhoVr {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (lam : D.what₂.Tau → DomWeight V.rank) (γ : GQ V)
    (γE : GL (Fin V.rank) D.host.E) (h : Bridge.IsRatMat V γ γE) (x : GA D V) (v : VV D.what₂.LL lam) :
    rhoK lam (invTrK (realGL θ V (γ.1 * x)⁻¹)) (mapVV D.what₂.embLL lam (rhoVr (labLL D) lam γE v)) =
      rhoK lam (invTrK (realGL θ V x⁻¹)) (mapVV D.what₂.embLL lam v) := by
  have hlab : ∀ τ x, D.what₂.embLL (labLL D τ x) = tauE D τ x := fun τ x =>
    DFunLike.congr_fun (GlobalTheory.ThetaFiresProbe.labE_fixed τ) x
  have e : (fun τ => Formalism.UG.bc D.what₂.embLL (invTrK (embGL (labLL D) γE) τ)) = invTrK (realGL θ V γ) := by
    funext τ
    apply Units.ext
    rw [bc_coe, invTrK_coe, invTrK_coe, realGL_rat hθ V γ γE h, embGL_inv, ← map_inv, embGL_coe, bc_coe]
    ext a b
    exact hlab _ _
  have e2 : (γ.1 * x)⁻¹ * γ.1 = x⁻¹ := by group
  show rhoK _ _ (mapVV _ _ (rhoK lam (invTrK (embGL (labLL D) γE)) _)) = _
  rw [mapVV_rhoK, e, ← Module.End.mul_apply, ← map_mul (rhoK lam), ← map_mul invTrK, ← map_mul (realGL θ V), e2]

theorem scal_left {θ : InfFam D} (hθ : IsInfFam θ) (ξ : Module.Dual ℂ (VV ℂ (LaP G))) (Ψ : GLf G → WtSp G)
    (hΨ : ∀ γ g, Ψ (ratIn G γ * g) = rhoW G γ (Ψ g)) (γ : GQ (Xp G)) (γE : UR D.sp.cm (Xp G).gram)
    (h : Bridge.IsRatMat (Xp G) γ γE.1) (x : GA D (Xp G)) : scal θ ξ Ψ (γ.1 * x) = scal θ ξ Ψ x := by
  have e : Ψ (Formalism.IndefR.Lev.finE (Xp G) (γ.1 * x)) = rhoVr (labLL D) (LaP G) γE.1 (Ψ (Formalism.IndefR.Lev.finE (Xp G) x)) := by
    rw [map_mul (Formalism.IndefR.Lev.finE (Xp G)), finE_rat γ γE h, hΨ]
    rfl
  unfold scal
  rw [e, map_rhoVr hθ (Xp G) (LaP G) γ γE.1 h]

theorem pair_rhoW (γ : UR D.sp.cm (Xp G).gram) (x y : WtSp G) :
    pairK (LaP G) (gramKd (emb D) (Xp G).gram) (rhoW G γ x) (rhoW G γ y) = pairK (LaP G) (gramKd (emb D) (Xp G).gram) x y := by
  refine pairInv D.what₂.LL _ _ (LaP G) _ (invTrK (embGL (emb D) γ.1)) (fun τ => ?_) x y
  have h0 : cT (D.sp.cm.sig : D.host.E →+* D.host.E) γ.1.1 * (Xp G).gram * γ.1.1 = (Xp G).gram := γ.2
  have hg : (γ.1.1.map (emb D τ))ᴴ * (Xp G).gram.map (emb D τ) * γ.1.1.map (emb D τ) = (Xp G).gram.map (emb D τ) := by
    have h1 := congrArg (fun M => M.map (emb D τ)) h0
    simp only [Matrix.map_mul] at h1
    have h2 : (γ.1.1.map (emb D τ))ᴴ = (cT (D.sp.cm.sig : D.host.E →+* D.host.E) γ.1.1).map (emb D τ) := by
      ext i j
      exact star_emb τ _
    rw [h2, h1]
  have h := congrArg (fun M => (M⁻¹)ᵀ) hg
  simp only [Matrix.mul_inv_rev, Matrix.transpose_mul] at h
  rw [invTrK_coe, gramKd, Matrix.coe_units_inv, embGL_coe]
  have h3 : ∀ A : Matrix (Fin (Xp G).rank) (Fin (Xp G).rank) D.what₂.LL, A⁻¹ᵀᴴ = Aᴴ⁻¹ᵀ := fun A => by
    rw [← Matrix.conjTranspose_nonsing_inv]; rfl
  rw [h3, h]

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
  (Λ : Submodule (𝓞 E) (Fin n → E))

theorem mem_globLat_rat (γ : GL (Fin n) E) (g : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (x : Fin n → E) :
    γ.1 *ᵥ x ∈ CS.globLat (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * g) Λ ↔ x ∈ CS.globLat g Λ := by
  have e : (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((γ.1 *ᵥ x) i)) =
      (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ).1 *ᵥ fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i) := by
    funext i
    exact RingHom.map_mulVec _ _ _ i
  simp only [CS.globLat, ← SetLike.mem_coe, Submodule.coe_set_mk, AddSubmonoid.coe_set_mk, AddSubsemigroup.coe_set_mk, Set.mem_ofPred_eq]
  rw [e, mulVec_mulVec, ← Units.val_mul, _root_.mul_inv_rev, inv_mul_cancel_right]

theorem globLat_mul [StarRing E] (g k : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (hk : k ∈ Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := F) Λ)) : CS.globLat (g * k) Λ = CS.globLat g Λ := by
  ext x
  simp only [CS.globLat, ← SetLike.mem_coe, Submodule.coe_set_mk, AddSubmonoid.coe_set_mk, AddSubsemigroup.coe_set_mk, Set.mem_ofPred_eq]
  rw [_root_.mul_inv_rev, Units.val_mul, ← mulVec_mulVec]
  exact ((inv_mem hk : k⁻¹ ∈ _) _).symm

end Gen

theorem mem_latOf_rat (γ : UR D.sp.cm (Xp G).gram) (g : GLf G) (x : Fin (Xp G).rank → D.host.E) :
    γ.1.1 *ᵥ x ∈ latOf G (ratIn G γ * g) ↔ x ∈ latOf G g := mem_globLat_rat _ γ.1 g x

theorem latOf_mul (g : GLf G) {k : GLf G} (hk : k ∈ G.Kplus) : latOf G (g * k) = latOf G g :=
  globLat_mul _ g k hk.2.1

theorem psi_ne_zero (rp : ClassReps G) (hN : rp.Neat) {n : ℕ} (e : Fin n ≃ TestIx G × VVIdx (LaP G)) (a : Fin n) :
    psi rp e a (rp.x (e a).1.2) ≠ 0 := by
  rw [psi, rp.gridClassReps_delta_apply_rep hN, if_pos rfl]
  exact (bVV D.what₂.LL (LaP G)).ne_zero _

theorem isTestLat_unique {rp : ClassReps G} {n : ℕ} {e : Fin n ≃ TestIx G × VVIdx (LaP G)} {X X' M M'}
    (h : IsTestLat G rp n e X M) (h' : IsTestLat G rp n e X' M') : M = M' := h.2.trans h'.2.symm

theorem exists_testLat (h : (L.ΛY 0).FG) (rp : ClassReps G) : ∃ n e X M, 0 < n ∧ IsTestLat G rp n e X M := by
  obtain ⟨n, ⟨e⟩⟩ := exists_coords G h
  obtain ⟨X, M, hM⟩ := exists_isTestLat G rp n e
  obtain ⟨i⟩ := SlopeModel.nonempty_idx (LaP G)
  exact ⟨n, e, X, M, (e.symm (⟨fun _ => default, Quotient.mk'' 1⟩, i)).pos, hM⟩

end GlobalTheory.FunObj.TestLatModel

end
