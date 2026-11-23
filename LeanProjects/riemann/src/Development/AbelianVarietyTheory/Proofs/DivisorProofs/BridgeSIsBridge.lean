import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFundamentalDomainMulRight
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.AdelicIsomorphismStatement
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.UnitaryPointsRankZeroSubsingleton

noncomputable section

namespace GlobalTheory.HCFinU

open NumberField Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def starOf (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) : StarRing E where
  star := σ
  star_involutive := hσ
  star_mul x y := by simp only [map_mul, mul_comm]
  star_add := map_add σ

def mkI (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x)
    (cm : @Formalism.BasicNotions.CMData F E _ _ _ _ (starOf σ hσ) _) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (hdet : J.det ≠ 0) (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG)
    (hspan : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (hdual : ∀ x : Fin n → E, x ∈ L ↔
      ∀ y ∈ L, Formalism.UG.hform (σ : E →+* E) J y x ∈ (algebraMap (𝓞 E) E).range)
    (ε : InfinitePlace F → Fin n → Bool) (φ : InfinitePlace F → (E →+* ℂ))
    (hφ : ∀ v (a : F), φ v (algebraMap F E a) = v.embedding a) (P : InfinitePlace F → Matrix (Fin n) (Fin n) ℂ)
    (hPu : ∀ v, IsUnit (P v)) (hP : ∀ v, (P v)ᴴ * J.map (φ v) * P v = Formalism.REAL.Jm (ε v)) :
    Formalism.MainNotions.S.AutInst :=
  letI := starOf σ hσ
  { F := F, E := E, cm := cm, n := n, J := J
    J_herm := Matrix.ext fun i j => hJ i j
    J_det := hdet
    L := L
    L_span := hspan
    L_fg := hfg
    L_dual := hdual
    ε := ε
    φ := φ
    φ_over := hφ
    P := P
    P_unit := hPu
    P_spec := hP
    topf := (Formalism.MainNotions.S.Inh.aut_HTop_holds cm J L hfg hspan).choose
    topf_group := (Formalism.MainNotions.S.Inh.aut_HTop_holds cm J L hfg hspan).choose_spec.1
    topf_open := (Formalism.MainNotions.S.Inh.aut_HTop_holds cm J L hfg hspan).choose_spec.2.1
    topf_basis := (Formalism.MainNotions.S.Inh.aut_HTop_holds cm J L hfg hspan).choose_spec.2.2 }

theorem mkI_sig (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x)
    (cm : @Formalism.BasicNotions.CMData F E _ _ _ _ (starOf σ hσ) _) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (hdet : J.det ≠ 0) (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG)
    (hspan : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (hdual : ∀ x : Fin n → E, x ∈ L ↔
      ∀ y ∈ L, Formalism.UG.hform (σ : E →+* E) J y x ∈ (algebraMap (𝓞 E) E).range)
    (ε : InfinitePlace F → Fin n → Bool) (φ : InfinitePlace F → (E →+* ℂ))
    (hφ : ∀ v (a : F), φ v (algebraMap F E a) = v.embedding a) (P : InfinitePlace F → Matrix (Fin n) (Fin n) ℂ)
    (hPu : ∀ v, IsUnit (P v)) (hP : ∀ v, (P v)ᴴ * J.map (φ v) * P v = Formalism.REAL.Jm (ε v)) :
    σ = (mkI σ hσ cm J hJ hdet L hfg hspan hdual ε φ hφ P hPu hP).cm.sig :=
  AlgHom.ext fun _ => rfl

def bridgeS (I : Formalism.MainNotions.S.AutInst) (s : I.E →ₐ[I.F] I.E) (hs : s = I.cm.sig) :
    I.GA ≃ₜ* GlobalTheory.AdelicU.GAd s I.J := by
  subst hs
  exact Formalism.L2.SG.AdBridge.toHA I (Formalism.L2.SG.Closed.AdBridgeIso_holds I)

theorem bridgeS_isBridge (I : Formalism.MainNotions.S.AutInst) :
    Formalism.L2.SG.AdBridge.IsBridge I (bridgeS I I.cm.sig rfl) :=
  Formalism.L2.SG.AdBridge.toHA_isBridge I _

theorem bridgeS_rat (I : Formalism.MainNotions.S.AutInst) (s : I.E →ₐ[I.F] I.E) (hs : s = I.cm.sig) :
    ∀ γ ∈ I.GFset, bridgeS I s hs γ ∈ GlobalTheory.AdelicU.ratPts s I.J := by
  subst hs
  intro γ hγ
  have h := Formalism.L2.SG.Closed.AdBridgeGF_holds I (bridgeS I _ rfl) (bridgeS_isBridge I)
  have h2 : bridgeS I _ rfl γ ∈ Formalism.L2.SG.AdBridge.ratHA I := h ▸ Set.mem_image_of_mem _ hγ
  exact Subgroup.mem_subgroupOf.2 h2

end GlobalTheory.HCFinU

end
