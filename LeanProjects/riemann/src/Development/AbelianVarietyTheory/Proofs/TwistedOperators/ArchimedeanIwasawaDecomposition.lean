import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointRadical
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDoubledHermitianSpaceRealPlace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaDecompositionUnitaryIsotropicFlag

noncomputable section

namespace GlobalTheory.IwArchMin

open Matrix

section Alg

variable {A : Type} [CommRing A] {n : ℕ}

def toC (e : A ≃+* ℂ) (b : GL (Fin n) A) : (Fin n → A) →ₛₗ[(e : A →+* ℂ)] (Fin n → ℂ) where
  toFun y := fun r => e (((b⁻¹ : GL (Fin n) A).1 *ᵥ y) r)
  map_add' y z := by funext r; simp [Matrix.mulVec_add]
  map_smul' c y := by funext r; simp [Matrix.mulVec_smul]

theorem toC_apply (e : A ≃+* ℂ) (b : GL (Fin n) A) (y : Fin n → A) (r : Fin n) :
    toC e b y r = e (((b⁻¹ : GL (Fin n) A).1 *ᵥ y) r) := rfl

theorem inv_mul_val (b : GL (Fin n) A) : b.1 * (b⁻¹ : GL (Fin n) A).1 = 1 := by
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem toC_injective (e : A ≃+* ℂ) (b : GL (Fin n) A) : Function.Injective (toC e b) := by
  intro y z h
  have h1 : (b⁻¹ : GL (Fin n) A).1 *ᵥ y = (b⁻¹ : GL (Fin n) A).1 *ᵥ z :=
    funext fun r => e.injective (congrFun h r)
  have h2 := congrArg (fun v => b.1 *ᵥ v) h1
  simpa only [Matrix.mulVec_mulVec, inv_mul_val, Matrix.one_mulVec] using h2

theorem toC_mulVec (e : A ≃+* ℂ) (b M : GL (Fin n) A) (y : Fin n → A) :
    toC e b (M.1 *ᵥ y) =
      (Matrix.GeneralLinearGroup.map (e : A →+* ℂ) (b⁻¹ * M * b)).1 *ᵥ toC e b y := by
  funext r
  rw [toC_apply]
  have : (b⁻¹ : GL (Fin n) A).1 *ᵥ (M.1 *ᵥ y) = (b⁻¹ * M * b).1 *ᵥ ((b⁻¹ : GL (Fin n) A).1 *ᵥ y) := by
    simp only [Units.val_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc, inv_mul_val, Matrix.mul_one]
  rw [this]
  exact RingHom.map_mulVec (e : A →+* ℂ) _ _ r

theorem form_conj (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A) (b : GL (Fin n) A) (y z : Fin n → A) :
    (fun i => σ (((b⁻¹ : GL (Fin n) A).1 *ᵥ y) i)) ⬝ᵥ
      ((Formalism.UG.cT σ b.1 * J * b.1) *ᵥ ((b⁻¹ : GL (Fin n) A).1 *ᵥ z)) = (fun i => σ (y i)) ⬝ᵥ (J *ᵥ z) := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, inv_mul_val, Matrix.mul_one, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec]
  congr 1
  funext i
  rw [Formalism.UG.cT, Matrix.vecMul_transpose]
  have := RingHom.map_mulVec σ b.1 ((b⁻¹ : GL (Fin n) A).1 *ᵥ y) i
  rw [Matrix.mulVec_mulVec, inv_mul_val, Matrix.one_mulVec] at this
  exact this.symm

end Alg

end GlobalTheory.IwArchMin

namespace GlobalTheory.IwArchMin

open Matrix

section Alg2

variable {A : Type} [CommRing A] {n : ℕ}

theorem jm_eq_map (e : A ≃+* ℂ) (ε : Fin n → Bool) :
    Formalism.REAL.Jm ε = (Matrix.diagonal fun i => if ε i then (1 : A) else -1).map (e : A →+* ℂ) := by
  rw [Formalism.REAL.Jm, Matrix.diagonal_map (map_zero _)]
  congr 1; funext i; split_ifs <;> simp

theorem map_injective' (e : A ≃+* ℂ) {P Q : Matrix (Fin n) (Fin n) A} (h : P.map e = Q.map e) : P = Q := by
  ext i j; exact e.injective (congrFun (congrFun h i) j)

theorem exists_alg (σ : A →+* A) (e : A ≃+* ℂ) (he : ∀ x, e (σ x) = star (e x))
    (J : Matrix (Fin n) (Fin n) A) (b : GL (Fin n) A) (ε : Fin n → Bool)
    (S : Matrix (Fin n) (Fin n) A) (hSm : Formalism.REAL.Jm ε = S.map (e : A →+* ℂ)) (hb : Formalism.UG.cT σ b.1 * J * b.1 = S)
    {k : ℕ} (X : Fin (k + 1) → Submodule A (Fin n → A)) (h0 : X 0 = ⊥) (hX : Monotone X)
    (hiso : ∀ y ∈ X (Fin.last k), ∀ z ∈ X (Fin.last k), (fun i => σ (y i)) ⬝ᵥ (J *ᵥ z) = 0)
    (g : GL (Fin n) A) (hg : g ∈ Formalism.UG.UJ σ J) :
    ∃ K ∈ Formalism.UG.UJ σ J, b⁻¹ * K * b ∈ Formalism.UG.UJ σ 1 ∧ ∀ i, ∀ y ∈ X i, (g * K⁻¹).1 *ᵥ y ∈ X i := by
  have hJm := hSm
  let L := toC e b
  let W : Fin (k + 1) → Submodule ℂ (Fin n → ℂ) := fun i => (X i).map L
  have hWm : Monotone W := fun i j h => Submodule.map_mono (hX h)
  have hW : GlobalTheory.FlagMeas.IsIsoFlag ε
      (fun i : Fin k => Module.finrank ℂ (W i.succ) - Module.finrank ℂ (W i.castSucc)) W := by
    refine ⟨by simp [W, h0], hWm, fun i => ?_, ?_⟩
    · have := Submodule.finrank_mono (hWm (Fin.castSucc_le_succ i)); dsimp only; omega
    · rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
      have h1 : star (L y) = fun i => e (σ (((b⁻¹ : GL (Fin n) A).1 *ᵥ y) i)) := by
        funext i; simp [L, toC_apply, he]
      have h2 : Formalism.REAL.Jm ε *ᵥ L z = fun i => e ((S *ᵥ ((b⁻¹ : GL (Fin n) A).1 *ᵥ z)) i) := by
        funext i; rw [hJm]; exact (RingHom.map_mulVec (e : A →+* ℂ) S _ i).symm
      rw [h1, h2]
      have h3 := (RingHom.map_dotProduct (e : A →+* ℂ) (fun i => σ (((b⁻¹ : GL (Fin n) A).1 *ᵥ y) i))
        (S *ᵥ ((b⁻¹ : GL (Fin n) A).1 *ᵥ z))).symm
      refine h3.trans ?_
      rw [← hb, form_conj, hiso y hy z hz, map_zero]
  have mapForm : ∀ M : GL (Fin n) A, M ∈ Formalism.UG.UJ σ S →
      (Matrix.GeneralLinearGroup.map (e : A →+* ℂ) M).1ᴴ * Formalism.REAL.Jm ε *
        (Matrix.GeneralLinearGroup.map (e : A →+* ℂ) M).1 = Formalism.REAL.Jm ε := by
    intro M hM
    have hM' : Formalism.UG.cT σ M.1 * S * M.1 = S := hM
    change (M.1.map (e : A →+* ℂ))ᴴ * _ * M.1.map (e : A →+* ℂ) = _
    rw [← GlobalTheory.Core.Rk.IwArch.map_cT σ (e : A →+* ℂ) he, hJm, ← Matrix.map_mul, ← Matrix.map_mul, hM']
  have hg' : b⁻¹ * g * b ∈ Formalism.UG.UJ σ S := hb ▸ GlobalTheory.Core.Rk.IwArch.conj_mem_UJ σ b hg
  obtain ⟨kc, hkc, hstab⟩ := GlobalTheory.RealIwasawa.exists_stab_mul_compact hW
    ⟨Matrix.GeneralLinearGroup.map (e : A →+* ℂ) (b⁻¹ * g * b), mapForm _ hg'⟩
  set K0 := Matrix.GeneralLinearGroup.map (e.symm : ℂ →+* A) kc.1 with hK0
  have hK0e : Matrix.GeneralLinearGroup.map (e : A →+* ℂ) K0 = kc.1 := by
    ext i j; simp [K0]
  have hK0m : K0.1.map (e : A →+* ℂ) = kc.1.1 := congrArg Units.val hK0e
  have hkc2 : (kc.1.1)ᴴ * Formalism.REAL.Jm ε * kc.1.1 = Formalism.REAL.Jm ε := kc.2
  have hkc1 : (kc.1.1)ᴴ * kc.1.1 = 1 := hkc
  have hK0S : K0 ∈ Formalism.UG.UJ σ S := by
    show Formalism.UG.cT σ K0.1 * S * K0.1 = S
    apply map_injective' e
    have := hkc2
    rw [← hK0m, ← GlobalTheory.Core.Rk.IwArch.map_cT σ (e : A →+* ℂ) he, hJm, ← Matrix.map_mul, ← Matrix.map_mul] at this
    exact this
  have hK01 : K0 ∈ Formalism.UG.UJ σ 1 := by
    show Formalism.UG.cT σ K0.1 * 1 * K0.1 = 1
    apply map_injective' e
    have := hkc1
    rw [← hK0m, ← GlobalTheory.Core.Rk.IwArch.map_cT σ (e : A →+* ℂ) he, ← Matrix.map_mul] at this
    rw [Matrix.mul_one]
    refine this.trans ?_
    exact (Matrix.map_one _ (map_zero _) (map_one _)).symm
  refine ⟨b * K0 * b⁻¹, ?_, ?_, fun i y hy => ?_⟩
  · have := GlobalTheory.Core.Rk.IwArch.conj_mem_UJ σ b⁻¹ hK0S
    rw [inv_inv, ← hb, GlobalTheory.Core.Rk.IwArch.cT_inv_cancel] at this
    exact this
  · have : b⁻¹ * (b * K0 * b⁻¹) * b = K0 := by group
    rw [this]; exact hK01
  · have hy' : L y ∈ W i := Submodule.mem_map_of_mem hy
    have h4 := hstab i (L y) hy'
    have e1 : Formalism.MainNotions.S.uMat (⟨Matrix.GeneralLinearGroup.map (e : A →+* ℂ) (b⁻¹ * g * b), mapForm _ hg'⟩ * kc⁻¹ :
        Formalism.REAL.UJ ε) = (Matrix.GeneralLinearGroup.map (e : A →+* ℂ) (b⁻¹ * (g * (b * K0 * b⁻¹)⁻¹) * b)).1 := by
      have : b⁻¹ * (g * (b * K0 * b⁻¹)⁻¹) * b = (b⁻¹ * g * b) * K0⁻¹ := by group
      have e2 : Matrix.GeneralLinearGroup.map (e : A →+* ℂ) (b⁻¹ * (g * (b * K0 * b⁻¹)⁻¹) * b) =
          Matrix.GeneralLinearGroup.map (e : A →+* ℂ) (b⁻¹ * g * b) * kc.1⁻¹ := by
        rw [this, map_mul (Matrix.GeneralLinearGroup.map (e : A →+* ℂ)) (b⁻¹ * g * b) K0⁻¹, map_inv, hK0e]
      rw [e2]; rfl
    rw [e1, ← toC_mulVec] at h4
    obtain ⟨z, hz, hzL⟩ := Submodule.mem_map.1 h4
    rwa [toC_injective e b hzL] at hz

end Alg2

end GlobalTheory.IwArchMin

namespace GlobalTheory.IwArchMin

open scoped TensorProduct
open NumberField Matrix

section Place

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem exists_par_mul_stabArch (hc : Formalism.BasicNotions.CMData F E) (hcm : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E hc.sig)
    (V : Formalism.BasicNotions.HSpace E) (𝔉 : GlobalTheory.Cusp.IsoFlag V) (w : InfinitePlace F)
    (b : GL (Fin V.rank) (w.Completion ⊗[F] E)) (ε : Fin V.rank → Bool)
    (hb : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion hc.sig) b.1 * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR w.Completion V.gram * b.1 =
      Matrix.diagonal fun i => if ε i then 1 else -1)
    (g : GlobalTheory.AdelicU.GArch hc.sig V.gram w) :
    ∃ p ∈ 𝔉.par hc w.Completion, ∃ k ∈ GlobalTheory.AdelicU.stabArch hc.sig V.gram w b, g = p * k := by
  obtain ⟨τ⟩ : Nonempty (GlobalTheory.AdelicU.EmbOver E w) := inferInstance
  let e : w.Completion ⊗[F] E ≃+* ℂ := RingEquiv.ofBijective (GlobalTheory.AdelicU.infEmb τ) (GlobalTheory.AdelicU.infEmb_bijective hcm τ)
  have he : ∀ x, e (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion hc.sig x) = star (e x) := fun x =>
    (GlobalTheory.AdelicU.infEmb_sigR hcm τ x).symm
  let X : Fin (𝔉.k + 1) → Submodule (w.Completion ⊗[F] E) (Fin V.rank → w.Completion ⊗[F] E) :=
    fun i => GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.extSub V w.Completion (𝔉.X i)
  have h0 : X 0 = ⊥ := by simp [X, 𝔉.zero]
  have hX : Monotone X := fun i j h => GlobalTheory.Cusp.extSub_mono V w.Completion (𝔉.strictMono.monotone h)
  have hiso : ∀ y ∈ X (Fin.last 𝔉.k), ∀ z ∈ X (Fin.last 𝔉.k),
      (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion hc.sig (y i)) ⬝ᵥ
        (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR w.Completion V.gram *ᵥ z) = 0 := by
    intro y hy z hz
    have hz' := GlobalTheory.Cusp.extSub_mono V w.Completion 𝔉.iso hz
    have := (GlobalTheory.Cusp.mem_extSub_perp hc V).1 hz' y hy
    rw [GlobalTheory.Cusp.hR_eq] at this
    exact this
  obtain ⟨K, hK, hK1, hp⟩ := exists_alg (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion hc.sig) e he
    (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR w.Completion V.gram) b ε _ (jm_eq_map e ε) hb X h0 hX hiso
    (GlobalTheory.AdelicU.matHom w.Completion hc.sig V.gram g) g.2
  let kk : GlobalTheory.AdelicU.GArch hc.sig V.gram w := ⟨K, hK⟩
  refine ⟨g * kk⁻¹, ?_, kk, GlobalTheory.AdelicU.mem_stabArch.2 hK1, by group⟩
  refine GlobalTheory.Cusp.IsoFlag.mem_par.2 fun i => GlobalTheory.Cusp.mem_parab_iff_maps.2 fun y hy => ?_
  have := hp i y hy
  exact this

end Place

end GlobalTheory.IwArchMin

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

namespace GlobalTheory.IwArchMin

theorem iwasawa_minPar : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (L : _) (a : _), Φ.IsGood D.sp.cm L a →
    ∀ w (g : GArch D.sp.cm.sig V.gram w), ∃ p ∈ PArch Φ.flag0 w,
      ∃ k ∈ stabArch D.sp.cm.sig V.gram w (Formalism.UG.bc (compInf D.host.F D.host.E w) a), g = p * k := by
  intro D V Φ L a h w g
  obtain ⟨ε, hε⟩ := h.2.2.2.1 w
  exact exists_par_mul_stabArch D.sp.cm (isCMExt_host D) _ Φ.flag0 w _ ε hε g

end GlobalTheory.IwArchMin
