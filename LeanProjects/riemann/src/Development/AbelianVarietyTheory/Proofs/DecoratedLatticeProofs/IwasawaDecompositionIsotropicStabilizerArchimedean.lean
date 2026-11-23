import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDoubledHermitianSpaceRealPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaIsotropicColumnsRingIsoComplexStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittHyperbolicIsotropicColumnsAtRealPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemWittStabilizerOfKeepsIsotropicRealPlacesStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

namespace GlobalTheory.Core.Rk.IwIso

open GlobalTheory.AdelicU Formalism.UG

theorem local_decomp {A : Type} [CommRing A] {n r : ℕ} (σ : A →+* A) (f : A →+* ℂ) (hf : Function.Bijective f)
    (hσ : ∀ x, f (σ x) = star (f x)) {J : Matrix (Fin n) (Fin n) A} (b : GL (Fin n) A) (ε : Fin n → Bool)
    (hb : Formalism.UG.cT σ b.1 * J * b.1 = Matrix.diagonal fun i => if ε i then 1 else -1)
    (X : Matrix (Fin n) (Fin r) A) (hX : Formalism.UG.cT σ X * J * X = 0) (g : GL (Fin n) A) (hg : g ∈ UJ σ J) :
    ∃ k ∈ UJ σ J, b⁻¹ * k * b ∈ UJ σ (1 : Matrix (Fin n) (Fin n) A) ∧
      ∃ β : Matrix (Fin r) (Fin r) A, (g * k⁻¹).1 * X = X * β :=
  GlobalTheory.T.iwasawa_isotropic_columns_ring_iso_complex σ f hf hσ b ε hb X hX g hg

theorem iso_arch {D : D7} {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) (w : InfinitePlace D.host.F) :
    (Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion D.sp.cm.sig) (Matrix.map d.jX (compInf D.host.F D.host.E w)) *
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR w.Completion T.gram : Matrix (Fin r) (Fin T.rank) _) *
      Matrix.map d.jX (compInf D.host.F D.host.E w) = 0 :=
  GlobalTheory.T.wittHyperbolic_isotropic_columns_at_real_place d w

theorem mem_stab_of_arch {D : D7} {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) (q : GA D T) (hfin : q ∈ GinfC T)
    (harch : ∀ w : InfinitePlace D.host.F, ∃ β : Matrix (Fin r) (Fin r) (TensorProduct D.host.F w.Completion D.host.E),
      (matHom _ D.sp.cm.sig T.gram (projArch D.sp.cm.sig T.gram w q)).1 * Matrix.map d.jX (compInf D.host.F D.host.E w) =
        Matrix.map d.jX (compInf D.host.F D.host.E w) * β) :
    q ∈ stab d :=
  GlobalTheory.T.mem_wittStabilizer_of_keeps_isotropic_real_places d q hfin harch

theorem glue {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (k : ∀ w : InfinitePlace F, GArch σ J w) :
    ∃ g : GAd σ J, (∀ w, projArch σ J w g = k w) ∧ projFin σ J g = 1 := by
  classical
  have key : ∀ s : Finset (InfinitePlace F), ∃ g : GAd σ J, (∀ w ∈ s, projArch σ J w g = k w) ∧
      (∀ w ∉ s, projArch σ J w g = 1) ∧ projFin σ J g = 1 := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by simp, fun _ _ => map_one _, map_one _⟩
    | insert a s ha ih =>
      obtain ⟨g, h1, h2, h3⟩ := ih
      refine ⟨g * embArch σ J a (k a), fun w hw => ?_, fun w hw => ?_, ?_⟩
      · rw [map_mul]
        rcases Finset.mem_insert.1 hw with rfl | hw
        · rw [h2 w ha, projArch_embArch_self, one_mul]
        · have hne : w ≠ a := fun e => ha (e ▸ hw)
          rw [h1 w hw, projArch_embArch_ne σ J hne, mul_one]
      · have hne : w ≠ a := fun e => hw (e ▸ Finset.mem_insert_self a s)
        rw [map_mul, h2 w (fun h => hw (Finset.mem_insert_of_mem h)), projArch_embArch_ne σ J hne, mul_one]
      · rw [map_mul, h3, projFin_embArch, mul_one]
  obtain ⟨g, h1, -, h3⟩ := key Finset.univ
  exact ⟨g, fun w => h1 w (Finset.mem_univ w), h3⟩

theorem local_at_arch {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hc : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (w : InfinitePlace F)
    (b : GL (Fin n) (TensorProduct F w.Completion E)) (ε : Fin n → Bool)
    (hb : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ) b.1 * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR w.Completion J * b.1 =
      Matrix.diagonal fun i => if ε i then 1 else -1)
    (X : Matrix (Fin n) (Fin r) (TensorProduct F w.Completion E))
    (hX : (Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ) X * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR w.Completion J :
      Matrix (Fin r) (Fin n) _) * X = 0)
    (g : GL (Fin n) (TensorProduct F w.Completion E))
    (hg : g ∈ UJ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR w.Completion J)) :
    ∃ k ∈ UJ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR w.Completion J),
      b⁻¹ * k * b ∈ UJ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ) (1 : Matrix (Fin n) (Fin n) _) ∧
      ∃ β : Matrix (Fin r) (Fin r) (TensorProduct F w.Completion E), (g * k⁻¹).1 * X = X * β := by
  obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
  exact local_decomp _ (infEmb τ) (infEmb_bijective hc τ) (fun x => (infEmb_sigR hc τ x).symm) b ε hb X hX g hg

theorem mem_stabArch_of {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (w : InfinitePlace F)
    (b : GL (Fin n) (TensorProduct F w.Completion E)) (g : GArch σ J w)
    (h : b⁻¹ * matHom _ σ J g * b ∈ UJ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ) 1) : g ∈ stabArch σ J w b := by
  show (MulAut.conj b⁻¹) (matHom _ σ J g) ∈ UJ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ) (1 : Matrix (Fin n) (Fin n) _)
  rwa [MulAut.conj_apply, inv_inv]

set_option maxHeartbeats 2000000 in

theorem iwasawa_stab_arch : ∀ (D : D7) (T T₀ : HSp D) (r : ℕ) (d : HypDec T T₀ r) (b : GL (Fin T.rank) (AE D)), IsMaj T b → ∀ y ∈ GinfC T, ∃ q ∈ stab d, ∃ k ∈ Kmax T b, q ∈ GinfC T ∧ y = q * k := by
  intro D T T₀ r d b hb y hy
  have hloc := fun w : InfinitePlace D.host.F => local_at_arch (isCMExt_host D) T.gram w _ (hb w).choose
    (hb w).choose_spec _ (iso_arch d w) (matHom _ D.sp.cm.sig T.gram (projArch D.sp.cm.sig T.gram w y))
    (projArch D.sp.cm.sig T.gram w y).2
  choose kk hk hk1 hβ using hloc
  obtain ⟨k, hkw, hkf⟩ := glue D.sp.cm.sig T.gram (fun w => ⟨kk w, hk w⟩)
  have hfk : finHom T k = 1 := by
    have e : finHom T k = GlobalTheory.AdelicU.matHom (Af D.host.F) D.sp.cm.sig T.gram (projFin D.sp.cm.sig T.gram k) := rfl
    rw [e, hkf, map_one]
  refine ⟨y * k⁻¹, ?_, k, ?_, ?_, by group⟩
  · refine mem_stab_of_arch d _ ?_ fun w => ?_
    · show finHom T (y * k⁻¹) = 1
      rw [map_mul, map_inv, hfk, inv_one, mul_one]
      exact hy
    · obtain ⟨β, h⟩ := hβ w
      refine ⟨β, ?_⟩
      rw [MonoidHom.map_mul (projArch D.sp.cm.sig T.gram w), MonoidHom.map_inv (projArch D.sp.cm.sig T.gram w), hkw w,
        MonoidHom.map_mul]
      exact h
  · rw [Kmax, levelAll, Subgroup.mem_inf, mem_levelOpen, Subgroup.mem_iInf]
    refine ⟨fun v => ?_, fun w => ?_⟩
    · rw [← projFinLoc_projFin, hkf, map_one]
      exact one_mem _
    · refine Subgroup.mem_comap.2 ?_
      have h3 := mem_stabArch_of D.sp.cm.sig T.gram w _ ⟨kk w, hk w⟩ (hk1 w)
      rw [← hkw w] at h3
      exact h3
  · show finHom T (y * k⁻¹) = 1
    rw [map_mul, map_inv, hfk, inv_one, mul_one]
    exact hy

end GlobalTheory.Core.Rk.IwIso
