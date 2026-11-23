import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Formalism.LocalToGlobal.Columns.XtPhiTopGCongr
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TwistEmptyOfChartsEx
import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocBases
import Formalism.LocalToGlobal.LatticeGeometry.GeometryDefinitions.PNeatB
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryCompletionMapsDualLattices
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsSpan
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemLatSLatAdIff
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col GlobalTheory.TwU Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.MemDual

theorem prV_inclE {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (e : E) :
    prV (E := E) v (inclE (F := F) (FiniteAdeleRing (𝓞 F) F) e) = inclE (F := F) (v.adicCompletion F) e := by
  simp [prV, inclE]

theorem prV_sigR {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (x : E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    prV (E := E) v (sigR σ (FiniteAdeleRing (𝓞 F) F) x) = sigR σ (v.adicCompletion F) (prV (E := E) v x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | tmul a b => simp [prV, sigR]

theorem bc_prV_mem_UPts {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))
    {k : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (hk : k ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
    bc (prV (E := E) v) k ∈ UPts σ J (v.adicCompletion F) := by
  have hg' : cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) (k : Matrix (Fin n) (Fin n) _) *
      J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) * (k : Matrix (Fin n) (Fin n) _) =
      J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) := hk
  change cT (sigR σ (v.adicCompletion F)) ((k : Matrix (Fin n) (Fin n) _).map (prV (E := E) v)) *
      J.map (inclE (F := F) (v.adicCompletion F)) * ((k : Matrix (Fin n) (Fin n) _).map (prV (E := E) v)) =
      J.map (inclE (F := F) (v.adicCompletion F))
  have h1 : cT (sigR σ (v.adicCompletion F)) ((k : Matrix (Fin n) (Fin n) _).map (prV (E := E) v)) =
      (cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) (k : Matrix (Fin n) (Fin n) _)).map (prV (E := E) v) := by
    ext i j
    simp [cT, prV_sigR]
  have hJ' : (J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F))).map (prV (E := E) v) =
      J.map (inclE (F := F) (v.adicCompletion F)) := by
    ext i j
    simp [prV_inclE]
  rw [h1, ← hJ', ← Matrix.map_mul, ← Matrix.map_mul, hg']

theorem pullV_ratA_mul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    (c : GL (Fin N) E) (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (y : Fin N → E) :
    pullV (F := F) (ratA F c * x) ((c : Matrix (Fin N) (Fin N) E) *ᵥ y) =
      ((x⁻¹ : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) *ᵥ fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (y i) := by
  unfold pullV
  rw [_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]
  congr 1
  have hc : (((ratA F c)⁻¹ : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) =
      ((c⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E).map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) := by
    rw [← map_inv]; rfl
  rw [hc]
  ext i
  have := RingHom.map_mulVec (inclE (F := F) (FiniteAdeleRing (𝓞 F) F))
    ((c⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) ((c : Matrix (Fin N) (Fin N) E) *ᵥ y) i
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at this
  rw [this]; rfl

end GlobalTheory.MemDual

namespace GlobalTheory.MemDual

theorem mem_latS_dual_of_latCo : ∀ {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E), IsUnit J.det → ∀ (c : GL (Fin N) E) (a : 𝓞 E)
    (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)), x ∈ UPts sp.cm.sig J (FiniteAdeleRing (𝓞 F) F) →
    ∀ (Lb : Submodule (𝓞 E) (Fin N → E)), Module.Finite (𝓞 E) Lb → Submodule.span E (Lb : Set (Fin N → E)) = ⊤ →
    (∀ y ∈ Lb, y ∈ dualSet (sp.cm.sig : E →+* E) J Lb) → ∀ (v : HeightOneSpectrum (𝓞 F)) (y : Fin N → E),
    y ∈ latCo sp J c a x Lb →
    (fun l => prV (E := E) v (pullV (F := F) (ratA F c * x) y l)) ∈
      latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) J Lb)) := by
  intro R F E _ _ _ _ _ _ sp N J hJ c a x hx Lb hfin hspan hdual v y hy
  obtain ⟨y', hy', rfl⟩ := hy
  set σ : E →ₐ[F] E := sp.cm.sig with hσ
  set Λ := latAd x Lb with hΛ
  set xv := bc (prV (E := E) v) x with hxv
  have hLb : Submodule.IsLattice E Lb := ⟨Module.Finite.iff_fg.mp hfin, hspan⟩
  have hLam : Submodule.IsLattice E Λ := by
    have hlat : Formalism.L2.PairingIndexBounds.F.latAd x Lb = Formalism.UG.CS.globLat x Lb := Submodule.span_eq (Formalism.UG.CS.globLat x Lb)
    rw [hΛ, hlat]
    exact Formalism.UG.P.csGlob_lattice Lb hfin hspan x
  have hxU : xv ∈ UPts σ J (v.adicCompletion F) := bc_prV_mem_UPts σ J v hx
  have hcarry := GlobalTheory.LocCarry.mem_latS_latAd_iff x Lb hfin hspan v

  have hpull : (fun l => prV (E := E) v (pullV (F := F) (ratA F c * x) ((c : Matrix (Fin N) (Fin N) E) *ᵥ y') l)) =
      ((xv⁻¹ : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) *ᵥ fun i => inclE (F := F) (v.adicCompletion F) (y' i) := by
    rw [pullV_ratA_mul, GlobalTheory.LocCarry.prV_mulVec, hxv, GlobalTheory.LocCarry.coe_bc_inv]
    congr 1
  show (fun l => prV (E := E) v (pullV (F := F) (ratA F c * x) ((c : Matrix (Fin N) (Fin N) E) *ᵥ y') l)) ∈ _
  rw [hpull]

  have hsub : compan (sp := sp) J a Λ ≤ Λ ⊔ dualL (σ : E →+* E) J Λ :=
    sup_le_sup_left (Submodule.smul_le_right) _
  obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp (hsub hy')
  have hadd : (fun i => inclE (F := F) (v.adicCompletion F) ((p + q) i)) =
      (fun i => inclE (F := F) (v.adicCompletion F) (p i)) + fun i => inclE (F := F) (v.adicCompletion F) (q i) := by
    ext i; simp
  rw [hadd, Matrix.mulVec_add]
  have hmono : latS (F := F) (v.adicCompletion F) (intV E v) Lb ≤
      latS (F := F) (v.adicCompletion F) (intV E v) (dualL (σ : E →+* E) J Lb) :=
    Submodule.span_mono (Set.image_mono fun z hz => Submodule.subset_span (hdual z hz))
  refine add_mem ?_ ?_
  · exact hmono ((hcarry _).1 (Submodule.subset_span ⟨p, hp, rfl⟩))
  · exact (GlobalTheory.DualCompletion.dual_move F E σ N J v Λ Lb xv hJ hLam hLb hxU hcarry _).1
      (Submodule.subset_span ⟨q, hq, rfl⟩)

end GlobalTheory.MemDual
