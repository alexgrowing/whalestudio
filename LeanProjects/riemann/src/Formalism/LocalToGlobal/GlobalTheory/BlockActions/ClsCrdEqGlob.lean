import Formalism.LocalToGlobal.GlobalTheory.BlockActions.SelfDualPHolds
import Formalism.LocalToGlobal.GlobalTheory.BlockActions.ClassMapPropertiesOfSymmetricForms
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ColSpanMap

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.L2.Forms NumberField Formalism.UG Matrix
open scoped TensorProduct
open IsDedekindDomain

theorem isLat_dlN (D : D7) (i : ℕ) (hi : i ≤ D.R.m) (M : Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)) (hM : Comp.IsLat M) :
    Comp.IsLat (Comp.dl (sigD D) (gramN D i hi) M) := by
  have hL : Submodule.IsLattice D.host.E M := ⟨Module.Finite.iff_fg.1 hM.1, hM.2⟩
  obtain ⟨d, hd, hle⟩ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.dual_le_bnd (sigD D : D.host.E →+* D.host.E) (gramN D i hi)
    (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D i hi) M hL
  exact ⟨Module.Finite.iff_fg.2 (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.fg_of_le_bnd hd hle),
    Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.dual_span (sigD D : D.host.E →+* D.host.E) (gramN D i hi) M hL⟩

variable {D : D7} {u : D.what₂.Word}

theorem clsCrd_finite (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) :
    Module.Finite (𝓞 D.host.E) (clsCrd D u i hi c) := by
  let _ := D.host.cmStar
  rw [Module.Finite.iff_fg]
  exact (D.clsLat_lat u i c).fg.map _

theorem clsCrd_eq_glob {i : ℕ} {hi : i ≤ D.R.m} (K : ClsTied u i hi) (c : (D.mem u).C.cls i) :
    clsCrd D u i hi c = Formalism.UG.CS.globLat (K.y c).1 K.lev.Lb := by
  ext x
  constructor
  · intro hx
    exact (K.y_lat c _).1 (latS_of_mem _ x hx)
  · intro hx
    exact latLocGlob _ _ _ _ (clsCrd_finite i hi c) x ((K.y_lat c _).2 hx)

theorem ld_eq_glob {i : ℕ} {hi : i ≤ D.R.m} (K : ClsTied u i hi) (c : (D.mem u).C.cls i) :
    Ld D u i hi c = Formalism.UG.CS.globLat (K.y c).1 (Comp.dl (sigD D) (gramN D i hi) K.lev.Lb) := by
  have hLb : Comp.IsLat K.lev.Lb := ⟨K.lev.Lb_fin, K.lev.Lb_span⟩
  show Comp.dl (sigD D) (gramN D i hi) (clsCrd D u i hi c) = _
  rw [clsCrd_eq_glob K c, Comp.glob_dl (sigD D) (gramN D i hi) (isLat_dlN D i hi) hLb _ (K.y c).2]

section Gen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem bc_val' {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (g : GL (Fin n) A) :
    ((bc φ g : GL (Fin n) B) : Matrix (Fin n) (Fin n) B) = (g : Matrix (Fin n) (Fin n) A).map φ := rfl

theorem bc_incl_w (w : HeightOneSpectrum (𝓞 F)) (γ : GL (Fin n) E) :
    bc (inclE (F := F) (w.adicCompletion F)) γ = bc (prV (E := E) w) (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ) := by
  apply Units.ext
  rw [bc_val', bc_val', bc_val', Matrix.map_map, ← RingHom.coe_comp, Formalism.L2.G.Cmp.prV_incl]

theorem locDual (w : HeightOneSpectrum (𝓞 F)) (g : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (Λ : Submodule (𝓞 E) (Fin n → E))
    (z : Fin n → E) (hz : z ∈ Formalism.UG.CS.globLat g Λ) :
    ((bc (prV (E := E) w) g)⁻¹ : GL (Fin n) (E ⊗[F] w.adicCompletion F)).1 *ᵥ (fun a => inclE (F := F) (w.adicCompletion F) (z a)) ∈
      latS (F := F) (w.adicCompletion F) (intV E w) Λ := by
  have h1 : ((g⁻¹ : GL (Fin n) _) : Matrix _ _ _) *ᵥ (fun a => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (z a)) ∈
      latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ := hz
  have h2 := latS_prV w _ _ h1
  have e : ((bc (prV (E := E) w) g)⁻¹ : GL (Fin n) (E ⊗[F] w.adicCompletion F)).1 *ᵥ
      (fun a => inclE (F := F) (w.adicCompletion F) (z a)) =
      fun j => prV (E := E) w ((((g⁻¹ : GL (Fin n) _) : Matrix _ _ _) *ᵥ
        (fun a => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (z a))) j) := by
    rw [← map_inv, bc_val']
    funext j
    rw [RingHom.map_mulVec]
    have hc : (⇑(prV (E := E) w) ∘ fun a => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (z a)) =
        fun a => inclE (F := F) (w.adicCompletion F) (z a) := by
      funext a
      exact RingHom.congr_fun (Formalism.L2.G.Cmp.prV_incl (E := E) w) (z a)
    rw [hc]
  rw [e]
  exact h2

theorem conj_step (w : HeightOneSpectrum (𝓞 F)) (Y κ : GL (Fin n) (E ⊗[F] w.adicCompletion F)) (γ : GL (Fin n) E)
    (h : bc (inclE (F := F) (w.adicCompletion F)) γ = Y * κ * Y⁻¹) (x : Fin n → E) :
    (Y⁻¹).val *ᵥ (fun a => inclE (F := F) (w.adicCompletion F) ((γ.val *ᵥ x) a)) =
      κ.val *ᵥ ((Y⁻¹).val *ᵥ fun a => inclE (F := F) (w.adicCompletion F) (x a)) := by
  have em : (fun a => inclE (F := F) (w.adicCompletion F) ((γ.val *ᵥ x) a)) =
      (bc (inclE (F := F) (w.adicCompletion F)) γ).val *ᵥ
        (fun a => inclE (F := F) (w.adicCompletion F) (x a)) := by
    funext a
    rw [bc_val']
    exact RingHom.map_mulVec _ _ _ a
  rw [em, h, mulVec_mulVec, mulVec_mulVec, ← Units.val_mul, ← Units.val_mul]
  congr 2
  group

theorem conj_stepA (w : HeightOneSpectrum (𝓞 F)) (Y κ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (γ : GL (Fin n) E)
    (h : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ = Y * κ * Y⁻¹) (x : Fin n → E) :
    ((bc (prV (E := E) w) Y)⁻¹).val *ᵥ (fun a => inclE (F := F) (w.adicCompletion F) ((γ.val *ᵥ x) a)) =
      (bc (prV (E := E) w) κ).val *ᵥ (((bc (prV (E := E) w) Y)⁻¹).val *ᵥ fun a => inclE (F := F) (w.adicCompletion F) (x a)) :=
  conj_step w _ _ γ (by rw [bc_incl_w, h, map_mul, map_mul, map_inv]) x

end Gen

theorem dualLoc_of {i : ℕ} {hi : i ≤ D.R.m} (K : ClsTied u i hi) (w : HeightOneSpectrum (𝓞 D.host.F)) (c : (D.mem u).C.cls i)
    (z : Fin (D.R.N i) → D.host.E) (hz : z ∈ Ld D u i hi c) :
    ((bc (prV (E := D.host.E) w) (K.y c).1)⁻¹).1 *ᵥ (fun a => inclE (F := D.host.F) (w.adicCompletion D.host.F) (z a)) ∈
      latS (F := D.host.F) (w.adicCompletion D.host.F) (intV D.host.E w)
        (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) K.lev.Lb)) := by
  rw [ld_eq_glob K c] at hz
  exact locDual w (K.y c).1 _ z hz

end Formalism.L2.GlobalTheoryTheory.Br
