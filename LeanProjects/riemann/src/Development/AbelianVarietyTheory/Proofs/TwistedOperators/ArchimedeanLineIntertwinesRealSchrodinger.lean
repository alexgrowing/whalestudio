import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionUnitaryCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairingStdP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActsRhoOfAtInf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdmissibleFiniteFactorArchimedeanSchwartzStatement

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.ArchUniq MeasureTheory
open scoped SchwartzMap Classical

noncomputable section

namespace GlobalTheory.ArchFam

open scoped Matrix

variable {F : Type} [Field F] [NumberField F]

theorem at_liftV {κ : Type} (y : κ → mixedEmbedding.mixedSpace F) : At (evI F) (liftV y) := by
  intro u hu
  have h : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.1 hu
  funext i
  refine Prod.ext ?_ ?_
  · change u.1 * _ = 0
    rw [h, zero_mul]
  · change u.2 * 0 = 0
    exact mul_zero _

theorem rho_tens (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) {W' : Type} [AddCommGroup W'] [Module (AF F) W']
    {Bf : W' → W' → AF F} {κ : Type} [Fintype κ] (dc : Darboux Bf κ) (w : W') (hw : At (evI F) w)
    (φ : (κ → mixedEmbedding.mixedSpace F) → ℂ) (r : (κ → AF F) → ℂ)
    (hr : ∀ x z, At (evI F) z → r (x + z) = r x) :
    dc.rho ψ w (tens (evI F) φ r) =
      tens (evI F) (schrF (trP F κ) (locV (dc.e w).1, locV (dc.e w).2) φ) r := by
  have hab : ∀ u : AF F, evI F u = 0 → u • dc.e w = 0 := fun u hu => by
    rw [← map_smul, hw u hu, map_zero]
  have ha : At (evI F) (dc.e w).1 := fun u hu => congrArg Prod.fst (hab u hu)
  have hb : At (evI F) (dc.e w).2 := fun u hu => congrArg Prod.snd (hab u hu)
  funext x
  have ht : At (evI F) (x ⬝ᵥ (dc.e w).2 + ⅟(2 : AF F) * (dc.e w).1 ⬝ᵥ (dc.e w).2) := fun u hu => by
    have h : ∀ y : κ → AF F, u * (y ⬝ᵥ (dc.e w).2) = 0 := fun y => by
      rw [← smul_eq_mul, ← dotProduct_smul, hb u hu, dotProduct_zero]
    rw [smul_eq_mul, mul_add, h, mul_left_comm, h, mul_zero, add_zero]
  have hloc : (fun i => evI F ((x + (dc.e w).1) i)) = locV x + locV (dc.e w).1 := by
    funext i
    simp only [Pi.add_apply, locV, evI_eq_evIHom, map_add]
  simp only [Darboux.rho, schr, tens]
  rw [hψ.2.2 _ ht, trace_evI_heis, hr x _ ha, hloc, schrF]
  exact (mul_assoc _ _ _).symm

theorem tens_inj {κ : Type} (r : (κ → AF F) → ℂ) (hr : ∀ x z, At (evI F) z → r (x + z) = r x)
    (x₀ : κ → AF F) (h0 : r x₀ ≠ 0) (φ₁ φ₂ : (κ → mixedEmbedding.mixedSpace F) → ℂ)
    (h : tens (evI F) φ₁ r = tens (evI F) φ₂ r) : φ₁ = φ₂ := by
  funext y
  have hz : At (evI F) (liftV (y - locV x₀)) := at_liftV _
  have hx := congrFun h (x₀ + liftV (y - locV x₀))
  simp only [tens] at hx
  have hl : (fun i => evI F ((x₀ + liftV (y - locV x₀)) i)) = y := by
    change locV (x₀ + liftV (y - locV x₀)) = y
    rw [Coord.loc_add, Coord.loc_lift]
    abel
  rw [hl, hr _ _ hz] at hx
  exact mul_right_cancel₀ h0 hx

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

def wv (M : Model σ X W)
    (v : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) :
    Matrix (Fin n) (Fin d) (AE F E) :=
  M.co.e.symm (liftV v.1, liftV v.2)

theorem at_wv (M : Model σ X W)
    (v : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) :
    At (evI F) (wv M v) := by
  intro u hu
  rw [wv, ← map_smul, Prod.smul_mk, at_liftV v.1 u hu, at_liftV v.2 u hu, Prod.mk_zero_zero, map_zero]

theorem at_mul {w : Matrix (Fin n) (Fin d) (AE F E)} (hw : At (evI F) w) (m : Matrix (Fin d) (Fin d) (AE F E)) :
    At (evI F) (w * m) := by
  intro u hu
  rw [← Matrix.smul_mul, hw u hu, Matrix.zero_mul]

def amap (M : Model σ X W) (m : Matrix (Fin d) (Fin d) (AE F E)) :
    ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
      ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) where
  toFun v := Coord.coordI M (wv M v * m)
  map_add' v v' := by
    simp only [wv, Prod.fst_add, Prod.snd_add, Coord.lift_add, ← Prod.mk_add_mk, map_add, Matrix.add_mul,
      Coord.coordI_add]
  map_smul' c v := by
    simp only [wv, Prod.smul_fst, Prod.smul_snd, Coord.lift_smul, ← Prod.smul_mk, map_smul, Matrix.smul_mul,
      Coord.coordI_smul, RingHom.id_apply]

end GlobalTheory.ArchFam

namespace GlobalTheory.ArchFam

open scoped Matrix

open GlobalTheory.ArchUniq.Coord in

theorem schr_equiv : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    IsStd ψ → M.IsWeil ψ χX χW om → ∀ γ ∈ Lines σ W, ∀ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
    (∀ t (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) ⇑f ⇑(T t f)) →
    ∃ A : ℝ → ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
        ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)),
      (∀ v, Continuous fun t => A t v) ∧
      ∀ t v (f f₁ : SInf F (Fin n × Fin d)), ⇑f₁ = schrF (trP F (Fin n × Fin d)) v ⇑f →
        ⇑(T t f₁) = schrF (trP F (Fin n × Fin d)) (A t v) ⇑(T t f) := by
  intro F E _ _ _ _ _ σ n d X W M ψ χX χW om hψ hW γ hγ T hT
  refine ⟨fun t => amap M (mat (γ (Multiplicative.ofAdd t)))ᵀ, fun v => ?_, fun t v f f₁ hf => ?_⟩
  · haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
    haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
    haveI : IsModuleTopology (AF F) (Matrix (Fin n) (Fin d) (AE F E)) :=
      inferInstanceAs (IsModuleTopology (AF F) (Fin n → Fin d → AE F E))
    have hm : Continuous fun t : ℝ => (mat (γ (Multiplicative.ofAdd t)))ᵀ :=
      ((Units.continuous_val.comp continuous_subtype_val).comp (hγ.1.comp continuous_ofAdd)).matrix_transpose
    have he : Continuous M.co.e := IsModuleTopology.continuous_of_linearMap M.co.e.toLinearMap
    have hev : Continuous (evI F) := by
      change Continuous fun a : AF F => InfiniteAdeleRing.ringEquiv_mixedSpace F a.1
      refine Continuous.comp ?_ continuous_fst
      change Continuous fun x : InfiniteAdeleRing F =>
        ((fun (v : {w : InfinitePlace F // w.IsReal}) => InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
         (fun (v : {w : InfinitePlace F // w.IsComplex}) => InfinitePlace.Completion.extensionEmbedding v.1 (x v)))
      refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
      · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
      · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)
    have hl : Continuous (locV : (Fin n × Fin d → AF F) → _) := continuous_pi fun i => hev.comp (continuous_apply i)
    show Continuous fun t => (locV (M.co.e (wv M v * (mat (γ (Multiplicative.ofAdd t)))ᵀ)).1,
      locV (M.co.e (wv M v * (mat (γ (Multiplicative.ofAdd t)))ᵀ)).2)
    exact ((hl.comp continuous_fst).prodMk (hl.comp continuous_snd)).comp (he.comp (continuous_const.matrix_mul hm))
  · obtain ⟨r₀, hr₀, hinj⟩ := GlobalTheory.T.exists_admissible_finiteFactor_archimedeanSchwartz (F := F) (Fin n × Fin d)
    have hrr := (hr₀ 0).1
    by_cases hz : ∀ x, r₀ x = 0
    · have h0 : ∀ g : SInf F (Fin n × Fin d), g = 0 := fun g => hinj g 0 (by funext x; simp [tens, hz])
      rw [h0 (T t f₁), h0 (T t f)]
      funext y
      simp [schrF]
    simp only [not_forall] at hz
    obtain ⟨x₀, hx₀⟩ := hz
    have hs := hW.isUSplitting
    have hc : (locV (M.co.e (wv M v)).1, locV (M.co.e (wv M v)).2) = v := coordI_lift M v
    have e1 : tens (evI F) ⇑f₁ r₀ = M.co.rho ψ (wv M v) (tens (evI F) ⇑f r₀) := by
      rw [rho_tens ψ hψ M.co _ (at_wv M v) _ _ hrr, hc, ← hf]
    have e2 : om (1, γ (Multiplicative.ofAdd t)) (M.co.rho ψ (wv M v) (tens (evI F) ⇑f r₀)) =
        M.co.rho ψ (wv M v * (mat (γ (Multiplicative.ofAdd t)))ᵀ)
          (om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) ⇑f r₀)) := by
      rw [hs.impl (1, γ (Multiplicative.ofAdd t)) (wv M v) _ (hr₀ f).2]
      congr 2
      simp only [actAB, mat, OneMemClass.coe_one, Units.val_one, Matrix.one_mul]
    have e3 := hT t f r₀ (hr₀ f)
    have e4 := hT t f₁ r₀ (hr₀ f₁)
    apply tens_inj r₀ hrr x₀ hx₀
    rw [← e4, e1, e2, e3, rho_tens ψ hψ M.co _ (at_mul (at_wv M v) _) _ _ hrr]
    rfl

end GlobalTheory.ArchFam
