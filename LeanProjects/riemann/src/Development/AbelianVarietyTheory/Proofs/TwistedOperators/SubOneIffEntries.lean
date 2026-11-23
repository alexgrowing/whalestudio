import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KgFrame

open Formalism.L2.DIV Formalism.L2.Herm Formalism.UG
open scoped TensorProduct Matrix

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem dvd_of_forall_mem (g : ℕ) (hg : 1 ≤ g) (hr : (Ideal.span {(g : 𝓞 E)}).IsRadical)
    (b : 𝓞 E) (hb : ∀ PP : Pl E, (g : 𝓞 E) ∈ PP.asIdeal → b ∈ PP.asIdeal) : (g : 𝓞 E) ∣ b := by
  have hg0 : (g : 𝓞 E) ≠ 0 := by exact_mod_cast (by omega : g ≠ 0)
  rw [← Ideal.mem_span_singleton]
  refine hr ?_
  rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
  rintro J ⟨hJ, hp⟩
  have hJ0 : J ≠ ⊥ := by
    intro e
    rw [e, le_bot_iff, Ideal.span_singleton_eq_bot] at hJ
    exact hg0 hJ
  exact hb ⟨J, hp, hJ0⟩ (hJ (Ideal.mem_span_singleton_self _))

theorem entries_iff_red (g : ℕ) (hg : 1 ≤ g) (hr : (Ideal.span {(g : 𝓞 E)}).IsRadical) (y : GL (Fin n) (intAf F E)) :
    (∀ i j, ∃ t : intAf F E, (y : Matrix (Fin n) (Fin n) (intAf F E)) i j -
        (1 : Matrix (Fin n) (Fin n) (intAf F E)) i j = g • t) ↔
      ∀ PP : Pl E, (g : 𝓞 E) ∈ PP.asIdeal → bc (resS F PP) y = 1 := by
  constructor
  · intro h PP hP
    have hgk : ((g : ℕ) : kP PP) = 0 := by
      have := Ideal.Quotient.eq_zero_iff_mem.2 hP
      rwa [map_natCast] at this
    apply Units.ext
    ext i j
    obtain ⟨t, ht⟩ := h i j
    have h1 := congrArg (resS F PP) ht
    rw [map_sub, map_nsmul, nsmul_eq_mul, hgk, zero_mul, sub_eq_zero] at h1
    show resS F PP ((y : Matrix (Fin n) (Fin n) (intAf F E)) i j) = (1 : Matrix (Fin n) (Fin n) (kP PP)) i j
    rw [h1]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  · intro h i j
    refine lc_div g (by omega) (dvd_of_forall_mem g hg hr) _ fun PP hP => ?_
    have h1 := congrArg (fun M : GL (Fin n) (kP PP) => (M : Matrix (Fin n) (Fin n) (kP PP)) i j) (h PP hP)
    change resS F PP ((y : Matrix (Fin n) (Fin n) (intAf F E)) i j) = (1 : Matrix (Fin n) (Fin n) (kP PP)) i j at h1
    rw [map_sub, h1]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]

theorem sub_one_iff_entries (Λ : Submodule (𝓞 E) (Fin n → E)) (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (hβ : IsFrame β Λ)
    (g : ℕ) (y : GL (Fin n) (intAf F E)) :
    (∀ v ∈ hatL (F := F) Λ, ∃ z ∈ hatL (F := F) Λ,
      (((frGL β y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) - 1) *ᵥ v =
        (g : E ⊗[F] Formalism.L2.Herm.Af F) • z) ↔
    ∀ i j, ∃ t : intAf F E, (y : Matrix (Fin n) (Fin n) (intAf F E)) i j -
        (1 : Matrix (Fin n) (Fin n) (intAf F E)) i j = g • t := by
  classical
  set B : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) := (β : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) with hB
  set Bi : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) :=
    ((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) with hBi
  set Y : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) :=
    (y : Matrix (Fin n) (Fin n) (intAf F E)).map (intAf F E).subtype with hY
  have hXe : ((frGL β y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = B * Y * Bi :=
    lc_frGL_coe β y
  have hBiB : Bi * B = 1 := Units.inv_mul β
  have hBBi : B * Bi = 1 := Units.mul_inv β
  have hX1 : ((frGL β y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) - 1 = B * (Y - 1) * Bi := by
    rw [hXe, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hBBi]
  have hYe : ∀ i j, Y i j - (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) i j =
      (((y : Matrix (Fin n) (Fin n) (intAf F E)) i j - (1 : Matrix (Fin n) (Fin n) (intAf F E)) i j : intAf F E) :
        E ⊗[F] Formalism.L2.Herm.Af F) := by
    intro i j
    rw [← lc_one_coe]
    rfl
  constructor
  · intro h i j
    obtain ⟨z, hz, e⟩ := h _ (lc_frame_mem hβ (Pi.single j 1) (fun k => by rw [Pi.single_apply]; split_ifs; exacts [one_mem _, zero_mem _]))
    have hc := (hβ z).1 hz
    refine ⟨⟨(Bi *ᵥ z) i, hc i⟩, ?_⟩
    apply Subtype.ext
    rw [← hYe]
    have e2 := congrArg (fun w => (Bi *ᵥ w) i) e
    beta_reduce at e2
    have hconj : Bi * (B * (Y - 1) * Bi) * B = Y - 1 := by
      calc Bi * (B * (Y - 1) * Bi) * B = (Bi * B) * (Y - 1) * (Bi * B) := by simp only [Matrix.mul_assoc]
        _ = Y - 1 := by rw [hBiB, Matrix.one_mul, Matrix.mul_one]
    rw [hX1, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hB, hconj, Matrix.mulVec_smul, Matrix.mulVec_single_one] at e2
    rw [Pi.smul_apply, smul_eq_mul] at e2
    rw [show (Y i j - (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) i j) = (Y - 1).col j i from rfl, e2]
    simp [nsmul_eq_mul]
  · intro h
    choose t ht using h
    set M' : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) := fun i j => ((t i j : intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) with hM'
    have hYM : Y - 1 = (g : E ⊗[F] Formalism.L2.Herm.Af F) • M' := by
      ext i j
      rw [Matrix.sub_apply, hYe, ht i j]
      rw [Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul]
      rfl
    refine fun v hv => ⟨B *ᵥ (M' *ᵥ (Bi *ᵥ v)), lc_frame_mem hβ _ fun i => ?_, ?_⟩
    · have hc := (hβ v).1 hv
      simp only [Matrix.mulVec, dotProduct]
      exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (t i j).2 (hc j)
    · rw [hX1, hYM, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

end Gen

theorem Lf_eq (D : D7) : (Formalism.L2.SG.InstExistsPf.instOf D).Lf =
      hatL (F := D.host.F) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) := by
  have hΛ : Formalism.L2.SG.InstExistsPf.Lv D = Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0 := by
    rw [Formalism.L2.SG.InstExistsPf.Lv_eq_map]; rfl
  show lamAf (F := ↥D.host.F) (Formalism.L2.SG.InstExistsPf.Lv D) = _
  rw [hΛ]
  unfold lamAf hatL Formalism.UG.latS
  rw [Set.image_eq_range]
  rfl

set_option maxHeartbeats 2000000 in

theorem mem_Kg_iff_redFn : ∀ (D : D7) (β : GL (Fin (Yc D 0).rank) (EAf D)) (x : (Formalism.L2.SG.InstExistsPf.instOf D).Gf) (g : ℕ),
    IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → x ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Kset → 1 ≤ g →
    (Ideal.span {(g : 𝓞 D.host.E)}).IsRadical →
    (x ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Kg g ↔
      ∀ PP : Formalism.L2.DIV.Pl D.host.E, (g : 𝓞 D.host.E) ∈ PP.asIdeal → Formalism.L2.DIV.redFn β PP x.1 = 1) := by
  intro D β x g hβ hx hg hr
  have hLf := Lf_eq D
  have hSt : x.1 ∈ St β := by
    rw [stabilizer_eq_stabilizer_lattice _ _ _ _ β hβ, ← hLf]
    exact hx
  obtain ⟨y, hy⟩ := hSt
  have hred : ∀ PP : Pl D.host.E, redFn β PP x.1 = bc (resS D.host.F PP) y := fun PP => by
    rw [← hy, redFn_frGL]

  have key := (sub_one_iff_entries _ β hβ g y).trans (entries_iff_red g hg hr y)
  have hfm : (Formalism.L2.SG.InstExistsPf.instOf D).fmat x = (frGL β y).val := by
    show x.1.val = _
    rw [← hy]
  have hv1 := fun v => SetLike.ext_iff.1 hLf v
  constructor
  · intro hk PP hP
    refine (hred PP).trans (key.1 (fun v hv => ?_) PP hP)
    obtain ⟨z, hz, e⟩ := hk.2 v ((hv1 v).2 hv)
    refine ⟨z, (hv1 z).1 hz, ?_⟩
    rw [← hfm]
    exact e
  · intro h
    refine ⟨hx, fun v hv => ?_⟩
    obtain ⟨z, hz, e⟩ := key.2 (fun PP hP => (hred PP).symm.trans (h PP hP)) v ((hv1 v).1 hv)
    refine ⟨z, (hv1 z).2 hz, ?_⟩
    rw [hfm]
    exact e

end GlobalTheory.KgFrame
