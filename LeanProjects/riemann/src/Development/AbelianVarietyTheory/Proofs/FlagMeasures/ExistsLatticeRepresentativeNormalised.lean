import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LinearFormsBoundedRepresentatives
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsNeZeroSmulMem
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowPartner

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

theorem mem_orth_iff (U : Submodule E S.V) (y : S.V) : y ∈ orth S U ↔ ∀ x ∈ U, S.hT x y = 0 := by
  simp [orth, Submodule.mem_iInf]

theorem X_iso (F : LFlag S r T) {x y : S.V} (hx : x ∈ Xsp F) (hy : y ∈ Xsp F) : S.hT x y = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨b, rfl⟩ := hy; exact F.fl.e_iso a b
    | zero => simp
    | add u v _ _ hu hv => simp [hu, hv]
    | smul c u _ hu => simp [hu]
  | zero => simp
  | add u v _ _ hu hv => simp [hu, hv]
  | smul c u _ hu => simp [hu]

theorem z_mem_orth (F : LFlag S r T) : F.fl.z ∈ orth S (Xsp F) := by
  rw [mem_orth_iff]
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨a, rfl⟩ := hx; exact F.fl.z_orth a
  | zero => simp
  | add u v _ _ hu hv => simp [hu, hv]
  | smul c u _ hu => simp [hu]

theorem X_le_orth (F : LFlag S r T) : Xsp F ≤ orth S (Xsp F) := fun y hy =>
  (mem_orth_iff _ _).2 fun x hx => X_iso F hx hy

theorem half_not_int : ¬ ∃ o : 𝓞 E, (o : E) = algebraMap ℚ E (1 / 2) := by
  rintro ⟨o, ho⟩
  have h1 : IsIntegral ℤ (algebraMap ℚ E (1 / 2)) := by rw [← ho]; exact o.2
  rw [isIntegral_algebraMap_iff (algebraMap ℚ E).injective] at h1
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp h1
  have h2 : ((2 * n : ℤ) : ℚ) = 1 := by push_cast; rw [show (algebraMap ℤ ℚ n) = (n : ℚ) from rfl] at hn; rw [hn]; norm_num
  have h3 : 2 * n = 1 := by exact_mod_cast h2
  omega

end Gen

end GlobalTheory.RowPartner

namespace GlobalTheory.RowPartner

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

theorem exists_smul_mem_lat (L : Submodule (𝓞 E) S.V) (hL : Submodule.IsLattice E L) (x : S.V) :
    ∃ r : 𝓞 E, r ≠ 0 ∧ r • x ∈ L := by
  first
  | exact @_root_.GlobalTheory.NonzeroIntegerSmulMem.exists_ne_zero_smul_mem
  | exact _root_.GlobalTheory.NonzeroIntegerSmulMem.exists_ne_zero_smul_mem
  | (apply _root_.GlobalTheory.NonzeroIntegerSmulMem.exists_ne_zero_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.NonzeroIntegerSmulMem.exists_ne_zero_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NonzeroIntegerSmulMem.exists_ne_zero_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NonzeroIntegerSmulMem.exists_ne_zero_smul_mem ..)

theorem z_not_mem_X (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T)
    (hprim : ∀ c : E, c • F.fl.z ∈ Lsub Λ F → ∃ o : 𝓞 E, (o : E) = c) : F.fl.z ∉ Xsp F := by
  intro hz
  apply half_not_int (E := E)
  apply hprim
  have hc : algebraMap ℚ E (1 / 2) • F.fl.z ∈ Xsp F := (Xsp F).smul_mem _ hz
  exact ⟨Submodule.mem_sup_right hc, X_le_orth F hc⟩

theorem exists_partner_rep (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T)
    (hlat : Submodule.IsLattice E Λ) (hU : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) (hz : F.fl.z ∈ Λ)
    (hprim : ∀ c : E, c • F.fl.z ∈ Lsub Λ F → ∃ o : 𝓞 E, (o : E) = c) :
    ∃ σ ∈ Lrep Λ F, S.hT σ F.fl.z = 1 := by
  have hzX := z_not_mem_X Λ F hprim
  obtain ⟨φ, hφX, hφz⟩ := LinearMap.exists_extend_of_notMem (0 : Xsp F →ₗ[E] E) hzX 1
  have hφ0 : ∀ y ∈ Xsp F, φ y = 0 := fun y hy => by simpa using congr($hφX ⟨y, hy⟩)
  set U : Submodule E S.V := Xsp F ⊔ Submodule.span E {F.fl.z} with hUdef
  set M0 : Submodule (𝓞 E) S.V := Λ ⊓ toO S U with hM0
  have hUo : U ≤ orth S (Xsp F) := sup_le (X_le_orth F)
    ((Submodule.span_singleton_le_iff_mem _ _).2 (z_mem_orth F))
  have hprimM : IsPrimitiveSub M0 Λ := by
    refine ⟨inf_le_left, le_antisymm (le_inf inf_le_left fun x hx => Submodule.subset_span hx) ?_⟩
    refine inf_le_inf_left _ ?_
    intro x hx
    exact (Submodule.span_le (p := U)).2 (fun y hy => hy.2) hx
  have hint : ∀ x : M0, ∃ o : 𝓞 E, (o : E) = φ x := by
    rintro ⟨x, hxΛ, hxU⟩
    obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.1 (show x ∈ U from hxU)
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hw
    have hxo : y + a • F.fl.z ∈ orth S (Xsp F) := hUo hxU
    obtain ⟨o, ho⟩ := hprim a ⟨by
        have h1 : y + a • F.fl.z ∈ Lrep Λ F := ⟨hxΛ, hxo⟩
        have h2 : -y ∈ toO S (Xsp F) := (Xsp F).neg_mem hy
        have := Submodule.add_mem_sup h1 h2
        simpa using this, (orth S (Xsp F)).smul_mem a (z_mem_orth F)⟩
    refine ⟨o, ?_⟩
    simp [map_add, hφ0 y hy, hφz, ho]
  choose ψ hψ using hint
  let ψ' : M0 →ₗ[𝓞 E] 𝓞 E :=
    { toFun := ψ
      map_add' := fun x y => by
        apply RingOfIntegers.ext
        simp [hψ]
      map_smul' := fun c x => by
        apply RingOfIntegers.ext
        simp only [hψ, RingHom.id_apply, smul_eq_mul, map_mul, Submodule.coe_smul]
        rw [← algebraMap_smul E c (x : S.V), map_smul]
        simp [hψ] }
  obtain ⟨w, hw⟩ := GlobalTheory.LoopC.FunIdx.exists_dual_vec S M0 Λ hlat hprimM ψ'
  have hwM : ∀ x (hx : x ∈ M0), S.hT w x = φ x := fun x hx => by
    rw [← hw ⟨x, hx⟩]; exact hψ ⟨x, hx⟩
  have hwΛ : (w : S.V) ∈ Λ := by
    have := w.2.1
    rwa [hU] at this
  refine ⟨w, ⟨hwΛ, ?_⟩, ?_⟩
  · show (w : S.V) ∈ orth S (Xsp F)
    rw [mem_orth_iff]
    intro x hx
    obtain ⟨c, hc0, hcx⟩ := exists_smul_mem_lat Λ hlat x
    have hcX : c • x ∈ Xsp F := by
      rw [← algebraMap_smul E c x]; exact (Xsp F).smul_mem _ hx
    have hm : c • x ∈ M0 := ⟨hcx, Submodule.mem_sup_left hcX⟩
    have h1 := hwM _ hm
    rw [hφ0 _ hcX] at h1
    have h2 : S.hT w x = 0 := by
      rw [← algebraMap_smul E c x, map_smul, smul_eq_mul] at h1
      exact (mul_eq_zero.1 h1).resolve_left (by simpa using hc0)
    rw [← S.herm.eq, h2]; simp
  · rw [hwM _ ⟨hz, Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)⟩, hφz]

end Gen

end GlobalTheory.RowPartner

namespace GlobalTheory.RowPartner

theorem exists_partner_rowLat : ∀ (D : D7) (T : D.host.E) (F0 : FlagG (VS D) D.R.rS T) (Λ : LV D),
    IsRowLat D F0 Λ → ∃ σ ∈ Lrep Λ (lf D F0), (VS D).hT σ F0.z = 1 := by
  intro D T F0 Λ h
  obtain ⟨_, ⟨hlat, hU, ⟨hz, _⟩, ⟨_, hprim⟩⟩, _⟩ := h
  exact exists_partner_rep Λ (lf D F0) hlat hU hz hprim

end GlobalTheory.RowPartner
