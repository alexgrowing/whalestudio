import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ParGMapGlRed
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ParabolicReductionImage
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.StRedOfSplit
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SplitTransport

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxStImB MassDataIdxRed

section Loc

variable {D : D7} (X : HidaSetting D)

abbrev SuX (u : D.what₂.Word) (p : TypX X) : Subgroup (HAp X p) :=
  Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u)

def StSImgB (u : D.what₂.Word) (p : TypX X) : Prop :=
  ∃ K : Subgroup (HAp X p), (K : Set (HAp X p)) = KvX X p ∧
    ∃ ψ : K →* GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p), Function.Surjective ψ ∧
      (∀ x : K, (∀ i j, ((ψ x : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p))
        - 1) i j ∈ Ideal.span {((gOf p : ℕ) : Op X p)}) ↔ (x : HAp X p) ∈ KgX X p) ∧
      ∃ c, ((SuX X u p).comap K.subtype).map ψ = (sG (Op X p) D.R.rS D.R.k).map (MulAut.conj c).toMonoidHom

theorem parabolic_image_of_residue (u : D.what₂.Word) (p : TypX X) (hR : StResZ X p) (hS : StSImgB X u p) :
    ParabolicReductionImage X u p := by
  obtain ⟨π, hπ, hker⟩ := hR
  obtain ⟨K, hK, ψ, hψ, hP, c, hc⟩ := hS
  have : Fact (gOf p).Prime := ⟨gOf_prime X p⟩
  set ρ₀ : K →* GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p)) := (glRed π).comp ψ with hρ₀
  have hker₀ : ∀ x : K, ρ₀ x = 1 ↔ (x : HAp X p) ∈ KgX X p := by
    intro x
    rw [hρ₀, MonoidHom.comp_apply, glRed_eq_one_iff, hker]
    exact hP x
  have hmemK : ∀ y : HAp X p, y ∈ KvX X p → y ∈ K := fun y hy => by
    rw [← SetLike.mem_coe, hK]; exact hy
  refine ⟨K, hK, ρ₀, (glRed_surjective π hπ (isUnit_of_map π hπ)).comp hψ, hker₀,
    (SuX X u p).comap K.subtype ⊔ ρ₀.ker, ?_, le_sup_right, glRed π c, ?_⟩
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨s, hs, κ, hκ, rfl⟩ := (mem_sup_ker ρ₀ _).1 hx
      have hκ' : (κ : HAp X p) ∈ KgX X p := (hker₀ κ).1 hκ
      have hsK : (s : HAp X p) ∈ KvX X p := by rw [← hK]; exact s.2
      have hxK : ((s * κ : K) : HAp X p) ∈ KvX X p := by rw [← hK]; exact (s * κ).2
      exact ⟨hxK, s, κ, hs, hsK, hκ', rfl⟩
    · rintro ⟨hy, s, κ, hs, hsK, hκ, rfl⟩
      refine ⟨⟨s, hmemK s hsK⟩ * ⟨κ, hmemK κ hκ.1⟩, ?_, rfl⟩
      refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right ?_)
      · exact hs
      · rw [MonoidHom.mem_ker, hker₀]; exact hκ
  · rw [map_sup_ker, hρ₀, ← Subgroup.map_map, hc, map_conj,
      sG_map_glRed π hπ]

def StFrameB (u : D.what₂.Word) (p : TypX X) : Prop :=
  ∃ K : Subgroup (HAp X p), (K : Set (HAp X p)) = KvX X p ∧
    ∃ ψ : K →* GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p), Function.Surjective ψ ∧
      (∀ x : K, (∀ i j, ((ψ x : Matrix (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (Op X p))
        - 1) i j ∈ Ideal.span {((gOf p : ℕ) : Op X p)}) ↔ (x : HAp X p) ∈ KgX X p) ∧
      ∃ c, ∀ x : K, (x : HAp X p) ∈ SuX X u p ↔ c⁻¹ * ψ x * c ∈ sG (Op X p) D.R.rS D.R.k

theorem stSImgB_of (u : D.what₂.Word) (p : TypX X) (h : StFrameB X u p) : StSImgB X u p := by
  obtain ⟨K, hK, ψ, hψ, hP, c, hc⟩ := h
  exact ⟨K, hK, ψ, hψ, hP, c, map_eq_conj ψ hψ _ _ c fun x => hc x⟩

theorem parabolic_image_of_residue_frame (u : D.what₂.Word) (p : TypX X) (hR : StResZ X p) (h : StFrameB X u p) :
    ParabolicReductionImage X u p :=
  parabolic_image_of_residue X u p hR (stSImgB_of X u p h)

theorem parabolic_image_of_frame (u : D.what₂.Word) (p : TypX X) (h : StFrameB X u p) : ParabolicReductionImage X u p :=
  parabolic_image_of_residue_frame X u p (stResZ_holds X p) h

end Loc

end MassDataIdxSteps
