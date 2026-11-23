import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.REALTH
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilModulusHypothesis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FieldInducedMaxCompactVector
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th ComplexConjugate
open GroundTheory.Automorphic.GodementSection (localChar)
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.SphFUnr

theorem indicator_integers_mem_SBE (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] :
    IsLocallyConstant (Set.indicator {x : E | x ∈ 𝒪[E]} (1 : E → ℂ)) ∧
      HasCompactSupport (Set.indicator {x : E | x ∈ 𝒪[E]} (1 : E → ℂ)) := by
  have hset : ({x : E | x ∈ 𝒪[E]} : Set E) = (valBall E 0 : Set E) := by
    rw [coe_valBall_zero]; rfl
  have hclopen : IsClopen ({x : E | x ∈ 𝒪[E]} : Set E) := by
    rw [hset]; exact ⟨isClosed_valBall 0, isOpen_valBall 0⟩
  have hcomp : IsCompact ({x : E | x ∈ 𝒪[E]} : Set E) := by
    rw [hset]; exact isCompact_valBall 0
  refine ⟨?_, HasCompactSupport.intro hcomp fun x hx => Set.indicator_of_notMem hx _⟩
  refine (IsLocallyConstant.iff_exists_open _).2 fun x => ?_
  by_cases hx : x ∈ ({x : E | x ∈ 𝒪[E]} : Set E)
  · exact ⟨_, hclopen.isOpen, hx, fun y hy => by
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]; rfl⟩
  · exact ⟨_, hclopen.compl.isOpen, hx, fun y hy => by
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩

theorem sphf : Ad3.K.GL2LocalData.WPiRep → Ad3.K.QuadraticBaseChangeGL3.Th.PIKF → Ad3.K.QuadraticBaseChangeGL3.Th.NORMU → Ad3.K.QuadraticBaseChangeGL3.Th.SPHF := by
  intro hP hK hN F _ _ _ _ _ _ _ χ hχ hχ1 E _ _ _ _ _ _ _ hd hc σ hσ η hη hcond hres c hcu
  have hW := GlobalTheory.CompanionTheory.NormModulus.wMod F χ hχ hχ1 E hd hc σ hσ η hη
  have hmodt : ∀ t : Eˣ, modulus (Algebra.norm F (t : E)) = 1 → modulus (t : E) = 1 := by
    intro t ht
    have h := hW (t : E)
    rw [ht] at h
    exact_mod_cast h
  have hct : ∀ t : Eˣ, modulus (t : E) = 1 → c t = 1 := by
    intro t ht
    have hmem : t ∈ unitFiltrationUnits E 0 :=
      ord_eq_zero_iff_mem.1 (modulus_eq_one_iff.1 ht).2
    exact MonoidHom.mem_ker.1 (hcu hmem)
  have hSB : Set.indicator {x : E | x ∈ 𝒪[E]} (1 : E → ℂ) ∈ GL2LocalData.SBc F E c := by
    obtain ⟨h1, h2⟩ := indicator_integers_mem_SBE E
    refine ⟨h1, h2, fun u hu x => ?_⟩
    have hm : modulus (u : E) = 1 := hmodt u (by rw [hu]; simp)
    rw [GlobalTheory.CompanionTheory.PiKFUnr.indicator_mul_of_modulus_eq_one hm x, hct u hm]
    simp
  refine ⟨fun k hk g => ?_, ?_⟩
  · obtain ⟨hk1, hk2⟩ := (GLnLocal.mem_integralGL_iff F 2).1 hk
    let u : Fˣ := Matrix.GeneralLinearGroup.det k
    have hu1 : (u : F) ∈ 𝒪[F] := GlobalTheory.CompanionTheory.PiKFUnr.det_mem_of_entries hk1
    have hu2 : ((u⁻¹ : Fˣ) : F) ∈ 𝒪[F] := by
      have : ((u⁻¹ : Fˣ) : F) = ((k⁻¹ : GL (Fin 2) F).val).det := by
        simp [u, map_inv]
      rw [this]
      exact GlobalTheory.CompanionTheory.PiKFUnr.det_mem_of_entries hk2
    have hex : ∃ t : Eˣ, Algebra.norm F (t : E) = (k.val).det :=
      hN F χ hχ hχ1 E hd hc σ hσ η hη hres u hu1 hu2
    rw [(hP F χ hχ hχ1 E hd hc σ hσ η hη c _ hSB g k hex).1,
      hK F χ hχ hχ1 E hd hc σ hσ η hη hcond hres c hcu k hk]
  · show GL2LocalData.Wc χ σ (GL2LocalData.muE E χ) (GL2LocalData.lamE E χ η) c _ 1 = 1
    have hex : ∃ t : Eˣ, Algebra.norm F (t : E) = ((1 : GL (Fin 2) F).val).det :=
      ⟨1, by simp⟩
    unfold GL2LocalData.Wc
    rw [dif_pos hex]
    have hN1 : Algebra.norm F (hex.choose : E) = 1 := by
      rw [hex.choose_spec]; simp
    generalize hex.choose = t at hN1 ⊢
    have hm : modulus (t : E) = 1 := hmodt _ (by rw [hN1]; simp)
    have hmem : (t : E) ∈ {x : E | x ∈ 𝒪[E]} := modulus_le_one_iff.1 hm.le
    have hns : GL2LocalData.nsg E (1 : F) = 1 := by
      unfold GL2LocalData.nsg
      rw [if_pos ⟨1, by simp⟩]
    rw [hct _ hm]
    simp only [GL2LocalData.rW]
    simp [hns]
    exact Set.indicator_of_mem hmem (1 : E → ℂ)

end GlobalTheory.CompanionTheory.SphFUnr
