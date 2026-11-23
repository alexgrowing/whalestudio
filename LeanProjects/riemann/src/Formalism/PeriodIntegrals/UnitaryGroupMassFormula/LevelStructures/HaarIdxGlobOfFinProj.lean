import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.ConjugateLevelOpenUnitary
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.Bridge

noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge PI.MassDataKppVolLemmas
open Formalism.MainNotions.S (AutInst)
open scoped TensorProduct

def FinProjOpen : Prop :=
  ∀ I : AutInst, IsOpenMap (fun h : HAd I => (splitA I.cm.sig I.J h).2)

theorem finPart_inf_one (I : AutInst) (hb : AdBridgeIso I) (s : I.Ginf) :
    (splitA I.cm.sig I.J (toHA I hb (s, 1))).2 = 1 := by
  apply Bridge_HA_ext
  have hB : I.fmat 1 = ofHAFin I (toHA I hb (s, 1)) := (toHA_isBridge I hb (s, 1)).2
  have hm : ((HA.mat (Af I.F) I.cm.sig I.J ((splitA I.cm.sig I.J (toHA I hb (s, 1))).2) :
      GL (Fin I.n) (Af I.F ⊗[I.F] I.E)) : Matrix (Fin I.n) (Fin I.n) _) =
      (ofHAFin I (toHA I hb (s, 1))).map (swapE I) := by
    ext i j
    simp only [ofHAFin, Matrix.map_apply]
    rw [← Bridge_tens_eq]
    rfl
  rw [hm, ← hB]
  have h1 : I.fmat 1 = 1 := rfl
  rw [h1, Matrix.map_one _ (map_zero _) (map_one _)]
  rfl

theorem finPart_eq (I : AutInst) (hb : AdBridgeIso I) (s : I.Ginf) (x : I.Gf) :
    (splitA I.cm.sig I.J (toHA I hb (s, x))).2 = tf I hb x := by
  unfold tf
  rw [show ((s, x) : I.GA) = (s, 1) * (1, x) by ext <;> simp, map_mul, map_mul, Prod.snd_mul,
    finPart_inf_one I hb s, one_mul]

theorem one_mem_Kg (I : AutInst) (g : ℕ) : (1 : I.Gf) ∈ I.Kg g := by
  refine ⟨?_, fun y _ => ⟨0, zero_mem _, by simp [Formalism.MainNotions.S.AutInst.fmat]⟩⟩
  show _ ∈ Formalism.UG.stabGL I.Lf
  simpa using one_mem (Formalism.UG.stabGL I.Lf)

theorem level_subgroup_isOpen {D : D7} (X : HidaSetting D) (hL : X.LevelSubgroupNormalized) (hK : X.LevelSubgroupCharacter) :
    IsOpen (X.K2 : Set X.B.I.Gf) := by
  have hg1 : 1 ≤ X.B.g := by
    rw [X.g_eq]
    exact Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
  have hKg : IsOpen (X.B.I.Kg X.B.g : Set X.B.I.Gf) := X.B.I.topf_open X.B.g hg1
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have ho : IsOpen ((fun y => x⁻¹ * y) ⁻¹' (X.B.I.Kg X.B.g : Set X.B.I.Gf)) :=
    hKg.preimage (continuous_const.mul continuous_id)
  refine Filter.mem_of_superset (ho.mem_nhds (by simpa using one_mem_Kg X.B.I X.B.g)) ?_
  intro y hy
  have h2 := hK.2.1 x hx _ (hL.1 _ hy).1
  simpa using h2

theorem conjugate_level_isOpen (hP : FinProjOpen) {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)
    (hK : X.LevelSubgroupCharacter) (hL : X.LevelSubgroupNormalized) (w : D.what₂.Word) :
    IsOpen (K2u X hb w) := by
  set a := X.xu w
  have hU : IsOpen ((fun y => a * y * a⁻¹) '' X.K2) := by
    have e : (fun y => a * y * a⁻¹) '' X.K2 = (fun y => a⁻¹ * y * a) ⁻¹' X.K2 := by
      ext y
      simp only [Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨k, hk, rfl⟩
        simpa [mul_assoc] using hk
      · intro hy
        exact ⟨a⁻¹ * y * a, hy, by group⟩
    rw [e]
    exact (level_subgroup_isOpen X hL hK).preimage ((continuous_const.mul continuous_id).mul continuous_const)
  have hW : IsOpen ((toHA X.B.I hb) '' (Set.univ ×ˢ ((fun y => a * y * a⁻¹) '' X.K2))) :=
    (toHA X.B.I hb).toHomeomorph.isOpenMap _ (isOpen_univ.prod hU)
  have e : K2u X hb w = (fun h : HAd X.B.I => (splitA X.B.I.cm.sig X.B.I.J h).2) ''
      ((toHA X.B.I hb) '' (Set.univ ×ˢ ((fun y => a * y * a⁻¹) '' X.K2))) := by
    have hom : ∀ k, tf X.B.I hb (a * k * a⁻¹) = finHA X hb a * finHA X hb k * (finHA X hb a)⁻¹ := by
      intro k
      show tfHom X.B.I hb (a * k * a⁻¹) = tfHom X.B.I hb a * tfHom X.B.I hb k * (tfHom X.B.I hb a)⁻¹
      rw [map_mul, map_mul, map_inv]
    ext h
    constructor
    · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      refine ⟨toHA X.B.I hb (1, a * k * a⁻¹), ⟨(1, a * k * a⁻¹), ⟨trivial, k, hk, rfl⟩, rfl⟩, ?_⟩
      show (splitA X.B.I.cm.sig X.B.I.J (toHA X.B.I hb (1, a * k * a⁻¹))).2 = _
      rw [finPart_eq, hom]
    · rintro ⟨_, ⟨⟨s, x⟩, ⟨-, k, hk, rfl⟩, rfl⟩, rfl⟩
      show (splitA X.B.I.cm.sig X.B.I.J (toHA X.B.I hb (s, a * k * a⁻¹))).2 ∈ K2u X hb w
      rw [finPart_eq, hom]
      exact ⟨finHA X hb k, ⟨k, hk, rfl⟩, rfl⟩
  rw [e]
  exact hP X.B.I _ hW

theorem k2uOpenH_of (hP : FinProjOpen) : ConjugateLevelOpenUnitary := by
  unfold ConjugateLevelOpenUnitary
  intro D X hb hK _ hL w
  exact (conjugate_level_isOpen hP X hb hK hL w).preimage continuous_subtype_val

theorem haarIdxGlob_of_finProj (hP : FinProjOpen) : HaarIdxGlob :=
  haarIdxGlob_of (k2uOpenH_of hP)

def EvalVOpen : Prop :=
  ∀ (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)), IsOpenMap (haMap I.cm.sig I.J (evalV I.F v))

theorem k2vOpenS_of (hP : FinProjOpen) (hE : EvalVOpen) : ParabolicLevelOpenLocal := by
  intro D X hb hK _ hL w p
  exact ((hE X.B.I p.1) _ (conjugate_level_isOpen hP X hb hK hL w)).preimage continuous_subtype_val

theorem haarIdxLoc_of_open (hP : FinProjOpen) (hE : EvalVOpen) : HaarIdxLoc :=
  haarIdxLoc_of (k2vOpenS_of hP hE)

end MassDataLevelSSteps
