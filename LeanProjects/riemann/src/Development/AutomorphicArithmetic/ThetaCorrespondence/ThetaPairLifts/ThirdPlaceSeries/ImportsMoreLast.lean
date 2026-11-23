import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftThroughCompletionIso
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.LiftOther
end GlobalTheory.LiftOther
namespace GlobalTheory.LiftOther
theorem main_alt_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (i : D.nd.Loc) (PI : D.naut.AV i) (k : Fin 2) (v : D.nd.PlG k) (s : SplitPlace D.host.E), s.w = D.naut.plGw k v → ∀ c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E, Continuous c → (∀ x : D.host.E, c (s.i x) = algebraMap D.host.E (s.w.adicCompletion D.host.E) x) → ∀ L : G0g D.nd → GAf D.host.E D.R.nV, IsTypeGroupBlockLift D D.R.nV L → ∀ F ∈ D.naut.typeV i PI, ∀ (h : GL (Fin D.R.r) (ZMod (D.host.g k))) (g : G0g D.nd), g ⟨k, v⟩ = h → (∀ kv, kv ≠ ⟨k, v⟩ → g kv = 1) → ∃ x : GAf D.host.E D.R.nV, TrivOutside {s.v} x ∧ IsLiftN h (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) ∧ NG.rt D.host.E D.R.nV (L g) ((P.M.loc i).real F) = NG.rt D.host.E D.R.nV x ((P.M.loc i).real F) := by
  intro hL D P i PI k v s hs c hc hcs L hLift F hF h g hg1 hg2
  classical
  obtain ⟨x, hxT, hxe⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq D.R.nV s (s.loc D.R.nV (L g))
  refine ⟨x, hxT, ?_, ?_⟩
  · rw [hxe]
    have := ((hLift g).2 ⟨k, v⟩ s hs)
    rw [hg1] at this
    exact isLiftN_map' s c hc hcs _ _ h _ this
  obtain ⟨hj1, hj2⟩ := D.nd.j_range i
  let j : Fin D.R.m := ⟨D.nd.j i - 1, by omega⟩
  have hj : j.1 + 1 = D.nd.j i := by simp only [j]; omega
  let K : Subgroup (GAf D.host.E D.R.nV) := (P.M.loc i).χ.ker.map (P.M.loc i).J.subtype
  set y := x⁻¹ * L g with hy
  have hsv : s.v ∈ PendOf.gPl D := ⟨⟨k, v⟩, by rw [← hs]; exact s.w_under⟩
  have hfin := gPl_finite D
  let T := hfin.toFinset.erase s.v
  have hyT : TrivOutside (T : Set _) y := by
    intro w hw
    rw [map_inv_mul]
    by_cases hws : w = s.v
    · subst hws
      rw [GlobalTheory.T.splitPlace_component_unitaryAdelic_determined s (L g) x hxe.symm]
      exact map_inv_mul_self _ x
    · have hwg : w ∉ PendOf.gPl D := by
        intro hwg; apply hw; simp [T, hws, hwg]
      rw [(hLift g).1 w hwg]
      have hx1 := hxT w (by simpa using hws)
      have e := map_inv_mul_self w x
      rw [hx1, mul_one] at e
      rw [e, mul_one]
  have hyK : y ∈ K := by
    refine GlobalTheory.T.mem_subgroup_of_trivOutside_of_local_points K T y hyT fun w hw => ?_
    have hwne : w ≠ s.v := (Finset.mem_erase.1 hw).1
    have hwg : w ∈ PendOf.gPl D := hfin.mem_toFinset.1 (Finset.mem_erase.1 hw).2
    obtain ⟨kv, hkv⟩ := hwg
    obtain ⟨s', hs'⟩ := GlobalTheory.SplitPlaceOfFixed.exists_splitPlace_plGw D kv
    have hs'v : s'.v = w := over_eq s' (by rw [hs']; exact hkv)
    have hkvne : kv ≠ ⟨k, v⟩ := by
      rintro rfl
      apply hwne
      rw [← hs'v]
      exact over_eq s' (by rw [hs', ← hs]; exact s.w_under)
    obtain ⟨p, hpT, hpe⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq D.R.nV s' (s'.loc D.R.nV y)
    have hloc : s'.loc D.R.nV y = s'.loc D.R.nV (L g) := by
      rw [hy, map_mul]
      have : s'.loc D.R.nV x⁻¹ = 1 := by
        rw [map_inv]
        rw [loc_eq_one_of_compAt' s' x (hxT _ (by rw [hs'v]; simpa using hwne)), inv_one]
      rw [this, one_mul]
    have hlift := (hLift g).2 kv s' hs'
    rw [hg2 kv hkvne, ← hloc, ← hpe] at hlift
    obtain ⟨ψ₀, ξ, hψ, -, hU⟩ := P.H.level.uni i j hj kv.1 kv.2 s' hs'
    obtain ⟨hpJ, hpχ⟩ := GlobalTheory.T.blockLiftIdentity_mem_unipotentLevel_character_one (P.M.loc i).J (P.M.loc i).χ s' D.R.r (D.host.g kv.1) (D.host.g_prime kv.1).one_lt
      ψ₀ ξ hψ hU p hpT hlift
    refine ⟨p, ⟨⟨p, hpJ⟩, hpχ, rfl⟩, hs'v ▸ hpT, ?_⟩
    rw [← hs'v]
    exact GlobalTheory.T.splitPlace_component_unitaryAdelic_determined s' p y hpe
  obtain ⟨⟨y', hy'J⟩, hy'χ, hy'e⟩ := hyK
  have hTS : (P.M.loc i).real F ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ := by
    rw [← (P.M.loc i).real_range]; exact LinearMap.mem_range_self _ _
  have hfix : NG.rt D.host.E D.R.nV y ((P.M.loc i).real F) = (P.M.loc i).real F := by
    have e := hTS.2 ⟨y', hy'J⟩
    have h1 : (((P.M.loc i).χ ⟨y', hy'J⟩ : ℂˣ) : ℂ) = 1 := by
      rw [show (P.M.loc i).χ ⟨y', hy'J⟩ = 1 from hy'χ]; rfl
    rw [h1, one_smul] at e
    have hy'y : y' = y := hy'e
    rw [← hy'y]; exact e
  have hLg : L g = x * y := by rw [hy, mul_inv_cancel_left]
  rw [hLg]
  funext z
  have e := congrFun hfix (z * x)
  simp only [NG.rt, LinearMap.coe_mk, AddHom.coe_mk] at e ⊢
  rw [← mul_assoc, e]
end GlobalTheory.LiftOther
end
