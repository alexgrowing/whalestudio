import Formalism.SharpRestriction.LevelLetterCocycles.SecondRankCount
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GeneratorBoundOfHypotheses

noncomputable section

namespace Formalism.MainNotions.N.Ln34.RankLink

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem toLA_range_le (T : LocLat G Qp LL O) (π' : LetA O n) (c : ZMod n)
    (S : Submodule O (LcQ W T π' c)) :
    LinearMap.range (toLA W T π' c S) ≤ LinearMap.range (toLA W T π' c ⊤) := by
  have e : toLA W T π' c S =
      toLA W T π' c ⊤ ∘ₗ TensorProduct.map LinearMap.id (Submodule.inclusion le_top) := by
    apply TensorProduct.ext'
    intro x s
    simp [toLA, TensorProduct.map_tmul]
  rw [e]
  exact LinearMap.range_comp_le_range _ _

theorem lamLA_le (T : LocLat G Qp LL O) (π' Eπ : LetA O n) (h' : ℕ) (c : ZMod n)
    (S : Submodule O (LcQ W T π' c)) : LamLA W T π' Eπ h' c S ≤ LamLA W T π' Eπ h' c ⊤ := by
  unfold LamLA
  exact Submodule.comap_mono (toLA_range_le W T π' c S)

theorem invL_le (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n)
    (h' : ℕ) (c : ZMod n) (S : Submodule O (LcQ W T π' c)) :
    InvL W T Pt π' Eπ h' c S ≤ LamLA W T π' Eπ h' c ⊤ := by
  unfold InvL
  exact le_trans inf_le_left (lamLA_le W T π' Eπ h' c S)

def iota (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n)
    (h' : ℕ) (c : ZMod n) (S : Submodule O (LcQ W T π' c)) :
    IIrest W T Pt π' Eπ h' c S →ₗ[O] Formalism.MainNotions.N.Ln34.QL W T Pt π' Eπ h' c :=
  Submodule.mapQ _ _ (Submodule.inclusion (invL_le W T Pt π' Eπ h' c S)) (fun x hx => by
    simpa [Submodule.mem_comap] using hx)

theorem iota_inj (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n)
    (h' : ℕ) (c : ZMod n) (S : Submodule O (LcQ W T π' c)) :
    Function.Injective (iota W T Pt π' Eπ h' c S) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro y hy
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [LinearMap.mem_ker] at hy
  unfold iota at hy
  rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hy
  rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
  simpa [Submodule.mem_comap] using hy

theorem rank_link_of_model [IsDomain O] [IsPrincipalIdealRing O] (T : LocLat G Qp LL O)
    (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n) (h' : ℕ) (c : ZMod n)
    (hQ : ModelQ W T Pt π' Eπ h' c) (hR : SecondRankCount W T Pt π' Eπ h' c) : SecondPropositionFree W T Pt π' Eπ h' c := by
  intro S
  obtain ⟨hfin, htf⟩ := hQ
  have hinj := iota_inj W T Pt π' Eπ h' c S
  haveI : Module.Finite O (Formalism.MainNotions.N.Ln34.QL W T Pt π' Eπ h' c) := hfin
  haveI : IsNoetherian O (Formalism.MainNotions.N.Ln34.QL W T Pt π' Eπ h' c) :=
    isNoetherian_of_isNoetherianRing_of_finite O _
  haveI hfinI : Module.Finite O (IIrest W T Pt π' Eπ h' c S) :=
    Module.Finite.of_injective (iota W T Pt π' Eπ h' c S) hinj
  haveI : NoZeroSMulDivisors O (Formalism.MainNotions.N.Ln34.QL W T Pt π' Eπ h' c) := by
    refine ⟨fun {a q} h => ?_⟩
    by_cases ha : a = 0
    · exact Or.inl ha
    · exact Or.inr (htf a q ha h)
  haveI : NoZeroSMulDivisors O (IIrest W T Pt π' Eπ h' c S) :=
    Function.Injective.noZeroSMulDivisors _ hinj (map_zero _) (fun a x => map_smul _ a x)
  exact ⟨hfinI, Module.free_of_finite_type_torsion_free', hR S⟩

end Local

set_option maxHeartbeats 1000000 in
theorem rank_link_holds : Formalism.MainNotions.N.Ln34.SecondPropositionOfRank := by
  intro D HW hM hR l _ hl K LL hG π' E hp T h' hh hC hJ c
  haveI := Formalism.MainNotions.N.Ln34.GenPf.isDVR (D.loc l) LL
  exact rank_link_of_model _ T _ π' _ h' c (hM l hl K LL hG π' E hp h' hh T hC hJ c)
    (hR l hl K LL hG π' E hp T h' hh hC hJ c)

end Formalism.MainNotions.N.Ln34.RankLink

end
