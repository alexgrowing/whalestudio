import Formalism.SharpRestriction.LevelLetterCocycles.ExpansionFormAll
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ConstantCoeffQZeroEqP
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ExistsAutPrim

noncomputable section

namespace Formalism.MainNotions.N.Ln34.CrystallineExponents

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

theorem exponent_recursion_of_dimension (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (h1 : Formalism.MainNotions.ElementDenominator.adm1 D HW F Cm) (h8 : Formalism.MainNotions.ElementDenominator.adm8 D)
    (hdim : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hG : Good K 1 LL)
      (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys ((D.loc l).PD K) T.ρ →
      ∀ (c : ZMod (finrank ℚ_[l] ↥(K0 K))) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1),
        finrank ↥LL.1 ↥(Formalism.MainNotions.DeltaInvariantLattices.ιDi ((HW l).W K 1 LL hG) T c) ≤
          finrank ↥LL.1 ↥(DdRE ((D.loc l).PD K) T.ρ τ)) :
    ExpansionFormAll D HW := by
  intro l _ hl K LL hG T h' hh' hT hJ c y _ hyc hk hexp
  obtain ⟨p1, -, p3, p4, p5, -⟩ := h1 l K 1 LL hG
  obtain ⟨⟨hfc, -⟩, hfd⟩ := h8 l K LL T
  have hFr : IsFractionRing ↥(OL LL) ↥LL.1 := by
    haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
    exact integralClosure.isFractionRing_of_finite_extension ℚ_[l] ↥LL.1
  haveI : FiniteDimensional ↥LL.1
      ↥(DcrisL ((D.loc l).PD K) T.ρ (((HW l).W K 1 LL hG).emb c)) :=
    Submodule.finiteDimensional_of_le (inf_le_left : _ ≤ Dcris ((D.loc l).PD K) T.ρ)
  haveI : FiniteDimensional ↥LL.1 ↥(Formalism.MainNotions.DeltaInvariantLattices.ιDi ((HW l).W K 1 LL hG) T c) := by
    unfold Formalism.MainNotions.DeltaInvariantLattices.ιDi
    infer_instance
  have hyc' : (letE c : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) • y = y := by
    have h := LinearMap.mem_ker.1 hyc
    simpa only [LinearMap.restrictScalars_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero] using h
  refine mem_N_of_exp ((HW l).W K 1 LL hG) hFr ((HW l).W_s K 1 LL hG) T
    (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) (M := fun _ => h') (h := fun _ => h') (p1 T hT) (p3 T hT)
    (p4 T hT) (p5 T _ _ hT fun τ _ _ => hJ τ) c (fun ζ hζ => ?_) (fun τ => (hfd τ).1)
    (hdim l K LL hG T hT c) y hyc' hk hexp
  rw [(D.loc l).PD_p] at hζ
  exact exists_pt D HW hG c ζ hζ

end Formalism.MainNotions.N.Ln34.CrystallineExponents

end
