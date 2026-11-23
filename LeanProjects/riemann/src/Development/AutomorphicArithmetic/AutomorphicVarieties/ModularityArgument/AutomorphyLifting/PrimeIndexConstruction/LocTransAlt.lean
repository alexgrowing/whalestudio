import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.LocTrans
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.SatOfVec
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.ExistsContRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocCompR
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.UopSum
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.HkReps
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.FinProj

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd Matrix
open private UpperTheory.V.Sd.Wc.sep_of_sum from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.FinProj
open private UpperTheory.V.Af.Nf.satLoc' from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.SatOfVec
open private UpperTheory.V.Af.RealLocalComponent.exists_comp UpperTheory.V.Af.RealLocalComponent.isotypic from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocCompR

namespace UpperTheory.V.Z.Win.Birth

private theorem level_zero_eq_maximal_compact {F : Type} [Field F] [NumberField F] (w : Pl F) : K1 w 0 = GlobalTheory.LFun.KGL w 2 := by
  ext g
  refine ⟨fun ⟨k, _, e⟩ => ⟨k, e⟩, fun ⟨k, e⟩ => ⟨k, ?_, e⟩⟩
  haveI : Subsingleton (w.adicCompletionIntegers F ⧸ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ 0) :=
    Ideal.Quotient.subsingleton_iff.2 (by simp)
  exact Subsingleton.elim _ _

private theorem scalar_fin {F : Type} [Field F] [NumberField F] (w : Pl F) (x : (w.adicCompletion F)ˣ) :
    finGL F 2 (locGL F 2 w (GeneralLinearGroup.scalar (Fin 2) x)) = GeneralLinearGroup.scalar (Fin 2) (localIdele F w x) := by
  have h := GlobalTheory.CuspRep.finId_det_locGL w (GeneralLinearGroup.scalar (Fin 1) x)
  rw [locGL, GlobalTheory.CuspRep.cornerGL_scalar] at h ⊢
  rw [finGL, GlobalTheory.CuspRep.cornerGL_scalar]
  congr 1
  exact (congrArg (finId F) (GlobalTheory.CuspRep.CG.det_oneByOne _)).symm.trans
    (h.trans (congrArg (localIdele F w) (GlobalTheory.CuspRep.CG.det_oneByOne _)))

private theorem hasU_of_map {F : Type} [Field F] [NumberField F] (w : Pl F) {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ (GL (Fin 2) (w.adicCompletion F)) V}
    {ρ' : Representation ℂ (GL (Fin 2) (w.adicCompletion F)) W} (p : V →ₗ[ℂ] W) (hp : ∀ g y, p (ρ g y) = ρ' g (p y))
    {c : ℕ} {lam : ℂ} {x : V} (h0 : p x ≠ 0) (hx : x ∈ Hi.fixd ρ (K1 w c)) (hU : Uop w ρ c x = lam • x) :
    HasU w ρ' c lam := by
  obtain ⟨N, a, -, h⟩ := Wc.hkReps uopSum F w c
  have hx' : p x ∈ Hi.fixd ρ' (K1 w c) := fun u hu => by rw [← hp, hx u hu]
  refine ⟨p x, h0, hx', ?_⟩
  rw [(h W ρ' _ hx').2]
  have e := (h V ρ x hx).2
  rw [hU] at e
  have e2 := congrArg p e
  rw [map_smul, map_sum] at e2
  rw [e2]
  simp only [hp]

theorem _root_.UpperTheory.V.Z.Win.Birth.locTrans : LocTrans := by
  intro F _ _ _ π w
  refine ⟨fun ⟨x, hx0, hx⟩ => ?_, fun σ hσ => ⟨fun c lam ⟨x, hx0, hx, hU⟩ => ?_, fun ω hω z v => ?_⟩⟩
  · obtain ⟨σ, hσ⟩ := UpperTheory.V.Af.RealLocalComponent.exists_comp admissibleReal π w
    have hi := UpperTheory.V.Af.RealLocalComponent.isotypic π w σ hσ
    obtain ⟨B, hB⟩ := (UpperTheory.V.Af.Nf.satLoc' F 2 w σ).1 (GlobalTheory.CuspRep.LocSph.exists_fixed_of_mem_iSup (π.locRep w) σ.ρ σ.irred
      (fun f : {f : σ.V →ₗ[ℂ] π.V // ∀ g v, f (σ.ρ g v) = π.finPart (locGL F 2 w g) (f v)} => f.1) (fun f => f.2)
      (GlobalTheory.LFun.KGL w 2 : Set _) x hx0 (fun k hk => hx k (level_zero_eq_maximal_compact w ▸ hk)) (hi.2 ▸ Submodule.mem_top))
    exact ⟨B, ((UpperTheory.V.Af.Nf.satLoc' F 2 w σ).2 _ _ hi B).2 hB⟩
  · have hi := UpperTheory.V.Af.RealLocalComponent.isotypic π w σ hσ
    obtain ⟨p, h0, hp⟩ := UpperTheory.V.Sd.Wc.sep_of_sum σ.ρ σ.irred (π.locRep w) hi.2 x hx0
    exact hasU_of_map w p hp h0 hx hU
  · obtain ⟨f, h0, hf⟩ := hσ
    have hinj : LinearMap.ker f = ⊥ := ((isIrreducible_iff σ.ρ).1 σ.irred).2 _ (fun g v hv => by
      rw [LinearMap.mem_ker] at hv ⊢
      rw [hf, hv, map_zero]) |>.resolve_right fun e => h0 (LinearMap.ker_eq_top.1 e)
    refine LinearMap.ker_eq_bot.1 hinj ?_
    rw [hf, map_smul]
    refine Subtype.ext (Subtype.ext (funext fun g => ?_))
    change (f v).1.1 (g * finGL F 2 (locGL F 2 w (GeneralLinearGroup.scalar (Fin 2) z))) = ((ω.loc w z : ℂˣ) : ℂ) * (f v).1.1 g
    rw [scalar_fin, ← GlobalTheory.CuspRep.scalar_comm, hω _ _ (f v).2]
    rfl

end UpperTheory.V.Z.Win.Birth
