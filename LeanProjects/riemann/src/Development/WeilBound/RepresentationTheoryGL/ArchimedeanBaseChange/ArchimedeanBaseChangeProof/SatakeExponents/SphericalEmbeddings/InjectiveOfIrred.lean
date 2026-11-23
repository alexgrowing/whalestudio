import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.ExtremeSph
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemCharIdem

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LFun
open GlobalTheory.CuspRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC

namespace PositivityTheory.Rg.BcB.N3.Psl

open PositivityTheory.Rg.BcB.N3

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {G V : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V]

theorem isSmooth_sub {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) (S : Subrepresentation ρ) :
    IsSmooth S.toRepresentation := by
  intro y
  have e : {g : G | S.toRepresentation g y = y} = {g : G | ρ g (y : V) = y} := by
    ext g
    simp only [Set.mem_ofPred_eq]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  rw [e]
  exact hρ (y : V)

theorem injective_of_irred {W : Type} [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ G V}
    {σ : Representation ℂ G W} (hi : ρ.IsIrreducible) (f : ρ.IntertwiningMap σ) (hf : f ≠ 0) :
    Function.Injective f := by
  have := hi
  exact (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right hf

theorem coe_mem_fixed {ρ : Representation ℂ G V} (S : Subrepresentation ρ) {K : Subgroup G}
    {s : S.toSubmodule} (hs : s ∈ fixed S.toRepresentation K) : s.1 ∈ fixed ρ K :=
  GlobalTheory.LGrp.mem_fixed.2 fun g hg => congrArg Subtype.val (GlobalTheory.LGrp.mem_fixed.1 hs g hg)

theorem hI {W : Type} [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (f : ρ.IntertwiningMap σ) (g : G) (y : V) : f (ρ g y) = σ g (f y) :=
  Representation.IntertwiningMap.isIntertwining _ _ f g y

set_option maxHeartbeats 4000000 in
theorem satLink : SatLink := by
  intro E _ _ w c n N h σ P ξ hq hsph ⟨f, hf⟩
  have hKO : ∀ m, KGL w m = KO (w.adicCompletion E) (Fin m) := fun m => (SphCompletion.KO_completion w m).symm
  have hc : IsCompact (KO (w.adicCompletion E) (Fin n) : Set (GL (Fin n) (w.adicCompletion E))) :=
    GlobalTheory.SplitFlip.isCompact_KO

  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hsph
  have hfi := injective_of_irred P.irred f hf

  have hy : f x ∈ fixed (iP (k := w.adicCompletion E) ξ) (KO _ (Fin n)) :=
    GlobalTheory.LGrp.mem_fixed.2 fun g hg => by rw [← hI f, GlobalTheory.LGrp.mem_fixed.1 hx g hg]
  have hy0 : f x ≠ 0 := fun e => hx0 (hfi (e.trans (map_zero f).symm))
  have hφ : Formalism.UG.IsSpherical E w (fun i => (ξ i : ℂ)) (f x).1.1 :=
    (SphCompletion.isSpherical_iff E w n ξ _).2 ⟨f x, hy, rfl⟩
  have hφ0 : (f x).1.1 ≠ 0 := fun e => hy0 (Subtype.ext (Subtype.ext e))
  have hsatφ := isSatVecGL_of_isSpherical (w := w) hφ hφ0
  have hsatY : IsSatVecGL w (iP (k := w.adicCompletion E) ξ) (f x) (Finset.univ.val.map ξ) :=
    IsSatVecGL.of_map (ρ' := rightReg ℂ _ ℂ) ((Submodule.subtype _).comp (Submodule.subtype _))
      (fun _ _ => rfl) (fun u v e => Subtype.ext (Subtype.ext e)) hsatφ
  have hsatX : IsSatVecGL w P.ρ x (Finset.univ.val.map ξ) :=
    IsSatVecGL.of_map f.toLinearMap (fun g y => hI f g y) hfi hsatY

  obtain ⟨S, q, hqs⟩ := hq
  obtain ⟨s0, hs0⟩ := hqs x
  have hSs : IsSmooth S.toRepresentation := isSmooth_sub (isSmooth_parInd _ _) S
  set s := GlobalTheory.LocGL.idem hSs hc s0 with hsdef
  have hqs' : q s = x := by
    rw [hsdef, GlobalTheory.LocGL.map_idem hSs P.smooth hc q s0, hs0, GlobalTheory.LocGL.idem_of_mem P.smooth hc hx]
  have hsfix : s ∈ fixed S.toRepresentation (KO _ (Fin n)) := GlobalTheory.LocGL.idem_mem hSs hc s0
  have htfix : s.1 ∈ fixed (locProd h w σ) (KGL w n) := by
    rw [hKO]
    exact coe_mem_fixed S hsfix
  have ht0 : s.1 ≠ 0 := fun e => hx0 (by rw [← hqs', show s = 0 from Subtype.ext e, map_zero])
  obtain ⟨B, hB, hsat⟩ := GlobalTheory.SatInd.exists_sat_multiProd h (fun i => (σ i).smooth) (fun i => (σ i).irred) htfix ht0
  have hsatS : IsSatVecGL w S.toRepresentation s (∑ i, B i) :=
    IsSatVecGL.of_map (S.toSubmodule.subtype) (fun _ _ => rfl) Subtype.val_injective hsat
  have hsatX' : IsSatVecGL w P.ρ x (∑ i, B i) := by
    have := hsatS.map q.toLinearMap (fun g y => hI q g y) (by
      show q s ≠ 0
      rw [hqs']; exact hx0)
    rwa [show q.toLinearMap s = x from hqs'] at this
  exact ⟨fun i => (hB i).1, B, hB, hsatX'.unique hsatX⟩

end PositivityTheory.Rg.BcB.N3.Psl
