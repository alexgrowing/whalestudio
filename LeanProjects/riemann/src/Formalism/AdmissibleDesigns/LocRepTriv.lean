import Formalism.AdmissibleDesigns.ExistsUnrDec
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Formalism.BasicNotions Classical

namespace Formalism.MainNotions.N.KUnr

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations

section Loc

variable {O : Type} [CommRing O] [IsDomain O] {Γ : Type} [Group Γ] {M : Type} [AddCommGroup M] [Module O M]

theorem locRep_triv (g : Γ) (x : KHf.MK (O := O) M) :
    KHf.locRep (Representation.trivial O Γ M) g x = x := by
  induction x using LocalizedModule.induction_on with
  | h m s =>
    show LocalizedModule.map (nonZeroDivisors O) (Representation.trivial O Γ M g) (LocalizedModule.mk m s) =
      LocalizedModule.mk m s
    rw [LocalizedModule.map_mk]
    rfl

end Loc

section Rec

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (δO : D.nd.O i)

theorem col_mem (l : K.Col i dc) : K.plOf i dc (K.colIdx i dc l) ∈ dc.col := by
  have h : l.1 ∈ K.plSet i dc := by
    unfold K.plSet
    simp [l.2]
  rw [K.colIdx, K.plOf_idx i dc h]
  exact l.2

theorem unrFinIn (hA : EmbeddingTypes.UnramifiedTrivialH1f i dc) (l : K.Col i dc) : KFin.UnrFinIn i dc δO l := by
  intro f hf
  have hn := col_over i dc l
  refine Submodule.mem_map_of_mem ?_
  show (fun g => KHf.mkK (((KFin.uzOf i dc δO l f hf.1 : _ → _) g))) ∈
    ((KHf.fZ i dc (K.colIdx i dc l) (KHf.locRep (Representation.trivial (D.nd.O i) ↥(KFin.Γc i dc l)
      ↥(Ideal.span {δO})))).restrictScalars (D.nd.O i))
  rw [Submodule.restrictScalars_mem, KHf.fZ_pos i dc _ hn]
  have hU := hA (K.plOf i dc (K.colIdx i dc l)) hn (col_mem i dc l) (TruncatedSeriesCountingIdentities.CoefExt.self i _ hn)
  let Bw := D.nbr i (K.plOf i dc (K.colIdx i dc l)) hn
  let V := KHf.MK (O := D.nd.O i) ↥(Ideal.span {δO})
  let c' : Br.G D.nbr i _ hn → Br.LLw Bw := fun g =>
    KHf.eK Bw (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) (f (Br.iota D.nbr i _ hn g)))
  have hc' : c' ∈ Z1ur (1 : Representation (Br.LLw Bw) (Br.G D.nbr i _ hn) (Br.LLw Bw)) (Br.inert D.nbr i _ hn) := by
    refine ⟨⟨hf.2.2 hn, fun g h => ?_⟩, 0, fun g hg => ?_⟩
    · show c' (g * h) = c' g + c' h
      have h1 : f (Br.iota D.nbr i _ hn g * Br.iota D.nbr i _ hn h) =
          f (Br.iota D.nbr i _ hn g) + f (Br.iota D.nbr i _ hn h) := hf.1 _ _
      simp only [c', map_mul]
      rw [h1, map_add, map_add]
    · show c' g = 0 - 0
      rw [sub_zero]
      show KHf.eK Bw (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) (f (Br.iota D.nbr i _ hn g))) = 0
      rw [hf.2.1 _ hg, map_zero, map_zero]
  have hcf : c' ∈ finiteCocycles (Br.PD D.loc D.nbr i _ hn) (1 : Representation (Br.LLw Bw) (Br.G D.nbr i _ hn) (Br.LLw Bw)) := by
    have hU' : finiteCocycles (Br.PD D.loc D.nbr i _ hn) (1 : Representation (Br.LLw Bw) (Br.G D.nbr i _ hn) (Br.LLw Bw)) =
        Z1ur 1 (Br.inert D.nbr i _ hn) := hU
    rw [hU']
    exact hc'
  let v0 : KHf.TrV (KHf.eK Bw) V := KHf.mkK (⟨δO, Ideal.mem_span_singleton_self δO⟩ : ↥(Ideal.span {δO}))
  let f0 : Br.LLw Bw →ₗ[Br.LLw Bw] KHf.TrV (KHf.eK Bw) V := LinearMap.toSpanSingleton _ _ v0
  have hf0 : Continuous f0 := continuous_id.smul continuous_const
  let ρ' := KHf.repL (KHf.eK Bw) (KHf.locRep (Representation.trivial (D.nd.O i) ↥(KFin.Γc i dc l) ↥(Ideal.span {δO})))
    (Br.iota D.nbr i _ hn)
  have heq : ∀ g x, f0 ((1 : Representation (Br.LLw Bw) (Br.G D.nbr i _ hn) (Br.LLw Bw)) g x) = ρ' g (f0 x) :=
    fun g x => (locRep_triv (Br.iota D.nbr i _ hn g) (f0 x : V)).symm
  have key := (cocyclesFunctorial_holds _ _ _ _ _ _ (Br.PD D.loc D.nbr i _ hn) (Br.LLw Bw) (Br.LLw Bw) (KHf.TrV (KHf.eK Bw) V)
    1 ρ' f0 hf0 heq c').2 hcf
  let lhs : Br.G D.nbr i _ hn → KHf.TrV (KHf.eK Bw) V := fun g =>
    ((KHf.mkK ((KFin.uzOf i dc δO l f hf.1 : ↥(KFin.Γc i dc l) → ↥(Ideal.span {δO})) (Br.iota D.nbr i _ hn g)) : V) :
      KHf.TrV (KHf.eK Bw) V)
  show lhs ∈ finiteCocycles (Br.PD D.loc D.nbr i _ hn) ρ'
  suffices hfun : lhs = ⇑f0 ∘ c' by
    rw [hfun]
    exact key
  funext g
  show _ = f0 (c' g)
  rw [LinearMap.toSpanSingleton_apply]
  show _ = ((KHf.eK Bw).symm (c' g) • (show V from v0) : V)
  simp only [c', RingEquiv.symm_apply_apply]
  rw [algebraMap_smul]
  rw [← map_smul]
  show KHf.mkK ((KFin.uzOf i dc δO l f hf.1 : ↥(KFin.Γc i dc l) → ↥(Ideal.span {δO})) (Br.iota D.nbr i _ hn g)) =
    KHf.mkK _
  congr 1
  apply Subtype.ext
  show δO * f (Br.iota D.nbr i _ hn g) = f (Br.iota D.nbr i _ hn g) * δO
  ring

theorem unrFin (hA : EmbeddingTypes.UnramifiedTrivialH1f i dc) : KHf.UnrFin i dc δO (KFin.uz i dc δO) :=
  KFin.unrFin i dc δO (unrHom i dc) (unrFinIn i dc δO hA)

end Rec

end Formalism.MainNotions.N.KUnr
