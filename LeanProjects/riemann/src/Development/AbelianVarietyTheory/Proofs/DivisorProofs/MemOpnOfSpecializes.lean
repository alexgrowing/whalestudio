import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralPointPullbackComparison
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LocM GlobalTheory.MixedLocalChains GlobalTheory.ShFam.Pad

namespace GlobalTheory.GroupBplus

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {H : Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

def sabMapCast {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f f' : S' ⟶ S} (h : f = f') (m : SABMap t' t f) :
    SABMap t' t f' := h ▸ m

theorem genPt_specializes {X : Scheme.{0}} [IsIntegral X] (q : Sp (Kbar X)) (x : X) : genPt X q ⤳ x := by
  have h1 : genPt X q ⤳ genericPoint X := by
    have : genPt X q ∈ Set.range (X.fromSpecStalk (genericPoint X)) := ⟨_, rfl⟩
    rw [Scheme.range_fromSpecStalk] at this
    exact this
  exact h1.trans (genericPoint_specializes x)

theorem mem_opn_of_specializes (Z : Mdl Y i₀) [IsOpenImmersion (Y Z.i).j] {v : Z.X} {U : Set Z.X} (hU : IsOpen U)
    (hne : U.Nonempty) (hv : ∀ u ∈ U, v ⤳ u) : v ∈ Z.opn := by
  have ho : IsOpen Z.opn := (Y Z.i).j.isOpenEmbedding.isOpen_range.preimage Z.π.continuous
  obtain ⟨u, hu, huU⟩ := Z.dense.inter_open_nonempty U hU hne
  exact (hv u hu).mem_open ho huU

theorem genericType_of_range (Z : Mdl Y i₀) [IsOpenImmersion (Y Z.i).j] {X : Scheme.{0}} [IsIntegral X] (g : X ⟶ Z.X)
    (h : Set.range (genPt X ≫ g ≫ Z.π) ⊆ Set.range (Y Z.i).j) : GenericType Dw g Z.t := by
  set y := IsOpenImmersion.lift (Y Z.i).j (genPt X ≫ g ≫ Z.π) h
  have hy : y ≫ (Y Z.i).j = genPt X ≫ g ≫ Z.π := IsOpenImmersion.lift_fac _ _ _
  set s₀ := y ≫ pullback.fst (Xo Z.i.l).s (spMap (IntermediateField.inclusion Z.i.c.le).toRingHom) ≫ (Xo Z.i.l).s
  have hs : spMap (Spec.preimage s₀).hom = s₀ := by
    change Spec.map (CommRingCat.ofHom (Spec.preimage s₀).hom) = s₀
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  obtain ⟨o', ⟨mo⟩⟩ := GlobalTheory.obj_pull E H Dw Z.i.l _ _ (baseKA Z.i.l) (baseKA Z.i.l) (RingHom.id _) _ _ _
    (spMap (Spec.preimage s₀).hom) y rfl rfl (by rw [hs]; change _ = s₀ ≫ Spec.map (𝟙 _); rw [Spec.map_id, Category.comp_id]) (Y Z.i).oF
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ y (Y Z.i).m mo.toSABMap
  obtain ⟨m', -⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ Z.π (genPt X ≫ g) Z.tMap
    (sabMapCast (hy.trans (Category.assoc _ _ _).symm) n)
  exact genericType_of_obj (Spec.preimage s₀).hom o' m'

theorem genericAt {D : Formalism.BasicNotions.D7} {A : GlobalTheory.ShFam.Amb D} {N j : ℕ} {S : GlobalTheory.ShFam.Sig A N j} {κ : GlobalTheory.ShFam.Lv A}
    {p : ℕ} {hp : p.Prime} {W : ValuationSubring ℂ} {hW : (p : ℂ) ∈ W.nonunits} (z : AdmAt S κ hp hW) : GenericAt z := by
  haveI := isDiscreteValuationRing_V z.Z.i.c hp hW
  intro c B f
  haveI : IsOpenImmersion ((S.sys.Y p W hp hW) z.Z.i).j := GlobalTheory.TriplesAlong.isOpenImmersion_j W _
  refine genericType_of_range z.Z _ ?_
  rintro _ ⟨q, rfl⟩
  have hv := mem_opn_of_specializes z.Z (v := (f.f ≫ (nmodel z.Z).compι c) (genPt B.X q))
    (U := Set.range ((nmodel z.Z).compι c)) (NModel.Comp.opens c).ι.isOpenEmbedding.isOpen_range
    ⟨_, ⟨genericPoint ((nmodel z.Z).comp c).X, rfl⟩⟩ (by
      rintro _ ⟨a, rfl⟩
      obtain ⟨x, rfl⟩ := f.surjective.surj a
      exact (genPt_specializes q x).map (f.f ≫ (nmodel z.Z).compι c).continuous)
  exact hv

theorem genericSt : GenericSt := fun _ _ _ _ _ _ _ _ _ z => genericAt z

theorem groupAllSt_of_groupSt (h : GroupSt) : GroupAllSt := h.all genericSt

end GlobalTheory.GroupBplus

end
