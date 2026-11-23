import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassesAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalElementsCommuteDistinctFinitePlacesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalAtPlaceConjProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelElementLocalCoprimeActsTriviallyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCosetProductsCommuteSplitPlaceStatement

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeckeCommFrame

open Classical in

theorem exists_equiv_of_fibre_card {G : Type} [Group G] (K : Subgroup G) (A B : Finset G) (Tr : G → Prop)
    (hcount : ∀ c : G ⧸ K, ((A ×ˢ B).filter (fun x => ((x.1 * x.2 : G) : G ⧸ K) = c)).card =
      ((B ×ˢ A).filter (fun x => ((x.1 * x.2 : G) : G ⧸ K) = c)).card)
    (htr : ∀ s ∈ A, ∀ t ∈ B, ∀ t' ∈ B, ∀ s' ∈ A, (t' * s')⁻¹ * (s * t) ∈ K → Tr ((t' * s')⁻¹ * (s * t))) :
    ∃ σ : A × B ≃ B × A, ∀ x, Tr ((((σ x).1 : G) * (σ x).2)⁻¹ * ((x.1 : G) * x.2)) := by
  classical
  have fib : ∀ (A B : Finset G) (c : G ⧸ K),
      Fintype.card {x : A × B // (((x.1 : G) * x.2 : G) : G ⧸ K) = c} =
        ((A ×ˢ B).filter (fun x => ((x.1 * x.2 : G) : G ⧸ K) = c)).card := by
    intro A B c
    rw [← Fintype.card_coe]
    exact Fintype.card_congr
      { toFun := fun x => ⟨((x.1.1 : G), (x.1.2 : G)), Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨x.1.1.2, x.1.2.2⟩, x.2⟩⟩
        invFun := fun y => ⟨(⟨y.1.1, (Finset.mem_product.1 (Finset.mem_filter.1 y.2).1).1⟩,
          ⟨y.1.2, (Finset.mem_product.1 (Finset.mem_filter.1 y.2).1).2⟩), (Finset.mem_filter.1 y.2).2⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  let f : A × B → G ⧸ K := fun x => (((x.1 : G) * x.2 : G) : G ⧸ K)
  let g : B × A → G ⧸ K := fun x => (((x.1 : G) * x.2 : G) : G ⧸ K)
  have e : ∀ c, {x // f x = c} ≃ {y // g y = c} := fun c =>
    Fintype.equivOfCardEq (by rw [fib A B c, fib B A c]; convert hcount c)
  refine ⟨Equiv.ofFiberEquiv e, fun x => ?_⟩
  have h := Equiv.ofFiberEquiv_map e x
  have hK : (((Equiv.ofFiberEquiv e x).1 : G) * (Equiv.ofFiberEquiv e x).2)⁻¹ * ((x.1 : G) * x.2) ∈ K :=
    QuotientGroup.eq.1 h
  exact htr _ x.1.2 _ x.2.2 _ (Equiv.ofFiberEquiv e x).1.2 _ (Equiv.ofFiberEquiv e x).2.2 hK

theorem commAt_of {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)
    (j : Fin D.R.m) (P : Formalism.CohomologicalDescent.LogSmallConstantBounds.Par) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : CommAt p j P w := by
  intro _ e0 b io ev bs rk sh Lf _ kap chi hc F i i'
  have hN : P.Nr = (Vc D j).rank := by simpa using Fintype.card_congr rk.toEquiv
  have hi1 : 1 ≤ i.1.2 := i.2.1
  have hi2 : i.1.2 ≤ (Vc D j).rank := hN ▸ i.2.2.1
  have hi1' : 1 ≤ i'.1.2 := i'.2.1
  have hi2' : i'.1.2 ≤ (Vc D j).rank := hN ▸ i'.2.2.1
  have hA := (p.R.B.L j (p.R.mu w)).hecke.hA_loc i.1 ⟨hi1, hi2⟩
  have hA' := (p.R.B.L j (p.R.mu w)).hecke.hA_loc i'.1 ⟨hi1', hi2'⟩
  by_cases hv : (plOf p j (p.R.mu w) i.1.1).under (𝓞 D.host.F) = (plOf p j (p.R.mu w) i'.1.1).under (𝓞 D.host.F)
  · exact exists_equiv_of_fibre_card (levJ p j (p.R.mu w)) (hkA p j (p.R.mu w) i.1) (hkA p j (p.R.mu w) i'.1) F.Triv
      (GlobalTheory.T.heckeCosetProducts_commute_splitPlace p j (p.R.mu w) i.1 i'.1 hi1 hi2 hi1' hi2' hv)
      (fun s hs t ht t' ht' s' hs' hK => GlobalTheory.T.levelElement_local_coprime_acts_trivially p j w e0 b io ev bs rk sh Lf kap chi hc i.1 hi1 hi2 i.2.2.2 _ hK
        (GlobalTheory.T.isLocalAtPlace_conj_product (Vc D j) p.R.pl (p.P.A3.A.ok (p.R.mu w)) i.1 i'.1 s t t' s' hv (hA s hs) (hA' t ht) (hA' t' ht') (hA s' hs')))
  · refine ⟨Equiv.prodComm _ _, fun x => ?_⟩
    have hcomm : (x.1 : F.G) * (x.2 : F.G) = (x.2 : F.G) * (x.1 : F.G) :=
      GlobalTheory.T.localElements_commute_distinct_realPlaces (Vc D j) p.R.pl (p.P.A3.A.ok (p.R.mu w)) i.1 i'.1 (x.1 : F.G) (x.2 : F.G) hv (hA _ x.1.2) (hA' _ x.2.2)
    show F.Triv (((x.2 : F.G) * (x.1 : F.G))⁻¹ * ((x.1 : F.G) * (x.2 : F.G)))
    rw [hcomm, inv_mul_cancel]
    exact ⟨one_mem _, map_one _, map_one _⟩

theorem comm : InRange fun _ _ _ _ p j P _ w => SmallAt p j P w → CommAt p j P w :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ =>
    EvPt.of_forall fun _ _ _ p _ _ j P _ _ _ w _ _ _ => commAt_of p j P w⟩⟩

end GlobalTheory.HeckeCommFrame

end
