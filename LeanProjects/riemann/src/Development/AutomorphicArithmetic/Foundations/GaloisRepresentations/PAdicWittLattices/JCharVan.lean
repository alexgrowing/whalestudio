import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitDesc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyBijectiveOfSupportBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafOfRingFunctorSectionsLocallyBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleMemIffPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyCoefficientMapFunctorialAdditive

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace UpperTheory.Gal.G3

private theorem prim_isEmpty {k : Type} [Field k] {q : ℕ} (hq : (q : k) = 0) {V : Scheme.{0}} (v : V) (f : V ⟶ sp k) :
    IsEmpty (Prim q Γ(V, ⊤)) := by
  constructor
  rintro ⟨ζ, hu, -⟩
  have h0 : ((q : ℕ) : Γ(sp k, ⊤)) = 0 := by
    rw [← map_natCast (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom,
      show ((q : ℕ) : CommRingCat.of k) = 0 from hq, map_zero]
  have h1 : ((q : ℕ) : Γ(V, ⊤)) = 0 := by
    rw [← map_natCast f.appTop.hom, h0, map_zero]
  rw [h1] at hu
  haveI : Nonempty (⊤ : V.Opens) := ⟨⟨v, trivial⟩⟩
  exact not_isUnit_zero hu

private theorem sec_subsingleton {k : Type} [Field k] {q : ℕ} (hq : (q : k) = 0) (i : ℤ) {U : Scheme.{0}} (f : U ⟶ sp k) :
    Subsingleton (Sec (tw q i) U) := by
  suffices h : ∀ x : Sec (tw q i) U, x = 0 from ⟨fun x y => by rw [h x, h y]⟩
  intro x
  let S : Sieve U :=
    { arrows := fun V j => Sec.res j x = 0
      downward_closed := by
        intro V W j hj g
        have hj' : ModuleCat.Hom.hom ((tw q i).obj.map j.op) x = 0 := hj
        show ModuleCat.Hom.hom ((tw q i).obj.map (g ≫ j).op) x = 0
        rw [op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply, hj', map_zero] }
  have hS : S ∈ Scheme.etaleTopology U := by
    rw [GlobalTheory.etale_mem_iff_points]
    intro u
    obtain ⟨V, j, v, m, -, hj, hv, hm⟩ := (GlobalTheory.ofRings_loc (ZMod q) (twF q i) U).1 x u
    refine ⟨V, j, v, hj, hv, ?_⟩
    refine hm.symm.trans ?_
    haveI : IsEmpty (Prim q Γ(V, ⊤)) := prim_isEmpty hq v (j ≫ f)
    obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective (twRel q i Γ(V, ⊤)) m
    rw [Subsingleton.elim g 0, Submodule.Quotient.mk_zero]
    exact map_zero _
  have hsh := (isSheaf_iff_isSheaf_of_type _ _).mp
    ((Presheaf.isSheaf_iff_isSheaf_forget (J := Scheme.etaleTopology) (P' := (tw q i).obj)
      (forget (ModuleCat.{1} (ULift.{1, 0} (ZMod q))))).mp (tw q i).cond)
  exact (hsh S hS).isSeparatedFor (fun _ _ _ => 0) x 0 (fun V j hj => hj)
    (fun V j hj => show ModuleCat.Hom.hom ((tw q i).obj.map j.op) 0 = 0 from map_zero _)

private theorem ht_subsingleton {k : Type} [Field k] {q : ℕ} (hq : (q : k) = 0) {X : Scheme.{0}} (p : X ⟶ sp k) (n i : ℤ) :
    Subsingleton (Ht q (sch.obj X) n i) := by
  have hbij := GlobalTheory.T.etaleCohomology_bijective_of_support_bijective (ZMod q) (sch.obj X) (0 : tw q i ⟶ tw q i) (fun U hU => by
    obtain ⟨g⟩ := hU
    have g' : U ⟶ X := g
    haveI := sec_subsingleton hq i (g' ≫ p)
    exact ⟨fun a b _ => Subsingleton.elim a b, fun b => ⟨b, Subsingleton.elim _ _⟩⟩) n
  have hz : HK.post (ZMod q) ((chains (ZMod q)).obj (sch.obj X)) (0 : tw q i ⟶ tw q i) n = 0 := by
    have h := PostFun.post_add ((chains (ZMod q)).obj (sch.obj X)) (0 : tw q i ⟶ tw q i) 0 n
    rw [add_zero] at h
    exact left_eq_add.1 h
  refine ⟨fun a b => hbij.1 ?_⟩
  rw [hz]; rfl

theorem jCharVan : CharVan := by
  intro l _ k _ hl X x n i
  have hs : ∀ m : ℕ, Subsingleton (Ht (l ^ (m + 1)) (sch.obj X) n i) := fun m =>
    ht_subsingleton (k := k) (by push_cast; rw [hl, zero_pow (Nat.succ_ne_zero m)]) x n i
  constructor
  intro a b
  apply Subtype.ext
  funext m
  cases m with
  | zero =>
    rw [← a.2 0, ← b.2 0]
    congr 1
    exact (hs 0).elim _ _
  | succ m => exact (hs m).elim _ _

end UpperTheory.Gal.G3

end
