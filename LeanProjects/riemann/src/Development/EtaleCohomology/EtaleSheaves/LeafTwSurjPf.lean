import Development.EtaleCohomology.EtaleSheaves.LeafTwSecPf
import Development.EtaleCohomology.TateTwists.EtaleLocallyExistsPrimitiveRootOfUnityOfInvertib

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4 LateralTheory.E.LeafTwSecPf

namespace LateralTheory.E.LeafTwSurjPf

variable {q : ℕ} {B : Type} [CommRing B] (ζ : Prim q B) (k : ℤ)

theorem mem_add {U : Over (Spec (CommRingCat.of B))} (s t : ToType ((Pr q k _).obj (op U)))
    (hs : Presheaf.imageSieve (cmap ζ k) s ∈ Scheme.etaleTopology.over _ U)
    (ht : Presheaf.imageSieve (cmap ζ k) t ∈ Scheme.etaleTopology.over _ U) :
    Presheaf.imageSieve (cmap ζ k) (s + t) ∈ Scheme.etaleTopology.over _ U := by
  refine GrothendieckTopology.superset_covering _ ?_ (GrothendieckTopology.intersection_covering _ hs ht)
  rintro V f ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  exact ⟨a + b, by rw [map_add, ha, hb, map_add]⟩

theorem mem_smul {U : Over (Spec (CommRingCat.of B))} (c : ULift.{1} (ZMod q)) (s : ToType ((Pr q k _).obj (op U)))
    (hs : Presheaf.imageSieve (cmap ζ k) s ∈ Scheme.etaleTopology.over _ U) :
    Presheaf.imageSieve (cmap ζ k) (c • s) ∈ Scheme.etaleTopology.over _ U := by
  refine GrothendieckTopology.superset_covering _ ?_ hs
  rintro V f ⟨a, ha⟩
  exact ⟨c • a, by rw [map_smul, ha, map_smul]⟩

theorem mem_zero {U : Over (Spec (CommRingCat.of B))} :
    Presheaf.imageSieve (cmap ζ k) (0 : ToType ((Pr q k _).obj (op U))) ∈ Scheme.etaleTopology.over _ U := by
  refine GrothendieckTopology.superset_covering _ ?_ (GrothendieckTopology.top_mem _ U)
  rintro V f -
  exact ⟨0, by rw [map_zero, map_zero]⟩

theorem rel_single {A : Type} [CommRing A] (ζ' ξ : Prim q A) (a : (ZMod q)ˣ) (h : ξ.1 = ζ'.1 ^ (a : ZMod q).val) :
    Submodule.Quotient.mk (p := twRel q k A) (Finsupp.single ξ 1) =
      (ULift.up ((a ^ k : (ZMod q)ˣ) : ZMod q)) • Submodule.Quotient.mk (p := twRel q k A) (Finsupp.single ζ' 1) := by
  have hm : Finsupp.single ξ 1 - Finsupp.single ζ' (ULift.up ((a ^ k : (ZMod q)ˣ) : ZMod q)) ∈ twRel q k A :=
    Submodule.subset_span ⟨ζ', ξ, a, h, rfl⟩
  rw [← Submodule.Quotient.mk_smul, Finsupp.smul_single, Submodule.Quotient.eq]
  convert hm using 3
  first | rfl | (ext1; simp)

theorem rel_map {A A' : Type} [CommRing A] [CommRing A'] (φ : Prim q A → Prim q A') (ζ' ξ : Prim q A)
    (a : (ZMod q)ˣ) (h : (φ ξ).1 = (φ ζ').1 ^ (a : ZMod q).val) :
    Submodule.Quotient.mk (p := twRel q k A') (Finsupp.mapDomain φ (Finsupp.single ξ 1)) =
      (ULift.up ((a ^ k : (ZMod q)ˣ) : ZMod q)) •
        Submodule.Quotient.mk (p := twRel q k A') (Finsupp.mapDomain φ (Finsupp.single ζ' 1)) := by
  rw [Finsupp.mapDomain_single, Finsupp.mapDomain_single]
  exact rel_single k _ _ a h

theorem mem_single [NeZero q] (U : Over (Spec (CommRingCat.of B))) (ξ : Prim q Γ(U.left, ⊤)) :
    Presheaf.imageSieve (cmap ζ k)
      (Submodule.Quotient.mk (p := twRel q k Γ(U.left, ⊤)) (Finsupp.single ξ 1) : ToType ((Pr q k _).obj (op U)))
      ∈ Scheme.etaleTopology.over _ U := by
  obtain ⟨S, hS, hP⟩ := LateralTheory.EtaleFoundations.PrimLocPf.part2 q U.left (Prim.map (ρ U) ζ) ξ
  rw [GrothendieckTopology.mem_over_iff]
  refine GrothendieckTopology.superset_covering _ ?_ hS
  intro W g hg
  rw [Sieve.overEquiv_iff]
  obtain ⟨a, ha⟩ := hP W g hg
  refine ⟨ULift.up ((a ^ k : (ZMod q)ˣ) : ZMod q), ?_⟩
  change LinearMap.toSpanSingleton _ _ (gen ζ k (Over.mk (g ≫ U.hom))) (ULift.up ((a ^ k : (ZMod q)ˣ) : ZMod q)) =
    ((Pr q k _).map (Over.homMk g : Over.mk (g ≫ U.hom) ⟶ U).op).hom
      (Submodule.Quotient.mk (p := twRel q k Γ(U.left, ⊤)) (Finsupp.single ξ 1))
  rw [LinearMap.toSpanSingleton_apply, ← gen_map ζ k (Over.homMk g : Over.mk (g ≫ U.hom) ⟶ U)]
  exact (rel_map k _ _ _ a ha).symm

end LateralTheory.E.LeafTwSurjPf

namespace LateralTheory.E.LeafTwSecPf

theorem LeafTwSurj_of : LeafTwSurj := by
  intro q _ B _ ζ k
  constructor
  intro U s
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (twRel q k Γ(U.left, ⊤)) s
  induction x using Finsupp.induction_linear with
  | zero => exact LateralTheory.E.LeafTwSurjPf.mem_zero ζ k
  | add f g hf hg =>
    rw [Submodule.Quotient.mk_add]
    exact LateralTheory.E.LeafTwSurjPf.mem_add ζ k _ _ hf hg
  | single ξ c =>
    have h : Finsupp.single ξ c = c • Finsupp.single ξ (1 : ULift.{1} (ZMod q)) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [h, Submodule.Quotient.mk_smul]
    exact LateralTheory.E.LeafTwSurjPf.mem_smul ζ k c _ (LateralTheory.E.LeafTwSurjPf.mem_single ζ k U ξ)

end LateralTheory.E.LeafTwSecPf
