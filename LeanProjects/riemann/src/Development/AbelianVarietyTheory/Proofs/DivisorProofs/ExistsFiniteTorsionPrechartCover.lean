import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionPrechartStatement
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus.Aff.FinCover

theorem exists_finite_charts (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K]
    [CharZero K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G)
    (N : ℕ) (hN : N ≠ 0) :
    ∃ (Idx : Type) (_ : Finite Idx) (q : Idx → PrimeSpectrum R) (c : ∀ i, PreChart G N (q i)),
      ∀ (k : Type) [Field k] [Algebra R k] (z : Tors G N k), ∃ i, Set.range z.1.left ⊆ (c i).W := by
  classical
  let chart : ∀ q : PrimeSpectrum R, PreChart G N q := fun q => (GlobalTheory.T.exists_torsion_prechart R K G hG N hN q).some
  let e : Sp R ⟶ G.left := (η[G]).left
  let m : G.left ⟶ G.left := (𝟙 G ^ N).left
  have hes : e ≫ G.hom = 𝟙 _ := Over.w (η[G])
  have hms : m ≫ G.hom = G.hom := Over.w (𝟙 G ^ N)
  have hpow : ∀ (B : Type) [CommRing B] [Algebra R B] (z : SpAlg R B ⟶ G), (z ^ N).left = z.left ≫ m := by
    intro B _ _ z
    have h : z ^ N = z ≫ (𝟙 G ^ N) := by rw [comp_pow, Category.comp_id]
    rw [h, Over.comp_left]
  have hone : ∀ (B : Type) [CommRing B] [Algebra R B], (1 : SpAlg R B ⟶ G).left = spMap (algebraMap R B) ≫ e :=
    fun _ _ _ => rfl
  haveI : IsSeparated G.hom := hG.separated
  haveI : IsClosedImmersion (e ≫ G.hom) := by rw [hes]; infer_instance
  haveI : IsClosedImmersion e := IsClosedImmersion.of_comp e G.hom
  haveI : QuasiCompact G.hom := hG.quasiCompact
  haveI : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have hT : IsCompact (Set.range (pullback.fst m e)) :=
    (pullback.fst m e).isClosedEmbedding.isClosed_range.isCompact

  have key : ∀ p : (pullback m e : Scheme), ∃ q : PrimeSpectrum R, pullback.fst m e p ∈ (chart q).W := by
    intro p
    let k := (pullback m e).residueField p
    let f : Spec k ⟶ Sp R := (pullback m e).fromSpecResidueField p ≫ pullback.snd m e
    letI : Algebra R k := (Spec.preimage f).hom.toAlgebra
    have hf : spMap (algebraMap R k) = f := Spec.map_preimage f
    let zl : Spec k ⟶ G.left := (pullback m e).fromSpecResidueField p ≫ pullback.fst m e
    have hzl : zl ≫ G.hom = spMap (algebraMap R k) := by
      rw [hf, ← hms]
      simp only [zl, f, Category.assoc]
      rw [pullback.condition_assoc, hes, Category.comp_id]
    let z0 : SpAlg R k ⟶ G := Over.homMk zl hzl
    have hz0 : z0 ^ N = 1 := by
      apply Over.OverMorphism.ext
      rw [hpow, hone, hf]
      simp only [z0, Over.homMk_left, zl, f, Category.assoc, pullback.condition]
    let q : PrimeSpectrum R := ⟨RingHom.ker (algebraMap R k), RingHom.ker_isPrime _⟩
    refine ⟨q, (chart q).fibre k rfl ⟨z0, hz0⟩ ⟨IsLocalRing.closedPoint k, ?_⟩⟩
    show zl _ = _
    exact (Scheme.Hom.comp_apply _ _ _).trans (congrArg _ (Scheme.fromSpecResidueField_apply p _))

  choose qf hqf using key
  obtain ⟨t, ht⟩ := hT.elim_finite_subcover (fun p => ((chart (qf p)).W : Set G.left)) (fun p => (chart (qf p)).W.isOpen)
    (by rintro _ ⟨p, rfl⟩; exact Set.mem_iUnion.2 ⟨p, hqf p⟩)
  refine ⟨t, inferInstance, fun i => qf i.1, fun i => chart (qf i.1), ?_⟩
  intro k _ _ z
  have hz : z.1.left ≫ m = spMap (algebraMap R k) ≫ e := by
    rw [← hpow, ← hone, z.2]
  let l := pullback.lift z.1.left (spMap (algebraMap R k)) hz
  let s0 : Sp k := IsLocalRing.closedPoint k
  have hs0 : z.1.left s0 ∈ Set.range (pullback.fst m e) :=
    ⟨l s0, by rw [← Scheme.Hom.comp_apply, pullback.lift_fst]⟩
  obtain ⟨p, hp, hW⟩ := Set.mem_iUnion₂.1 (ht hs0)
  refine ⟨⟨p, hp⟩, ?_⟩
  rintro _ ⟨s, rfl⟩
  have hs : s = s0 := by
    have h1 := (s : PrimeSpectrum k).isPrime
    have h2 := (s0 : PrimeSpectrum k).isPrime
    exact PrimeSpectrum.ext ((Ideal.eq_bot_of_prime (s : PrimeSpectrum k).asIdeal).trans
      (Ideal.eq_bot_of_prime (s0 : PrimeSpectrum k).asIdeal).symm)
  rwa [hs]

end GlobalTheory.GroupBplus.Aff.FinCover
