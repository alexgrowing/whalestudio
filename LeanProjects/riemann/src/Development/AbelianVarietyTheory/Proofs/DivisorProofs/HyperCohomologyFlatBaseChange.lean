import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsPullForm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechHyperCohomologyAffineLatticeCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAffineCoverInfClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamHypercohomologyOneBaseChangeFlatBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveLiftSemiSecPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsRestTail

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Div.HypFlatBaseChange

theorem square {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {X X' : Scheme.{0}}
    {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X} (w : φ ≫ s = s' ≫ spMap σ)
    {J : Type} [Preorder J] (U : J → X.affineOpens) (hU : Monotone U) (U' : J → X'.affineOpens)
    (hU' : Monotone U') (hle : ∀ i, (U' i).1 ≤ φ ⁻¹ᵁ (U i).1)
    (g : CoefMap σ (hU.functor.op ⋙ OAff s) (hU'.functor.op ⋙ OAff s')) (θ : 𝟭 _ ⟶ g.G)
    (hg : ∀ T b, g.α T (mp (hU.functor.op ⋙ OAff s) (θ.app T) b) =
      GlobalTheory.CechDR.secPull s s' ⟨(U' T.unop, U T.unop), hle _⟩ b) (c : HH1 s) :
    pullHyp1 (CoefMap.restrict (OAff s') hU'.functor.op) (pullHH1 w c) =
      pullHyp1 g (pullHyp1 (CoefMap.restrict (OAff s) hU.functor.op) c) := by
  have hp : Monotone fun i : J ↦ (⟨(U' i, U i), hle i⟩ : Pair φ) := fun i j hij ↦ ⟨hU' hij, hU hij⟩
  have k := congrArg (pullHyp1 (CoefMap.restrict (OPair φ s') hp.functor.op)) (isPull1_pullHH1 w c)
  rw [← pullHyp1_comp, ← pullHyp1_comp] at k
  rw [← pullHyp1_comp]
  have k1 := pullHyp1_eq_of_natTrans
    (F' := hU'.functor.op ⋙ OAff s')
    ((pairRes φ s').comp (CoefMap.restrict (OPair φ s') hp.functor.op))
    (CoefMap.restrict (OAff s') hU'.functor.op) (𝟙 _) (fun T b ↦ mp_id (OAff s') _ b) (pullHH1 w c)
  have k2 := pullHyp1_eq_of_natTrans
    (F' := hU'.functor.op ⋙ OAff s')
    ((pairPull w).comp (CoefMap.restrict (OPair φ s') hp.functor.op))
    ((CoefMap.restrict (OAff s) hU.functor.op).comp g) (Functor.whiskerRight θ hU.functor.op)
    (fun T b ↦ hg T b) c
  exact k1.symm.trans (k.symm.trans k2)

theorem main : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] [Module.Flat R R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (φ : X' ⟶ X) (h : IsPullback φ s' s (spMap (algebraMap R R'))), IsSeparated s → QuasiCompact s → Function.Bijective (liftSemi (pullHH1 h.w)) := by
  intro R R' _ _ _ _ X X' s s' φ h hs hq
  obtain ⟨J, _, _, U, hU, hinf, hcov⟩ := GlobalTheory.exists_finite_affine_cover_infClosed R X s hs hq
  haveI : IsAffineHom φ := MorphismProperty.of_isPullback (P := @IsAffineHom) h.flip inferInstance
  let U' : J → X'.affineOpens := fun i ↦ ⟨φ ⁻¹ᵁ (U i).1, (U i).2.preimage φ⟩
  have hU' : Monotone U' := fun i j hij x hx ↦ hU hij hx
  have hinf' : ∀ i j, (U' (i ⊓ j)).1 = (U' i).1 ⊓ (U' j).1 := fun i j ↦ by
    change φ ⁻¹ᵁ (U (i ⊓ j)).1 = _
    rw [hinf]; rfl
  have hcov' : ⨆ i, (U' i).1 = ⊤ := by
    change ⨆ i, φ ⁻¹ᵁ (U i).1 = ⊤
    rw [← Scheme.Hom.preimage_iSup, hcov]; rfl
  have hp : Monotone fun i : J ↦ (⟨(U' i, U i), le_rfl⟩ : Pair φ) := fun i j hij ↦ ⟨hU' hij, hU hij⟩
  haveI : Finite Jᵒᵖ := Finite.of_equiv J Opposite.equivToOpposite
  haveI : ∀ T T' : Jᵒᵖ, Finite (T ⟶ T') := fun T T' ↦
    Finite.of_injective (β := T'.unop ⟶ T.unop) Quiver.Hom.unop Quiver.Hom.unop_inj
  have hb := GlobalTheory.T.deRhamHypercohomologyOne_baseChange_flat_bijective R R' Jᵒᵖ (hU.functor.op ⋙ OAff s) (hU'.functor.op ⋙ OAff s')
    (fun T ↦ GlobalTheory.CechDR.secPull s s' ⟨(U' T.unop, U T.unop), le_rfl⟩)
    (fun a b ↦ (pairPull h.w).naturality (hp.functor.op.map a) b)
    (fun T ↦ semiHom_secPull h.w ⟨(U' T.unop, U T.unop), le_rfl⟩)
    (fun T f hf ↦ GlobalTheory.CechDR.bijective_liftSemi_secPull R R' X X' s s' φ h ⟨(U' T.unop, U T.unop), le_rfl⟩ rfl f hf)
  have hsq := fun c ↦ square h.w U hU U' hU' (fun _ ↦ le_rfl)
    ⟨𝟭 _, fun T ↦ GlobalTheory.CechDR.secPull s s' ⟨(U' T.unop, U T.unop), le_rfl⟩,
      fun a b ↦ (pairPull h.w).naturality (hp.functor.op.map a) b,
      fun T ↦ semiHom_secPull h.w ⟨(U' T.unop, U T.unop), le_rfl⟩⟩ (𝟙 _)
    (fun T b ↦ congrArg (GlobalTheory.CechDR.secPull s s' ⟨(U' T.unop, U T.unop), le_rfl⟩)
      (mp_id (hU.functor.op ⋙ OAff s) T b)) c
  exact (GlobalTheory.Div.BaseChangeIso.main R R' (HH1 s) (Hyp1 (hU.functor.op ⋙ OAff s)) (HH1 s')
    (Hyp1 (hU'.functor.op ⋙ OAff s')) (pullHyp1 (CoefMap.restrict (OAff s) hU.functor.op))
    (pullHyp1 (CoefMap.restrict (OAff s') hU'.functor.op)) (pullHH1 h.w) _
    (GlobalTheory.T.cech_hyper_cohomology_affine_lattice_cover R X s J U hU hinf hcov) (GlobalTheory.T.cech_hyper_cohomology_affine_lattice_cover R' X' s' J U' hU' hinf' hcov') hsq).2 hb

end GlobalTheory.Div.HypFlatBaseChange
