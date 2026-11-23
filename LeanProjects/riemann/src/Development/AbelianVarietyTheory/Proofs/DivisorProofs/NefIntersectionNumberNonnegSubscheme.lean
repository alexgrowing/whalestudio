import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm
open GlobalTheory.Cartier
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FibreNef

theorem lbIso_pull_comp {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (a : Y ⟶ X) (b : Z ⟶ Y) :
    LBIso (L.pull (b ≫ a)) ((L.pull a).pull b) :=
  LBIso.symm (LBIso.chartPull (chartPullLinComb L a (fun _ : PUnit => b)
      (fun _ => b ≫ a) (fun _ => 1) (𝟙 _) fun _ => (Category.id_comp _).symm)
      (chartPullId _) (PolBaseChange.lbIso_refl (LB.isLB_pull hL _)))

theorem isProjOver_fibre {k : Type} [CommRing k] [Module.Finite ℤ k] {X : Scheme.{0}} {p : X ⟶ Sp k}
    (hp : IsProjOver p) (l : ℕ) [Fact l.Prime] {Z : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i]
    [Algebra (ZMod l) Γ(Z, ⊤)] : IsProjOver (strHom (ZMod l) Z) := by
  obtain ⟨N, e, he, -⟩ := hp
  have hb : IsFinite (spMap (Int.castRingHom k)) := by
    rw [spMap, IsFinite.SpecMap_iff]
    exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
  have P₀ := GlobalTheory.ProjSpace.isPullback_baseChange N (Int.castRingHom k)
  have hf : IsFinite (GlobalTheory.ProjSpace.baseChange N (Int.castRingHom k)) :=
    MorphismProperty.of_isPullback P₀.flip hb
  have hZ : IsProjOver ((i ≫ e ≫ GlobalTheory.ProjSpace.baseChange N (Int.castRingHom k)) ≫ PSpace.str ℤ N) :=
    GlobalTheory.isProjOver_comp_of_isFinite _ ⟨N, 𝟙 _, inferInstance, Category.id_comp _⟩
  obtain ⟨M, φ, hφ, -⟩ := hZ
  have P := GlobalTheory.ProjSpace.isPullback_baseChange M (Int.castRingHom (ZMod l))
  have hc : IsClosedImmersion (spMap (Int.castRingHom (ZMod l))) :=
    IsClosedImmersion.spec_of_surjective _ (ZMod.ringHom_surjective _)
  have hcb : IsClosedImmersion (GlobalTheory.ProjSpace.baseChange M (Int.castRingHom (ZMod l))) :=
    MorphismProperty.of_isPullback P.flip hc
  let ψ := P.lift φ (strHom (ZMod l) Z) (specZIsTerminal.hom_ext _ _)
  have hψ : ψ ≫ PSpace.str (ZMod l) M = strHom (ZMod l) Z := P.lift_snd _ _ _
  have hψ' : ψ ≫ GlobalTheory.ProjSpace.baseChange M (Int.castRingHom (ZMod l)) = φ := P.lift_fst _ _ _
  have : IsClosedImmersion (ψ ≫ GlobalTheory.ProjSpace.baseChange M (Int.castRingHom (ZMod l))) := by
    rw [hψ']; exact hφ
  exact ⟨M, ψ, IsClosedImmersion.of_comp_isClosedImmersion ψ
    (GlobalTheory.ProjSpace.baseChange M (Int.castRingHom (ZMod l))), hψ⟩

theorem isNef_pull_of_nefOver {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} (l : ℕ)
    [Fact l.Prime] {Z : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i] [Algebra (ZMod l) Γ(Z, ⊤)]
    (L : HermLB p) (hL : NefOver L l) : IsNef (ZMod l) (L.B.pull i) := by
  have hLi := LB.isLB_pull L.isLB i
  refine isNef_iff_isClosedImmersion.2 ⟨hLi, fun C c hc hC hd _ => ?_⟩
  letI := algebraΓAlong (ZMod l) c
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have h := hL C (c ≫ i) (ZMod l) hd
  rw [interNumOn_eq_interNum_pull (fun r => rfl) (fun j => by fin_cases j; exact hLi)]
  rw [topSelfIntersection] at h
  refine h.trans_eq (interNum_congr_lbIso _ _ (fun _ => LB.isLB_pull L.isLB _)
    (fun j => by fin_cases j; exact LB.isLB_pull hLi c) fun j => ?_)
  fin_cases j
  exact lbIso_pull_comp L.isLB i c

theorem interNum_nonneg_of_nefOver : Hypotheses2 → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (l : ℕ) [Fact l.Prime] (Z : Scheme.{0}) (i : Z ⟶ X)
    [IsClosedImmersion i] [IsIntegral Z] [Algebra (ZMod l) Γ(Z, ⊤)], topologicalKrullDim Z = D →
    ∀ N : Fin D → HermLB p, (∀ j, NefOver (N j) l) →
      0 ≤ interNum (ZMod l) (structureModule Z) (fun j => (N j).B.pull i) := by
  intro hP k _ X _ p D hX l _ Z i _ _ _ hZ N hN
  haveI := hX.finite
  exact hP.q7.1.interNum_nonneg (isProjOver_fibre hX.isProjOver l i) hZ
    fun j => isNef_pull_of_nefOver l i (N j) (hN j)

end GlobalTheory.FibreNef
