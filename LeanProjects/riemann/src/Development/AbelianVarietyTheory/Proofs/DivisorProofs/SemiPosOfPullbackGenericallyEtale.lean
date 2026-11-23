import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtLevi

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef GlobalTheory.Points GlobalTheory.SemiPosBir

namespace GlobalTheory.SemiPosEtale

variable {k : Type} [CommRing k] {X Z : Scheme.{0}} {p : X ⟶ Sp k} {q : Z ⟶ Sp k} {σ : k →+* ℂ}
  {D : ℕ}

theorem exists_map_eq_of_etale (j : Z ⟶ X) [Etale j] (hj : j ≫ p = q) {y : CxPts p σ}
    (hy : y.1 (IsLocalRing.closedPoint ℂ) ∈ Set.range j) :
    ∃ z : CxPts q σ, PtsOver.map j hj _ z = y := by
  obtain ⟨v, hv⟩ := hy
  obtain ⟨w, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := j) (g := y.1) v _ hv
  have : JacobsonSpace ↥(pullback j y.1) := LocallyOfFiniteType.jacobsonSpace (pullback.snd j y.1)
  obtain ⟨c, -, hc⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set ↥(pullback j y.1)))
    ⟨w, trivial⟩ isOpen_univ.isLocallyClosed
  replace hc : IsClosed {c} := hc
  refine ⟨⟨pointOfClosedPoint (pullback.snd j y.1) c hc ≫ pullback.fst j y.1, ?_⟩, Subtype.ext ?_⟩
  · rw [← hj, Category.assoc, pullback.condition_assoc, pointOfClosedPoint_comp_assoc]
    exact y.2
  · change (pointOfClosedPoint (pullback.snd j y.1) c hc ≫ pullback.fst j y.1) ≫ j = y.1
    rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]

def img (j : Z ⟶ X) [Etale j] : X.Opens := ⟨Set.range j, j.isOpenMap.isOpen_range⟩

theorem PosOn.of_etale (j : Z ⟶ X) [Etale j] (hj : j ≫ p = q) {f : CxPts p σ → ℝ}
    {S : Set (CxPts p σ)}
    (h : PosOn D (fun w => f (PtsOver.map j hj _ w)) (PtsOver.map j hj (spMap σ) ⁻¹' S)) :
    PosOn D f (S ∩ ptsIn p σ (img j)) := fun c y hy ξ => by
  obtain ⟨z, rfl⟩ := exists_map_eq_of_etale j hj (mem_ptsIn.1 hy.2.2)
  obtain ⟨W, hW, hzW, e⟩ := exists_isAffineOpen_le z.1 (V := j ⁻¹ᵁ c.U) (c.source_subset hy.1)
  have h₂ : (MvPolynomial.eval₂Hom (algX q W) fun a => (j.appLE _ W e).hom (c.x a)).Etale := by
    rw [← appLE_comp_eval hj e]
    exact RingHom.Etale.stableUnderComposition _ _ c.etale
      (HasRingHomProperty.appLE @Etale j inferInstance ⟨c.U, c.affine⟩ ⟨W, hW⟩ e)
  obtain ⟨c', hc, rfl, hcx⟩ := AlgChart.exists_of_etale (y := z) hW _ h₂ hzW
  rw [← levi_pull hj f c c' e (congrFun hcx) hc hy.1]
  exact h c' _ ⟨hc, hy.2.1⟩ ξ

end GlobalTheory.SemiPosEtale

namespace GlobalTheory.SemiPosEtale

theorem semiPos_of_pull_etale : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D : ℕ), IsArithVar p D → IsArithVar q D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (V : Y.Opens), (V : Set Y).Nonempty → Etale (V.ι ≫ π) → ∀ L : HermLB p, (L.pull π hπ).SemiPos D → L.SemiPos D := by
  intro k _ X Y _ _ p q D hp _ π hπ V hV hE L hL σ i
  have := hp.isDomain
  have := hp.finite
  have hσ : Function.Injective σ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
    rw [RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
    exact RingHom.injective_int _
  have : Etale (V.ι ≫ π) := hE
  have hj : (V.ι ≫ π) ≫ p = V.ι ≫ q := by rw [Category.assoc, hπ]
  have hU : ((img (V.ι ≫ π) : X.Opens) : Set X).Nonempty := by
    obtain ⟨v, hv⟩ := hV
    exact ⟨_, ⟨v, hv⟩, rfl⟩
  change PosOn D ((L.φ σ).φ i) (ptsIn p σ (L.B.U i))
  refine PosOn.of_inter hσ (isOpen_ptsIn _) (L.cInf σ i) hU (PosOn.of_etale (V.ι ≫ π) hj ?_)
  let J : (L.B.pull π).ι := fun _ => i
  have h₀ : PosOn D (((L.φ σ).pull π hπ).φ J) (ptsIn q σ ((L.B.pull π).U J)) := hL σ J
  have e₁ : ptsIn q σ ((L.B.pull π).U J) =
      PtsOver.map π hπ (spMap σ) ⁻¹' ptsIn p σ (L.B.U i) := Set.ext fun z => by
    rw [Set.mem_preimage, mem_ptsIn, mem_ptsIn]
    exact ⟨fun h => Set.mem_iInter.1 h PUnit.unit, fun h => Set.mem_iInter.2 fun _ => h⟩
  have e₂ : ((L.φ σ).pull π hπ).φ J = fun w => (L.φ σ).φ i (PtsOver.map π hπ _ w) :=
    funext ((L.φ σ).pull_φ π hπ J)
  rw [e₁, e₂] at h₀
  have h₁ := h₀.pull V.ι (q := V.ι ≫ q) rfl
  have e₃ (w : CxPts (V.ι ≫ q) σ) : PtsOver.map π hπ _ (PtsOver.map V.ι rfl _ w) =
      PtsOver.map (V.ι ≫ π) hj _ w := Subtype.ext (Category.assoc _ _ _)
  simp only [e₃] at h₁
  exact h₁

end GlobalTheory.SemiPosEtale
