import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsArcGenericFibrePointsBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PointFamiliesEqOfValuesLevelsUniversalFamilyStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsFormalConvergence
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaSumShiftStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueFactorOfIsAlgClosed

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ConstRational

section Sums
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)

theorem fsum_mem (j : ℕ) [NeZero j] (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (hth : th ∈ A.Theta j α) (v : A.V) :
    A.FSum j α th v ∈ Conv.convLaurent := by
  obtain ⟨T, hT⟩ := exists_formal_convergence O A
  obtain ⟨h, -⟩ := ((hT T le_rfl j).1 α th hth).1 v
  exact Conv.halfRing_le_convLaurent T h

theorem exists_shift_mem (k : ℕ) [NeZero k] (la : A.La) (hla : ∀ α, (k : ℤ) ∣ A.be la.y α) :
    ∃ ψ : (Σ α : A.X, A.Theta k α) → A.V → ℂ⸨X⸩,
      ∀ i z, IsFShift A k i.1 i.2 la z (ψ i z) ∧ ψ i z ∈ Conv.convLaurent := by
  obtain ⟨cz, -, h⟩ := GlobalTheory.T.theta_sum_shift_eq_single_mul_fSum O A k la hla
  choose th' hth' _ h' using h
  refine ⟨fun i z => HahnSeries.single (A.be la.y i.1 / k) (cz z) *
    A.FSum k (i.1 + la.y) (th' i.1 i.2 i.2.2) z, fun i z => ⟨((h' i.1 i.2 i.2.2 z).1 _).2 rfl, ?_⟩⟩
  exact mul_mem (Conv.halfRing_le_convLaurent 0 (Conv.single_mem_halfRing 0 _ _))
    (fsum_mem A k _ _ (hth' _ _ _) z)

end Sums

theorem points_frames_eq (L₁ : Out.Laws) (L₂ : Out.Laws2) {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : Host E} [StarRing (𝓞 E)] {D : Datum H} {l : Level H} {Xo : Moduli D l} {A : AnArc (𝓞 E)}
    (σ : KA l →+* ℂ) {y : Sp ℂ⸨X⸩ ⟶ Xo.X} (Φ : GenPts A Xo.univ.t y) (laA laM : D.La → A.La) (hA : AnFin A)
    (hy : y ≫ Xo.s = spMap ((algebraMap ℂ ℂ⸨X⸩).comp σ))
    (levA : ∀ v, Φ.LevelPt l.A (toUnit _ ≫ Xo.univ.etaA v) (laA v))
    (levM : ∀ v ∈ idealPart D l, Φ.LevelPt l.M (toUnit _ ≫ Xo.univ.eta v) (laM v))
    {F : Type} [Field F] [IsAlgClosed F] [CharZero F] (f g : ℂ⸨X⸩ →+* F)
    (hfg : ∀ a ∈ Conv.convLaurent, f a = g a) (v : A.V) :
    spMap f ≫ (Φ.x v).left = spMap g ≫ (Φ.x v).left ∧
      ∀ j, ⊤ ≤ (Φ.x v).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → f (Φ.τ v j) = g (Φ.τ v j) := by
  haveI : NeZero l.A := ⟨l.A_pos.ne'⟩
  haveI : NeZero l.M := ⟨by have := l.three_le; omega⟩
  let φ : ∀ j, (Σ α : A.X, A.Theta j α) → A.V → F := fun j i v =>
    if h : j = 0 then 0 else haveI : NeZero j := ⟨h⟩; f (A.FSum j i.1 i.2 v)
  have hf : ∀ (j : ℕ) [NeZero j] i v, φ j i v = f (A.FSum j i.1 i.2 v) := fun j _ i v =>
    dif_neg (NeZero.ne j)
  have hg : ∀ (j : ℕ) [NeZero j] i v, φ j i v = g (A.FSum j i.1 i.2 v) := fun j _ i v =>
    (hf j i v).trans (hfg _ (fsum_mem A j _ _ i.2.2 v))
  obtain ⟨Θ₁, x₁, l₁⟩ := GlobalTheory.T.exists_arcGenericFibrePoints_baseChange E H Xo.X A Xo.univ.t y Φ F f φ hA hf
  obtain ⟨Θ₂, x₂, l₂⟩ := GlobalTheory.T.exists_arcGenericFibrePoints_baseChange E H Xo.X A Xo.univ.t y Φ F g φ hA hg
  have lev : ∀ (k : ℕ) [NeZero k] (ξ : 𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G) (la : A.La),
      Φ.LevelPt k (toUnit _ ≫ ξ) la → ∃ ψ, Θ₁.Lev k (toUnit _ ≫ ξ) ψ ∧ Θ₂.Lev k (toUnit _ ≫ ξ) ψ := by
    intro k _ ξ la h
    obtain ⟨ψ, hψ⟩ := exists_shift_mem A k la h.2.1.2
    refine ⟨fun i z => f (ψ i z), l₁ k ξ la ψ h fun i z => (hψ i z).1, ?_⟩
    have e : (fun i z => f (ψ i z)) = fun i z => g (ψ i z) :=
      funext fun i => funext fun z => hfg _ (hψ i z).2
    rw [e]
    exact l₂ k ξ la ψ h fun i z => (hψ i z).1
  have hs : (spMap f ≫ y) ≫ Xo.s = (spMap g ≫ y) ≫ Xo.s := by
    have e : f.comp ((algebraMap ℂ ℂ⸨X⸩).comp σ) = g.comp ((algebraMap ℂ ℂ⸨X⸩).comp σ) :=
      RingHom.ext fun a => hfg _ (Conv.convLaurent.algebraMap_mem (σ a))
    rw [Category.assoc, Category.assoc, hy]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e]
  obtain ⟨e₁, e₂⟩ := GlobalTheory.T.pointFamilies_eq_of_values_levels_universalFamily L₁ L₂ E H D l Xo F A.V _ _ φ _ _ Θ₁ Θ₂ hs
    (fun v => lev _ _ _ (levA v)) (fun v hv => lev _ _ _ (levM v hv)) v
  refine ⟨(x₁ v).1.symm.trans (e₁.trans (x₂ v).1), fun j hj => ?_⟩
  rw [← (x₁ v).2 j hj, ← (x₂ v).2 j hj]
  refine e₂ j ?_
  rw [(x₁ v).1]
  exact fun p _ => hj (Set.mem_univ (spMap f p))

theorem rational : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (A : AnArc (𝓞 E)) (σ : KA l →+* ℂ) (y : Sp ℂ⸨X⸩ ⟶ Xo.X) (Φ : GenPts A Xo.univ.t y) (laA laM : D.La → A.La), AnFin A → y ≫ Xo.s = spMap ((algebraMap ℂ ℂ⸨X⸩).comp σ) → (∀ v, Φ.LevelPt l.A (toUnit _ ≫ Xo.univ.etaA v) (laA v)) → (∀ v ∈ idealPart D l, Φ.LevelPt l.M (toUnit _ ≫ Xo.univ.eta v) (laM v)) → Φ.Rational := by
  intro L₁ L₂ E _ _ _ H _ D l Xo A σ y Φ laA laM hA hy levA levM
  haveI : CharZero ℂ⸨X⸩ := algebraRat.charZero _
  haveI : CharZero Conv.convLaurent := algebraRat.charZero _
  have key := fun s : AlgebraicClosure ℂ⸨X⸩ ≃ₐ[Conv.convLaurent] AlgebraicClosure ℂ⸨X⸩ =>
    points_frames_eq L₁ L₂ σ Φ laA laM hA hy levA levM
      ((s : AlgebraicClosure ℂ⸨X⸩ →+* AlgebraicClosure ℂ⸨X⸩).comp (algebraMap ℂ⸨X⸩ _))
      (algebraMap ℂ⸨X⸩ (AlgebraicClosure ℂ⸨X⸩)) (fun a ha => s.commutes (⟨a, ha⟩ : Conv.convLaurent))
  refine ⟨fun v => ?_, fun v j hj => ?_⟩
  · refine (FixedPoint.existsUnique_factor (K₀ := Conv.convLaurent) (L := AlgebraicClosure ℂ⸨X⸩)
      (Φ.x v).left fun s => ?_).exists
    have h := (key s v).1
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact h
  · obtain ⟨a, ha⟩ := FixedPoint.mem_range_of_algebraMap_fixed (K₀ := Conv.convLaurent)
      (L := AlgebraicClosure ℂ⸨X⸩) (Φ.τ v j) fun s => (key s v).2 j hj
    exact ha ▸ a.2

end GlobalTheory.ConstRational
