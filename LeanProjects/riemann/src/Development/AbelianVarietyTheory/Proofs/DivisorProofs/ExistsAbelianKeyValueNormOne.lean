import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TanRel
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.NotGoodClassZeroSucc
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormValFUnit

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.AbKey

theorem res_res' {X : Scheme.{0}} {U V W : X.Opens} (h : W ≤ V) (h' : V ≤ U) (u : Γ(X, U)ˣ) :
    res h (res h' u) = res (h.trans h') u := by
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem exists_unit_sec {X : Scheme.{0}} (L : LB X) (F : X ⟶ X) (hF : F = 𝟙 X) (t : LB.Gen (L.pull F)) (ht : t.IsGen) :
    ∃ s : H0 L 1, ∀ j, IsUnit (s.f j) := by
  subst hF
  have le : ∀ j : Fin 1 → L.ι, LB.wchart L (fun _ : Fin 1 => 𝟙 X) j ≤ LB.wchart L (fun _ : PUnit => 𝟙 X) (fun _ => j 0) :=
    fun j y hy => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy 0
  refine ⟨⟨fun j => (res (le j) (t.s fun _ => j 0)).val, fun i j => ?_⟩, fun j => Units.isUnit _⟩
  have h := congrArg (res (inf_le_inf (le i) (le j))) (ht (fun _ => i 0) (fun _ => j 0))
  replace h := h.trans (map_mul (res (inf_le_inf (le i) (le j))) _ _)
  have e : res (inf_le_inf (le i) (le j)) ((L.pull (𝟙 X)).g (fun _ => i 0) (fun _ => j 0)) =
      (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => ((1 : ℕ) : ℤ))).g i j := by
    simp only [LB.pull, LB.LinComb, Fintype.prod_unique, Nat.cast_one, zpow_one]
    exact res_res' _ _ _
  have h' : res inf_le_left (res (le i) (t.s fun _ => i 0)) =
      (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => ((1 : ℕ) : ℤ))).g i j *
        res inf_le_right (res (le j) (t.s fun _ => j 0)) := by
    refine ((res_res' _ _ _).trans (res_res' _ _ _).symm).trans (h.trans ?_)
    exact congrArg₂ (· * ·) e ((res_res' _ _ _).trans (res_res' _ _ _).symm)
  exact congrArg Units.val h'

theorem norm_th_one {V : Type} [CommRing V] [IsDomain V] {D : DegPre V} {C : Type} [NormedField C]
    [Algebra (FractionRing V) C] {N : NumD C} (ν : NumOf D C N) (hν : ν.IntN) (hg : D.P.g = 0) : ‖N.th 1‖ = 1 := by
  haveI : IsIso D.P.A.hom := GlobalTheory.ZM.Model.isIso_of_dim_zero D.P.A D.P.isAb (hg ▸ D.P.smoothDim)
  have he : eSec D.P.A ≫ D.P.A.hom = 𝟙 _ := Over.w η[D.P.A]
  have he' : D.P.A.hom ≫ eSec D.P.A = 𝟙 _ := by
    rw [← cancel_mono D.P.A.hom, Category.assoc, Category.id_comp]
    exact (congrArg _ he).trans (Category.comp_id _)
  obtain ⟨s, hs⟩ := exists_unit_sec D.P.L (D.P.A.hom ≫ eSec D.P.A) he'
    (LB.pullGen D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => 1) D.rig D.P.A.hom)
    (DVR.pullGen_isGen _ _ _ _ D.rig_gen _)
  obtain ⟨r, hr⟩ := ν.th_gen s
  have hu : ∀ j, IsUnit (ν.th.f j) := fun j => isUnit_of_mul_isUnit_right (hr j ▸ hs j)
  obtain ⟨S, hS, hI⟩ := hν
  obtain ⟨x₀, hx, hU⟩ := hI (ν.eA 1)
  have h := congrArg norm (ν.th_eq 1)
  have hT : (TF (R := V) C).hom = spMap S.subtype ≫ x₀ ≫ D.P.A.hom := by
    rw [← Over.w (ν.eA 1), ← hx, Category.assoc]
  have hT' : (TF (R := V) C).hom ≫ eSec D.P.A = (ν.eA 1).left := by
    rw [← Over.w (ν.eA 1), Category.assoc]
    exact (congrArg _ he').trans (Category.comp_id _)
  have h1 : ‖sF ν.th (ν.eA 1).left ν.J‖ = 1 := by
    unfold sF
    have := UnitNorm.norm_valF_unit hS x₀ (LB.wchart D.P.L (fun _ : Fin 1 => 𝟙 D.P.A.left)
      fun _ => ν.J ((ν.eA 1).left ≫ 𝟙 _)) (fun y hy => Set.mem_iInter.2 fun _ => by
        rw [Category.comp_id]; exact hU hy) _ (hu _)
    rw [hx] at this
    exact this
  have h2 : ‖vF (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig (TF (R := V) C).hom ν.J‖ = 1 := by
    unfold vF
    have := UnitNorm.norm_valF_unit hS (x₀ ≫ D.P.A.hom) (LB.wchart D.P.L (fun _ : PUnit => eSec D.P.A)
      fun _ => ν.J ((TF (R := V) C).hom ≫ eSec D.P.A)) (fun y hy => Set.mem_iInter.2 fun _ => by
        rw [hT']
        change ((x₀ ≫ D.P.A.hom) ≫ eSec D.P.A) y ∈ D.P.L.U _
        have e : (x₀ ≫ D.P.A.hom) ≫ eSec D.P.A = x₀ :=
          (Category.assoc _ _ _).trans ((congrArg _ he').trans (Category.comp_id _))
        rw [e]; exact hU hy) _ (Units.isUnit (D.rig.s _))
    rw [← hT] at this
    exact this
  rwa [norm_mul, h1, h2, _root_.mul_one] at h

theorem sec_unique {X : Scheme.{0}} {L : LB X} (t : H0 L 1) {a b : L.Sec}
    (ha : ∀ i : L.ι, ∀ h : LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => i) ≤ L.U i, t.f (fun _ => i) = resG _ h (a.f i))
    (hb : ∀ i : L.ι, ∀ h : LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => i) ≤ L.U i, t.f (fun _ => i) = resG _ h (b.f i)) :
    a = b := by
  have key : a.f = b.f := funext fun i => by
    have h : LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => i) ≤ L.U i := LB.wchart_le L _ _ 0
    have h' : L.U i ≤ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => i) := fun y hy => Set.mem_iInter.2 fun _ => hy
    have e := congrArg (resG _ h') ((ha i h).symm.trans (hb i h))
    have r : ∀ z : Γ(X, L.U i), resG _ h' (resG _ h z) = z := fun z => by
      rw [← CommRingCat.comp_apply, ← Functor.map_comp]
      exact (congrArg (fun f => (X.presheaf.map f).hom z) (Subsingleton.elim _ (𝟙 _))).trans (by rw [X.presheaf.map_id]; rfl)
    rwa [r, r] at e
  cases a; cases b; cases key; rfl

theorem exists_bKey : ∀ κ : Rule, Rule4 κ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V] (D : DegPre V) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CharZero C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∀ (N : NumD C) (ν : NumOf D C N), ν.IntN → ∀ vB : Fin D.P.g → (epsR V ⟶ D.P.A), IsLieBasis vB → ∃ k : C, BKey κ ν vB k ∧ ‖k‖ = 1 := by
  intro κ hκ V _ _ _ _ D C _ _ _ _ hC N ν hν vB hv
  by_cases hg : D.P.g = 0
  · have h := norm_th_one ν hν hg
    have h0 : N.th 1 ≠ 0 := fun e => by simp [e] at h
    refine ⟨(N.th 1 ^ 8)⁻¹, ⟨fun _ => mul_inv_cancel₀ (pow_ne_zero _ h0), fun hg' => by omega⟩, by
      rw [norm_inv, norm_pow, h, one_pow, inv_one]⟩
  by_cases hex : ∃ th : D.P.L.Sec, (∀ s : Sp V, ∃ x : D.P.A.left, D.P.A.hom x = s ∧ x ∈ Out.nonzeroLocus th) ∧
      ∀ i : D.P.L.ι, ∀ h : LB.wchart D.P.L (fun _ : Fin 1 => 𝟙 D.P.A.left) (fun _ => i) ≤ D.P.L.U i,
        ν.th.f (fun _ => i) = resG _ h (th.f i)
  · obtain ⟨th, hth, hf⟩ := hex
    obtain ⟨u, hu⟩ := hκ.2.2.2 V ⟨D.P, Nat.one_le_iff_ne_zero.2 hg, D.rig, D.rig_gen, th, hth, vB, hv⟩
    refine ⟨toF V C u, ⟨fun e => (hg e).elim, fun _ _ th' _ _ x hf' hx => ?_⟩, ?_⟩
    · obtain rfl := sec_unique ν.th hf hf'
      exact hu C _ x hx
    · have h1 : ‖toF V C u‖ ≤ 1 := hC.1 _
      have h2 : ‖toF V C ↑u⁻¹‖ ≤ 1 := hC.1 _
      have h3 : ‖toF V C u‖ * ‖toF V C ↑u⁻¹‖ = 1 := by rw [← norm_mul, ← map_mul, Units.mul_inv, map_one, norm_one]
      nlinarith [norm_nonneg (toF V C u), norm_nonneg (toF V C ↑u⁻¹)]
  · exact ⟨1, ⟨fun e => (hg e).elim, fun _ _ th hth _ _ hf _ => (hex ⟨th, hth, hf⟩).elim⟩, norm_one⟩

end GlobalTheory.MBLow.AbKey

end
