import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsDerivAt0CompLinMap
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AppellHumbertDataEqOfLbIsoPowPull
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueLinearLiftOfHolomorphicAbelianVariet
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AppellHumbertUnifTangentWeilPairing
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionEqAndWeilIsOfIsHolTo
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaUniformisationComplexAbelianVarieties
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ChiEqOneOrOfSym
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstOfNormPeriodic
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.Unimod

theorem mem_of_unimodular {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ))
    (hfull : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re)
    (Ef : LinearMap.BilinForm ℤ Λ) (hE : ∀ a b : Λ, (Ef a b : ℝ) = (hermForm Hm a b).im)
    (hB : Function.Bijective Ef) (w : Fin g → ℂ)
    (hw : ∀ l : Λ, ∃ k : ℤ, (hermForm Hm w l).im = k) : w ∈ Λ := by
  have addR : ∀ (v x y : Fin g → ℂ), hermForm Hm v (x + y) = hermForm Hm v x + hermForm Hm v y := fun v x y => by
    simp [hermForm, Matrix.mulVec_add, dotProduct_add]
  have addL : ∀ (v v' x : Fin g → ℂ), hermForm Hm (v - v') x = hermForm Hm v x - hermForm Hm v' x := fun v v' x => by
    simp [hermForm, sub_dotProduct]
  have smulR : ∀ (v x : Fin g → ℂ) (r : ℝ), hermForm Hm v (r • x) = r * hermForm Hm v x := fun v x r => by
    have e : star (r • x) = (r : ℂ) • star x := by
      ext i
      simp
    simp only [hermForm, e, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  choose k hk using hw
  have kadd : ∀ a b : Λ, k (a + b) = k a + k b := fun a b => by
    have h := hk (a + b)
    rw [Submodule.coe_add, addR, Complex.add_im, hk a, hk b] at h
    exact_mod_cast h.symm
  let ℓ : Λ →ₗ[ℤ] ℤ := (AddMonoidHom.mk' k kadd).toIntLinearMap
  obtain ⟨c, hc⟩ := hB.2 ℓ
  have hv : ∀ x ∈ Submodule.span ℝ (Λ : Set (Fin g → ℂ)), (hermForm Hm (w - c) x).im = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      have h := hE c ⟨x, hx⟩
      have h' : Ef c ⟨x, hx⟩ = k ⟨x, hx⟩ := LinearMap.congr_fun hc _
      rw [addL, Complex.sub_im, ← h, h']
      have := hk ⟨x, hx⟩
      simp only at this
      rw [this, sub_self]
    | zero => simp [hermForm]
    | add x y _ _ hx hy => rw [addR, Complex.add_im, hx, hy, add_zero]
    | smul r x _ hx => rw [smulR, Complex.im_ofReal_mul, hx, mul_zero]
  have hI : (hermForm Hm (w - c) (Complex.I • (w - c))).im = 0 := hv _ (by rw [hfull]; trivial)
  have hv0 : w - (c : Fin g → ℂ) = 0 := by
    by_contra hne
    have hp := hpos _ hne
    have e : star (Complex.I • (w - (c : Fin g → ℂ))) = (-Complex.I) • star (w - (c : Fin g → ℂ)) := by
      ext i
      simp
    have e' : hermForm Hm (w - c) (Complex.I • (w - c)) = -Complex.I * hermForm Hm (w - c) (w - c) := by
      simp only [hermForm, e, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
    rw [e'] at hI
    have : (hermForm Hm (w - c) (w - c)).re = 0 := by simpa using hI
    exact hp.ne' this
  rw [sub_eq_zero.1 hv0]
  exact c.2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {L : Type} [Field L] [NumberField L]

theorem exists_compare (D : PPData H L) (σ : L →+* ℂ) (a : D.Frame σ) :
    ∃ (g' : ℕ) (Λ₀ : Submodule ℤ (Fin g' → ℂ)) (H₀ : Matrix (Fin g') (Fin g') ℂ) (χ₀ : Λ₀ → ℂ)
      (Ef : LinearMap.BilinForm ℤ Λ₀) (F : (Fin D.g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (hΛ : ∀ l ∈ a.u.Λ, F l ∈ Λ₀),
      Submodule.span ℝ (Λ₀ : Set (Fin g' → ℂ)) = ⊤ ∧
      (∀ z : Fin g' → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₀.mulVec (star z)).re) ∧
      (∀ x y : Λ₀, (Ef x y : ℝ) = (hermForm H₀ x y).im) ∧ Function.Bijective Ef ∧
      (∀ l : Λ₀, χ₀ l = 1 ∨ χ₀ l = -1) ∧
      (∀ z w, hermForm a.Hm z w = hermForm H₀ (F z) (F w)) ∧
      (∀ l : a.u.Λ, a.χ l = χ₀ ⟨F l, hΛ l l.2⟩) ∧
      (∀ z, F z ∈ Λ₀ → z ∈ a.u.Λ) ∧ Function.Surjective F := by
  have hLφ : (D.t.PP.L.pull a.φ).IsLB := pull_isLB D.t.PP.isLB _
  obtain ⟨hpr, hamp, hkt⟩ := D.princ
  have := D.tK.semi.smooth
  have := D.tK.semi.geomConnected
  have : ConnectedSpace D.tK.G.left := GeometricallyConnected.connectedSpace D.tK.G.hom D.tK.G.hom.isOpenMap
  obtain ⟨gd, hgd⟩ := exists_dim_of_preconnected D.tK.G.hom (Classical.arbitrary _)
  let P₀ : Out.PolAV (Sp L) :=
    { A := D.tK.G, g := gd, smoothDim := hgd, L := D.tK.PP.L, isLB := D.tK.PP.isLB, ample := hamp, ktriv := hkt
      isAb := ⟨D.tK.semi.comm, D.tK.semi.smooth, hpr, D.tK.semi.geomConnected⟩
      rigid := GlobalTheory.ObjDim.rigidified
      sym := GlobalTheory.ObjDim.sym }
  obtain ⟨P', ψ, hψ, -, hm, t, ht⟩ := GlobalTheory.polBaseChange_holds (Sp L) (Sp ℂ) (spMap σ) P₀
  have hpb : IsGrpPullback P'.A D.tK.G (spMap σ) ψ := by
    refine ⟨hψ, fun T x y x₀ y₀ hx hy => ?_⟩
    rw [(Over.OverMorphism.ext hx : x₀ = Out.toBase hψ.w x), (Over.OverMorphism.ext hy : y₀ = Out.toBase hψ.w y), ← hm]
    rfl
  have hpc : IsGrpPullback P'.A D.t.G (emb σ) (ψ ≫ D.m.φ) :=
    (hpb.comp D.m.cart).congr (by rw [spMap_comp_spMap]) rfl
  obtain ⟨e, hmon, he⟩ := grpPullback_iso a.cart hpc
  haveI := hmon
  obtain ⟨rig, hrig⟩ := P'.rigid
  obtain ⟨u₀, H₀, χ₀, Ef, hu₀, -, hv, hw, -, -, hE, hB, -⟩ := GlobalTheory.thetaUnifAV_closed P' rig hrig
  have hol : IsHolTo (Set.univ : Set (Fin D.g → ℂ)) (fun w => (a.u.ex w ≫ e.hom).left) := by
    simpa only [Over.comp_left] using GlobalTheory.HolTorsion.isHolTo_comp (Flat.PerGram.isHolTo_ex a.u) e.hom.left
  obtain ⟨F, hF, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo P'.A P'.isAb P'.L P'.g D.g u₀ hv hw
    (fun w => a.u.ex w ≫ e.hom) (fun p q => by rw [a.u.ex_add, MonObj.mul_comp]) hol
  have hΛ : ∀ l ∈ a.u.Λ, F l ∈ u₀.Λ := fun l hl => (u₀.ker _).1 (by
    rw [hF, (a.u.ker l).2 hl, MonObj.one_comp])
  have back : ∀ z, F z ∈ u₀.Λ → z ∈ a.u.Λ := fun z hz => (a.u.ker z).1 (by
    have h := (u₀.ker _).2 hz
    rw [hF] at h
    have h' := congrArg (· ≫ e.inv) h
    simpa [MonObj.one_comp] using h')
  have hsurj : Function.Surjective F := by
    haveI := u₀.discrete
    refine LinearMap.range_eq_top.1 (GlobalTheory.AHWeil.eq_top_of_add_discrete u₀.Λ _ fun w => ?_)
    obtain ⟨z, hz⟩ := a.u.ex_onto (u₀.ex w ≫ e.inv)
    have hz' : u₀.ex (F z) = u₀.ex w := by
      rw [hF, hz, Category.assoc, e.inv_hom_id, Category.comp_id]
    have h := u₀.ex_add (w - F z) (F z)
    rw [sub_add_cancel, hz'] at h
    exact ⟨⟨w - F z, (u₀.ker _).1 (mul_eq_right.1 h.symm)⟩, z, by simp⟩
  have i₁ : LBIso P'.L (D.tK.PP.L.pull ψ) := LBIso.symm ⟨t, ht⟩
  have i₂ : LBIso D.tK.PP.L (D.t.PP.L.pull D.m.φ) := by
    obtain ⟨w, hw, -⟩ := D.m.lin
    exact ⟨w, hw⟩
  have i₃ : LBIso (D.tK.PP.L.pull ψ) (D.t.PP.L.pull (ψ ≫ D.m.φ)) :=
    GlobalTheory.GenSpread.lbIso_pull_of_lbIso i₂ ψ rfl
  have i₄ : LBIso P'.L (D.t.PP.L.pull (ψ ≫ D.m.φ)) :=
    LBIso.trans P'.isLB (pull_isLB D.tK.PP.isLB _) (pull_isLB D.t.PP.isLB _) i₁ i₃
  have i₅ : LBIso (P'.L.pull e.hom.left) (D.t.PP.L.pull a.φ) :=
    GlobalTheory.GenSpread.lbIso_pull_of_lbIso i₄ e.hom.left he.symm
  have iso : LBIso (lbPow (D.t.PP.L.pull a.φ) 1) (lbPow (P'.L.pull e.hom.left) 1) :=
    GlobalTheory.lbIso_lbPow (LBIso.symm i₅) 1
  obtain ⟨hH, hχ⟩ := GlobalTheory.appellHumbert_data_eq_of_lbIso_pow_pull a.A P'.A _ P'.L D.g P'.g a.u u₀ a.Hm H₀ a.χ χ₀
    e.hom F hΛ 1 one_pos hLφ P'.isLB a.ah hu₀ hF iso
  exact ⟨P'.g, u₀.Λ, H₀, χ₀, Ef, F, hΛ, u₀.full, hu₀.2.1, hE, hB,
    GlobalTheory.ThetaUnifCompare.chi_eq_one_or_of_sym P'.isLB P'.sym hu₀, hH, fun l => by simpa using hχ l, back, hsurj⟩

theorem frame_unimodular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (σ : L →+* ℂ) (a : D.Frame σ), (∀ l l' : a.u.Λ, ∃ k : ℤ, (a.herm l l').im = k) ∧ (∀ w : Fin D.g → ℂ, (∀ l : a.u.Λ, ∃ k : ℤ, (a.herm w l).im = k) → w ∈ a.u.Λ) ∧ (∀ l l' : a.u.Λ, a.χ (l + l') = a.χ l * a.χ l' * Complex.exp (Real.pi * Complex.I * (a.herm l l').im)) ∧ ∀ l : a.u.Λ, a.χ l ^ 2 = 1 := by
  intro E _ _ _ H L _ _ D σ a
  have hLφ : (D.t.PP.L.pull a.φ).IsLB := pull_isLB D.t.PP.isLB _
  obtain ⟨g', Λ₀, H₀, χ₀, Ef, F, hΛ, hfull, hpos, hE, hB, hχ₀, hH, hχ, back, hsurj⟩ := exists_compare D σ a
  refine ⟨fun l l' => ?_, fun w hw => ?_, fun l l' => GlobalTheory.FrameValue.chi_add hLφ a.ah l l', fun l => ?_⟩
  · obtain ⟨n, hn⟩ := GlobalTheory.FrameValue.exists_int_im hLφ a.ah l l'
    exact ⟨n, hn.symm⟩
  · refine back w (mem_of_unimodular Λ₀ hfull H₀ hpos Ef hE hB (F w) fun l₀ => ?_)
    obtain ⟨z, hz⟩ := hsurj l₀
    have hzΛ : z ∈ a.u.Λ := back z (hz ▸ l₀.2)
    obtain ⟨k, hk⟩ := hw ⟨z, hzΛ⟩
    refine ⟨k, ?_⟩
    rw [← hz, ← hH]
    exact hk
  · rw [hχ l]
    rcases hχ₀ ⟨F l, hΛ l l.2⟩ with h | h <;> simp [h]

end GlobalTheory.CompanionTheory.Ar.Sl.Unimod
