import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceHalfHeisenbergInvariantForm
import Formalism.LocalToGlobal.IndefiniteReal.ExistsGADet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmSplitHalves
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNeZeroAtZero

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CharsFromWeil

section Alg

variable {R : Type*} [CommRing R]

theorem alg_key (c : R →+* R) {e a b : R} (he1 : e * e = e) (hec : e * c e = 0) (hab : a * b = 1) :
    (e * a + c e * c b + (1 - e - c e)) * (e * b + c e * c a + (1 - e - c e)) = 1 := by
  have hce : c e * c e = c e := by rw [← map_mul, he1]
  have hcab : c a * c b = 1 := by rw [← map_mul, hab, map_one]
  linear_combination e * e * hab + c e * c e * hcab +
    (a * c a + c b * b - a - b - c b - c a + 2) * hec + (2 - a - b) * he1 + (2 - c b - c a) * hce

theorem alg_conj (c : R →+* R) (hcc : ∀ z, c (c z) = z) (e a b : R) :
    c (e * a + c e * c b + (1 - e - c e)) = e * b + c e * c a + (1 - e - c e) := by
  simp only [map_add, map_mul, map_sub, map_one, hcc]
  ring

theorem alg_supp (c : R →+* R) {e a b : R} (he1 : e * e = e) (hec : e * c e = 0) :
    (e + c e) * ((e * a + c e * c b + (1 - e - c e)) - 1) = (e * a + c e * c b + (1 - e - c e)) - 1 := by
  have hce : c e * c e = c e := by rw [← map_mul, he1]
  linear_combination (a - 1) * he1 + (c b - 1) * hce + (c b + a - 2) * hec

theorem alg_at (c : R →+* R) {e a b : R} (he1 : e * e = e) (hec : e * c e = 0) :
    e * (e * a + c e * c b + (1 - e - c e)) + (1 - e) = e * a + (1 - e) := by
  linear_combination (a - 1) * he1 + (c b - 1) * hec

theorem alg_prod {e f E x : R} (hef : e * f = 0) (hsum : e + f = E) (hsupp : E * (x - 1) = x - 1) :
    x = (e * x + (1 - e)) * (f * x + (1 - f)) := by
  linear_combination (-(x - 1) ^ 2) * hef - (x - 1) * hsum - hsupp

end Alg

variable {D : D7}

theorem splitFac_eq {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT χS' χT' : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (H : IsWeilDatumO ψ S T χS χT om) (H' : IsWeilDatumO ψ S T χS' χT' om) {e : AE D} (he : IsSplitIdem D e)
    {g : GA D S} {h : GA D T} (hg : SuppAt e S g) (hh : SuppAt e T h) {x y : (AE D)ˣ}
    (hx : IsDetAt e S g x) (hy : IsDetAt e T h y) :
    splitFacO χS χT x y = splitFacO χS' χT' x y := by
  obtain ⟨r, hr, h1⟩ := H.om_split e he g h hg hh x y hx hy
  obtain ⟨r', hr', h2⟩ := H'.om_split e he g h hg hh x y hx hy
  obtain ⟨ℓ, hℓ, f, hf, hne⟩ := GlobalTheory.HalfCoinv.exists_invariant_form D ψ H.std S T e he
  have e1 := h1 ℓ hℓ f hf
  rw [h2 ℓ hℓ f hf] at e1
  have e2 : (r' : ℂ) * (splitFacO χS' χT' x y : ℂ) = r * (splitFacO χS χT x y : ℂ) :=
    mul_right_cancel₀ hne e1
  have e3 : r' = r := by
    have := congrArg norm e2
    rwa [norm_mul, norm_mul, Circle.norm_coe, Circle.norm_coe, mul_one, mul_one, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg hr.le, Real.norm_of_nonneg hr'.le] at this
  subst e3
  apply Circle.ext
  exact (mul_left_cancel₀ (Complex.ofReal_ne_zero.2 hr'.ne') e2).symm

theorem exists_unit_idem {e : AE D} (he : e * e = e) (u : (AE D)ˣ) : ∃ x : (AE D)ˣ, (x : AE D) = e * u + (1 - e) := by
  have hu : (u : AE D) * ((u⁻¹ : (AE D)ˣ) : AE D) = 1 := u.mul_inv
  have hk : (e * u + (1 - e)) * (e * ((u⁻¹ : (AE D)ˣ) : AE D) + (1 - e)) = 1 := by
    linear_combination (2 - (u : AE D) - ((u⁻¹ : (AE D)ˣ) : AE D)) * he + e * e * hu
  exact ⟨⟨_, _, hk, by rw [mul_comm]; exact hk⟩, rfl⟩

theorem isSplitIdem_conj' {e : AE D} (h : IsSplitIdem D e) : IsSplitIdem D (cA D e) := by
  obtain ⟨h1, h2, v, ε, hε, h3⟩ := h
  exact ⟨by rw [← map_mul, h1], by rw [Formalism.L2.Theta.cA_cA, mul_comm, h2], v, ε, hε,
    by rw [Formalism.L2.Theta.cA_cA, add_comm, h3]⟩

theorem isDetAt_one (e : AE D) (V : HSp D) : IsDetAt e V 1 1 := by
  change (1 : AE D) = e * (Formalism.L2.Theta.mt V 1).det + (1 - e)
  rw [Formalism.IndefR.flipTwoThree.mt_one', Matrix.det_one]
  ring

theorem exists_detUnit {e : AE D} (he : IsSplitIdem D e) (u : (AE D)ˣ) :
    ∃ X : (AE D)ˣ, (X : AE D) * cA D (X : AE D) = 1 ∧ Formalism.IndefR.InjectiveDecompositionAction.SuppAtU D e X ∧
      e * (X : AE D) + (1 - e) = e * u + (1 - e) := by
  have hab : (u : AE D) * ((u⁻¹ : (AE D)ˣ) : AE D) = 1 := u.mul_inv
  have hk := alg_key (cA D) he.1 he.2.1 hab
  refine ⟨⟨_, _, hk, by rw [mul_comm]; exact hk⟩, ?_, alg_supp (cA D) he.1 he.2.1, alg_at (cA D) he.1 he.2.1⟩
  change _ * cA D _ = 1
  rw [alg_conj (cA D) Formalism.L2.Theta.cA_cA]
  exact hk

theorem chiT_agree {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT χS' χT' : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (H : IsWeilDatumO ψ S T χS χT om) (H' : IsWeilDatumO ψ S T χS' χT' om) (hS : 0 < S.rank) {e : AE D}
    (he : IsSplitIdem D e) (u x : (AE D)ˣ) (hx : (x : AE D) = e * u + (1 - e)) : χT x = χT' x := by
  obtain ⟨X, hX1, hX2, hX3⟩ := exists_detUnit he u
  obtain ⟨g, hg, ⟨x', hx'⟩, hdet⟩ := Formalism.IndefR.flipTwoThree.splitDet D S hS e he X hX1 hX2
  have h0 : (x' : AE D) = e * (Formalism.L2.Theta.mt S g).det + (1 - e) := hx'
  have hxx : x' = x := Units.ext (by rw [h0, hdet, hX3, hx])
  subst hxx
  have := splitFac_eq H H' he hg (GlobalTheory.WeilDetermined.suppAt_one e T) hx' (isDetAt_one e T)
  simpa only [splitFacO, map_one, mul_one, _root_.inv_inj] using this

theorem chiS_agree {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT χS' χT' : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (H : IsWeilDatumO ψ S T χS χT om) (H' : IsWeilDatumO ψ S T χS' χT' om) (hT : 0 < T.rank) {e : AE D}
    (he : IsSplitIdem D e) (u y : (AE D)ˣ) (hy : (y : AE D) = e * u + (1 - e)) : χS y = χS' y := by
  obtain ⟨X, hX1, hX2, hX3⟩ := exists_detUnit he u
  obtain ⟨h, hh, ⟨y', hy'⟩, hdet⟩ := Formalism.IndefR.flipTwoThree.splitDet D T hT e he X hX1 hX2
  have h0 : (y' : AE D) = e * (Formalism.L2.Theta.mt T h).det + (1 - e) := hy'
  have hyy : y' = y := Units.ext (by rw [h0, hdet, hX3, hy])
  subst hyy
  have := splitFac_eq H H' he (GlobalTheory.WeilDetermined.suppAt_one e S) hh (isDetAt_one e S) hy'
  simpa only [splitFacO, map_one, inv_one, one_mul] using this

theorem eq_of_comp {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (χ χ' : (AE D)ˣ →* Circle)
    (hag : ∀ e, IsSplitIdem D e → ∀ u x : (AE D)ˣ, (x : AE D) = e * u + (1 - e) → χ x = χ' x)
    (x : (AE D)ˣ) (h1 : infPart D (x : AE D) = 1)
    (h2 : ∀ w, w ≠ p.v → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w (finPart D (x : AE D)) = 1) : χ x = χ' x := by
  obtain ⟨ε, hε, hsum⟩ := p.above
  have hsupp : algebraMap (AF D.host.F) (AE D) ε * ((x : AE D) - 1) = (x : AE D) - 1 :=
    (GlobalTheory.VacStabFixed.supp_iff hε _).2 ⟨by rw [map_sub, map_one, h1, sub_self],
      fun w hw => by rw [map_sub, map_sub, map_one, map_one, h2 w hw, sub_self]⟩
  have he : IsSplitIdem D p.e := p.split
  have hce : IsSplitIdem D (cA D p.e) := isSplitIdem_conj' he
  obtain ⟨x1, hx1⟩ := exists_unit_idem he.1 x
  obtain ⟨x2, hx2⟩ := exists_unit_idem hce.1 x
  have hprod : x = x1 * x2 := by
    apply Units.ext
    rw [Units.val_mul, hx1, hx2]
    exact alg_prod he.2.1 hsum hsupp
  rw [hprod, map_mul, map_mul, hag p.e he x x1 hx1, hag _ hce x x2 hx2]

theorem charUnram_transfer {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (χ χ' : (AE D)ˣ →* Circle)
    (hag : ∀ e, IsSplitIdem D e → ∀ u x : (AE D)ˣ, (x : AE D) = e * u + (1 - e) → χ x = χ' x)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χ p.v) : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χ' p.v := by
  intro x h1 h2 h3 h4
  rw [← eq_of_comp p χ χ' hag x h1 h2]
  exact h x h1 h2 h3 h4

theorem charUnram_of_weil : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT χS' χT' : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S T χS' χT' om → (0 < S.rank → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χT p.v → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χT' p.v) ∧ (0 < T.rank → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χS p.v → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χS' p.v) := by
  intro D k _ _ _ _ p ψ S T χS χT χS' χT' om H H'
  exact ⟨fun hS => charUnram_transfer p χT χT' fun e he u x hx => chiT_agree H H' hS he u x hx,
    fun hT => charUnram_transfer p χS χS' fun e he u y hy => chiS_agree H H' hT he u y hy⟩

end GlobalTheory.CharsFromWeil

end
