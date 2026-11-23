import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbRegCountOfRanks
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitSeparationRegularDeterminantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeepsCuspLatticeNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankGrowthBoundSmallScaleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeBoundsForFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodAtOfAntitoneGapWeightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightConditionsAtIndexStatement
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsIsDeepOfField
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InterNumDetNonposSplitTorus
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.MeanLogLeOfBounds
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.BadEmb

section Abstract

variable {K Γ A : Type} [Field K] [Group Γ] [CommRing A] [Algebra K A] (B : Subalgebra K A) (tr : Γ → A →ₐ[K] A)
  (t1 : ∀ f, tr 1 f = f) (tm : ∀ g h f, tr (g * h) f = tr g (tr h f)) (tB : ∀ g, ∀ f ∈ B, tr g f ∈ B)

def subAct : Γ →* (B →ₐ[K] B) where
  toFun g := ((tr g).comp B.val).codRestrict B fun f => tB g f f.2
  map_one' := AlgHom.ext fun f => Subtype.ext (t1 f)
  map_mul' g h := AlgHom.ext fun f => Subtype.ext (tm g h f)

theorem det_mem_nonZeroDivisors (S : Subgroup Γ) [Fintype S] [DecidableEq S] (u : B)
    (h : ∀ f ∈ B, (Matrix.of fun a b : S => tr ((a * b : S) : Γ)⁻¹ u).det * f = 0 → f = 0) :
    (Matrix.of fun a b : S => subAct B tr t1 tm tB ((a : Γ) * b) u).det ∈ nonZeroDivisors B := by
  have e : B.val.toRingHom.mapMatrix (Matrix.of fun a b : S => subAct B tr t1 tm tB ((a : Γ) * b) u) =
      ((Matrix.of fun a b : S => tr ((a * b : S) : Γ)⁻¹ u).submatrix (Equiv.inv S) (Equiv.inv S)).transpose := by
    refine Matrix.ext fun a b => ?_
    show tr ((a : Γ) * b) u = tr ((b⁻¹ * a⁻¹ : S) : Γ)⁻¹ u
    simp
  rw [mem_nonZeroDivisors_iff_left]
  intro f hf
  refine Subtype.ext (h f f.2 ?_)
  have h1 := congrArg B.val.toRingHom hf
  rw [map_mul, map_zero, RingHom.map_det, e, Matrix.det_transpose, Matrix.det_submatrix_equiv_self] at h1
  exact h1

def subEquiv (V : Submodule K A) (hV : ∀ f ∈ V, f ∈ B) : V.comap B.val.toLinearMap ≃ₗ[K] V where
  toFun f := ⟨f.1.1, f.2⟩
  invFun f := ⟨⟨f.1, hV _ f.2⟩, f.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

def subRep (V : Submodule K A) (hV : ∀ g, ∀ f ∈ V, tr g f ∈ V) : Representation K Γ (V.comap B.val.toLinearMap) where
  toFun g := (subAct B tr t1 tm tB g).toLinearMap.restrict fun f hf => hV g f hf
  map_one' := LinearMap.ext fun f => Subtype.ext (Subtype.ext (t1 f))
  map_mul' g h := LinearMap.ext fun f => Subtype.ext (Subtype.ext (tm g h f))

include t1 tm tB in

theorem embReg_of_submodules [Algebra K ℂ] [Finite Γ] (Vm V V₁ V₂ U : Submodule K A) (bm : ∀ f ∈ Vm, f ∈ B)
    (b0 : ∀ f ∈ V, f ∈ B) (b2 : ∀ f ∈ V₂, f ∈ B) (bU : ∀ f ∈ U, f ∈ B)
    (m0 : ∀ f ∈ Vm, ∀ u ∈ U, f * u ∈ V) (m1 : ∀ f ∈ V, ∀ u ∈ U, f * u ∈ V₁) (m2 : ∀ f ∈ V₁, ∀ u ∈ U, f * u ∈ V₂)
    (kU : ∀ g, ∀ f ∈ U, tr g f ∈ U) (k0 : ∀ g, ∀ f ∈ V, tr g f ∈ V) (k1 : ∀ g, ∀ f ∈ V₁, tr g f ∈ V₁)
    (f0 : FiniteDimensional K V) (f2 : FiniteDimensional K V₂) (t : ℝ) (ht : 0 ≤ t)
    (hr : (Module.finrank K V₂ : ℝ) ≤ t * Module.finrank K Vm)
    (S₀ S : Subgroup Γ) (i0 : Fintype S₀) (d0 : DecidableEq S₀) (i1 : Fintype S) (d1 : DecidableEq S)
    (h0 : ∃ u ∈ U, ∀ f ∈ B, (Matrix.of fun a b : S₀ => tr ((a * b : S₀) : Γ)⁻¹ u).det * f = 0 → f = 0)
    (h1 : ∃ u ∈ U, ∀ f ∈ B, (Matrix.of fun a b : S => tr ((a * b : S) : Γ)⁻¹ u).det * f = 0 → f = 0)
    (ρ : Representation ℂ Γ (ℂ ⊗[K] V)) (χ : Γ →* ℂˣ) (lam : S₀ →* ℂˣ)
    (hρ : ∀ (g : Γ) (v w : V), (w : A) = tr g v → ρ g ((1 : ℂ) ⊗ₜ[K] v) = ((χ g : ℂˣ) : ℂ) • ((1 : ℂ) ⊗ₜ[K] w)) :
    ∃ n : ℕ, EmbReg ρ S n ∧ (n : ℝ) * Nat.card S ≤ t * Nat.card S₀ * Module.finrank ℂ (eig ρ S₀ lam) := by
  obtain ⟨u0, hu0, r0⟩ := h0
  obtain ⟨u, hu, r1⟩ := h1
  haveI := (subEquiv B V b0).symm.finiteDimensional
  haveI := (subEquiv B V₂ b2).symm.finiteDimensional
  refine GlobalTheory.BadCount.embReg_count_of_ranks K Γ B (ℂ ⊗[K] V) (subAct B tr t1 tm tB) S₀ S ⟨u0, bU _ hu0⟩ ⟨u, bU _ hu⟩
    (det_mem_nonZeroDivisors B tr t1 tm tB S₀ _ r0) (det_mem_nonZeroDivisors B tr t1 tm tB S _ r1)
    (Vm.comap B.val.toLinearMap) (V.comap B.val.toLinearMap) (V₁.comap B.val.toLinearMap) (V₂.comap B.val.toLinearMap)
    (subRep B tr t1 tm tB V k0) (fun _ _ => rfl)
    (fun h x hx => m0 _ hx _ (kU _ _ hu0)) (fun h x hx => m1 _ hx _ (kU _ _ hu)) (fun h x hx => k1 _ _ hx)
    (fun h x hx => m2 _ hx _ (kU _ _ hu)) t ht ?_
    (TensorProduct.mk K ℂ _ 1 ∘ₗ (subEquiv B V b0).toLinearMap) ?_ ρ χ (fun g v => hρ g _ _ rfl) lam
  · rwa [(subEquiv B V₂ b2).finrank_eq, (subEquiv B Vm bm).finrank_eq]
  · exact IsBaseChange.of_equiv ((subEquiv B V b0).baseChange K ℂ _ _) fun x => by simp

end Abstract

section General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M)
  {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

theorem transl_mem {G : WTZ E} (k : KeepsCusp U G) (g : LevelAut Dw l) (f : Rul Xo c) (hf : f ∈ cuspW Xo c U G) :
    transl Xo c g f ∈ cuspW Xo c U G := by
  rw [← LevDesc.pull_inv]; exact k _ f hf

theorem cusp_mem_secRing (G : WTZ E) (f : Rul Xo c) (hf : f ∈ cuspW Xo c U G) : f ∈ secRing Xo c :=
  LevDesc.mem_secRing (AllWt.cuspW_le_secZ _ hf)

include hpq hA in

theorem embReg_of_cusp (Gm G G₁ G₂ W : WTZ E) (em : Even Gm.2) (eW : Even W.2) (a0 : Gm + W = G) (a1 : G + W = G₁)
    (a2 : G₁ + W = G₂) (kW : KeepsCusp U W) (k0 : KeepsCusp U G) (k1 : KeepsCusp U G₁)
    (f0 : FiniteDimensional c.F (cuspW Xo c U G)) (f2 : FiniteDimensional c.F (cuspW Xo c U G₂)) (t : ℝ) (ht : 0 ≤ t)
    (hr : (Module.finrank c.F (cuspW Xo c U G₂) : ℝ) ≤ t * Module.finrank c.F (cuspW Xo c U Gm))
    (S₀ S : Subgroup (LevelAut Dw l))
    (h0 : ∃ u ∈ cuspW Xo c U W, ∀ f ∈ secRing Xo c, levDet Xo c S₀ u * f = 0 → f = 0)
    (h1 : ∃ u ∈ cuspW Xo c U W, ∀ f ∈ secRing Xo c, levDet Xo c S u * f = 0 → f = 0)
    (ρ : Representation ℂ (LevelAut Dw l) (ℂ ⊗[c.F] cuspW Xo c U G)) (χ : LevelAut Dw l →* ℂˣ) (lam : S₀ →* ℂˣ)
    (hρ : ∀ (g : LevelAut Dw l) (v w : cuspW Xo c U G), (w : Rul Xo c) = transl Xo c g v →
      ρ g ((1 : ℂ) ⊗ₜ[c.F] v) = ((χ g : ℂˣ) : ℂ) • ((1 : ℂ) ⊗ₜ[c.F] w)) :
    ∃ n : ℕ, EmbReg ρ S n ∧ (n : ℝ) * Nat.card S ≤ t * Nat.card S₀ * Module.finrank ℂ (eig ρ S₀ lam) := by
  have e0 : Even G.2 := a0 ▸ em.add eW
  have e1 : Even G₁.2 := a1 ▸ e0.add eW
  exact embReg_of_submodules (secRing Xo c) (transl Xo c) (LevDesc.transl_one hpq hA) (LevDesc.transl_mul hpq hA)
    (fun g f hf => by rw [← LevDesc.pull_inv]; exact LevDesc.pull_mem_secRing hpq hA _ hf)
    (cuspW Xo c U Gm) (cuspW Xo c U G) (cuspW Xo c U G₁) (cuspW Xo c U G₂) (cuspW Xo c U W)
    (cusp_mem_secRing U _) (cusp_mem_secRing U _) (cusp_mem_secRing U _) (cusp_mem_secRing U _)
    (fun f hf u hu => a0 ▸ SlopeRec.mul_mem_cuspW em eW hf hu) (fun f hf u hu => a1 ▸ SlopeRec.mul_mem_cuspW e0 eW hf hu)
    (fun f hf u hu => a2 ▸ SlopeRec.mul_mem_cuspW e1 eW hf hu) (transl_mem U kW) (transl_mem U k0) (transl_mem U k1)
    f0 f2 t ht hr S₀ S _ _ _ _ h0 h1 ρ χ lam hρ

end General

section Weights

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)

theorem shiftG_add (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (s t : ℤ) :
    shiftG Dw a n s + wtOf Dw (t • hodgeWt Dw) 0 = shiftG Dw a n (s + t) := by
  rw [shiftG, shiftG, add_smul, add_assoc]
  exact congrArg _ (AllWt.wtOf_add _ _ 0 0).symm

theorem shiftG_zero' (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : shiftG Dw a n 0 = wtZ a n := by
  rw [shiftG, zero_smul, AllWt.wtOf_zero, add_zero]

theorem even_shiftG (a : (E →+* ℂ) × ℕ → ℕ) {n : ℕ} (hn : Even n) (s : ℤ) : Even (shiftG Dw a n s).2 :=
  Even.add ((Int.even_coe_nat n).2 hn) (AllWt.even_wtOf _ _)

theorem antitone_add_hodge (v : AllWt.Weight Dw) (τ : Psi H) (hv : Antitone (v τ)) {t : ℤ} (ht : 0 ≤ t) :
    Antitone ((v + t • hodgeWt Dw) τ) := by
  intro a b hab
  have h := hv hab
  have hab' : (a : ℕ) ≤ b := hab
  simp only [hodgeWt, CompHt.barWt, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> omega

theorem gap_add_hodge (hp : 1 ≤ Dw.p) (hq : 1 ≤ Dw.q) (v : AllWt.Weight Dw) (τ : Psi H) (t : ℤ) :
    gap ((v + t • hodgeWt Dw) τ) (Dw.p - 1) = gap (v τ) (Dw.p - 1) + t := by
  have hk : Dw.p - 1 + 1 < Dw.p + Dw.q := by omega
  simp only [gap, dif_pos hk, Pi.add_apply, Pi.smul_apply, hodgeWt, CompHt.barWt, Fin.val_mk, smul_eq_mul]
  split_ifs <;> first | omega | ring

end Weights

theorem finrank_of_goodAt {D : D7} {T : Core D} {j : ℕ} {Y : Deep T j} {G : WTZ D.host.E} (h : Y.GoodAt G) :
    FiniteDimensional Y.d.c₂.F (Y.V G) ∧ Module.finrank Y.d.c₂.F (Y.V G) = Y.rk G := by
  refine ⟨Module.Finite.of_basis h.1.some.2.1.1, ?_⟩
  show _ = Module.finrank Y.d.c₂.F (Submodule.span Y.d.c₂.F (latW Y.U G : Set (Y.V G)))
  rw [h.2.2, finrank_top]

theorem embReg_deep {D : D7} {T : CoreJ D} (hL : LawsJ T) {j : ℕ} (hp1 : 1 ≤ (T.Q.Dw j).p) (hq1 : 1 ≤ (T.Q.Dw j).q)
    (hf : 2 < Module.finrank ℚ D.host.E / 2) (hj : InR D j) (Y : Deep T.toCore j) {e : ℕ} {o : ℝ} (hY : Y.Good e o)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hn : Even n) (c : ℤ) (g0 : Y.GoodAt (wtZ a n))
    (gm : Y.GoodAt (shiftG (T.Q.Dw j) a n (-c))) (g2 : Y.GoodAt (shiftG (T.Q.Dw j) a n (c + c))) (t : ℝ) (ht : 0 ≤ t)
    (hr : (Y.rk (shiftG (T.Q.Dw j) a n (c + c)) : ℝ) ≤ t * Y.rk (shiftG (T.Q.Dw j) a n (-c)))
    (S₀ S : Subgroup (LevelAut (T.Q.Dw j) Y.d.l₂))
    (h0 : ∃ u ∈ Y.V (wtOf (T.Q.Dw j) (c • hodgeWt (T.Q.Dw j)) 0), ∀ f ∈ secRing Y.d.Xo₂ Y.d.c₂,
      levDet Y.d.Xo₂ Y.d.c₂ S₀ u * f = 0 → f = 0)
    (h1 : ∃ u ∈ Y.V (wtOf (T.Q.Dw j) (c • hodgeWt (T.Q.Dw j)) 0), ∀ f ∈ secRing Y.d.Xo₂ Y.d.c₂,
      levDet Y.d.Xo₂ Y.d.c₂ S u * f = 0 → f = 0)
    (ρ : Representation ℂ (LevelAut (T.Q.Dw j) Y.d.l₂) (ℂ ⊗[Y.d.c₂.F] Y.V (wtZ a n)))
    (χ : LevelAut (T.Q.Dw j) Y.d.l₂ →* ℂˣ) (lam : S₀ →* ℂˣ)
    (hρ : ∀ (g : LevelAut (T.Q.Dw j) Y.d.l₂) (v w : Y.V (wtZ a n)), (w : Rul Y.d.Xo₂ Y.d.c₂) = transl Y.d.Xo₂ Y.d.c₂ g v →
      ρ g ((1 : ℂ) ⊗ₜ[Y.d.c₂.F] v) = ((χ g : ℂˣ) : ℂ) • ((1 : ℂ) ⊗ₜ[Y.d.c₂.F] w)) :
    ∃ m : ℕ, EmbReg ρ S m ∧ (m : ℝ) * Nat.card S ≤ t * Nat.card S₀ * Module.finrank ℂ (eig ρ S₀ lam) := by
  have kp := fun G hG => (GlobalTheory.LevelIsometry.keeps_cusp_lattice_norm D T hL j hp1 hq1 hf hj Y e o hY G hG).1
  have hA : Y.d.l₂.A.Coprime Y.d.l₂.M := by rw [hY.lev.2]; exact Nat.coprime_one_left _
  rw [← (finrank_of_goodAt g2).2, ← (finrank_of_goodAt gm).2] at hr
  have a0 : shiftG (T.Q.Dw j) a n (-c) + wtOf (T.Q.Dw j) (c • hodgeWt (T.Q.Dw j)) 0 = wtZ a n := by
    rw [shiftG_add, neg_add_cancel, shiftG_zero']
  exact embReg_of_cusp (le_add_right hp1) hA Y.U (shiftG (T.Q.Dw j) a n (-c)) (wtZ a n) (shiftG (T.Q.Dw j) a n c)
    (shiftG (T.Q.Dw j) a n (c + c)) (wtOf (T.Q.Dw j) (c • hodgeWt (T.Q.Dw j)) 0) (even_shiftG _ _ hn _) (AllWt.even_wtOf _ _)
    a0 rfl (shiftG_add _ _ _ _ _) (kp _ (AllWt.even_wtOf _ _)) (kp _ ((Int.even_coe_nat _).2 hn)) (kp _ (even_shiftG _ _ hn _))
    (finrank_of_goodAt g0).1 (finrank_of_goodAt g2).1 t ht hr S₀ S h0 h1 ρ χ lam hρ

theorem lifts_of_four {Q₁ Q₂ Q₃ Q₄ R : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x) (p : Pt Fm x hx ι)
      (_i : Fin (Fm.D x ι).R.m) (_PP _C : ℝ), Prop}
    (h₁ : Lifts Q₁) (h₂ : Lifts Q₂) (h₃ : Lifts Q₃) (h₄ : Lifts Q₄)
    (h : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x) (p : Pt Fm x hx ι) (i : Fin (Fm.D x ι).R.m)
      (PP C₁ C₂ C₃ C₄ : ℝ), Q₁ Fm x hx ι p i PP C₁ → Q₂ Fm x hx ι p i PP C₂ → Q₃ Fm x hx ι p i PP C₃ →
      Q₄ Fm x hx ι p i PP C₄ → R Fm x hx ι p i PP 0) : Lifts R := by
  refine (((h₁.and h₂).and h₃).and h₄).imp fun Fm CH _ h' => ?_
  obtain ⟨⟨⟨⟨_, -, a1⟩, _, -, a2⟩, _, -, a3⟩, _, -, a4⟩ := h'
  obtain ⟨x0, h'⟩ := ((a1.and a2).and a3).and a4
  refine ⟨0, le_rfl, x0, fun x hx hle ι p hp i => ?_⟩
  obtain ⟨⟨⟨b1, b2⟩, b3⟩, b4⟩ := h' x hx hle ι p hp
  exact h Fm x hx ι p i _ _ _ _ _ (b1 i) (b2 i) (b3 i) (b4 i)

set_option maxHeartbeats 1000000 in

theorem embReg_cover : GlobalTheory.CovTop.HypothesesX → Hypotheses2 → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → Gram → DeepGood → Size → FlatDeg → Deg → Share → Covers fun Fm x _ ι p i Y _ _ => ∀ (fr : TypeFrame (dat p i) Y.d.l₂) (π : (LevelAut (dat p i) Y.d.l₂) →* G0g (Fm.D x ι).nd) (ρ : Representation ℂ (LevelAut (dat p i) Y.d.l₂) (ℂ ⊗[Y.d.c₂.F] Y.V (Gk p i))) (χ : (LevelAut (dat p i) Y.d.l₂) →* ℂˣ) (Pb : Subgroup (G0g (Fm.D x ι).nd)) (lamb : Pb.comap π →* ℂˣ) (H : Fin 2 → Subgroup (G0g (Fm.D x ι).nd)), Pb.comap π = grpHR fr → (∀ k, (H k).comap π = grpGHR fr k) → (∀ (g : (LevelAut (dat p i) Y.d.l₂)) (v w : Y.V (Gk p i)), (w : Rul Y.d.Xo₂ Y.d.c₂) = transl Y.d.Xo₂ Y.d.c₂ g v → ρ g ((1 : ℂ) ⊗ₜ[Y.d.c₂.F] v) = ((χ g : ℂˣ) : ℂ) • ((1 : ℂ) ⊗ₜ[Y.d.c₂.F] w)) → ∀ k : Fin 2, ∃ n : ℕ, EmbReg ρ ((H k).comap π) n ∧ (n : ℝ) * Nat.card ((H k).comap π) ≤ 3 / 2 * Nat.card (Pb.comap π) * Module.finrank ℂ (eig ρ (Pb.comap π) lamb) := by
  intro hX hP hGD hQ hS hT hSA _ hDG hSz hFD hDg hSh
  first
    | have h4 := GlobalTheory.T.rank_growth_bound_small_scale hX hP hS hT hGD hQ hSA hDG hSz hFD hDg hSh
    | have h4 := GlobalTheory.T.rank_growth_bound_small_scale hP hS hT hGD hQ hSA hDG hSz hFD hDg hSh
  first
    | have ua0 := GlobalTheory.T.type_frame_large_genus_bound hX hP hGD hQ hS hT hSA
    | have ua0 := GlobalTheory.T.type_frame_large_genus_bound hP hGD hQ hS hT hSA
  first
    | have sg := GlobalTheory.T.good_at_of_antitone_gap_weight hX hP
    | have sg := GlobalTheory.T.good_at_of_antitone_gap_weight hP
  have h3 := GlobalTheory.T.size_bounds_for_family hSz
  unfold DeepGood Covers at hDG
  unfold Covers at h3 h4 ⊢
  refine lifts_of_four hDG GlobalTheory.T.weight_conditions_at_index h3 h4 ?_
  clear hDG h3 h4
  intro eps Fm x hx ι p i PP _ _ _ _ b1 b2 b3 b4 hi Y hY fr π ρ χ Pb lamb H hPb hH hρ k
  have g0 := (b1 hi Y hY).1
  have gm := (b1 hi Y hY).2.1
  have hL := (b2 hi).1
  have hp1 := (b2 hi).2.1
  have hq1 := (b2 hi).2.2.1
  have hf := (b2 hi).2.2.2.1
  have hj := (b2 hi).2.2.2.2.1
  have hn := (b2 hi).2.2.2.2.2.1
  have hs := (b2 hi).2.2.2.2.2.2.2.2
  have he := (b3 hi Y hY).2.2.2.2.2.2.1
  have hg := (b3 hi Y hY).2.2.2.2.2.2.2.1
  have hrk := b4 hi Y hY 2 one_le_two le_rfl
  have hc0 : 0 ≤ cZero (Fm.D x ι) ((i : ℕ) + 1) := Int.natCast_nonneg _
  have hs1 := hs _ (Or.inr (Or.inr rfl))
  have ec : ((2 : ℕ) : ℤ) * cZero (Fm.D x ι) ((i : ℕ) + 1) =
      cZero (Fm.D x ι) ((i : ℕ) + 1) + cZero (Fm.D x ι) ((i : ℕ) + 1) := by push_cast; ring
  rw [ec] at hrk
  have g2 : Y.GoodAt (Gs p i (cZero (Fm.D x ι) ((i : ℕ) + 1) + cZero (Fm.D x ι) ((i : ℕ) + 1))) :=
    sg _ p.T hL _ hp1 hq1 hf hj Y _ _ hY.1 (wtA (p.κ i)) (p.κ i).n _ hn
      (fun τ => by
        rw [add_smul, ← add_assoc]
        exact antitone_add_hodge _ _ τ (hs1.1 τ) hc0)
      (fun τ => by
        rw [add_smul, ← add_assoc, gap_add_hodge _ hp1 hq1]
        exact le_add_of_le_of_nonneg (hs1.2 τ) hc0)
  have ua := ua0 _ p.T hL _ hp1 hq1 hf hj Y _ _ hY.1 he hg fr
  have hr : (Y.rk (Gs p i (cZero (Fm.D x ι) ((i : ℕ) + 1) + cZero (Fm.D x ι) ((i : ℕ) + 1))) : ℝ) ≤
      3 / 2 * Y.rk (Gs p i (-(cZero (Fm.D x ι) ((i : ℕ) + 1)))) := by
    refine hrk.trans (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _))
    exact (add_le_add_right (min_le_left _ _) _).trans (by norm_num)
  exact embReg_deep hL hp1 hq1 hf hj Y hY.1 _ _ hn _ g0 gm g2 (3 / 2) (by norm_num) hr _ _
    (ua _ (Or.inl hPb)) (ua _ (Or.inr ⟨k, hH k⟩)) ρ χ lamb hρ

end GlobalTheory.BadEmb

end
