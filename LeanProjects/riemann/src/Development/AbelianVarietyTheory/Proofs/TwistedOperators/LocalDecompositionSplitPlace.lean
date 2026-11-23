import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointRadical
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaIsotropicStabiliserSplitPlace

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.IwSplitFrame

section Frame

variable {D : D7} {V : HSp D} (Φ : WittFrame V)

def cols {r : ℕ} (x : Fin r → V.V) : Matrix (Fin V.rank) (Fin r) D.host.E := Matrix.of fun k i => V.frame.repr (x i) k

theorem gram_cols {r s : ℕ} (x : Fin r → V.V) (y : Fin s → V.V) (i : Fin r) (j : Fin s) :
    (((cols x).map D.sp.cm.sig).transpose * V.gram * cols y) i j = V.hT (x i) (y j) := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.hT_coord V]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, cols, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

theorem fe : ((cols Φ.f).map D.sp.cm.sig).transpose * V.gram * cols Φ.e = 1 := by
  ext j i
  rw [gram_cols, Matrix.one_apply, ← HSpace.hD, Φ.ef]
  simp only [eq_comm]

theorem ee : ((cols Φ.e).map D.sp.cm.sig).transpose * V.gram * cols Φ.e = 0 := by
  ext j i
  rw [gram_cols, Matrix.zero_apply, ← HSpace.hD, Φ.ee]

theorem ff : ((cols Φ.f).map D.sp.cm.sig).transpose * V.gram * cols Φ.f = 0 := by
  ext j i
  rw [gram_cols, Matrix.zero_apply, ← HSpace.hD, Φ.ff]

theorem ef : ((cols Φ.e).map D.sp.cm.sig).transpose * V.gram * cols Φ.f = 1 := by
  ext i j
  have h1 : V.hT (Φ.e i) (Φ.f j) = star (V.hT (Φ.f j) (Φ.e i)) := GlobalTheory.IndefiniteRowSideFullHecke.BesselData.hT_swap rfl
  rw [gram_cols, Matrix.one_apply, h1, ← HSpace.hD, Φ.ef]
  split_ifs <;> simp

theorem coordMat_eq (R : Type) [CommRing R] [Algebra D.host.F R] :
    (Matrix.of fun (x : Fin V.rank) (i : Fin (wittIndex V)) => GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR (F := D.host.F) V R (Φ.e i) x) =
      (cols Φ.e).map (inclR (F := D.host.F) R) := by
  ext; rfl

end Frame

theorem exists_compl {K : Type} [Field K] [CharZero K] {n r : ℕ} (e e' : Matrix (Fin n) (Fin r) K)
    (p a : Matrix (Fin r) (Fin n) K) (hpe : p * e = 1) (hpe' : p * e' = 0) (hae : a * e = 0) (hae' : a * e' = 1) :
    ∃ (k : ℕ) (i : Matrix (Fin n) (Fin k) K) (q : Matrix (Fin k) (Fin n) K), n = r + k + r ∧
      e * p + i * q + e' * a = 1 := by
  set π : Matrix (Fin n) (Fin n) K := 1 - e * p - e' * a with hπdef
  have hXX : e * p * (e * p) = e * p := by rw [Matrix.mul_assoc, ← Matrix.mul_assoc p, hpe, Matrix.one_mul]
  have hXY : e * p * (e' * a) = 0 := by rw [Matrix.mul_assoc, ← Matrix.mul_assoc p, hpe', Matrix.zero_mul, Matrix.mul_zero]
  have hYX : e' * a * (e * p) = 0 := by rw [Matrix.mul_assoc, ← Matrix.mul_assoc a, hae, Matrix.zero_mul, Matrix.mul_zero]
  have hYY : e' * a * (e' * a) = e' * a := by rw [Matrix.mul_assoc, ← Matrix.mul_assoc a, hae', Matrix.one_mul]
  have hπ : π * π = π := by
    simp only [hπdef, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hXX, hXY, hYX, hYY]
    abel
  have hid : IsIdempotentElem (Matrix.toLin' π) := by
    rw [IsIdempotentElem, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hπ]
  set W := LinearMap.range (Matrix.toLin' π)
  set b := Module.finBasis K W
  refine ⟨Module.finrank K W, LinearMap.toMatrix' (W.subtype ∘ₗ b.equivFun.symm.toLinearMap),
    LinearMap.toMatrix' (b.equivFun.toLinearMap ∘ₗ (Matrix.toLin' π).rangeRestrict), ?_, ?_⟩
  · have h1 := (LinearMap.IsIdempotentElem.isProj_range _ hid).trace
    rw [Matrix.trace_toLin'_eq, hπdef, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_mul_comm e,
      Matrix.trace_mul_comm e', hpe, hae', Matrix.trace_one, Matrix.trace_one] at h1
    simp only [Fintype.card_fin] at h1
    have h2 : ((r + Module.finrank K W + r : ℕ) : K) = n := by push_cast; rw [← h1]; ring
    exact (Nat.cast_injective h2).symm
  · rw [← LinearMap.toMatrix'_comp]
    have h3 : (W.subtype ∘ₗ b.equivFun.symm.toLinearMap) ∘ₗ (b.equivFun.toLinearMap ∘ₗ (Matrix.toLin' π).rangeRestrict) =
        Matrix.toLin' π := by
      refine LinearMap.ext fun x => ?_
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, Submodule.subtype_apply,
        LinearMap.rangeRestrict, LinearMap.codRestrict_apply]
    rw [h3, LinearMap.toMatrix'_toLin', hπdef]
    abel

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n r : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {v : HeightOneSpectrum (𝓞 F)}

theorem mat_mul (g h : GLoc σ J v) : (HA.mat (F := F) (Fv F v) σ J (g * h)).1 =
    (HA.mat (F := F) (Fv F v) σ J g).1 * (HA.mat (F := F) (Fv F v) σ J h).1 := by
  rw [← GlobalTheory.AdelicU.matHom_apply, ← GlobalTheory.AdelicU.matHom_apply, ← GlobalTheory.AdelicU.matHom_apply, map_mul, Units.val_mul]

theorem mat_one : (HA.mat (F := F) (Fv F v) σ J 1).1 = 1 := by
  rw [← GlobalTheory.AdelicU.matHom_apply, map_one, Units.val_one]

def keepGrp (j : Matrix (Fin n) (Fin r) (Fv F v ⊗[F] E)) : Subgroup (GLoc σ J v) where
  carrier := {q | ∃ β : GL (Fin r) (Fv F v ⊗[F] E), (HA.mat (F := F) (Fv F v) σ J q).1 * j = j * β.1}
  mul_mem' := by
    rintro a b ⟨β, hβ⟩ ⟨β', hβ'⟩
    refine ⟨β * β', ?_⟩
    rw [mat_mul, Matrix.mul_assoc, hβ', ← Matrix.mul_assoc, hβ, Units.val_mul, Matrix.mul_assoc]
  one_mem' := ⟨1, by rw [mat_one, Matrix.one_mul, Units.val_one, Matrix.mul_one]⟩
  inv_mem' := by
    rintro a ⟨β, hβ⟩
    refine ⟨β⁻¹, ?_⟩
    have h1 : (HA.mat (F := F) (Fv F v) σ J a⁻¹).1 * (HA.mat (F := F) (Fv F v) σ J a).1 = 1 := by
      rw [← mat_mul, inv_mul_cancel, mat_one]
    calc (HA.mat (F := F) (Fv F v) σ J a⁻¹).1 * j
        = (HA.mat (F := F) (Fv F v) σ J a⁻¹).1 * (j * β.1) * (β⁻¹).1 := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc j, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      _ = j * (β⁻¹).1 := by rw [← hβ, ← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem keeps_of_split (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (g : GLoc σ J v) {e : Matrix (Fin n) (Fin r) E}
    {p : Matrix (Fin r) (Fin n) E} (hp : p * e = 1) {a a' : Matrix (Fin r) (Fin r) (Fv F v)}
    (h1 : (splitHom σ J τ g).1 * e.map τ = e.map τ * a)
    (h2 : (splitHom σ J (τ.comp σ) g).1 * e.map (τ.comp σ) = e.map (τ.comp σ) * a') :
    g ∈ keepGrp (σ := σ) (J := J) (v := v) (e.map (inclR (F := F) (Fv F v))) := by
  set j := e.map (inclR (F := F) (Fv F v))
  set P := p.map (inclR (F := F) (Fv F v))
  have hP : P * j = 1 := by
    rw [← Matrix.map_mul, hp, Matrix.map_one _ (map_zero _) (map_one _)]
  have key : ∀ (t : E →ₐ[F] Fv F v) {b : Matrix (Fin r) (Fin r) (Fv F v)},
      (splitHom σ J t g).1 * e.map t = e.map t * b →
      (HA.mat (F := F) (Fv F v) σ J g).1.map ((splitProj t).toRingHom) * j.map ((splitProj t).toRingHom) =
        j.map ((splitProj t).toRingHom) * b := fun t b hb => by
    have e2 : j.map ((splitProj t).toRingHom) = e.map t := by
      ext k l
      simp [j, splitProj_inclR]
    rw [e2]
    exact hb
  have hk : (HA.mat (F := F) (Fv F v) σ J g).1 * j = j * (P * ((HA.mat (F := F) (Fv F v) σ J g).1 * j)) := by
    ext k l
    exact split_ext h τ (congrFun (congrFun (GlobalTheory.Core.Rk.IwFlagSplit.map_keeps _ hP (key τ h1)) k) l)
      (congrFun (congrFun (GlobalTheory.Core.Rk.IwFlagSplit.map_keeps _ hP (key _ h2)) k) l)
  have hk' : (HA.mat (F := F) (Fv F v) σ J g⁻¹).1 * (HA.mat (F := F) (Fv F v) σ J g).1 = 1 := by
    rw [← mat_mul, inv_mul_cancel, mat_one]
  have h3 : (P * ((HA.mat (F := F) (Fv F v) σ J g⁻¹).1 * j)) * (P * ((HA.mat (F := F) (Fv F v) σ J g).1 * j)) = 1 := by
    rw [Matrix.mul_assoc P, Matrix.mul_assoc (HA.mat (F := F) (Fv F v) σ J g⁻¹).1, ← hk,
      ← Matrix.mul_assoc (HA.mat (F := F) (Fv F v) σ J g⁻¹).1, hk', Matrix.one_mul, hP]
  exact ⟨⟨_, _, mul_eq_one_comm.1 h3, h3⟩, hk⟩

end Local

theorem iwasawa_span_split : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (a : GL (Fin V.rank) (TensorProduct D.host.F (AF D.host.F) D.host.E)), Φ.IsGood D.sp.cm L a → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v → ∀ (g : GLoc D.sp.cm.sig V.gram v), ∃ q k : GLoc D.sp.cm.sig V.gram v, k ∈ stabLoc D.sp.cm.sig V.gram L v ∧ g = q * k ∧ ∃ β : GL (Fin (wittIndex V)) (TensorProduct D.host.F (Fv D.host.F v) D.host.E), (HA.mat (F := D.host.F) (Fv D.host.F v) D.sp.cm.sig V.gram q).1 * (Matrix.of fun (x : Fin V.rank) (i : Fin (wittIndex V)) => GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR (F := D.host.F) V (Fv D.host.F v) (Φ.e i) x) = (Matrix.of fun (x : Fin V.rank) (i : Fin (wittIndex V)) => GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR (F := D.host.F) V (Fv D.host.F v) (Φ.e i) x) * β.1 := by
  intro D V Φ L a hG v ⟨P, P', hne, hP, hP'⟩ g
  obtain ⟨τ, -⟩ := existsUnique_splitPrime_eq (isCMExt_host D) (v := v) hne (HeightOneSpectrum.ext hP)
    (HeightOneSpectrum.ext hP')
  haveI : Submodule.IsLattice D.host.E L := hG.1
  obtain ⟨k, i, qq, hn, hsum⟩ := exists_compl (cols Φ.e) (cols Φ.f)
    (((cols Φ.f).map D.sp.cm.sig).transpose * V.gram) (((cols Φ.e).map D.sp.cm.sig).transpose * V.gram)
    (fe Φ) (ff Φ) (ee Φ) (ef Φ)
  obtain ⟨B, lv, hB⟩ := GlobalTheory.Core.Rk.IwFlagSplit.exists_flag_basis (v := v) τ (GlobalTheory.Doubling.isHermND_gram V)
    (e := cols Φ.e) (e' := cols Φ.f) (i := i) (p := ((cols Φ.f).map D.sp.cm.sig).transpose * V.gram) (q := qq)
    (Fintype.equivOfCardEq (by simp only [Fintype.card_sum, Fintype.card_fin]; omega)) hsum (ef Φ)
  have hQ : ∀ x : GLoc D.sp.cm.sig V.gram v, (B⁻¹ * splitHom D.sp.cm.sig V.gram τ x * B).1.BlockTriangular lv →
      x ∈ keepGrp (σ := D.sp.cm.sig) (J := V.gram) (v := v) ((cols Φ.e).map (inclR (F := D.host.F) (Fv D.host.F v))) :=
    fun x hx => by
      obtain ⟨⟨b, hb⟩, b', hb'⟩ := hB x hx
      exact keeps_of_split (isCMExt_host D) τ x (fe Φ) hb hb'
  obtain ⟨q, k', hq, hk, rfl⟩ := GlobalTheory.Core.Rk.IwFlagSplit.iwasawa_of_triangular (isCMExt_host D)
    (GlobalTheory.Doubling.isHermND_gram V) τ L (hG.2.1 v) _ B lv hQ g
  obtain ⟨β, hβ⟩ := hq
  refine ⟨q, k', hk, rfl, β, ?_⟩
  rw [coordMat_eq]
  exact hβ

end GlobalTheory.IwSplitFrame
