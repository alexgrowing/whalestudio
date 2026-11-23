import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMat
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open GlobalTheory.FlagCls

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.FlagCls.MatGr

open Limits

theorem linearIndependent_repr {R N K : Type} [CommRing R] [AddCommGroup N] [Module R N] [Field K]
    {ι κ : Type} [Fintype ι] [Fintype κ] (b : Module.Basis ι R N) (b' : Module.Basis κ R N) (φ : R →+* K) :
    LinearIndependent K fun k j => φ (b.repr (b' k) j) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg k'
  have key (k : κ) : ∑ j, φ (b.repr (b' k) j) * φ (b'.repr (b j) k') = if k = k' then 1 else 0 := by
    have h1 : ∑ j, b.repr (b' k) j * b'.repr (b j) k' = b'.repr (b' k) k' := by
      conv_rhs => rw [← b.sum_repr (b' k)]
      simp only [map_sum, map_smul, Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul]
    simp only [← map_mul, ← map_sum]
    rw [h1, b'.repr_self, Finsupp.single_apply]
    split_ifs <;> simp
  have h2 (j : ι) : ∑ k, g k * φ (b.repr (b' k) j) = 0 := by
    simpa using congrFun hg j
  have h3 : ∑ k, g k * ∑ j, φ (b.repr (b' k) j) * φ (b'.repr (b j) k') = 0 := by
    simp only [Finset.mul_sum, ← mul_assoc]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, h2, zero_mul, Finset.sum_const_zero]
  simpa [key] using h3

theorem card_le_of_rows {K : Type} [Field K] {r n : ℕ} (hn : n ≤ r) (A : Matrix (Fin r) (Fin r) K)
    {κ : Type} [Fintype κ] (v : κ → Fin r → K) (hv : LinearIndependent K v)
    (h : ∀ k, ∃ cf : Fin r → K, (∀ l : Fin r, n ≤ l → cf l = 0) ∧ v k = Matrix.vecMul cf A) :
    Fintype.card κ ≤ n := by
  choose cf h0 h1 using h
  let L : (Fin n → K) →ₗ[K] (Fin r → K) := Fintype.linearCombination K fun l => A (Fin.castLE hn l)
  have e : v = L ∘ fun k l => cf k (Fin.castLE hn l) := by
    funext k
    rw [h1, Matrix.vecMul_eq_sum, Function.comp_apply, Fintype.linearCombination_apply]
    symm
    refine Finset.sum_of_injOn (Fin.castLE hn) (Fin.castLE_injective hn).injOn
      (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) (fun j _ hj => ?_) (fun _ _ => rfl)
    rw [h0 k j (Nat.le_of_not_lt fun hlt => hj ⟨⟨j, hlt⟩, by simp, Fin.ext rfl⟩), zero_smul]
  rw [e] at hv
  simpa using (LinearIndependent.of_comp L hv).fintype_card_le_finrank

end GlobalTheory.FlagCls.MatGr

open Limits GlobalTheory.FlagCls.MatGr in

theorem GlobalTheory.FlagCls.FlagMat.coeff_ne_zero : ∀ (B Y : Scheme.{0}) (M : B.Modules) (r : ℕ) (hM : IsVB M r) (π : Y ⟶ B) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj M) r) (V : B.Opens) (f : Fin r → Γ(M, V)) (hf : IsFrame f) (K : Type) [Field K] (y : Sp K ⟶ Y) (A : Matrix (Fin r) (Fin r) K), FlagMat hM π fl hf y A → ∀ (i : Fin r) (ch : Chart (fl.gr i) 1) (W : Y.Opens) (hW : W ≤ ch.U) (hWV : W ≤ π ⁻¹ᵁ V) (t : Γ(fl.F i.succ, W)), (fl.π i).app W t = Twist.resM _ hW (ch.e 0) → ∀ (hy : ⊤ ≤ y ⁻¹ᵁ W) (cf : Fin r → K), coordAt hM π hf y hWV hy ((fl.ι i.succ).app W t) = Matrix.vecMul cf A → cf i ≠ 0 := by
  intro B Y M r hM π fl V f hf K _ y A hA i ch W hW hWV t ht hy cf hcf h0
  have := hM.isQuasicoherent
  let p : Sp K := IsLocalRing.closedPoint K
  have hp : y p ∈ W := hy (Set.mem_univ p)
  obtain ⟨U₁, a, hp₁, ha⟩ := fl.isVB i.castSucc (y p)
  obtain ⟨U₂, c, hp₂, hc⟩ := fl.isVB_cokernel i.succ (y p)
  obtain ⟨U₃, h₃, hp₃, u, hu⟩ := VBExt.exists_lifts (cokernel.π (fl.ι i.succ)) c hp₂
  let U : Y.Opens := W ⊓ (U₁ ⊓ U₃)
  have hUW : U ≤ W := inf_le_left
  have hU₁ : U ≤ U₁ := inf_le_right.trans inf_le_left
  have hU₃ : U ≤ U₃ := inf_le_right.trans inf_le_right
  have hyU : ⊤ ≤ y ⁻¹ᵁ U := fun q _ => by
    obtain rfl : q = p := Subsingleton.elim (α := PrimeSpectrum K) _ _
    exact ⟨hp, hp₁, hp₃⟩
  have f₁ := VBExt.isFrame_sumElim (S := .mk (fl.step i) (cokernel.π _) (cokernel.condition _))
    { exact := ShortComplex.exact_cokernel _ } (ha.res hU₁) (t := fun _ : Fin 1 => Twist.resM _ hUW t) (by
      have h := ch.isFrame.res (hUW.trans hW)
      change IsFrame fun _ : Fin 1 => (fl.π i).app U (Twist.resM _ hUW t)
      convert h using 2 with k
      obtain rfl : k = 0 := Subsingleton.elim _ _
      rw [Twist.app_resM, ht, Twist.resM_resM])
  have f₂ := VBExt.isFrame_sumElim (S := .mk (fl.ι i.succ) (cokernel.π _) (cokernel.condition _))
    { exact := ShortComplex.exact_cokernel _ } f₁ (t := fun k => Twist.resM _ hU₃ (u k)) (by
      have h := hc.res (hU₃.trans h₃)
      convert h using 2 with k
      change (cokernel.π (fl.ι i.succ)).app U _ = _
      rw [Twist.app_resM, hu, Twist.resM_resM])
  have li := (linearIndependent_repr ((hf.pullback π).basis (hUW.trans hWV)) (f₂.basis le_rfl)
    (TangentOrigin.evalPt y U hyU)).comp Sum.inl Sum.inl_injective
  have hle := card_le_of_rows (n := i) i.2.le A _ li (by
    rintro (k | k)
    · obtain ⟨cf', h1, h2⟩ := hA.2 i.castSucc U (hUW.trans hWV) (Twist.resM _ hU₁ (a k)) hyU
      refine ⟨cf', h1, Eq.trans ?_ h2⟩
      funext j
      simp only [Function.comp_apply, IsFrame.basis_apply, Twist.resM_self, Sum.elim_inl, coordAt]
      rw [← fl.step_ι i]
      rfl
    · obtain ⟨cf', h1, h2⟩ := hA.2 i.succ W hWV t hy
      obtain rfl : cf = cf' := by
        have := Matrix.vecMul_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det A).2 hA.1)
        exact this (hcf.symm.trans h2)
      refine ⟨cf, fun l hl => ?_, Eq.trans ?_ hcf⟩
      · rcases eq_or_lt_of_le hl with e | e
        · rwa [← Fin.ext e]
        · exact h1 l e
      · funext j
        simp only [Function.comp_apply, IsFrame.basis_apply, Twist.resM_self, Sum.elim_inl, Sum.elim_inr, coordAt]
        rw [Twist.app_resM, (hf.pullback π).repr_resM hWV hUW]
        exact TangentOrigin.evalPt_res y hUW hy hyU _)
  simp at hle

end
