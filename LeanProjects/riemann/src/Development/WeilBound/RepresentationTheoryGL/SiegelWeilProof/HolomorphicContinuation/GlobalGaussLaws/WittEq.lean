import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.WittEqA
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral

noncomputable section

open scoped Matrix ComplexConjugate nonZeroDivisors
open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.WEq

local notation "hermF" => ReciprocityTheory.ChartRestriction.G.FD.herm
local notation "ccF" => ReciprocityTheory.ChartRestriction.G.FD.cc

theorem coord_hT (D : D7) [IsCMField D.host.E] (hst : ∀ z : D.host.E, star z = IsCMField.complexConj D.host.E z)
    (V : HSp D) (x y : Fin V.rank → D.host.E) :
    V.hT (V.frame.equivFun.symm y) (V.frame.equivFun.symm x) = hermF (V.gram)ᵀ x y := by
  simp only [Module.Basis.equivFun_symm_apply, map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
  simp only [ReciprocityTheory.ChartRestriction.G.FD.herm, Matrix.transpose_apply, HSpace.gram, ReciprocityTheory.ChartRestriction.G.FD.cc, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [starRingEnd_apply, hst]
  ring

theorem perm_exists {r k : ℕ} (hk : k ≤ r) (ε : Fin r → Bool) (he : cnt ε true = k) :
    ∃ π : Equiv.Perm (Fin r), ∀ a, ε a = decide (((π a : Fin r) : ℕ) < k) := by
  classical
  have c1 : Fintype.card {a // ε a = true} = Fintype.card {a : Fin r // (a : ℕ) < k} := by
    rw [Fintype.card_subtype]
    have e : {a : Fin r // (a : ℕ) < k} ≃ Fin k :=
      ⟨fun a => ⟨a, a.2⟩, fun i => ⟨⟨i, by omega⟩, i.2⟩, fun _ => rfl, fun _ => rfl⟩
    rw [Fintype.card_congr e, Fintype.card_fin]
    exact he
  have c2 : Fintype.card {a // ¬ ε a = true} = Fintype.card {a : Fin r // ¬ (a : ℕ) < k} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, c1]
  let e1 := Fintype.equivOfCardEq c1
  let e2 := Fintype.equivOfCardEq c2
  refine ⟨(Equiv.sumCompl (fun a => ε a = true)).symm.trans
    ((Equiv.sumCongr e1 e2).trans (Equiv.sumCompl (fun a : Fin r => (a : ℕ) < k))), fun a => ?_⟩
  by_cases h : ε a = true
  · rw [Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_pos (p := fun a => ε a = true) h, Equiv.trans_apply, Equiv.sumCongr_apply,
      Sum.map_inl, Equiv.sumCompl_apply_inl, h]
    exact (decide_eq_true (e1 ⟨a, h⟩).2).symm
  · rw [Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_neg (p := fun a => ε a = true) h, Equiv.trans_apply, Equiv.sumCongr_apply,
      Sum.map_inr, Equiv.sumCompl_apply_inr]
    simp only [Bool.not_eq_true] at h
    rw [h]
    exact (decide_eq_false (e2 ⟨a, by simp [h]⟩).2).symm

theorem wittLBeq : WittLBeq := by
  intro D V k hk hS
  letI hcm : IsCMField D.host.E := D.host.isCMField_hostE
  have hst : ∀ z : D.host.E, star z = IsCMField.complexConj D.host.E z := fun _ => rfl
  set r := V.rank with hrdef
  set G₁ : Matrix (Fin r) (Fin r) D.host.E := (V.gram)ᵀ with hG₁
  let v : (Fin r → D.host.E) ≃ₗ[D.host.E] V.V := V.frame.equivFun.symm
  let L : Submodule (𝓞 D.host.E) (Fin r → D.host.E) :=
    V.L0.map ((V.frame.equivFun : V.V →ₗ[D.host.E] (Fin r → D.host.E)).restrictScalars (𝓞 D.host.E))
  have memL : ∀ x, x ∈ L ↔ v x ∈ V.L0 := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [v] using hy
    · intro hx
      exact ⟨v x, hx, V.frame.equivFun.apply_symm_apply x⟩
  have hL : ReciprocityTheory.MultiplicativeHeights.IsLattice L := by
    refine ⟨V.standardTuple_isLattice.fg.map _, ?_⟩
    have hc : (L : Set (Fin r → D.host.E)) = V.frame.equivFun '' (V.L0 : Set V.V) := by
      ext x; simp [L]
    rw [hc, show (⇑V.frame.equivFun : V.V → (Fin r → D.host.E)) =
        ⇑(V.frame.equivFun : V.V →ₗ[D.host.E] (Fin r → D.host.E)) from rfl, Submodule.span_image,
      V.standardTuple_isLattice.span_eq_top, Submodule.map_top, LinearEquiv.range]
  have hone : ∀ z : D.host.E, z ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) ↔
      z ∈ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
    intro z
    rw [Submodule.mem_one, FractionalIdeal.mem_one_iff]
  have hdual : ∀ z : V.V, z ∈ V.L0 ↔ ∀ y ∈ V.L0, V.hT y z ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
    intro z
    have hu := V.baseLattice_isUnimodular
    unfold Formalism.HermitianLatticesTheory.IsUnimodular Formalism.HermitianLatticesTheory.dual at hu
    conv_lhs => rw [← hu]
    simp [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap]
  have hmod : ∀ x, x ∈ L ↔ ∀ y ∈ L, hermF G₁ x y ∈ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
    intro x
    rw [memL, hdual]
    constructor
    · intro h y hy
      rw [← coord_hT D hst V x y, ← hone]
      exact h _ ((memL y).1 hy)
    · intro h y' hy'
      have hy : V.frame.equivFun y' ∈ L := (memL _).2 (by simpa [v] using hy')
      have := h _ hy
      rw [← coord_hT D hst V x _, ← hone] at this
      simpa [v] using this
  have hG : ∀ a b, ccF (G₁ a b) = G₁ b a := by
    intro a b
    have := V.herm.eq (V.frame b) (V.frame a)
    simp only [hG₁, Matrix.transpose_apply, HSpace.gram, ReciprocityTheory.ChartRestriction.G.FD.cc]
    rw [← hst]
    exact this
  have hd : G₁.det ≠ 0 := by rw [hG₁, Matrix.det_transpose]; exact GlobalTheory.MassLinkSD.gram_det_ne V
  have key : ∀ ρ : D.what₂.Tau, ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧
      (dSgn r k).map (tauE D ρ) = Qᵀ * G₁.map (tauE D ρ) * Q.map (starRingEnd ℂ) := by
    intro ρ
    obtain ⟨ε, fr, hfr, hdiag, hk1, hk2⟩ := hS ρ
    have hc := cnt_add ε
    obtain ⟨π, hπ⟩ := perm_exists (r := r) (k := k) (by omega) ε (by omega)
    let X : Matrix (Fin r) (Fin r) ℂ := (π.symm.toPEquiv).toMatrix
    have hX : X.det ≠ 0 := by
      simp only [X, Matrix.det_permutation]
      rcases Int.units_eq_one_or (Equiv.Perm.sign π.symm) with h | h <;> simp [h]
    have hfr' : fr.det ≠ 0 := hfr.ne_zero
    have hT' : (frᴴ)ᵀ = fr.map (starRingEnd ℂ) := by
      ext i j; simp [Matrix.conjTranspose_apply]
    have h1 : ReciprocityTheory.ChartRestriction.G.FD.gram (tauE D ρ) G₁ fr = Matrix.diagonal (sgn ε) := by
      rw [GlobalTheory.Published.gram_eq, hG₁, Matrix.transpose_map]
      have e : (HSpace.gram V).map (tauE D ρ) = gramAt D V ρ := rfl
      rw [e]
      have := congrArg Matrix.transpose hdiag
      rw [Matrix.diagonal_transpose, Matrix.transpose_mul, Matrix.transpose_mul, hT', ← Matrix.mul_assoc] at this
      exact this
    have h2 : ReciprocityTheory.ChartRestriction.G.FD.gram (tauE D ρ) (dSgn r k) X = Matrix.diagonal (sgn ε) := by
      have hXc : X.map (starRingEnd ℂ) = X := by
        ext i j; simp only [X, Matrix.map_apply, PEquiv.toMatrix_apply]; split_ifs <;> simp
      have hXt : Xᵀ = π.toPEquiv.toMatrix := by
        simp only [X]
        rw [← PEquiv.toMatrix_symm, ← Equiv.toPEquiv_symm, Equiv.symm_symm]
      rw [GlobalTheory.Published.gram_eq, hXc, hXt, PEquiv.toMatrix_toPEquiv_mul]
      simp only [X]
      rw [PEquiv.mul_toMatrix_toPEquiv, Equiv.symm_symm, Matrix.submatrix_submatrix, dSgn,
        Matrix.diagonal_map (map_zero _), Function.comp_id, Function.id_comp, Matrix.submatrix_diagonal_equiv]
      congr 1
      funext a
      have ha := hπ a
      simp only [Function.comp_apply, sgn]
      rw [ha]
      by_cases h : ((π a : Fin r) : ℕ) < k <;> simp [h]
    exact GlobalTheory.Published.Landherr.congr_of_gram_eq (G := G₁) (G' := dSgn r k) (tauE D ρ) hfr' hX (h1.trans h2.symm)
  have hs : ∀ σ : D.host.E →+* ℂ, ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧
      (dSgn r k).map σ = Qᵀ * G₁.map σ * Q.map (starRingEnd ℂ) := by
    intro σ
    by_cases h : ∃ ρ, tauE D ρ = NumberField.ComplexEmbedding.conjugate σ
    · obtain ⟨ρ, hρ⟩ := h
      have := GlobalTheory.Published.Landherr.congr_conjugate (G := G₁) (G' := dSgn r k) (tauE D ρ) (key ρ)
      rw [hρ, NumberField.ComplexEmbedding.involutive_conjugate D.host.E σ] at this
      exact this
    · obtain ⟨ρ, hρ⟩ := (GlobalTheory.PointAtPlace.tauE_cm σ).2 h
      rw [← hρ]
      exact key ρ
  have hL' : ReciprocityTheory.MultiplicativeHeights.IsLattice (GlobalTheory.InertWitt.stdLat D.host.E r) :=
    ⟨(GlobalTheory.InertWitt.stdLat_isLattice D.host.E r).fg, (GlobalTheory.InertWitt.stdLat_isLattice D.host.E r).span_eq_top⟩
  have hcc : ∀ z ∈ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E),
      ccF z ∈ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
    intro z hz
    rw [mem_one_iff_isIntegral] at hz ⊢
    exact cc_isIntegral hz
  haveI : Algebra.Unramified (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) :=
    Formalism.L2.Pj.unramBridge D.host.E (Formalism.L2.Pj.cmUnram_conj D)
  obtain ⟨P, hP, hPG⟩ := GlobalTheory.SelfDualGenus.congr_of_modular (G := G₁) (G' := dSgn r k) (L := L)
    (L' := GlobalTheory.InertWitt.stdLat D.host.E r) (𝔟 := 1)
    (GlobalTheory.LocalQuad.landherr_of_hasseNormSt GlobalTheory.QNorm.hasseNormSt) GlobalTheory.QNorm.hasseNormSt one_ne_zero hcc hG
    (fun a b => dSgn_hermF (r := r) (k := k) a b) hd (dSgn_det (r := r) (k := k)) hL hL' hmod
    (mod_std (r := r) (k := k)) hs
  let f : (Fin k → D.host.E) →ₗ[D.host.E] V.V := v.toLinearMap ∘ₗ P.mulVecLin ∘ₗ extL hk
  have hPi : Function.Injective P.mulVecLin := by
    have hu : IsUnit P := (Matrix.isUnit_iff_isUnit_det P).2 (isUnit_iff_ne_zero.2 hP)
    simpa [Matrix.coe_mulVecLin] using (Matrix.mulVec_injective_iff_isUnit.2 hu)
  have hf : Function.Injective f := v.injective.comp (hPi.comp (extL_injective hk))
  have hfin : Module.finrank D.host.E (LinearMap.range f) = k := by
    rw [LinearMap.finrank_range_of_inj hf, Module.finrank_fin_fun]
  have hiso : ∀ x ∈ LinearMap.range f, ∀ y ∈ LinearMap.range f, V.hT x y = 0 := by
    rintro _ ⟨u, rfl⟩ _ ⟨u', rfl⟩
    show V.hT (v (P *ᵥ ext hk u)) (v (P *ᵥ ext hk u')) = 0
    rw [coord_hT D hst V, GlobalTheory.SelfDualGenus.herm_mulVec, ← hPG, herm_ext]
  unfold Formalism.MainNotions.SchurIrreducible.wittIdx
  refine le_csSup ⟨Module.finrank D.host.E V.V, ?_⟩ ⟨LinearMap.range f, hfin, hiso⟩
  rintro d ⟨W, rfl, -⟩
  exact Submodule.finrank_le W

end PositivityTheory.Rg.Sw.Glob.WEq

namespace PositivityTheory.Rg.Sw.Glob

theorem wittLBeq : WittLBeq := WEq.wittLBeq

end PositivityTheory.Rg.Sw.Glob
