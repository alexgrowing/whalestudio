import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieDerivativePolynomialFockArchimedeanUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactUnitaryPreservesPolynomialFockStatement

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix

namespace GlobalTheory.HoweRealKer

theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let A' : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have hA' : A'ᵀ * M * A'.map star = (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm := by
    rw [← hA]
    ext i j
    simp [A', Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, Matrix.map_apply]
  have hD : (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1 : Matrix (Fin s) (Fin s) ℂ)).det ≠ 0 := by
    rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul, Matrix.det_neg, Matrix.det_one, mul_one]
    simp
  intro hM
  apply hD
  rw [← Matrix.det_submatrix_equiv_self e.symm, ← hA', Matrix.det_mul, Matrix.det_mul, hM, mul_zero, zero_mul]

theorem det_ne_zero_of_sig {E : Type} [Field E] {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (f : E →+* ℂ) {r s : ℕ} (h : HasSig (J.map f) r s) : J.det ≠ 0 := by
  intro hJ
  apply det_ne_zero_of_hasSig h
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hJ, map_zero]

theorem det_ne_zero_of_sigI {E : Type} [Field E] {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (f : E →+* ℂ) {r s : ℕ} (h : HasSig (Complex.I • J.map f) r s) : J.det ≠ 0 := by
  intro hJ
  apply det_ne_zero_of_hasSig h
  rw [Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hJ, map_zero, mul_zero]

theorem resEtaPow_div {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {χ χ' : Chr F E} {n m : ℕ}
    (h : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ n)
    (h' : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ' m) :
    ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range (χ / χ') (n + m) := by
  intro x
  rw [MonoidHom.div_apply, Circle.coe_div, h x, h' x]
  split_ifs
  · simp
  · rw [pow_add]
    rcases neg_one_pow_eq_or ℂ m with hm | hm <;> rw [hm] <;> ring

theorem isHecke_div {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {χ χ' : Chr F E} (h : IsHecke F E χ) (h' : IsHecke F E χ') : IsHecke F E (χ / χ') :=
  ⟨h.1.div' h'.1, fun x => by simp only [MonoidHom.div_apply, h.2 x, h'.2 x, div_self']⟩

theorem actsD_zero {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (T : ℝ → ((κ → AF F) → ℂ) →ₗ[ℂ] (κ → AF F) → ℂ) :
    ActsD (evI F) (fun t => T t) ((0 : SInf F κ) : (κ → mixedEmbedding.mixedSpace F) → ℂ) ((0 : SInf F κ) : _) := by
  intro r _ x
  have h0 : tens (evI F) ((0 : SInf F κ) : (κ → mixedEmbedding.mixedSpace F) → ℂ) r = 0 := by
    funext y; simp [tens]
  simp only [h0, map_zero, Pi.zero_apply]
  exact hasDerivAt_const 0 0

theorem acts_zero {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (T : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ → AF F) → ℂ) :
    Acts (evI F) T ((0 : SInf F κ) : (κ → mixedEmbedding.mixedSpace F) → ℂ) ((0 : SInf F κ) : _) := by
  intro r _
  have h0 : tens (evI F) ((0 : SInf F κ) : (κ → mixedEmbedding.mixedSpace F) → ℂ) r = 0 := by
    funext y; simp [tens]
  simp only [h0, map_zero]

theorem main : GlobalTheory.Published.HoweDualityReal → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
      (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')))),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSubInf G.M Bs.ψ Bs.emb om (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a'))), GlobalTheory.Published.ThetaSubInf G.M Bs.ψ Bs.emb om N →
        N ≠ G.M.Pol Bs.ψ Bs.emb → ∀ f ∈ N, R.p f = 0 := by
  intro hHD F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hMt
  obtain ⟨ht, hr, -⟩ := hMt
  have w0 : InfinitePlace F := Classical.arbitrary _
  have hVdet : G.V.J.det ≠ 0 := det_ne_zero_of_sig _ _ (ht.geo.hV.sig w0)
  have hV'det : G.V'.J.det ≠ 0 := det_ne_zero_of_sig _ _ (ht.geo.hV'.sig w0)
  have hWdet : G.W.J.det ≠ 0 := det_ne_zero_of_sigI _ _ (ht.geo.hW.sig w0)
  have hresW : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range (Xc.β / Xc.α) (a + a') :=
    resEtaPow_div ht.chars.resβ ht.chars.resα
  have hresW' : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range (Xc.α / Xc.β) (a' + a) :=
    resEtaPow_div ht.chars.resα ht.chars.resβ
  rw [Nat.add_comm a' a] at hresW'
  have hHk := isHecke_div ht.chars.heckeβ ht.chars.heckeα
  have hHk' := isHecke_div ht.chars.heckeα ht.chars.heckeβ
  obtain ⟨hchain, hsum⟩ := hHD F E σ ht.base.cm a (a + a') G.V G.W G.M Bs.ψ Xc.β (Xc.β / Xc.α) om ht.base.std
    ht.geo.hV.herm hVdet ht.geo.hW.skew hWdet ht.chars.resβ hresW ht.chars.heckeβ hHk ht.weil Bs.emb
    ht.geo.hV.cartan ht.geo.hW.cartan
  have L := GlobalTheory.T.lieDerivative_polynomialFock_archimedeanUnitary F E σ ht.base.cm a (a + a') G.V G.W G.M Bs.ψ Xc.β (Xc.β / Xc.α) om ht.base.std
    ht.geo.hV.herm hVdet ht.geo.hW.skew hWdet ht.chars.resβ hresW ht.chars.heckeβ hHk ht.weil Bs.emb
    ht.geo.hV.cartan ht.geo.hW.cartan
  have L' := GlobalTheory.T.lieDerivative_polynomialFock_archimedeanUnitary F E σ ht.base.cm a' (a + a') G.V' G.W G.M' Bs.ψ Xc.α (Xc.α / Xc.β) om' ht.base.std
    ht.geo.hV'.herm hV'det ht.geo.hW.skew hWdet ht.chars.resα hresW' ht.chars.heckeα hHk' ht.weil' Bs.emb
    ht.geo.hV'.cartan ht.geo.hW.cartan
  have C := GlobalTheory.T.compactUnitary_preserves_polynomialFock F E σ ht.base.cm a (a + a') G.V G.W G.M Bs.ψ Xc.β (Xc.β / Xc.α) om ht.base.std
    ht.geo.hV.herm hVdet ht.geo.hW.skew hWdet ht.chars.resβ hresW ht.chars.heckeβ hHk ht.weil Bs.emb
    ht.geo.hV.cartan ht.geo.hW.cartan
  have C' := GlobalTheory.T.compactUnitary_preserves_polynomialFock F E σ ht.base.cm a' (a + a') G.V' G.W G.M' Bs.ψ Xc.α (Xc.α / Xc.β) om' ht.base.std
    ht.geo.hV'.herm hV'det ht.geo.hW.skew hWdet ht.chars.resα hresW' ht.chars.heckeα hHk' ht.weil' Bs.emb
    ht.geo.hV'.cartan ht.geo.hW.cartan
  refine ⟨hchain, ?_⟩
  intro N hN hNP

  set P := G.M.Pol Bs.ψ Bs.emb with hPdef
  let K : Submodule ℂ (SInf F (Fin a × Fin (a + a'))) := LinearMap.ker R.p ⊓ P
  have hK : GlobalTheory.Published.ThetaSubInf G.M Bs.ψ Bs.emb om K := by
    refine ⟨inf_le_right, ?_, ?_, ?_, ?_⟩
    · intro γ hγ g hg g₁ hg₁
      exact ⟨LinearMap.mem_ker.mpr (hr.quot.lie γ hγ g hg g₁ hg₁), hN.1 (hN.2.1 γ hγ g hg g₁ hg₁)⟩
    · intro k hk g hg g₁ hg₁
      refine ⟨?_, hN.1 (hN.2.2.1 k hk g hg g₁ hg₁)⟩
      show R.p (g₁ - g) = 0
      rw [map_sub, hr.quot.cpt k hk g hg g₁ hg₁, sub_self]
    · intro γ hγ g hg g₁ hg₁
      refine ⟨?_, (L γ hγ g hg.2).2 g₁ hg₁⟩
      have e := hr.lie γ hγ g hg.2 0 (Submodule.zero_mem _) g₁ 0 hg₁ (actsD_zero _)
        (by rw [LinearMap.mem_ker.mp hg.1, map_zero])
      show R.p g₁ = 0
      rw [e, map_zero]
    · intro k hk g hg g₁ hg₁
      refine ⟨?_, (C k hk g hg.2).2 g₁ hg₁⟩
      have e := hr.cpt k hk g hg.2 0 (Submodule.zero_mem _) g₁ 0 hg₁ (acts_zero _)
        (by rw [LinearMap.mem_ker.mp hg.1, map_zero])
      show R.p g₁ = 0
      rw [e, map_zero]
  have hKP : K ≠ P := by
    intro hKP
    haveI := hr.nontriv
    have hle : P ≤ LinearMap.ker R.p := hKP ▸ inf_le_left
    have hbot : P.map R.p = ⊥ := by
      rw [eq_bot_iff, Submodule.map_le_iff_le_comap]
      intro x hx
      simpa [Submodule.mem_comap] using hle hx
    exact bot_ne_top (hbot.symm.trans hr.quot.onto)

  have hirr := hr.irred (N.map R.p) ?_ ?_
  · rcases hirr with hbot | htop
    · intro f hf
      have : R.p f ∈ N.map R.p := Submodule.mem_map_of_mem hf
      rw [hbot] at this
      exact (Submodule.mem_bot ℂ).mp this
    · exfalso
      apply hsum N K hN hK hNP hKP
      refine le_antisymm (sup_le hN.1 inf_le_right) ?_
      intro g hg
      have hpg : R.p g ∈ N.map R.p := htop ▸ Submodule.mem_top
      obtain ⟨n₀, hn₀, hpn⟩ := hpg
      have hk : g - n₀ ∈ K := ⟨show R.p (g - n₀) = 0 by rw [map_sub, hpn, sub_self], P.sub_mem hg (hN.1 hn₀)⟩
      have := Submodule.add_mem_sup hn₀ hk
      simpa using this
  · intro γ hγ g hg g₁ hg₁ hpg
    obtain ⟨n₀, hn₀, hpn⟩ := hpg
    have hg' : R.p g ∈ (G.M'.Pol Bs.ψ Bs.emb).map R.p' := hr.quot'.onto ▸ Submodule.mem_top
    obtain ⟨g', hg'P, hpg'⟩ := hg'
    obtain ⟨g₁', hg₁'⟩ := (L' γ hγ g' hg'P).1
    obtain ⟨n₁, hn₁⟩ := (L γ hγ n₀ (hN.1 hn₀)).1
    have e1 := hr.lie γ hγ g hg g' hg'P g₁ g₁' hg₁ hg₁' hpg'.symm
    have e2 := hr.lie γ hγ n₀ (hN.1 hn₀) g' hg'P n₁ g₁' hn₁ hg₁' (hpn.trans hpg'.symm)
    exact ⟨n₁, hN.2.2.2.1 γ hγ n₀ hn₀ n₁ hn₁, e2.trans e1.symm⟩
  · intro k hk g hg g₁ hg₁ hpg
    obtain ⟨n₀, hn₀, hpn⟩ := hpg
    have hg' : R.p g ∈ (G.M'.Pol Bs.ψ Bs.emb).map R.p' := hr.quot'.onto ▸ Submodule.mem_top
    obtain ⟨g', hg'P, hpg'⟩ := hg'
    obtain ⟨g₁', hg₁'⟩ := (C' k hk g' hg'P).1
    obtain ⟨n₁, hn₁⟩ := (C k hk n₀ (hN.1 hn₀)).1
    have e1 := hr.cpt k hk g hg g' hg'P g₁ g₁' hg₁ hg₁' hpg'.symm
    have e2 := hr.cpt k hk n₀ (hN.1 hn₀) g' hg'P n₁ g₁' hn₁ hg₁' (hpn.trans hpg'.symm)
    exact ⟨n₁, hN.2.2.2.2 k hk n₀ hn₀ n₁ hn₁, e2.trans e1.symm⟩

end GlobalTheory.HoweRealKer
