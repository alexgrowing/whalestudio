import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubGAlgDOne
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieDerivativePolynomialFockArchimedeanUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactUnitaryPreservesPolynomialFockStatement

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped Matrix

noncomputable section

namespace GlobalTheory.HoweRealSmall

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

private theorem det_ne_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let A' : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have h1 : A'ᵀ * M * A'.map star = (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm := by
    rw [← hA]; ext i j; simp [A', Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.map_apply]
  have h2 : (A'ᵀ * M * A'.map star).det ≠ 0 := by
    rw [h1, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
    simp [Matrix.det_neg]
  intro h0
  apply h2
  rw [Matrix.det_mul, Matrix.det_mul, h0]; simp

private theorem det_ne_sig_map {E : Type} [Field E] {n r s : ℕ} {J : Matrix (Fin n) (Fin n) E} (τ : E →+* ℂ) (c : ℂ)
    (h : HasSig (c • J.map τ) r s) : J.det ≠ 0 := by
  intro h0
  apply det_ne_hasSig h
  have e := RingHom.map_det τ J
  rw [RingHom.mapMatrix_apply] at e
  rw [Matrix.det_smul, ← e, h0, map_zero, mul_zero]

private theorem hecke_div {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {χ χ' : Chr F E} (h : GlobalTheory.LFun.IsHecke F E χ) (h' : GlobalTheory.LFun.IsHecke F E χ') :
    GlobalTheory.LFun.IsHecke F E (χ / χ') :=
  ⟨h.1.div' h'.1, fun x => by simp only [MonoidHom.div_apply, h.2 x, h'.2 x, div_self']⟩

private theorem resEta_div {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {K : Subgroup Rˣ}
    {χ χ' : Aˣ →* Circle} {n m k : ℕ} (h : ResEtaPow K χ n) (h' : ResEtaPow K χ' m) (hk : k = n + m) :
    ResEtaPow K (χ / χ') k := by
  subst hk
  intro a
  have e := h a
  have e' := h' a
  rw [MonoidHom.div_apply, Circle.coe_div, e, e']
  split_ifs
  · simp
  · rw [pow_add]
    rcases neg_one_pow_eq_or ℂ m with hm | hm <;> rw [hm] <;> ring

private theorem acts_zero {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (T : Module.End ℂ ((κ → AF F) → ℂ)) :
    Acts (evI F) ⇑T ⇑(0 : SInf F κ) ⇑(0 : SInf F κ) := by
  intro r _
  have e : tens (evI F) (⇑(0 : SInf F κ)) r = 0 := by funext y; simp [tens]
  rw [e, map_zero]

private theorem actsD_zero {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (T : ℝ → Module.End ℂ ((κ → AF F) → ℂ)) :
    ActsD (evI F) (fun t => ⇑(T t)) ⇑(0 : SInf F κ) ⇑(0 : SInf F κ) := by
  intro r _ x
  have e : tens (evI F) (⇑(0 : SInf F κ)) r = 0 := by funext y; simp [tens]
  simp only [e, map_zero, Pi.zero_apply]
  exact hasDerivAt_const _ _

theorem howe_real_ker' : GlobalTheory.Published.HoweDualityReal →
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
      (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a')))),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSubInf G.M' Bs.ψ Bs.emb om' (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a'))), GlobalTheory.Published.ThetaSubInf G.M' Bs.ψ Bs.emb om' N →
        N ≠ G.M'.Pol Bs.ψ Bs.emb → ∀ f ∈ N, R.p' f = 0 := by
  intro hHD F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM
  have hT := hM.triple
  have hg := hT.geo
  have hc := hT.chars
  have hR := hM.real
  obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have dV' : G.V'.J.det ≠ 0 := det_ne_sig_map (Bs.emb w₀).1 1 (by rw [one_smul]; exact hg.hV'.sig w₀)
  have dW : G.W.J.det ≠ 0 := det_ne_sig_map (Bs.emb w₀).1 Complex.I (hg.hW.sig w₀)
  have hres := resEta_div hc.resα hc.resβ (Nat.add_comm a a')
  have hhk := hecke_div hc.heckeα hc.heckeβ
  obtain ⟨hbdd, hsum⟩ := hHD F E σ hT.base.cm a' (a + a') G.V' G.W G.M' Bs.ψ Xc.α (Xc.α / Xc.β) om' hT.base.std
    hg.hV'.herm dV' hg.hW.skew dW hc.resα hres hc.heckeα hhk hT.weil' Bs.emb hg.hV'.cartan hg.hW.cartan
  have hLie := GlobalTheory.T.lieDerivative_polynomialFock_archimedeanUnitary F E σ hT.base.cm a' (a + a') G.V' G.W G.M' Bs.ψ Xc.α (Xc.α / Xc.β) om' hT.base.std
    hg.hV'.herm dV' hg.hW.skew dW hc.resα hres hc.heckeα hhk hT.weil' Bs.emb hg.hV'.cartan hg.hW.cartan
  have hCpt := GlobalTheory.T.compactUnitary_preserves_polynomialFock F E σ hT.base.cm a' (a + a') G.V' G.W G.M' Bs.ψ Xc.α (Xc.α / Xc.β) om' hT.base.std
    hg.hV'.herm dV' hg.hW.skew dW hc.resα hres hc.heckeα hhk hT.weil' Bs.emb hg.hV'.cartan hg.hW.cartan
  refine ⟨hbdd, ?_⟩
  intro N hN hNe φ hφ
  set K : Submodule ℂ (SInf F (Fin a' × Fin (a + a'))) := LinearMap.ker R.p' ⊓ G.M'.Pol Bs.ψ Bs.emb with hKdef
  have hK : GlobalTheory.Published.ThetaSubInf G.M' Bs.ψ Bs.emb om' K := by
    refine ⟨inf_le_right, ?_, ?_, ?_, ?_⟩
    · intro γ hγ f hf f₁ hact
      exact Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 (hR.quot'.lie γ hγ f hf f₁ hact), hN.1 (hN.2.1 γ hγ f hf f₁ hact)⟩
    · intro k hk f hf f₁ hact
      refine Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 ?_, hN.1 (hN.2.2.1 k hk f hf f₁ hact)⟩
      rw [map_sub, hR.quot'.cpt k hk f hf f₁ hact, sub_self]
    · intro γ hγ f hf f₁ hact
      have hf' := Submodule.mem_inf.1 hf
      have hp := hR.lie γ hγ 0 (zero_mem _) f hf'.2 0 f₁
        (actsD_zero (fun t => om (1, γ (Multiplicative.ofAdd t)))) hact
        (by rw [map_zero]; exact (LinearMap.mem_ker.1 hf'.1).symm)
      rw [map_zero] at hp
      exact Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 hp.symm, (hLie γ hγ f hf'.2).2 f₁ hact⟩
    · intro k hk f hf f₁ hact
      have hf' := Submodule.mem_inf.1 hf
      have hp := hR.cpt k hk 0 (zero_mem _) f hf'.2 0 f₁ (acts_zero _) hact
        (by rw [map_zero]; exact (LinearMap.mem_ker.1 hf'.1).symm)
      rw [map_zero] at hp
      exact Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 hp.symm, (hCpt k hk f hf'.2).2 f₁ hact⟩
  have hKne : K ≠ G.M'.Pol Bs.ψ Bs.emb := by
    intro hKe
    have hbot : (G.M'.Pol Bs.ψ Bs.emb).map R.p' = ⊥ := by
      rw [Submodule.eq_bot_iff]
      rintro _ ⟨f, hf, rfl⟩
      rw [← hKe] at hf
      exact LinearMap.mem_ker.1 (Submodule.mem_inf.1 hf).1
    rw [hR.quot'.onto] at hbot
    haveI := hR.nontriv
    exact top_ne_bot hbot
  have hNK : N ⊔ K ≠ G.M'.Pol Bs.ψ Bs.emb := hsum N K hN hK hNe hKne
  rcases hR.irred (N.map R.p') (by
    intro γ hγ f hf f₁ hact hpm
    obtain ⟨n, hn, hpn⟩ := Submodule.mem_map.1 hpm
    obtain ⟨n₁, hactn⟩ := (hLie γ hγ n (hN.1 hn)).1
    rw [hR.lie γ hγ f hf n (hN.1 hn) f₁ n₁ hact hactn hpn.symm]
    exact Submodule.mem_map_of_mem (hN.2.2.2.1 γ hγ n hn n₁ hactn)) (by
    intro k hk f hf f₁ hact hpm
    obtain ⟨n, hn, hpn⟩ := Submodule.mem_map.1 hpm
    obtain ⟨n₁, hactn⟩ := (hCpt k hk n (hN.1 hn)).1
    rw [hR.cpt k hk f hf n (hN.1 hn) f₁ n₁ hact hactn hpn.symm]
    exact Submodule.mem_map_of_mem (hN.2.2.2.2 k hk n hn n₁ hactn)) with h0 | htop
  · have hmem : R.p' φ ∈ N.map R.p' := Submodule.mem_map_of_mem hφ
    rw [h0] at hmem
    exact (Submodule.mem_bot ℂ).1 hmem
  · exfalso
    apply hNK
    refine le_antisymm (sup_le hN.1 inf_le_right) ?_
    intro f hf
    have hm : R.p' f ∈ N.map R.p' := by rw [htop]; exact Submodule.mem_top
    obtain ⟨n, hn, hpn⟩ := Submodule.mem_map.1 hm
    have hk : f - n ∈ K :=
      Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 (by rw [map_sub, hpn, sub_self]), sub_mem hf (hN.1 hn)⟩
    have := Submodule.add_mem_sup hn hk
    rwa [add_sub_cancel] at this

end GlobalTheory.HoweRealSmall

end
