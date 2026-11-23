import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubGAlgDOne
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AlgAtLeAlgD
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelInfAlt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorEqTopOrLeKerFiniteLengthModulesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLinearTensorPolyVacuumPureTensorsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstMemberLieAlgebraPreservesPolynomialFockStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstMemberMaximalCompactPreservesPolynomialFockStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsOrbitKernelStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HoweDualityRealPlacesPolynomialVectorsSmallPairStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryDualPairGlobalToLocalTensorTransferStatement

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct
open scoped Matrix

noncomputable section

namespace GlobalTheory.HoweGlobalPair

theorem decomp {M₀ : Type} [AddCommGroup M₀] [Module ℂ M₀] {ι : Type} [Fintype ι] {M : ι → Type}
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)] (t : M₀ ⊗[ℂ] (⨂[ℂ] i, M i)) :
    ∃ (m : ℕ) (f : Fin m → M₀) (φ : Fin m → ∀ i, M i), t = ∑ j, f j ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (φ j) := by
  classical

  have join : ∀ t₁ t₂ : M₀ ⊗[ℂ] (⨂[ℂ] i, M i),
      (∃ (m : ℕ) (f : Fin m → M₀) (φ : Fin m → ∀ i, M i), t₁ = ∑ j, f j ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (φ j)) →
      (∃ (m : ℕ) (f : Fin m → M₀) (φ : Fin m → ∀ i, M i), t₂ = ∑ j, f j ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (φ j)) →
      ∃ (m : ℕ) (f : Fin m → M₀) (φ : Fin m → ∀ i, M i), t₁ + t₂ = ∑ j, f j ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (φ j) := by
    rintro t₁ t₂ ⟨m₁, f₁, φ₁, rfl⟩ ⟨m₂, f₂, φ₂, rfl⟩
    refine ⟨m₁ + m₂, Fin.append f₁ f₂, Fin.append φ₁ φ₂, ?_⟩
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  | tmul x y =>
    induction y using PiTensorProduct.induction_on with
    | smul_tprod r g =>
      refine ⟨1, fun _ => r • x, fun _ => g, ?_⟩
      rw [Fin.sum_univ_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    | add y₁ y₂ h₁ h₂ =>
      rw [TensorProduct.tmul_add]
      exact join _ _ h₁ h₂
  | add t₁ t₂ h₁ h₂ => exact join _ _ h₁ h₂

theorem det_ne_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h

  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let B : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have key : Bᵀ * M * B.map star =
      (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).submatrix e.symm e.symm := by
    rw [← hA]
    ext i j
    simp [B, Matrix.mul_apply]
  have hdet := congrArg Matrix.det key
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_mul, Matrix.det_mul] at hdet
  intro h0
  rw [h0, mul_zero, zero_mul, Matrix.det_one, one_mul, Matrix.det_neg, Matrix.det_one, mul_one] at hdet
  exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero) hdet.symm

theorem det_ne_sig_map {E : Type} [Field E] {n r s : ℕ} {J : Matrix (Fin n) (Fin n) E} (τ : E →+* ℂ) (c : ℂ)
    (h : HasSig (c • J.map τ) r s) : J.det ≠ 0 := by
  intro h0
  apply det_ne_hasSig h
  have hmap : (J.map τ).det = τ J.det := (RingHom.map_det τ J).symm
  rw [Matrix.det_smul, hmap, h0, map_zero, mul_zero]

theorem hecke_div {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {χ χ' : Chr F E} (h : GlobalTheory.LFun.IsHecke F E χ) (h' : GlobalTheory.LFun.IsHecke F E χ') :
    GlobalTheory.LFun.IsHecke F E (χ / χ') := by
  refine ⟨?_, fun x => ?_⟩
  · have hc : Continuous fun z => χ z / χ' z := h.1.div' h'.1
    exact hc
  · rw [MonoidHom.div_apply, h.2 x, h'.2 x, div_one]

theorem resEta_div {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {K : Subgroup Rˣ}
    {χ χ' : Aˣ →* Circle} {n m k : ℕ} (h : ResEtaPow K χ n) (h' : ResEtaPow K χ' m) (hk : k = n + m) :
    ResEtaPow K (χ / χ') k := by
  subst hk
  intro x
  rw [MonoidHom.div_apply, Circle.coe_div, h x, h' x]
  split_ifs
  · exact div_one 1
  · rw [pow_add, div_eq_mul_inv, ← inv_pow, inv_neg, inv_one]

theorem stage : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    (∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ ((Fin a' × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ)),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSub om' v (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ ((Fin a' × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ), GlobalTheory.Published.ThetaSub om' v N →
        N ≠ GlobalTheory.WeilM.SB _ → ∀ φ ∈ N, Rf.p' v φ = 0) →
    ((∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a')))),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSubInf G.M' Bs.ψ Bs.emb om' (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a'))), GlobalTheory.Published.ThetaSubInf G.M' Bs.ψ Bs.emb om' N →
        N ≠ G.M'.Pol Bs.ψ Bs.emb → ∀ f ∈ N, R.p' f = 0) →
    ∀ N : Submodule ℂ ((Fin a' × Fin (a + a') → AF F) → ℂ), GlobalTheory.SquareAgree.IsThetaSubG G.M' Bs.ψ Bs.emb om' N →
      ∀ T : Finset (Pl F), Xc.T ⊆ T →
        GlobalTheory.HoweGlobal.algAt G.M' Bs.ψ Bs.emb T ≤ N ∨
          ∀ Φ ∈ N, Φ ∈ GlobalTheory.HoweGlobal.algAt G.M' Bs.ψ Bs.emb T → PolMatch Bs G Xc R Rf 0 Φ := by
  intro F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM hfin hR N hN T hT
  classical
  have hb := hM.triple.base
  have hg := hM.triple.geo
  have hc := hM.triple.chars

  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hdetV : G.V'.J.det ≠ 0 :=
    det_ne_sig_map (Bs.emb w).1 1 (by rw [one_smul]; exact hg.hV'.sig w)
  have hdetW : G.W.J.det ≠ 0 := det_ne_sig_map (Bs.emb w).1 Complex.I (hg.hW.sig w)

  have hres : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range (Xc.α / Xc.β) (a + a') :=
    resEta_div hc.resα hc.resβ (Nat.add_comm a a')
  have hhk : GlobalTheory.LFun.IsHecke F E (Xc.α / Xc.β) := hecke_div hc.heckeα hc.heckeβ

  have hLie := GlobalTheory.T.firstMember_lieAlgebra_preserves_polynomialFock F E σ hb.cm a' (a + a') G.V' G.W G.M' Bs.ψ Xc.α (Xc.α / Xc.β) om' hb.std
    hg.hV'.herm hdetV hg.hW.skew hdetW hc.resα hres hc.heckeα hhk hM.triple.weil' Bs.emb hg.hV'.cartan hg.hW.cartan
  have hCpt := GlobalTheory.T.firstMember_maximalCompact_preserves_polynomialFock F E σ hb.cm a' (a + a') G.V' G.W G.M' Bs.ψ Xc.α (Xc.α / Xc.β) om' hb.std
    hg.hV'.herm hdetV hg.hW.skew hdetW hc.resα hres hc.heckeα hhk hM.triple.weil' Bs.emb hg.hV'.cartan hg.hW.cartan

  obtain ⟨r₀, c₀, k₀, rel₀, st₀⟩ := GlobalTheory.T.howeDuality_realPlaces_polynomialVectors_smallPair F E σ Bs a a' G Xc om om' R Rf hM hR hLie hCpt
  have hloc := fun v : T => GlobalTheory.T.matched_maps_orbit_kernel F E σ Bs a a' G Xc om om' R Rf hM hfin v.1

  have hvac : ∀ v, G.M'.vac v ∈ SB (Fin a' × Fin (a + a') → Fv F v) := fun v => (hg.hM'.vac v).1
  obtain ⟨L, hL, hrange⟩ := GlobalTheory.T.exists_linear_tensor_polyVacuum_pureTensors G.M' Bs.ψ Bs.emb hg.hM'.std T
  obtain ⟨h₁, h₂, h₃, h₄⟩ := GlobalTheory.T.unitaryDualPair_global_to_local_tensor_transfer G.M' Bs.ψ Bs.emb om' hvac hg.hM'.std N hN T L hL

  have hdich := GlobalTheory.T.tensor_eq_top_or_le_ker_finiteLength_modules (ι := T) (M₀ := ↥(G.M'.Pol Bs.ψ Bs.emb)) (P₀ := R.Pi)
    (M := fun v : T => ↥(SB (Fin a' × Fin (a + a') → Fv F v.1))) (P := fun v : T => Rf.Pi v.1)
    (GlobalTheory.HoweGlobalPair.opInf G.M' Bs.ψ Bs.emb om') (fun v => GlobalTheory.HoweGlobalPair.opFin om' v.1)
    (GlobalTheory.HoweGlobalPair.relInf G.M' Bs.ψ Bs.emb om') (fun v => GlobalTheory.HoweGlobalPair.relFin om' v.1)
    (R.p' ∘ₗ (G.M'.Pol Bs.ψ Bs.emb).subtype)
    (fun v => Rf.p' v.1 ∘ₗ (SB (Fin a' × Fin (a + a') → Fv F v.1)).subtype)
    r₀ (fun v => (hloc v).1) c₀ k₀ rel₀ st₀ (fun v => (hloc v).2.1) (fun v => (hloc v).2.2.1)
    (fun v => (hloc v).2.2.2.1) (fun v => (hloc v).2.2.2.2) (N.comap L)
    (fun x hx y => h₁ x hx y) (fun v x hx x₀ y => h₂ v x hx x₀ y) (fun g hg t ht => h₃ g hg t ht)
    (fun v g hg t ht => h₄ v g hg t ht)
  rcases hdich with htop | hker
  · left
    intro Φ hΦ
    obtain ⟨t, rfl⟩ := hrange hΦ
    have ht : t ∈ N.comap L := by rw [htop]; exact Submodule.mem_top
    exact ht
  · right
    intro Φ hΦN hΦA
    obtain ⟨t, rfl⟩ := hrange hΦA
    have hk : t ∈ LinearMap.ker _ := hker (show t ∈ N.comap L from hΦN)
    obtain ⟨m, f, φ, rfl⟩ := decomp t
    rw [LinearMap.mem_ker, map_sum] at hk

    let φ' : Fin m → ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ := fun j v =>
      if h : v ∈ T then (φ j ⟨v, h⟩ : (Fin a' × Fin (a + a') → Fv F v) → ℂ) else G.M'.vac v
    have hin : ∀ j v (h : v ∈ T), φ' j v = φ j ⟨v, h⟩ := fun j v h => dif_pos h
    have hout : ∀ j, ∀ v ∉ T, φ' j v = G.M'.vac v := fun j v h => dif_neg h
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch
    refine ⟨T, hT, 0, m, Fin.elim0, Fin.elim0, fun j => (f j : SInf F _), φ', fun i => i.elim0, fun j => ?_, ?_, ?_, ?_⟩
    · refine ⟨(f j).2, fun v => ?_, hout j⟩
      by_cases h : v ∈ T
      · rw [hin j v h]; exact (φ j ⟨v, h⟩).2
      · rw [hout j v h]; exact hvac v
    · simp
    · rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => hL (f j) (φ j) (φ' j) (hin j) (hout j)
    · rw [Finset.univ_eq_empty, Finset.sum_empty, ← hk]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [TensorProduct.map_tmul, PiTensorProduct.map_tprod, LinearMap.comp_apply, Submodule.subtype_apply]
      refine congrArg (TensorProduct.tmul ℂ (R.p' (f j : SInf F _)))
        (congrArg (PiTensorProduct.tprod ℂ (s := fun v : T => Rf.Pi v.1)) (funext fun v => ?_))
      rw [hin j v.1 v.2]
      rfl

theorem allInKer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    (∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ ((Fin a' × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ)),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSub om' v (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ ((Fin a' × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ), GlobalTheory.Published.ThetaSub om' v N →
        N ≠ GlobalTheory.WeilM.SB _ → ∀ φ ∈ N, Rf.p' v φ = 0) →
    ((∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a')))),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSubInf G.M' Bs.ψ Bs.emb om' (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a'))), GlobalTheory.Published.ThetaSubInf G.M' Bs.ψ Bs.emb om' N →
        N ≠ G.M'.Pol Bs.ψ Bs.emb → ∀ f ∈ N, R.p' f = 0) →
    ∀ N : Submodule ℂ ((Fin a' × Fin (a + a') → AF F) → ℂ), GlobalTheory.SquareAgree.IsThetaSubG G.M' Bs.ψ Bs.emb om' N →
      N ≠ GlobalTheory.SquareAgree.algD G.M' Bs.ψ Bs.emb → ∀ Φ ∈ N, PolMatch Bs G Xc R Rf 0 Φ := by
  intro F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM hfin hR N hN hne Φ hΦ

  obtain ⟨Ψ, hΨ, hΨN⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hN.le hne)

  obtain ⟨T₁, hT₁, hΦ₁⟩ := GlobalTheory.HoweGlobal.exists_algAt G.M' Bs.ψ Bs.emb (hN.le hΦ) Xc.T
  obtain ⟨T, hT, hΨT⟩ := GlobalTheory.HoweGlobal.exists_algAt G.M' Bs.ψ Bs.emb hΨ T₁
  have hΦT := GlobalTheory.HoweGlobal.algAt_mono G.M' Bs.ψ Bs.emb hT hΦ₁
  rcases stage F E σ Bs a a' G Xc om om' R Rf hM hfin hR N hN T (hT₁.trans hT) with hle | hmatch
  · exact absurd (hle hΨT) hΨN
  · exact hmatch Φ hΦ hΦT

end GlobalTheory.HoweGlobalPair

end
