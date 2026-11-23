import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIntegralSplitIdempotentOverTwo
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OneEqSumPlaceIdempotentsOverTwoAddTwoMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CmAdeleIdempotentOfPlacePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaInnerProductHermitianStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilMatrixComponentAtPlaceMemCompletedLatticeStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceCompress

open GlobalTheory.SplitScalar

variable {D : D7}

theorem exists_half_idem (v : FinPl D) (h : (2 : 𝓞 D.host.F) ∉ v.asIdeal) :
    ∃ b : AE D, finPart D b ∈ intAE D ∧ b + b = idem D (.inl v) := by
  have h2 : algebraMap D.host.F (Fv D.host.F v) (2 : D.host.F)⁻¹ ∈ v.adicCompletionIntegers D.host.F :=
    GlobalTheory.LatVac.half_mem_adicCompletionIntegers D.host.F v h
  have hsum : algebraMap D.host.F (Fv D.host.F v) (2 : D.host.F)⁻¹ +
      algebraMap D.host.F (Fv D.host.F v) (2 : D.host.F)⁻¹ = 1 := by
    rw [← map_add, ← two_mul, mul_inv_cancel₀ two_ne_zero, map_one]
  refine ⟨algebraMap (AF D.host.F) (AE D) (GlobalTheory.SplitIdem.placeHom D.host.F v
      (algebraMap D.host.F (Fv D.host.F v) (2 : D.host.F)⁻¹)), ?_, ?_⟩
  · unfold intAE finPart
    refine AddSubgroup.subset_closure ⟨_, GlobalTheory.SplitIdem.singleV_mem_intAf D.host.F v ⟨_, h2⟩, 1, ?_⟩
    simp [GlobalTheory.SplitIdem.placeHom, Algebra.TensorProduct.algebraMap_apply] <;> rfl
  · rw [← map_add, ← map_add, hsum]
    rfl

variable {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}
  {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}

theorem exists_char_act (v : FinPl D) {u : WO S T} (hu : u ∈ latO S T LS LT fun w => w = v)
    (hi : idem D (.inl v) • u = u) :
    ∃ y : AF D.host.F, ∀ f, IsLatVac (heisO ψ S T) (latO S T LS LT fun w => w = v) f →
      heisO ψ S T u f = ψ y • f := by
  classical
  have hidem := (GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D).2.2.2.1 v
  by_cases h2 : (2 : 𝓞 D.host.F) ∈ v.asIdeal
  · obtain ⟨e, hee, hec, hsum, -⟩ := GlobalTheory.SplitIdem.exists_split_idempotent D v h2
    have hsum' : e + cA D e = idem D (.inl v) := by rw [hsum]; rfl
    have hsp : IsSplitIdem D e := by
      unfold IsSplitIdem
      exact ⟨hee, hec, v, _, hidem.2.2, hsum⟩
    have hsp' : IsSplitIdem D (cA D e) := isSplitIdem_conj hsp
    have hcc : cA D e * cA D e = cA D e := by rw [← map_mul, hee]
    have hint : finPart D e ∈ intAE D :=
      GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, hee])
    have hint' : finPart D (cA D e) ∈ intAE D :=
      GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, hcc])
    have hm1 := GlobalTheory.LatticeStable.smul_mem_latO D S T LS LT _ e hint u hu
    have hm2 := GlobalTheory.LatticeStable.smul_mem_latO D S T LS LT _ (cA D e) hint' u hu
    have hh1 : IsHalf e (e • u) := (isHalf_iff e (e • u)).2 (by rw [smul_smul, hee])
    have hh2 : IsHalf (cA D e) (cA D e • u) := (isHalf_iff (cA D e) (cA D e • u)).2 (by rw [smul_smul, hcc])
    have hsplit : e • u + cA D e • u = u := by rw [← add_smul, hsum', hi]
    refine ⟨-symplOH S T (e • u) (cA D e • u), fun f hf => ?_⟩
    unfold IsLatVac at hf
    have k1 := hf.2 e hsp _ hm1 hh1
    have k2 := hf.2 _ hsp' _ hm2 hh2
    have key := heisO_heisO ψ S T (e • u) (cA D e • u) f
    rw [k2, k1, hsplit] at key
    conv_rhs => rw [key]
    rw [smul_smul, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_smul]
  · obtain ⟨b, hb, hbb⟩ := exists_half_idem v h2
    refine ⟨0, fun f hf => ?_⟩
    unfold IsLatVac at hf
    have hm := GlobalTheory.LatticeStable.smul_mem_latO D S T LS LT _ b hb u hu
    have h2u : 2 • (b • u) = u := by rw [two_nsmul, ← add_smul, hbb, hi]
    rw [AddChar.map_zero_eq_one, one_smul, ← h2u]
    exact hf.1 _ hm

private theorem ipO_smul_smul' {m n : ℕ} (μ : Measure (Mx D m n)) (𝓕 : Set (Mx D m n)) (a b : ℂ)
    (f g : Mx D m n → ℂ) : ipO μ 𝓕 (a • f) (b • g) = (a * starRingEnd ℂ b) * ipO μ 𝓕 f g := by
  unfold ipO
  rw [← integral_const_mul]
  congr 1
  ext t
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  ring

theorem compress_fin : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → IsCovolOne (ratL T S) μ 𝓕 → ∀ (v : FinPl D) (w : WO S T), ∃ γ : ℂ, ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun u => u = v) f → IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun u => u = v) g → ipO μ 𝓕 g (heisO ψ S T (wAt (.inl v) w) f) = γ * ipO μ 𝓕 g f := by
  intro D ψ S T ΛS ΛT μ 𝓕 hψ hS hT hμ v w
  classical
  have hn : ∀ a, ‖ψ a‖ = 1 := by
    have h := hψ
    unfold IsStdChar IsCharAF at h
    exact h.1.2.1
  obtain ⟨hI1, -, hI3, hI4, -⟩ := GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D
  obtain ⟨ι, hι⟩ : ∃ ι, ι = idem D (.inl v) := ⟨_, rfl⟩
  have hιι : ι * ι = ι := by rw [hι]; exact hI1 _
  have hcι : cA D ι = ι := by rw [hι]; exact hI3 _
  have hinf : infPart D ι = 0 := by rw [hι]; exact (hI4 v).1
  obtain ⟨x, hx⟩ : ∃ x, x = ι • w := ⟨_, rfl⟩
  rw [wAt_eq_smul, ← hι, ← hx]
  have hιx : ι • x = x := by rw [hx, smul_smul, hιι]
  have hloc : ∀ u ∈ latO S T ΛS ΛT (fun _ => True), ι • u ∈ latO S T ΛS ΛT (fun u => u = v) := by
    intro u hu
    have h := ((GlobalTheory.T.weilMatrixComponentAtPlace_mem_completedLattice D S T ΛS ΛT (fun _ => True) u hu) (.inl v)).1
    rw [wAt_eq_smul, ← hι] at h
    exact latO_mono (fun v' h' => Sum.inl.inj h'.2) h
  have hloc' : ∀ u ∈ latO S T ΛS ΛT (fun u => u = v), ι • u ∈ latO S T ΛS ΛT (fun u => u = v) := by
    intro u hu
    have h := ((GlobalTheory.T.weilMatrixComponentAtPlace_mem_completedLattice D S T ΛS ΛT (fun u => u = v) u hu) (.inl v)).1
    rw [wAt_eq_smul, ← hι] at h
    exact latO_mono (fun v' h' => h'.1) h
  have hpair : ∀ a, symplO S T (ι • a) x = symplO S T a x := by
    intro a
    rw [symplO_smul, hcι, hιx]
  by_cases hA : ∀ l ∈ latO S T ΛS ΛT (fun u => u = v), ψ (symplO S T l x) = 1
  · have hxg : x ∈ latO S T ΛS ΛT (fun _ => True) := by
      refine ((GlobalTheory.T.self_dual_lattice_pairing_dual D ψ S T ΛS ΛT hψ hS hT).1 x ?_).2 ?_
      · rw [hx]
        ext i j
        simp [Matrix.map_apply, Matrix.smul_apply, map_mul, hinf]
      · intro u' hu'
        rw [symplO_skew, AddChar.map_neg_eq_inv, ← hpair, hA _ (hloc u' hu'), inv_one]
    have hxv : x ∈ latO S T ΛS ΛT (fun u => u = v) := by
      rw [← hιx]
      exact hloc x hxg
    obtain ⟨y, hy⟩ := exists_char_act (ψ := ψ) v hxv (by rw [← hι]; exact hιx)
    refine ⟨starRingEnd ℂ (ψ y), fun f g hf hg hvf hvg => ?_⟩
    rw [hy f hvf]
    exact ((GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 hψ hμ g f hg hf).2.2.1 (ψ y)).2
  · push_neg at hA
    obtain ⟨l, hl, hl1⟩ := hA
    have hιl : ι • (ι • l) = ι • l := by rw [smul_smul, hιι]
    obtain ⟨y, hy⟩ := exists_char_act (ψ := ψ) v (hloc' l hl) (by rw [← hι]; exact hιl)
    refine ⟨0, fun f g hf hg hvf hvg => ?_⟩
    rw [zero_mul]
    have hxf : IsThetaFunO ψ S T (heisO ψ S T x f) :=
      (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1 x f hf
    have hU := ((GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 hψ hμ g (heisO ψ S T x f) hg hxf).2.2.2.2.2.2.1 (ι • l)).1
    rw [hy g hvg, heisO_comm, hy f hvf, heisO_smul, smul_smul, ipO_smul_smul', map_mul] at hU
    have hc : ψ y * starRingEnd ℂ (ψ y) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]
      norm_num
    have hs : starRingEnd ℂ (ψ (symplO S T (ι • l) x)) ≠ 1 := by
      rw [hpair]
      intro h
      exact hl1 ((starRingEnd ℂ).injective (by rw [h, map_one]))
    have h0 : (starRingEnd ℂ (ψ (symplO S T (ι • l) x)) - 1) * ipO μ 𝓕 g (heisO ψ S T x f) = 0 := by
      linear_combination hU - (starRingEnd ℂ (ψ (symplO S T (ι • l) x)) * ipO μ 𝓕 g (heisO ψ S T x f)) * hc
    exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hs)

end GlobalTheory.PlaceCompress
