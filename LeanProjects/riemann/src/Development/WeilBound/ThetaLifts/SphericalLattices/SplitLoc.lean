import Development.WeilBound.ThetaLifts.SphericalLattices.HoweInert
import Development.WeilBound.ThetaLifts.SphericalLattices.ExistsFixedSum
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.PfDict
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDict
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfSurj
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.ExistsExtZ
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.ExistsFull
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyCompSideMulEq
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLatticeIndicatorFourier

noncomputable section

namespace PositivityTheory.Sph.SplitPl

open scoped Matrix Topology
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK
  GlobalTheory.SplitFlip PositivityTheory.KCo

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ}

def trH : Matrix (Fin n) (Fin d) k ≃ₜ Matrix (Fin d) (Fin n) k where
  toFun := Matrix.transpose
  invFun := Matrix.transpose
  left_inv := Matrix.transpose_transpose
  right_inv := Matrix.transpose_transpose
  continuous_toFun := continuous_id.matrix_transpose
  continuous_invFun := continuous_id.matrix_transpose

def actL (n d : ℕ) : GlobalTheory.SplitWeil.KO k (Fin n) →* Module.End ℂ (Matrix (Fin n) (Fin d) k → ℂ) where
  toFun g :=
    { toFun := fun Φ Y => Φ (((g : GL (Fin n) k)⁻¹).val * Y)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := LinearMap.ext fun Φ => funext fun Y => by simp
  map_mul' a b := LinearMap.ext fun Φ => funext fun Y => by simp [Matrix.mul_assoc]

def actR (n d : ℕ) : GlobalTheory.SplitWeil.KO k (Fin d) →* Module.End ℂ (Matrix (Fin n) (Fin d) k → ℂ) where
  toFun h :=
    { toFun := fun Φ Y => Φ (Y * (h : GL (Fin d) k).val)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := LinearMap.ext fun Φ => funext fun Y => by simp
  map_mul' a b := LinearMap.ext fun Φ => funext fun Y => by simp [Matrix.mul_assoc]

theorem nabs_KO {m : ℕ} {g : GL (Fin m) k} (hg : g ∈ GlobalTheory.SplitWeil.KO k (Fin m)) :
    GlobalTheory.SplitWeil.nabs k (gdet g) = 1 :=
  GlobalTheory.SplitWeil.nabs_eq_one_of_valuation_eq_one (valuation_gdet_of_mem_KO hg)

theorem apow_KO {m : ℕ} {g : GL (Fin m) k} (hg : g ∈ GlobalTheory.SplitWeil.KO k (Fin m)) (z : ℂ) : apow (gdet g) z = 1 :=
  apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hg) z

theorem stabL {Φ : Matrix (Fin n) (Fin d) k → ℂ} (hΦ : Φ ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin d) k)) :
    ∃ U ∈ 𝓝 (1 : GlobalTheory.SplitWeil.KO k (Fin n)), ∀ g ∈ U, actL n d g Φ = Φ := by
  have ho := GlobalTheory.SplitWeil.isOpen_stabilizer_om (μ := 1) (by rw [MonoidHom.ker_one]; exact isOpen_univ) hΦ
  refine ⟨(fun g : GlobalTheory.SplitWeil.KO k (Fin n) => ((1 : GL (Fin d) k), (g : GL (Fin n) k))) ⁻¹'
    {gh | GlobalTheory.SplitWeil.om 1 gh.1 gh.2 Φ = Φ},
    (ho.preimage (continuous_const.prodMk continuous_subtype_val)).mem_nhds (GlobalTheory.SplitWeil.om_one 1 Φ), fun g hg => ?_⟩
  have hg' : GlobalTheory.SplitWeil.om 1 (1 : GL (Fin d) k) (g : GL (Fin n) k) Φ = Φ := hg
  have e : actL n d g Φ = GlobalTheory.SplitWeil.om 1 (1 : GL (Fin d) k) (g : GL (Fin n) k) Φ := by
    funext Y
    simp [actL, GlobalTheory.SplitWeil.om, nabs_KO g.2, GlobalTheory.SplitWeil.nabs_one]
  rw [e, hg']

theorem stabR {Φ : Matrix (Fin n) (Fin d) k → ℂ} (hΦ : Φ ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin d) k)) :
    ∃ U ∈ 𝓝 (1 : GlobalTheory.SplitWeil.KO k (Fin d)), ∀ g ∈ U, actR n d g Φ = Φ := by
  have ho := GlobalTheory.SplitWeil.isOpen_stabilizer_om (μ := 1) (by rw [MonoidHom.ker_one]; exact isOpen_univ) hΦ
  refine ⟨(fun g : GlobalTheory.SplitWeil.KO k (Fin d) => ((g : GL (Fin d) k), (1 : GL (Fin n) k))) ⁻¹'
    {gh | GlobalTheory.SplitWeil.om 1 gh.1 gh.2 Φ = Φ},
    (ho.preimage (continuous_subtype_val.prodMk continuous_const)).mem_nhds (GlobalTheory.SplitWeil.om_one 1 Φ), fun g hg => ?_⟩
  have hg' : GlobalTheory.SplitWeil.om 1 (g : GL (Fin d) k) (1 : GL (Fin n) k) Φ = Φ := hg
  have e : actR n d g Φ = GlobalTheory.SplitWeil.om 1 (g : GL (Fin d) k) (1 : GL (Fin n) k) Φ := by
    funext Y
    simp [actR, GlobalTheory.SplitWeil.om, nabs_KO g.2, GlobalTheory.SplitWeil.nabs_one]
  rw [e, hg']

theorem avgL {Φ : Matrix (Fin n) (Fin d) k → ℂ} (hΦ : Φ ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin d) k)) :
    ∃ (m : ℕ) (g : Fin (m + 1) → GL (Fin n) k), (∀ i, g i ∈ GlobalTheory.SplitWeil.KO k (Fin n)) ∧
      ∀ h : GL (Fin n) k, h ∈ GlobalTheory.SplitWeil.KO k (Fin n) → ∀ Y : Matrix (Fin n) (Fin d) k,
        ∑ i, Φ (((g i)⁻¹).val * (h.val * Y)) = ∑ i, Φ (((g i)⁻¹).val * Y) := by
  have : CompactSpace (GlobalTheory.SplitWeil.KO k (Fin n)) := isCompact_iff_compactSpace.1 isCompact_KO
  obtain ⟨m, g, hg⟩ := exists_fixed_sum (actL n d) Φ (stabL hΦ)
  refine ⟨m, fun i => g i, fun i => (g i).2, fun h hh Y => ?_⟩
  have := congrFun (hg (⟨h, hh⟩ : GlobalTheory.SplitWeil.KO k (Fin n))⁻¹) Y
  simpa [actL, Finset.sum_apply, Matrix.mul_assoc] using this

theorem avgR {Φ : Matrix (Fin n) (Fin d) k → ℂ} (hΦ : Φ ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin d) k)) :
    ∃ (m : ℕ) (g : Fin (m + 1) → GL (Fin d) k), (∀ i, g i ∈ GlobalTheory.SplitWeil.KO k (Fin d)) ∧
      ∀ h : GL (Fin d) k, h ∈ GlobalTheory.SplitWeil.KO k (Fin d) → ∀ Y : Matrix (Fin n) (Fin d) k,
        ∑ i, Φ (Y * h.val * (g i).val) = ∑ i, Φ (Y * (g i).val) := by
  have : CompactSpace (GlobalTheory.SplitWeil.KO k (Fin d)) := isCompact_iff_compactSpace.1 isCompact_KO
  obtain ⟨m, g, hg⟩ := exists_fixed_sum (actR n d) Φ (stabR hΦ)
  refine ⟨m, fun i => g i, fun i => (g i).2, fun h hh Y => ?_⟩
  have := congrFun (hg (⟨h, hh⟩ : GlobalTheory.SplitWeil.KO k (Fin d))) Y
  simpa [actR, Finset.sum_apply, Matrix.mul_assoc] using this

theorem ind_tr {a b : ℕ} (A : Matrix (Fin a) (Fin b) k) :
    Set.indicator {Z : Matrix (Fin b) (Fin a) k | ∀ i j, Z i j ∈ 𝒪[k]} (fun _ => (1 : ℂ)) Aᵀ =
      Set.indicator {Z : Matrix (Fin a) (Fin b) k | ∀ i j, Z i j ∈ 𝒪[k]} (fun _ => (1 : ℂ)) A := by
  have e : (Aᵀ ∈ {Z : Matrix (Fin b) (Fin a) k | ∀ i j, Z i j ∈ 𝒪[k]}) ↔ (A ∈ {Z : Matrix (Fin a) (Fin b) k | ∀ i j, Z i j ∈ 𝒪[k]}) :=
    ⟨fun h i j => h j i, fun h i j => h j i⟩
  by_cases hA : A ∈ {Z : Matrix (Fin a) (Fin b) k | ∀ i j, Z i j ∈ 𝒪[k]}
  · rw [Set.indicator_of_mem hA, Set.indicator_of_mem (e.2 hA)]
  · rw [Set.indicator_of_notMem hA, Set.indicator_of_notMem (mt e.1 hA)]

theorem int_mul {a b c : ℕ} {A : Matrix (Fin a) (Fin b) k} {B : Matrix (Fin b) (Fin c) k} (hA : ∀ i j, A i j ∈ 𝒪[k])
    (hB : ∀ i j, B i j ∈ 𝒪[k]) : ∀ i j, (A * B) i j ∈ 𝒪[k] := fun i j => by
  rw [Matrix.mul_apply]
  exact sum_mem fun l _ => mul_mem (hA i l) (hB l j)

theorem ind_mulKO {a b : ℕ} (Y : Matrix (Fin a) (Fin b) k) {h : GL (Fin b) k} (hh : h ∈ GlobalTheory.SplitWeil.KO k (Fin b)) :
    Set.indicator {Z : Matrix (Fin a) (Fin b) k | ∀ i j, Z i j ∈ 𝒪[k]} (fun _ => (1 : ℂ)) (Y * h.1) =
      Set.indicator {Z : Matrix (Fin a) (Fin b) k | ∀ i j, Z i j ∈ 𝒪[k]} (fun _ => (1 : ℂ)) Y := by
  obtain ⟨h1, h2⟩ := (mem_KO_iff h).1 hh
  have e : (Y * h.1 ∈ {Z : Matrix (Fin a) (Fin b) k | ∀ i j, Z i j ∈ 𝒪[k]}) ↔
      (Y ∈ {Z : Matrix (Fin a) (Fin b) k | ∀ i j, Z i j ∈ 𝒪[k]}) := by
    refine ⟨fun hY => ?_, fun hY => int_mul hY h1⟩
    have := int_mul hY h2
    rwa [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] at this
  by_cases hY : Y ∈ {Z : Matrix (Fin a) (Fin b) k | ∀ i j, Z i j ∈ 𝒪[k]}
  · rw [Set.indicator_of_mem hY, Set.indicator_of_mem (e.2 hY)]
  · rw [Set.indicator_of_notMem hY, Set.indicator_of_notMem (mt e.1 hY)]

theorem split_weil_rep_left_action (α : kˣ →* ℂˣ) (g : GL (Fin n) k) (Φ : Matrix (Fin n) (Fin d) k → ℂ) :
    omB 1 α g 1 Φ = fun Y => apow (gdet g) ((d : ℂ) / 2) * Φ (g.valᵀ * Y) := by
  funext Y
  simp [omB]

theorem split_weil_rep_right_action (α : kˣ →* ℂˣ) (h : GL (Fin d) k) (Φ : Matrix (Fin n) (Fin d) k → ℂ) :
    omB 1 α 1 h Φ = fun Y => (α (gdet h) : ℂ) * apow (gdet h) ((n : ℂ) / 2) * Φ (Y * h.val) := by
  funext Y
  simp [omB]

theorem latT (hL : LatSt) {Ψ : Matrix (Fin n) (Fin d) k → ℂ} (hΨ : Ψ ∈ SB (Matrix (Fin n) (Fin d) k))
    (hi : ∀ h : GL (Fin d) k, h ∈ GlobalTheory.SplitWeil.KO k (Fin d) → ∀ Y : Matrix (Fin n) (Fin d) k, Ψ (Y * h.1) = Ψ Y) :
    Ψ ∈ Submodule.span ℂ {f | ∃ g : GL (Fin n) k,
      f = fun Y => Set.indicator {Z : Matrix (Fin n) (Fin d) k | ∀ i j, Z i j ∈ 𝒪[k]} (fun _ => (1 : ℂ)) (g.1 * Y)} := by
  have hT : (fun Z : Matrix (Fin d) (Fin n) k => Ψ Zᵀ) ∈ SB (Matrix (Fin d) (Fin n) k) :=
    ⟨hΨ.1.comp_continuous continuous_id.matrix_transpose, hΨ.2.comp_homeomorph (trH (n := d) (d := n))⟩
  have hs := hL k d n _ hT fun g hg Z => by
    simp only [Matrix.transpose_mul]
    have h1 : (invT g)⁻¹ ∈ GlobalTheory.SplitWeil.KO k (Fin d) := inv_mem (invT_mem_KO hg)
    have := hi _ h1 Zᵀ
    rwa [invT_inv_val] at this
  have key : ∀ G ∈ Submodule.span ℂ {f | ∃ h : GL (Fin n) k, f = fun Z : Matrix (Fin d) (Fin n) k =>
      Set.indicator {Z' : Matrix (Fin d) (Fin n) k | ∀ i j, Z' i j ∈ 𝒪[k]} (fun _ => (1 : ℂ)) (Z * h.1)},
      (fun Y : Matrix (Fin n) (Fin d) k => G Yᵀ) ∈ Submodule.span ℂ {f | ∃ g : GL (Fin n) k,
        f = fun Y => Set.indicator {Z : Matrix (Fin n) (Fin d) k | ∀ i j, Z i j ∈ 𝒪[k]} (fun _ => (1 : ℂ)) (g.1 * Y)} := by
    intro G hG
    induction hG using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      refine Submodule.subset_span ⟨(invT h)⁻¹, funext fun Y => ?_⟩
      show Set.indicator _ _ (Yᵀ * h.1) = Set.indicator _ _ (((invT h)⁻¹).1 * Y)
      rw [show Yᵀ * h.1 = (((invT h)⁻¹).1 * Y)ᵀ by rw [invT_inv_val, Matrix.transpose_mul, Matrix.transpose_transpose], ind_tr]
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul a x _ hx => exact Submodule.smul_mem _ a hx
  simpa only [Matrix.transpose_transpose] using key _ hs

end Loc

end PositivityTheory.Sph.SplitPl

end
