import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NodeFunctionLeviDecompositionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatNodeFunctionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStable
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.LimV.NodeCarry

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N r s : ℕ}

theorem mul_mem_Sm {e φ : GA E N → ℂ} (he : e ∈ Sm E N) (hφ : φ ∈ Sm E N) :
    (fun x => e x * φ x) ∈ Sm E N := by
  intro g
  refine ((he g).mul (hφ g)).congr fun x hx => ?_
  have hx' : IsUnit (Matrix.of x) := hx
  simp [chart, hx']

theorem memInd2_of_mem {U₁ : Submodule ℂ (Sm E r)} {U₂ : Submodule ℂ (Sm E s)} {φ : Sm E (r + s)}
    (h : φ ∈ indSpan U₁ U₂) : MemInd2 U₁ U₂ φ := by
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨fun _ _ => rfl, fun _ _ => zero_mem _⟩
  | add x y _ _ hx hy =>
    refine ⟨fun u g => ?_, fun k g => add_mem (hx.2 k g) (hy.2 k g)⟩
    change x.1 _ + y.1 _ = x.1 g + y.1 g
    rw [hx.1, hy.1]
  | smul c x _ hx =>
    refine ⟨fun u g => ?_, fun k g => Submodule.smul_mem _ c (hx.2 k g)⟩
    change c • x.1 _ = c • x.1 g
    rw [hx.1]

theorem carries_translate {e : GA E N → ℂ} {U U' : Submodule ℂ (Sm E N)} (hU : FinStable U) (hU' : FinStable U')
    (hc : Carries e U U') (P : GL (Fin N) (Af E)) {a : Sm E N} (ha : a ∈ U) :
    ∃ a' ∈ U', ∀ m, a'.1 m = e (m * finGL E N P) * a.1 m := by
  obtain ⟨b, hb, hbe⟩ := hc _ (hU P⁻¹ a ha)
  refine ⟨act (.fin P) b, hU' P b hb, fun m => ?_⟩
  have e1 : (act (.fin P) b).1 m = b.1 (m * finGL E N P) := rfl
  have e2 : (act (.fin P⁻¹) a).1 (m * finGL E N P) = a.1 (m * finGL E N P * finGL E N P⁻¹) := rfl
  rw [e1, hbe, e2, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]

theorem finGL_unip (x : BlockIx (r + s) r → Af E) : finGL E (r + s) (unip x) = unip fun p => sFin E (x p) := by
  refine ga_ext ?_ ?_
  · rw [pInf_finGL, IwaAd.map_unip]
    have : (fun p => pInf E (sFin E (x p))) = 0 := funext fun p => map_zero (infEq E).symm
    rw [this]
    exact unip_zero.symm
  · rw [pFin_finGL, IwaAd.map_unip]
    rfl

theorem finGL_lev (p : GL (Fin r) (Af E) × GL (Fin s) (Af E)) :
    finGL E (r + s) (lev (Af E) r s p) = lev (Ad E) r s (finGL E r p.1, finGL E s p.2) := by
  refine ga_ext ?_ ?_
  · rw [pInf_finGL, IwaAd.map_lev, pInf_finGL, pInf_finGL]
    exact (map_one (lev (Cinf E) r s)).symm
  · rw [pFin_finGL, IwaAd.map_lev, pFin_finGL, pFin_finGL]

theorem nodeFn_slice {e₁ : GA E r → ℂ} {e₂ : GA E s → ℂ} (h₁ : FlatFn e₁) (h₂ : FlatFn e₂) (k : Kinf E (r + s))
    (g : GL (Fin (r + s)) (Af E)) : ∃ p : GL (Fin r) (Af E) × GL (Fin s) (Af E), ∀ m : GA E r × GA E s,
      nodeFn e₁ e₂ (lev (Ad E) r s m * cf (r + s) k g) = e₁ (m.1 * finGL E r p.1) * e₂ (m.2 * finGL E s p.2) := by
  obtain ⟨xf, p, c, hc, hg⟩ := IwaFin.exists_unip_lev_integral E r s g
  refine ⟨p, fun m => ?_⟩
  obtain ⟨v, hv⟩ := lev_mul_unip m fun q => sFin E (xf q)
  have e1 : cf (r + s) k g = unip (fun q => sFin E (xf q)) * lev (Ad E) r s (finGL E r p.1, finGL E s p.2) *
      cf (r + s) k c := by
    rw [hg, cf, cf, map_mul _ (unip xf * _) c, ← mul_assoc, infGL_comm, mul_assoc (finGL _ _ _), map_mul, finGL_unip,
      finGL_lev]
  rw [e1, ← mul_assoc, ← mul_assoc, hv, mul_assoc (unip v), ← map_mul]
  exact GlobalTheory.T.node_function_levi_decomposition e₁ e₂ h₁ h₂ v _ k c hc

theorem carries_nodeFn : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ} (e₁ : GA E r → ℂ) (e₂ : GA E s → ℂ) (U₁ U₁' : Submodule ℂ (Sm E r)) (U₂ U₂' : Submodule ℂ (Sm E s)), FlatFn e₁ → FlatFn e₂ → FinStable U₁ → FinStable U₁' → FinStable U₂ → FinStable U₂' → Carries e₁ U₁ U₁' → Carries e₂ U₂ U₂' → Carries (nodeFn e₁ e₂) (indSpan U₁ U₂) (indSpan U₁' U₂') := by
  intro E _ _ _ r s e₁ e₂ U₁ U₁' U₂ U₂' h₁ h₂ s₁ s₁' s₂ s₂' c₁ c₂ φ hφ
  have hF := GlobalTheory.T.flat_node_function e₁ e₂ h₁ h₂
  have hI := memInd2_of_mem hφ
  refine ⟨⟨fun x => nodeFn e₁ e₂ x * φ.1 x, mul_mem_Sm hF.sm φ.2⟩,
    Submodule.subset_span ⟨fun u g => ?_, fun k g => ?_⟩, fun _ => rfl⟩
  · change nodeFn e₁ e₂ (unip u * g) * φ.1 (unip u * g) = nodeFn e₁ e₂ g * φ.1 g
    rw [hI.1]
    obtain ⟨v, m, k, c, hc, rfl⟩ := exists_iw g
    rw [← mul_assoc, ← mul_assoc, ← D.unip_add', GlobalTheory.T.node_function_levi_decomposition e₁ e₂ h₁ h₂ _ _ _ _ hc,
      GlobalTheory.T.node_function_levi_decomposition e₁ e₂ h₁ h₂ _ _ _ _ hc]
  · obtain ⟨p, hp⟩ := nodeFn_slice h₁ h₂ k g
    obtain ⟨n, ψ₁, ψ₂, u₁, u₂, hs⟩ := tensor_pair_finite_sum (hI.2 k g)
    choose a ha hae using fun i => carries_translate s₁ s₁' c₁ p.1 (u₁ i)
    choose b hb hbe using fun i => carries_translate s₂ s₂' c₂ p.2 (u₂ i)
    convert A.sum_mem ha hb using 1
    funext m
    have hm : φ.1 (lev (Ad E) r s m * cf (r + s) k g) = ∑ i, (ψ₁ i).1 m.1 * (ψ₂ i).1 m.2 := congrFun hs m
    change nodeFn e₁ e₂ (lev (Ad E) r s m * cf (r + s) k g) * φ.1 (lev (Ad E) r s m * cf (r + s) k g) = _
    rw [hm, hp, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hae, hbe]
    ring

end GlobalTheory.CompanionTheory.LimV.NodeCarry
