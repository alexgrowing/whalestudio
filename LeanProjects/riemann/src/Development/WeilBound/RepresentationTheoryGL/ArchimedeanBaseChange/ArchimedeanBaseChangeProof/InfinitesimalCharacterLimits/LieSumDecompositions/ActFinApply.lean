import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksSl
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CapelliDetDiagonalBlockActsByInfinitesimalCharac
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapelliLeviFactorizationSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermAuxiliaryStatementB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraFiniteFormsGLSingleCharSpanMem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericFiniteByInduction
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PProjA

noncomputable section

open NumberField IsDedekindDomain MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Affgl PositivityTheory.Rg.Rs GlobalTheory.BlockCap
open PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockDerivatives

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockSlices

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem act_fin_apply {a : ℕ} (h : GL (Fin a) (Af E)) (F : Sm E a) (x : GA E a) :
    (act (.fin h) F).1 x = F.1 (x * finGL E a h) := rfl

theorem act_cpt_apply {a : ℕ} (k : Kinf E a) (F : Sm E a) (x : GA E a) :
    (act (.cpt k) F).1 x = F.1 (x * infGL E a (Unitary.toUnits k)) := rfl

variable {r s : ℕ}

theorem yp_one : yp (E := E) (a := r + s) 1 1 = 1 := by
  simp [yp]

theorem base_one {U : Submodule ℂ (Sm E (r + s))} (hU : IsAutSt U) {c : ℂ} {T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)}
    (hT : IsSliceMap U c T) {ψ : Sm E (r + s)} (hψ : ψ ∈ U) (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) :
    ∃ ψ' ∈ U, ∀ x, (T ψ').1 x = (T ψ).1 (x * yp k g) := by
  refine ⟨act (.cpt k) (act (.fin g) ψ), hU.1 _ _ (hU.1 _ _ hψ), fun x => ?_⟩
  rw [hT.equiv _ _ (hU.1 _ _ hψ), hT.equiv _ _ hψ]
  exact InducedTensorMap.A.act_cf k g (T ψ) x

theorem mem_LS_of {U : Submodule ℂ (Sm E (r + s))} {T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)} {ψ : Sm E (r + s)}
    (hψ : ψ ∈ U) (ℓ : Sm E r) (m₂ : GA E s) (h : ∀ m₁, ℓ.1 m₁ = (T ψ).1 (lev (Ad E) r s (m₁, m₂))) : ℓ ∈ LS U T :=
  Submodule.subset_span ⟨ψ, hψ, 1, 1, m₂, fun m₁ => by rw [h, yp_one, mul_one]⟩

theorem mem_RS_of {U : Submodule ℂ (Sm E (r + s))} {T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)} {ψ : Sm E (r + s)}
    (hψ : ψ ∈ U) (ℓ : Sm E s) (m₁ : GA E r) (h : ∀ m₂, ℓ.1 m₂ = (T ψ).1 (lev (Ad E) r s (m₁, m₂))) : ℓ ∈ RS U T :=
  Submodule.subset_span ⟨ψ, hψ, 1, 1, m₁, fun m₂ => by rw [h, yp_one, mul_one]⟩

omit [IsCMField E] in
theorem upd0 (m₁ y : GA E r) (m₂ : GA E s) :
    Function.update (CapFactor.levPair (n := ![r, s]) (m₁, m₂)) 0 y = CapFactor.levPair (n := ![r, s]) (y, m₂) := by
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

omit [IsCMField E] in
theorem upd1 (m₁ : GA E r) (m₂ y : GA E s) :
    Function.update (CapFactor.levPair (n := ![r, s]) (m₁, m₂)) 1 y = CapFactor.levPair (n := ![r, s]) (m₁, y) := by
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

section Step

variable {U : Submodule ℂ (Sm E (r + s))} (hU : IsAutSt U) {c : ℂ} {T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)}
  (hT : IsSliceMap U c T)
include hU hT

theorem act_left {ψ : Sm E (r + s)} (hψ : ψ ∈ U) (ℓ : Sm E r) (m₂ : GA E s)
    (h : ∀ m₁, ℓ.1 m₁ = (T ψ).1 (lev (Ad E) r s (m₁, m₂))) (o : Op E r) : act o ℓ ∈ LS U T := by
  cases o with
  | fin h' =>
    refine mem_LS_of (hU.1 (.fin (lev (Af E) r s (h', 1))) ψ hψ) _ m₂ fun m₁ => ?_
    have e : lev (Ad E) r s (finGL E r h', 1) = finGL E (r + s) (lev (Af E) r s (h', 1)) := by
      rw [← Slice1.lev_finGL, map_one]
    rw [act_fin_apply, h, hT.equiv _ _ hψ, act_fin_apply, Slice1.lev_mul_one, e]
  | cpt κ =>
    refine mem_LS_of (hU.1 (.cpt (Slice1.levK E r s κ)) ψ hψ) _ m₂ fun m₁ => ?_
    rw [act_cpt_apply, h, hT.equiv _ _ hψ, act_cpt_apply, Slice1.lev_mul_one, Slice1.infGL_levK]
  | lie X =>
    let n : Fin 2 → ℕ := ![r, s]
    have h2 : ∑ i, n i = n 0 + n 1 := CapFactor.two_sum n
    refine mem_LS_of (hU.1 (.lie (blockCLM (stdBlocks n h2) 0 X)) ψ hψ) _ m₂ fun m₁ => ?_
    have key := LinearMap.congr_fun
      (restrLin_lie (E := E) (stdBlocks n h2) (CapFactor.levPair (n := n) ((1 : GA E r), m₂)) 0 X) (T ψ)
    have hℓ : ℓ = restrLin (stdBlocks n h2) (CapFactor.levPair (n := n) ((1 : GA E r), m₂)) 0 (T ψ) :=
      Subtype.ext (funext fun y => by
        rw [h y]
        change _ = (T ψ).1 (leviEmb (Ad E) (stdBlocks n h2)
          (Function.update (CapFactor.levPair (n := n) ((1 : GA E r), m₂)) 0 y))
        rw [upd0, ← CapFactor.lev_eq_leviEmb]
        rfl)
    have key2 : (restrLin (stdBlocks n h2) (CapFactor.levPair (n := n) ((1 : GA E r), m₂)) 0
        (lie E (r + s) (blockCLM (stdBlocks n h2) 0 X) (T ψ))).1 m₁ = (lie E r X ℓ).1 m₁ := by
      rw [hℓ]
      exact congrArg (fun φ : Sm E (n 0) => φ.1 m₁) key
    rw [hT.equiv _ _ hψ]
    change (lie E r X ℓ).1 m₁ = (lie E (r + s) (blockCLM (stdBlocks n h2) 0 X) (T ψ)).1 (lev (Ad E) r s (m₁, m₂))
    rw [← key2]
    change (lie E (r + s) (blockCLM (stdBlocks n h2) 0 X) (T ψ)).1 (leviEmb (Ad E) (stdBlocks n h2)
      (Function.update (CapFactor.levPair (n := n) ((1 : GA E r), m₂)) 0 m₁)) = _
    rw [upd0, ← CapFactor.lev_eq_leviEmb]
    rfl

theorem act_right {ψ : Sm E (r + s)} (hψ : ψ ∈ U) (ℓ : Sm E s) (m₁ : GA E r)
    (h : ∀ m₂, ℓ.1 m₂ = (T ψ).1 (lev (Ad E) r s (m₁, m₂))) (o : Op E s) : act o ℓ ∈ RS U T := by
  cases o with
  | fin h' =>
    refine mem_RS_of (hU.1 (.fin (lev (Af E) r s (1, h'))) ψ hψ) _ m₁ fun m₂ => ?_
    rw [act_fin_apply, h, hT.equiv _ _ hψ, act_fin_apply, Slice2.lev_mul_right, Slice2.lev_finGL_one]
  | cpt κ =>
    refine mem_RS_of (hU.1 (.cpt (Slice2.levK E r s κ)) ψ hψ) _ m₁ fun m₂ => ?_
    rw [act_cpt_apply, h, hT.equiv _ _ hψ, act_cpt_apply, Slice2.lev_mul_right, Slice2.lev_infGL_one,
      Slice2.toUnits_levK]
  | lie X =>
    let n : Fin 2 → ℕ := ![r, s]
    have h2 : ∑ i, n i = n 0 + n 1 := CapFactor.two_sum n
    refine mem_RS_of (hU.1 (.lie (blockCLM (stdBlocks n h2) 1 X)) ψ hψ) _ m₁ fun m₂ => ?_
    have key := LinearMap.congr_fun
      (restrLin_lie (E := E) (stdBlocks n h2) (CapFactor.levPair (n := n) (m₁, (1 : GA E s))) 1 X) (T ψ)
    have hℓ : ℓ = restrLin (stdBlocks n h2) (CapFactor.levPair (n := n) (m₁, (1 : GA E s))) 1 (T ψ) :=
      Subtype.ext (funext fun y => by
        rw [h y]
        change _ = (T ψ).1 (leviEmb (Ad E) (stdBlocks n h2)
          (Function.update (CapFactor.levPair (n := n) (m₁, (1 : GA E s))) 1 y))
        rw [upd1, ← CapFactor.lev_eq_leviEmb]
        rfl)
    have key2 : (restrLin (stdBlocks n h2) (CapFactor.levPair (n := n) (m₁, (1 : GA E s))) 1
        (lie E (r + s) (blockCLM (stdBlocks n h2) 1 X) (T ψ))).1 m₂ = (lie E s X ℓ).1 m₂ := by
      rw [hℓ]
      exact congrArg (fun φ : Sm E (n 1) => φ.1 m₂) key
    rw [hT.equiv _ _ hψ]
    change (lie E s X ℓ).1 m₂ = (lie E (r + s) (blockCLM (stdBlocks n h2) 1 X) (T ψ)).1 (lev (Ad E) r s (m₁, m₂))
    rw [← key2]
    change (lie E (r + s) (blockCLM (stdBlocks n h2) 1 X) (T ψ)).1 (leviEmb (Ad E) (stdBlocks n h2)
      (Function.update (CapFactor.levPair (n := n) (m₁, (1 : GA E s))) 1 m₂)) = _
    rw [upd1, ← CapFactor.lev_eq_leviEmb]
    rfl

theorem LS_stable : IsStable (LS U T) := by
  intro o φ hφ
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨ψ, hψ, k, g, m₂, hx⟩ := hx
    obtain ⟨ψ', hψ', e⟩ := base_one hU hT hψ k g
    exact act_left hU hT hψ' x m₂ (fun m₁ => by rw [hx, ← e]) o
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

theorem RS_stable : IsStable (RS U T) := by
  intro o φ hφ
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨ψ, hψ, k, g, m₁, hx⟩ := hx
    obtain ⟨ψ', hψ', e⟩ := base_one hU hT hψ k g
    exact act_right hU hT hψ' x m₁ (fun m₂ => by rw [hx, ← e]) o
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

omit hU in

theorem LS_aut : ∀ φ ∈ LS U T, IsAutForm φ := by
  intro φ hφ
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨ψ, hψ, k, g, m₂, hx⟩ := hx
    obtain ⟨ψ₁, hA, h1, -⟩ := hT.left ψ hψ k g m₂
    have : x = ψ₁ := Subtype.ext (funext fun m₁ => (hx m₁).trans (h1 m₁).symm)
    exact this ▸ hA
  | zero => exact GlobalTheory.HCF.FormsSub.isAutForm_zero
  | add x y _ _ hx hy => exact GlobalTheory.CompanionTheory.AffglAssembly.isAutForm_add hx hy
  | smul a x _ hx => exact GlobalTheory.CompanionTheory.AffglAssembly.isAutForm_smul a hx

omit hU in

theorem RS_aut : ∀ φ ∈ RS U T, IsAutForm φ := by
  intro φ hφ
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨ψ, hψ, k, g, m₁, hx⟩ := hx
    obtain ⟨ψ₂, hA, h1, -⟩ := hT.right ψ hψ k g m₁
    have : x = ψ₂ := Subtype.ext (funext fun m₂ => (hx m₂).trans (h1 m₂).symm)
    exact this ▸ hA
  | zero => exact GlobalTheory.HCF.FormsSub.isAutForm_zero
  | add x y _ _ hx hy => exact GlobalTheory.CompanionTheory.AffglAssembly.isAutForm_add hx hy
  | smul a x _ hx => exact GlobalTheory.CompanionTheory.AffglAssembly.isAutForm_smul a hx

theorem memInd2 : ∀ ψ ∈ U, MemInd2 (LS U T) (RS U T) (T ψ) := by
  intro ψ hψ
  refine ⟨hT.unipInv ψ hψ, fun k g => ?_⟩
  obtain ⟨n, b, q, hb, hq, he⟩ := expand hU hT ψ hψ k g
  have e : (fun m => (T ψ).1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g))) =
      fun m => ∑ i, (b i).1 m.1 * (q i).1 m.2 := funext he
  rw [e]
  exact ParabolicProjection.sum_mem_tens2 (fun i => Submodule.span_le.2 (lsF_sub_LS hψ k g) (hb i))
    (fun i => rsF_sub_RS hψ k g (hq i))

end Step

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockSlices

end
