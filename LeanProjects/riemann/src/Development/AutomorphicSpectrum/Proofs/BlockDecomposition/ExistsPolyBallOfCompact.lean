import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocallyConstantCompactSupportUnipotent
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicDoubleCosetDecomposition
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicCellStructureData
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeTwistedIso
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProjectionToTwistedEigenfunctionSupport
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMemTwKerPolyBall
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRepsSumEqZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousMatMir
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsIntertwinerOfEquiv

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.LocC

section Abstract

variable {G Z : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup Z] [Module ℂ Z]

theorem exists_avg (H : Subgroup G) (σ : Representation ℂ H Z) (L : Subgroup G) (hL : IsCompact (L : Set G))
    (θ : L →* ℂˣ) (hθ : IsOpen (θ.ker : Set L)) (f : cIndSpace H σ) :
    ∃ g : cIndSpace H σ, f - g ∈ twKer (cInd H σ) L θ ∧
      (∀ l : L, cInd H σ (l : G) g = (θ l : ℂ) • g) ∧
      ∀ x, (g : smoothPart (ind H σ)).1.1 x ≠ 0 → ∃ l ∈ L, (f : smoothPart (ind H σ)).1.1 (x * l) ≠ 0 := by
  obtain ⟨ι, _, r, c, h1, h2⟩ := GlobalTheory.CompanionTheory.TwAvgInd.exists_finite_average (cInd H σ)
    (GlobalTheory.CompanionTheory.BZFun.isSmooth_cInd H σ) hL θ hθ f
  refine ⟨_, h1, h2, fun x hx => ?_⟩
  by_contra hcon
  push_neg at hcon
  apply hx
  let E : cIndSpace H σ →ₗ[ℂ] Z := (GlobalTheory.CompanionTheory.TwAvgInd.evalAt H σ x) ∘ₗ (cIndSpace H σ).subtype
  have hz : ∀ i, E (GlobalTheory.CompanionTheory.TwistedAverage.twOrbit (cInd H σ) L θ f (r i)) = 0 := by
    intro i
    have : E (cInd H σ ((r i : L) : G) f) = 0 := hcon _ (r i).2
    simp only [GlobalTheory.CompanionTheory.TwistedAverage.twOrbit, map_smul, this, smul_zero]
  have : E (c • ∑ i, GlobalTheory.CompanionTheory.TwistedAverage.twOrbit (cInd H σ) L θ f (r i)) = 0 := by
    rw [map_smul, map_sum, Finset.sum_eq_zero fun i _ => hz i, smul_zero]
  exact this

theorem avgVanish_conj (H : Subgroup G) (σ : Representation ℂ H Z) (U : Subgroup G) (θ : U →* ℂˣ) (y : G)
    (hU : ∀ u ∈ U, y * u * y⁻¹ ∈ U) (hU' : ∀ u ∈ U, y⁻¹ * u * y ∈ U)
    (hθ : ∀ (u : U) (h : y⁻¹ * (u : G) * y ∈ U), θ ⟨_, h⟩ = θ u)
    (f : cIndSpace H σ) (hf : AvgVanish H σ U θ (cInd H σ y f) 1) : AvgVanish H σ U θ f y := by
  obtain ⟨L', hL', hc, g', h1, h2, h3⟩ := hf
  let c : G →* G := (MulAut.conj y⁻¹).toMonoidHom
  have hcv : ∀ x, c x = y⁻¹ * x * y := fun x => by simp [c, MulAut.conj_apply]
  have hcc : Continuous c := by
    have : (c : G → G) = fun x => y⁻¹ * x * y := funext hcv
    rw [this]; fun_prop
  let L : Subgroup G := L'.map c
  have hL : L ≤ U := by
    rintro _ ⟨l, hl, rfl⟩
    rw [hcv]; exact hU' _ (hL' hl)
  have key : ∀ (n : L') , ∃ m : L, (m : G) = y⁻¹ * n * y ∧
      (θ.comp (Subgroup.inclusion hL)) m = (θ.comp (Subgroup.inclusion hL')) n := by
    intro n
    refine ⟨⟨y⁻¹ * n * y, ⟨n, n.2, hcv _⟩⟩, rfl, ?_⟩
    exact hθ ⟨n, hL' n.2⟩ (hU' _ (hL' n.2))
  have hconj : ∀ (n : G) (w : cIndSpace H σ), cInd H σ y⁻¹ (cInd H σ n w) =
      cInd H σ (y⁻¹ * n * y) (cInd H σ y⁻¹ w) := by
    intro n w
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
    congr 2
    group
  refine ⟨L, hL, hc.image hcc, cInd H σ y⁻¹ g', ?_, ?_, ?_⟩
  · have e : f - cInd H σ y⁻¹ g' = cInd H σ y⁻¹ (cInd H σ y f - g') := by
      rw [map_sub, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [e]
    have hle : twKer (cInd H σ) L' (θ.comp (Subgroup.inclusion hL')) ≤
        (twKer (cInd H σ) L (θ.comp (Subgroup.inclusion hL))).comap (cInd H σ y⁻¹) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨n, v, rfl⟩
      obtain ⟨m, hm, hm'⟩ := key n
      refine Submodule.subset_span ⟨m, cInd H σ y⁻¹ v, ?_⟩
      rw [map_sub, map_smul, hconj, hm, hm']
    exact hle h1
  · rintro ⟨_, n, hn, rfl⟩
    have e := hconj n g'
    rw [h2 ⟨n, hn⟩, map_smul] at e
    have e3 : θ (Subgroup.inclusion hL ⟨c n, n, hn, rfl⟩) = θ (Subgroup.inclusion hL' ⟨n, hn⟩) := by
      have h4 := hθ ⟨n, hL' hn⟩ (hU' _ (hL' hn))
      rw [← show (⟨y⁻¹ * n * y, hU' _ (hL' hn)⟩ : U) = Subgroup.inclusion hL ⟨c n, n, hn, rfl⟩ from
        Subtype.ext (hcv n).symm]
      exact h4
    have e5 : cInd H σ (c n) (cInd H σ y⁻¹ g') = _ :=
      (congrArg (fun x => cInd H σ x (cInd H σ y⁻¹ g')) (hcv n)).trans e.symm
    refine e5.trans ?_
    show ((θ (Subgroup.inclusion hL' ⟨n, hn⟩) : ℂˣ) : ℂ) • _ = ((θ (Subgroup.inclusion hL ⟨c n, n, hn, rfl⟩) : ℂˣ) : ℂ) • _
    rw [e3]
  · intro u hu
    have := h3 _ (hU u hu)
    rw [one_mul] at this
    exact this

theorem avgVanish_left (H : Subgroup G) (σ : Representation ℂ H Z) (U : Subgroup G) (θ : U →* ℂˣ)
    (f : cIndSpace H σ) (y e h : G) (hh : h ∈ H) (he : y⁻¹ * e * y ∈ U)
    (hf : AvgVanish H σ U θ f y) : AvgVanish H σ U θ f (h * e * y) := by
  obtain ⟨L, hL, hc, g, h1, h2, h3⟩ := hf
  refine ⟨L, hL, hc, g, h1, h2, fun u hu => ?_⟩
  have e1 : h * e * y * u = h * (y * ((y⁻¹ * e * y) * u)) := by group
  have hh2 := (g : smoothPart (ind H σ)).1.2 ⟨h, hh⟩ (y * ((y⁻¹ * e * y) * u))
  rw [e1]
  have h4 := h3 _ (U.mul_mem he hu)
  refine hh2.trans ?_
  rw [h4, map_zero]

end Abstract

section Grp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable (k) in

def uEl (i t : ℕ) (c : Fin (i + 1) → k) (d : Fin (t + 1) → k) : Mir k ((i + 1) + t + 1) :=
  ⟨unip k ((i + 1) + (t + 1)) (Multiplicative.ofAdd (Fin.append c d)), MirU_le_Mir k _ ⟨_, rfl⟩⟩

theorem dEmb_eq (i t : ℕ) (d : Fin (t + 1) → k) : dEmb k i t d = uEl k i t 0 d := rfl

theorem uEl_mul (i t : ℕ) (c c' : Fin (i + 1) → k) (d d' : Fin (t + 1) → k) :
    uEl k i t c d * uEl k i t c' d' = uEl k i t (c + c') (d + d') := by
  apply Subtype.ext
  have : Fin.append (c + c') (d + d') = Fin.append c d + Fin.append c' d' := by
    funext x; refine Fin.addCases ?_ ?_ x <;> simp
  simp only [uEl, Subgroup.coe_mul, this, ofAdd_add, map_mul]

theorem uEl_mem (i t : ℕ) (c : Fin (i + 1) → k) (d : Fin (t + 1) → k) :
    uEl k i t c d ∈ MirUin k ((i + 1) + t + 1) := ⟨_, rfl⟩

theorem exists_uEl (i t : ℕ) (u : Mir k ((i + 1) + t + 1)) (hu : u ∈ MirUin k ((i + 1) + t + 1)) :
    ∃ c d, u = uEl k i t c d := by
  obtain ⟨w, hw⟩ := (Subgroup.mem_subgroupOf.1 hu : ((u : Mir k ((i + 1) + t + 1)) : GL _ k) ∈ MirU k ((i + 1) + t + 1))
  refine ⟨fun a => w.toAdd (Fin.castAdd (t + 1) a), fun a => w.toAdd (Fin.natAdd (i + 1) a), ?_⟩
  apply Subtype.ext
  refine hw.symm.trans ?_
  show unip k ((i + 1) + t + 1) w = unip k ((i + 1) + (t + 1)) _
  congr 1
  let w' : Fin ((i + 1) + (t + 1)) → k := w.toAdd
  have e : Fin.append (fun a => w' (Fin.castAdd (t + 1) a)) (fun a => w' (Fin.natAdd (i + 1) a)) = w' :=
    Fin.append_castAdd_natAdd
  exact congrArg Multiplicative.ofAdd e.symm

theorem mirChar_uEl (ψ : AddChar k Circle) (i t : ℕ) (c : Fin (i + 1) → k) (d : Fin (t + 1) → k)
    (h : uEl k i t c d ∈ MirUin k ((i + 1) + t + 1)) :
    mirChar k ψ ((i + 1) + t) ⟨uEl k i t c d, h⟩ = Circle.toUnits (ψ (d (Fin.last t))) := by
  rw [mirChar_eq k ψ ((i + 1) + t) _ (Multiplicative.ofAdd (Fin.append c d : Fin ((i + 1) + (t + 1)) → k)) rfl]
  have : (Fin.last ((i + 1) + t) : Fin ((i + 1) + t + 1)) = Fin.natAdd (i + 1) (Fin.last t) := rfl
  rw [toAdd_ofAdd, this, Fin.append_right]

theorem ePG_inj {i t : ℕ} {a b : Σ x, Two (Fin (i + 1)) (Fin t) x} : ePG i t a = ePG i t b ↔ a = b :=
  (ePG i t).injective.eq_iff

theorem ePG_true_eq (i t : ℕ) (b : Fin (t + 1)) :
    ePG (i + 1) (t + 1) ⟨true, b⟩ = Fin.castSucc (Fin.natAdd (i + 1) b) := by
  apply Fin.ext
  rw [GlobalTheory.CompanionTheory.BZPhiPG.Fib.ePG_true_val]
  simp

theorem ePG_false_eq (i t : ℕ) (a : Fin (i + 1)) :
    ePG (i + 1) (t + 1) ⟨false, Fin.castSucc a⟩ = Fin.castSucc (Fin.castAdd (t + 1) a) := by
  apply Fin.ext
  rw [GlobalTheory.CompanionTheory.BZPhiPG.Cells.ePG_false_val]
  simp

theorem uEl_val (i t : ℕ) (c : Fin (i + 1) → k) (d : Fin (t + 1) → k) :
    ((uEl k i t c d : Mir k _) : GL (Fin ((i + 1) + (t + 1) + 1)) k).val =
      1 + colMat k ((i + 1) + (t + 1)) (Fin.append c d) := rfl

theorem uEl_mem_HPG (i t : ℕ) (c : Fin (i + 1) → k) : uEl k i t c 0 ∈ HPG k (i + 1) (t + 1) := by
  show ((uEl k i t c 0 : Mir k _) : GL (Fin ((i + 1) + (t + 1) + 1)) k) ∈ parab k (ePG (i + 1) (t + 1))
  refine mem_parab_iff.2 ?_
  intro a b x y hab
  cases a <;> cases b <;> first | exact absurd hab (by decide) | skip
  rw [uEl_val, Matrix.add_apply, Matrix.one_apply_ne (fun e => by simpa using ePG_inj.1 e), zero_add, ePG_true_eq]
  by_cases hy : y = Fin.last (i + 1)
  · subst hy
    rw [ePG_false_last]
    simp only [colMat, if_true, Fin.lastCases_castSucc, Fin.append_right, Pi.zero_apply]
  · obtain ⟨y', rfl⟩ := Fin.exists_castSucc_eq.2 hy
    rw [ePG_false_eq]
    simp [colMat, Fin.castSucc_ne_last]

theorem colMat_ePG_false (i t : ℕ) (c : Fin (i + 1) → k) (a b : Fin (i + 1 + 1)) :
    colMat k ((i + 1) + (t + 1)) (Fin.append c 0) (ePG (i + 1) (t + 1) ⟨false, a⟩) (ePG (i + 1) (t + 1) ⟨false, b⟩) =
      colMat k (i + 1) c a b := by
  induction b using Fin.lastCases with
  | last =>
    rw [ePG_false_last]
    induction a using Fin.lastCases with
    | last => rw [ePG_false_last]; simp [colMat]
    | cast a => rw [ePG_false_eq]; simp [colMat]
  | cast b =>
    rw [ePG_false_eq]
    simp [colMat, Fin.castSucc_ne_last]

theorem pgProj_uEl (i t : ℕ) (c : Fin (i + 1) → k) :
    pgProj k (i + 1) (t + 1) ⟨uEl k i t c 0, uEl_mem_HPG i t c⟩ =
      (GlobalTheory.CompanionTheory.BZPhiPhi.unipM k i (Multiplicative.ofAdd c), 1) := by
  apply Prod.ext
  · apply Subtype.ext
    apply Units.ext
    ext a b
    show (leviProj k (ePG (i + 1) (t + 1)) (hpgIncl k (i + 1) (t + 1) ⟨uEl k i t c 0, uEl_mem_HPG i t c⟩) false :
      GL (Fin (i + 1 + 1)) k).val a b = (1 + colMat k (i + 1) c : Matrix (Fin (i + 1 + 1)) (Fin (i + 1 + 1)) k) a b
    rw [leviProj_apply]
    show (1 + colMat k ((i + 1) + (t + 1)) (Fin.append c 0) : Matrix (Fin ((i + 1) + (t + 1) + 1)) (Fin ((i + 1) + (t + 1) + 1)) k)
      (ePG (i + 1) (t + 1) ⟨false, a⟩) (ePG (i + 1) (t + 1) ⟨false, b⟩) = _
    rw [Matrix.add_apply, Matrix.add_apply, colMat_ePG_false]
    congr 1
    by_cases hab : a = b
    · subst hab; simp
    · rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne (fun e => hab (by simpa using ePG_inj.1 e))]
  · apply Units.ext
    ext a b
    show (leviProj k (ePG (i + 1) (t + 1)) (hpgIncl k (i + 1) (t + 1) ⟨uEl k i t c 0, uEl_mem_HPG i t c⟩) true :
      GL (Fin (t + 1)) k).val a b = (1 : Matrix (Fin (t + 1)) (Fin (t + 1)) k) a b
    rw [leviProj_apply]
    show (1 + colMat k ((i + 1) + (t + 1)) (Fin.append c 0) : Matrix (Fin ((i + 1) + (t + 1) + 1)) (Fin ((i + 1) + (t + 1) + 1)) k)
      (ePG (i + 1) (t + 1) ⟨true, a⟩) (ePG (i + 1) (t + 1) ⟨true, b⟩) = _
    rw [Matrix.add_apply, ePG_true_eq, ePG_true_eq]
    have h0 : colMat k ((i + 1) + (t + 1)) (Fin.append c 0) (Fin.castSucc (Fin.natAdd (i + 1) a))
        (Fin.castSucc (Fin.natAdd (i + 1) b)) = 0 := by
      unfold colMat
      exact if_neg (Fin.castSucc_ne_last _)
    rw [h0, add_zero]
    by_cases hab : a = b
    · subst hab; simp
    · rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne (fun e => hab (by simpa using e))]

variable {i t : ℕ} (τ : MRep k (i + 1)) (σ : GRep k (t + 1))

def rU : Representation ℂ (Multiplicative (Fin (i + 1) → k)) (τ.V ⊗[ℂ] σ.V) :=
  (extTensor τ.ρ σ.ρ).comp ((GlobalTheory.CompanionTheory.BZPhiPhi.unipM k i).prod 1)

theorem rU_tmul (c : Multiplicative (Fin (i + 1) → k)) (a : τ.V) (b : σ.V) :
    rU τ σ c (a ⊗ₜ b) = τ.ρ (GlobalTheory.CompanionTheory.BZPhiPhi.unipM k i c) a ⊗ₜ b := by
  simp [rU]

theorem isSmooth_rU (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) : IsSmooth (rU τ σ) := by
  refine isSmooth_comp (isSmooth_extTensor hτ hσ) _ ?_
  refine Continuous.prodMk ?_ continuous_const
  exact (GlobalTheory.CompanionTheory.BZPhiPhi.continuous_unipM (k := k) i).comp continuous_toAdd

theorem sigX_uEl (c : Fin (i + 1) → k) :
    sigX τ σ ⟨uEl k i t c 0, uEl_mem_HPG i t c⟩ = rU τ σ (Multiplicative.ofAdd c) := by
  apply TensorProduct.ext'
  intro a b
  rw [rU_tmul]
  have e2 := pgProj_uEl (k := k) i t c
  have e1 : sigX τ σ ⟨uEl k i t c 0, uEl_mem_HPG i t c⟩ (a ⊗ₜ b) =
      (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (pgProj k (i + 1) (t + 1) ⟨uEl k i t c 0, uEl_mem_HPG i t c⟩).1 a ⊗ₜ[ℂ]
        (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ (pgProj k (i + 1) (t + 1) ⟨uEl k i t c 0, uEl_mem_HPG i t c⟩).2 b :=
    extTensor_tmul (mtw τ _).ρ (σ.tw _).ρ _ a b
  have e3 : (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (pgProj k (i + 1) (t + 1) ⟨uEl k i t c 0, uEl_mem_HPG i t c⟩).1 a =
      τ.ρ (GlobalTheory.CompanionTheory.BZPhiPhi.unipM k i (Multiplicative.ofAdd c)) a := by
    rw [e2]
    show twist τ.ρ (dpowM _ _) _ a = _
    rw [twist_apply, GlobalTheory.CompanionTheory.LeibOrd.DerivTw.dpowM_uin _ ⟨_, GlobalTheory.CompanionTheory.BZPhiPhi.unipM_mem_MirUin k i _⟩]
    simp
  have e4 : (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ (pgProj k (i + 1) (t + 1) ⟨uEl k i t c 0, uEl_mem_HPG i t c⟩).2 b = b := by
    rw [e2]
    show ((σ.tw _).ρ 1) b = b
    rw [map_one]
    rfl
  refine e1.trans ?_
  exact congrArg₂ (fun (x : τ.V) (y : σ.V) => (x ⊗ₜ[ℂ] y : τ.V ⊗[ℂ] σ.V)) e3 e4

end Grp

section Integral

open MeasureTheory GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.Rodier.SmIntEl GlobalTheory.CompanionTheory.MirFourier ValuativeRel

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

local instance instMSpi (n : ℕ) : MeasurableSpace (Fin n → k) := borel _
local instance instBSpi (n : ℕ) : BorelSpace (Fin n → k) := ⟨rfl⟩

instance muD_haar (n : ℕ) : (muD k n).IsAddHaarMeasure := by
  unfold muD
  infer_instance

def chi (ψ : AddChar k Circle) {t : ℕ} (d : Fin (t + 1) → k) : ℂ := (((Circle.toUnits (ψ (d (Fin.last t))))⁻¹ : ℂˣ) : ℂ)

theorem isLocallyConstant_chi (ψ : AddChar k Circle) (hψ : Continuous ψ) (t : ℕ) :
    IsLocallyConstant (chi ψ : (Fin (t + 1) → k) → ℂ) := by
  have hl : IsLocallyConstant (ψ : k → Circle) := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    refine ⟨(fun y => y - x) ⁻¹' {y : k | ψ y = 1},
      (GlobalTheory.CompanionTheory.BZFun.isOpen_addChar_eq_one k ψ hψ).preimage (by fun_prop), by simp, fun y hy => ?_⟩
    have hy' : ψ (y - x) = 1 := hy
    have : ψ y = ψ (y - x) * ψ x := by rw [← AddChar.map_add_eq_mul, sub_add_cancel]
    rw [this, hy', one_mul]
  exact (hl.comp_continuous (continuous_apply (Fin.last t))).comp
    (fun z : Circle => (((Circle.toUnits z)⁻¹ : ℂˣ) : ℂ))

theorem chi_add (ψ : AddChar k Circle) {t : ℕ} (a b : Fin (t + 1) → k) :
    chi ψ a = ((Circle.toUnits (ψ (b (Fin.last t))) : ℂˣ) : ℂ) * chi ψ (a + b) := by
  simp only [chi, Pi.add_apply, AddChar.map_add_eq_mul, map_mul, mul_inv]
  rw [← Units.val_mul]
  congr 1
  rw [mul_comm ((Circle.toUnits (ψ (a (Fin.last t))))⁻¹), mul_inv_cancel_left]

variable {i t : ℕ} {τ : MRep k (i + 1)} {σ : GRep k (t + 1)}

def phi (ψ : AddChar k Circle) (w : XS τ σ) (d : Fin (t + 1) → k) : τ.V ⊗[ℂ] σ.V :=
  chi ψ d • evX w (dEmb k i t d * 1)

theorem phi_lc (ψ : AddChar k Circle) (hψ : Continuous ψ) (w : XS τ σ) : IsLocallyConstant (phi ψ w) := by
  exact (isLocallyConstant_chi ψ hψ t).comp₂
    (GlobalTheory.CompanionTheory.BZPhiPG.Fib.fibre_isLocallyConstant_hasCompactSupport k i t τ σ w 1).1 (fun a b => a • b)

theorem phi_cs (ψ : AddChar k Circle) (w : XS τ σ) : HasCompactSupport (phi ψ w) := by
  refine (GlobalTheory.CompanionTheory.BZPhiPG.Fib.fibre_isLocallyConstant_hasCompactSupport k i t τ σ w 1).2.mono ?_
  intro d hd
  intro h0
  exact hd (by
    simp only [phi]
    rw [show evX w (dEmb k i t d * 1) = 0 from h0, smul_zero])

theorem evX_add (a b : XS τ σ) (x : Mir k ((i + 1) + (t + 1))) : evX (a + b) x = evX a x + evX b x := rfl

theorem evX_smul (c : ℂ) (a : XS τ σ) (x : Mir k ((i + 1) + (t + 1))) : evX (c • a) x = c • evX a x := rfl

theorem phi_add (ψ : AddChar k Circle) (a b : XS τ σ) : phi ψ (a + b) = phi ψ a + phi ψ b := by
  funext d
  simp only [phi, Pi.add_apply]
  rw [evX_add, smul_add]

theorem phi_smul (ψ : AddChar k Circle) (c : ℂ) (a : XS τ σ) :
    phi ψ (c • a) = (c • (LinearMap.id : (τ.V ⊗[ℂ] σ.V) →ₗ[ℂ] (τ.V ⊗[ℂ] σ.V))) ∘ phi ψ a := by
  funext d
  simp only [phi, Function.comp_apply, LinearMap.smul_apply, LinearMap.id_apply]
  rw [evX_smul, smul_comm]

def iF (ψ : AddChar k Circle) (w : XS τ σ) : τ.V ⊗[ℂ] σ.V := smInt (muD k (t + 1)) (phi ψ w)

theorem iF_add (ψ : AddChar k Circle) (hψ : Continuous ψ) (a b : XS τ σ) : iF ψ (a + b) = iF ψ a + iF ψ b :=
  (congrArg (smInt (muD k (t + 1))) (phi_add ψ a b)).trans
    (smInt_add _ (phi_lc ψ hψ a) (phi_cs ψ a) (phi_lc ψ hψ b) (phi_cs ψ b))

theorem iF_smul (ψ : AddChar k Circle) (hψ : Continuous ψ) (c : ℂ) (a : XS τ σ) : iF ψ (c • a) = c • iF ψ a :=
  (congrArg (smInt (muD k (t + 1))) (phi_smul ψ c a)).trans
    (smInt_linear _ _ (phi_lc ψ hψ a) (phi_cs ψ a))

def iL (ψ : AddChar k Circle) (hψ : Continuous ψ) : XS τ σ →ₗ[ℂ] τ.V ⊗[ℂ] σ.V where
  toFun w := iF ψ w
  map_add' := iF_add ψ hψ
  map_smul' := iF_smul ψ hψ

theorem evX_cInd (w : XS τ σ) (g x : Mir k ((i + 1) + t + 1)) :
    evX (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) g w) x = evX w (x * g) := rfl

theorem evX_left (w : XS τ σ) (c : Fin (i + 1) → k) (x : Mir k ((i + 1) + t + 1)) :
    evX w (uEl k i t c 0 * x) = rU τ σ (Multiplicative.ofAdd c) (evX w x) := by
  have := (w : smoothPart (ind (HPG k (i + 1) (t + 1)) (sigX τ σ))).1.2 ⟨_, uEl_mem_HPG i t c⟩ x
  rw [sigX_uEl] at this
  exact this

theorem dEmb_mul_uEl (c : Fin (i + 1) → k) (d d₁ : Fin (t + 1) → k) :
    dEmb k i t d * 1 * uEl k i t c d₁ = uEl k i t c 0 * (dEmb k i t (d + d₁) * 1) := by
  simp only [mul_one, dEmb_eq, uEl_mul, zero_add, add_zero]

theorem phi_translate (ψ : AddChar k Circle) (w : XS τ σ) (c : Fin (i + 1) → k) (d₁ d : Fin (t + 1) → k) :
    phi ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (uEl k i t c d₁) w) d =
      ((Circle.toUnits (ψ (d₁ (Fin.last t))) : ℂˣ) : ℂ) • rU τ σ (Multiplicative.ofAdd c) (phi ψ w (d + d₁)) := by
  simp only [phi]
  rw [evX_cInd, dEmb_mul_uEl, evX_left, chi_add ψ d d₁, map_smul, smul_smul]

theorem smInt_translate {W : Type} [AddCommGroup W] [Module ℂ W] (T : W →ₗ[ℂ] W) {φ : (Fin (t + 1) → k) → W}
    (hl : IsLocallyConstant φ) (hc : HasCompactSupport φ) (d₁ : Fin (t + 1) → k) :
    smInt (muD k (t + 1)) ((T ∘ φ) ∘ fun d => d + d₁) = T (smInt (muD k (t + 1)) φ) := by
  rw [smInt_comp_measurePreserving _ (measurePreserving_add_right (muD k (t + 1)) d₁) (hl.comp T),
    smInt_linear _ _ hl hc]

theorem iF_translate (ψ : AddChar k Circle) (hψ : Continuous ψ) (w : XS τ σ) (c : Fin (i + 1) → k)
    (d₁ : Fin (t + 1) → k) :
    iF ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (uEl k i t c d₁) w) =
      ((Circle.toUnits (ψ (d₁ (Fin.last t))) : ℂˣ) : ℂ) • rU τ σ (Multiplicative.ofAdd c) (iF ψ w) := by
  have e : phi ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (uEl k i t c d₁) w) =
      ((((Circle.toUnits (ψ (d₁ (Fin.last t))) : ℂˣ) : ℂ) • rU τ σ (Multiplicative.ofAdd c)) ∘ phi ψ w) ∘
        fun d => d + d₁ := funext fun d => phi_translate ψ w c d₁ d
  exact (congrArg (smInt (muD k (t + 1))) e).trans (smInt_translate _ (phi_lc ψ hψ w) (phi_cs ψ w) d₁)

end Integral

section Main

open MeasureTheory GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.Rodier.SmIntEl GlobalTheory.CompanionTheory.MirFourier ValuativeRel

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

attribute [local instance] instMSpi instBSpi

theorem exists_val_ge (s₁ s₂ : kˣ) :
    ∃ s : kˣ, valuation k (s₁ : k) ≤ valuation k (s : k) ∧ valuation k (s₂ : k) ≤ valuation k (s : k) := by
  rcases le_total (valuation k (s₁ : k)) (valuation k (s₂ : k)) with h | h
  · exact ⟨s₂, h, le_rfl⟩
  · exact ⟨s₁, le_rfl, h⟩

theorem exists_polyBall_of_compact {n : ℕ} {K : Set (Fin n → k)} (hK : IsCompact K) :
    ∃ s : kˣ, ∀ x ∈ K, Multiplicative.ofAdd x ∈ polyBall n s := by
  refine hK.induction_on (p := fun S => ∃ s : kˣ, ∀ x ∈ S, Multiplicative.ofAdd x ∈ polyBall n s)
    ⟨1, by simp⟩ ?_ ?_ ?_
  · rintro S T hST ⟨s, hs⟩
    exact ⟨s, fun x hx => hs x (hST hx)⟩
  · rintro S T ⟨s₁, h₁⟩ ⟨s₂, h₂⟩
    obtain ⟨s, a, b⟩ := exists_val_ge s₁ s₂
    refine ⟨s, fun x hx => ?_⟩
    rcases hx with hx | hx
    · exact polyBall_mono n a (h₁ x hx)
    · exact polyBall_mono n b (h₂ x hx)
  · intro x _
    obtain ⟨s, hs⟩ := exists_mem_polyBall (Multiplicative.ofAdd x)
    exact ⟨_, mem_nhdsWithin_of_mem_nhds
      (((isOpen_polyBall n s).preimage continuous_ofAdd).mem_nhds hs), s, fun y hy => hy⟩

theorem twKer_one_mono {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    {A B : Subgroup G} (h : A ≤ B) : twKer ρ A 1 ≤ twKer ρ B 1 := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨n, v, rfl⟩
  exact Submodule.subset_span ⟨⟨n, h n.2⟩, v, rfl⟩

theorem eq_zero_of_fixed_twKer {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) (L : Subgroup G) (hL : IsCompact (L : Set G))
    {v : V} (hv : v ∈ twKer ρ L 1) (hf : ∀ l ∈ L, ρ l v = v) : v = 0 := by
  have ho : IsOpen (((1 : L →* ℂˣ).ker : Subgroup L) : Set L) := by
    have : (((1 : L →* ℂˣ).ker : Subgroup L) : Set L) = Set.univ := by
      ext x
      simp [MonoidHom.mem_ker]
    rw [this]
    exact isOpen_univ
  obtain ⟨K, T, -, -, -, hT, hsum⟩ :=
    (GlobalTheory.CompanionTheory.TwistedAverage.mem_twKer_iff_average ρ hρ L hL 1 ho v).1 hv
  have hne : T.Nonempty := by
    obtain ⟨t, ⟨ht, -⟩, -⟩ := hT 1
    exact ⟨t, ht⟩
  have hc : (T.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hne.card_pos.ne'
  have h1 : (T.card : ℂ) • v = 0 := by
    rw [← hsum, Nat.cast_smul_eq_nsmul, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hf _ x.2]
    simp
  exact (smul_eq_zero.1 h1).resolve_left hc

variable {i t : ℕ} {τ : MRep k (i + 1)} {σ : GRep k (t + 1)}

theorem exists_polyBall_tmul (x : τ.V) (hx : x ∈ twKer τ.ρ (MirUin k (i + 1)) 1) (b : σ.V) :
    ∃ s : kˣ, (x ⊗ₜ[ℂ] b : τ.V ⊗[ℂ] σ.V) ∈ twKer (rU τ σ) (polyBall (i + 1) s) 1 := by
  unfold twKer at hx
  induction hx using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨u, a, rfl⟩ := hw
    obtain ⟨v, hv⟩ := (Subgroup.mem_subgroupOf.1 u.2 : ((u : Mir k (i + 1)) : GL (Fin (i + 1 + 1)) k) ∈ MirU k (i + 1))
    have hu : (u : Mir k (i + 1)) = GlobalTheory.CompanionTheory.BZPhiPhi.unipM k i v := Subtype.ext hv.symm
    obtain ⟨s, hs⟩ := exists_mem_polyBall v
    refine ⟨s, Submodule.subset_span ⟨⟨v, hs⟩, a ⊗ₜ b, ?_⟩⟩
    rw [rU_tmul, hu]
    simp [TensorProduct.sub_tmul]
  | zero => exact ⟨1, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨s₁, h₁⟩ := hx
    obtain ⟨s₂, h₂⟩ := hy
    obtain ⟨s, a, c⟩ := exists_val_ge s₁ s₂
    refine ⟨s, ?_⟩
    rw [TensorProduct.add_tmul]
    exact add_mem (twKer_one_mono _ (polyBall_mono _ a) h₁) (twKer_one_mono _ (polyBall_mono _ c) h₂)
  | smul c x _ hx =>
    obtain ⟨s, hs⟩ := hx
    refine ⟨s, ?_⟩
    rw [← TensorProduct.smul_tmul']
    exact Submodule.smul_mem _ _ hs

theorem exists_polyBall_of_qC (z : τ.V ⊗[ℂ] σ.V) (hz : qC τ σ z = 0) :
    ∃ s : kˣ, z ∈ twKer (rU τ σ) (polyBall (i + 1) s) 1 := by
  let K := twKer τ.ρ (MirUin k (i + 1)) 1
  have ex : Function.Exact (LinearMap.rTensor σ.V K.subtype) (LinearMap.rTensor σ.V K.mkQ) :=
    rTensor_exact σ.V (LinearMap.exact_subtype_mkQ K) (Submodule.mkQ_surjective K)
  obtain ⟨y, rfl⟩ := (ex z).1 hz
  clear hz
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨1, by simp⟩
  | tmul x b => exact exists_polyBall_tmul x.1 x.2 b
  | add a b ha hb =>
    obtain ⟨s₁, h₁⟩ := ha
    obtain ⟨s₂, h₂⟩ := hb
    obtain ⟨s, u, v⟩ := exists_val_ge s₁ s₂
    refine ⟨s, ?_⟩
    rw [map_add]
    exact add_mem (twKer_one_mono _ (polyBall_mono _ u) h₁) (twKer_one_mono _ (polyBall_mono _ v) h₂)

variable (k) in

def Lball (i t : ℕ) (s : kˣ) : Subgroup (Mir k ((i + 1) + t + 1)) :=
  (polyBall ((i + 1) + t + 1) s).map (GlobalTheory.CompanionTheory.BZPhiPhi.unipM k ((i + 1) + t))

theorem Lball_le (s : kˣ) : Lball k i t s ≤ MirUin k ((i + 1) + t + 1) := by
  rintro _ ⟨v, -, rfl⟩
  exact GlobalTheory.CompanionTheory.BZPhiPhi.unipM_mem_MirUin k _ v

theorem isCompact_Lball (s : kˣ) : IsCompact (Lball k i t s : Set (Mir k ((i + 1) + t + 1))) := by
  have := (isCompact_polyBall (k := k) ((i + 1) + t + 1) s).image
    ((GlobalTheory.CompanionTheory.BZPhiPhi.continuous_unipM (k := k) ((i + 1) + t)).comp continuous_toAdd)
  exact this

theorem uEl_mem_Lball {s : kˣ} {c : Fin (i + 1) → k} {d : Fin (t + 1) → k}
    (hc : Multiplicative.ofAdd c ∈ polyBall (i + 1) s) (hd : Multiplicative.ofAdd d ∈ polyBall (t + 1) s) :
    uEl k i t c d ∈ Lball k i t s := by
  refine ⟨Multiplicative.ofAdd (Fin.append c d : Fin ((i + 1) + (t + 1)) → k), ?_, rfl⟩
  have key : ∀ y : Fin ((i + 1) + (t + 1)), (Fin.append c d : Fin ((i + 1) + (t + 1)) → k) y ∈ GlobalTheory.SplitWeil.cball s := by
    intro y
    refine Fin.addCases (fun a => ?_) (fun a => ?_) y
    · rw [Fin.append_left]; exact hc a
    · rw [Fin.append_right]; exact hd a
  exact key

theorem exists_of_mem_Lball {s : kˣ} {l : Mir k ((i + 1) + t + 1)} (hl : l ∈ Lball k i t s) :
    ∃ (c : Fin (i + 1) → k) (d : Fin (t + 1) → k), Multiplicative.ofAdd c ∈ polyBall (i + 1) s ∧
      Multiplicative.ofAdd d ∈ polyBall (t + 1) s ∧ l = uEl k i t c d := by
  obtain ⟨v, hv, rfl⟩ := hl
  let w' : Fin ((i + 1) + (t + 1)) → k := v.toAdd
  have e : Fin.append (fun a => w' (Fin.castAdd (t + 1) a)) (fun a => w' (Fin.natAdd (i + 1) a)) = w' :=
    Fin.append_castAdd_natAdd
  refine ⟨fun a => w' (Fin.castAdd (t + 1) a), fun a => w' (Fin.natAdd (i + 1) a), fun a => hv _, fun a => hv _, ?_⟩
  apply Subtype.ext
  show unip k ((i + 1) + t + 1) v = unip k ((i + 1) + (t + 1)) _
  congr 1
  exact congrArg Multiplicative.ofAdd e.symm

theorem vanish_of_eigen (ψ : AddChar k Circle) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (s : kˣ) (g : XS τ σ)
    (hev : ∀ (c : Fin (i + 1) → k) (d : Fin (t + 1) → k), Multiplicative.ofAdd c ∈ polyBall (i + 1) s →
      Multiplicative.ofAdd d ∈ polyBall (t + 1) s → ∀ x : Mir k ((i + 1) + t + 1),
        evX g (x * uEl k i t c d) = ((Circle.toUnits (ψ (d (Fin.last t))) : ℂˣ) : ℂ) • evX g x)
    (hsupp : ∀ d : Fin (t + 1) → k, evX g (dEmb k i t d * 1) ≠ 0 → Multiplicative.ofAdd d ∈ polyBall (t + 1) s)
    (hk : iF ψ g ∈ twKer (rU τ σ) (polyBall (i + 1) s) 1) (c : Fin (i + 1) → k) (d : Fin (t + 1) → k) :
    evX g (uEl k i t c d) = 0 := by
  have zc : Multiplicative.ofAdd (0 : Fin (i + 1) → k) ∈ polyBall (i + 1) s := (polyBall (i + 1) s).one_mem
  have zd : Multiplicative.ofAdd (0 : Fin (t + 1) → k) ∈ polyBall (t + 1) s := (polyBall (t + 1) s).one_mem
  have h1 : ∀ d : Fin (t + 1) → k, Multiplicative.ofAdd d ∈ polyBall (t + 1) s →
      evX g (dEmb k i t d * 1) = ((Circle.toUnits (ψ (d (Fin.last t))) : ℂˣ) : ℂ) • evX g 1 := by
    intro d hd
    have := hev 0 d zc hd 1
    rwa [one_mul, ← dEmb_eq, ← mul_one (dEmb k i t d)] at this
  let D : Set (Fin (t + 1) → k) := {d | Multiplicative.ofAdd d ∈ polyBall (t + 1) s}
  have hphi : phi ψ g = D.indicator fun _ => evX g 1 := by
    funext d
    by_cases hd : d ∈ D
    · rw [Set.indicator_of_mem hd]
      simp only [phi]
      rw [h1 d hd, smul_smul]
      have : chi ψ d * ((Circle.toUnits (ψ (d (Fin.last t))) : ℂˣ) : ℂ) = 1 := by
        simp only [chi]
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      rw [this, one_smul]
    · rw [Set.indicator_of_notMem hd]
      simp only [phi]
      have : evX g (dEmb k i t d * 1) = 0 := by
        by_contra h
        exact hd (hsupp d h)
      rw [this, smul_zero]
  have hI : iF ψ g = (((muD k (t + 1) D).toReal : ℝ) : ℂ) • evX g 1 := by
    unfold iF
    rw [hphi]
    exact smInt_indicator _ _ _
  have hDo : IsOpen D := (isOpen_polyBall (t + 1) s).preimage continuous_ofAdd
  have hDc : IsCompact D := by
    have := (isCompact_polyBall (k := k) (t + 1) s).image continuous_toAdd
    convert this using 1
    ext x
    constructor
    · intro hx
      exact ⟨Multiplicative.ofAdd x, hx, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact hy
  have hvol : (((muD k (t + 1) D).toReal : ℝ) : ℂ) ≠ 0 := by
    have h3 : (muD k (t + 1) D).toReal ≠ 0 := ENNReal.toReal_ne_zero.2
      ⟨(hDo.measure_pos _ ⟨0, zd⟩).ne', hDc.measure_lt_top.ne⟩
    exact_mod_cast h3
  have hg1 : evX g 1 ∈ twKer (rU τ σ) (polyBall (i + 1) s) 1 := by
    rw [hI] at hk
    exact (Submodule.smul_mem_iff _ hvol).1 hk
  have hfix : ∀ l ∈ polyBall (i + 1) s, rU τ σ l (evX g 1) = evX g 1 := by
    intro l hl
    have e1 := evX_left g (Multiplicative.toAdd l) 1
    have e2 := hev (Multiplicative.toAdd l) 0 hl zd 1
    rw [mul_one] at e1
    rw [one_mul] at e2
    have e3 : rU τ σ l (evX g 1) = evX g (uEl k i t (Multiplicative.toAdd l) 0) := e1.symm
    rw [e3, e2]
    simp
  have hzero : evX g 1 = 0 :=
    eq_zero_of_fixed_twKer (rU τ σ) (isSmooth_rU τ σ hτ hσ) _ (isCompact_polyBall (i + 1) s) hg1 hfix
  have hD : ∀ d : Fin (t + 1) → k, evX g (dEmb k i t d * 1) = 0 := by
    intro d
    by_cases hd : Multiplicative.ofAdd d ∈ polyBall (t + 1) s
    · rw [h1 d hd, hzero, smul_zero]
    · by_contra h
      exact hd (hsupp d h)
  have e : uEl k i t c d = uEl k i t c 0 * (dEmb k i t d * 1) := by
    simp only [mul_one, dEmb_eq, uEl_mul, zero_add, add_zero]
  rw [e, evX_left, hD, map_zero]

end Main

end GlobalTheory.CompanionTheory.BZPhiPG.LocC

end
