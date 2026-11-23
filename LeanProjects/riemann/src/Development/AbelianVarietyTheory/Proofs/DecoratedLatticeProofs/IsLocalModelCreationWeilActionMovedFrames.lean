import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationCommFockPolynomialVectors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPureTensorO
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormUnitaryPairAction
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.StepData NumberField
open scoped Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LocModMove

variable {D : D7}

theorem half_iff {m n : ℕ} (e : AE D) (u : Mx D m n) : IsHalf e u ↔ e • u = u := by
  constructor
  · intro h; ext i j; rw [Matrix.smul_apply, smul_eq_mul, h i j]
  · intro h i j; have := congrFun (congrFun h i) j; rwa [Matrix.smul_apply, smul_eq_mul] at this

theorem mtMul (V : HSp D) (a b : GA D V) : Formalism.L2.Theta.mt V (a * b) = Formalism.L2.Theta.mt V a * Formalism.L2.Theta.mt V b := by
  simp [Formalism.L2.Theta.mt]

theorem mtOne (V : HSp D) : Formalism.L2.Theta.mt V 1 = 1 := by
  simp [Formalism.L2.Theta.mt]

theorem half_actO {e : AE D} {S T : HSp D} (g : GA D S) (h : GA D T) {u : WO S T} (hu : IsHalf e u) :
    IsHalf e (actO S T g h u) := by
  rw [half_iff] at hu ⊢
  calc e • actO S T g h u = actO S T g h (e • u) := by simp only [actO, Matrix.mul_smul, Matrix.smul_mul]
    _ = actO S T g h u := by rw [hu]

theorem actO_actO_inv'' {S T : HSp D} (g : GA D S) (h : GA D T) (y : WO S T) :
    actO S T g h (actO S T g⁻¹ h⁻¹ y) = y := by
  simp only [actO, inv_inv]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← mtMul, mul_inv_cancel, mtOne, Matrix.one_mul, Matrix.mul_assoc,
    ← mtMul, mul_inv_cancel, mtOne, Matrix.mul_one]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

theorem infPart_e (p : Place D k) : infPart D p.e = 0 := by
  obtain ⟨h1, h2, v, ε, ⟨α, rfl, -⟩, h3⟩ := p.split
  have h0 : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 0 := TensorProduct.zero_tmul _ _
  have : p.e = p.e * (p.e + cA D p.e) := by rw [mul_add, h1, h2, add_zero]
  rw [this, h3, RingHom.map_mul, h0, mul_zero]

theorem half_up (p : Place D k) {S T : HSp D} (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (x : Matrix Y Y' k) :
    IsHalf p.e (p.up FS FT x) := by
  intro i j
  simp only [Place.up, Matrix.map_apply]
  rw [← p.ι_π, p.π_ι]

theorem eq_of_half (p : Place D k) {m n : ℕ} {z z' : Mx D m n} (hz : IsHalf p.e z) (hz' : IsHalf p.e z')
    (h : z.map p.π = z'.map p.π) : z = z' := by
  ext i j
  have a := p.ι_π (z i j)
  have b := p.ι_π (z' i j)
  rw [hz i j] at a
  rw [hz' i j] at b
  rw [← a, ← b]
  exact congrArg p.ι (congrFun (congrFun h i) j)

theorem up_move (p : Place D k) {S T : HSp D} (FS GS : Frame k S.rank Y') (FT GT : Frame k T.rank Y) (g : GA D S)
    (h : GA D T) (hS : GS.β = (Formalism.L2.Theta.mt S g).map p.π * FS.β) (hT : GT.β = (Formalism.L2.Theta.mt T h).map p.π * FT.β)
    (x : Matrix Y Y' k) : p.up GS GT x = actO S T g h (p.up FS FT x) := by
  apply eq_of_half p (half_up p GS GT x) (half_actO g h (half_up p FS FT x))
  have hm : ∀ {a b c : ℕ} (A : Matrix (Fin a) (Fin b) (AE D)) (B : Matrix (Fin b) (Fin c) (AE D)),
      (A * B).map p.π = A.map p.π * B.map p.π := fun A B => Matrix.map_mul
  have h1 : FS.γ * (Formalism.L2.Theta.mt S g⁻¹).map p.π * GS.β = 1 := by
    rw [hS, Matrix.mul_assoc, ← Matrix.mul_assoc ((Formalism.L2.Theta.mt S g⁻¹).map p.π), ← hm, ← mtMul, inv_mul_cancel,
      mtOne, Matrix.map_one _ (map_zero p.π) (map_one p.π), Matrix.one_mul, FS.γβ]
  have hγ : FS.γ * (Formalism.L2.Theta.mt S g⁻¹).map p.π = GS.γ := by
    calc FS.γ * (Formalism.L2.Theta.mt S g⁻¹).map p.π = FS.γ * (Formalism.L2.Theta.mt S g⁻¹).map p.π * (GS.β * GS.γ) := by
          rw [GS.βγ, Matrix.mul_one]
      _ = GS.γ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hπι : ∀ M : Matrix (Fin T.rank) (Fin S.rank) k, (M.map p.ι).map p.π = M := by
    intro M; ext i j; simp [p.π_ι]
  simp only [Place.up, actO]
  rw [hm, hm, hT, ← hγ]
  simp only [hπι, Matrix.mul_assoc]

end GlobalTheory.LocModMove

namespace GlobalTheory.LocModMove

theorem isModel_move : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS GS : Frame k S.rank Y') (FT GT : Frame k T.rank Y) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsInfFam θ → IsWeilDatumO ψ S T χS χT ω → ∀ (g : GA D S) (h : GA D T), GS.β = (Formalism.L2.Theta.mt S g).map p.π * FS.β → GT.β = (Formalism.L2.Theta.mt T h).map p.π * FT.β → ∀ sS sT BS BT P T₁, p.IsModel ψ FS FT T₁ → ∃ T₂, p.IsModel ψ GS GT T₂ ∧ ∀ Φ, T₂ Φ = ω (g, h) (pureTensorO ψ θ S T sS sT BS BT (T₁ Φ) P) := by
  intro D k _ _ _ _ p Y Y' _ _ _ _ S T FS GS FT GT ψ θ χS χT ω hθ hω g h hS hT sS sT BS BT P T₁ hT₁
  have hψ := hω.std
  have e0 := infPart_e p
  have ce0 : infPart D (cA D p.e) = 0 := GlobalTheory.PlaceDatum.infPart_cA e0
  have pt_add : ∀ f f', IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' →
      pureTensorO ψ θ S T sS sT BS BT (f + f') P =
        pureTensorO ψ θ S T sS sT BS BT f P + pureTensorO ψ θ S T sS sT BS BT f' P := by
    intro f f' hf hf'
    have := GlobalTheory.FockFiniteHeis.pureTensorO_lin ψ θ S T hψ hθ sS BS sT BT 1 hf hf' P
    rwa [one_smul, one_smul] at this
  have pt_smul : ∀ (c : ℂ) f, IsThetaFunO ψ S T f →
      pureTensorO ψ θ S T sS sT BS BT (c • f) P = c • pureTensorO ψ θ S T sS sT BS BT f P := by
    intro c f hf
    have := GlobalTheory.FockFiniteHeis.pureTensorO_lin ψ θ S T hψ hθ sS BS sT BT c hf GlobalTheory.OrientedHeis.theta_zero P
    rwa [add_zero, GlobalTheory.FockFiniteHeis.pureTensorO_zero ψ θ S T hψ hθ sS BS sT BT P, add_zero] at this
  let L : SB (Matrix Y Y' k) →ₗ[ℂ] (WO S T → ℂ) :=
    { toFun := fun Φ => pureTensorO ψ θ S T sS sT BS BT (T₁ Φ) P
      map_add' := fun Φ Φ' => by
        simp only [map_add]; exact pt_add _ _ (hT₁.theta Φ) (hT₁.theta Φ')
      map_smul' := fun c Φ => by
        simp only [map_smul, RingHom.id_apply]; exact pt_smul c _ (hT₁.theta Φ) }
  have comm : ∀ u : WO S T, u.map (infPart D) = 0 → ∀ Φ,
      pureTensorO ψ θ S T sS sT BS BT (heisO ψ S T u (T₁ Φ)) P =
        heisO ψ S T u (pureTensorO ψ θ S T sS sT BS BT (T₁ Φ) P) :=
    fun u hu Φ => ((GlobalTheory.FinTranslate.finite_translate D ψ θ S T hψ hθ _ (hT₁.theta Φ)).2 u hu).2 sS BS sT BT P
  have thL : ∀ Φ, IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT (T₁ Φ) P) := fun Φ =>
    GlobalTheory.GalLift.Vec.theta_pureTensorO hψ hθ sS BS sT BT (hT₁.theta Φ) P
  refine ⟨(ω (g, h)) ∘ₗ L, ⟨fun Φ => hω.om_pres _ _ (thL Φ), ?_, ?_⟩, fun Φ => rfl⟩
  · intro x Φ Φ' hΦ
    have hu := GlobalTheory.PlaceDatum.infPart_of_half e0 (half_up p FS FT x)
    show ω (g, h) (pureTensorO ψ θ S T sS sT BS BT (T₁ Φ') P) =
      heisO ψ S T (p.up GS GT x) (ω (g, h) (pureTensorO ψ θ S T sS sT BS BT (T₁ Φ) P))
    rw [hT₁.trans x Φ Φ' hΦ, comm _ hu, hω.om_heis g h _ _ (thL Φ), ← up_move p FS GS FT GT g h hS hT x]
  · intro y hy Φ Φ' hΦ
    obtain ⟨y', hy'd⟩ : ∃ y', y' = actO S T g⁻¹ h⁻¹ y := ⟨_, rfl⟩
    have hy' : IsHalf (cA D p.e) y' := hy'd ▸ half_actO _ _ hy
    have hyy : actO S T g h y' = y := hy'd ▸ actO_actO_inv'' g h y
    have hΦ' : ∀ t, Φ'.1 t = ψ (symplO S T (p.up FS FT t) y') * Φ.1 t := by
      intro t
      rw [hΦ t, up_move p FS GS FT GT g h hS hT t, ← GlobalTheory.SymplOInv.symplO_actO D S T g h (p.up FS FT t) y', hyy]
    show ω (g, h) (pureTensorO ψ θ S T sS sT BS BT (T₁ Φ') P) =
      heisO ψ S T y (ω (g, h) (pureTensorO ψ θ S T sS sT BS BT (T₁ Φ) P))
    rw [hT₁.modul y' hy' Φ Φ' hΦ', comm _ (GlobalTheory.PlaceDatum.infPart_of_half ce0 hy'), hω.om_heis g h _ _ (thL Φ), hyy]

end GlobalTheory.LocModMove
