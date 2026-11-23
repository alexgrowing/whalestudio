import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValuationGdetKapAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SquareFlipEquivariantBlockDiagonalColumnSubstituStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SquareFlipRowsIntegralGLInvariantStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlipGridPathAtSquareSplitStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSplitThetaGridPathFlipGridPathAtSquareStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitThetaGridPathAvoidsOppositeCornerStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemGridPathInnerVerticesFlipGridPathAtSquareStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

noncomputable section
namespace GlobalTheory.FlipAdm

theorem isPath_flipPath {γ : List Edge} {i j : ℕ} (hγ : IsPath γ) (h : PassesThrough i j γ) :
    IsPath (flipPath i j γ) := GlobalTheory.T.isSplitThetaGridPath_flipGridPathAtSquare hγ h

theorem exists_split {γ : List Edge} {i j : ℕ} (hγ : IsPath γ) (h : PassesThrough i j γ) :
    ∃ l₁ l₂ : List Edge, γ = l₁ ++ [Edge.theta i j, Edge.ex i j] ++ l₂ ∧
      flipPath i j γ = l₁ ++ [Edge.ex i (j + 1), Edge.theta (i + 1) j] ++ l₂ := GlobalTheory.T.flipGridPathAtSquare_split hγ h

theorem not_touch {γ : List Edge} {i j : ℕ} (hγ : IsPath γ) (h : PassesThrough i j γ) :
    ∀ b ∈ γ, b.src ≠ (i + 1, j + 1) ∧ b.tgt ≠ (i + 1, j + 1) := GlobalTheory.T.splitThetaGridPath_avoids_opposite_corner hγ h

theorem innerVertices_flipPath {γ : List Edge} {i j : ℕ} (hγ : IsPath γ) (h : PassesThrough i j γ) :
    ∀ X ∈ innerVertices (flipPath i j γ), X ≠ (i, j) ∧ (X ≠ (i + 1, j + 1) → X ∈ innerVertices γ) :=
  GlobalTheory.T.mem_gridPathInnerVertices_flipGridPathAtSquare hγ h

end GlobalTheory.FlipAdm

noncomputable section
namespace GlobalTheory.FlipAdm
section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
  [BorelSpace k]

theorem squareFlip_const_mul {A A' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D]
    [DecidableEq D] (μ : Measure (GL A' k)) (σ : A ⊕ A' ≃ D) (ψ : AddChar k Circle) (ν : kˣ →* ℂˣ) (ϖ : kˣ) (e : ℕ)
    (P : Finset D) (c : ℂ) (Φ : Matrix A' D k → ℂ) (X : Matrix A D k) :
    squareFlip μ σ ψ ν ϖ e P (fun Z => c * Φ Z) X = c * squareFlip μ σ ψ ν ϖ e P Φ X := by
  have hs : ∀ (Ψ : Matrix A' D k → ℂ) (Y : Matrix A' D k), smallF μ ν (c • Ψ) Y = c * smallF μ ν Ψ Y := by
    intro Ψ Y
    simp only [smallF, Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact integral_const_mul c _
  have hf : ∀ (Ψ : Matrix A' D k → ℂ) (Y : Matrix A D k), fFun μ σ ν (c • Ψ) Y = c * fFun μ σ ν Ψ Y := by
    intro Ψ Y
    unfold fFun
    split_ifs
    · rw [hs]; ring
    · simp
  have h1 : ∀ Ψ : Matrix A' D k → ℂ, phiA μ σ ν ϖ e (blockLat ϖ e P) (c • Ψ) = c • phiA μ σ ν ϖ e (blockLat ϖ e P) Ψ := by
    intro Ψ
    funext Y
    simp only [phiA, Pi.smul_apply, smul_eq_mul]
    split_ifs
    · rw [hf]
    · simp
  have h0 : (fun Z => c * Φ Z) = c • Φ := rfl
  rw [h0, squareFlip, map_smul, h1, map_smul]
  rfl

variable {G : Grid k}

theorem toCols₁_mul_fromBlocks {m n o : Type} [Fintype n] [Fintype o] (Z : Matrix m (n ⊕ o) k) (A : Matrix n n k)
    (D : Matrix o o k) : (Z * fromBlocks A 0 0 D).toCols₁ = Z.toCols₁ * A := by
  ext r c; simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.toCols₁]

theorem toCols₂_mul_fromBlocks {m n o : Type} [Fintype n] [Fintype o] (Z : Matrix m (n ⊕ o) k) (A : Matrix n n k)
    (D : Matrix o o k) : (Z * fromBlocks A 0 0 D).toCols₂ = Z.toCols₂ * D := by
  ext r c; simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.toCols₂]

theorem joinA_moveArgs (i j : ℕ) (g : G.VertexGroup) (x : G.Args) :
    G.joinA i j (G.moveArgs .one g x) =
      fromCols ((g (i + 1, j + 1)).valᵀ * (G.joinA i j x * fromBlocks (invT (g (i, j + 1))).val 0 0 (g (i + 1, j)).val).toCols₁)
        (((g (i + 1, j + 1))⁻¹).val * (G.joinA i j x * fromBlocks (invT (g (i, j + 1))).val 0 0 (g (i + 1, j)).val).toCols₂) := by
  have e1 : (G.joinA i j x * fromBlocks (invT (g (i, j + 1))).val 0 0 (g (i + 1, j)).val).toCols₁ =
      x (.ex i (j + 1)) * (invT (g (i, j + 1))).val := by
    simp [Grid.joinA, fromCols_mul_fromBlocks]
  have e2 : (G.joinA i j x * fromBlocks (invT (g (i, j + 1))).val 0 0 (g (i + 1, j)).val).toCols₂ =
      (x (.theta (i + 1) j))ᵀ * (g (i + 1, j)).val := by
    simp [Grid.joinA, fromCols_mul_fromBlocks]
  rw [e1, e2]
  simp only [Grid.joinA, Grid.moveArgs, Assignment.read, invT_inv_val, Matrix.transpose_mul, Matrix.transpose_transpose,
    invT_val, Matrix.mul_assoc]

theorem sliceB_pathAct (γ : List Edge) (i j : ℕ) (g : G.VertexGroup) (hg : g (i, j) = 1) (T : G.Args → ℂ)
    (x : G.Args) (Z : Matrix (Fin (G.rank (i, j))) (G.Cols i j) k) :
    G.sliceB i j (G.pathAct .one γ g T) x Z = (γ.map (G.edgeFactor .one g)).prod *
      G.sliceB i j T (G.moveArgs .one g x) (Z * fromBlocks (invT (g (i, j + 1))).val 0 0 (g (i + 1, j)).val) := by
  simp only [Grid.sliceB, Grid.pathAct]
  congr 2
  have hne : Edge.theta i j ≠ Edge.ex i j := by simp
  funext b
  by_cases hb : b = .ex i j
  · subst hb
    simp only [Function.update_self, Grid.moveArgs, Assignment.read, invT_inv_val]
    simp [hg, toCols₂_mul_fromBlocks, Matrix.transpose_mul]
  · by_cases hb' : b = .theta i j
    · subst hb'
      simp only [Function.update_of_ne hne, Function.update_self, Grid.moveArgs, Assignment.read]
      simp [hg, toCols₁_mul_fromBlocks]
    · simp only [Grid.moveArgs, Function.update_of_ne hb, Function.update_of_ne hb']

theorem pathAct_mulSingle_of_not_touch {ϖ : kˣ} {e : ℕ} {γ : List Edge} {T : G.Args → ℂ} (hT : G.IsTensor ϖ e γ T)
    (X : ℕ × ℕ) (hX : ∀ b ∈ γ, b.src ≠ X ∧ b.tgt ≠ X) (u : GL (Fin (G.rank X)) k) :
    G.pathAct .one γ (Pi.mulSingle X u) T = T := by
  funext x
  have h1 : (γ.map (G.edgeFactor .one (Pi.mulSingle X u))).prod = 1 := List.prod_eq_one fun c hc => by
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hc
    have hap : ∀ z, apow (1 : kˣ) z = 1 := fun z => apow_of_valuation_eq_one (by simp) z
    simp [Grid.edgeFactor, Pi.mulSingle_eq_of_ne (hX b hb).1, Pi.mulSingle_eq_of_ne (hX b hb).2, hap]
  rw [Grid.pathAct, h1, one_mul]
  refine hT.1 fun b hb => ?_
  simp [Grid.moveArgs, Pi.mulSingle_eq_of_ne (hX b hb).1, Pi.mulSingle_eq_of_ne (hX b hb).2]

theorem edgeFactor_square (i j : ℕ) (g : G.VertexGroup) (hg : g (i, j) = 1) (hK : ∀ Y, g Y ∈ KO k _) :
    G.edgeFactor .one g (.ex i (j + 1)) * G.edgeFactor .one g (.theta (i + 1) j) *
        ((G.nu i j (gdet (g (i, j + 1))) : ℂ) * (G.nu i j (gdet (g (i + 1, j))) : ℂ)) =
      G.edgeFactor .one g (.theta i j) * G.edgeFactor .one g (.ex i j) * (G.nu i j (gdet (g (i + 1, j + 1))) : ℂ) := by
  have ha : ∀ Y, ∀ z : ℂ, apow (gdet (Assignment.one.read (g Y))) z = 1 := fun Y z =>
    apow_of_valuation_eq_one (valuation_gdet_of_mem_KO (Assignment.one.read_mem_KO (hK Y))) z
  have hap : ∀ z, apow (1 : kˣ) z = 1 := fun z => apow_of_valuation_eq_one (by simp) z
  simp only [Grid.edgeFactor, Edge.src, Edge.tgt, ha, mul_one, hg, map_one, hap]
  simp only [Grid.kappa, Grid.blockChar, Grid.nu, gdet, map_one, MonoidHom.div_apply, Units.val_div_eq_div_val,
    Units.val_inv_eq_inv_val, Units.val_one, inv_one, mul_one, one_mul]
  field_simp
end
end GlobalTheory.FlipAdm

noncomputable section
namespace GlobalTheory.FlipAdm
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
  [BorelSpace k] {G : Grid k}

theorem pathAct_flipTensor {ψ : AddChar k Circle} {ϖ : kˣ} {e : ℕ} (hϖ : IsUnif ϖ) (hψ : HasConductor ψ 1) (he : 1 ≤ e)
    {i j : ℕ} (hν : CondLE ϖ e (G.nu i j)) {J : G.Level} (hJ : IsOpen (J (i, j) : Set (GL (Fin (G.rank (i, j))) k)))
    (hJK : J (i, j) ≤ KO k _) (l₁ l₂ : List Edge) {T : G.Args → ℂ}
    (hT : G.IsTensor ϖ e (l₁ ++ [Edge.theta i j, Edge.ex i j] ++ l₂) T) (g : G.VertexGroup) (hg : g (i, j) = 1)
    (hK : ∀ Y, g Y ∈ KO k _) :
    G.pathAct .one (l₁ ++ [Edge.ex i (j + 1), Edge.theta (i + 1) j] ++ l₂) g (G.flipTensor .one ψ ϖ e i j J T) =
      G.flipTensor .one ψ ϖ e i j J (G.pathAct .one (l₁ ++ [Edge.theta i j, Edge.ex i j] ++ l₂) g T) := by
  have hJ' := isOpen_map_invT hJ hJK
  haveI := isHaarMeasure_haarVol hJ'.1 hJ'.2
  funext x
  set Φ := G.sliceB i j T (G.moveArgs .one g x) with hΦ
  have hN : IsNatDatum ϖ e Φ := isNatDatum_sliceB hT (by simp) (by simp) _
  have hM₁ : invT (g (i, j + 1)) ∈ KO k _ := invT_mem_KO (hK _)
  have hM₂ : g (i + 1, j) ∈ KO k _ := hK _
  have hcol := GlobalTheory.T.squareFlip_equivariant_blockDiagonal_columnSubstitution (haarVol ((J (i, j)).map invT)) (stdSplit (G.rank_square i j)) ψ (G.nu i j) ϖ e hϖ hψ he hν
    Φ hN _ hM₁ _ hM₂ (G.joinA i j x)
  have hrow := GlobalTheory.T.squareFlip_rows_integralGL_invariant (haarVol ((J (i, j)).map invT)) (stdSplit (G.rank_square i j)) ψ (G.nu i j) ϖ e hϖ hψ he hν
    Φ hN _ (hK (i + 1, j + 1))
    (G.joinA i j x * fromBlocks (invT (g (i, j + 1))).val 0 0 (g (i + 1, j)).val)
  have hsl : G.sliceB i j (G.pathAct .one (l₁ ++ [Edge.theta i j, Edge.ex i j] ++ l₂) g T) x =
      fun Z => ((l₁ ++ [Edge.theta i j, Edge.ex i j] ++ l₂).map (G.edgeFactor .one g)).prod *
        Φ (Z * fromBlocks (invT (g (i, j + 1))).val 0 0 (g (i + 1, j)).val) :=
    funext fun Z => sliceB_pathAct _ i j g hg T x Z
  have hsc := edgeFactor_square i j g hg hK
  simp only [Grid.flipTensor, Grid.pathAct]
  rw [hsl, squareFlip_const_mul, hcol, joinA_moveArgs, ← hΦ]
  have hrow' := (eq_inv_mul_iff_mul_eq₀ (Units.ne_zero _)).2 hrow
  rw [hrow']
  simp only [List.map_append, List.prod_append, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [gdet_invT, map_inv, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val]
  generalize squareFlip (haarVol ((J (i, j)).map invT)) (stdSplit (G.rank_square i j)) ψ (G.nu i j) ϖ e
    (Assignment.one.block _ _) Φ (G.joinA i j x * fromBlocks (invT (g (i, j + 1))).val 0 0 (g (i + 1, j)).val) = S
  have h1 := Units.ne_zero (G.nu i j (gdet (g (i, j + 1))))
  have h2 := Units.ne_zero (G.nu i j (gdet (g (i + 1, j))))
  have h3 := Units.ne_zero (G.nu i j (gdet (g (i + 1, j + 1))))
  field_simp
  linear_combination ((l₁.map (G.edgeFactor .one g)).prod * (l₂.map (G.edgeFactor .one g)).prod * S) * hsc

end GlobalTheory.FlipAdm

noncomputable section
namespace GlobalTheory.FlipAdm

theorem isAdmissible_flip : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {Γ : Grid k} (ψ : AddChar k Circle) (ϖ : kˣ) (e : ℕ), IsUnif ϖ → HasConductor ψ 1 → 1 ≤ e →
    ∀ (St : Γ.PiLocalization₂) (x : ℕ × ℕ), CondLE ϖ e (Γ.nu x.1 x.2) → PassesThrough x.1 x.2 St.path →
    (∀ X, IsOpen (St.level X : Set (GL (Fin (Γ.rank X)) k)) ∧ St.level X ≤ KO k _) →
    St.IsAdmissible .one ϖ e → (St.flip .one ψ ϖ e x).IsAdmissible .one ϖ e := by
  intro k _ _ _ _ _ _ Γ ψ ϖ e hϖ hψ he St x hν hpt hlev hadm
  obtain ⟨i, j⟩ := x
  obtain ⟨γ, J, T⟩ := St
  obtain ⟨hpath, -, htens, hinv⟩ := hadm
  simp only at hν hpt hlev hpath htens hinv
  obtain ⟨l₁, l₂, hγ, hfl⟩ := exists_split hpath hpt
  have h1 : Edge.theta i j ∈ γ := hpt.subset (by simp)
  have h2 : Edge.ex i j ∈ γ := hpt.subset (by simp)
  refine ⟨isPath_flipPath hpath hpt, fun X _ => ?_, isTensor_flipTensor hϖ hψ he hν (hlev (i, j)).1 (hlev (i, j)).2 h1 h2 htens,
    fun X hX u hu => ?_⟩
  · by_cases hXW : X = (i + 1, j + 1)
    · subst hXW
      simp only [Grid.PiLocalization₂.flip, Grid.flipLevel, Function.update_self]
      exact ⟨isOpen_KO, le_rfl⟩
    · simp only [Grid.PiLocalization₂.flip, Grid.flipLevel, Function.update_of_ne hXW]
      exact hlev X
  · simp only [Grid.PiLocalization₂.flip] at hX hu ⊢
    obtain ⟨hX1, hX2⟩ := innerVertices_flipPath hpath hpt X hX
    have huK : u ∈ KO k _ := by
      by_cases hXW : X = (i + 1, j + 1)
      · subst hXW; simpa [Grid.flipLevel] using hu
      · rw [Grid.flipLevel, Function.update_of_ne hXW] at hu; exact (hlev X).2 hu
    have hg1 : (Pi.mulSingle X u : Γ.VertexGroup) (i, j) = 1 := Pi.mulSingle_eq_of_ne (Ne.symm hX1) _
    have hgK : ∀ Y, (Pi.mulSingle X u : Γ.VertexGroup) Y ∈ KO k _ := fun Y => by
      by_cases hY : Y = X
      · subst hY; simpa using huK
      · rw [Pi.mulSingle_eq_of_ne hY]; exact one_mem _
    rw [hfl]
    subst hγ
    rw [pathAct_flipTensor hϖ hψ he hν (hlev (i, j)).1 (hlev (i, j)).2 l₁ l₂ htens _ hg1 hgK]
    congr 1
    by_cases hXW : X = (i + 1, j + 1)
    · subst hXW
      exact pathAct_mulSingle_of_not_touch htens _ (not_touch hpath hpt) u
    · rw [Grid.flipLevel, Function.update_of_ne hXW] at hu
      exact hinv X (hX2 hXW) u hu

end GlobalTheory.FlipAdm
