import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RevPosRevPos
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RowHighestLeSpanColWordComplex
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorTestThetaZeroEqThetaSeries
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormRationality
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealSmulSplit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealPointStandardSourceUnitaryComponentsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionRealPointFockVectorsScalarColumnActionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockPolynomialVectorInjectiveNonzeroVacuumStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReversedMinorProductMemHarmonicRowHighestStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HarmonicColumnOperatorEndMemOfUnitaryStableStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdSpan.StableFock

theorem revB_isB : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (B₀ : C.Bas), C.IsB B₀ → C.IsB (revB C.X.p0 B₀) ∧ C.sB (revB C.X.p0 B₀) = C.sB B₀ := by
  intro D S T C B₀ hB₀
  let σ : Equiv.Perm (Fin T.rank) := Function.Involutive.toPerm (revPos C.X.p0) (revPos_revPos C.X.p0)
  have hσ : ∀ τ, revB C.X.p0 B₀ τ = (B₀ τ).submatrix id σ := fun τ => rfl
  have hsg : ∀ a : Fin T.rank, sgn C.X.p0 ((σ a : Fin T.rank) : ℕ) = sgn C.X.p0 (a : ℕ) := by
    intro a
    show sgn C.X.p0 ((revPos C.X.p0 a : Fin T.rank) : ℕ) = _
    unfold revPos
    split_ifs with h
    · simp only [sgn, if_pos h.1, if_pos (show C.X.p0 - 1 - (a : ℕ) < C.X.p0 by omega)]
    · rfl
  have hD : (sgnM C.X).submatrix σ σ = sgnM C.X := by
    unfold sgnM
    rw [Matrix.submatrix_diagonal _ _ σ.injective]
    congr 1
    funext a
    simp only [Function.comp, hsg]
  have hD' : ∀ M : Matrix (Fin T.rank) (Fin T.rank) ℂ, M.submatrix id σ * sgnM C.X = (M * sgnM C.X).submatrix id σ := by
    intro M
    ext i j
    simp only [sgnM, Matrix.mul_diagonal, Matrix.submatrix_apply, id, hsg]
  refine ⟨fun τ => ?_, funext fun τ => ?_⟩
  · rw [hσ, Matrix.conjTranspose_submatrix, ← Matrix.submatrix_id_id (gramAt D T τ),
      ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, hB₀ τ, hD]
  · show (revB C.X.p0 B₀ τ) * sgnM C.X * (revB C.X.p0 B₀ τ)⁻¹ = B₀ τ * sgnM C.X * (B₀ τ)⁻¹
    rw [hσ, hD', show (B₀ τ).submatrix id σ = (B₀ τ).submatrix (Equiv.refl _) σ from rfl,
      Matrix.inv_submatrix_equiv, show (B₀ τ * sgnM C.X).submatrix id σ = (B₀ τ * sgnM C.X).submatrix (Equiv.refl _) σ from rfl,
      Matrix.submatrix_mul_equiv]
    rfl

theorem pureTensorO_revB : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (B₀ : C.Bas), C.IsB B₀ → ∀ (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (f : WO S T → ℂ), C.IsTh f → ∀ P : MvPolynomial (FVar D T.rank S.rank) ℂ, pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB B₀) BS B₀ f P = pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB B₀) BS (revB C.X.p0 B₀) f (MvPolynomial.rename (fun v : FVar D T.rank S.rank => (v.1, revPos C.X.p0 v.2.1, v.2.2)) P) := by
  intro D S T C B₀ hB₀ BS f hf P
  have hS : ∀ τ, IsCartanInv (gramAt D S τ) 1 := by
    intro τ
    have e : gramAt D S τ = 1 := by simp [gramAt, C.m.gS]
    rw [e]
    refine ⟨by simp, by simp, ?_⟩
    simpa using Matrix.PosDef.one
  have hT := fun τ => (((GlobalTheory.Ker.onBasis_frame_period D S T C).2 B₀ hB₀).2.2.1 τ).1
  have := GlobalTheory.OneMapRef.IoCmp.pureTensorO_rename C.std C.inf hS hT hf BS B₀ (revB C.X.p0 B₀)
    (fun _ => revPos C.X.p0) (fun τ => rfl) (fun v : FVar D T.rank S.rank => v.1)
    (fun v => revPos C.X.p0 v.2.1) (fun v => v.2.2) P
  simp only [revPos_revPos] at this
  rw [← this]
  have e : (MvPolynomial.rename fun k : FVar D T.rank S.rank => (k.1, k.2.1, k.2.2)) P = P := by
    change MvPolynomial.rename id P = P
    exact MvPolynomial.rename_id_apply P
  rw [e]

theorem pureTensorO_source : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ), (∀ τ, (BS τ)ᴴ * BS τ = 1) → ∃ u : C.X.Ψ → GL (Fin S.rank) ℂ, (∀ σ, (u σ : Matrix (Fin S.rank) (Fin S.rank) ℂ) ∈ Matrix.unitaryGroup (Fin S.rank) ℂ) ∧ ∀ Q Q' : MvPolynomial (FVar D T.rank S.rank) ℂ, C.toH Q' = Harm.colActHom u (C.toH Q) → ∀ B, C.IsB B → ∀ f, C.IsTh f → pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB B) BS B f Q = C.fvec B f Q' := by
  intro D S T C BS hBS
  obtain ⟨h, -, hh⟩ := GlobalTheory.T.exists_realPoint_standardSource_unitaryComponents D S T C BS hBS
  obtain ⟨u, hu, -, hcol⟩ := GlobalTheory.Ker.ColChange.col_change D S T C h
  refine ⟨u, hu, fun Q Q' hQ B hB f hf => ?_⟩
  have := hcol Q Q' hQ B hB f hf
  rwa [show (fun τ => compAt C.θ τ (mt S h)) = BS from funext hh] at this

theorem colU_surjective : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (u : C.X.Ψ → GL (Fin S.rank) ℂ), (∀ σ, (u σ : Matrix (Fin S.rank) (Fin S.rank) ℂ) ∈ Matrix.unitaryGroup (Fin S.rank) ℂ) → ∃ h ∈ GinfC S, GlobalTheory.Ker.ColChange.colU C h = u := by
  intro D S T C u hu
  have hv : ∀ τ, ((u (C.m.e τ) : Matrix (Fin S.rank) (Fin S.rank) ℂ).map conj)ᴴ *
      (u (C.m.e τ) : Matrix (Fin S.rank) (Fin S.rank) ℂ).map conj = 1 := by
    intro τ
    have hA := (Matrix.mem_unitaryGroup_iff').1 (hu (C.m.e τ))
    have e : ((u (C.m.e τ) : Matrix (Fin S.rank) (Fin S.rank) ℂ).map conj)ᴴ *
        (u (C.m.e τ) : Matrix (Fin S.rank) (Fin S.rank) ℂ).map conj =
        (star (u (C.m.e τ) : Matrix (Fin S.rank) (Fin S.rank) ℂ) *
          (u (C.m.e τ) : Matrix (Fin S.rank) (Fin S.rank) ℂ)).map conj := by
      ext i j
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum, Matrix.star_eq_conjTranspose]
    rw [e, hA]
    ext i j
    simp [Matrix.one_apply]
  obtain ⟨h, hh, hcomp⟩ := GlobalTheory.T.exists_realPoint_standardSource_unitaryComponents D S T C _ hv
  refine ⟨h, hh, funext fun σ => Units.ext ?_⟩
  show (compAt C.θ (C.m.e.symm σ) (mt S h)).map conj = (u σ : Matrix (Fin S.rank) (Fin S.rank) ℂ)
  rw [hcomp]
  ext i j
  simp

theorem fockSpan_rowHighest : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → T.rank ≤ S.rank → ∀ B₀, C.IsB B₀ → ∀ BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ, (∀ τ, (BS τ)ᴴ * BS τ = 1) → ∀ f, C.IsTh f → C.IsFock B₀ f → f ≠ 0 → ∀ (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ), (∀ τ, p τ = C.X.p0) → (∀ τ, q τ = C.q0) → ∀ (pt : MvPolynomial (FVar D T.rank S.rank) ℂ → WO S T → ℂ) (U : Submodule ℂ (MvPolynomial (FVar D T.rank S.rank) ℂ)), (∀ P, pt P = pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB B₀) BS B₀ f P) → Formalism.IndefR.Datum.delta p q ap am ∈ U → (∀ h ∈ GinfC S, ∀ P ∈ U, ∃ P' ∈ U, om (h, 1) (pt P) = pt P') → C.IsB (revB C.X.p0 B₀) ∧ C.sB (revB C.X.p0 B₀) = C.sB B₀ ∧ ∃ (c : C.X.Ψ → Fin C.q0 → ℕ) (c' : C.X.Ψ → Fin C.X.p0 → ℕ) (Q₀ : MvPolynomial (FVar D T.rank S.rank) ℂ), C.toH Q₀ ∈ Harm.rowHighest ℂ c c' ∧ C.fvec (revB C.X.p0 B₀) f Q₀ = pt (Formalism.IndefR.Datum.delta p q ap am) ∧ pt (Formalism.IndefR.Datum.delta p q ap am) ≠ 0 ∧ ∀ Q, C.toH Q ∈ Harm.rowHighest ℂ c c' → ∃ P ∈ U, C.fvec (revB C.X.p0 B₀) f Q = pt P := by
  intro D S T C om hom hrk B₀ hB₀ BS hBS f hf hF hf0 p q ap am hp hq pt U hpt hΔ hU
  obtain ⟨hB, hsB⟩ := revB_isB D S T C B₀ hB₀
  refine ⟨hB, hsB, ?_⟩
  have hFB : C.IsFock (revB C.X.p0 B₀) f := by
    intro τ
    rw [hsB]
    exact hF τ
  obtain ⟨u₀, -, hcol⟩ := pureTensorO_source D S T C BS hBS
  have hinj := C.toH_bijective.1
  have hsurj := C.toH_bijective.2
  have hpt' : ∀ P, ∃ Q, C.toH Q = Harm.colActHom u₀ (C.toH (MvPolynomial.rename
      (fun v : FVar D T.rank S.rank => (v.1, revPos C.X.p0 v.2.1, v.2.2)) P)) ∧
      C.fvec (revB C.X.p0 B₀) f Q = pt P := by
    intro P
    obtain ⟨Q, hQ⟩ := hsurj (Harm.colActHom u₀ (C.toH (MvPolynomial.rename
      (fun v : FVar D T.rank S.rank => (v.1, revPos C.X.p0 v.2.1, v.2.2)) P)))
    refine ⟨Q, hQ, ?_⟩
    rw [hpt, pureTensorO_revB D S T C B₀ hB₀ BS f hf P]
    have := hcol _ _ hQ (revB C.X.p0 B₀) hB f hf
    rw [hsB] at this
    exact this.symm
  obtain rfl : p = fun _ => C.X.p0 := funext hp
  obtain rfl : q = fun _ => C.q0 := funext hq
  obtain ⟨c, c', hc, hc0⟩ := GlobalTheory.T.reversedMinorProduct_mem_harmonicRowHighest D S T C hrk ap am
  obtain ⟨Q₀, hQ₀, hQ₀pt⟩ := hpt' (Formalism.IndefR.Datum.delta (fun _ => C.X.p0) (fun _ => C.q0) ap am)
  have hQ₀mem : C.toH Q₀ ∈ Harm.rowHighest ℂ c c' := by
    rw [hQ₀]
    exact Harm.colAct_mem_rowHighest u₀ hc
  have hQ₀ne : C.toH Q₀ ≠ 0 := by
    rw [hQ₀]
    intro h
    apply hc0
    apply (Harm.colAct ℂ C.X.Ψ C.q0 C.X.p0 (Fin S.rank) u₀).injective
    rw [map_zero]
    exact h
  have hfv0 : C.fvec (revB C.X.p0 B₀) f 0 = 0 := by
    unfold Ctx.fvec
    exact map_zero _
  have hptne : pt (Formalism.IndefR.Datum.delta (fun _ => C.X.p0) (fun _ => C.q0) ap am) ≠ 0 := by
    rw [← hQ₀pt]
    intro h
    have := GlobalTheory.T.fockPolynomialVector_injective_nonzeroVacuum D S T C _ hB f hf hFB hf0 (h.trans hfv0.symm)
    exact hQ₀ne (by rw [this, map_zero])
  refine ⟨c, c', Q₀, hQ₀mem, hQ₀pt, hptne, ?_⟩

  set L₁ := pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB (revB C.X.p0 B₀)) (fun _ => 1) (revB C.X.p0 B₀) f
    with hL₁
  set L₂ := pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB B₀) BS B₀ f with hL₂
  have hfv : ∀ Q, C.fvec (revB C.X.p0 B₀) f Q = L₁ Q := fun Q => rfl
  let V : Submodule ℂ (MvPolynomial (FVar D T.rank S.rank) ℂ) := (U.map L₂).comap L₁
  have hV : ∀ Q, Q ∈ V ↔ ∃ P ∈ U, C.fvec (revB C.X.p0 B₀) f Q = pt P := by
    intro Q
    simp only [V, Submodule.mem_comap, Submodule.mem_map, hfv, hpt]
    exact ⟨fun ⟨P, hP, e⟩ => ⟨P, hP, e.symm⟩, fun ⟨P, hP, e⟩ => ⟨P, hP, e.symm⟩⟩
  let W : Submodule ℂ (Harm.Poly ℂ C.X.Ψ C.q0 C.X.p0 (Fin S.rank)) :=
    V.map C.toH.toLinearMap ⊓ Harm.rowHighest ℂ c c'
  have hW : ∀ w, w ∈ W ↔ (∃ Q ∈ V, C.toH Q = w) ∧ w ∈ Harm.rowHighest ℂ c c' := by
    intro w
    simp [W, Submodule.mem_inf, Submodule.mem_map]
  have hWst : ∀ g : C.X.Ψ → GL (Fin S.rank) ℂ,
      (∀ t, (g t : Matrix (Fin S.rank) (Fin S.rank) ℂ) ∈ Matrix.unitaryGroup (Fin S.rank) ℂ) →
      ∀ w ∈ W, Harm.colActHom g w ∈ W := by
    intro g hg w hw
    obtain ⟨⟨Q, hQV, rfl⟩, hwR⟩ := (hW w).1 hw
    refine (hW _).2 ⟨?_, Harm.colAct_mem_rowHighest g hwR⟩
    obtain ⟨Q', hQ'⟩ := hsurj (Harm.colActHom g (C.toH Q))
    refine ⟨Q', ?_, hQ'⟩
    obtain ⟨h, hh, rfl⟩ := colU_surjective D S T C g hg
    obtain ⟨a, ha, hact⟩ := GlobalTheory.T.weilAction_realPoint_fockVectors_scalar_columnAction D S T C om hom _ hB f hf hFB h hh
    obtain ⟨P, hPU, hP⟩ := (hV Q).1 hQV
    obtain ⟨P', hP'U, hP'⟩ := hU h hh P hPU
    refine (hV Q').2 ⟨a⁻¹ • P', U.smul_mem _ hP'U, ?_⟩
    have e1 := hact Q Q' hQ'
    rw [hP, hP'] at e1
    rw [hpt, map_smul, ← hpt, e1, smul_smul, inv_mul_cancel₀ ha, one_smul]
  have hle : W ≤ Harm.rowHighest ℂ c c' := inf_le_right
  have hLie := GlobalTheory.T.harmonicColumnOperatorEnd_mem_of_unitary_stable W hWst
  have hWne : W ≠ ⊥ := by
    intro h
    have : C.toH Q₀ ∈ W := (hW _).2 ⟨⟨Q₀, (hV Q₀).2 ⟨_, hΔ, hQ₀pt⟩, rfl⟩, hQ₀mem⟩
    rw [h, Submodule.mem_bot] at this
    exact hQ₀ne this
  have hn : C.q0 + C.X.p0 ≤ S.rank := by have := C.hr; omega
  have hbase := Harm.basePoly_mem_of_colLie_stable hn c c' W hle hLie hWne
  have hword : ∀ w, Harm.colWord ℂ hn c c' w ∈ W := by
    intro w
    induction w with
    | nil => exact hbase
    | cons i w ih => exact hLie i.1 i.2.1 i.2.2 _ ih
  have hall : Harm.rowHighest ℂ c c' ≤ W :=
    (Harm.rowHighest_le_span_colWord_complex hn c c').trans
      (Submodule.span_le.2 (by rintro _ ⟨w, rfl⟩; exact hword w))
  intro Q hQ
  obtain ⟨⟨Q₁, hQ₁, e⟩, -⟩ := (hW _).1 (hall hQ)
  obtain rfl := hinj e
  exact (hV Q₁).1 hQ₁

end GlobalTheory.AdSpan.StableFock

end
