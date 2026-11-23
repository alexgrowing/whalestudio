import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompReixMemAdm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxSymplecticDoubledHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFreeLocalChartStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot GlobalTheory.DblBox

noncomputable section

namespace GlobalTheory.DblBox

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}

def renumU {J : Matrix (Fin n) (Fin n) E} {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E}
    (hJ : J₂ = dblGram finSumFinEquiv J) : UG (cA σ) (GlobalTheory.WeilM.dbl (incM F J)) →* UA σ J₂ :=
  ((Units.map (Matrix.reindexAlgEquiv (AE F E) (AE F E) finSumFinEquiv).toRingEquiv.toMonoidHom).comp
    (UG (cA σ) (GlobalTheory.WeilM.dbl (incM F J))).subtype).codRestrict _ fun p => by
      have hp : p.1.1ᵀ * GlobalTheory.WeilM.dbl (incM F J) * p.1.1.map (cA σ) = GlobalTheory.WeilM.dbl (incM F J) := p.2
      rw [hJ, GlobalTheory.DefDoubling.incM_dblGram]
      change (p.1.1.submatrix finSumFinEquiv.symm finSumFinEquiv.symm)ᵀ *
        (GlobalTheory.WeilM.dbl (incM F J)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm *
        (p.1.1.submatrix finSumFinEquiv.symm finSumFinEquiv.symm).map (cA σ) =
        (GlobalTheory.WeilM.dbl (incM F J)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm
      rw [Matrix.transpose_submatrix, ← Matrix.submatrix_map, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hp]

theorem mat_renumU {J : Matrix (Fin n) (Fin n) E} {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E}
    (hJ : J₂ = dblGram finSumFinEquiv J) (p : UG (cA σ) (GlobalTheory.WeilM.dbl (incM F J))) :
    mat (renumU hJ p) = p.1.1.submatrix finSumFinEquiv.symm finSumFinEquiv.symm := rfl

theorem continuous_renumU {J : Matrix (Fin n) (Fin n) E} {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E}
    (hJ : J₂ = dblGram finSumFinEquiv J) : Continuous (renumU (F := F) (σ := σ) hJ) := by
  have h1 : Continuous fun p : UG (cA σ) (GlobalTheory.WeilM.dbl (incM F J)) => mat (renumU hJ p) :=
    (Units.continuous_val.comp continuous_subtype_val).matrix_submatrix _ _
  refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨h1, (h1.comp continuous_inv).congr fun k => ?_⟩)
  rw [Function.comp_apply, map_inv]
  rfl

def tw {A : Type} (w : Matrix (Fin d) (Fin n ⊕ Fin n) A) : Matrix (Fin (n + n)) (Fin d) A :=
  fun k j => w j (finSumFinEquiv.symm k)

theorem upB_tw {A : Type} (w : Matrix (Fin d) (Fin n ⊕ Fin n) A) : upB (tw w) = (Matrix.toCols₁ w)ᵀ := by
  ext i j; simp [upB, tw, Matrix.toCols₁]

theorem loB_tw {A : Type} (w : Matrix (Fin d) (Fin n ⊕ Fin n) A) : loB (tw w) = (Matrix.toCols₂ w)ᵀ := by
  ext i j; simp only [loB, tw, Equiv.symm_apply_apply]; rfl

theorem tw_diag_mem {A : Type} [CommRing A] (z : Matrix (Fin d) (Fin n) A) (j : Fin d) :
    (tw (z * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) A)ᵀ))ᵀ j ∈ diagSub A finSumFinEquiv := by
  rw [diagCols, Matrix.transpose_fromRows, Matrix.transpose_one, Matrix.mul_fromCols, Matrix.mul_one]
  refine funext fun k => ?_
  simp only [LinearMap.funLeft_apply, Function.comp_apply, Matrix.transpose_apply, tw, Equiv.symm_apply_apply]
  rfl

theorem blocks_of_diagCols {A : Type} [CommRing A] {P : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) A}
    {t : Matrix (Fin n) (Fin n) A}
    (h : (P * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) A) : Matrix (Fin n ⊕ Fin n) (Fin n) A) =
      (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) A) * t) :
    P.toBlocks₁₁ + P.toBlocks₁₂ = t ∧ P.toBlocks₂₁ + P.toBlocks₂₂ = t := by
  rw [← Matrix.fromBlocks_toBlocks P, diagCols, Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul] at h
  simpa using Matrix.fromRows_inj h

def reixRep {G κ κ' : Type} [Group G] (e : κ ≃ κ') (om : G →* Module.End ℂ ((κ' → AF F) → ℂ)) :
    G →* Module.End ℂ ((κ → AF F) → ℂ) where
  toFun g := (reix e).symm.toLinearMap ∘ₗ om g ∘ₗ (reix e).toLinearMap
  map_one' := LinearMap.ext fun φ => by simp
  map_mul' g h := LinearMap.ext fun φ => by simp

theorem reix_reixRep {G κ κ' : Type} [Group G] (e : κ ≃ κ') (om : G →* Module.End ℂ ((κ' → AF F) → ℂ)) (g : G)
    (φ : (κ → AF F) → ℂ) : reix e (reixRep e om g φ) = om g (reix e φ) := (reix e).apply_symm_apply _

theorem left_factor : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s' r₁ s₁ : ℕ),
    IsPair B M χX χW om r s' r₁ s₁ →
    ∀ X₂ : Spc F E (n + n), X₂.J = dblGram finSumFinEquiv X.J →
    ∀ i : UA σ X.J × UA σ X.J →* UA σ X₂.J, (∀ g g', mat (i (g, g')) = blkMat finSumFinEquiv (mat g) (mat g')) →
    ∀ (Mb : Model σ X₂ W) (χ χ' : Chr F E) (omb : Rep σ X₂ W) (r₂ s₂ : ℕ), IsPair B Mb χ χ' omb r₂ s₂ r₁ s₁ → IsBoxCo M.co Mb.co →
    ∀ l ∈ (adeleClass F).adm (Fin (n + n) × Fin d), (∃ φ ∈ schA F (Fin (n + n) × Fin d), l φ ≠ 0) →
    (∀ u : Matrix (Fin (n + n)) (Fin d) (AE F E), (∀ j, uᵀ j ∈ diagSub (AE F E) finSumFinEquiv) →
      ∀ φ ∈ schA F (Fin (n + n) × Fin d), l (Mb.co.rho B.ψ u φ) = l φ) →
    (∀ p : siegelOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype, ∀ φ ∈ schA F (Fin (n + n) × Fin d),
      l (omb ((p : UA σ X₂.J), 1) φ) = (χW (aOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype p) : ℂ) *
        GlobalTheory.Doubling.npow (absE F E (aOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype p)) ((d : ℂ) / 2) * l φ) →
    ∀ (g : UA σ X.J), ∀ φ₁ ∈ schA F (Fin n × Fin d), ∀ φ₂ ∈ schA F (Fin n × Fin d),
      omb (i (g, 1), 1) (bx φ₁ φ₂) = bx (om (g, 1) φ₁) φ₂ := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s' r₁ s₁ hP X₂ hJ i hi Mb χ χ' omb r₂ s₂ hPb hbox l hl hne hinv hlaw
    g φ₁ hφ₁ φ₂ hφ₂
  obtain ⟨-, ⟨d', hd', -, dd, omd, hdd, ⟨-, hSd, hR⟩, hres⟩, -⟩ := hP.weil
  have hSb := hPb.weil.isUSplitting
  let R := reix (R := AF F) (rIdx n d)
  let ρ : UG (cA σ) (GlobalTheory.WeilM.dbl (incM F X.J)) →* Module.End ℂ (Fn F (n + n) d) :=
    omb.comp ((MonoidHom.inl _ _).comp (renumU hJ))
  have hρ : ∀ p, ρ p = omb (renumU hJ p, 1) := fun p => rfl
  have hrho : ∀ w φ, R (dd.rho B.ψ w φ) = Mb.co.rho B.ψ (tw w) (R φ) := fun w φ => by
    rw [hbox.rho_reix, upB_tw, loB_tw, ← hd', ← hd', Matrix.transpose_transpose, Matrix.transpose_transpose, ← hdd,
      Matrix.fromCols_toCols]
    rfl
  have hact : ∀ (p : UG (cA σ) (GlobalTheory.WeilM.dbl (incM F X.J))) (w : Matrix (Fin d) (Fin n ⊕ Fin n) (AE F E)),
      tw (actB (cA σ) p w) = actAB (cA σ) (renumU hJ p, (1 : UA σ W.J)) (tw w) := fun p w => by
    change tw (w * p.1.1ᵀ) = mat (renumU hJ p) * tw w * (1 : Matrix (Fin d) (Fin d) (AE F E))ᵀ
    rw [Matrix.transpose_one, Matrix.mul_one, mat_renumU]
    ext k j
    simp only [tw, Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply]
    rw [← finSumFinEquiv.symm.sum_comp]
    exact Finset.sum_congr rfl fun x _ => mul_comm _ _
  have hR' : ∀ φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), R φ ∈ schA F (Fin (n + n) × Fin d) :=
    fun φ h => reix_mem_schA _ h
  have hS₁ : IsSplitting (adeleClass F) B.ψ dd (actB (cA σ)) (reixRep (rIdx n d) ρ) := by
    refine ⟨fun p φ hφ => (reix_mem_schA_iff (rIdx n d)).1 ?_, fun p w φ hφ => R.injective ?_, fun p l' hl' => ?_⟩
    · rw [reix_reixRep]; exact hSb.pres _ _ (hR' φ hφ)
    · rw [hrho, reix_reixRep, reix_reixRep, hrho, hρ, hSb.impl _ _ _ (hR' φ hφ), hact]
    · exact comp_reix_mem_adm (rIdx n d) (hSb.adm (renumU hJ p, 1) _ (comp_reix_mem_adm (rIdx n d).symm hl'))
  have hC₁ : IsContOn (adeleClass F) (reixRep (rIdx n d) ρ) := fun l' hl' φ hφ =>
    (hSb.cont _ (comp_reix_mem_adm (rIdx n d).symm hl') _ (hR' φ hφ)).comp
      ((continuous_renumU hJ).prodMk continuous_const)
  have hsc : ∀ u : (AE F E)ˣ, ((((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F) u) : ℝ) ^
      ((Fintype.card (Fin d) : ℝ) / 2) : ℝ) : ℂ) = GlobalTheory.Doubling.npow (absE F E u) ((d : ℂ) / 2) := by
    intro u
    rw [GlobalTheory.ModuAdele.modu_norm_eq_absE, GlobalTheory.Doubling.npow, Complex.ofReal_cpow (NNReal.coe_nonneg _)]
    congr 1
    push_cast
    simp only [Fintype.card_fin]
  have heq := GlobalTheory.T.weil_doubled_darboux_coordinates F E σ hP.base.cm d n W.J X.J 1 (fun i j => by simp [hP.herm.herm i j])
    (isUnit_det_of_isHerm F E σ B n X r s' hP.herm).ne_zero B.ψ hP.base.std _ dd omd (reixRep (rIdx n d) ρ)
    hSd.toIsSplitting hSd.cont hS₁ hC₁ (l ∘ₗ R.toLinearMap)
    (by
      obtain ⟨φ, hφ, h⟩ := hne
      exact ⟨R.symm φ, reix_mem_schA (rIdx n d).symm hφ, by simpa using h⟩)
    (fun p t hpt φ hφ => by
      have h1 := hR (l ∘ₗ R.toLinearMap) (comp_reix_mem_adm (rIdx n d) hl) (fun z φ hφ => by
        change l (R (dd.rho B.ψ _ φ)) = l (R φ)
        rw [hrho]
        exact hinv _ (tw_diag_mem z) _ (hR' φ hφ)) p t hpt φ hφ
      have hb := blocks_of_diagCols hpt
      have hsub : (mat (renumU hJ p)).submatrix finSumFinEquiv finSumFinEquiv = p.1.1 := by
        rw [mat_renumU]; simp
      have hlev : leviMat finSumFinEquiv (mat (renumU hJ p)) = t.1 := by rw [leviMat, hsub, hb.1]
      have hmem : renumU hJ p ∈ siegelOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype := by
        rw [mem_siegelOf]
        change KeepsDiag finSumFinEquiv (mat (renumU hJ p))
        rw [KeepsDiag, hlev, hsub, hb.2]
      have ha : aOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype ⟨_, hmem⟩ = Matrix.GeneralLinearGroup.det t :=
        Units.ext (congrArg Matrix.det hlev)
      have h2 := hlaw ⟨_, hmem⟩ _ (hR' φ hφ)
      rw [ha] at h2
      rw [h1, hsc]
      change _ = l (R (reixRep (rIdx n d) ρ p φ))
      rw [reix_reixRep]
      exact h2.symm)
  have hg : renumU hJ (GlobalTheory.DblEvalLaw.leftU g) = i (g, 1) := by
    apply Subtype.ext; apply Units.ext
    change mat _ = mat _
    rw [hi, mat_renumU]
    rfl
  have h3 := congrArg R ((hres g (GlobalTheory.DblEvalLaw.leftU g) rfl φ₁ hφ₁ φ₂ hφ₂).symm.trans
    (heq _ _ (GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ φ₁ hφ₁ φ₂ hφ₂)))
  rw [reix_reixRep, hρ, hg] at h3
  exact h3.symm

end GlobalTheory.DblBox

end
