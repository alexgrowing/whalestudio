import Development.WeilBound.ThetaLifts.CartanFactorisation.FockSecondActionMatrixUnitEq
import Development.WeilBound.ThetaLifts.Reductions.LocalPoly
import Development.WeilBound.ThetaLifts.Reductions.TensJoin
import Development.WeilBound.ThetaLifts.Reductions.JoinDef

noncomputable section

namespace PositivityTheory.ThKR.Join

open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.ThK PiTensorProduct
open PositivityTheory.ThKF.Unit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem join_pair {n d P Q R S : ℕ} {X : Spc F E n} {W : Spc F E d} {B : Base F E} {M : Model σ X W} {om : Rep σ X W}
    (hcm : IsCMExt F E σ) {A : InfinitePlace F → Matrix (Fin n) (Ix P Q) ℂ} {C : InfinitePlace F → Matrix (Fin d) (Ix R S) ℂ}
    (fr : Framed B.emb (incM F X.J) (incM F W.J) 1 Complex.I A C) {Φ : Tens F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d)}
    (inj : Function.Injective Φ) (hr : LinearMap.range Φ = M.Pol B.ψ B.emb) {c₁ c₂ : InfinitePlace F → ℂ}
    (h1 : ActsBy B.emb A (om.comp (MonoidHom.inl _ _)) Φ (fockAct1 P Q R S) c₁)
    (h2 : ActsBy B.emb C (om.comp (MonoidHom.inr _ _)) Φ (fockAct2 P Q R S) c₂)
    (ho : ∀ w, Two P Q R S (-c₁ w)) : JoinAt B M om := by
  have mem : ∀ T, Φ T ∈ M.Pol B.ψ B.emb := fun T => hr ▸ LinearMap.mem_range_self Φ T
  have sA : ∀ N, GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om N → ∀ w Z T,
      atL w (fockAct1 P Q R S Z) T + (c₁ w * Z.trace) • T ∈ N.comap Φ := fun N hN w Z T => by
    have u : ∀ Z ∈ upq P Q, atL w (fockAct1 P Q R S Z) T + (c₁ w * Z.trace) • T ∈ N.comap Φ := fun Z hZ => by
      obtain ⟨γ, hγ, h⟩ := line_at hcm fr.2.1 h1 w hZ
      exact hN.2.1 γ hγ (Φ T) (mem T) _ (h T)
    obtain ⟨Z₁, a1, Z₂, a2, rfl, -⟩ := decomp Z
    have e : atL w (fockAct1 P Q R S (Z₁ + Complex.I • Z₂)) T + (c₁ w * (Z₁ + Complex.I • Z₂).trace) • T =
        (atL w (fockAct1 P Q R S Z₁) T + (c₁ w * Z₁.trace) • T) +
          Complex.I • (atL w (fockAct1 P Q R S Z₂) T + (c₁ w * Z₂.trace) • T) := by
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
      module
    rw [e]
    exact add_mem (u Z₁ a1) (Submodule.smul_mem _ _ (u Z₂ a2))
  have sZ : ∀ N, GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om N → ∀ (f : InfinitePlace F → Formalism.BasicNotions.TH.Pol P Q R S) w,
      f w ∈ ReciprocityTheory.ThetaSummability.Real.coinvSub (ReciprocityTheory.ChartRestriction.G.ThK.Real.act1 P Q R S) (ReciprocityTheory.ChartRestriction.G.ThK.Real.chiTr (-c₁ w)) →
      tprod ℂ f ∈ N.comap Φ := fun N hN f w hf => by
    let j : Formalism.BasicNotions.TH.Pol P Q R S →ₗ[ℂ] Tens F P Q R S := (PiTensorProduct.tprod ℂ).toLinearMap f w
    have hj : ∀ (L : Module.End ℂ (Formalism.BasicNotions.TH.Pol P Q R S)) x, j (L x) = atL w L (j x) := fun L x => (atL_tprod w L f x).symm
    have : ReciprocityTheory.ThetaSummability.Real.coinvSub (ReciprocityTheory.ChartRestriction.G.ThK.Real.act1 P Q R S) (ReciprocityTheory.ChartRestriction.G.ThK.Real.chiTr (-c₁ w)) ≤
        (N.comap Φ).comap j := iSup_le fun Z => by
      rintro _ ⟨x, rfl⟩
      show j (FockH1Action.fockAct1 P Q R S Z x - (-c₁ w * Z.trace) • x) ∈ N.comap Φ
      rw [fockFirstAction_matrixUnit_eq, map_sub, map_smul, hj, neg_mul, neg_smul, sub_neg_eq_add]
      exact sA N hN w Z _
    simpa [j] using this hf
  have sB : ∀ N, GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om N → ∀ w Z, ∀ x ∈ N.comap Φ,
      atL w (fockAct2 P Q R S Z) x ∈ N.comap Φ := fun N hN w Z x hx => by
    have u : ∀ Z ∈ upq R S, atL w (fockAct2 P Q R S Z) x ∈ N.comap Φ := fun Z hZ => by
      obtain ⟨γ, hγ, h⟩ := line_at hcm fr.2.2 h2 w hZ
      have : _ ∈ N.comap Φ := hN.2.2.2.1 γ hγ (Φ x) hx _ (h x)
      simpa using (N.comap Φ).sub_mem this ((N.comap Φ).smul_mem (c₂ w * Z.trace) hx)
    obtain ⟨Z₁, a1, Z₂, a2, rfl, -⟩ := decomp Z
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
    exact add_mem (u Z₁ a1) (Submodule.smul_mem _ _ (u Z₂ a2))
  have top : ∀ N, GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om N → N.comap Φ = ⊤ → N = M.Pol B.ψ B.emb := fun N hN e =>
    le_antisymm hN.1 (by
      rw [← hr]
      rintro _ ⟨T, rfl⟩
      exact (e ▸ Submodule.mem_top : T ∈ N.comap Φ))
  intro N N' hN hN' n1 n2 e
  choose K k1 k2 k3 v k4 using ho
  refine (tens_join (V := fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol P Q R S) (A := fun _ => Mat R S)
    (fun _ Z => fockAct2 P Q R S Z) K _
    (fun _ => by rw [← (MvPolynomial.basisMonomials _ ℂ).mk_eq_rank'']; exact Cardinal.mk_le_aleph0) k1
    (fun w Z x hx => fockSecondAction_matrixUnit_eq P Q R S ▸ k2 w Z x hx) (fun w N h h' => k3 w N h (fockSecondAction_matrixUnit_eq P Q R S ▸ h')) v
    (fun w => fockSecondAction_matrixUnit_eq P Q R S ▸ k4 w) (N.comap Φ) (N'.comap Φ) (sZ N hN) (sZ N' hN') (sB N hN) (sB N' hN')
    (eq_top_iff.2 fun T _ => ?_)).elim (fun h => n1 (top N hN h)) fun h => n2 (top N' hN' h)
  obtain ⟨x, hx, y, hy, e'⟩ := Submodule.mem_sup.1 (e ▸ mem T : Φ T ∈ N ⊔ N')
  obtain ⟨x, rfl⟩ : x ∈ LinearMap.range Φ := hr ▸ hN.1 hx
  obtain ⟨y, rfl⟩ : y ∈ LinearMap.range Φ := hr ▸ hN'.1 hy
  rw [← inj ((map_add Φ x y).trans e')]
  exact Submodule.add_mem_sup hx hy

theorem joinTri_of (hF : FockEx) (hP : PolRange) (h1 : LieFirst) (h2 : LieSecond) : JoinTri := by
  intro F E _ _ _ _ _ σ B a a' G X om om' t
  have par := PositivityTheory.RL.even_im_hermitian_sub F E σ B a a' G X om om' t
  have hg := t.geo
  have hb := t.base
  have hc := t.chars
  have od : ∀ w, Two (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) (-(((B.mβ w - B.mα w : ℤ) : ℂ) / 2)) ∧
      Two G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) (-(((B.mα w - B.mβ w : ℤ) : ℂ) / 2)) := fun w => by
    have k := hg.kappa w
    obtain ⟨m, hm⟩ := par w
    obtain ⟨m', hm'⟩ := hg.even
    have e1 := hg.lt
    have e2 := hg.eBig
    have e3 := hg.aBig
    have ek : (((B.mα w - B.mβ w).toNat : ℕ) : ℤ) = B.mα w - B.mβ w := Int.toNat_of_nonneg (by omega)
    have := two_data ⟨a, a', G.p, G.q, (B.mα w - B.mβ w).toNat⟩ (by constructor <;> simp only <;> omega)
    have ec : (((B.mα w - B.mβ w).toNat : ℕ) : ℂ) = ((B.mα w - B.mβ w : ℤ) : ℂ) := by exact_mod_cast congrArg (Int.cast : ℤ → ℂ) ek
    simp only [ec] at this
    refine ⟨?_, this.2⟩
    rw [show -(((B.mβ w - B.mα w : ℤ) : ℂ) / 2) = ((B.mα w - B.mβ w : ℤ) : ℂ) / 2 by push_cast; ring]
    exact this.1
  obtain ⟨A, C, Φ, fr, a1, a2, hΦ⟩ := PositivityTheory.ThKF.PC.exists_fock hF (PositivityTheory.ThKG.pairV t)
  obtain ⟨A', C', Φ', fr', a1', a2', hΦ'⟩ := PositivityTheory.ThKF.PC.exists_fock hF (PositivityTheory.ThKG.pairV' t)
  have hwp : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V.J) (incM F G.W.J) G.M.co X.β (X.β / X.α) om := t.weil
  have hwp' : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V'.J) (incM F G.W.J) G.M'.co X.α (X.α / X.β) om' := t.weil'
  obtain ⟨d, hd, hB1⟩ := hwp.2.1
  obtain ⟨d', hd', hB1'⟩ := hwp'.2.1
  exact ⟨join_pair hb.cm fr hΦ.1 (hP F E σ _ _ _ _ _ _ G.V G.W G.M B.ψ B.emb A C Φ hb.cm hb.std fr a1 a2 hΦ)
      (h1 F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co d 1 Complex.I A C Φ _ _ _ hb.cm hb.std fr hΦ hd hB1
        (hasExp_div B.emb hc.expβ hc.expα))
      (h2 F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co 1 Complex.I A C Φ _ X.β B.mβ hb.cm hb.std fr hΦ hwp.1 hc.expβ)
      fun w => (od w).1,
    join_pair hb.cm fr' hΦ'.1 (hP F E σ _ _ _ _ _ _ G.V' G.W G.M' B.ψ B.emb A' C' Φ' hb.cm hb.std fr' a1' a2' hΦ')
      (h1 F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M'.co d' 1 Complex.I A' C' Φ' _ _ _ hb.cm hb.std fr' hΦ' hd' hB1'
        (hasExp_div B.emb hc.expα hc.expβ))
      (h2 F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M'.co 1 Complex.I A' C' Φ' _ X.α B.mα hb.cm hb.std fr' hΦ' hwp'.1 hc.expα)
      fun w => (od w).2⟩

end PositivityTheory.ThKR.Join

end
