import Development.WeilBound.ThetaLifts.CartanFactorisation.PolCountDef
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLActs
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLFrame

noncomputable section

namespace PositivityTheory.ThKF.PC

open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem incM_map {n m : Type} (J : Matrix n m E) {w : InfinitePlace F} (τ : EmbOver E w) :
    (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  simp [incM, piInf, compInf, inclR, infEmb_tmul]

theorem pol_le (hV : VacLine) {n d P Q R S : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) {ψ : AddChar (AF F) ℂ}
    {τ : ∀ w : InfinitePlace F, EmbOver E w} {A : InfinitePlace F → Matrix (Fin n) (Ix P Q) ℂ}
    {C : InfinitePlace F → Matrix (Fin d) (Ix R S) ℂ} {Φ : Tens F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d)}
    (hcm : IsCMExt F E σ) (hψ : IsStd ψ) (hfr : Framed τ (incM F X.J) (incM F W.J) 1 Complex.I A C)
    (hθX : ∀ w, X.θ w * A w = A w * Jm P Q) (hθW : ∀ w, W.θ w * C w = C w * Jm R S) (hΦ : IsFockMap ψ τ M.co A C Φ) :
    M.Pol ψ τ ≤ LinearMap.range Φ := by
  have hL := PositivityTheory.RL.actsLaws
  have hz : ∀ (u : Matrix (Fin n) (Fin d) (AE F E)) (t : ℝ), M.co.rho ψ (realAd F t • u) 0 = 0 := by
    intro u t; funext x; simp [Darboux.rho, schr]
  have toD : ∀ u (f f₁ : SInf F (Fin n × Fin d)), SD (fun t => M.co.rho ψ (realAd F t • u)) f f₁ →
      ActsD (evI F) (M.heisLine ψ u) f f₁ := fun u f f₁ h => (hL F (Fin n × Fin d) f f₁ f₁).1 _ (hz u) h
  choose A' hA' using fun w => (hfr.2.1 w).2
  choose C' hC' using fun w => (hfr.2.2 w).2
  have decomp : ∀ (u : Matrix (Fin n) (Fin d) (AE F E)) w,
      u.map (piInf (τ w)) = A w * (A' w * u.map (piInf (τ w)) * (C' w)ᵀ) * (C w)ᵀ := by
    intro u w
    rw [show A w * (A' w * u.map (piInf (τ w)) * (C' w)ᵀ) * (C w)ᵀ =
        (A w * A' w) * u.map (piInf (τ w)) * ((C w) * (C' w))ᵀ by
          rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc], hA', hC']
    simp
  have tw : ∀ w (c : Matrix (Ix P Q) (Ix R S) ℂ) (e : ℂ),
      A w * (e • (Jm P Q * c * Jm R S)) * (C w)ᵀ = e • (X.θ w * (A w * c * (C w)ᵀ) * (W.θ w)ᵀ) := by
    intro w c e
    have h2 : (C w)ᵀ * (W.θ w)ᵀ = Jm R S * (C w)ᵀ := by
      rw [← Matrix.transpose_mul, hθW w, Matrix.transpose_mul,
        show (Jm R S)ᵀ = Jm R S by simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_transpose]]
    calc A w * (e • (Jm P Q * c * Jm R S)) * (C w)ᵀ = e • ((A w * Jm P Q) * c * (Jm R S * (C w)ᵀ)) := by
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      _ = _ := by rw [← hθX w, ← h2]; simp only [Matrix.mul_assoc]
  unfold Model.Pol
  refine sInf_le ⟨fun f₀ hf₀ => ?_, fun u hu f hf f₁ h1 => ?_⟩
  · obtain ⟨ε, hε⟩ := hf₀
    obtain ⟨z, hz⟩ := hV F E σ (Fin n) (Fin d) (Fin n × Fin d) P Q R S ψ τ (incM F X.J) (incM F W.J) M.co 1
      Complex.I A C Φ hcm hψ hfr hΦ f₀ ε (fun u u' hu hu' c hc hc' f f' hf hf' =>
        hε u u' hu hu' (fun w => by rw [hc' w, tw, ← hc w]) f f' (toD _ _ _ hf) (toD _ _ _ hf'))
    exact ⟨z • PiTensorProduct.tprod ℂ (fun _ => (1 : Formalism.BasicNotions.TH.Pol P Q R S)), by rw [map_smul, hz]⟩
  · obtain ⟨T, rfl⟩ := hf
    exact ⟨_, (hL F _ _ _ _).2.2.1 _ (toD _ _ _ (hΦ.2 u hu _ (decomp u) T)) h1⟩

theorem exists_fock (hF : FockEx) {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {B : Base F E} {M : Model σ X W} {χX χW : Chr F E}
    {om : Rep σ X W} {r s r' s' : ℕ} (hp : IsPair B M χX χW om r s r' s') :
    ∃ (A : InfinitePlace F → Matrix (Fin n) (Ix r s) ℂ) (C : InfinitePlace F → Matrix (Fin d) (Ix r' s') ℂ)
      (Φ : Tens F r s r' s' →ₗ[ℂ] SInf F (Fin n × Fin d)), Framed B.emb (incM F X.J) (incM F W.J) 1 Complex.I A C ∧
      (∀ w, X.θ w * A w = A w * Jm r s) ∧ (∀ w, W.θ w * C w = C w * Jm r' s') ∧ IsFockMap B.ψ B.emb M.co A C Φ := by
  choose A hA using fun w => PositivityTheory.RL.frameEx n r s _ _ (hp.herm.sig w) (hp.herm.cartan w)
  choose C hC using fun w => PositivityTheory.RL.frameEx d r' s' _ _ (hp.skew.sig w) (hp.skew.cartan w)
  have hfr : Framed B.emb (incM F X.J) (incM F W.J) 1 Complex.I A C :=
    ⟨one_mul _, fun w => by rw [one_smul, incM_map]; exact (hA w).1, fun w => by rw [incM_map]; exact (hC w).1⟩
  obtain ⟨Φ, hΦ⟩ := hF F E σ _ _ _ r s r' s' B.ψ B.emb _ _ M.co 1 Complex.I A C hp.base.cm hp.base.std hfr
  exact ⟨A, C, Φ, hfr, fun w => (hA w).2, fun w => (hC w).2, hΦ⟩

theorem rank_tens {ι L : Type} [Fintype ι] [Finite L] : Module.rank ℂ (⨂[ℂ] _ : ι, MvPolynomial L ℂ) ≤ Cardinal.aleph0 := by
  have b := Basis.piTensorProduct fun _ : ι => MvPolynomial.basisMonomials L ℂ
  rw [← b.mk_eq_rank'']
  exact Cardinal.mk_le_aleph0

theorem polCount_of (hF : FockEx) (hV : VacLine) : PolCount := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp
  obtain ⟨A, C, Φ, h1, h2, h3, h4⟩ := exists_fock hF hp
  exact (Submodule.rank_mono (pol_le hV M hp.base.cm hp.base.std h1 h2 h3 h4)).trans
    ((rank_range_le Φ).trans rank_tens)

end PositivityTheory.ThKF.PC

end
