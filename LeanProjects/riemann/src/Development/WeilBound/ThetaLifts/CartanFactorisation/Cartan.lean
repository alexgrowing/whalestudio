import Development.WeilBound.ThetaLifts.CartanFactorisation.CartanConj
import Development.WeilBound.ThetaLifts.CartanFactorisation.CartanA
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.EvIHalfTrace
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLActs

noncomputable section

namespace PositivityTheory.ThKF

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.RealLift

theorem cartan_conjugacy_holds : CartanConj := fun _ _ _ _ _ _ _ _ B _ W W₂ _ _ hB h1 h2 =>
  Cart.exists_conj hB.cm B.emb W Complex.I Complex.I_ne_zero W₂.θ h1.sig h1.cartan h2.cartan

namespace Cart

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}

theorem at_act {u : Matrix (Fin n) (Fin d) (AE F E)} (hu : At (evI F) u) (a : Matrix (Fin n) (Fin n) (AE F E))
    (b : Matrix (Fin d) (Fin d) (AE F E)) : At (evI F) (a * u * bᵀ) := fun c hc => by
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, hu c hc, Matrix.mul_zero, Matrix.zero_mul]

theorem pol_le {X X₂ : Spc F E n} {W W₂ : Spc F E d} (M : Model σ X W) (M₂ : Model σ X₂ W₂) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (D : Matrix (Fin n) (Fin d) (AE F E) → SInf F (Fin n × Fin d) → SInf F (Fin n × Fin d))
    (hD : ∀ u, At (evI F) u → ∀ f f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ u) f f₁ ↔ f₁ = D u f)
    (hD₂ : ∀ u, At (evI F) u → ∀ f f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (M₂.heisLine ψ u) f f₁ ↔ f₁ = D u f)
    (T : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d)) (a : Matrix (Fin n) (Fin n) (AE F E))
    (b : Matrix (Fin d) (Fin d) (AE F E)) (hT : ∀ u, At (evI F) u → ∀ f, T (D (a * u * bᵀ) f) = D u (T f))
    (hsurj : ∀ u, At (evI F) u → ∃ u₀ : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u₀ ∧ a * u₀ * bᵀ = u)
    (ha : ∀ w, a.map (piInf (τ w)) * X.θ w = X₂.θ w * a.map (piInf (τ w)))
    (hb : ∀ w, b.map (piInf (τ w)) * W.θ w = W₂.θ w * b.map (piInf (τ w))) :
    (M₂.Pol ψ τ).map T ≤ M.Pol ψ τ := by
  rw [Submodule.map_le_iff_le_comap]
  refine sInf_le ⟨fun f₀ ⟨ε, hε⟩ => ?_, fun u hu f hf f₁ h₁ => ?_⟩
  · refine Submodule.mem_sInf.2 fun N hN => hN.1 _ ⟨ε, fun u u' hu hu' e f f' hf hf' => ?_⟩
    rw [(hD u hu _ _).1 hf, (hD u' hu' _ _).1 hf', ← hT u hu, ← hT u' hu', ← map_smul]
    refine congrArg T (hε _ _ (at_act hu a b) (at_act hu' a b) (fun w => ?_) _ _ ((hD₂ _ (at_act hu a b) _ _).2 rfl)
      ((hD₂ _ (at_act hu' a b) _ _).2 rfl))
    simp only [Matrix.map_mul, Matrix.transpose_map]
    rw [e w, Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    calc a.map (piInf (τ w)) * (X.θ w * u.map (piInf (τ w)) * (W.θ w)ᵀ) * (b.map (piInf (τ w)))ᵀ
        = (a.map (piInf (τ w)) * X.θ w) * u.map (piInf (τ w)) * (b.map (piInf (τ w)) * W.θ w)ᵀ := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = _ := by rw [ha, hb]; simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  · obtain ⟨u₀, h0, rfl⟩ := hsurj u hu
    refine Submodule.mem_sInf.2 fun N hN => hN.2 u₀ h0 (T f) (Submodule.mem_sInf.1 hf N hN) _ ?_
    rw [(hD₂ _ hu _ _).1 h₁, hT u₀ h0]
    exact (hD u₀ h0 _ _).2 rfl

variable {X : Spc F E n} {W : Spc F E d} {B : Base F E} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ}

theorem rho_zero (ψ : AddChar (AF F) ℂ) (z) : M.co.rho ψ z 0 = 0 := by
  funext x
  simp [Darboux.rho, schr]

theorem intertw (hp : IsPair B M χX χW om r s r' s')
    (D : Matrix (Fin n) (Fin d) (AE F E) → (SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d)))
    (hD : ∀ u, At (evI F) u → ∀ f, SD (fun t => M.co.rho B.ψ (realAd F t • u)) f (D u f)) {x T} (hT : IsArchOp om x T)
    (u) (hu : At (evI F) u) (f) : T (D u f) = D (mat x.1 * u * (mat x.2)ᵀ) (T f) := by
  have hs := hp.weil.isUSplitting
  refine (PositivityTheory.RL.actsLaws F _ (T f) _ _).2.2.2.2 _ (fun g hg l hl => ?_) (hD _ (at_act hu _ _) (T f))
  have h1 := hD u hu f g hg _ (hs.adm x l hl)
  simp only [LinearMap.comp_apply] at h1
  rw [hT.1 _ g hg] at h1
  refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  show l _ = l _
  rw [hs.impl x _ _ (Submodule.subset_span ⟨f, g, hg, rfl⟩), hT.1 f g hg]
  congr 2
  show _ = mat x.1 * (realAd F t • u) * (mat x.2)ᵀ
  rw [Matrix.mul_smul, Matrix.smul_mul]

end Cart

open Cart in
theorem cartanMove_of (hO : ArchOp) : CartanMove := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp X₂ W₂ M₂ hco hp₂ h hh eh
  obtain ⟨g, hg, eg⟩ := Cart.exists_conj (σ := σ) hp.base.cm B.emb X 1 one_ne_zero X₂.θ
    (fun w => by rw [one_smul]; exact hp.herm.sig w) (fun w => by rw [one_smul]; exact hp.herm.cartan w)
    fun w => by rw [one_smul]; exact hp₂.herm.cartan w
  refine ⟨g, hg, eg, fun T hT => ?_⟩
  obtain ⟨D, hD⟩ := PositivityTheory.RL.derEx F E σ _ _ _ B.ψ _ _ M.co hp.base.std
  have hD1 : ∀ u, At (evI F) u → ∀ f f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine B.ψ u) f f₁ ↔ f₁ = D u f :=
    fun u hu f f₁ =>
      have a := (PositivityTheory.RL.actsLaws F _ f (D u f) f).1 (M.heisLine B.ψ u) (fun _ => rho_zero _ _) (hD u hu f).1
      ⟨fun e => (PositivityTheory.RL.actsLaws F _ f f₁ _).2.2.1 _ e a, fun e => e ▸ a⟩
  have hD2 : ∀ u, At (evI F) u → ∀ f f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (M₂.heisLine B.ψ u) f f₁ ↔ f₁ = D u f := by
    have : ∀ u, M₂.heisLine B.ψ u = M.heisLine B.ψ u := fun u => funext fun t => by
      unfold Model.heisLine; rw [hco]; rfl
    simp only [this]
    exact hD1
  have mm : ∀ {m : ℕ} {J : Matrix (Fin m) (Fin m) E} (x : UA σ J), mat x * mat x⁻¹ = 1 ∧ mat x⁻¹ * mat x = 1 :=
    fun x => ⟨Units.mul_inv x.1, Units.inv_mul x.1⟩
  have inv : ∀ {m : ℕ} {Y : Spc F E m} (x : UA σ Y.J), x ∈ UAt σ Y (evI F) → x⁻¹ ∈ UAt σ Y (evI F) := fun x hx c hc => by
    have : mat x⁻¹ - 1 = -(mat x⁻¹ * (mat x - 1)) := by rw [Matrix.mul_sub, (mm x).2, Matrix.mul_one, neg_sub]
    rw [this, smul_neg, ← Matrix.mul_smul, hx c hc, Matrix.mul_zero, neg_zero]
  have can : ∀ (x : UA σ X.J) (y : UA σ W.J) (u : Matrix (Fin n) (Fin d) (AE F E)),
      mat x * (mat x⁻¹ * u * (mat y⁻¹)ᵀ) * (mat y)ᵀ = u := fun x y u => by
    calc _ = (mat x * mat x⁻¹) * u * (mat y * mat y⁻¹)ᵀ := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = u := by rw [(mm x).1, (mm y).1, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  have flip : ∀ {m : ℕ} {J : Matrix (Fin m) (Fin m) E} (x : UA σ J) w (θ θ₂ : Matrix (Fin m) (Fin m) ℂ),
      (mat x).map (piInf (B.emb w)) * θ₂ = θ * (mat x).map (piInf (B.emb w)) →
      (mat x⁻¹).map (piInf (B.emb w)) * θ = θ₂ * (mat x⁻¹).map (piInf (B.emb w)) := fun x w θ θ₂ e => by
    have e1 : (mat x).map (piInf (B.emb w)) * (mat x⁻¹).map (piInf (B.emb w)) = 1 := by
      rw [← Matrix.map_mul, (mm x).1, Matrix.map_one _ (map_zero _) (map_one _)]
    have e2 := mul_eq_one_comm.1 e1
    calc _ = (mat x⁻¹).map (piInf (B.emb w)) * (θ * (mat x).map (piInf (B.emb w))) * (mat x⁻¹).map (piInf (B.emb w)) := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, e1, Matrix.mul_one]
      _ = _ := by rw [← e, ← Matrix.mul_assoc, e2, Matrix.one_mul]
  obtain ⟨T', hT', -⟩ := hO F E σ B n d X W M χX χW om r s r' s' hp g⁻¹ (inv g hg) h⁻¹ (inv h hh)
  have hD' := fun u hu f => (hD u hu f).1
  have l1 := pol_le M M₂ B.ψ B.emb (fun u f => D u f) hD1 hD2 (T : _ →ₗ[ℂ] _) (mat g⁻¹) (mat h⁻¹)
    (fun u hu f => by
      have := intertw hp D hD' hT _ (at_act hu (mat g⁻¹) (mat h⁻¹)) f
      rwa [can] at this)
    (fun u hu => ⟨_, at_act hu (mat g) (mat h), by simpa using can g⁻¹ h⁻¹ u⟩)
    (fun w => flip g w _ _ (eg w)) fun w => flip h w _ _ (eh w)
  have l2 := pol_le M₂ M B.ψ B.emb (fun u f => D u f) hD2 hD1 (T' : _ →ₗ[ℂ] _) (mat g) (mat h)
    (fun u hu f => by
      have := intertw hp D hD' hT' _ (at_act hu (mat g) (mat h)) f
      have c := can g⁻¹ h⁻¹ u
      rw [inv_inv, inv_inv] at c
      rwa [c] at this)
    (fun u hu => ⟨_, at_act hu (mat g⁻¹) (mat h⁻¹), can g h u⟩) eg eh
  refine le_antisymm l1 fun f hf => ⟨T' f, l2 ⟨f, hf, rfl⟩, ?_⟩
  have a1 : SA (om 1) f (T (T' f)) := fun φ hφ => by
    rw [← hT.1 _ φ hφ, ← hT'.1 _ φ hφ, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_inv_cancel]
    rfl
  have a2 : SA (om 1) f f := fun φ _ => by rw [map_one]; rfl
  exact (PositivityTheory.RL.actsLaws F _ f _ _).2.2.2.1 _ ((PositivityTheory.RL.actsLaws F _ f _ f).2.1 _ (map_zero _) a1)
    ((PositivityTheory.RL.actsLaws F _ f _ f).2.1 _ (map_zero _) a2)

end PositivityTheory.ThKF

end
