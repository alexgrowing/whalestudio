import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChosenSeries

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Chain.RealIt.TensorGlob

theorem der_span {E : Type*} [AddCommGroup E] [Module ℂ E] {s : Set E} (hs : Submodule.span ℂ s = ⊤)
    (f : ℝ → E →ₗ[ℂ] ℂ) (g : E →ₗ[ℂ] ℂ) (h : ∀ e ∈ s, HasDerivAt (fun t => f t e) (g e) 0) (e : E) :
    HasDerivAt (fun t => f t e) (g e) 0 := by
  have he : e ∈ Submodule.span ℂ s := hs ▸ Submodule.mem_top
  induction he using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero =>
    have h0 : (fun t => f t 0) = fun _ => (0 : ℂ) := funext fun t => map_zero (f t)
    rw [h0, map_zero]
    exact hasDerivAt_const _ _
  | add x y _ _ hx hy =>
    have h0 : (fun t => f t (x + y)) = fun t => f t x + f t y := funext fun t => map_add (f t) x y
    rw [h0, map_add]
    exact hx.add hy
  | smul a x _ hx =>
    have h0 : (fun t => f t (a • x)) = fun t => a * f t x := funext fun t => map_smul (f t) a x
    rw [h0, map_smul, smul_eq_mul]
    exact hx.const_mul a

theorem der_span₂ {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    {s : Set E} (hs : Submodule.span ℂ s = ⊤) {s' : Set F} (hs' : Submodule.span ℂ s' = ⊤)
    (f : ℝ → E →ₗ[ℂ] F →ₗ[ℂ] ℂ) (g : E →ₗ[ℂ] F →ₗ[ℂ] ℂ)
    (h : ∀ e ∈ s, ∀ x ∈ s', HasDerivAt (fun t => f t e x) (g e x) 0) (e : E) (x : F) :
    HasDerivAt (fun t => f t e x) (g e x) 0 := by
  have h1 : ∀ x ∈ s', ∀ e', HasDerivAt (fun t => f t e' x) (g e' x) 0 := fun x hx e' =>
    der_span hs (fun t => (f t).flip x) (g.flip x) (fun e'' he'' => h e'' he'' x hx) e'
  exact der_span hs' (fun t => f t e) (g e) (fun x hx => h1 x hx e) x

variable {D : D7}

open Classical in
theorem glue_update {a b : ℕ} (P : D.what₂.Tau → LPol b a) (τ : D.what₂.Tau) (p : LPol b a) :
    glue (Function.update P τ p) = MvPolynomial.rename (fun s => (τ, s)) p *
      ∏ ρ ∈ Finset.univ.erase τ, MvPolynomial.rename (fun s => (ρ, s)) (P ρ) := by
  unfold glue
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ)]
  congr 1
  · simp
  · exact Finset.prod_congr rfl fun ρ hρ => by simp [Finset.ne_of_mem_erase hρ]

open Classical in
theorem glue_update_add_smul {a b : ℕ} (P : D.what₂.Tau → LPol b a) (τ : D.what₂.Tau) (p : LPol b a) (c : ℂ) :
    glue (Function.update P τ p) + c • glue P = glue (Function.update P τ (p + c • P τ)) := by
  have h0 : glue P = glue (Function.update P τ (P τ)) := by rw [Function.update_eq_self]
  rw [h0, glue_update, glue_update, glue_update, map_add, map_smul, add_mul, smul_mul_assoc]

variable {V : HSp D} {S : D.what₂.Tau → SPar}

theorem ellT_tprod' (M : DSModel V S) (w v : ∀ τ, M.H τ) :
    ellT M w (PiTensorProduct.tprod ℂ v) = ∏ τ, ⟪w τ, v τ⟫_ℂ := by
  unfold ellT
  rw [PiTensorProduct.lift.tprod]
  simp

open Classical in
theorem ellT_update (M : DSModel V S) (w v : ∀ τ, M.H τ) (τ : D.what₂.Tau) (u : M.H τ) :
    ellT M w (PiTensorProduct.tprod ℂ (Function.update v τ u)) =
      ⟪w τ, u⟫_ℂ * ∏ ρ ∈ Finset.univ.erase τ, ⟪w ρ, v ρ⟫_ℂ := by
  rw [ellT_tprod', ← Finset.mul_prod_erase _ _ (Finset.mem_univ τ)]
  congr 1
  · simp
  · exact Finset.prod_congr rfl fun ρ hρ => by simp [Finset.ne_of_mem_erase hρ]

open Classical in
theorem actT_tprod (M : DSModel V S) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (v : ∀ τ, M.H τ) :
    actT M τ g (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ (Function.update v τ (M.rep τ g (v τ))) := by
  unfold actT
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext ρ
  by_cases hρ : ρ = τ
  · subst hρ; simp
  · simp [Function.update_of_ne hρ]

theorem der_inner {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {c : ℝ → H} {y : H}
    (h : HasDerivAt c y 0) (w : H) (k : ℂ) : HasDerivAt (fun t => ⟪w, c t⟫_ℂ * k) (⟪w, y⟫_ℂ * k) 0 := by
  have h1 : HasDerivAt (fun t => ⟪w, c t⟫_ℂ) ⟪w, y⟫_ℂ 0 := by
    simpa [Function.comp_def] using ((innerSL ℂ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
  exact h1.mul_const k

open Classical in

theorem exists_globIt : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (aS aT : D.what₂.Tau → ℚ) (A : ∀ τ, LPol W.rank V.rank →ₗ[ℂ] M'.H τ →ₗ[ℂ] M.H τ), GlobalTheory.IndefiniteRowSideFullHecke.ContractionTensorModels.ContrTensor → GlueLaw D V.rank W.rank → (∀ τ, LocIt M M' τ (aS τ) (aT τ) (A τ)) → ∃ It I, GlobIt M M' aS aT It I := by
  intro D V W S S' M M' aS aT A hC hG hL
  have hs := hG.1
  have hs' : Submodule.span ℂ (Set.range (PiTensorProduct.tprod ℂ : (∀ τ, M'.H τ) → ⨂[ℂ] τ, M'.H τ)) = ⊤ :=
    PiTensorProduct.span_tprod_eq_top
  obtain ⟨I, hI, -⟩ := hC D.what₂.Tau (fun _ => Fin W.rank × Fin V.rank) (FVar D W.rank V.rank)
    (Equiv.sigmaEquivProd D.what₂.Tau (Fin W.rank × Fin V.rank) :
      (Σ _ : D.what₂.Tau, Fin W.rank × Fin V.rank) ≃ FVar D W.rank V.rank)
    (fun τ => M'.H τ) (fun τ => M.H τ) A
  have hIg : ∀ (P : D.what₂.Tau → LPol W.rank V.rank) (v : ∀ τ, M'.H τ),
      I (glue P) (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ fun ρ => A ρ (P ρ) (v ρ) :=
    fun P v => hI P v
  let Itl : ∀ τ, LPol W.rank V.rank →ₗ[ℂ] M'.sm τ →ₗ[ℂ] M.sm τ := fun τ =>
    LinearMap.mk₂ ℂ (fun P y => (⟨A τ P (y : M'.H τ), (hL τ).sm P (y : M'.H τ)⟩ : M.sm τ))
      (fun P Q y => Subtype.ext (by simp)) (fun c P y => Subtype.ext (by simp))
      (fun P y z => Subtype.ext (by simp)) (fun c P y => Subtype.ext (by simp))
  have hItl : ∀ τ P y, ((Itl τ P y : M.sm τ) : M.H τ) = A τ P (y : M'.H τ) := fun _ _ _ => rfl
  obtain ⟨It, hIt, hItne⟩ := hC D.what₂.Tau (fun _ => Fin W.rank × Fin V.rank) (FVar D W.rank V.rank)
    (Equiv.sigmaEquivProd D.what₂.Tau (Fin W.rank × Fin V.rank) :
      (Σ _ : D.what₂.Tau, Fin W.rank × Fin V.rank) ≃ FVar D W.rank V.rank)
    (fun τ => ↥(M'.sm τ)) (fun τ => ↥(M.sm τ)) Itl
  have hItg : ∀ (P : D.what₂.Tau → LPol W.rank V.rank) (v : ∀ τ, M'.sm τ),
      It (glue P) (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ fun ρ => Itl ρ (P ρ) (v ρ) :=
    fun P v => hIt P v
  have hupdP : ∀ (P : D.what₂.Tau → LPol W.rank V.rank) (τ : D.what₂.Tau) (Q : LPol W.rank V.rank)
      (v : ∀ τ, M'.H τ), (PiTensorProduct.tprod ℂ fun ρ => A ρ (Function.update P τ Q ρ) (v ρ)) =
        PiTensorProduct.tprod ℂ (Function.update (fun ρ => A ρ (P ρ) (v ρ)) τ (A τ Q (v τ))) := by
    intro P τ Q v
    congr 1
    funext ρ
    by_cases hρ : ρ = τ
    · subst hρ; simp
    · simp [Function.update_of_ne hρ]
  have hupdV : ∀ (P : D.what₂.Tau → LPol W.rank V.rank) (τ : D.what₂.Tau) (v : ∀ τ, M'.H τ) (y : M'.H τ),
      (PiTensorProduct.tprod ℂ fun ρ => A ρ (P ρ) (Function.update v τ y ρ)) =
        PiTensorProduct.tprod ℂ (Function.update (fun ρ => A ρ (P ρ) (v ρ)) τ (A τ (P τ) y)) := by
    intro P τ v y
    congr 1
    funext ρ
    by_cases hρ : ρ = τ
    · subst hρ; simp
    · simp [Function.update_of_ne hρ]
  refine ⟨It, I, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro φ v
    have h1 : It.compr₂ (inclT M) = I.compl₂ (inclT M') := by
      refine LinearMap.ext_on hs ?_
      rintro _ ⟨P, rfl⟩
      refine PiTensorProduct.ext (MultilinearMap.ext fun v => ?_)
      simp only [LinearMap.compMultilinearMap_apply, LinearMap.compr₂_apply, LinearMap.compl₂_apply, hItg]
      unfold inclT
      simp only [PiTensorProduct.map_tprod, Submodule.subtype_apply, hItl, hIg]
    exact DFunLike.congr_fun (DFunLike.congr_fun h1 φ) v
  · apply hItne
    intro τ h0
    obtain ⟨P, y, hy, hne⟩ := (hL τ).ne
    apply hne
    have h2 := congrArg (fun B : LPol W.rank V.rank →ₗ[ℂ] M'.sm τ →ₗ[ℂ] M.sm τ =>
      ((B P ⟨y, hy⟩ : M.sm τ) : M.H τ)) h0
    simpa [hItl] using h2
  · intro φ w
    have hφ : φ ∈ Submodule.span ℂ (Set.range (glue : (D.what₂.Tau → LPol W.rank V.rank) → PolF D W.rank V.rank)) :=
      hs ▸ Submodule.mem_top
    induction hφ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨P, rfl⟩ := hx
      choose w' hw' using fun τ => (hL τ).adj (P τ) (w τ)
      refine Submodule.subset_span ⟨w', ?_⟩
      refine PiTensorProduct.ext (MultilinearMap.ext fun v => ?_)
      simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, hIg, ellT_tprod', hw']
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add, LinearMap.comp_add]
      exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [map_smul, LinearMap.comp_smul]
      exact Submodule.smul_mem _ a hx
  · intro τ X hX φ x w
    have key := der_span₂ hs hs' (fun t => I.compr₂ (ellT M w ∘ₗ actT M τ (NormedSpace.exp (t • X))))
      ((I ∘ₗ srcOp M M' τ (aT τ) X).compr₂ (ellT M w)) ?hyp φ x
    · simpa only [LinearMap.compr₂_apply, LinearMap.comp_apply] using key
    case hyp =>
      rintro _ ⟨P, rfl⟩ _ ⟨v, rfl⟩
      simp only [LinearMap.compr₂_apply, LinearMap.comp_apply, srcOp, LinearMap.add_apply,
        LinearMap.smul_apply, Module.End.one_apply, (hG.2 τ (M.ε τ) (M'.ε τ) P).1, glue_update_add_smul,
        hIg, hupdP, actT_tprod, ellT_update]
      rw [neg_smul, ← sub_eq_add_neg]
      exact der_inner ((hL τ).src X hX (P τ) (v τ)) (w τ) _
  · intro τ Y hY φ x w
    have key := der_span₂ hs hs'
      (fun t => (I.compl₂ (actT M' τ (NormedSpace.exp (t • Y)))).compr₂ (ellT M w))
      (-((I ∘ₗ tgtOp M M' τ (aS τ) Y).compr₂ (ellT M w))) ?hyp φ x
    · simpa only [LinearMap.compr₂_apply, LinearMap.compl₂_apply, LinearMap.comp_apply,
        LinearMap.neg_apply] using key
    case hyp =>
      rintro _ ⟨P, rfl⟩ _ ⟨v, rfl⟩
      simp only [LinearMap.compr₂_apply, LinearMap.compl₂_apply, LinearMap.comp_apply, LinearMap.neg_apply,
        tgtOp, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
        (hG.2 τ (M.ε τ) (M'.ε τ) P).2, glue_update_add_smul, hIg, hupdP, hupdV, actT_tprod, ellT_update]
      rw [← neg_mul, ← inner_neg_right]
      exact der_inner ((hL τ).tgt Y hY (P τ) (v τ)) (w τ) _

end GlobalTheory.Chain.RealIt.TensorGlob

end
