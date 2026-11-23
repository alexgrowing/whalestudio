import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUMOfMem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousLeviUnipotentProjStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreFunctionLocallyConstantCompactStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreIntegralIntertwinesUnipotentStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreIntegralIntertwinesLeviStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwKerOfFibIntEqZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothRightInv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeOfProductInducedIsoStatement

noncomputable section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct
namespace GlobalTheory.CompanionTheory.BZPsiPG.Hand
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {i t : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem fibInt_levi (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W)
    [MeasurableSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k))
    (f : cIndSpace (HPG k i t) (hRep τ σ)) (g' g : GL (Fin (i + t)) k) :
    fibInt μ (prodPG τ σ (levi k (i + t) g') f) g = fibInt μ f (g * g') := by
  have : fibV (prodPG τ σ (levi k (i + t) g') f) g = fibV f (g * g') := by
    funext v
    have e : uM k (i + t) (midV k i t v) * levi k (i + t) (g * g') =
        uM k (i + t) (midV k i t v) * levi k (i + t) g * levi k (i + t) g' := by
      rw [map_mul, mul_assoc]
    exact (congrArg f.1.1.1 e).symm
  exact congrArg (fun x => clT τ W (smInt μ x)) this

theorem isOpen_stab_of {G Z : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup Z] [Module ℂ Z]
    (ρ : Representation ℂ G Z) (z : Z) (S : Set G) (hS : IsOpen S) (h1 : (1 : G) ∈ S) (h : ∀ s ∈ S, ρ s z = z) :
    IsOpen {g : G | ρ g z = z} := by
  rw [isOpen_iff_mem_nhds]
  intro g hg
  have ho : IsOpen ((fun y => g⁻¹ * y) ⁻¹' S) := hS.preimage (by fun_prop)
  refine Filter.mem_of_superset (ho.mem_nhds (by simpa using h1)) fun y hy => ?_
  have e := h _ hy
  show ρ y z = z
  have : y = g * (g⁻¹ * y) := by group
  rw [this, map_mul, Module.End.mul_apply, e]
  exact hg

theorem isOpen_cInd_stab {τ : Representation ℂ (Mir k i) V} {σ : Representation ℂ (GL (Fin t) k) W}
    (f : cIndSpace (HPG k i t) (hRep τ σ)) : IsOpen {p | prodPG τ σ p f = f} := by
  have h : IsOpen {g | ind (HPG k i t) (hRep τ σ) g f.1.1 = f.1.1} := f.1.2
  have e : {p | prodPG τ σ p f = f} = {g | ind (HPG k i t) (hRep τ σ) g f.1.1 = f.1.1} := by
    ext p
    constructor
    · intro e
      exact congrArg (fun x : cIndSpace (HPG k i t) (hRep τ σ) => x.1.1) e
    · intro e
      exact Subtype.ext (Subtype.ext e)
  rw [e]
  exact h

section Map
variable (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W) (hτ : IsSmooth τ) (hσ : IsSmooth σ)
  [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure]

include hτ hσ

theorem fibInt_add (a b : cIndSpace (HPG k i t) (hRep τ σ)) (g : GL (Fin (i + t)) k) :
    fibInt μ (a + b) g = fibInt μ a g + fibInt μ b g := by
  obtain ⟨a1, a2⟩ := GlobalTheory.T.fibre_function_locally_constant_compact k i t τ σ hτ hσ a g
  obtain ⟨b1, b2⟩ := GlobalTheory.T.fibre_function_locally_constant_compact k i t τ σ hτ hσ b g
  have e : fibV (a + b) g = fibV a g + fibV b g := by
    funext v
    exact map_add (evL (uM k (i + t) (midV k i t v) * levi k (i + t) g)) a b
  have h := (GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_properties (W := V ⊗[ℂ] W) (W' := V ⊗[ℂ] W) μ).1 _ _ a1 a2 b1 b2
  exact (congrArg (fun x => clT τ W (smInt μ x)) e).trans ((congrArg (clT τ W) h).trans (map_add _ _ _))

theorem fibInt_smul (c : ℂ) (a : cIndSpace (HPG k i t) (hRep τ σ)) (g : GL (Fin (i + t)) k) :
    fibInt μ (c • a) g = c • fibInt μ a g := by
  obtain ⟨a1, a2⟩ := GlobalTheory.T.fibre_function_locally_constant_compact k i t τ σ hτ hσ a g
  have e : fibV (c • a) g = ((c • LinearMap.id : V ⊗[ℂ] W →ₗ[ℂ] V ⊗[ℂ] W)) ∘ fibV a g := by
    funext v
    exact map_smul (evL (uM k (i + t) (midV k i t v) * levi k (i + t) g)) c a
  have h := (GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_properties (W := V ⊗[ℂ] W) (W' := V ⊗[ℂ] W) μ).2.1
    (c • LinearMap.id : V ⊗[ℂ] W →ₗ[ℂ] V ⊗[ℂ] W) _ a1 a2
  exact (congrArg (fun x => clT τ W (smInt μ x)) e).trans ((congrArg (clT τ W) h).trans (map_smul (clT τ W) c _))

def phiInd (f : cIndSpace (HPG k i t) (hRep τ σ)) : indSpace (Qp k i t) (qRep τ σ) :=
  ⟨fibInt μ f, fun q g => GlobalTheory.T.fibre_integral_intertwines_unipotent k i t τ σ hτ hσ μ f q g⟩

theorem phiInd_right (f : cIndSpace (HPG k i t) (hRep τ σ)) (s : GL (Fin (i + t)) k)
    (hs : prodPG τ σ (levi k (i + t) s) f = f) :
    ind (Qp k i t) (qRep τ σ) s (phiInd τ σ hτ hσ μ f) = phiInd τ σ hτ hσ μ f := by
  apply Subtype.ext
  funext g
  exact (fibInt_levi τ σ μ f s g).symm.trans (congrArg (fun x => fibInt μ x g) hs)

theorem phiInd_mem (f : cIndSpace (HPG k i t) (hRep τ σ)) :
    phiInd τ σ hτ hσ μ f ∈ smoothPart (ind (Qp k i t) (qRep τ σ)) := by
  have h : IsOpen {g | ind (Qp k i t) (qRep τ σ) g (phiInd τ σ hτ hσ μ f) = phiInd τ σ hτ hσ μ f} :=
    isOpen_stab_of (ind (Qp k i t) (qRep τ σ)) _
      (levi k (i + t) ⁻¹' {p | prodPG τ σ p f = f})
      ((isOpen_cInd_stab f).preimage (GlobalTheory.T.continuous_levi_unipotent_proj k _).1)
      (by
        have h0 : levi k (i + t) (1 : GL (Fin (i + t)) k) = 1 := (levi k (i + t)).map_one
        have h1 : prodPG τ σ (1 : Mir k (i + t)) = 1 := (prodPG τ σ).map_one
        exact (congrArg (fun x => prodPG τ σ x f) h0).trans (LinearMap.congr_fun h1 f))
      (fun s hs => phiInd_right τ σ hτ hσ μ f s hs)
  exact h

def phiFun (f : cIndSpace (HPG k i t) (hRep τ σ)) : smoothPart (ind (Qp k i t) (qRep τ σ)) :=
  ⟨phiInd τ σ hτ hσ μ f, phiInd_mem τ σ hτ hσ μ f⟩

def phiLin : cIndSpace (HPG k i t) (hRep τ σ) →ₗ[ℂ] smoothPart (ind (Qp k i t) (qRep τ σ)) where
  toFun := phiFun τ σ hτ hσ μ
  map_add' a b := Subtype.ext (Subtype.ext (funext fun g => fibInt_add τ σ hτ hσ μ a b g))
  map_smul' c a := Subtype.ext (Subtype.ext (funext fun g => fibInt_smul τ σ hτ hσ μ c a g))

theorem phiLin_apply (f : cIndSpace (HPG k i t) (hRep τ σ)) (g : GL (Fin (i + t)) k) :
    (phiLin τ σ hτ hσ μ f).1.1 g = fibInt μ f g := rfl

theorem twKer_le_ker : twKer (prodPG τ σ) (MirUin k (i + t)) 1 ≤ LinearMap.ker (phiLin τ σ hτ hσ μ) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨u, w, rfl⟩
  have e : phiLin τ σ hτ hσ μ (prodPG τ σ (u : Mir k (i + t)) w) = phiLin τ σ hτ hσ μ w :=
    Subtype.ext (Subtype.ext (funext fun g => GlobalTheory.T.fibre_integral_intertwines_levi k i t τ σ hτ hσ μ w (u : Mir k (i + t)) u.2 g))
  have e2 : (((1 : MirUin k (i + t) →* ℂˣ) u : ℂˣ) : ℂ) • w = w := by simp
  show phiLin τ σ hτ hσ μ _ = 0
  exact (congrArg (fun x => phiLin τ σ hτ hσ μ (prodPG τ σ (u : Mir k (i + t)) w - x)) e2).trans
    ((map_sub (phiLin τ σ hτ hσ μ) _ _).trans (sub_eq_zero.2 e))

theorem ker_le_twKer : LinearMap.ker (phiLin τ σ hτ hσ μ) ≤ twKer (prodPG τ σ) (MirUin k (i + t)) 1 := by
  intro f hf
  have h : phiLin τ σ hτ hσ μ f = 0 := hf
  exact GlobalTheory.CompanionTheory.BZPsiPG.FibKer.mem_twKer_of_fibInt_eq_zero k i t τ σ hτ hσ μ f fun g => congrFun (congrArg (fun x : smoothPart (ind (Qp k i t) (qRep τ σ)) => x.1.1) h) g

theorem phiLin_surj : Function.Surjective (phiLin τ σ hτ hσ μ) := by
  intro G
  have h := GlobalTheory.CompanionTheory.BZPsiPG.exists_fibInt_eq k i t τ σ hτ hσ μ G
  refine h.imp fun f hf => ?_
  have e : (phiLin τ σ hτ hσ μ f).1.1 = G.1.1 := funext fun g => (phiLin_apply τ σ hτ hσ μ f g).trans (hf g)
  exact Subtype.ext (Subtype.ext e)

theorem phiLin_levi (f : cIndSpace (HPG k i t) (hRep τ σ)) (g : GL (Fin (i + t)) k) :
    phiLin τ σ hτ hσ μ (prodPG τ σ (levi k (i + t) g) f) = smInd (Qp k i t) (qRep τ σ) g (phiLin τ σ hτ hσ μ f) :=
  Subtype.ext (Subtype.ext (funext fun x => fibInt_levi τ σ μ f g x))

end Map

theorem twAct_equiv_of_map {G M Z Z' : Type} [Group G] [Group M] [AddCommGroup Z] [Module ℂ Z] [AddCommGroup Z'] [Module ℂ Z']
    (ρ : Representation ℂ G Z) (N : Subgroup G) (θ : N →* ℂˣ) (s : M →* G)
    (hs : ∀ (m : M) (n : N), ∃ h : s m * (n : G) * (s m)⁻¹ ∈ N, θ ⟨_, h⟩ = θ n) (ρ' : Representation ℂ M Z')
    (Φ : Z →ₗ[ℂ] Z') (hk : LinearMap.ker Φ = twKer ρ N θ) (hsurj : Function.Surjective Φ)
    (hint : ∀ m z, Φ (ρ (s m) z) = ρ' m (Φ z)) :
    Nonempty ((twAct ρ N θ s hs).Equiv ρ') := by
  let e : TwJacquet ρ N θ ≃ₗ[ℂ] Z' :=
    (Submodule.quotEquivOfEq _ _ hk.symm).trans (Φ.quotKerEquivOfSurjective hsurj)
  refine ⟨.mk e fun g => ?_⟩
  apply LinearMap.ext
  intro x
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact hint g f

theorem core (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W) (hτ : IsSmooth τ) (hσ : IsSmooth σ) :
    Nonempty ((psiMinus k (prodPG τ σ)).Equiv (smInd (Qp k i t) (qRep τ σ))) := by
  letI : MeasurableSpace (Fin t → k) := borel _
  haveI : BorelSpace (Fin t → k) := ⟨rfl⟩
  exact twAct_equiv_of_map (prodPG τ σ) (MirUin k (i + t)) 1 (levi k (i + t)) (levi_normalises (i + t))
    (smInd (Qp k i t) (qRep τ σ)) (phiLin τ σ hτ hσ (MeasureTheory.Measure.addHaar : MeasureTheory.Measure (Fin t → k)))
    (le_antisymm (ker_le_twKer τ σ hτ hσ _) (twKer_le_ker τ σ hτ hσ _))
    (phiLin_surj τ σ hτ hσ _) (fun g f => phiLin_levi τ σ hτ hσ _ f g)

theorem isSmoothChar_dpow (n : ℕ) (s : ℝ) : IsSmoothChar (dpow (k := k) n s) :=
  (isSmoothChar_of_isUnram (isUnram_absPow k _)).detChar

theorem isSmoothChar_dpowM (n : ℕ) (s : ℝ) : IsSmoothChar (dpowM (k := k) n s) :=
  (isSmoothChar_dpow (n + 1) s).comp _ continuous_subtype_val

theorem psiPG : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], PsiPG k := by
  intro k _ _ _ _ i t τ σ hτ hσ
  exact GlobalTheory.T.derivative_of_product_induced_iso k i t τ σ hτ hσ
    (core _ _ (isSmooth_twist hτ (isSmoothChar_dpowM _ _)) (isSmooth_twist hσ (isSmoothChar_dpow _ _)))

end GlobalTheory.CompanionTheory.BZPsiPG.Hand
end
