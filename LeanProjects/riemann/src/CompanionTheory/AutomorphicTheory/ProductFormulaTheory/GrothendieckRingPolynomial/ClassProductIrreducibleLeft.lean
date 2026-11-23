import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.ProdList
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicProductHasFiniteLengthGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import Mathlib
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ZelevinskyClassification.ZelevinskySegments.SegDefs
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SocleOfMultiplicityOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentRepSplitIntertwiner
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.GlobalTheory.BernsteinZelevinskyFiniteness

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false

namespace CompanionTheory.Groth

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Bil

variable {ι M : Type*} [AddCommGroup M] (f : ι → ι → M)

def bil (a b : ι →₀ ℤ) : M := a.sum fun x m => b.sum fun y n => (m * n) • f x y

theorem bil_zero_left (b : ι →₀ ℤ) : bil f 0 b = 0 := Finsupp.sum_zero_index

theorem bil_zero_right (a : ι →₀ ℤ) : bil f a 0 = 0 := by
  unfold bil
  simp only [Finsupp.sum_zero_index]
  exact Finset.sum_const_zero

theorem bil_add_left (a a' b : ι →₀ ℤ) : bil f (a + a') b = bil f a b + bil f a' b := by
  unfold bil
  rw [Finsupp.sum_add_index']
  · intro x
    simp only [zero_mul, zero_smul]
    exact Finset.sum_const_zero
  · intro x m₁ m₂
    simp only [add_mul, add_smul, Finsupp.sum_add]

theorem bil_add_right (a b b' : ι →₀ ℤ) : bil f a (b + b') = bil f a b + bil f a b' := by
  unfold bil
  rw [← Finsupp.sum_add]
  refine Finsupp.sum_congr fun x _ => ?_
  rw [Finsupp.sum_add_index']
  · intro y
    simp only [mul_zero, zero_smul]
  · intro y n₁ n₂
    rw [mul_add, add_smul]

theorem bil_single (x y : ι) : bil f (Finsupp.single x 1) (Finsupp.single y 1) = f x y := by
  unfold bil
  rw [Finsupp.sum_single_index, Finsupp.sum_single_index, mul_one, one_smul]
  · rw [mul_zero, zero_smul]
  · simp only [zero_mul, zero_smul]
    exact Finset.sum_const_zero

end Bil

theorem mulR_eq_bil (a b : GrothGL k) :
    mulR a b = bil (fun x y : IrrGL k => cl0 (prod₂ (IrrGL.rep x) (IrrGL.rep y))) a b := rfl

theorem mulR_zero_left (b : GrothGL k) : mulR 0 b = 0 :=
  (mulR_eq_bil _ _).trans (bil_zero_left _ b)

theorem mulR_zero_right (a : GrothGL k) : mulR a 0 = 0 :=
  (mulR_eq_bil _ _).trans (bil_zero_right _ a)

theorem mulR_add_left (a a' b : GrothGL k) : mulR (a + a') b = mulR a b + mulR a' b :=
  (mulR_eq_bil _ _).trans ((bil_add_left _ a a' b).trans
    (congrArg₂ (· + ·) (mulR_eq_bil a b).symm (mulR_eq_bil a' b).symm))

theorem mulR_add_right (a b b' : GrothGL k) : mulR a (b + b') = mulR a b + mulR a b' :=
  (mulR_eq_bil _ _).trans ((bil_add_right _ a b b').trans
    (congrArg₂ (· + ·) (mulR_eq_bil a b).symm (mulR_eq_bil a b').symm))

theorem mulR_sg_sg (x y : IrrGL k) : mulR (sg x) (sg y) = cl0 (prod₂ (IrrGL.rep x) (IrrGL.rep y)) :=
  (mulR_eq_bil _ _).trans (bil_single _ x y)

section Cl0

variable {N : ℕ} {U V W : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

theorem class_eq_finite_length_class (π : Representation ℂ (GL (Fin N) k) V) (h : HasFiniteLength π) : cl0 π = clsGL π h := by
  unfold cl0
  exact dif_pos h

theorem class_irreducible_basis (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π) (hi : π.IsIrreducible) :
    cl0 π = sg (IrrGL.of π hs hi) := by
  have h := (⟨V, π, hs, hi⟩ : IrrRep (GL (Fin N) k)).hasFiniteLength
  rw [class_eq_finite_length_class π h]
  exact clsGL_irr ⟨V, π, hs, hi⟩ h

theorem class_congr_equiv {π : Representation ℂ (GL (Fin N) k) V} {τ : Representation ℂ (GL (Fin N) k) W}
    (φ : π.Equiv τ) : cl0 π = cl0 τ := by
  by_cases h : HasFiniteLength π
  · rw [class_eq_finite_length_class π h, class_eq_finite_length_class τ (h.of_equiv φ), clsGL_congr φ]
  · have h' : ¬ HasFiniteLength τ := fun h' => h (h'.of_equiv φ.symm)
    unfold cl0
    rw [dif_neg h, dif_neg h']

theorem class_subsingleton [Subsingleton V] (π : Representation ℂ (GL (Fin N) k) V) : cl0 π = 0 := by
  rw [class_eq_finite_length_class π (GlobalTheory.ProdLength.hasFiniteLength_of_subsingleton π), clsGL]
  have : cls π (GlobalTheory.ProdLength.hasFiniteLength_of_subsingleton π) = 0 := by
    ext c
    rw [cls_apply, jhMult_of_subsingleton c.rep.irr]
    simp
  rw [this, Finsupp.mapDomain_zero]

theorem class_eq_zero_of_trivial_space {π : Representation ℂ (GL (Fin N) k) V} (h : ∀ v : V, v = 0) : cl0 π = 0 := by
  have : Subsingleton V := ⟨fun a b => (h a).trans (h b).symm⟩
  exact class_subsingleton π

theorem class_additive_exact {α : Representation ℂ (GL (Fin N) k) U} {β : Representation ℂ (GL (Fin N) k) V}
    {γ : Representation ℂ (GL (Fin N) k) W} (i : α.IntertwiningMap β) (q : β.IntertwiningMap γ)
    (hi : Function.Injective i) (hq : Function.Surjective q) (he : Function.Exact i q)
    (h : HasFiniteLength β) : cl0 β = cl0 α + cl0 γ := by
  have hα : HasFiniteLength α := GlobalTheory.ProdLength.hasFiniteLength_of_injective i hi h
  have hγ : HasFiniteLength γ := GlobalTheory.JacquetBlocks.hasFiniteLength_of_surjective q hq h
  rw [class_eq_finite_length_class β h, class_eq_finite_length_class α hα, class_eq_finite_length_class γ hγ, clsGL, clsGL, clsGL, cls_exact i q hi hq he h hα hγ,
    Finsupp.mapDomain_add]

end Cl0

section Induction

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def subIncl {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} (S : Subrepresentation ρ) :
    S.toRepresentation.IntertwiningMap ρ :=
  ⟨S.toSubmodule.subtype, fun _ => rfl⟩

theorem induction_length (P : ∀ (Y : Type) [AddCommGroup Y] [Module ℂ Y], Representation ℂ G Y → Prop)
    (hzero : ∀ (Y : Type) [AddCommGroup Y] [Module ℂ Y] [Subsingleton Y] (σ : Representation ℂ G Y), P Y σ)
    (hirr : ∀ (Y : Type) [AddCommGroup Y] [Module ℂ Y] (σ : Representation ℂ G Y), IsSmooth σ →
      σ.IsIrreducible → P Y σ)
    (hses : ∀ (A B C : Type) [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] [AddCommGroup C]
      [Module ℂ C] (α : Representation ℂ G A) (β : Representation ℂ G B) (γ : Representation ℂ G C)
      (i : α.IntertwiningMap β) (q : β.IntertwiningMap γ), Function.Injective i → Function.Surjective q →
      Function.Exact i q → IsSmooth β → HasFiniteLength β → P A α → P C γ → P B β)
    {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (hs : IsSmooth ρ)
    (hf : HasFiniteLength ρ) : P V ρ := by
  obtain ⟨h1, h2⟩ := (hasFiniteLength_iff_wellFounded ρ).1 hf
  have hsub : ∀ S : Subrepresentation ρ, IsSmooth S.toRepresentation ∧ HasFiniteLength S.toRepresentation :=
    fun S => ⟨(IsSubquotient.of_injective (subIncl S) Subtype.val_injective).isSmooth hs,
      GlobalTheory.ProdLength.hasFiniteLength_of_injective (subIncl S) Subtype.val_injective hf⟩
  have key : ∀ S : Subrepresentation ρ, P _ S.toRepresentation := by
    intro S
    induction S using WellFoundedLT.induction with
    | ind S ih =>
    rcases eq_or_ne S ⊥ with rfl | hS
    · have : Subsingleton (⊥ : Subrepresentation ρ).toSubmodule :=
        inferInstanceAs (Subsingleton (⊥ : Submodule ℂ V))
      exact hzero _ _
    obtain ⟨T, -, hT⟩ := exists_le_covBy_of_lt (bot_lt_iff_ne_bot.2 hS)
    let i : T.toRepresentation.IntertwiningMap S.toRepresentation :=
      ⟨Submodule.inclusion hT.le, fun _ => rfl⟩
    let q : S.toRepresentation.IntertwiningMap (subQuot S T) := ⟨Submodule.mkQ _, fun _ => rfl⟩
    have hq : Function.Surjective q := Submodule.Quotient.mk_surjective _
    have hex : Function.Exact i q := by
      intro y
      refine ⟨fun hy => ⟨⟨y.1, (Submodule.Quotient.mk_eq_zero (T.toSubmodule.comap S.toSubmodule.subtype)).1 hy⟩,
        rfl⟩, ?_⟩
      rintro ⟨x, rfl⟩
      exact (Submodule.Quotient.mk_eq_zero (T.toSubmodule.comap S.toSubmodule.subtype)).2 x.2
    have hsq : IsSmooth (subQuot S T) :=
      ((IsSubquotient.of_surjective q hq).trans
        (IsSubquotient.of_injective (subIncl S) Subtype.val_injective)).isSmooth hs
    exact hses _ _ _ _ _ _ i q (Submodule.inclusion_injective hT.le) hq hex (hsub S).1 (hsub S).2 (ih T hT.lt)
      (hirr _ _ hsq (isIrreducible_subQuot hT))
  let z : Representation.IntertwiningMap ρ (Representation.trivial ℂ G PUnit) :=
    { toLinearMap := 0, isIntertwining' := fun _ => by ext }
  refine hses _ _ _ _ ρ _ (topEquiv ρ).toIntertwiningMap z (topEquiv ρ).injective
    (fun _ => ⟨0, Subsingleton.elim _ _⟩) ?_ hs hf (key ⊤) (hzero _ _)
  intro y
  exact ⟨fun _ => (topEquiv ρ).surjective y, fun _ => Subsingleton.elim _ _⟩

end Induction

section Exact

variable {r t : ℕ}

def extL {G H A B W : Type} [Group G] [Group H] [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    [AddCommGroup W] [Module ℂ W] {α : Representation ℂ G A} {β : Representation ℂ G B}
    (i : α.IntertwiningMap β) (ρ : Representation ℂ H W) :
    (extTensor α ρ).IntertwiningMap (extTensor β ρ) where
  toLinearMap := i.toLinearMap.rTensor W
  isIntertwining' g := TensorProduct.ext' fun v w => by
    simp [i.isIntertwining]

def extR {G H A B X : Type} [Group G] [Group H] [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ G X) {α : Representation ℂ H A}
    {β : Representation ℂ H B} (i : α.IntertwiningMap β) :
    (extTensor ρ α).IntertwiningMap (extTensor ρ β) where
  toLinearMap := i.toLinearMap.lTensor X
  isIntertwining' g := TensorProduct.ext' fun v w => by
    simp [i.isIntertwining]

theorem continuous_levi_pair :
    Continuous fun h : Levi k (Two (Fin r) (Fin t)) => (h false, h true) :=
  (continuous_apply false).prodMk (continuous_apply true)

theorem parInd_ses {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) {A B C : Type}
    [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] [AddCommGroup C] [Module ℂ C]
    {ξ : Representation ℂ (Levi k m) A} {η : Representation ℂ (Levi k m) B} {ζ : Representation ℂ (Levi k m) C}
    (i : ξ.IntertwiningMap η) (q : η.IntertwiningMap ζ) (hi : Function.Injective i)
    (hq : Function.Surjective q) (he : Function.Exact i q) (hη : IsSmooth η) :
    Function.Injective (parIndMap e i) ∧ Function.Surjective (parIndMap e q) ∧
      Function.Exact (parIndMap e i) (parIndMap e q) := by
  refine ⟨GlobalTheory.ParIndExact.parIndMap_injective e i hi,
    GlobalTheory.CompanionTheory.SegQuotTwo.parIndMap_surjective e q hη hq, fun φ => ⟨fun hφ => ?_, ?_⟩⟩
  · exact GlobalTheory.ParIndExact.parIndMap_exact e i q hi (fun v hv => (he v).1 hv) φ hφ
  · rintro ⟨ψ, rfl⟩
    apply Subtype.ext
    apply Subtype.ext
    funext g
    exact he.apply_apply_eq_zero (ψ.1.1 g)

theorem prod₂_ses_left {A B C W : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    [AddCommGroup C] [Module ℂ C] [AddCommGroup W] [Module ℂ W]
    {α : Representation ℂ (GL (Fin r) k) A} {β : Representation ℂ (GL (Fin r) k) B}
    {γ : Representation ℂ (GL (Fin r) k) C} (ρ : Representation ℂ (GL (Fin t) k) W)
    (i : α.IntertwiningMap β) (q : β.IntertwiningMap γ) (hi : Function.Injective i)
    (hq : Function.Surjective q) (he : Function.Exact i q) (hβ : IsSmooth β) (hρ : IsSmooth ρ) :
    ∃ (I : (prod₂ α ρ).IntertwiningMap (prod₂ β ρ)) (Q : (prod₂ β ρ).IntertwiningMap (prod₂ γ ρ)),
      Function.Injective I ∧ Function.Surjective Q ∧ Function.Exact I Q := by
  let s := (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom
  have hi' : Function.Injective (compMap (extL i ρ) s) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ hi
  have hq' : Function.Surjective (compMap (extL q ρ) s) := LinearMap.rTensor_surjective W hq
  have he' : Function.Exact (compMap (extL i ρ) s) (compMap (extL q ρ) s) :=
    rTensor_exact W (f := i.toLinearMap) (g := q.toLinearMap) he hq
  obtain ⟨h1, h2, h3⟩ := parInd_ses (two (stdSum (rfl : r + t = r + t))) _ _ hi' hq' he'
    (isSmooth_comp (isSmooth_extTensor hβ hρ) _ continuous_levi_pair)
  exact ⟨_, _, h1, h2, h3⟩

theorem prod₂_ses_right {X A B C : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] [AddCommGroup C] [Module ℂ C] (ρ : Representation ℂ (GL (Fin r) k) X)
    {α : Representation ℂ (GL (Fin t) k) A} {β : Representation ℂ (GL (Fin t) k) B}
    {γ : Representation ℂ (GL (Fin t) k) C}
    (i : α.IntertwiningMap β) (q : β.IntertwiningMap γ) (hi : Function.Injective i)
    (hq : Function.Surjective q) (he : Function.Exact i q) (hρ : IsSmooth ρ) (hβ : IsSmooth β) :
    ∃ (I : (prod₂ ρ α).IntertwiningMap (prod₂ ρ β)) (Q : (prod₂ ρ β).IntertwiningMap (prod₂ ρ γ)),
      Function.Injective I ∧ Function.Surjective Q ∧ Function.Exact I Q := by
  let s := (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom
  have hi' : Function.Injective (compMap (extR ρ i) s) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ hi
  have hq' : Function.Surjective (compMap (extR ρ q) s) := LinearMap.lTensor_surjective X hq
  have he' : Function.Exact (compMap (extR ρ i) s) (compMap (extR ρ q) s) :=
    lTensor_exact X (f := i.toLinearMap) (g := q.toLinearMap) he hq
  obtain ⟨h1, h2, h3⟩ := parInd_ses (two (stdSum (rfl : r + t = r + t))) _ _ hi' hq' he'
    (isSmooth_comp (isSmooth_extTensor hρ hβ) _ continuous_levi_pair)
  exact ⟨_, _, h1, h2, h3⟩

theorem indSp_eq_zero {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) {B : Type} [AddCommGroup B]
    [Module ℂ B] [Subsingleton B] (η : Representation ℂ (Levi k m) B) (φ : IndSp e η) : φ = 0 :=
  Subtype.ext (Subtype.ext (funext fun _ => Subsingleton.elim _ _))

theorem class_product_zero_left {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [Subsingleton V] (π₁ : Representation ℂ (GL (Fin r) k) V) (π₂ : Representation ℂ (GL (Fin t) k) W) :
    cl0 (prod₂ π₁ π₂) = 0 :=
  class_eq_zero_of_trivial_space (indSp_eq_zero (two (stdSum (rfl : r + t = r + t)))
    ((extTensor π₁ π₂).comp (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom))

theorem class_product_zero_right {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [Subsingleton W] (π₁ : Representation ℂ (GL (Fin r) k) V) (π₂ : Representation ℂ (GL (Fin t) k) W) :
    cl0 (prod₂ π₁ π₂) = 0 :=
  class_eq_zero_of_trivial_space (indSp_eq_zero (two (stdSum (rfl : r + t = r + t)))
    ((extTensor π₁ π₂).comp (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom))

end Exact

section Main

variable {r t : ℕ}

theorem class_product_irreducibles {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π₁ : Representation ℂ (GL (Fin r) k) V) (π₂ : Representation ℂ (GL (Fin t) k) W)
    (s₁ : IsSmooth π₁) (i₁ : π₁.IsIrreducible) (s₂ : IsSmooth π₂) (i₂ : π₂.IsIrreducible) :
    cl0 (prod₂ π₁ π₂) = mulR (cl0 π₁) (cl0 π₂) := by
  rw [class_irreducible_basis π₁ s₁ i₁, class_irreducible_basis π₂ s₂ i₂, mulR_sg_sg]
  exact class_congr_equiv (prod₂Equiv (IrrGL.equivOf π₁ s₁ i₁) (IrrGL.equivOf π₂ s₂ i₂))

theorem class_product_irreducible_left {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π₁ : Representation ℂ (GL (Fin r) k) V) (s₁ : IsSmooth π₁) (i₁ : π₁.IsIrreducible)
    (π₂ : Representation ℂ (GL (Fin t) k) W) (s₂ : IsSmooth π₂) (h₂ : HasFiniteLength π₂) :
    cl0 (prod₂ π₁ π₂) = mulR (cl0 π₁) (cl0 π₂) := by
  have hBZ := GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness
  have hf₁ : HasFiniteLength π₁ := (⟨V, π₁, s₁, i₁⟩ : IrrRep (GL (Fin r) k)).hasFiniteLength
  refine induction_length (fun Y _ _ τ => IsSmooth τ → HasFiniteLength τ →
      cl0 (prod₂ π₁ τ) = mulR (cl0 π₁) (cl0 τ)) ?_ ?_ ?_ π₂ s₂ h₂ s₂ h₂
  · intro Y _ _ _ τ _ _
    rw [class_product_zero_right, class_subsingleton τ, mulR_zero_right]
  · intro Y _ _ τ hs hi _ _
    exact class_product_irreducibles π₁ τ s₁ i₁ hs hi
  · intro A B C _ _ _ _ _ _ α β γ i q hi hq he hsβ hfβ hα hγ _ _
    have hsα : IsSmooth α := (IsSubquotient.of_injective i hi).isSmooth hsβ
    have hsγ : IsSmooth γ := (IsSubquotient.of_surjective q hq).isSmooth hsβ
    have hfα : HasFiniteLength α := GlobalTheory.ProdLength.hasFiniteLength_of_injective i hi hfβ
    have hfγ : HasFiniteLength γ := GlobalTheory.JacquetBlocks.hasFiniteLength_of_surjective q hq hfβ
    obtain ⟨I, Q, hI, hQ, hE⟩ := prod₂_ses_right π₁ i q hi hq he s₁ hsβ
    rw [class_additive_exact I Q hI hQ hE (GlobalTheory.ProdLength.prod₂_hasFiniteLength hBZ k r t V B π₁ β hf₁ hfβ s₁ hsβ),
      hα hsα hfα, hγ hsγ hfγ, ← mulR_add_right, ← class_additive_exact i q hi hq he hfβ]

theorem class_parabolic_product {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π₁ : Representation ℂ (GL (Fin r) k) V) (π₂ : Representation ℂ (GL (Fin t) k) W)
    (h₁ : HasFiniteLength π₁) (h₂ : HasFiniteLength π₂) (s₁ : IsSmooth π₁) (s₂ : IsSmooth π₂) :
    cl0 (prod₂ π₁ π₂) = mulR (cl0 π₁) (cl0 π₂) := by
  have hBZ := GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness
  refine induction_length (fun Y _ _ ρ => IsSmooth ρ → HasFiniteLength ρ →
      cl0 (prod₂ ρ π₂) = mulR (cl0 ρ) (cl0 π₂)) ?_ ?_ ?_ π₁ s₁ h₁ s₁ h₁
  · intro Y _ _ _ ρ _ _
    rw [class_product_zero_left, class_subsingleton ρ, mulR_zero_left]
  · intro Y _ _ ρ hs hi _ _
    exact class_product_irreducible_left ρ hs hi π₂ s₂ h₂
  · intro A B C _ _ _ _ _ _ α β γ i q hi hq he hsβ hfβ hα hγ _ _
    have hsα : IsSmooth α := (IsSubquotient.of_injective i hi).isSmooth hsβ
    have hsγ : IsSmooth γ := (IsSubquotient.of_surjective q hq).isSmooth hsβ
    have hfα : HasFiniteLength α := GlobalTheory.ProdLength.hasFiniteLength_of_injective i hi hfβ
    have hfγ : HasFiniteLength γ := GlobalTheory.JacquetBlocks.hasFiniteLength_of_surjective q hq hfβ
    obtain ⟨I, Q, hI, hQ, hE⟩ := prod₂_ses_left π₂ i q hi hq he hsβ s₂
    rw [class_additive_exact I Q hI hQ hE (GlobalTheory.ProdLength.prod₂_hasFiniteLength hBZ k r t B W β π₂ hfβ h₂ hsβ s₂),
      hα hsα hfα, hγ hsγ hfγ, ← mulR_add_left, ← class_additive_exact i q hi hq he hfβ]

end Main

variable (k) in

theorem mulCls : MulCls k := by
  intro r t V W _ _ _ _ π₁ π₂ h₁ h₂ s₁ s₂
  exact ⟨GlobalTheory.ProdLength.prod₂_hasFiniteLength GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness k r t V W π₁ π₂
    h₁ h₂ s₁ s₂, class_parabolic_product π₁ π₂ h₁ h₂ s₁ s₂⟩

end CompanionTheory.Groth

end
