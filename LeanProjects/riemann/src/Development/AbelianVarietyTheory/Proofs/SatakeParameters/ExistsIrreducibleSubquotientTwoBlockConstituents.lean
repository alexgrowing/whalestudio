import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIwVecTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel

namespace GlobalTheory.ParIndExact
open TensorProduct

theorem exists_covBy_of_split {L : Type} [PartialOrder L] [WellFoundedLT L] [WellFoundedGT L]
    (Q : L → L → Prop) (hself : ∀ S, ¬ Q S S)
    (hsplit : ∀ S U T, T ≤ U → U ≤ S → Q S T → Q U T ∨ Q S U) :
    ∀ S T, T ≤ S → Q S T → ∃ S' T', T' ⋖ S' ∧ Q S' T' := by
  intro S₀
  refine WellFoundedLT.induction (motive := fun S => ∀ T, T ≤ S → Q S T → ∃ S' T', T' ⋖ S' ∧ Q S' T') S₀ ?_
  intro S ihS T₀
  refine WellFoundedGT.induction (motive := fun T => T ≤ S → Q S T → ∃ S' T', T' ⋖ S' ∧ Q S' T') T₀ ?_
  intro T ihT hTS hQ
  have hne : T < S := lt_of_le_of_ne hTS (fun h => hself S (h ▸ hQ))
  by_cases hc : T ⋖ S
  · exact ⟨S, T, hc, hQ⟩
  · obtain ⟨U, hTU, hUS⟩ : ∃ U, T < U ∧ U < S := by
      by_contra hno
      exact hc ⟨hne, fun U h1 h2 => hno ⟨U, h1, h2⟩⟩
    rcases hsplit S U T hTU.le hUS.le hQ with h | h
    · exact ihS U hUS T hTU.le h
    · exact ihT U hTU hUS.le h

section SubQuot
variable {F G V : Type} [Field F] [Group G] [AddCommGroup V] [Module F V] {ρ : Representation F G V}

theorem isSubquotient_subQuot (S T : Subrepresentation ρ) : IsSubquotient (subQuot S T) ρ :=
  ⟨S, ⟨(Submodule.comap S.toSubmodule.subtype T.toSubmodule).mkQ, fun g => LinearMap.ext fun x => rfl⟩,
    Submodule.mkQ_surjective _⟩

theorem subQuot_top_bot (ρ : Representation F G V) :
    ∃ ι : ρ.IntertwiningMap (subQuot (⊤ : Subrepresentation ρ) ⊥), Function.Injective ι := by
  refine ⟨⟨(Submodule.comap (⊤ : Subrepresentation ρ).toSubmodule.subtype
      (⊥ : Subrepresentation ρ).toSubmodule).mkQ ∘ₗ
      LinearMap.codRestrict (⊤ : Subrepresentation ρ).toSubmodule LinearMap.id (fun _ => trivial),
      fun g => LinearMap.ext fun x => rfl⟩, ?_⟩
  intro x y hxy
  have := (Submodule.Quotient.eq _).1 hxy
  have h2 : x - y = 0 := this
  exact sub_eq_zero.1 h2

theorem subQuot_exact {S U T : Subrepresentation ρ} (hTU : T ≤ U) (hUS : U ≤ S) :
    ∃ (ι : (subQuot U T).IntertwiningMap (subQuot S T)) (p : (subQuot S T).IntertwiningMap (subQuot S U)),
      Function.Injective ι ∧ Function.Surjective p ∧ (∀ y, p (ι y) = 0) ∧ ∀ x, p x = 0 → ∃ y, ι y = x := by
  have hUS' : U.toSubmodule ≤ S.toSubmodule := hUS
  have hTU' : T.toSubmodule ≤ U.toSubmodule := hTU
  let i : U.toSubmodule →ₗ[F] S.toSubmodule := Submodule.inclusion hUS'
  have hi : Submodule.comap U.toSubmodule.subtype T.toSubmodule ≤
      Submodule.comap i (Submodule.comap S.toSubmodule.subtype T.toSubmodule) := fun x hx => hx
  have hj : Submodule.comap S.toSubmodule.subtype T.toSubmodule ≤
      Submodule.comap LinearMap.id (Submodule.comap S.toSubmodule.subtype U.toSubmodule) :=
    fun x hx => hTU' hx
  refine ⟨⟨Submodule.mapQ _ _ i hi, fun g => Submodule.linearMap_qext _ (LinearMap.ext fun x => rfl)⟩,
    ⟨Submodule.mapQ _ _ LinearMap.id hj, fun g => Submodule.linearMap_qext _ (LinearMap.ext fun x => rfl)⟩,
    ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    induction x using Submodule.Quotient.induction_on with | H x =>
    induction y using Submodule.Quotient.induction_on with | H y =>
    have := (Submodule.Quotient.eq _).1 hxy
    exact (Submodule.Quotient.eq _).2 this
  · intro x
    induction x using Submodule.Quotient.induction_on with | H x =>
    exact ⟨Submodule.Quotient.mk x, rfl⟩
  · intro y
    induction y using Submodule.Quotient.induction_on with | H y =>
    show Submodule.Quotient.mk _ = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact y.2
  · intro x hx
    induction x using Submodule.Quotient.induction_on with | H x =>
    have hx' : (Submodule.Quotient.mk x : S.toSubmodule ⧸ Submodule.comap S.toSubmodule.subtype U.toSubmodule) = 0 := hx
    have hxU : (x : V) ∈ U.toSubmodule := (Submodule.Quotient.mk_eq_zero (Submodule.comap S.toSubmodule.subtype U.toSubmodule)).1 hx'
    exact ⟨Submodule.Quotient.mk ⟨x, hxU⟩, rfl⟩

end SubQuot

section Tensor
variable {F G H V₁ V V₂ W : Type} [Field F] [Group G] [Group H]
    [AddCommGroup V₁] [Module F V₁] [AddCommGroup V] [Module F V] [AddCommGroup V₂] [Module F V₂]
    [AddCommGroup W] [Module F W]

def extTensorMapLeft {ρ₁ : Representation F G V₁} {ρ : Representation F G V} (B : Representation F H W)
    (f : ρ₁.IntertwiningMap ρ) : (extTensor ρ₁ B).IntertwiningMap (extTensor ρ B) :=
  ⟨f.toLinearMap.rTensor W, fun g => TensorProduct.ext' fun v w => by
    simp only [LinearMap.comp_apply, extTensor_tmul, LinearMap.rTensor_tmul]
    exact congrArg (· ⊗ₜ[F] (B g.2) w) (Representation.IntertwiningMap.isIntertwining _ _ f g.1 v)⟩

def extTensorMapRight {ρ₁ : Representation F H V₁} {ρ : Representation F H V} (A : Representation F G W)
    (f : ρ₁.IntertwiningMap ρ) : (extTensor A ρ₁).IntertwiningMap (extTensor A ρ) :=
  ⟨f.toLinearMap.lTensor W, fun g => TensorProduct.ext' fun v w => by
    simp only [LinearMap.comp_apply, extTensor_tmul, LinearMap.lTensor_tmul]
    exact congrArg ((A g.1) v ⊗ₜ[F] ·) (Representation.IntertwiningMap.isIntertwining _ _ f g.2 w)⟩

theorem extTensor_injective_left {ρ₁ : Representation F G V₁} {ρ : Representation F G V}
    (B : Representation F H W) (ι : ρ₁.IntertwiningMap ρ) (hι : Function.Injective ι) :
    ∃ ι' : (extTensor ρ₁ B).IntertwiningMap (extTensor ρ B), Function.Injective ι' :=
  ⟨extTensorMapLeft B ι, Module.Flat.rTensor_preserves_injective_linearMap ι.toLinearMap hι⟩

theorem extTensor_injective_right {ρ₁ : Representation F H V₁} {ρ : Representation F H V}
    (A : Representation F G W) (ι : ρ₁.IntertwiningMap ρ) (hι : Function.Injective ι) :
    ∃ ι' : (extTensor A ρ₁).IntertwiningMap (extTensor A ρ), Function.Injective ι' :=
  ⟨extTensorMapRight A ι, Module.Flat.lTensor_preserves_injective_linearMap ι.toLinearMap hι⟩

theorem extTensor_exact_left {ρ₁ : Representation F G V₁} {ρ : Representation F G V}
    {ρ₂ : Representation F G V₂} (B : Representation F H W) (ι : ρ₁.IntertwiningMap ρ)
    (p : ρ.IntertwiningMap ρ₂) (hι : Function.Injective ι) (hp : Function.Surjective p)
    (hpι : ∀ u, p (ι u) = 0) (hex : ∀ v, p v = 0 → ∃ u, ι u = v) :
    ∃ (ι' : (extTensor ρ₁ B).IntertwiningMap (extTensor ρ B)) (p' : (extTensor ρ B).IntertwiningMap (extTensor ρ₂ B)),
      Function.Injective ι' ∧ ∀ x, p' x = 0 → ∃ y, ι' y = x := by
  have hexact : Function.Exact ι.toLinearMap p.toLinearMap := fun v =>
    ⟨fun h => hex v h, fun ⟨u, hu⟩ => hu ▸ hpι u⟩
  refine ⟨extTensorMapLeft B ι, extTensorMapLeft B p,
    Module.Flat.rTensor_preserves_injective_linearMap ι.toLinearMap hι, fun x hx => ?_⟩
  exact (rTensor_exact W hexact hp x).1 hx

theorem extTensor_exact_right {ρ₁ : Representation F H V₁} {ρ : Representation F H V}
    {ρ₂ : Representation F H V₂} (A : Representation F G W) (ι : ρ₁.IntertwiningMap ρ)
    (p : ρ.IntertwiningMap ρ₂) (hι : Function.Injective ι) (hp : Function.Surjective p)
    (hpι : ∀ u, p (ι u) = 0) (hex : ∀ v, p v = 0 → ∃ u, ι u = v) :
    ∃ (ι' : (extTensor A ρ₁).IntertwiningMap (extTensor A ρ)) (p' : (extTensor A ρ).IntertwiningMap (extTensor A ρ₂)),
      Function.Injective ι' ∧ ∀ x, p' x = 0 → ∃ y, ι' y = x := by
  have hexact : Function.Exact ι.toLinearMap p.toLinearMap := fun v =>
    ⟨fun h => hex v h, fun ⟨u, hu⟩ => hu ▸ hpι u⟩
  refine ⟨extTensorMapRight A ι, extTensorMapRight A p,
    Module.Flat.lTensor_preserves_injective_linearMap ι.toLinearMap hι, fun x hx => ?_⟩
  exact (lTensor_exact W hexact hp x).1 hx

end Tensor
end GlobalTheory.ParIndExact

namespace GlobalTheory.ParIndExact

theorem isSubquotient_of_step {F G V W : Type} [Field F] [Group G] [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W] {σ : Representation F G W} {ρ : Representation F G V}
    {S T : Subrepresentation ρ} (h : GlobalTheory.JHMult.Step σ S T) : IsSubquotient σ ρ := by
  obtain ⟨f, hsurj, hint, -⟩ := h
  refine ⟨S, ⟨f ∘ₗ S.toSubmodule.subtype, fun g => LinearMap.ext fun v => ?_⟩, fun w => ?_⟩
  · exact hint g v v.2
  · obtain ⟨v, hv, rfl⟩ := hsurj w
    exact ⟨⟨v, hv⟩, rfl⟩

theorem isSubquotient_dichotomy {F G V W V₁ V₂ : Type} [Field F] [Group G] [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W] [AddCommGroup V₁] [Module F V₁] [AddCommGroup V₂] [Module F V₂]
    {σ : Representation F G W} {ρ : Representation F G V} {ρ₁ : Representation F G V₁}
    {ρ₂ : Representation F G V₂} (ι : ρ₁.IntertwiningMap ρ) (p : ρ.IntertwiningMap ρ₂)
    (hσ : σ.IsIrreducible) (hex : ∀ v, p v = 0 → ∃ u, ι u = v) (h : IsSubquotient σ ρ) :
    IsSubquotient σ ρ₁ ∨ IsSubquotient σ ρ₂ := by
  obtain ⟨S, f, hf⟩ := h
  obtain ⟨f', hf'⟩ := LinearMap.exists_extend f.toLinearMap
  have hf'v : ∀ v (hv : v ∈ S.toSubmodule), f' v = f ⟨v, hv⟩ := fun v hv =>
    LinearMap.congr_fun hf' ⟨v, hv⟩
  let T : Subrepresentation ρ :=
    ⟨Submodule.map S.toSubmodule.subtype (LinearMap.ker f.toLinearMap), by
      rintro g _ ⟨x, hx, rfl⟩
      refine ⟨S.toRepresentation g x, ?_, rfl⟩
      have hx' : f x = 0 := hx
      show f (S.toRepresentation g x) = 0
      rw [Representation.IntertwiningMap.isIntertwining, hx', map_zero]⟩
  have hTS : T ≤ S := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hstep : GlobalTheory.JHMult.Step σ S T := by
    refine ⟨f', fun w => ?_, fun g v hv => ?_, fun v hv => ?_⟩
    · obtain ⟨x, rfl⟩ := hf w
      exact ⟨x, x.2, hf'v x x.2⟩
    · rw [hf'v v hv, hf'v _ (S.apply_mem_toSubmodule g hv)]
      exact Representation.IntertwiningMap.isIntertwining _ _ f g ⟨v, hv⟩
    · rw [hf'v v hv]
      constructor
      · intro h0
        exact ⟨⟨v, hv⟩, h0, rfl⟩
      · rintro ⟨x, hx, hxv⟩
        have : x = ⟨v, hv⟩ := Subtype.ext hxv
        subst this
        exact hx
  rcases GlobalTheory.JHMult.step_dichotomy ι p hσ hex hTS hstep with h1 | h2
  · exact Or.inl (isSubquotient_of_step h1)
  · exact Or.inr (isSubquotient_of_step h2)

end GlobalTheory.ParIndExact

namespace GlobalTheory.ParIndExact

section ParInd
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
    [Fintype n] [DecidableEq n]

theorem parIndMap_injective {V₁ V : Type} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V] [Module ℂ V]
    (e : (Σ a, m a) ≃ n) {ρ₁ : Representation ℂ (Levi k m) V₁} {ρ : Representation ℂ (Levi k m) V}
    (ι : ρ₁.IntertwiningMap ρ) (hι : Function.Injective ι) : Function.Injective (parIndMap e ι) := by
  intro φ ψ h
  have h' : ∀ g, ι (φ.1.1 g) = ι (ψ.1.1 g) := fun g => congrFun (congrArg (fun x => x.1.1) h) g
  exact Subtype.ext (Subtype.ext (funext fun g => hι (h' g)))

theorem parIndMap_exact {V₁ V V₂ : Type} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V₂] [Module ℂ V₂] (e : (Σ a, m a) ≃ n) {ρ₁ : Representation ℂ (Levi k m) V₁}
    {ρ : Representation ℂ (Levi k m) V} {ρ₂ : Representation ℂ (Levi k m) V₂}
    (ι : ρ₁.IntertwiningMap ρ) (p : ρ.IntertwiningMap ρ₂) (hι : Function.Injective ι)
    (hex : ∀ v, p v = 0 → ∃ u, ι u = v) :
    ∀ f, parIndMap e p f = 0 → ∃ g, parIndMap e ι g = f := by
  intro φ hφ
  let σ₁ := (twist ρ₁ (deltaHalf k m)).comp (leviProj k e)
  let σ := (twist ρ (deltaHalf k m)).comp (leviProj k e)
  let ιt : Representation.IntertwiningMap σ₁ σ := compMap (twistMap ι (deltaHalf k m)) (leviProj k e)
  have hp0 : ∀ g, p (φ.1.1 g) = 0 := fun g => congrFun (congrArg (fun x => x.1.1) hφ) g
  choose ψf hψf using fun g => hex _ (hp0 g)
  have hφind : ∀ (h : parab k e) g, φ.1.1 (↑h * g) = σ h (φ.1.1 g) := φ.1.2
  have hmem : ψf ∈ indSpace (parab k e) σ₁ := by
    intro h g
    apply hι
    calc ι (ψf (↑h * g)) = φ.1.1 (↑h * g) := hψf _
      _ = σ h (φ.1.1 g) := hφind h g
      _ = σ h (ι (ψf g)) := by rw [hψf g]
      _ = ι (σ₁ h (ψf g)) := (Representation.IntertwiningMap.isIntertwining _ _ ιt h (ψf g)).symm
  let ψ' : indSpace (parab k e) σ₁ := ⟨ψf, hmem⟩
  have hset : {x | (ind (parab k e) σ₁ x) ψ' = ψ'} = {x | (ind (parab k e) σ x) φ.1 = φ.1} := by
    ext x
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hx
      apply Subtype.ext
      funext y
      have := congrFun (congrArg Subtype.val hx) y
      change ψf (y * x) = ψf y at this
      change φ.1.1 (y * x) = φ.1.1 y
      rw [← hψf, ← hψf, this]
    · intro hx
      apply Subtype.ext
      funext y
      have := congrFun (congrArg Subtype.val hx) y
      change φ.1.1 (y * x) = φ.1.1 y at this
      change ψf (y * x) = ψf y
      apply hι
      rw [hψf, hψf, this]
  have hsm : ψ' ∈ smoothPart (ind (parab k e) σ₁) := by
    change IsOpen {x | (ind (parab k e) σ₁ x) ψ' = ψ'}
    rw [hset]
    exact φ.2
  exact ⟨⟨ψ', hsm⟩, Subtype.ext (Subtype.ext (funext fun g => hψf g))⟩

end ParInd
end GlobalTheory.ParIndExact

namespace GlobalTheory.ParIndExact

section Glue
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : Type} [Fintype n] [DecidableEq n] {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

theorem ind₂_dichotomy (e : a ⊕ b ≃ n) {V₁ V V₂ U : Type} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V]
    [Module ℂ V] [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup U] [Module ℂ U]
    {ρ₁ : Representation ℂ (GL a k × GL b k) V₁} {ρ : Representation ℂ (GL a k × GL b k) V}
    {ρ₂ : Representation ℂ (GL a k × GL b k) V₂}
    (ι : ρ₁.IntertwiningMap ρ) (p : ρ.IntertwiningMap ρ₂) (hι : Function.Injective ι)
    (hex : ∀ v, p v = 0 → ∃ u, ι u = v) {π : Representation ℂ (GL n k) U} (hπ : π.IsIrreducible)
    (h : IsSubquotient π (ind₂ e ρ)) : IsSubquotient π (ind₂ e ρ₁) ∨ IsSubquotient π (ind₂ e ρ₂) := by
  have hι' : Function.Injective (compMap ι (leviTwo k a b).symm.toMonoidHom) := hι
  have hex' : ∀ v, compMap p (leviTwo k a b).symm.toMonoidHom v = 0 →
      ∃ u, compMap ι (leviTwo k a b).symm.toMonoidHom u = v := hex
  exact isSubquotient_dichotomy _ _ hπ (parIndMap_exact (two e) _ _ hι' hex') h

theorem ind₂_of_injective (e : a ⊕ b ≃ n) {V₁ V U : Type} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V]
    [Module ℂ V] [AddCommGroup U] [Module ℂ U]
    {ρ₁ : Representation ℂ (GL a k × GL b k) V₁} {ρ : Representation ℂ (GL a k × GL b k) V}
    (ι : ρ₁.IntertwiningMap ρ) (hι : Function.Injective ι) {π : Representation ℂ (GL n k) U}
    (h : IsSubquotient π (ind₂ e ρ₁)) : IsSubquotient π (ind₂ e ρ) := by
  have hι' : Function.Injective (compMap ι (leviTwo k a b).symm.toMonoidHom) := hι
  exact h.trans (IsSubquotient.of_injective _ (parIndMap_injective (two e) _ hι'))

theorem not_isSubquotient_ind₂ (e : a ⊕ b ≃ n) {V U : Type} [AddCommGroup V] [Module ℂ V] [Subsingleton V]
    [AddCommGroup U] [Module ℂ U] (ρ : Representation ℂ (GL a k × GL b k) V)
    {π : Representation ℂ (GL n k) U} (hπ : π.IsIrreducible) : ¬ IsSubquotient π (ind₂ e ρ) := by
  rintro ⟨S, f, hf⟩
  haveI := nontrivial_of_irreducible hπ
  obtain ⟨x, y, hxy⟩ := exists_pair_ne U
  obtain ⟨x', rfl⟩ := hf x
  obtain ⟨y', rfl⟩ := hf y
  apply hxy
  congr 1
  apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
  funext g
  exact Subsingleton.elim _ _

end Glue

theorem subsingleton_subQuot_self {F G V : Type} [Field F] [Group G] [AddCommGroup V] [Module F V]
    {ρ : Representation F G V} (S : Subrepresentation ρ) :
    Subsingleton (S.toSubmodule ⧸ Submodule.comap S.toSubmodule.subtype S.toSubmodule) := by
  constructor
  intro x y
  induction x using Submodule.Quotient.induction_on with
  | H x =>
  induction y using Submodule.Quotient.induction_on with
  | H y =>
  rw [Submodule.Quotient.eq]
  simp

theorem tensor_subsingleton_left {F V W : Type} [Field F] [AddCommGroup V] [Module F V] [AddCommGroup W]
    [Module F W] [Subsingleton V] : Subsingleton (TensorProduct F V W) := by
  have h0 : ∀ z : TensorProduct F V W, z = 0 := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | tmul v w => rw [Subsingleton.elim v 0, TensorProduct.zero_tmul]
    | add x y hx hy => rw [hx, hy, add_zero]
  exact ⟨fun x y => by rw [h0 x, h0 y]⟩

theorem tensor_subsingleton_right {F V W : Type} [Field F] [AddCommGroup V] [Module F V] [AddCommGroup W]
    [Module F W] [Subsingleton W] : Subsingleton (TensorProduct F V W) := by
  have h0 : ∀ z : TensorProduct F V W, z = 0 := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | tmul v w => rw [Subsingleton.elim w 0, TensorProduct.tmul_zero]
    | add x y hx hy => rw [hx, hy, add_zero]
  exact ⟨fun x y => by rw [h0 x, h0 y]⟩

section Main
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem step_left {r t : ℕ} {U V W : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin (r + t)) k) U)
    (A : Representation ℂ (GL (Fin r) k) V) (B : Representation ℂ (GL (Fin t) k) W)
    (hπ : π.IsIrreducible) {S M T : Subrepresentation A} (hTM : T ≤ M) (hMS : M ≤ S)
    (h : IsSubquotient π (prod₂ (subQuot S T) B)) :
    IsSubquotient π (prod₂ (subQuot M T) B) ∨ IsSubquotient π (prod₂ (subQuot S M) B) := by
  obtain ⟨ι, p, hι, hp, hpι, hex⟩ := subQuot_exact (ρ := A) hTM hMS
  obtain ⟨ι', p', hι', hex'⟩ := extTensor_exact_left (F := ℂ) (G := GL (Fin r) k) (H := GL (Fin t) k) B ι p hι hp hpι hex
  exact ind₂_dichotomy _ ι' p' hι' hex' hπ h

theorem step_right {r t : ℕ} {U V W : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin (r + t)) k) U)
    (A : Representation ℂ (GL (Fin r) k) V) (B : Representation ℂ (GL (Fin t) k) W)
    (hπ : π.IsIrreducible) {S M T : Subrepresentation B} (hTM : T ≤ M) (hMS : M ≤ S)
    (h : IsSubquotient π (prod₂ A (subQuot S T))) :
    IsSubquotient π (prod₂ A (subQuot M T)) ∨ IsSubquotient π (prod₂ A (subQuot S M)) := by
  obtain ⟨ι, p, hι, hp, hpι, hex⟩ := subQuot_exact (ρ := B) hTM hMS
  obtain ⟨ι', p', hι', hex'⟩ := extTensor_exact_right (F := ℂ) (G := GL (Fin r) k) (H := GL (Fin t) k) A ι p hι hp hpι hex
  exact ind₂_dichotomy _ ι' p' hι' hex' hπ h

theorem top_left {r t : ℕ} {U V W : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin (r + t)) k) U)
    (A : Representation ℂ (GL (Fin r) k) V) (B : Representation ℂ (GL (Fin t) k) W)
    (h : IsSubquotient π (prod₂ A B)) :
    IsSubquotient π (prod₂ (subQuot (⊤ : Subrepresentation A) ⊥) B) := by
  exact (subQuot_top_bot A).elim fun ι hι =>
    (extTensor_injective_left (F := ℂ) (G := GL (Fin r) k) (H := GL (Fin t) k) B ι hι).elim
      fun ι' hι' => ind₂_of_injective _ ι' hι' h

theorem top_right {r t : ℕ} {U V W : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin (r + t)) k) U)
    (A : Representation ℂ (GL (Fin r) k) V) (B : Representation ℂ (GL (Fin t) k) W)
    (h : IsSubquotient π (prod₂ A B)) :
    IsSubquotient π (prod₂ A (subQuot (⊤ : Subrepresentation B) ⊥)) := by
  exact (subQuot_top_bot B).elim fun ι hι =>
    (extTensor_injective_right (F := ℂ) (G := GL (Fin r) k) (H := GL (Fin t) k) A ι hι).elim
      fun ι' hι' => ind₂_of_injective _ ι' hι' h

theorem exists_covBy_left {r t : ℕ} {U V W : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin (r + t)) k) U)
    (A : Representation ℂ (GL (Fin r) k) V) (B : Representation ℂ (GL (Fin t) k) W)
    (hπ : π.IsIrreducible) (hA : HasFiniteLength A) (h : IsSubquotient π (prod₂ A B)) :
    ∃ S T : Subrepresentation A, T ⋖ S ∧ IsSubquotient π (prod₂ (subQuot S T) B) := by
  obtain ⟨h1, h2⟩ := (hasFiniteLength_iff_wellFounded A).1 hA
  refine exists_covBy_of_split (fun (S T : Subrepresentation A) => IsSubquotient π (prod₂ (subQuot S T) B)) ?_ ?_ ⊤ ⊥ bot_le ?_
  · intro S hS
    haveI := subsingleton_subQuot_self S
    haveI := tensor_subsingleton_left (F := ℂ)
      (V := ↥S.toSubmodule ⧸ Submodule.comap S.toSubmodule.subtype S.toSubmodule) (W := W)
    exact not_isSubquotient_ind₂ _ _ hπ hS
  · intro S₀ M₀ T₀ hTM hMS hQ
    exact step_left π A B hπ hTM hMS hQ
  · exact top_left π A B h

theorem exists_covBy_right {r t : ℕ} {U V W : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin (r + t)) k) U)
    (A : Representation ℂ (GL (Fin r) k) V) (B : Representation ℂ (GL (Fin t) k) W)
    (hπ : π.IsIrreducible) (hB : HasFiniteLength B) (h : IsSubquotient π (prod₂ A B)) :
    ∃ S T : Subrepresentation B, T ⋖ S ∧ IsSubquotient π (prod₂ A (subQuot S T)) := by
  obtain ⟨h1, h2⟩ := (hasFiniteLength_iff_wellFounded B).1 hB
  refine exists_covBy_of_split (fun (S T : Subrepresentation B) => IsSubquotient π (prod₂ A (subQuot S T))) ?_ ?_ ⊤ ⊥ bot_le ?_
  · intro S hS
    haveI := subsingleton_subQuot_self S
    haveI := tensor_subsingleton_right (F := ℂ) (V := V)
      (W := ↥S.toSubmodule ⧸ Submodule.comap S.toSubmodule.subtype S.toSubmodule)
    exact not_isSubquotient_ind₂ _ _ hπ hS
  · intro S₀ M₀ T₀ hTM hMS hQ
    exact step_right π A B hπ hTM hMS hQ
  · exact top_right π A B h

end Main

end GlobalTheory.ParIndExact

open GlobalTheory.ParIndExact in
theorem GlobalTheory.ParIndExact.exists_irr_isSubquotient_prod₂ :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (U : Type) [AddCommGroup U] [Module ℂ U] (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin (r + t)) k) U) (A : Representation ℂ (GL (Fin r) k) V) (B : Representation ℂ (GL (Fin t) k) W), π.IsIrreducible → IsSmooth A → IsSmooth B → HasFiniteLength A → HasFiniteLength B → IsSubquotient π (prod₂ A B) → ∃ (σ₁ : Irr k r) (σ₂ : Irr k t), IsSubquotient σ₁.π A ∧ IsSubquotient σ₂.π B ∧ IsSubquotient π (prod₂ σ₁.π σ₂.π) := by
  intro k _ _ _ _ r t U _ _ V _ _ W _ _ π A B hπ hsA hsB hA hB h
  obtain ⟨S, T, hST, h1⟩ := exists_covBy_left π A B hπ hA h
  obtain ⟨S', T', hST', h2⟩ := exists_covBy_right π (subQuot S T) B hπ hB h1
  exact ⟨Irr.mk _ (subQuot S T) ((isSubquotient_subQuot S T).isSmooth hsA) (isIrreducible_subQuot hST),
    Irr.mk _ (subQuot S' T') ((isSubquotient_subQuot S' T').isSmooth hsB) (isIrreducible_subQuot hST'),
    isSubquotient_subQuot S T, isSubquotient_subQuot S' T', h2⟩
