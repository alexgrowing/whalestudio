import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult

namespace GlobalTheory

namespace SmGL

section Relative

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α β : Type} [Fintype α] [Fintype β] [LinearOrder β]
  {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  {c : α → β → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)]
  {W : Type} [AddCommGroup W] [Module ℂ W]

def relParab (f : ∀ i, (Σ j, c i j) ≃ m i) : Subgroup (Levi k m) :=
  Subgroup.pi Set.univ fun i => parab k (f i)

def relUnip (f : ∀ i, (Σ j, c i j) ≃ m i) : Subgroup (Levi k m) :=
  Subgroup.pi Set.univ fun i => unipRad k (f i)

def relProj (f : ∀ i, (Σ j, c i j) ≃ m i) : relParab k f →* ∀ i, Levi k (c i) where
  toFun p i := leviProj k (f i) ⟨p.1 i, p.2 i trivial⟩
  map_one' := funext fun i => map_one (leviProj k (f i))
  map_mul' p q := funext fun i =>
    map_mul (leviProj k (f i)) ⟨p.1 i, p.2 i trivial⟩ ⟨q.1 i, q.2 i trivial⟩

def relEmb (f : ∀ i, (Σ j, c i j) ≃ m i) : (∀ i, Levi k (c i)) →* Levi k m :=
  MonoidHom.pi fun i => (leviEmb k (f i)).comp (Pi.evalMonoidHom (fun i => Levi k (c i)) i)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype α] in

theorem relEmb_mem_normalizer (f : ∀ i, (Σ j, c i j) ≃ m i) (g : ∀ i, Levi k (c i)) :
    relEmb k f g ∈ Subgroup.normalizer (relUnip k f : Set (Levi k m)) :=
  Subgroup.mem_normalizer_iff.2 fun u => forall₂_congr fun i _ =>
    Subgroup.mem_normalizer_iff.1 (leviEmb_mem_normalizer k (f i) (g i)) (u i)

def relDeltaHalf (c : α → β → Type) [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)] :
    (∀ i, Levi k (c i)) →* ℂˣ :=
  ∏ i, (deltaHalf k (c i)).comp (Pi.evalMonoidHom (fun i => Levi k (c i)) i)

def swapBlocks {α β : Type} (c : α → β → Type) [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)] :
    (∀ j, Levi k fun i => c i j) →* ∀ i, Levi k (c i) where
  toFun g i j := g j i
  map_one' := rfl
  map_mul' _ _ := rfl

variable {k}

def relJac (f : ∀ i, (Σ j, c i j) ≃ m i) (ρ : Representation ℂ (Levi k m) W) :
    Representation ℂ (∀ i, Levi k (c i)) (Jacquet ρ (relUnip k f)) :=
  twist (jacquet ρ (relUnip k f) (relEmb k f) (relEmb_mem_normalizer k f)) (relDeltaHalf k c)⁻¹

def relInd (f : ∀ i, (Σ j, c i j) ≃ m i) (ρ : Representation ℂ (∀ i, Levi k (c i)) W) :
    Representation ℂ (Levi k m)
      (smoothPart (ind (relParab k f) ((twist ρ (relDeltaHalf k c)).comp (relProj k f)))) :=
  smInd (relParab k f) ((twist ρ (relDeltaHalf k c)).comp (relProj k f))

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype α] [LinearOrder β] in

theorem relEmb_apply (f : ∀ i, (Σ j, c i j) ≃ m i) (g : ∀ i, Levi k (c i)) (i : α) :
    relEmb k f g i = leviEmb k (f i) (g i) := rfl

theorem relDeltaHalf_apply (g : ∀ i, Levi k (c i)) :
    relDeltaHalf k c g = ∏ i, deltaHalf k (c i) (g i) := by
  simp [relDeltaHalf, MonoidHom.finsetProd_apply]

theorem relJac_mk (f : ∀ i, (Σ j, c i j) ≃ m i) (ρ : Representation ℂ (Levi k m) W)
    (g : ∀ i, Levi k (c i)) (v : W) :
    relJac f ρ g (Submodule.Quotient.mk v) =
      (((relDeltaHalf k c g)⁻¹ : ℂˣ) : ℂ) • Submodule.Quotient.mk (ρ (relEmb k f g) v) := rfl

theorem isSmooth_relInd (f : ∀ i, (Σ j, c i j) ≃ m i) (ρ : Representation ℂ (∀ i, Levi k (c i)) W) :
    IsSmooth (relInd f ρ) := isSmooth_smoothRep _

def cellFunctor [LinearOrder α] {m' : β → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)]
    (f : ∀ i, (Σ j, c i j) ≃ m i) (g : ∀ j, (Σ i, c i j) ≃ m' j)
    (ρ : Representation ℂ (Levi k m) W) :=
  relInd (c := fun j i => c i j) g ((relJac f ρ).comp (swapBlocks k c))

def SizeMatrix {α β : Type} [Fintype α] [Fintype β] (m : α → Type) [∀ i, Fintype (m i)]
    (m' : β → Type) [∀ j, Fintype (m' j)] : Type :=
  {b : α → β → ℕ // (∀ i, ∑ j, b i j = Fintype.card (m i)) ∧ ∀ j, ∑ i, b i j = Fintype.card (m' j)}

theorem SizeMatrix.nonempty_rows {α β : Type} [Fintype α] [Fintype β] {m : α → Type}
    [∀ i, Fintype (m i)] {m' : β → Type} [∀ j, Fintype (m' j)] (b : SizeMatrix m m') :
    Nonempty (∀ i, (Σ j, Fin (b.1 i j)) ≃ m i) :=
  ⟨fun i => Fintype.equivOfCardEq (by simp [b.2.1 i])⟩

theorem SizeMatrix.nonempty_cols {α β : Type} [Fintype α] [Fintype β] {m : α → Type}
    [∀ i, Fintype (m i)] {m' : β → Type} [∀ j, Fintype (m' j)] (b : SizeMatrix m m') :
    Nonempty (∀ j, (Σ i, Fin (b.1 i j)) ≃ m' j) :=
  ⟨fun j => Fintype.equivOfCardEq (by simp [b.2.2 j])⟩

end Relative

section Ring

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

abbrev GrothGL : Type 1 := (Σ n : ℕ, IrrCl (GL (Fin n) k)) →₀ ℤ

structure Segment : Type 1 where

  d : ℕ
  d_pos : 0 < d

  start : IrrCl (GL (Fin d) k)
  cusp : ∃ σ : IrrRep (GL (Fin d) k), σ.cl = start ∧ IsCuspidal σ.ρ

  len : ℕ
  len_pos : 0 < len

variable {k} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def clsGL {n : ℕ} (π : Representation ℂ (GL (Fin n) k) V) (h : HasFiniteLength π) : GrothGL k :=
  (cls π h).mapDomain (Sigma.mk n)

def segTerm {d : Type} [Fintype d] [DecidableEq d] (σ : Representation ℂ (GL d k) V) (l : ℕ)
    (a : Fin l) : Representation ℂ (GL d k) V :=
  twist σ (detChar d (absPow k ((a : ℕ) : ℂ)))

def IrrRep.det (n : Type) [Fintype n] [DecidableEq n] (χ : kˣ →* ℂˣ) (h : IsSmoothChar χ) :
    IrrRep (GL n k) :=
  IrrRep.ofChar (detChar n χ) h.detChar

def Segment.ofChar (χ : kˣ →* ℂˣ) (h : IsSmoothChar χ) (l : ℕ) (hl : 0 < l) : Segment k :=
  ⟨1, one_pos, (IrrRep.det (Fin 1) χ h).cl, ⟨_, rfl, isCuspidal_detRep_one h⟩, l, hl⟩

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in

theorem isSmoothChar_one {G : Type} [Group G] [TopologicalSpace G] : IsSmoothChar (1 : G →* ℂˣ) := by
  unfold IsSmoothChar; simp

variable (k) in

def GrothGL.unit : GrothGL k :=
  Finsupp.single ⟨0, (IrrRep.det (Fin 0) 1 isSmoothChar_one).cl⟩ 1

variable (k) in

def JacquetOfInducedFiltration : Prop :=
  ∀ (α β n : Type) [Fintype α] [LinearOrder α] [Fintype β] [LinearOrder β] [Fintype n] [DecidableEq n]
    (m : α → Type) [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
    (m' : β → Type) [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)]
    (e : (Σ i, m i) ≃ n) (e' : (Σ j, m' j) ≃ n),
    ∃ (N : ℕ) (b : Fin N ≃ SizeMatrix m m'),
      ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k m) W), IsSmooth ρ →
        ∃ S : Fin (N + 1) → Subrepresentation (jac e' (parInd e ρ)),
          Monotone S ∧ S 0 = ⊥ ∧ S (Fin.last N) = ⊤ ∧
            ∀ (t : Fin N) (f : ∀ i, (Σ j, Fin ((b t).1 i j)) ≃ m i)
              (g : ∀ j, (Σ i, Fin ((b t).1 i j)) ≃ m' j),
              Nonempty ((subQuot (S t.succ) (S t.castSucc)).Equiv (cellFunctor f g ρ))

variable (k) in

def CellSemisimplification : Prop :=
  ∀ (α β : Type) [Fintype α] [LinearOrder α] [Fintype β] [LinearOrder β]
    (m : α → Type) [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
    (m' : β → Type) [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)]
    (c : α → β → Type) [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)]
    (f : ∀ i, (Σ j, c i j) ≃ m i) (g : ∀ j, (Σ i, c i j) ≃ m' j)
    (X : α → Type) [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]
    (ρ : ∀ i, Representation ℂ (GL (m i) k) (X i)),
    (∀ i, IsSmooth (ρ i)) → (∀ i, HasFiniteLength (ρ i)) →
      ∃ T : Finset (∀ i j, IrrCl (GL (c i j) k)),
        (∀ s ∉ T, ∃ i, jhMult (piTensor fun j => (s i j).rep.ρ) (jac (f i) (ρ i)) = 0) ∧
        ∀ τ : IrrRep (Levi k m'),
          jhMult τ.ρ (cellFunctor f g (piTensor ρ)) =
            ∑ s ∈ T, (∏ i, jhMult (piTensor fun j => (s i j).rep.ρ) (jac (f i) (ρ i))) *
              jhMult τ.ρ (piTensor fun j => multiProd (g j) fun i => (s i j).rep.ρ)

variable (k) in

def IsSegmentClass (Z : ∀ Δ : Segment k, IrrCl (GL (Fin (Δ.len * Δ.d)) k)) : Prop :=
  ∀ (Δ : Segment k) (σ : IrrRep (GL (Fin Δ.d) k)), σ.cl = Δ.start →
    ∀ (e : (Σ _ : Fin Δ.len, Fin Δ.d) ≃ Fin (Δ.len * Δ.d)) (π : IrrRep (GL (Fin (Δ.len * Δ.d)) k)),
      (π.cl = Z Δ ↔ ∃ φ : π.ρ.IntertwiningMap (multiProd e (segTerm σ.ρ Δ.len)),
        Function.Injective φ) ∧
      (π.cl = Z Δ ↔ Nonempty ((jac e π.ρ).Equiv (piTensor (segTerm σ.ρ Δ.len))))

variable (k) in

def IsProductIso {A : Type 1} [CommRing A] (Ψ : GrothGL k ≃+ A) : Prop :=
  Ψ (GrothGL.unit k) = 1 ∧
    ∀ (r t : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
      (π₁ : Representation ℂ (GL (Fin r) k) V) (π₂ : Representation ℂ (GL (Fin t) k) W)
      (h₁ : HasFiniteLength π₁) (h₂ : HasFiniteLength π₂), IsSmooth π₁ → IsSmooth π₂ →
        ∃ h : HasFiniteLength (prod₂ π₁ π₂),
          Ψ (clsGL (prod₂ π₁ π₂) h) = Ψ (clsGL π₁ h₁) * Ψ (clsGL π₂ h₂)

end Ring

end SmGL

namespace Published

def GeometricLemma : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    JacquetOfInducedFiltration k ∧ CellSemisimplification k

def ZelevinskyPolynomialRing : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    ∃ (Z : ∀ Δ : Segment k, IrrCl (GL (Fin (Δ.len * Δ.d)) k))
      (Ψ : GrothGL k ≃+ MvPolynomial (Segment k) ℤ),
      IsSegmentClass k Z ∧ IsProductIso k Ψ ∧
        ∀ Δ, Ψ (Finsupp.single ⟨Δ.len * Δ.d, Z Δ⟩ 1) = MvPolynomial.X Δ

end Published

namespace SmGL

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Geometric

variable {α β n : Type} [Fintype α] [LinearOrder α] [Fintype β] [LinearOrder β] [Fintype n]
  [DecidableEq n] {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  {m' : β → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)]

instance : Finite (SizeMatrix m m') :=
  Finite.of_injective (fun (b : SizeMatrix m m') (i : α) (j : β) =>
    (⟨b.1 i j, Nat.lt_succ_of_le (b.2.1 i ▸
      Finset.single_le_sum (f := b.1 i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))⟩ :
        Fin (Fintype.card (m i) + 1)))
    fun _ _ h => Subtype.ext (funext fun i => funext fun j =>
      congrArg Fin.val (congrFun (congrFun h i) j))

theorem JacquetOfInducedFiltration.jhMult_eq (h : JacquetOfInducedFiltration k)
    [Fintype (SizeMatrix m m')] (e : (Σ i, m i) ≃ n) (e' : (Σ j, m' j) ≃ n)
    {W : Type} [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ (Levi k m) W} (hρ : IsSmooth ρ)
    (f : ∀ (b : SizeMatrix m m') i, (Σ j, Fin (b.1 i j)) ≃ m i)
    (g : ∀ (b : SizeMatrix m m') j, (Σ i, Fin (b.1 i j)) ≃ m' j)
    {Y : Type} [AddCommGroup Y] [Module ℂ Y] {τ : Representation ℂ (Levi k m') Y}
    (hτ : τ.IsIrreducible) :
    jhMult τ (jac e' (parInd e ρ)) = ∑ b, jhMult τ (cellFunctor (f b) (g b) ρ) := by
  obtain ⟨N, b, hb⟩ := h α β n m m' e e'
  obtain ⟨S, h1, h2, h3, h4⟩ := hb W ρ hρ
  exact (jhMult_filtration hτ S h1 h2 h3).trans (Fintype.sum_equiv b _ _ fun t =>
    (h4 t (f (b t)) (g (b t))).elim fun φ => jhMult_congr_right τ φ)

theorem exists_cell_of_isSubquotient (h : JacquetOfInducedFiltration k) (h' : CellSemisimplification k)
    (e : (Σ i, m i) ≃ n) (e' : (Σ j, m' j) ≃ n)
    {X : α → Type} [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]
    {ρ : ∀ i, Representation ℂ (GL (m i) k) (X i)} (hρ : ∀ i, IsSmooth (ρ i))
    (hl : ∀ i, HasFiniteLength (ρ i)) {Y : Type} [AddCommGroup Y] [Module ℂ Y]
    {τ : Representation ℂ (Levi k m') Y} (hτ : τ.IsIrreducible)
    (hs : IsSubquotient τ (jac e' (multiProd e ρ))) :
    ∃ (b : SizeMatrix m m') (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ m i)
      (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ m' j) (s : ∀ i j, IrrRep (GL (Fin (b.1 i j)) k)),
      (∀ i, IsSubquotient (piTensor fun j => (s i j).ρ) (jac (f i) (ρ i))) ∧
        IsSubquotient τ (piTensor fun j => multiProd (g j) fun i => (s i j).ρ) := by
  have := Fintype.ofFinite (SizeMatrix m m')
  have h0 := jhMult_ne_zero_iff.2 hs
  rw [multiProd, h.jhMult_eq e e' (isSmooth_piTensor hρ) (fun b => b.nonempty_rows.some)
    (fun b => b.nonempty_cols.some) hτ] at h0
  obtain ⟨b, -, hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero h0
  obtain ⟨T, -, hT⟩ := h' α β m m' _ b.nonempty_rows.some b.nonempty_cols.some X ρ hρ hl
  rw [hT ⟨Y, τ, hs.isSmooth (isSmooth_jac _ (isSmooth_parInd _ _)), hτ⟩] at hb
  obtain ⟨s, -, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero hb
  exact ⟨b, _, _, fun i j => (s i j).rep, fun i => jhMult_ne_zero_iff.1
    (Finset.prod_ne_zero_iff.1 (left_ne_zero_of_mul hs) i (Finset.mem_univ i)),
    jhMult_ne_zero_iff.1 (right_ne_zero_of_mul hs)⟩

end Geometric

section RingConsequences

variable {V W U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup U] [Module ℂ U]

theorem clsGL_irr {n : ℕ} (σ : IrrRep (GL (Fin n) k)) (h : HasFiniteLength σ.ρ) :
    clsGL σ.ρ h = Finsupp.single ⟨n, σ.cl⟩ 1 := by
  rw [clsGL, cls_irr, Finsupp.mapDomain_single]

theorem clsGL_apply {n : ℕ} (π : Representation ℂ (GL (Fin n) k) V) (h : HasFiniteLength π)
    (c : IrrCl (GL (Fin n) k)) : clsGL π h ⟨n, c⟩ = cls π h c :=
  Finsupp.mapDomain_apply sigma_mk_injective _ _

theorem clsGL_congr {n : ℕ} {π : Representation ℂ (GL (Fin n) k) V}
    {τ : Representation ℂ (GL (Fin n) k) W} (φ : π.Equiv τ) (h : HasFiniteLength π)
    (h' : HasFiniteLength τ) : clsGL π h = clsGL τ h' := by
  rw [clsGL, clsGL, cls_congr φ h h']

variable {A : Type 1} [CommRing A] {Ψ : GrothGL k ≃+ A}

theorem IsProductIso.comm (hΨ : IsProductIso k Ψ) {r t : ℕ} {π₁ : Representation ℂ (GL (Fin r) k) V}
    {π₂ : Representation ℂ (GL (Fin t) k) W} (h₁ : HasFiniteLength π₁) (h₂ : HasFiniteLength π₂)
    (s₁ : IsSmooth π₁) (s₂ : IsSmooth π₂) :
    ∃ h h', clsGL (prod₂ π₁ π₂) h = clsGL (prod₂ π₂ π₁) h' := by
  obtain ⟨h, e⟩ := hΨ.2 r t V W π₁ π₂ h₁ h₂ s₁ s₂
  obtain ⟨h', e'⟩ := hΨ.2 t r W V π₂ π₁ h₂ h₁ s₂ s₁
  exact ⟨h, h', Ψ.injective (by rw [e, e', mul_comm])⟩

theorem IsProductIso.cancel [IsDomain A] (hΨ : IsProductIso k Ψ) {r t : ℕ}
    (π₁ π₂ : IrrRep (GL (Fin r) k)) (τ : IrrRep (GL (Fin t) k))
    (φ : (prod₂ π₁.ρ τ.ρ).Equiv (prod₂ π₂.ρ τ.ρ)) : Nonempty (π₁.ρ.Equiv π₂.ρ) := by
  obtain ⟨h, e⟩ := hΨ.2 r t _ _ π₁.ρ τ.ρ π₁.hasFiniteLength τ.hasFiniteLength π₁.smooth τ.smooth
  obtain ⟨h', e'⟩ := hΨ.2 r t _ _ π₂.ρ τ.ρ π₂.hasFiniteLength τ.hasFiniteLength π₂.smooth τ.smooth
  have h0 : Ψ (clsGL τ.ρ τ.hasFiniteLength) ≠ 0 := by
    rw [clsGL_irr, map_ne_zero_iff _ Ψ.injective]
    exact Finsupp.single_ne_zero.2 one_ne_zero
  rw [clsGL_congr φ h h', e'] at e
  have h1 := Ψ.injective (mul_right_cancel₀ h0 e)
  rw [clsGL_irr, clsGL_irr, Finsupp.single_left_inj one_ne_zero] at h1
  exact IrrRep.cl_eq_iff.1 (sigma_mk_injective (β := fun n => IrrCl (GL (Fin n) k)) h1).symm

end RingConsequences

section Characters

variable {n : Type} [Fintype n] [DecidableEq n] {l : ℕ}

theorem nonempty_jac_det_equiv (e : (Σ _ : Fin l, Fin 1) ≃ n) (χ : kˣ →* ℂˣ) :
    Nonempty ((jac e (detRep n (χ * absPow k (((l : ℂ) - 1) / 2)))).Equiv
      (piTensor (segTerm (detRep (Fin 1) χ) l))) := by
  refine ⟨.mk ((Submodule.quotEquivOfEqBot _ (twKer_detRep e _)).trans
    (PiTensorProduct.constantBaseRingEquiv (Fin l) ℂ).toLinearEquiv.symm) fun g => ?_⟩
  have key : ∀ y, piTensor (segTerm (detRep (Fin 1) χ) l) g y =
      (detLevi e (χ * absPow k (((l : ℂ) - 1) / 2)) g : ℂ) • y := by
    intro y
    induction y using PiTensorProduct.induction_on with
    | add x y hx hy => rw [map_add, hx, hy, smul_add]
    | smul_tprod c x =>
      rw [map_smul, smul_comm, piTensor_tprod, detLevi_apply, Units.coe_prod,
        ← MultilinearMap.map_smul_univ]
      congr 2
      funext i
      rw [modExp_fin _ (fun _ => by simp), mul_assoc, ← absPow_add,
        show ((l : ℂ) - 1) / 2 + -(((l : ℤ) - 1 - 2 * ((i : ℕ) : ℤ) : ℤ) : ℂ) / 2 = ((i : ℕ) : ℂ) by
          push_cast; ring]
      simp [segTerm, detRep, mul_left_comm, mul_assoc]
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply]
  rw [key, Model.jac_detRep, map_smul]

theorem exists_det_embedding (e : (Σ _ : Fin l, Fin 1) ≃ n) {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) :
    ∃ φ : (detRep n (χ * absPow k (((l : ℂ) - 1) / 2))).IntertwiningMap
      (multiProd e (segTerm (detRep (Fin 1) χ) l)), Function.Injective φ := by
  obtain ⟨ψ⟩ := nonempty_jac_det_equiv e χ
  obtain ⟨φ, hφ⟩ := (Model.evalOne_bijective e ((isSmooth_ofChar_iff _).2
    (hχ.mul (isSmoothChar_of_isUnram (isUnram_absPow k _))).detChar) _).2 ψ.toIntertwiningMap
  refine ⟨φ, (injective_iff_map_eq_zero _).2 fun v hv => ?_⟩
  have h1 : ψ (Submodule.Quotient.mk v) = (φ v).1.1 1 :=
    (congrArg (fun F => F (Submodule.Quotient.mk v)) hφ).symm
  replace h1 : ψ (Submodule.Quotient.mk v) = 0 := h1.trans (congrArg (fun F => F.1.1 1) hv)
  have h2 : v ∈ twKer (detRep n (χ * absPow k (((l : ℂ) - 1) / 2))) (unipRad k e) 1 :=
    (Submodule.Quotient.mk_eq_zero _).1 ((map_eq_zero_iff ψ ψ.injective).1 h1)
  rwa [twKer_detRep] at h2

theorem IsSegmentClass.ofChar {Z : ∀ Δ : Segment k, IrrCl (GL (Fin (Δ.len * Δ.d)) k)}
    (hZ : IsSegmentClass k Z) {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) (hl : 0 < l) :
    Z (Segment.ofChar χ hχ l hl) = (IrrRep.det (Fin (l * 1)) (χ * absPow k (((l : ℂ) - 1) / 2))
      (hχ.mul (isSmoothChar_of_isUnram (isUnram_absPow k _)))).cl := by
  let e : (Σ _ : Fin l, Fin 1) ≃ Fin (l * 1) := Fintype.equivOfCardEq (by simp)
  have h1 := (hZ (Segment.ofChar χ hχ l hl) (IrrRep.det (Fin 1) χ hχ) rfl e
    (IrrRep.det (Fin (l * 1)) (χ * absPow k (((l : ℂ) - 1) / 2))
      (hχ.mul (isSmoothChar_of_isUnram (isUnram_absPow k _))))).2
  exact (h1.2 (nonempty_jac_det_equiv (l := l) (n := Fin (l * 1)) e χ)).symm

example : Function.Injective fun l : ℕ =>
    Segment.ofChar (1 : kˣ →* ℂˣ) isSmoothChar_one (l + 1) l.succ_pos :=
  fun _ _ h => Nat.succ_injective (congrArg Segment.len h)

example : ∃ b b' : SizeMatrix (fun _ : Fin 2 => Fin 1) (fun _ : Fin 2 => Fin 1), b ≠ b' :=
  ⟨⟨![![1, 0], ![0, 1]], by decide⟩, ⟨![![0, 1], ![1, 0]], by decide⟩, fun h =>
    absurd (congrArg (fun b => b.1 0 0) h) (by decide)⟩

end Characters

end SmGL

end GlobalTheory
