import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ExistsPrimeFiltrationOfIsMultiHomogIdeal

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

attribute [local instance 2000] lexDecEq
attribute [local instance] MvPolynomial.weightedGradedAlgebra

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def lexDeg (a : K → ℕ) : Lex (Fin (Fintype.card K) → ℕ) := toLex (a ∘ (Fintype.equivFin K).symm)

theorem lexDeg_add (a b : K → ℕ) : lexDeg (a + b) = lexDeg a + lexDeg b := rfl

variable (ι) in

abbrev grL : Lex (Fin (Fintype.card K) → ℕ) → Submodule ℤ (MRing ι) :=
  weightedHomogeneousSubmodule ℤ (lexW (ι := ι) (Fintype.equivFin K))

theorem mem_grL_iff (f : MRing ι) (a : K → ℕ) : f ∈ grL ι (lexDeg a) ↔ IsMultiHomog f a := by
  constructor
  · intro h
    have := isMultiHomog_of_mem_lex _ h
    convert this using 1
    funext k
    simp [lexDeg]
  · exact mem_lex_of_isMultiHomog _

theorem mHom_eq (a : K → ℕ) : mHom ι a = grL ι (lexDeg a) := by
  rw [mHom]
  have : {s : MRing ι | IsMultiHomog s a} = (grL ι (lexDeg a) : Set (MRing ι)) := by
    ext s
    exact (mem_grL_iff s a).symm
  rw [this, Submodule.span_eq]

theorem mem_mHom_iff (f : MRing ι) (a : K → ℕ) : f ∈ mHom ι a ↔ IsMultiHomog f a := by
  rw [mHom_eq, mem_grL_iff]

theorem isHomogeneous_grL {J : Ideal (MRing ι)} (hJ : IsMultiHomogIdeal J) :
    J.IsHomogeneous (grL ι) := (isHomogeneous_lex_iff _ J).mpr hJ

def pieceMap (J : Ideal (MRing ι)) (a : K → ℕ) : mHom ι a →ₗ[ℤ] MRing ι ⧸ J :=
  (Ideal.Quotient.mkₐ ℤ J).toLinearMap ∘ₗ (mHom ι a).subtype

theorem range_pieceMap (J : Ideal (MRing ι)) (a : K → ℕ) :
    LinearMap.range (pieceMap J a) = mPiece J a := by
  rw [pieceMap, LinearMap.range_comp, Submodule.range_subtype]
  rfl

theorem mem_ker_pieceMap (J : Ideal (MRing ι)) (a : K → ℕ) (x : mHom ι a) :
    x ∈ LinearMap.ker (pieceMap J a) ↔ (x : MRing ι) ∈ J := by
  simp [pieceMap, Ideal.Quotient.eq_zero_iff_mem]

theorem card_mPiece_eq (J : Ideal (MRing ι)) (a : K → ℕ) :
    Nat.card (mPiece J a) = Nat.card (mHom ι a ⧸ LinearMap.ker (pieceMap J a)) := by
  rw [← range_pieceMap]
  exact Nat.card_congr (LinearMap.quotKerEquivRange _).toEquiv.symm

theorem card_quot_chain {R V : Type*} [Ring R] [AddCommGroup V] [Module R V] (A B : Submodule R V)
    (h : A ≤ B) :
    Nat.card (V ⧸ A) = Nat.card (V ⧸ B) * Nat.card (B ⧸ A.comap B.subtype) := by
  have h1 := Submodule.card_eq_card_quotient_mul_card (B.map A.mkQ)
  have e1 : Nat.card ((V ⧸ A) ⧸ B.map A.mkQ) = Nat.card (V ⧸ B) :=
    Nat.card_congr (Submodule.quotientQuotientEquivQuotient A B h).toEquiv
  let φ : B →ₗ[R] V ⧸ A := A.mkQ ∘ₗ B.subtype
  have hr : LinearMap.range φ = B.map A.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hk : LinearMap.ker φ = A.comap B.subtype := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have e2 : Nat.card (B.map A.mkQ) = Nat.card (B ⧸ A.comap B.subtype) := by
    rw [← hr, ← hk]
    exact Nat.card_congr (LinearMap.quotKerEquivRange φ).toEquiv.symm
  rw [h1, e1, e2]
  ring

theorem isMultiHomog_mul {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := by
  rw [← mem_grL_iff] at hf hg ⊢
  rw [lexDeg_add]
  exact SetLike.GradedMul.mul_mem hf hg

theorem card_mPiece_step {J : Ideal (MRing ι)} (hJ : IsMultiHomogIdeal J) {f : MRing ι} {c : K → ℕ}
    (hf : IsMultiHomog f c) {q : Ideal (MRing ι)} (hq : ∀ g, g ∈ q ↔ g * f ∈ J) {a : K → ℕ}
    (hca : ∀ k, c k ≤ a k) :
    Nat.card (mPiece J a) = Nat.card (mPiece (J ⊔ Ideal.span {f}) a) * Nat.card (mPiece q (a - c)) := by
  classical
  set J' := J ⊔ Ideal.span {f}
  have hJJ' : J ≤ J' := le_sup_left
  set A := LinearMap.ker (pieceMap J a)
  set B := LinearMap.ker (pieceMap J' a)
  have hAB : A ≤ B := fun x hx => by
    rw [mem_ker_pieceMap] at hx ⊢
    exact hJJ' hx
  rw [card_mPiece_eq, card_mPiece_eq, card_mPiece_eq, card_quot_chain A B hAB]
  congr 1
  have hac : a - c + c = a := funext fun k => Nat.sub_add_cancel (hca k)
  have hmul : ∀ g : mHom ι (a - c), (g : MRing ι) * f ∈ mHom ι a := fun g => by
    rw [mem_mHom_iff]
    have := isMultiHomog_mul ((mem_mHom_iff _ _).mp g.2) hf
    rwa [hac] at this
  let χ' : mHom ι (a - c) →ₗ[ℤ] B :=
    { toFun := fun g => ⟨⟨(g : MRing ι) * f, hmul g⟩, by
        rw [mem_ker_pieceMap]
        exact Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self f))⟩
      map_add' := fun g h => by ext; simp [add_mul]
      map_smul' := fun r g => by ext; simp [mul_assoc] }
  let χ := (A.comap B.subtype).mkQ ∘ₗ χ'
  have hsurj : Function.Surjective χ := by
    intro z
    obtain ⟨⟨⟨x, hxa⟩, hxB⟩, rfl⟩ := Submodule.mkQ_surjective _ z
    have hxJ' : x ∈ J' := (mem_ker_pieceMap J' a ⟨x, hxa⟩).mp hxB
    obtain ⟨j, hj, y, hy, hjx⟩ := Submodule.mem_sup.mp hxJ'
    obtain ⟨h, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    have hf' : f ∈ grL ι (lexDeg c) := (mem_grL_iff f c).mpr hf
    set g := (DirectSum.decompose (grL ι) h (lexDeg (a - c)) : MRing ι)
    have hg : g ∈ mHom ι (a - c) := by
      rw [mHom_eq]
      exact SetLike.coe_mem _
    refine ⟨⟨g, hg⟩, ?_⟩
    have hx : x = (DirectSum.decompose (grL ι) j (lexDeg a) : MRing ι) + g * f := by
      have h1 : x ∈ grL ι (lexDeg a) := by rw [← mHom_eq]; exact hxa
      conv_lhs => rw [← DirectSum.decompose_of_mem_same (grL ι) h1, ← hjx]
      rw [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add]
      congr 1
      rw [← hac, lexDeg_add, DirectSum.coe_decompose_mul_add_of_right_mem (grL ι) hf']
    have hjc : (DirectSum.decompose (grL ι) j (lexDeg a) : MRing ι) ∈ J := isHomogeneous_grL hJ _ hj
    show (A.comap B.subtype).mkQ (χ' ⟨g, hg⟩) = (A.comap B.subtype).mkQ ⟨⟨x, hxa⟩, hxB⟩
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, Submodule.mem_comap,
      Submodule.coe_subtype, mem_ker_pieceMap]
    have : (((χ' ⟨g, hg⟩ - ⟨⟨x, hxa⟩, hxB⟩ : B) : mHom ι a) : MRing ι) = g * f - x := rfl
    rw [this, hx, show g * f - ((DirectSum.decompose (grL ι) j (lexDeg a) : MRing ι) + g * f) =
      -(DirectSum.decompose (grL ι) j (lexDeg a) : MRing ι) by ring]
    exact J.neg_mem hjc
  have hker : LinearMap.ker χ = LinearMap.ker (pieceMap q (a - c)) := by
    ext g
    rw [LinearMap.mem_ker, mem_ker_pieceMap, hq]
    show (A.comap B.subtype).mkQ (χ' g) = 0 ↔ _
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype,
      mem_ker_pieceMap]
    rfl
  rw [← hker]
  exact Nat.card_congr (LinearMap.quotKerEquivOfSurjective χ hsurj).toEquiv.symm

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
