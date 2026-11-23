import Mathlib
import ReciprocityTheory.DualLattices.CotangentSurjective
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.QuotientByFiniteFlatStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.ZarhinStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateDatumStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.OrdinaryCurveStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.PolarisedFlagStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AbFactorProdRetract
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsAddEquiv
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrdersOfZmodPExtremesStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TensorProductHopfOrdersStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TensorProductTightHopfOrdersStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TorsionPointsHopfOrderStatement

noncomputable section

namespace PositivityTheory.HtPt.Stight.BadRed

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

section Transport

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
  {N N' : Type} [AddCommGroup N] [AddCommGroup N']

def tr (e : N ≃+ N') : (N → C) ≃ₗ[R] (N' → C) where
  toFun f := fun y => f (e.symm y)
  invFun g := fun x => g (e x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv f := by ext x; simp
  right_inv g := by ext y; simp

def trS (M : Submodule R (N → C)) (e : N ≃+ N') : Submodule R (N' → C) :=
  M.map (tr e : (N → C) ≃ₗ[R] (N' → C)).toLinearMap

theorem mem_trS (M : Submodule R (N → C)) (e : N ≃+ N') (g : N' → C) :
    g ∈ trS M e ↔ (fun x => g (e x)) ∈ M := by
  constructor
  · rintro ⟨f, hf, rfl⟩
    simpa [tr] using hf
  · intro h
    exact ⟨_, h, by ext y; simp [tr]⟩

theorem trS_intFun (e : N ≃+ N') : trS (intFun (C := C) R N) e = intFun R N' := by
  ext g
  rw [mem_trS]
  constructor
  · intro h y
    simpa using h (e.symm y)
  · intro h x
    exact h (e x)

theorem trS_addFun (q : ℕ) (e : N ≃+ N') : trS (addFun (C := C) R q N) e = addFun R q N' := by
  ext g
  rw [mem_trS]
  constructor
  · intro h x y
    simpa using h (e.symm x) (e.symm y)
  · intro h x y
    simpa using h (e x) (e y)

theorem trS_pFun (q : ℕ) (e : N ≃+ N') : trS (pFun (C := C) R q N) e = pFun R q N' := by
  ext g
  rw [mem_trS]
  simp only [pFun, Submodule.mem_pi, Set.mem_univ, true_imp_iff]
  constructor
  · intro h y
    simpa using h (e.symm y)
  · intro h x
    exact h (e x)

theorem trS_inf (M M' : Submodule R (N → C)) (e : N ≃+ N') :
    trS (M ⊓ M') e = trS M e ⊓ trS M' e := by
  ext g
  simp only [Submodule.mem_inf, mem_trS]

theorem trS_sup (M M' : Submodule R (N → C)) (e : N ≃+ N') :
    trS (M ⊔ M') e = trS M e ⊔ trS M' e := by
  simp only [trS, Submodule.map_sup]

theorem trS_augIdeal (M : Submodule R (N → C)) (e : N ≃+ N') :
    trS (augIdeal M) e = augIdeal (trS M e) := by
  ext g
  simp only [augIdeal, Submodule.mem_inf, mem_trS, LinearMap.mem_ker, LinearMap.proj_apply,
    map_zero]

theorem trS_sqIdeal (I : Submodule R (N → C)) (e : N ≃+ N') :
    trS (sqIdeal I) e = sqIdeal (trS I e) := by
  simp only [trS, sqIdeal, Submodule.map_span]
  congr 1
  ext h
  constructor
  · rintro ⟨_, ⟨f, hf, f', hf', rfl⟩, rfl⟩
    exact ⟨_, Submodule.mem_map_of_mem hf, _, Submodule.mem_map_of_mem hf', by ext y; simp [tr]⟩
  · rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨a * b, ⟨a, ha, b, hb, rfl⟩, by ext y; simp [tr]⟩

def subquotEquiv {V V' : Type} [AddCommGroup V] [AddCommGroup V'] [Module R V] [Module R V']
    (Φ : V ≃ₗ[R] V') (A B : Submodule R V) (A' B' : Submodule R V')
    (hA : A.map Φ.toLinearMap = A') (hB : B.map Φ.toLinearMap = B') :
    (A ⧸ B.comap A.subtype) ≃ₗ[R] (A' ⧸ B'.comap A'.subtype) := by
  subst hA hB
  refine Submodule.Quotient.equiv _ _ (LinearEquiv.ofSubmodules Φ A _ rfl) ?_
  ext ⟨y, hy⟩
  constructor
  · rintro ⟨⟨x, hx⟩, hxB, h⟩
    have h' : Φ x = y := congrArg Subtype.val h
    exact ⟨x, hxB, h'⟩
  · rintro ⟨x, hxB, rfl⟩
    obtain ⟨x', hx', h'⟩ := hy
    have : x' = x := Φ.injective h'
    subst this
    exact ⟨⟨x', hx'⟩, hxB, rfl⟩

theorem hasLen_of_equiv {v : Valuation C NNReal} {X Y : Type} [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] (E : X ≃ₗ[R] Y) {c : NNReal} (h : HasLen v R X c) :
    HasLen v R Y c := by
  obtain ⟨m, d, ⟨f⟩, hd⟩ := h
  exact ⟨m, d, ⟨E.symm.trans f⟩, hd⟩

variable [Fintype N] [DecidableEq N] [Fintype N'] [DecidableEq N']

theorem trS_cols (B : Matrix N N C) (e : N ≃+ N') :
    trS (Submodule.span R (Set.range fun j x => B x j)) e =
      Submodule.span R (Set.range fun j x => (B.submatrix e.symm e.symm) x j) := by
  simp only [trS, Submodule.map_span]
  congr 1
  ext h
  constructor
  · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
    exact ⟨e j, by ext y; simp [tr]⟩
  · rintro ⟨j, rfl⟩
    exact ⟨_, ⟨e.symm j, rfl⟩, by ext y; simp [tr]⟩

theorem isLat_trS {M : Submodule R (N → C)} (e : N ≃+ N') (h : IsLat R M) :
    IsLat R (trS M e) := by
  obtain ⟨B, hB, rfl⟩ := h
  refine ⟨B.submatrix e.symm e.symm, ?_, trS_cols B e⟩
  rw [show (B.submatrix e.symm e.symm) = B.submatrix e.symm.toEquiv e.symm.toEquiv from rfl,
    Matrix.det_submatrix_equiv_self]
  exact hB

theorem hasColen_trS {v : Valuation C NNReal} {M : Submodule R (N → C)} (e : N ≃+ N') {c : NNReal}
    (h : HasColen R v M c) : HasColen R v (trS M e) c := by
  obtain ⟨B, rfl, hB⟩ := h
  refine ⟨B.submatrix e.symm e.symm, trS_cols B e, ?_⟩
  rw [show (B.submatrix e.symm e.symm) = B.submatrix e.symm.toEquiv e.symm.toEquiv from rfl,
    Matrix.det_submatrix_equiv_self]
  exact hB

theorem isTight_trS {v : Valuation C NNReal} {q : ℕ} {M : Submodule R (N → C)} (e : N ≃+ N')
    (h : IsTight v q M) : IsTight v q (trS M e) := by
  obtain ⟨cA, cN, cO, h1, h2, h3, h4, h5⟩ := h
  have hcard : Fintype.card N = Fintype.card N' := Fintype.card_congr e.toEquiv
  refine ⟨cA, cN, cO, ?_, hasColen_trS e h2, ?_, ?_, ?_⟩
  · refine hasLen_of_equiv (subquotEquiv (tr e) _ _ _ _ ?_ ?_) h1
    · exact (trS_inf _ _ e).trans (by rw [trS_intFun, trS_addFun]; rfl)
    · exact (trS_sup _ _ e).trans (by
        rw [trS_pFun, show afFun q M = M ⊓ addFun R q N from rfl, trS_inf, trS_addFun]; rfl)
  · refine hasLen_of_equiv (subquotEquiv (tr e) _ _ _ _ ?_ ?_) h3
    · exact trS_augIdeal M e
    · exact (trS_sqIdeal _ e).trans (by rw [trS_augIdeal])
  · rw [← hcard]; exact h4
  · rw [← hcard]; exact h5

theorem hopf_trS (AA : HopfOrder (C := C) R N) (e : N ≃+ N') :
    ∃ AA' : HopfOrder (C := C) R N', AA'.carrier = trS AA.carrier e := by
  refine ⟨⟨trS AA.carrier e, isLat_trS e AA.lat, ?_, ?_, ?_, ?_, ?_⟩, rfl⟩
  · rw [← trS_intFun e]
    exact Submodule.map_mono AA.le_int
  · rw [mem_trS]; exact AA.one_mem
  · intro f g hf hg
    rw [mem_trS] at *
    exact AA.mul_mem _ _ hf hg
  · intro f hf
    rw [mem_trS] at hf
    have h := AA.comul _ hf
    have key : ∀ F ∈ tensorSpan R AA.carrier,
        (fun q : N' × N' => F (e.symm q.1, e.symm q.2)) ∈ tensorSpan R (trS AA.carrier e) := by
      intro F hF
      induction hF using Submodule.span_induction with
      | mem F hF =>
        obtain ⟨g, hg, h, hh, rfl⟩ := hF
        refine Submodule.subset_span ⟨fun y => g (e.symm y), ?_, fun y => h (e.symm y), ?_, rfl⟩
        · rw [mem_trS]; simpa using hg
        · rw [mem_trS]; simpa using hh
      | zero => exact Submodule.zero_mem _
      | add F G _ _ hF hG => exact Submodule.add_mem _ hF hG
      | smul c F _ hF => exact Submodule.smul_mem _ c hF
    have := key _ h
    convert this using 1
    ext q
    simp [addPull, LinearMap.funLeft]
  · intro f hf
    rw [mem_trS] at *
    simpa using AA.antipode _ hf

end Transport

section Lattices

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

def charLat (R : Type) [CommRing R] [Algebra R C] (N : Type) [AddCommGroup N] :
    Submodule R (N → C) :=
  Submodule.span R (Set.range fun (ψ : AddChar N C) (x : N) => ψ x)

theorem trS_charLat {N N' : Type} [AddCommGroup N] [AddCommGroup N'] (e : N ≃+ N') :
    trS (charLat (C := C) R N) e = charLat R N' := by
  simp only [trS, charLat, Submodule.map_span]
  congr 1
  ext h
  constructor
  · rintro ⟨_, ⟨ψ, rfl⟩, rfl⟩
    exact ⟨ψ.compAddMonoidHom e.symm.toAddMonoidHom, by ext y; simp [tr]⟩
  · rintro ⟨ψ, rfl⟩
    exact ⟨_, ⟨ψ.compAddMonoidHom e.toAddMonoidHom, rfl⟩, by ext y; simp [tr]⟩

theorem charLat_prod (N₁ N₂ : Type) [AddCommGroup N₁] [AddCommGroup N₂] :
    charLat (C := C) R (N₁ × N₂) = tens (charLat R N₁) (charLat R N₂) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨ψ, rfl⟩
    refine Submodule.subset_span ⟨_, Submodule.subset_span
      ⟨ψ.compAddMonoidHom (AddMonoidHom.inl N₁ N₂), rfl⟩, _, Submodule.subset_span
      ⟨ψ.compAddMonoidHom (AddMonoidHom.inr N₁ N₂), rfl⟩, ?_⟩
    ext z
    simp only [AddChar.compAddMonoidHom_apply, AddMonoidHom.inl_apply, AddMonoidHom.inr_apply,
      ← AddChar.map_add_eq_mul]
    simp
  · have key : ∀ g ∈ charLat (C := C) R N₁, ∀ h ∈ charLat (C := C) R N₂,
        (fun z : N₁ × N₂ => g z.1 * h z.2) ∈ charLat (C := C) R (N₁ × N₂) := by
      intro g hg h hh
      induction hg using Submodule.span_induction with
      | mem g hg =>
        obtain ⟨ψ₁, rfl⟩ := hg
        induction hh using Submodule.span_induction with
        | mem h hh =>
          obtain ⟨ψ₂, rfl⟩ := hh
          refine Submodule.subset_span ⟨⟨fun z => ψ₁ z.1 * ψ₂ z.2, by simp, ?_⟩, rfl⟩
          intro a b
          simp only [Prod.fst_add, Prod.snd_add, AddChar.map_add_eq_mul]
          ring
        | zero =>
          convert Submodule.zero_mem (charLat (C := C) R (N₁ × N₂)) using 1
          ext z; simp
        | add a b _ _ ha hb =>
          convert Submodule.add_mem _ ha hb using 1
          ext z; simp [mul_add]
        | smul c a _ ha =>
          convert Submodule.smul_mem _ c ha using 1
          ext z; simp [Algebra.smul_def]; ring
      | zero =>
        convert Submodule.zero_mem (charLat (C := C) R (N₁ × N₂)) using 1
        ext z; simp
      | add a b _ _ ha hb =>
        convert Submodule.add_mem _ ha hb using 1
        ext z; simp [add_mul]
      | smul c a _ ha =>
        convert Submodule.smul_mem _ c ha using 1
        ext z; simp [Algebra.smul_def]; ring
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, hg, h, hh, rfl⟩
    exact key g hg h hh

theorem intFun_prod (N₁ N₂ : Type) [Fintype N₁] [DecidableEq N₁] [Fintype N₂] [DecidableEq N₂] :
    intFun (C := C) R (N₁ × N₂) = tens (intFun R N₁) (intFun R N₂) := by
  apply le_antisymm
  · intro f hf
    choose r hr using hf
    have hδ : ∀ {X : Type} [DecidableEq X] (a : X),
        (fun x => if x = a then (1 : C) else 0) ∈ intFun (C := C) R X := by
      intro X _ a x
      by_cases h : x = a
      · exact ⟨1, by simp [h]⟩
      · exact ⟨0, by simp [h]⟩
    have hf' : f = ∑ z : N₁ × N₂, r z • (fun w : N₁ × N₂ =>
        (if w.1 = z.1 then (1 : C) else 0) * (if w.2 = z.2 then (1 : C) else 0)) := by
      ext w
      rw [Finset.sum_apply, Finset.sum_eq_single w]
      · simp [Algebra.smul_def, hr]
      · intro z _ hz
        have : ¬ (w.1 = z.1 ∧ w.2 = z.2) := fun h => hz (Prod.ext h.1.symm h.2.symm)
        by_cases h1 : w.1 = z.1
        · have h2 : ¬ w.2 = z.2 := fun h2 => this ⟨h1, h2⟩
          simp [h2]
        · simp [h1]
      · simp
    rw [hf']
    exact Submodule.sum_mem _ fun z _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨_, hδ z.1, _, hδ z.2, rfl⟩)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨g, hg, h, hh, rfl⟩ z
    obtain ⟨a, ha⟩ := hg z.1
    obtain ⟨b, hb⟩ := hh z.2
    exact ⟨a * b, by simp [ha, hb]⟩

variable {Z : Type} [AddCommGroup Z] [Fintype Z] [DecidableEq Z] [Subsingleton Z]

theorem intFun_eq_cols :
    intFun (C := C) R Z = Submodule.span R (Set.range fun j x => (1 : Matrix Z Z C) x j) := by
  apply le_antisymm
  · intro f hf
    obtain ⟨r, hr⟩ := hf 0
    have : f = r • (fun x => (1 : Matrix Z Z C) x 0) := by
      ext x
      have hx : x = 0 := Subsingleton.elim _ _
      subst hx
      simp [Algebra.smul_def, hr]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨j, rfl⟩ x
    obtain rfl : x = j := Subsingleton.elim _ _
    exact ⟨1, by simp⟩

theorem charLat_trivial : charLat (C := C) R Z = intFun R Z := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨ψ, rfl⟩ x
    exact ⟨1, by simp [Subsingleton.elim x 0]⟩
  · intro f hf
    obtain ⟨r, hr⟩ := hf 0
    have : f = r • (fun x => (0 : AddChar Z C) x) := by
      ext x
      simp [Subsingleton.elim x 0, Algebra.smul_def, hr]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)

theorem hopf_trivial : ∃ AA : HopfOrder (C := C) R Z, AA.carrier = intFun R Z := by
  refine ⟨⟨intFun R Z, ⟨1, by simp, intFun_eq_cols⟩, le_rfl, fun _ => ⟨1, by simp⟩, ?_, ?_, ?_⟩, rfl⟩
  · intro f g hf hg x
    obtain ⟨a, ha⟩ := hf x
    obtain ⟨b, hb⟩ := hg x
    exact ⟨a * b, by simp [ha, hb]⟩
  · intro f hf
    obtain ⟨r, hr⟩ := hf 0
    have : addPull R Z f = r • (fun q : Z × Z => (1 : Z → C) q.1 * (1 : Z → C) q.2) := by
      ext q
      simp [addPull, LinearMap.funLeft, Subsingleton.elim (q.1 + q.2) 0, Algebra.smul_def, hr]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨1, fun _ => ⟨1, by simp⟩, 1, fun _ => ⟨1, by simp⟩, rfl⟩)
  · intro f hf x
    exact hf (-x)

theorem isTight_trivial (v : Valuation C NNReal) (q : ℕ) : IsTight v q (intFun (C := C) R Z) := by
  have hzero : ∀ (X : Type) [AddCommGroup X] [Module R X] [Subsingleton X], HasLen v R X 1 :=
    fun X _ _ _ => ⟨0, Fin.elim0, ⟨LinearEquiv.ofSubsingleton _ _⟩, by simp⟩
  have h1 : Subsingleton (AFQuot q (intFun (C := C) R Z)) := by
    refine Submodule.Quotient.subsingleton_iff.2 (eq_top_iff.2 ?_)
    rintro ⟨f, hf⟩ -
    exact Submodule.mem_sup_left ⟨hf.1, hf.2⟩
  have h2 : Subsingleton (OmAA (intFun (C := C) R Z)) := by
    refine Submodule.Quotient.subsingleton_iff.2 (eq_top_iff.2 ?_)
    rintro ⟨f, hf⟩ -
    have : f = 0 := by
      ext x
      have hx : x = 0 := Subsingleton.elim _ _
      subst hx
      exact hf.2
    subst this
    exact Submodule.zero_mem _
  refine ⟨1, 1, 1, hzero _, ⟨1, intFun_eq_cols, by simp⟩, hzero _, by simp, by simp⟩

end Lattices

section Main

variable (p : ℕ) [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  (v : Valuation C NNReal) {R : Type} [CommRing R] [Algebra R C]

def Good (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] (M : Submodule R (N → C)) : Prop :=
  (∃ AA : HopfOrder (C := C) R N, AA.carrier = M) ∧ IsAbFactor p M ∧ IsTight v p M

variable {p v}

theorem good_tens (hv : v.Integers R) (hp : v (p : C) < 1)
    {N₁ N₂ : Type} [AddCommGroup N₁] [Fintype N₁] [DecidableEq N₁]
    [AddCommGroup N₂] [Fintype N₂] [DecidableEq N₂]
    {M₁ : Submodule R (N₁ → C)} {M₂ : Submodule R (N₂ → C)}
    (k₁ : ∀ x : N₁, p • x = 0) (k₂ : ∀ x : N₂, p • x = 0)
    (g₁ : Good p v N₁ M₁) (g₂ : Good p v N₂ M₂) : Good p v (N₁ × N₂) (tens M₁ M₂) := by
  obtain ⟨⟨A₁, rfl⟩, f₁, t₁⟩ := g₁
  obtain ⟨⟨A₂, rfl⟩, f₂, t₂⟩ := g₂
  obtain ⟨AA, hAA, -⟩ := GlobalTheory.T.tensor_product_hopf_orders p C v R hv hp N₁ N₂ A₁ A₂
  exact ⟨⟨AA, hAA⟩, (GlobalTheory.CompanionTheory.Ar.GR.abFactor_prod_retract p C v R hv hp).1 _ _ _ _ f₁ f₂,
    GlobalTheory.T.tensor_product_tight_hopf_orders p C v R hv hp N₁ N₂ A₁ A₂ k₁ k₂ t₁ t₂⟩

theorem good_trS (hv : v.Integers R) (hp : v (p : C) < 1)
    {N N' : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
    [AddCommGroup N'] [Fintype N'] [DecidableEq N'] {M : Submodule R (N → C)} (e : N ≃+ N')
    (g : Good p v N M) : Good p v N' (trS M e) := by
  obtain ⟨⟨AA, rfl⟩, f, t⟩ := g
  refine ⟨hopf_trS AA e, ?_, isTight_trS e t⟩
  have h := (GlobalTheory.CompanionTheory.Ar.GR.abFactor_prod_retract p C v R hv hp).2 N' N AA.carrier e.symm.toAddMonoidHom e.toAddMonoidHom
    (fun x => by simp) (fun g hg => by simpa using hg) f
  have hm : (tr e : (N → C) ≃ₗ[R] (N' → C)).toLinearMap =
      LinearMap.funLeft R C (e.symm.toAddMonoidHom : N' → N) :=
    LinearMap.ext fun f => funext fun y => rfl
  rw [trS, hm]
  exact h

theorem isAbFactor_self {A : Over (Spec (CommRingCat.of R))} (gA : GrpObj A) (L : LB A.left)
    (ab : IsAbelianScheme A) (lb : L.IsLB) (am : Out.RelAmple A L) (T : TorsRep A p)
    {N : Type} [AddCommGroup N] {pt : N → (sp (R₀ := R) R ⟶ A)} (hpt : IsTorsPts A p pt) :
    IsAbFactor p (torsFun C T pt) := by
  refine ⟨A, gA, L, ab, lb, am, T, N, inferInstance, pt, hpt, AddMonoidHom.id N, AddMonoidHom.id N,
    fun _ => rfl, fun g hg => hg, ?_⟩
  have hm : LinearMap.funLeft R C ((AddMonoidHom.id N : N →+ N) : N → N) = LinearMap.id :=
    LinearMap.ext fun f => rfl
  rw [hm, Submodule.map_id]

theorem good_zmod (hv : v.Integers R) (hp : v (p : C) < 1)
    (hc : IsAdicComplete (Ideal.span {(p : R)}) R) (hOC : OrdinaryCurveStatement) :
    Good p v (ZMod p) (charLat (C := C) R (ZMod p)) ∧ Good p v (ZMod p) (intFun (C := C) R (ZMod p)) := by
  obtain ⟨A, gA, L, ab, lb, am, T, pt, hpt, hE⟩ := hOC p C v R hv hp hc
  obtain ⟨⟨Ae, ce, -, te, -⟩, ⟨Am, cm, -, -, tm, -⟩⟩ := GlobalTheory.T.hopf_orders_of_zmod_p_extremes p C v R hv hp
  have cm' : Am.carrier = charLat (C := C) R (ZMod p) := cm
  obtain ⟨AA, hAA, hl, hr, hsl, hsr, -⟩ := GlobalTheory.T.tensor_product_hopf_orders p C v R hv hp (ZMod p) (ZMod p) Am Ae
  have hf : IsAbFactor p AA.carrier := by
    rw [hAA, cm, ce, ← hE]
    exact isAbFactor_self gA L ab lb am T hpt
  have f₁ := (GlobalTheory.CompanionTheory.Ar.GR.abFactor_prod_retract p C v R hv hp).2 (ZMod p) (ZMod p × ZMod p) AA.carrier
    (AddMonoidHom.inl _ _) (AddMonoidHom.fst _ _) (fun _ => rfl) hsl hf
  have f₂ := (GlobalTheory.CompanionTheory.Ar.GR.abFactor_prod_retract p C v R hv hp).2 (ZMod p) (ZMod p × ZMod p) AA.carrier
    (AddMonoidHom.inr _ _) (AddMonoidHom.snd _ _) (fun _ => rfl) hsr hf
  rw [hl] at f₁
  rw [hr] at f₂
  exact ⟨⟨⟨Am, cm'⟩, cm' ▸ f₁, cm' ▸ tm⟩, ⟨⟨Ae, ce⟩, ce ▸ f₂, ce ▸ te⟩⟩

theorem good_trivial (hv : v.Integers R) (hp : v (p : C) < 1)
    (hc : IsAdicComplete (Ideal.span {(p : R)}) R) (hOC : OrdinaryCurveStatement)
    (Z : Type) [AddCommGroup Z] [Fintype Z] [DecidableEq Z] [Subsingleton Z] :
    Good p v Z (intFun (C := C) R Z) := by
  refine ⟨hopf_trivial, ?_, isTight_trivial v p⟩
  obtain ⟨⟨AA, hAA⟩, f, -⟩ := (good_zmod hv hp hc hOC).1
  rw [← hAA] at f
  have h := (GlobalTheory.CompanionTheory.Ar.GR.abFactor_prod_retract p C v R hv hp).2 Z (ZMod p) AA.carrier 0 0
    (fun _ => Subsingleton.elim _ _) ?_ f
  · convert h using 1
    apply le_antisymm
    · intro g hg
      obtain ⟨r, hr⟩ := hg 0
      refine ⟨r • 1, AA.carrier.smul_mem _ AA.one_mem, ?_⟩
      ext x
      simp [LinearMap.funLeft, Subsingleton.elim x 0, Algebra.smul_def, hr]
    · rintro _ ⟨g, hg, rfl⟩ x
      obtain ⟨r, hr⟩ := AA.le_int hg 0
      exact ⟨r, by simpa [LinearMap.funLeft] using hr⟩
  · intro g hg
    obtain ⟨r, hr⟩ := AA.le_int hg 0
    have : (fun x : ZMod p => g ((0 : Z →+ ZMod p) ((0 : ZMod p →+ Z) x))) = r • 1 := by
      ext x
      simp [Algebra.smul_def, hr]
    rw [this]
    exact AA.carrier.smul_mem _ AA.one_mem

def consEquiv (p d : ℕ) : (ZMod p × (Fin d → ZMod p)) ≃+ (Fin (d + 1) → ZMod p) where
  toFun z := Fin.cons z.1 z.2
  invFun f := (f 0, Fin.tail f)
  left_inv z := by simp
  right_inv f := by simp
  map_add' a b := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem good_pow (L : ∀ (N : Type) [AddCommGroup N], Submodule R (N → C))
    (hv : v.Integers R) (hp : v (p : C) < 1)
    (hprod : ∀ d, L (ZMod p × (Fin d → ZMod p)) = tens (L (ZMod p)) (L (Fin d → ZMod p)))
    (htr : ∀ (N N' : Type) [AddCommGroup N] [AddCommGroup N'] (e : N ≃+ N'), trS (L N) e = L N')
    (h₁ : Good p v (ZMod p) (L (ZMod p))) (h₀ : Good p v (Fin 0 → ZMod p) (L (Fin 0 → ZMod p)))
    (d : ℕ) : Good p v (Fin d → ZMod p) (L (Fin d → ZMod p)) := by
  induction d with
  | zero => exact h₀
  | succ d ih =>
    have h := good_tens hv hp (fun x => by simp) (fun x => by ext i; simp) h₁ ih
    rw [← hprod] at h
    have h' := good_trS hv hp (consEquiv p d) h
    rwa [htr] at h'

theorem good_of_killed (L : ∀ (N : Type) [AddCommGroup N], Submodule R (N → C))
    (hv : v.Integers R) (hp : v (p : C) < 1)
    (hprod : ∀ d, L (ZMod p × (Fin d → ZMod p)) = tens (L (ZMod p)) (L (Fin d → ZMod p)))
    (htr : ∀ (N N' : Type) [AddCommGroup N] [AddCommGroup N'] (e : N ≃+ N'), trS (L N) e = L N')
    (h₁ : Good p v (ZMod p) (L (ZMod p))) (h₀ : Good p v (Fin 0 → ZMod p) (L (Fin 0 → ZMod p)))
    (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] (hN : ∀ x : N, p • x = 0) :
    Good p v N (L N) := by
  letI : Module (ZMod p) N := AddCommGroup.zmodModule hN
  haveI h₂ : Module.Finite (ZMod p) N := Module.Finite.of_finite
  haveI h₃ : Module.Free (ZMod p) N := Module.Free.of_divisionRing _ _
  have b : Module.Basis (Fin (Module.finrank (ZMod p) N)) (ZMod p) N :=
    @Module.finBasis (ZMod p) N _ _ _ h₃ _ h₂
  have e : (Fin (Module.finrank (ZMod p) N) → ZMod p) ≃+ N := b.equivFun.symm.toAddEquiv
  have h := good_trS hv hp e (good_pow L hv hp hprod htr h₁ h₀ _)
  rwa [htr] at h

theorem main : HodgeTateDatumStatement → OrdinaryCurveStatement → ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → IsAdicComplete (Ideal.span {(p : R)}) R → ∀ (P : Out.PolAV (Spec (CommRingCat.of R))), ∀ (T : TorsRep P.A p) (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] (pt : N → (sp (R₀ := R) R ⟶ P.A)), IsTorsPts P.A p pt → ∀ (Nm : Type) [AddCommGroup Nm] [Fintype Nm] [DecidableEq Nm], ∀ (Ne : Type) [AddCommGroup Ne] [Fintype Ne] [DecidableEq Ne], (∀ x : Nm, p • x = 0) → (∀ x : Ne, p • x = 0) → IsAbFactor p (tens (torsFun C T pt) (tens (Submodule.span R (Set.range fun (ψ : AddChar Nm C) (x : Nm) => ψ x)) (intFun (C := C) R Ne))) ∧ IsTight v p (tens (torsFun C T pt) (tens (Submodule.span R (Set.range fun (ψ : AddChar Nm C) (x : Nm) => ψ x)) (intFun (C := C) R Ne))) := by
  intro hHT hOC p _ C _ _ _ v R _ _ hv hp hc P T N _ _ _ pt hpt Nm _ _ _ Ne _ _ _ hNm hNe
  haveI : IsCommMonObj P.A := P.isAb.comm
  obtain ⟨⟨AA, hAA⟩, -, -, -, k⟩ := GlobalTheory.T.torsion_points_hopf_order p C v R hv hp P.A T N pt hpt
  have g₁ : Good p v N (torsFun C T pt) :=
    ⟨⟨AA, hAA⟩, isAbFactor_self P.grp P.L P.isAb P.isLB P.ample T hpt,
      (GlobalTheory.CompanionTheory.Ar.GR.gp_polAV hHT p C v R hv hp hc P T N pt hpt).2⟩
  obtain ⟨zm, ze⟩ := good_zmod (R := R) hv hp hc hOC
  have gm : Good p v Nm (charLat (C := C) R Nm) :=
    good_of_killed (fun N => charLat R N) hv hp (fun d => charLat_prod _ _)
      (fun _ _ _ _ e => trS_charLat e) zm
      (by simpa only [charLat_trivial] using good_trivial hv hp hc hOC (Fin 0 → ZMod p)) Nm hNm
  have ge : Good p v Ne (intFun (C := C) R Ne) :=
    good_of_killed (fun N => intFun R N) hv hp (fun d => intFun_prod _ _)
      (fun _ _ _ _ e => trS_intFun e) ze (good_trivial hv hp hc hOC _) Ne hNe
  have h := good_tens hv hp k (fun x => Prod.ext (hNm x.1) (hNe x.2)) g₁
    (good_tens hv hp hNm hNe gm ge)
  exact ⟨h.2.1, h.2.2⟩

end Main

end PositivityTheory.HtPt.Stight.BadRed
