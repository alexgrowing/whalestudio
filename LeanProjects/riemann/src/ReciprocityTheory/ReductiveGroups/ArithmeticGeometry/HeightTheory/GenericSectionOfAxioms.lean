import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtDefs
import ReciprocityTheory.SemistableReduction.AlgAll
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.SectionSheafQuotient

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

noncomputable def htOf (hd : d.AxH 𝒜) (h : d.S1) : Formalism.MainNotions.Gaps.HeightData.HtData where
  K := K
  D := d.D
  δ := d.del
  i := d.i
  g0 := d.g0
  L := d.wsize d.wL
  G := d.Gc
  PH := d.PHc
  Prw := d.Prw
  Pet := d.Pet
  S := fun k => meanK fun sg => Real.log (d.supN sg d.wF (d.thp (hd.sel k)))
  etaPart := True
  Op := fun la => Op d.D d.N la
  SectionSheafQuotient := fun _ => ∀ c, OmS (Ω c) d.D d.N
  mA := fun la =>
    letI : ∀ c, Algebra (Op d.D d.N la) (OmS (Ω c) d.D d.N) := fun c => d.algOp h la c
    inferInstance
  A0 := fun la =>
    letI : ∀ c, Algebra (Op d.D d.N la) (OmS (Ω c) d.D d.N) := fun c => d.algOp h la c
    Submodule.span (Op d.D d.N la) (d.AdmissibleOmegaFamiliesAtPrimeOfSection hd.a4.choose la)
  t := fun _ => d.bvecG hd.sel hd.a4.choose
  Pts := fun la => Σ c, {w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ) // w ∈ d.PlOver la c}
  ep := fun _ _ => 1
  f := fun _ ζ => d.fze h ζ.1 ζ.2.1
  vEt := fun _ ζ => (d.ord ζ.1 (d.Wres ζ.1 ζ.2.1) (d.n1 • d.wde) (d.et ζ.1) : ℝ)

theorem genericSection_of_axioms (hd : d.AxH 𝒜) : d.S1 := by
  intro c
  have hS := (ReciprocityTheory.MultiplicativeHeights.Closed.fieldOfS K (Ω c) d.D d.N (d.x c) (hd.fg c) (hd.trdeg c)
    (hd.a1 c)).1
  have key : ∀ {M : Type} (j0 : Fin (d.N + 1)) (a : M) (f : Fin d.N → M),
      Fin.succAboveCases (α := fun _ => M) j0 a f j0 = a ∧
      ∀ k, Fin.succAboveCases (α := fun _ => M) j0 a f (j0.succAbove k) = f k :=
    fun j0 a f => ⟨by exact Fin.insertNth_apply_same (α := fun _ => _) j0 a f,
      fun k => by exact Fin.insertNth_apply_succAbove (α := fun _ => _) j0 a f k⟩
  let σ : Fin (d.N + 1) → Fin (d.N + 1) :=
    Fin.succAboveCases (α := fun _ => Fin (d.N + 1)) (d.jc c) 0 Fin.succ
  let ρ : Fin (d.N + 1) → Fin (d.N + 1) :=
    Fin.cases (motive := fun _ => Fin (d.N + 1)) (d.jc c) (d.jc c).succAbove
  have hρσ : Function.LeftInverse ρ σ := by
    intro j
    rcases Fin.eq_self_or_eq_succAbove (d.jc c) j with rfl | ⟨k, rfl⟩
    · simp only [σ, ρ, (key _ _ _).1, Fin.cases_zero]
    · simp only [σ, ρ, (key _ _ _).2, Fin.cases_succ]
  let g : TVar d.D d.N → Fin (d.D + 1) × Fin (d.N + 1) := fun p => (p.1, σ p.2)
  have hg : Function.Injective g := by
    intro p q hpq
    simp only [g, Prod.mk.injEq] at hpq
    exact Prod.ext hpq.1 (hρσ.injective hpq.2)
  have heq : ∀ p, sImg (d.jc c) (d.x c) p = ReciprocityTheory.MultiplicativeHeights.sImage (D := d.D) (d.x c) (g p) := by
    rintro ⟨i, j⟩
    rcases Fin.eq_self_or_eq_succAbove (d.jc c) j with rfl | ⟨k, rfl⟩
    · simp only [sImg, ReciprocityTheory.MultiplicativeHeights.sImage, g, σ, (key _ _ _).1, Fin.cases_zero]
    · simp only [sImg, ReciprocityTheory.MultiplicativeHeights.sImage, g, σ, (key _ _ _).2, Fin.cases_succ]
  have hfun : sImg (d.jc c) (d.x c) = ReciprocityTheory.MultiplicativeHeights.sImage (D := d.D) (d.x c) ∘ g := funext heq
  have hI : AlgebraicIndependent K (sImg (D := d.D) (d.jc c) (d.x c)) := by
    rw [hfun]
    exact hS.comp g hg
  exact hI

end Data

end ReciprocityTheory.ChartRestriction.G.T0
