import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SetupEig

noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.U

open PositivityTheory.Rg.BcB.F.Eig

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

structure UFam (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)) : Type 1 where
  ι : Type
  [ft : Fintype ι]
  π : ι → Submodule ℂ (UA E n → ℂ)
  σ : ι → ∀ w : Pl E, SmIrr (UL n w)
  comp : ∀ i, IsAutRepU (π i) ∧ (∀ v, HasWeightAt (π i) v.embedding (lam v)) ∧ HasLevel S (π i) K' ∧
    ∀ w ∈ S, IsCompU (π i) w (σ i w) ∧ fixed (σ i w).ρ (K' w) ≠ ⊥ ∧
      ∀ U : Subgroup (UL n w), IsOpen (U : Set (UL n w)) → FiniteDimensional ℂ (fixed (σ i w).ρ U)
  all : ∀ π₀, IsAutRepU π₀ → (∀ v, HasWeightAt π₀ v.embedding (lam v)) → HasLevel S π₀ K' →
    ∃ i, ∀ w ∈ S, IsCompU π₀ w (σ i w)
  tf : ∀ f, IsTest (KL n) K' f → (∃ w ∈ S, ∀ y, f w y ≠ 0 → y.1.val.charpoly.Separable) →
    ∑ i, ∏ᶠ w ∈ S, twTr (σ i w).ρ (KL n w) (K' w) (f w) LinearMap.id = geomU S lam f

attribute [instance] UFam.ft

theorem uFam_of (h : USide) (hE : GlobalTheory.BCT.Unr E) (hn : 1 ≤ n) {S : Set (Pl E)} (hS : IsSection S)
    (lam : InfinitePlace E → DomWeight n) {K' : ∀ w : Pl E, Subgroup (UL n w)}
    (hK : IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K') : Nonempty (UFam S lam K') := by
  obtain ⟨ι, _, π, σ, h1, h2, h3⟩ := h E hE n hn S hS lam K' hK
  exact ⟨⟨ι, π, σ, h1, h2, h3⟩⟩

structure UMod {S : Set (Pl E)} {lam : InfinitePlace E → DomWeight n} {K' : ∀ w : Pl E, Subgroup (UL n w)}
    (F : UFam S lam K') (B : Finset (Pl E)) (g : ∀ w : Pl E, UL n w → ℂ) where
  d : ℕ
  blk : Fin d → F.ι
  u : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d)
  comm : ∀ c, Commute u (diagOp blk c)
  tr : ∀ (k : ℕ) f, IsTest (KL n) K' f → (∀ i, ∀ w ∈ B, locOp (F.σ i w) (K' w) (f w) = locOp (F.σ i w) (K' w) (g w) ^ k) →
    ∑ i, ∏ᶠ w ∈ S, twTr (F.σ i w).ρ (KL n w) (K' w) (f w) LinearMap.id =
      LinearMap.trace ℂ _ ((u ^ k * diagOp blk fun i => ∏ᶠ w ∈ S \ ↑B, twTr (F.σ i w).ρ (KL n w) (KL n w) (f w) LinearMap.id :
        EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d)) : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin d))
  eig : ∀ i₀, (∀ w ∈ B, ∃ y, y ≠ 0 ∧ locOp (F.σ i₀ w) (K' w) (g w) y = y) →
    ∃ v, v ≠ 0 ∧ u v = v ∧ ∀ c, diagOp blk c v = c i₀ • v

def LevelOff (S : Set (Pl E)) (B : Finset (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)) : Prop :=
  (↑B : Set (Pl E)) ⊆ S ∧ IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' ∧ ∀ w, w ∉ B → K' w = KL n w

theorem sph_line (h1 : SphOne) (hE : GlobalTheory.BCT.Unr E) {S : Set (Pl E)} {lam : InfinitePlace E → DomWeight n}
    {K' : ∀ w : Pl E, Subgroup (UL n w)} (F : UFam S lam K') {B : Finset (Pl E)} (hB : LevelOff S B K') (i : F.ι)
    (w : Pl E) (hw : w ∈ S) (hwB : w ∉ B) : Module.finrank ℂ (fixed (F.σ i w).ρ (KL n w)) = 1 := by
  obtain ⟨-, h2, h3⟩ := (F.comp i).2.2.2 w hw
  have e := hB.2.2 w hwB
  have ho := (hB.2.1.1 w).1
  rw [e] at h2 ho
  exact h1 E hE n w _ h2 (h3 _ ho)

theorem uMod_of (h1 : SphOne) (h2 : SpecTrace) (hE : GlobalTheory.BCT.Unr E) {S : Set (Pl E)} {lam : InfinitePlace E → DomWeight n}
    {K' : ∀ w : Pl E, Subgroup (UL n w)} (F : UFam S lam K') {B : Finset (Pl E)} (hB : LevelOff S B K')
    (g : ∀ w : Pl E, UL n w → ℂ) : Nonempty (UMod F B g) := by
  obtain ⟨d, blk, u, a, b, c⟩ := h2 E n S B hB.1 K' hB.2.1 (fun w _ hw => hB.2.2 w hw) F.ι F.σ
    (fun i w hw => ((F.comp i).2.2.2 w hw).2.2 _ (hB.2.1.1 w).1) (sph_line h1 hE F hB) g
  exact ⟨⟨d, blk, u, a, b, c⟩⟩

abbrev UGen (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) : Type := ℂ ⊕ (Σ w : Pl E, UL n w → ℂ)

namespace UGen

def Ok (S : Set (Pl E)) (B : Finset (Pl E)) : UGen E n → Prop :=
  Sum.elim (fun _ => True) fun x => x.1 ∈ S ∧ x.1 ∉ B ∧ IsHecke (KL n x.1) x.2

def adj : UGen E n → UGen E n := Sum.map (starRingEnd ℂ) fun x => ⟨x.1, lstar x.2⟩

def p {S : Set (Pl E)} {lam : InfinitePlace E → DomWeight n} {K' : ∀ w : Pl E, Subgroup (UL n w)} (F : UFam S lam K')
    (x : UGen E n) (i : F.ι) : ℂ :=
  Sum.elim id (fun x : Σ w : Pl E, UL n w → ℂ => twTr (F.σ i x.1).ρ (KL n x.1) (KL n x.1) x.2 LinearMap.id) x

def sc (l : List (UGen E n)) : ℂ := (l.map (Sum.elim id fun _ => 1)).prod

def sph (l : List (UGen E n)) (w : Pl E) : UL n w → ℂ :=
  l.foldr (fun x f => Sum.elim (fun _ => f) (fun y : Σ w : Pl E, UL n w → ℂ => if h : y.1 = w then lconv (h ▸ y.2) f else f) x)
    ((KL n w : Set (UL n w)).indicator 1)

end UGen

def lone {w : Pl E} (K' : Subgroup (UL n w)) : UL n w → ℂ :=
  (K' : Set (UL n w)).indicator fun _ => ((K'.relIndex (KL n w) : ℕ) : ℂ)

def lpow {w : Pl E} (K' : Subgroup (UL n w)) (g : UL n w → ℂ) : ℕ → UL n w → ℂ
  | 0 => lone K'
  | k + 1 => lconv g (lpow K' g k)

def fam (B : Finset (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)) (g : ∀ w : Pl E, UL n w → ℂ) (k : ℕ) (l : List (UGen E n))
    (w : Pl E) : UL n w → ℂ := if w ∈ B then lpow (K' w) (g w) k else UGen.sph l w

namespace UMod

variable {S : Set (Pl E)} {lam : InfinitePlace E → DomWeight n} {K' : ∀ w : Pl E, Subgroup (UL n w)}
  {F : UFam S lam K'} {B : Finset (Pl E)} {g : ∀ w : Pl E, UL n w → ℂ} (R : UMod F B g)

def op (x : UGen E n) : EuclideanSpace ℂ (Fin R.d) →L[ℂ] EuclideanSpace ℂ (Fin R.d) := diagOp R.blk (x.p F)

theorem op_comm (h : DiagAlg) (x y : UGen E n) : Commute (R.op x) (R.op y) ∧ Commute (R.op x) (star (R.op y)) := by
  refine ⟨?_, ?_⟩
  · exact ((h _ _ R.blk _ _ 0).1.symm.trans (by rw [mul_comm])).trans (h _ _ R.blk _ _ 0).1
  · unfold op
    rw [(h _ _ R.blk (y.p F) 0 0).2.2.2]
    exact ((h _ _ R.blk _ _ 0).1.symm.trans (by rw [mul_comm])).trans (h _ _ R.blk _ _ 0).1

theorem u_comm (h : DiagAlg) (x : UGen E n) : Commute R.u (R.op x) ∧ Commute R.u (star (R.op x)) := by
  refine ⟨R.comm _, ?_⟩
  unfold op
  rw [(h _ _ R.blk (x.p F) 0 0).2.2.2]
  exact R.comm _

theorem exists_eigv (h : DiagAlg) (i₀ : F.ι) (hi : ∀ w ∈ B, ∃ y, y ≠ 0 ∧ locOp (F.σ i₀ w) (K' w) (g w) y = y) :
    ∃ v : EuclideanSpace ℂ (Fin R.d), v ≠ 0 ∧ R.u v = v ∧
      ∀ x : UGen E n, R.op x v = x.p F i₀ • v ∧ star (R.op x) v = starRingEnd ℂ (x.p F i₀) • v := by
  obtain ⟨v, h1, h2, h3⟩ := R.eig i₀ hi
  refine ⟨v, h1, h2, fun x => ⟨h3 _, ?_⟩⟩
  unfold op
  rw [(h _ _ R.blk (x.p F) 0 0).2.2.2, h3]
  rfl

end UMod

def UAdj : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (n : ℕ) (S : Set (Pl E))
  (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)) (F : UFam S lam K') (B : Finset (Pl E))
  (g : ∀ w : Pl E, UL n w → ℂ) (R : UMod F B g), LevelOff S B K' → ∀ x : UGen E n, x.Ok S B →
    x.adj.Ok S B ∧ R.op x.adj = star (R.op x)

def UWord : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (n : ℕ) (S : Set (Pl E))
  (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)) (F : UFam S lam K') (B : Finset (Pl E))
  (g : ∀ w : Pl E, UL n w → ℂ) (R : UMod F B g), LevelOff S B K' → (∀ w ∈ B, IsHecke (K' w) (g w)) →
  ∀ (k : ℕ) (l : List (UGen E n)), (∀ x ∈ l, x.Ok S B) → IsTest (KL n) K' (fam B K' g k l) ∧
    ((∃ w ∈ S, ∀ y, fam B K' g k l w y ≠ 0 → y.1.val.charpoly.Separable) →
      LinearMap.trace ℂ _ ((R.u ^ k * (l.map R.op).prod : EuclideanSpace ℂ (Fin R.d) →L[ℂ] EuclideanSpace ℂ (Fin R.d)) : EuclideanSpace ℂ (Fin R.d) →ₗ[ℂ] EuclideanSpace ℂ (Fin R.d)) =
        UGen.sc l * geomU S lam (fam B K' g k l))

def UAdjOf : Prop := DiagAlg → LocAlg → SphOne → CompUnit → SphStar → UAdj

def UWordOf : Prop := DiagAlg → LocAlg → SphOne → CompUnit → SphStar → UWord

end PositivityTheory.Rg.BcB.F.U

end
