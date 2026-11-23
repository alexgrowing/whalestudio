import Formalism.SharpRestriction.CuspSpanNormBounds.DataS
import Formalism.SharpRestriction.GrowthBounds.DataG

noncomputable section

namespace Formalism.BasicNotions.Examples₂

open Formalism.BasicNotions NumberField IsDedekindDomain

section S

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (sig : E →ₐ[F] E)

def locAdj (G : Finset ℕ) (loc : ∀ p, Formalism.MainNotions.S.Loc.LocAt F E sig p)
    (spl : ∀ p, Formalism.MainNotions.S.Loc.resChar p ∈ G →
      Formalism.MainNotions.S.Loc.SplitAt (loc p).Fp (loc p).Ep (loc p).cj (Formalism.MainNotions.S.Loc.resChar p))
    (p : HeightOneSpectrum (𝓞 F)) : Formalism.MainNotions.S.Loc.LocAt F E sig p :=
  { loc p with split := if h : Formalism.MainNotions.S.Loc.resChar p ∈ G then some (spl p h) else none }

theorem locAdj_split (G : Finset ℕ) (loc : ∀ p, Formalism.MainNotions.S.Loc.LocAt F E sig p)
    (spl : ∀ p, Formalism.MainNotions.S.Loc.resChar p ∈ G →
      Formalism.MainNotions.S.Loc.SplitAt (loc p).Fp (loc p).Ep (loc p).cj (Formalism.MainNotions.S.Loc.resChar p))
    (p : HeightOneSpectrum (𝓞 F)) :
    (locAdj sig G loc spl p).split.isSome ↔ Formalism.MainNotions.S.Loc.resChar p ∈ G := by
  unfold locAdj
  by_cases h : Formalism.MainNotions.S.Loc.resChar p ∈ G <;> simp [h]

variable {Word Tau : Type} [Subsingleton Word] (hc : Word → Tau → HCParam R)

def toySData (Del : ℚ) (hDel : 0 < Del)
    (hgap : ∀ (w : Word) (τ : Tau) (l : ℕ) (h : l + 1 < R.k - 1),
      (hc w τ).v ⟨l, by omega⟩ - (hc w τ).v ⟨l + 1, h⟩ = 4 * Del)
    (hlet : ∀ (w : Word) (τ : Tau) (l : ℕ) (h : l < R.k - 2),
      (hc w τ).u ⟨l + 1, by omega⟩ = (hc w τ).v ⟨l, by omega⟩ - 1 / 2)
    (loc : ∀ p, Formalism.MainNotions.S.Loc.LocAt F E sig p) :
    Formalism.MainNotions.S.Draft.SData R F E sig Word Tau hc where
  cdScale := fun _ _ => 1
  cdScale_pos := fun _ _ => one_pos
  Del := Del
  Del_pos := hDel
  cloud_gap := hgap
  letter := fun _ _ => false
  letter_inj := fun _ _ _ => Subsingleton.elim _ _
  u_letter := by
    intro w τ l h
    simp [hlet w τ l h]
  HH := EuclideanSpace ℂ (Fin 0)
  Cu := fun _ => EuclideanSpace ℂ (Fin 0)
  Pu := fun _ => 0
  volN := fun _ => 1
  volH := fun _ => 1
  volN_pos := fun _ => one_pos
  volH_pos := fun _ => one_pos
  Term := fun _ _ => Empty
  aTerm := fun _ _ t => t.elim
  isId := fun _ => False
  inS := fun _ => False
  relevant := fun _ => False
  FeqF := fun _ => False
  Gterm := fun t => t.elim
  atP := loc
  PlF := HeightOneSpectrum (𝓞 F)
  BBne := fun _ _ => False
  generic := fun _ => False
  Pair := fun _ _ => Empty
  pfst := fun t => t.elim
  psnd := fun t => t.elim
  s0 := fun _ => 0
  scalarPair := fun _ => False
  pval := fun _ => 0
  ptOf := fun t => t.elim
  cTerm := fun _ => 0
  massPair := fun _ => 0
  meanCount := fun _ _ _ => 0

variable {sig hc}

theorem toySData_HH (Del : ℚ) (hDel hgap hlet) (loc : ∀ p, Formalism.MainNotions.S.Loc.LocAt F E sig p) :
    Module.finrank ℂ (toySData sig hc Del hDel hgap hlet loc).HH = 0 := by
  show Module.finrank ℂ (EuclideanSpace ℂ (Fin 0)) = 0
  simp

theorem toySData_atP (Del : ℚ) (hDel hgap hlet) (loc : ∀ p, Formalism.MainNotions.S.Loc.LocAt F E sig p) (p) :
    (toySData sig hc Del hDel hgap hlet loc).atP p = loc p := rfl

theorem toySData_Del (Del : ℚ) (hDel hgap hlet) (loc : ∀ p, Formalism.MainNotions.S.Loc.LocAt F E sig p) :
    (toySData sig hc Del hDel hgap hlet loc).Del = Del := rfl

def toySData_Cu (Del : ℚ) (hDel hgap hlet) (loc : ∀ p, Formalism.MainNotions.S.Loc.LocAt F E sig p) (u : Word)
    {V : Type} [AddCommGroup V] [Module ℂ V] (M : Submodule ℂ V) (hM : M = ⊥) :
    (toySData sig hc Del hDel hgap hlet loc).Cu u ≃ₗ[ℂ] M := by
  subst hM
  haveI : Subsingleton (EuclideanSpace ℂ (Fin 0)) := ⟨fun a b => by ext i; exact i.elim0⟩
  exact LinearEquiv.ofSubsingleton (EuclideanSpace ℂ (Fin 0)) (⊥ : Submodule ℂ V)

def toySData_PlF (Del : ℚ) (hDel hgap hlet) (loc : ∀ p, Formalism.MainNotions.S.Loc.LocAt F E sig p) :
    (toySData sig hc Del hDel hgap hlet loc).PlF ≃ HeightOneSpectrum (𝓞 F) := Equiv.refl _

end S

section G

open Formalism.MainNotions.G

def emptyPlaces (p : ℕ) : Places p ℤ_[3] ℚ_[3] where
  w := 0
  nV := 0
  n' := fun v => v.elim0
  W := fun v => v.elim0
  Qq := fun v => v.elim0
  ringW := fun v => v.elim0
  domW := fun v => v.elim0
  dvrW := fun v => v.elim0
  fieldQ := fun v => v.elim0
  algWQ := fun v => v.elim0
  ι := fun v => v.elim0
  σ := fun v => v.elim0
  j := fun v => v.elim0
  setting := fun v => v.elim0
  m := 0
  r := 0
  lam0 := fun v => v.elim0
  dom := fun v => v.elim0

instance (p : ℕ) : Unique (emptyPlaces p).Tup :=
  inferInstanceAs (Unique (∀ _ : Fin 0, _))

def toySignLevel (p : ℕ) : Level (emptyPlaces p) where
  Γ := ℤˣ
  act := fun v => v.elim0
  χ := Units.map (Int.castRingHom ℤ_[3]).toMonoidHom

theorem emptyPlaces_natAct (p : ℕ) (A : ∀ v, GL (Fin ((emptyPlaces p).m + 1)) ((emptyPlaces p).Qq v)) :
    (emptyPlaces p).natAct A = LinearMap.id := by
  have hs : ∀ G, (emptyPlaces p).subst G = AlgHom.id _ _ := by
    intro G
    apply MvPolynomial.algHom_ext
    rintro ⟨v, _⟩
    exact v.elim0
  unfold Places.natAct
  rw [hs, Finset.prod_eq_one (fun v _ => v.elim0), one_smul]
  rfl

def gAtPExample (p : ℕ) : GAtP p where
  O := ℤ_[3]
  Kf := ℚ_[3]
  P := emptyPlaces p
  comp := Unit
  lev := fun _ => toySignLevel p
  e := 0

instance (p : ℕ) : Unique (gAtPExample p).P.Tup := inferInstanceAs (Unique (emptyPlaces p).Tup)

theorem toySignLevel_fin (p : ℕ) : (toySignLevel p).FinClasses := by
  refine ⟨{default}, fun _ _ v => v.elim0, fun L _ => ⟨default,
    Finset.mem_singleton_self _, 1, Subsingleton.elim _ _⟩⟩

theorem toySignLevel_M (p : ℕ) : (toySignLevel p).M = ⊥ := by
  rw [eq_bot_iff]
  intro F hF
  rw [Submodule.mem_bot]
  funext L
  have h := hF
  simp only [Level.M, Level.funMod, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker] at h
  have h1 := h.2 (show (toySignLevel p).Γ from (-1 : ℤˣ)) L
  have hs : (toySignLevel p).smul (show (toySignLevel p).Γ from (-1 : ℤˣ)) L = L := Subsingleton.elim _ _
  simp only [LinearMap.sub_apply, LinearMap.proj_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    hs] at h1
  have hc : ((toySignLevel p).χ (show (toySignLevel p).Γ from (-1 : ℤˣ)) : ℤ_[3]) = -1 := by
    show ((Units.map (Int.castRingHom ℤ_[3]).toMonoidHom (-1 : ℤˣ) : ℤ_[3]ˣ) : ℤ_[3]) = -1
    simp
  rw [hc] at h1
  have e : (((toySignLevel p).actX (show (toySignLevel p).Γ from (-1 : ℤˣ))).restrictScalars
      ℤ_[3]) (F L) = F L := by
    show (emptyPlaces p).natAct _ (F L) = F L
    rw [emptyPlaces_natAct]
    rfl
  rw [e, neg_one_smul, sub_neg_eq_add] at h1
  have h2 : (2 : ℚ_[3]) • F L = 0 := by rw [two_smul]; exact h1
  simpa using (smul_eq_zero.mp h2).resolve_left two_ne_zero

theorem gAtPExample_M (p : ℕ) : (gAtPExample p).M = ⊥ := by
  rw [eq_bot_iff]
  intro F hF
  rw [Submodule.mem_bot]
  funext i
  have h : F i ∈ (toySignLevel p).M := hF i (Set.mem_univ i)
  rw [toySignLevel_M] at h
  exact h

theorem gAtPExample_d (p : ℕ) : (gAtPExample p).d = 0 := by
  unfold GAtP.d
  rw [gAtPExample_M]
  exact finrank_bot _ _

end G

end Formalism.BasicNotions.Examples₂
