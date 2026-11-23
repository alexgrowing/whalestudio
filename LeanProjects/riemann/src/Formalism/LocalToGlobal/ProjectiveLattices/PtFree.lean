import Formalism.LocalToGlobal.ProjectiveLattices.VAtVNeBot
import Formalism.LocalToGlobal.ProjectiveLattices.RulInst

noncomputable section

namespace Formalism.L2.PjFree

open Formalism.L2.Pj NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

section One

variable {K : Type} [Field K] [NumberField K] {R : Type} [CommRing R] [Algebra K R]

structure IsVal (la : HeightOneSpectrum (𝓞 K)) (v : R → EReal) : Prop where
  zero : v 0 = ⊤
  ne_bot : ∀ r, v r ≠ ⊥
  add : ∀ r s, min (v r) (v s) ≤ v (r + s)
  smul : ∀ (a : K) r, a ≠ 0 → v (a • r) = (((vLa la a : ℤ) : ℝ) : EReal) + v r
  mul : ∀ r s, v (r * s) = v r + v s

structure IsNormOn (C : Submodule K R) (σ : K →+* ℂ) (N : R → ℝ) : Prop where
  nonneg : ∀ f ∈ C, 0 ≤ N f
  defin : ∀ f ∈ C, N f = 0 → f = 0
  smul : ∀ (a : K), ∀ f ∈ C, N (a • f) = ‖σ a‖ * N f
  add : ∀ f ∈ C, ∀ g ∈ C, N (f + g) ≤ N f + N g

end One

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)
  (cls : ∀ (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → Prop)

def algCls (T : CDVR) (ι : c.F →+* T.Fr) (y : IntFr Xo c T ι) : Prop := y.IsAlg

def valSet (la : HeightOneSpectrum (𝓞 c.F)) : Set (Rul Xo c → EReal) :=
  Set.range (vAtV : PtV Xo c cls Unit (fun _ _ _ _ => True) la → Rul Xo c → EReal)

variable {Xo c cls}

theorem isVal_vAt {PY : Type} {lies : ∀ (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → PY → Prop}
    {la : HeightOneSpectrum (𝓞 c.F)} (y : PtV Xo c cls PY lies la) : IsVal la (vAtV y) := by
  obtain ⟨⟨g, hg⟩, T, io, e, hO, y0, hcls, eta, hl, heq⟩ := y
  unfold vAtV
  dsimp only
  unfold profI at heq
  have hg1 := congrArg Prod.fst heq
  dsimp only at hg1
  subst hg1
  have h0 : evI y0 (0 : Rul Xo c) = 0 := by
    rw [← zero_smul c.F (0 : Rul Xo c), evI_smul, map_zero, zero_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show nval T.V e (evI y0 0) = ⊤
    rw [h0, nval_zero]
  · intro r
    show nval T.V e (evI y0 r) ≠ ⊥
    by_cases hr : evI y0 r = 0
    · rw [hr, nval_zero]
      simp
    · rw [nval_of_ne hr]
      exact EReal.coe_ne_bot _
  · intro r s
    show min (nval T.V e (evI y0 r)) (nval T.V e (evI y0 s)) ≤ nval T.V e (evI y0 (r + s))
    rw [evI_add]
    exact nval_add e _ _
  · intro a r ha
    show nval T.V e (evI y0 (a • r)) = (((vLa la a : ℤ) : ℝ) : EReal) + nval T.V e (evI y0 r)
    have hio : nval T.V e (io a) = (((vLa la a : ℤ) : ℝ) : EReal) := by
      rw [nval_of_ne ((map_ne_zero io).2 ha), hO.2 a]
      congr 1
      have he : (e : ℝ) ≠ 0 := by exact_mod_cast hO.1.ne'
      push_cast
      field_simp
    rw [evI_smul, nval_mul, hio]
  · intro r s
    show nval T.V e (evI y0 (r * s)) = nval T.V e (evI y0 r) + nval T.V e (evI y0 s)
    rw [evI_mul, nval_mul]

theorem isVal_valSet (la : HeightOneSpectrum (𝓞 c.F)) : ∀ v ∈ valSet Xo c cls la, IsVal la v := by
  rintro v ⟨y, rfl⟩
  exact isVal_vAt y

variable (Xo c cls)

def LiesTotal (PY : HeightOneSpectrum (𝓞 c.F) → Type)
    (lies : ∀ la (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → PY la → Prop) : Prop :=
  ∀ la (T : CDVR) (ι : c.F →+* T.Fr) (e : ℕ), OverLa la T.V ι e → ∀ y : IntFr Xo c T ι, cls T ι y →
    ∃ η, lies la T ι y η

variable {Xo c cls}

theorem nonneg_iff_of_liesTotal {PY : HeightOneSpectrum (𝓞 c.F) → Type}
    {lies : ∀ la (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → PY la → Prop}
    (h : LiesTotal Xo c cls PY lies) (f : Rul Xo c) :
    (∀ la, ∀ v ∈ valSet Xo c cls la, 0 ≤ v f) ↔
      ∀ la (y : PtV Xo c cls (PY la) (lies la) la), 0 ≤ vAtV y f := by
  constructor
  · intro H la y
    obtain ⟨⟨g, hg⟩, T, io, e, hO, y0, hcls, eta, hl, heq⟩ := y
    have hg1 := congrArg Prod.fst heq
    dsimp only at hg1
    subst hg1
    have hv := H la (vAtV (⟨profI Xo c Unit e y0 (), T, io, e, hO, y0, hcls, (), trivial, rfl⟩ :
      PtV Xo c cls Unit (fun _ _ _ _ => True) la)) ⟨_, rfl⟩
    exact hv
  · rintro H la v ⟨y, rfl⟩
    obtain ⟨⟨g, hg⟩, T, io, e, hO, y0, hcls, eta, hl, heq⟩ := y
    have hg1 := congrArg Prod.fst heq
    dsimp only at hg1
    subst hg1
    obtain ⟨η, hη⟩ := h la T io e hO y0 hcls
    exact H la ⟨profI Xo c (PY la) e y0 η, T, io, e, hO, y0, hcls, η, hη, rfl⟩

end Formalism.L2.PjFree
