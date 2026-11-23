import Formalism.LocalToGlobal.ProjectiveLattices.MulCMemSec

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

def RdIndep (σ : c.F →+* ℂ) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (k : ℕ), Dom a k → ∀ (n : ℕ) (b : Fin n → Rul Xo c), (∀ i, b i ∈ sec Xo c a k) →
    LinearIndependent c.F b → LinearIndependent ℂ (fun i => rdU (U σ) (b i))

def HolFD (σ : c.F →+* ℂ) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → FiniteDimensional ℂ (holSub (U σ).X (laU (U σ) a n))

theorem goodEmb_val : GoodEmb c c.F.val.toRingHom := rfl

theorem cuspFD_of (σ : c.F →+* ℂ) (hσ : GoodEmb c σ) (hI : RdIndep Xo c U σ) (hF : HolFD Xo c U σ) :
    CuspFD Xo c U := by
  intro a n hd
  haveI := hF a n hd
  have key : ∀ s : Finset (cusp Xo c U a n),
      LinearIndependent c.F (fun i : s => (i : cusp Xo c U a n)) →
        s.card ≤ Module.finrank ℂ (holSub (U σ).X (laU (U σ) a n)) := by
    intro s hs
    let e := s.equivFin
    have h0 : LinearIndependent c.F (fun j : Fin s.card => ((e.symm j : s) : cusp Xo c U a n)) :=
      hs.comp (fun j => e.symm j) e.symm.injective
    have hb : LinearIndependent c.F
        (fun j : Fin s.card => (((e.symm j : s) : cusp Xo c U a n) : Rul Xo c)) :=
      h0.map' (cusp Xo c U a n).subtype (Submodule.ker_subtype _)
    have hc := hI a n hd s.card _ (fun j => cusp_le_sec Xo c U a n ((e.symm j : s) : cusp Xo c U a n).2) hb
    have hmem : ∀ j : Fin s.card,
        rdU (U σ) (((e.symm j : s) : cusp Xo c U a n) : Rul Xo c) ∈ holSub (U σ).X (laU (U σ) a n) :=
      fun j => ((mem_cusp Xo c U a n _).1 ((e.symm j : s) : cusp Xo c U a n).2).2 σ hσ
    let b' : Fin s.card → holSub (U σ).X (laU (U σ) a n) := fun j => ⟨_, hmem j⟩
    have hc' : LinearIndependent ℂ b' := LinearIndependent.of_comp (holSub (U σ).X (laU (U σ) a n)).subtype hc
    have := hc'.fintype_card_le_finrank
    simpa using this
  haveI : Module.Free c.F ↥(cusp Xo c U a n) := Module.Free.of_divisionRing _ _
  exact Module.rank_lt_aleph0_iff.mp ((rank_le key).trans_lt (Cardinal.nat_lt_aleph0 _))

theorem cuspFD_of_val (hI : RdIndep Xo c U c.F.val.toRingHom) (hF : HolFD Xo c U c.F.val.toRingHom) :
    CuspFD Xo c U :=
  cuspFD_of Xo c U _ (goodEmb_val c) hI hF

end Formalism.L2.Pj
