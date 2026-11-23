import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.Mem.Col2.PtUniq

open Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2

theorem mem_iff_hatL {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    {n : ℕ} {N : Submodule (𝓞 E) (Sp E n)} (hN : Submodule.IsLattice E N) (v : Sp E n) :
    v ∈ N ↔ (fun i => Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (v i)) ∈ Formalism.L2.Herm.hatL (F := F) N := by
  have h1 := Formalism.UG.P.global_lattice_one_holds F E (Fin n) N (Module.Finite.iff_fg.2 hN.fg) hN.span_eq_top
  conv_lhs => rw [← h1]
  have e1 : ∀ (x : GL (Fin n) (AfE F E)) (Λ : Submodule (𝓞 E) (Fin n → E)) (v : Fin n → E),
      v ∈ Formalism.UG.CS.globLat x Λ ↔ Matrix.mulVec ((x⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E))
        (fun i => Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (v i)) ∈ Formalism.L2.Herm.hatL (F := F) Λ :=
    fun _ _ _ => Iff.rfl
  rw [e1, inv_one, Units.val_one, Matrix.one_mulVec]

theorem isPtOf_unique : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))} (g : GL (Fin n) (Formalism.L2.DIV.AfE F E))
    (p p' : Formalism.L2.Col.DecoF E n ST SG Q), GlobalTheory.Mem.Col2.IsPtOf hc g p → GlobalTheory.Mem.Col2.IsPtOf hc g p' → p = p' := by
  intro F E _ _ _ _ _ _ hc n ST SG Q g p p' h h'
  have hN : p.deco.1.N = p'.deco.1.N := by
    ext v
    rw [mem_iff_hatL (F := F) p.deco.2.lat, mem_iff_hatL (F := F) p'.deco.2.lat, h.lat, h'.lat]
  have hd : p.deco = p'.deco := by
    apply Subtype.ext
    refine Deco.Ok.ext_on p.deco.2 p'.deco.2 hN (fun P x hx => ?_) (fun w x hx => ?_)
    · rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        have hx0 : x = 0 := Subsingleton.elim _ _
        subst hx0
        have a := p.deco.2.f_smul P 0 0 (zero_mem _)
        have b := p'.deco.2.f_smul P 0 0 (zero_mem _)
        rw [zero_smul, map_zero, zero_mul] at a b
        rw [a, b]
      · exact HasRes.unique (h.f P x hx ⟨n - 1, by omega⟩ (by simp; omega))
          (h'.f P x (hN ▸ hx) ⟨n - 1, by omega⟩ (by simp; omega))
    · funext i
      exact HasRes.unique (h.be w x hx i) (h'.be w x (hN ▸ hx) i)
  have hfr : ∀ P : Q, p.fr P = p'.fr P := by
    intro P
    refine LinearEquiv.toLinearMap_injective (Module.Basis.ext (Pi.basisFun E (Fin n)) fun j => ?_)
    funext i
    have e := (h.fr P i j).symm.trans (h'.fr P i j)
    simpa using (algebraMap E (P.1.adicCompletion E)).injective e
  apply Subtype.ext
  exact Prod.ext hd (funext hfr)

end GlobalTheory.Mem.Col2.PtUniq
