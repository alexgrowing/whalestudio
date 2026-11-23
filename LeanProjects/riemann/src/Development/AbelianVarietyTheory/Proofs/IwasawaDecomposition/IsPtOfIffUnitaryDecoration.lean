import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMoveRight
import Formalism.LocalToGlobal.Columns.RecLevelLocP
import Formalism.LocalToGlobal.Columns.RecLevelCls
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.Col2.PtDeco

theorem isPtOf_iff_decoRaw : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (g : GL (Fin n) (AfE F E)) (p : DecoF E n ST SG Q), Q = ∅ → (IsPtOf hc g p ↔ g ∈ UAd hc n ∧ p.deco.1 = decoRaw ST SG g) := by
  intro F E _ _ _ _ _ _ hc n _ ST SG Q g p hQ
  subst hQ
  have hlast : ∀ i : Fin n, i.1 + 1 = n → lastIdx n = i := fun i hi => Fin.ext (by simp [lastIdx]; omega)
  constructor
  · intro h
    have hg : g ∈ UAd hc n := h.uni
    have hN : p.deco.1.N = Formalism.UG.CS.globLat g (stdLat E n) := by
      have h1 := Formalism.UG.P.global_lattice_one_holds F E (Fin n) p.deco.1.N (Module.Finite.iff_fg.2 p.deco.2.lat.fg)
        p.deco.2.lat.span_eq_top
      ext v
      conv_lhs => rw [← h1]
      have e1 : ∀ (x : GL (Fin n) (AfE F E)) (Λ : Submodule (𝓞 E) (Fin n → E)) (v : Fin n → E),
          v ∈ Formalism.UG.CS.globLat x Λ ↔ ((x⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ
            (fun i => Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (v i)) ∈ Formalism.L2.Herm.hatL (F := F) Λ :=
        fun _ _ _ => Iff.rfl
      rw [e1, e1, inv_one, Units.val_one, Matrix.one_mulVec]
      exact h.lat _
    refine ⟨hg, Deco.Ok.ext_on p.deco.2 (decorated_lattice_exists hc n ST SG g hg) hN (fun P x hx => ?_) (fun w x hx => ?_)⟩
    · have hx' : x ∈ Formalism.UG.CS.globLat g (stdLat E n) := hN ▸ hx
      refine HasRes.unique (h.f P x hx (lastIdx n) (by simp [lastIdx]; have := NeZero.pos n; omega)) ?_
      simp only [decoRaw]
      rw [if_pos (le_locP _ _ hx')]
      exact PtExist.hasRes_redA _ ((mem_globLat g x).1 hx' _)
    · have hx' : x ∈ Formalism.UG.CS.globLat g (stdLat E n) := hN ▸ hx
      funext i
      refine HasRes.unique (h.be w x hx i) ?_
      simp only [decoRaw]
      rw [if_pos (le_locP _ _ hx')]
      exact PtExist.hasRes_redA _ ((mem_globLat g x).1 hx' i)
  · rintro ⟨hg, hd⟩
    have hN : p.deco.1.N = Formalism.UG.CS.globLat g (stdLat E n) := by rw [hd]; rfl
    refine ⟨hg, hN ▸ PtExist.carries_globLat g, fun P x hx i hi => ?_, fun w x hx i => ?_,
      fun P => absurd P.2 (Finset.notMem_empty _)⟩
    · rw [hN] at hx
      rw [hd]
      simp only [decoRaw]
      rw [if_pos (le_locP _ _ hx), hlast i hi]
      exact PtExist.hasRes_redA _ ((mem_globLat g x).1 hx i)
    · rw [hN] at hx
      rw [hd]
      simp only [decoRaw]
      rw [if_pos (le_locP _ _ hx)]
      exact PtExist.hasRes_redA _ ((mem_globLat g x).1 hx i)

end GlobalTheory.Mem.Col2.PtDeco

end
