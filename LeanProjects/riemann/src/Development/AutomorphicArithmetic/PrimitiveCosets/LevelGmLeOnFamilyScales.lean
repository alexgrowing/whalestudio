import Development.AutomorphicArithmetic.PrimitiveCosets.WindowInequalityOfArtinInputs
import Formalism.SharpRestriction.GlobalSchurBounds.TieGlobal
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts

noncomputable section

namespace UpperTheory.Comparison₂

open Formalism.HC Formalism.MainNotions Formalism.BasicNotions

theorem arithOf_eq {φ : Frame} (H : HostRaw φ) : arithOf H = arith H := rfl

theorem tiedCore_of_chainTied {eps : ℝ} (Fm : FamP eps) (eD eL K cHH eK CL x : ℝ) (h : ChainTied Fm eD eL K cHH eK CL x) :
    FamCoreConstantBounds Fm.toFamCore eD eL K cHH eK x := by
  obtain ⟨i0, m, f, pt, av, bv, Top, iT, Dd, C, Xpp, ell, N, TT, T2, a, w, eT, eP, η, X', θ,
    -, -, -, ⟨tT, t2, -, -, hell⟩, h1, h2, h3, h4, h5, h7, h8, h9, h10, ⟨⟨s1, s2, s3, s4, s5, s6, ⟨n1, n2, n3⟩, s8⟩, th, -⟩, h12, h13⟩ := h
  have hTT : TT = (Fm.D x i0).host.TT := by
    ext t
    rw [tT t, ← Fm.TT_eq x i0, Finset.mem_image]
    exact ⟨fun ⟨s, hs, e⟩ => (Frame.A.val_injective _ e) ▸ hs, fun ht => ⟨t, ht, rfl⟩⟩
  subst hTT
  refine ⟨i0, _, inferInstance, id, fun u0 => (Fm.D x (pt u0)).what₂.Word, fun _ => inferInstance, fun _ => inferInstance, Top, iT,
    m, f, Dd, C, Xpp, ell, N, T2, a, w, eT, eP, η, X', θ, hell, h1, h2, h3, h4, h5, fun s _ => ⟨s, rfl⟩, h7, h8, h9, h10,
    ⟨s1, s2, s3, s4, s5, s6, fun u _ => n1 u, fun u _ => n2 u, fun u _ => n3 u, fun u _ => s8 u⟩, th, h12, h13, fun s hs => ?_⟩
  obtain ⟨k, -, rfl⟩ := (t2 0 s).1 hs
  exact Frame.digit_mem_cyclic_subgroup _ k

theorem level_gm_le_on_family_scales (Λ : Level) :
    ChebyshevInequalityOnWindows (Fam := FamP) (fun Fm => Fm.toFamCore) (fun Fm => ChainTied Fm) Λ :=
  windowInequality_of_artinInputs (fun Fm => tiedCore_of_chainTied Fm) Λ

theorem zeroFreeOn_of_chainTied {Q : PChar → Prop}
    (hW : ∀ ψ, Q ψ → ∃ (Λ : Level) (la : ℝ), ψ ∈ Λ.KEPT ∧ 1 < la ∧
      ChebyshevInequalityAtWindowScale (Fam := FamP) (fun Fm => Fm.toFamCore) (fun Fm => ChainTied Fm) la Λ) : ZeroFreeOn Q :=
  zeroFreeOn_of_core (fun Fm => tiedCore_of_chainTied Fm) hW

end UpperTheory.Comparison₂

end
