import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
import Formalism.LocalToGlobal.Columns.MtHeckeSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CorrectionOfTransport
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLatticeCongruenceInLevelCharacterOne
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg

noncomputable section

set_option maxHeartbeats 1000000

namespace GlobalTheory.Mem.R3.LiftBrg.FrameEquiv

theorem castGL_castGL_symm {R : Type} [CommRing R] {m n : ℕ} (h : m = n) (x : GL (Fin n) R) :
    castGL h (castGL h.symm x) = x := by
  subst h
  ext i j
  simp [castGL]

theorem bc_swapAE_injective (D : D7) (m : ℕ) :
    Function.Injective (Formalism.UG.bc (n := Fin m) (swapAE D)) := by
  intro a b h
  have hs : Function.Injective (swapAE D) := fun x y hxy =>
    (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).injective hxy
  ext i j
  have := congrArg (fun g : GL (Fin m) (Formalism.IndefR.Lev.EAf D) => g.val i j) h
  exact hs this

theorem frame_equiv : ∀ (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (EA X)) (hF : FrameOK X I U i t A k),
    ∃ Φ : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV ≃* Bridge.Gf (Vc X.toD7 i), ∀ u,
      castGL (rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7) ((Φ u : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _)) = A * k * (u : GL (Fin X.B.R.nV) (EA X)) * (A * k)⁻¹ := by
  intro X px I hX U Xg tr L i t A k hF
  obtain ⟨-, -, h3, hk, -, -⟩ := hF
  set V := Vc X.toD7 i
  set h := rkEq X i
  set G := Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV
  let c : Bridge.Gf V →* GL (Fin X.B.R.nV) (EA X) :=
    (castGL h.symm).toMonoidHom.comp ((Formalism.UG.bc (swapAE X.toD7)).comp (Bridge.Gf V).subtype)
  have hc : ∀ g, c g = castGL h.symm (Formalism.UG.bc (swapAE X.toD7) (g : GL (Fin V.rank) _)) := fun _ => rfl
  have hmem : ∀ g : Bridge.Gf V, (A * k)⁻¹ * c g * (A * k) ∈ G := by
    intro g
    have hUA : Formalism.UG.bc (swapAE X.toD7) (g : GL (Fin V.rank) _) ∈ UA X.toD7.sp.cm V.gram := by
      obtain ⟨κ, hκ⟩ := g.2
      rw [← hκ]
      exact GlobalTheory.LevFinCong.finE_mem_UA V κ
    have hx : A⁻¹ * c g * A ∈ G := by
      rw [h3]
      have e : A * (A⁻¹ * c g * A) * A⁻¹ = c g := by group
      rw [e, hc, castGL_castGL_symm]
      exact hUA
    have e2 : (A * k)⁻¹ * c g * (A * k) = k⁻¹ * (A⁻¹ * c g * A) * k := by group
    rw [e2]
    exact G.mul_mem (G.mul_mem (G.inv_mem hk) hx) hk
  let ψ : Bridge.Gf V →* G :=
    { toFun := fun g => ⟨(A * k)⁻¹ * c g * (A * k), hmem g⟩
      map_one' := by ext1; simp
      map_mul' := fun a b => by ext1; simp only [map_mul, Subgroup.coe_mul]; group }
  have hψ : ∀ g, ((ψ g : G) : GL (Fin X.B.R.nV) (EA X)) = (A * k)⁻¹ * c g * (A * k) := fun _ => rfl
  have hinj : Function.Injective ψ := by
    intro a b hab
    have e := congrArg (fun x : G => (x : GL (Fin X.B.R.nV) (EA X))) hab
    simp only [hψ, mul_left_inj, mul_right_inj] at e
    rw [hc, hc] at e
    have e' := (castGL h.symm).injective e
    exact Subtype.ext (bc_swapAE_injective X.toD7 V.rank e')
  have hsurj : Function.Surjective ψ := by
    intro u
    have hku : k * (u : GL (Fin X.B.R.nV) (EA X)) * k⁻¹ ∈ G := G.mul_mem (G.mul_mem hk u.2) (G.inv_mem hk)
    have hw := (h3 _).1 hku
    obtain ⟨κ, -, hκ⟩ := GlobalTheory.AdIsomCorrection.exists_finE V _ hw
    refine ⟨⟨finHom V κ, κ, rfl⟩, ?_⟩
    ext1
    rw [hψ, hc]
    change (A * k)⁻¹ * castGL h.symm (finE V κ) * (A * k) = _
    rw [hκ, castGL_castGL_symm h.symm]
    group
  have hbij : Function.Bijective ψ := ⟨hinj, hsurj⟩
  let Ψ := MulEquiv.ofBijective ψ hbij
  refine ⟨Ψ.symm, fun u => ?_⟩
  have e0 : ψ (Ψ.symm u) = u := Ψ.apply_symm_apply u
  have e := congrArg (fun x : G => (x : GL (Fin X.B.R.nV) (EA X))) e0
  simp only [hψ] at e
  rw [← hc, ← e]
  group

end GlobalTheory.Mem.R3.LiftBrg.FrameEquiv
