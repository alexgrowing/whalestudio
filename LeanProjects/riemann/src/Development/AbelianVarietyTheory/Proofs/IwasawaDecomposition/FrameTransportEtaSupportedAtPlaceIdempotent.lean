import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
import Formalism.LocalToGlobal.Columns.MtHeckeSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportedAtConjPrimeIdempotentOfTrivialOffPlaceStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg

namespace GlobalTheory.Mem.R3.LiftBrg.EtaSupp

theorem castGL_bc_comm {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {m k : ℕ} (h : m = k) (x : GL (Fin m) R) :
    castGL h (Formalism.UG.bc φ x) = Formalism.UG.bc φ (castGL h x) := by
  subst h
  ext i j
  simp [castGL, Formalism.UG.bc]

theorem finE_prV_eq_one {D : D7} (V : HSp D) (n : ℕ) [NeZero n] (h : n = V.rank) (v : HeightOneSpectrum (𝓞 D.host.F))
    (Pb : Formalism.L2.DIV.Pl D.host.E) (Ut : Formalism.L2.Col.MhlUnif Pb) (d : ℕ) (C : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) (α : GA D V)
    (hα : castGL h.symm (Formalism.UG.bc (swapAE D) (finHom V α)) = C * ((Formalism.L2.Col.mhlEta D.sp.cm n v Ut.hπ0 d : Formalism.L2.Col.UAd D.sp.cm n) : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) * C⁻¹)
    (w : HeightOneSpectrum (𝓞 D.host.F)) (hw : w ≠ v) :
    Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) w) (finE V α) = 1 := by
  apply (castGL h.symm).injective
  rw [map_one, castGL_bc_comm]
  show Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) w) (castGL h.symm (Formalism.UG.bc (swapAE D) (finHom V α))) = 1
  rw [hα]
  have key : ∀ {G H : Type} [Group G] [Group H] (f : G →* H) (c x : G), f x = 1 → f (c * x * c⁻¹) = 1 := by
    intro G H _ _ f c x hx
    rw [map_mul, map_mul, hx, mul_one, map_inv, mul_inv_cancel]
  have h1 : Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) w)
      ((Formalism.L2.Col.mhlEta D.sp.cm n v Ut.hπ0 d : Formalism.L2.Col.UAd D.sp.cm n) : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) = 1 :=
    Formalism.L2.Col.rll_put_ne n v w hw _
  exact key _ _ _ h1

end GlobalTheory.Mem.R3.LiftBrg.EtaSupp

namespace GlobalTheory.Mem.R3.LiftBrg

theorem eta_suppAt : ∀ {D : D7} (V : HSp D) (n : ℕ) [NeZero n] (h : n = V.rank) (v : HeightOneSpectrum (𝓞 D.host.F)) (Pb : Formalism.L2.DIV.Pl D.host.E) (Ut : Formalism.L2.Col.MhlUnif Pb) (d : ℕ) (e : Formalism.L2.Theta.AE D) (C : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) (α : GA D V), Formalism.L2.Col.IsOver v Pb → Formalism.L2.NTheta.IsIdemAt e (Formalism.L2.Col.conjPrime₂ Pb) → α ∈ GfC V → castGL h.symm (Formalism.UG.bc (swapAE D) (finHom V α)) = C * ((Formalism.L2.Col.mhlEta D.sp.cm n v Ut.hπ0 d : Formalism.L2.Col.UAd D.sp.cm n) : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) * C⁻¹ → SuppAt e V α := by
  intro D V n _ h v Pb Ut d e C α hv he hα hη
  exact GlobalTheory.T.supportedAt_conjPrimeIdempotent_of_trivial_offPlace V v Pb e hv he α hα fun w hw =>
    EtaSupp.finE_prV_eq_one V n h v Pb Ut d C α hη w hw

end GlobalTheory.Mem.R3.LiftBrg
