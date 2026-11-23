import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartWiden
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValLtOfRedM
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NearPair
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointRightTranslateByLevelCoupledStep
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypePrimeFramesRightTranslateDifferIntegralGL
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.QChi

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ} {P : HeightOneSpectrum (𝓞 E)}

theorem nearAt_congr' {n : ℕ} {x x' : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} {g g' : GL (Fin N) E}
    (h : GlobalTheory.TwU.NearAt P n x g) (hx : x = x') (hg : g = g') : GlobalTheory.TwU.NearAt P n x' g' := hx ▸ hg ▸ h

theorem nearAt_inv_int {n : ℕ} (hn : 1 ≤ n) {x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} {g h : GL (Fin N) E}
    (hx : GlobalTheory.TwU.NearAt P n x g) (hh : h = g⁻¹)
    (hint : ∀ a b, IntAt P ((h : Matrix (Fin N) (Fin N) E) a b) ∧ IntAt P (((h⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) a b)) :
    GlobalTheory.TwU.NearAt P n x⁻¹ h := by
  subst hh
  unfold GlobalTheory.TwU.NearAt at *
  have := GlobalTheory.CplPt.congAt_conj n (GlobalTheory.LevFrame.congAt_inv F E N n P _ hn hx) hint
  convert this using 1
  rw [map_inv]
  group

end Gen

section Near

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι)
  (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))

theorem prCat_last_le_int (hI : I.Ok) (P : SBof I a) :
    prCat (Pr := B.primes X) (I.cst a).sharp (B.R.m - 1) P.1 1 ≤ GLint B.fields.E (B.R.N (B.R.m - 1)) P.1 := by
  have hL := hI.idx_ok a
  have e : B.R.m - 1 = B.R.m - 2 + 1 := by have := hL.hm; omega
  obtain ⟨b, -⟩ := hL.last_uniq
  have h := hL.int _ b P
  rw [hL.last_h] at h
  rw [e]
  exact h

theorem nearV_one (P : SBof I a) : NearV I l Z a v P 1 1 := by
  unfold NearV
  exact nearAt_congr' (GlobalTheory.TwU.nearAt_self (F := (I.rec7 l Z).host.F) _ _ 1) ((map_one _).trans (map_one _).symm) (map_one _).symm

theorem nearV_mul (P : SBof I a) {x y} {g g' : Sp B.fields.E (B.R.N (B.R.m - 1)) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N (B.R.m - 1))}
    (hx : NearV I l Z a v P x g) (hy : NearV I l Z a v P y g') (hg' : g' ∈ GLint B.fields.E (B.R.N (B.R.m - 1)) P.1) :
    NearV I l Z a v P (x * y) (g * g') := by
  unfold NearV at *
  exact nearAt_congr' (GlobalTheory.CplPt.nearAt_mul_int _ hx hy (GlobalTheory.CplPt.seamGL_int (sm I l Z) ⟨g', hg'⟩))
    (map_mul _ _ _).symm (map_mul _ _ _).symm

theorem nearV_inv (P : SBof I a) (hD : 1 ≤ (I.cst a).D P) {x}
    {g : Sp B.fields.E (B.R.N (B.R.m - 1)) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N (B.R.m - 1))}
    (hx : NearV I l Z a v P x g) (hg : g⁻¹ ∈ GLint B.fields.E (B.R.N (B.R.m - 1)) P.1) :
    NearV I l Z a v P x⁻¹ g⁻¹ := by
  unfold NearV at *
  exact nearAt_congr' (nearAt_inv_int hD hx (map_inv _ _) (GlobalTheory.CplPt.seamGL_int (sm I l Z) ⟨g⁻¹, hg⟩))
    (map_inv _ _).symm rfl

theorem mem_of_midLev (P : SBof I a) {g : Sp B.fields.E (B.R.N (B.R.m - 1)) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N (B.R.m - 1))} {z : B.fields.K}
    (h : GlobalTheory.TwU.MidLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) (B.R.m - 1) P 1 g z) :
    g ∈ prCat (Pr := B.primes X) (I.cst a).sharp (B.R.m - 1) P.1 1 :=
  (GlobalTheory.TwU.exists_midLev_iff (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) (B.R.m - 1) P 1 g).1 ⟨z, h⟩

theorem exists_midLev_of_mem (P : SBof I a) {g : Sp B.fields.E (B.R.N (B.R.m - 1)) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N (B.R.m - 1))}
    (h : g ∈ prCat (Pr := B.primes X) (I.cst a).sharp (B.R.m - 1) P.1 1) :
    ∃ z, GlobalTheory.TwU.MidLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) (B.R.m - 1) P 1 g z :=
  (GlobalTheory.TwU.exists_midLev_iff (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) (B.R.m - 1) P 1 g).2 h

end Near

theorem nearSet_closed : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι)
    (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), 1 ∈ GlobalTheory.Mem.Col2.QChi.NearSet I l Z a v ∧
      (∀ x y, x ∈ GlobalTheory.Mem.Col2.QChi.NearSet I l Z a v → y ∈ GlobalTheory.Mem.Col2.QChi.NearSet I l Z a v → x * y ∈ GlobalTheory.Mem.Col2.QChi.NearSet I l Z a v) ∧
      ∀ x, x ∈ GlobalTheory.Mem.Col2.QChi.NearSet I l Z a v → x⁻¹ ∈ GlobalTheory.Mem.Col2.QChi.NearSet I l Z a v := by
  intro B X I hI l Z a v
  refine ⟨fun P _ => ?_, fun x y hx hy P hP => ?_, fun x hx P hP => ?_⟩
  · obtain ⟨z, hz⟩ := exists_midLev_of_mem I a P (one_mem _)
    exact ⟨1, z, hz, nearV_one I l Z a v P⟩
  · obtain ⟨g, z, hgz, hxg⟩ := hx P hP
    obtain ⟨g', z', hgz', hyg'⟩ := hy P hP
    have hg := mem_of_midLev I a P hgz
    have hg' := mem_of_midLev I a P hgz'
    obtain ⟨z'', hz''⟩ := exists_midLev_of_mem I a P (mul_mem hg hg')
    exact ⟨g * g', z'', hz'', nearV_mul I l Z a v P hxg hyg' (prCat_last_le_int I a hI P hg')⟩
  · obtain ⟨g, z, hgz, hxg⟩ := hx P hP
    have hgi := inv_mem (mem_of_midLev I a P hgz)
    obtain ⟨z', hz'⟩ := exists_midLev_of_mem I a P hgi
    exact ⟨g⁻¹, z', hz', nearV_inv I l Z a v P ((hI.idx_ok a).cst_ok.D_pos P) hxg (prCat_last_le_int I a hI P hgi)⟩

end GlobalTheory.Mem.Col2.QChi

end
