import Formalism.LocalToGlobal.Columns.TiedGlPl
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapLoc

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.UG Formalism.L2.DIV

section Tr

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E)

include hc in

theorem gls_trace_mem (a : 𝓞 E) : ∃ b : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) b = a + cO E a := by
  obtain ⟨b0, hb0⟩ := rll_norm_mem hc a
  obtain ⟨b1, hb1⟩ := rll_norm_mem hc (a + 1)
  refine ⟨b1 - b0 - 1, ?_⟩
  rw [map_sub, map_sub, map_one, hb1, hb0, map_add (cO E), map_one]
  ring

end Tr

section Ex

variable {X : Fields} {Pr : Primes X} (hc : Formalism.BasicNotions.CMData X.F X.E) (hPr : Pr.Ok)

include hPr in

theorem gls_exists (i : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)) (h : (Pr.g i : 𝓞 X.F) ∈ v.asIdeal) :
    Nonempty (Formalism.MainNotions.Gaps.LG.SplitAt hc.sig v (hc.sig (Pr.piG i : X.E))) := by
  obtain ⟨t, ht⟩ := gls_trace_mem hc (Pr.piG i)
  have hsig : ∀ x : X.E, hc.sig x = star x := fun _ => rfl
  have hN : algebraMap X.F X.E ((Pr.g i : 𝓞 X.F) : X.F) = (Pr.piG i : X.E) * hc.sig (Pr.piG i : X.E) := by
    have := congrArg (algebraMap (𝓞 X.E) X.E) (hPr.piG_norm i)
    rw [map_mul, map_natCast] at this
    have h0 : (((Pr.g i : ℕ) : 𝓞 X.F) : X.F) = ((Pr.g i : ℕ) : X.F) := map_natCast (algebraMap (𝓞 X.F) X.F) _
    rw [h0, map_natCast]
    exact this.symm
  have ht' : algebraMap X.F X.E (t : X.F) = (Pr.piG i : X.E) + hc.sig (Pr.piG i : X.E) := by
    have := congrArg (algebraMap (𝓞 X.E) X.E) ht
    rw [map_add, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 X.F) X.F X.E] at this
    exact this
  have htv : t ∉ v.asIdeal := by
    intro htv
    have hov := gwOf_over hc hPr i v h
    have h1 : algebraMap (𝓞 X.F) (𝓞 X.E) t ∈ (gwOf hc hPr i v h).1.asIdeal := by
      have : t ∈ (gwOf hc hPr i v h).1.asIdeal.comap (algebraMap (𝓞 X.F) (𝓞 X.E)) := hov ▸ htv
      exact this
    have h3 : X.conjO (Pr.piG i) ∈ (gwOf hc hPr i v h).1.asIdeal := decoFin_mem_of_mem_divs (gwOf_mem hc hPr i v h)
    have h4 : Pr.piG i ∈ (gwOf hc hPr i v h).1.asIdeal := by
      have h5 : Pr.piG i = algebraMap (𝓞 X.F) (𝓞 X.E) t - X.conjO (Pr.piG i) := by
        rw [ht]
        show Pr.piG i = Pr.piG i + cO X.E (Pr.piG i) - cO X.E (Pr.piG i)
        ring
      rw [h5]
      exact Ideal.sub_mem _ h1 h3
    obtain ⟨a, b, e⟩ := hPr.piG_cop i
    apply one_notMem (gwOf hc hPr i v h).1
    rw [← e]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h4) (Ideal.mul_mem_left _ _ h3)
  obtain ⟨s⟩ := Formalism.MainNotions.Gaps.LG.sc_core hc.sig (fun x => by rw [hsig, hsig, star_star])
    (fun x hx => (hc.fixed x).1 hx) hc.deg2 v (Pr.piG i) t (Pr.g i : 𝓞 X.F) ht' hN h htv
  exact Formalism.MainNotions.Gaps.LG.sc_orient s (Pr.piG i) (Pr.g i : 𝓞 X.F) h hN.symm

def gSplit : GSplit (Pr := Pr) hc where
  sp i v h := (Classical.choice (gls_exists hc hPr i v h)).φ
  sp_sig i v h := (Classical.choice (gls_exists hc hPr i v h)).sig
  sp_alg i v h := (Classical.choice (gls_exists hc hPr i v h)).alg
  sp_pi i v h := (Classical.choice (gls_exists hc hPr i v h)).ori

end Ex

end Formalism.L2.Col
