import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.SplitSatPre
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.WeilGroupRestriction.ConjugatePlaceNorm
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSatAsc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SatakeParametersOfTwist
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AbsPowOneNotIsAlgRat

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.Rg.Rs

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Rig

namespace RealThetaConjugation

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem conjPl_eq {w u : HeightOneSpectrum (𝓞 E)} (h : PositivityTheory.Rg.BcB.F.ConjPl w u) :
    u = conjSrc (PositivityTheory.NCmp.cc E) w := by
  rcases (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E)
      (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) w u).1 h.1 with rfl | hc
  · have hns : ¬ IsSplitAt u := h.2.resolve_left fun h' => h' rfl
    exact ((GlobalTheory.ConjAtPlace.conjSrc_eq_iff u).2 hns).symm
  · have e : w = conjSrc (PositivityTheory.NCmp.cc E) u := eq_conjSrc hc
    rw [e, PositivityTheory.NCmp.conjSrc_conjSrc]

theorem part_flip (hS : StrSat) {N : ℕ} (V : Submodule ℂ (Sm E N))
    (σ : ∀ w : HeightOneSpectrum (𝓞 E), SmIrr (GL (Fin N) (w.adicCompletion E))) (hN : 1 ≤ N) (hV : IsDiscrete V)
    (hloc : ∀ w, IsLocCompGL V w (σ w)) (hc : PositivityTheory.Rg.BcN.CsdAsc V) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ b : Multiset ℂˣ,
      (GlobalTheory.LGrp.IsSpherical (σ w).ρ (GlobalTheory.LFun.KGL w N) ∧ GlobalTheory.LFun.HasSatGL w (σ w).ρ b) ∧
      (GlobalTheory.LGrp.IsSpherical (σ (conjSrc (PositivityTheory.NCmp.cc E) w)).ρ (GlobalTheory.LFun.KGL (conjSrc (PositivityTheory.NCmp.cc E) w) N) ∧
        GlobalTheory.LFun.HasSatGL (conjSrc (PositivityTheory.NCmp.cc E) w) (σ (conjSrc (PositivityTheory.NCmp.cc E) w)).ρ (b.map (·⁻¹))) := by
  obtain ⟨a, d, P, hu, hn, hcsd, he⟩ := hc
  have hex : ∀ s : ℝ, ∃ χ : Formalism.L2.Host.HChar E, χ.IsAbsPow s :=
    fun s => ⟨_, GlobalTheory.HeckeGal.Model.absPow_isAbsPow E s⟩
  choose χ hχ using hex
  have h1 := hS E N a d V P σ hN hV hu hn he hloc (fun k => χ (spehExp d k)) (fun k => hχ _)
  have h0 : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ C, (CG.mk P).HasSat w C := by
    filter_upwards [PositivityTheory.Rg.Rs.satakeAscent.eventually_spherical P] with w hw
    exact GlobalTheory.CuspRep.UnrSat.exists_hasSatGL_locRep PositivityTheory.Rg.HF.GL.automorphicFormsFiniteGL E a P w hw
  have hcw : Filter.Tendsto (conjSrc (PositivityTheory.NCmp.cc E)) Filter.cofinite Filter.cofinite :=
    (conjSrc_injective _).tendsto_cofinite
  filter_upwards [h1, h0, hcw.eventually h1] with w g1 g2 g3
  obtain ⟨bw, hbw, hsw, hσw⟩ := g1
  obtain ⟨C, hC⟩ := g2
  obtain ⟨bc, hbc, hsc, hσc⟩ := g3
  refine ⟨∑ k, bw k, ⟨hsw, hσw⟩, hsc, ?_⟩
  have hCc := PositivityTheory.Pf1.CLGD.K.ConjugatePlaceNorm.hasSat_conj P hcsd w C hC
  have ew : ∀ k, bw k = C.map (· * (χ (spehExp d k)).val w) := fun k =>
    CG.HasSat.unique (hbw k) ((CG.hasSat_mk _ _ _).2
      (GlobalTheory.SphGal.hasSatGL_twist E a P _ w C ((hχ _).1 w) ((CG.hasSat_mk _ _ _).1 hC)))
  have ec : ∀ k, bc k = (C.map (·⁻¹)).map (· * (χ (spehExp d k)).val (conjSrc (PositivityTheory.NCmp.cc E) w)) := fun k =>
    CG.HasSat.unique (hbc k) ((CG.hasSat_mk _ _ _).2
      (GlobalTheory.SphGal.hasSatGL_twist E a P _ _ _ ((hχ _).1 _) ((CG.hasSat_mk _ _ _).1 hCc)))
  have hq : Ideal.absNorm (conjSrc (PositivityTheory.NCmp.cc E) w).asIdeal = Ideal.absNorm w.asIdeal :=
    GlobalTheory.ThetaSatake.absNorm_cw w
  have hxy : ∀ k : Fin d, ((χ (spehExp d k.rev)).val w)⁻¹ = (χ (spehExp d k)).val (conjSrc (PositivityTheory.NCmp.cc E) w) :=
    fun k => by
      apply Units.ext
      rw [Units.val_inv_eq_inv_val, (hχ (spehExp d k.rev)).2.1 w, (hχ (spehExp d k)).2.1, hq,
        PositivityTheory.Rg.Rs.satakeAscent.spehExp_rev, ← Complex.cpow_neg]
      congr 1
      push_cast
      ring
  have key : (∑ k, bw k).map (·⁻¹) = ∑ k, bc k := by
    calc (∑ k, bw k).map (·⁻¹) = Multiset.mapAddMonoidHom (fun z : ℂˣ => z⁻¹) (∑ k, bw k) := rfl
      _ = ∑ k, (bw k).map (·⁻¹) := map_sum _ _ _
      _ = ∑ k, (bw k.rev).map (·⁻¹) := (Fintype.sum_equiv Fin.revPerm _ _ fun _ => rfl).symm
      _ = ∑ k, bc k := Finset.sum_congr rfl fun k _ => by
        rw [ew, ec, Multiset.map_map, Multiset.map_map]
        refine Multiset.map_congr rfl fun z _ => ?_
        simp only [Function.comp_apply, mul_inv, hxy k]
  rw [key]
  exact hσc

end RealThetaConjugation

open RealThetaConjugation in
theorem rThetaN : RThetaN := by
  intro hS E _ _ _ n D hD
  have hall : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∀ i, ∃ b : Multiset ℂˣ,
      (GlobalTheory.LGrp.IsSpherical (D.σ i w).ρ (GlobalTheory.LFun.KGL w (D.N i)) ∧ GlobalTheory.LFun.HasSatGL w (D.σ i w).ρ b) ∧
      (GlobalTheory.LGrp.IsSpherical (D.σ i (conjSrc (PositivityTheory.NCmp.cc E) w)).ρ
                   (GlobalTheory.LFun.KGL (conjSrc (PositivityTheory.NCmp.cc E) w) (D.N i)) ∧
        GlobalTheory.LFun.HasSatGL (conjSrc (PositivityTheory.NCmp.cc E) w) (D.σ i (conjSrc (PositivityTheory.NCmp.cc E) w)).ρ (b.map (·⁻¹))) :=
    Filter.eventually_all.2 fun i =>
      part_flip hS (D.V i) (D.σ i) (D.pos i) (D.discrete i) (D.loc i) (hD i)
  filter_upwards [hall] with w hw
  choose b hb using hw
  refine ⟨∑ i, b i, ⟨b, fun i => (hb i).1, rfl⟩, fun u hu => ?_⟩
  obtain rfl := conjPl_eq hu
  refine ⟨fun i => (b i).map (·⁻¹), fun i => (hb i).2, ?_⟩
  exact (map_sum (Multiset.mapAddMonoidHom fun z : ℂˣ => z⁻¹) b Finset.univ).symm

end PositivityTheory.Rg.BcB.F.Rig

end
