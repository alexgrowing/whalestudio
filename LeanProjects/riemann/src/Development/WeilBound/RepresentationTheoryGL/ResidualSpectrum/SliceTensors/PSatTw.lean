import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSatDefs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SatakeParametersOfTwist
import Development.AbelianVarietyTheory.Definitions.Foundations.AbsCharNotUnitary

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.UG
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.LFun GlobalTheory.PRep

namespace PositivityTheory.Rg.Rs.SatakeVectors

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem finRep_mulChi {m : ℕ} (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin m) (w.adicCompletion E))
    (x : Sm E m) :
    finRep E m (locGL E m w g) (mulChi m χ x) =
      ((χ.loc w (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) • mulChi m χ (finRep E m (locGL E m w g) x) := by
  have := act_mulChi (o := (Op.fin (locGL E m w g) : Op E m)) χ x
  rw [opAdd, zero_smul, add_zero, opMul, CuspSub.chiDet_locGL, map_smul] at this
  exact this

theorem satLike_map_mulChi {m : ℕ} {V : Submodule ℂ (Sm E m)} {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ}
    {χ : HChar E} (hχ : χ.UnrAt w) (h : SatLike V w B) :
    SatLike (V.map (mulChi m χ).toLinearMap) w (B.map (· * χ.val w)) := by
  intro ψ hψ hK h0
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hψ
  have hxK : ∀ k ∈ KGL w m, finRep E m (locGL E m w k) x = x := fun k hk => by
    have e := hK k hk
    rw [LinearEquiv.coe_coe, finRep_mulChi, hχ _ (GlobalTheory.SphGal.isUnitAt_det_of_mem hk), Units.val_one,
      one_smul] at e
    exact (mulChi m χ).injective e
  have hx0 : x ≠ 0 := fun e => h0 (by rw [e, map_zero])
  have hs := h x hx hxK hx0
  refine ⟨h0, GlobalTheory.LGrp.mem_fixed.2 fun k hk => hK k hk, by rw [Multiset.card_map, hs.2.2.1],
    fun ϖ hϖ j hj => ?_⟩
  rw [LinearEquiv.coe_coe, GlobalTheory.SphGal.satEig_map_mul, mul_smul, ← map_smul (mulChi m χ),
    ← hs.2.2.2 ϖ hϖ j hj, heckeVec, heckeVec]
  have e := (mulChi m χ).toAddEquiv.map_finsum
    (fun c : _ ⧸ KGL w m => Tj ℂ m (Ov E w) ϖ j c.out • ((finRep E m).comp (locGL E m w)) c.out x)
  rw [show (mulChi m χ) _ = _ from e, smul_finsum]
  refine finsum_congr fun c => ?_
  by_cases hc : Tj ℂ m (Ov E w) ϖ j c.out = 0
  · simp [hc]
  · change Tj ℂ m (Ov E w) ϖ j c.out • finRep E m (locGL E m w c.out) (mulChi m χ x) = _
    rw [finRep_mulChi, GlobalTheory.SphGal.loc_det_of_Tj hχ hϖ hj hc, smul_comm]
    simp

open GlobalTheory.Mem.Chr.CharModel in
omit [IsTotallyComplex E] in
theorem unrAt_absC (s : ℂ) (w : HeightOneSpectrum (𝓞 E)) : (Model.absC E s).UnrAt w := fun x hx => Units.ext (by
  change Complex.exp (s * logNorm E (GlobalTheory.Mem.Chr.localIdele E w x)) = 1
  rw [logNorm_local w x 0 (by simpa [Formalism.L2.Host.IsUnitAt] using hx)]; simp)

open GlobalTheory.Mem.Chr.CharModel in
theorem val_absC (s : ℂ) (w : HeightOneSpectrum (𝓞 E)) : (Model.absC E s).val w = qU w (-s) := Units.ext (by
  change Complex.exp (s * logNorm E (GlobalTheory.Mem.Chr.localIdele E w (Formalism.L2.Host.atFin w (Formalism.L2.Host.unif w)))) = _
  have h0 : (Ideal.absNorm w.asIdeal : ℕ) ≠ 0 := by simpa [Ideal.absNorm_eq_zero_iff] using w.ne_bot
  rw [qU_val, logNorm_local w _ 1 (Formalism.L2.Host.unif_spec w), Complex.cpow_def_of_ne_zero (by exact_mod_cast h0),
    ← Complex.natCast_log]
  congr 1; push_cast; ring)

theorem satLike_tw {m : ℕ} {V : Submodule ℂ (Sm E m)} {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ}
    (h : SatLike V w B) (z : ℂ) : SatLike (tw V z) w (B.map (· * qU w (-z))) := by
  have := satLike_map_mulChi (unrAt_absC z w) h
  rw [val_absC] at this
  exact this

end PositivityTheory.Rg.Rs.SatakeVectors

end
