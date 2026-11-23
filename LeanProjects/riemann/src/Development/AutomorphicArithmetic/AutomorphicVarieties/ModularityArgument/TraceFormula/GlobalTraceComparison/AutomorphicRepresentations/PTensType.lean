import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.OrthZero
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiInvTop
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiVecExHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.TwtrContOfMem
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.IntegrableTens
import GroundTheory.AutomorphicForms.AdelicGLn

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.Zero.ConvolutionTheory.EB
open PositivityTheory.Rg.BcB.CG.prime_not_mem_section_base_place
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem uAt_mul' (v : InfinitePlace E) (k k' : Kinf E n) : uAt v (k * k') = uAt v k * uAt v k' := by
  apply Subtype.ext
  show ((k * k' : Kinf E n) : Matrix (Fin n) (Fin n) (Cinf E)).map (evV v) =
    (k : Matrix (Fin n) (Fin n) (Cinf E)).map (evV v) * (k' : Matrix (Fin n) (Fin n) (Cinf E)).map (evV v)
  rw [← Matrix.map_mul]
  rfl

private theorem coef_mul' (M : Mods E n) (I L : IxA M) (x k : Kinf E n) :
    coef M I L (x * k) = ∑ m : IxA M, coef M I m k * coef M m L x := by
  have h1 : ∀ v, ent (M v) ((M v).ρ (uAt v (x * k)⁻¹)) (I v) (L v) =
      ∑ l, ent (M v) ((M v).ρ (uAt v k⁻¹)) (I v) l * ent (M v) ((M v).ρ (uAt v x⁻¹)) l (L v) := by
    intro v
    rw [_root_.mul_inv_rev, uAt_mul', map_mul, PMul.ent_mul]
  calc coef M I L (x * k)
      = ∏ v, ∑ l, ent (M v) ((M v).ρ (uAt v k⁻¹)) (I v) l * ent (M v) ((M v).ρ (uAt v x⁻¹)) l (L v) :=
        Finset.prod_congr rfl fun v _ => h1 v
    _ = ∑ m ∈ Fintype.piFinset fun _ => Finset.univ,
          ∏ v, ent (M v) ((M v).ρ (uAt v k⁻¹)) (I v) (m v) * ent (M v) ((M v).ρ (uAt v x⁻¹)) (m v) (L v) :=
        Finset.prod_univ_sum _ _
    _ = ∑ m : IxA M, coef M I m k * coef M m L x := by
        simp only [Fintype.piFinset_univ, Finset.prod_mul_distrib, coef]

private theorem rinv_Wsp (M : Mods E n) : RInv (Wsp M) := by
  intro f hf k
  induction hf using Submodule.span_induction with
  | mem f h =>
    obtain ⟨p, rfl⟩ := h
    have e : (fun x => coef M p.1 p.2 (x * k)) = ∑ m : IxA M, coef M p.1 m k • coef M m p.2 := by
      funext x
      simp only [coef_mul', Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    show (fun x => coef M p.1 p.2 (x * k)) ∈ Wsp M
    rw [e]
    exact Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨(m, p.2), rfl⟩)
  | zero => exact (Wsp M).zero_mem
  | add a b _ _ ha hb => exact (Wsp M).add_mem ha hb
  | smul c a _ ha => exact (Wsp M).smul_mem c ha

private theorem level_open_compact {b : ℕ} (U : Subgroup (Hf E n b)) (hU : IsOpen (U : Set (Hf E n b))) :
    IsOpen ((U.comap (MonoidHom.inl _ _) ⊓ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n : Subgroup (GL (Fin n) (Af E))) : Set (GL (Fin n) (Af E))) ∧
      IsCompact ((U.comap (MonoidHom.inl _ _) ⊓ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n : Subgroup (GL (Fin n) (Af E))) : Set (GL (Fin n) (Af E))) := by
  have h1 : IsOpen ((U.comap (MonoidHom.inl _ _) : Subgroup (GL (Fin n) (Af E))) : Set (GL (Fin n) (Af E))) :=
    hU.preimage (Continuous.prodMk_left 1)
  have h2 : IsOpen ((U.comap (MonoidHom.inl _ _) ⊓ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n : Subgroup (GL (Fin n) (Af E))) : Set (GL (Fin n) (Af E))) :=
    h1.inter (GroundTheory.Automorphic.AdelicGLn.isOpen_integralFiniteGL E n)
  exact ⟨h2, (GroundTheory.Automorphic.AdelicGLn.isCompact_integralFiniteGL E n).of_isClosed_subset (Subgroup.isClosed_of_isOpen _ h2) Set.inter_subset_right⟩

end SlopeTestRemainingChoices

theorem tensType_pf : TensType := by
  intro E _ _ _ n μa μb _ _ Ma Mb κ ka kb va vb R ψ U ha hb hψ hU hlev i j
  obtain ⟨hKo, hKc⟩ := level_open_compact U hU
  refine ⟨tens_cs ha hb hψ i j, _, Wsp Ma, hKo, hKc, fd_Wsp Ma, rinv_Wsp Ma, fun u hu y => ?_, fun y => ?_⟩
  · have e1 : entA ka i.1.1 j.1.1 (finGL E n u * y.1) = entA ka i.1.1 j.1.1 y.1 := by
      have h := entA_fin ka i.1.1 j.1.1 u⁻¹ y.1
      rwa [map_inv, inv_inv] at h
    have e2 : hFin ((finGL E n u, 1) * y) = ((u, 1) : Hf E n 0) * hFin y := by
      show (gFin (finGL E n u * y.1), gFin (1 * y.2)) = (u * gFin y.1, 1 * gFin y.2)
      rw [map_mul, gFin_finGL, one_mul, one_mul]
    show entA ka i.1.1 j.1.1 (finGL E n u * y.1) * entA kb i.1.2 j.1.2 (1 * y.2) *
        ψ i.2 j.2 (hFin ((finGL E n u, 1) * y)) = entA ka i.1.1 j.1.1 y.1 * entA kb i.1.2 j.1.2 y.2 * ψ i.2 j.2 (hFin y)
    rw [e1, one_mul, e2, hlev i.2 j.2 (u, 1) hu.1 (hFin y)]
  · have e : (fun k : Kinf E n => tens ka kb ψ i j (((kI E n k)⁻¹, 1) * y)) =
        ∑ L : IxA Ma, (entA ka L j.1.1 y.1 * entA kb i.1.2 j.1.2 y.2 * ψ i.2 j.2 (hFin y)) • coef Ma i.1.1 L := by
      funext k
      have e2 : hFin (((kI E n k)⁻¹, 1) * y) = hFin y := by
        have h1 : gFin (infGL E n (Unitary.toUnits k)) = 1 := pFin_infGL _
        show (gFin ((infGL E n (Unitary.toUnits k))⁻¹ * y.1), gFin (1 * y.2)) = (gFin y.1, gFin y.2)
        rw [map_mul, map_inv, h1, inv_one, one_mul, one_mul]
      show entA ka i.1.1 j.1.1 ((infGL E n (Unitary.toUnits k))⁻¹ * y.1) * entA kb i.1.2 j.1.2 (1 * y.2) *
          ψ i.2 j.2 (hFin (((kI E n k)⁻¹, 1) * y)) = _
      rw [entA_inf ha, one_mul, e2, Finset.sum_mul, Finset.sum_mul]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun L _ => by ring
    rw [e]
    exact Submodule.sum_mem _ fun L _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i.1.1, L), rfl⟩)

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end
