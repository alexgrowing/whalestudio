import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegralityAtPrimeLattices.UpLatLoc0Of
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegralityAtPrimeLattices.AwayLoc
import Formalism.LocalToGlobal.LatticeGeometry.GeometryDefinitions.PClassE
import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.StabiliserOfLocalTransport
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsEquiv
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelaf

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace PI.UnitaryGroupMassFormula.IAT

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem inclE_algebraMap' (R : Type) [CommRing R] [Algebra F R] (f : F) :
    inclE (F := F) R (algebraMap F E f) = (1 : E) ⊗ₜ[F] (algebraMap F R f) := by
  show algebraMap F E f ⊗ₜ[F] (1 : R) = _
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one f, TensorProduct.smul_tmul]

theorem exists_not_mem_valuation_div_le_one (v0 p : HeightOneSpectrum (𝓞 F)) (hne : v0 ≠ p) (N : ℤ) (hN : N ≠ 0) :
    ∃ s : 𝓞 F, s ∉ p.asIdeal ∧ v0.valuation F (algebraMap (𝓞 F) F s / (N : F)) ≤ 1 := by
  have hN' : ((N : 𝓞 F)) ≠ 0 := Int.cast_ne_zero.2 hN
  have hv : v0.intValuation (N : 𝓞 F) =
      WithZero.exp (-(multiplicity v0.asIdeal (Ideal.span {((N : 𝓞 F))}) : ℤ)) :=
    v0.intValuation_eq_exp_neg_multiplicity hN'
  have hnot : ¬ (v0.asIdeal ^ (multiplicity v0.asIdeal (Ideal.span {((N : 𝓞 F))})) ≤ p.asIdeal) := by
    intro h
    have := p.isPrime
    have h1 : v0.asIdeal ≤ p.asIdeal := Ideal.IsPrime.le_of_pow_le h
    exact hne (HeightOneSpectrum.ext (v0.isMaximal.eq_of_le p.isPrime.ne_top h1))
  obtain ⟨s, hs, hsp⟩ := Set.not_subset.1 hnot
  refine ⟨s, hsp, ?_⟩
  have hNF : (N : F) = algebraMap (𝓞 F) F (N : 𝓞 F) := (map_intCast _ N).symm
  rw [hNF, map_div₀, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap, hv]
  rw [div_le_one₀ (zero_lt_iff.2 WithZero.exp_ne_zero)]
  exact (v0.intValuation_le_pow_iff_mem s _).2 hs

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem away_core (Λ : Submodule (𝓞 E) (Fin n → E)) (hΛ : Formalism.L2.GlobalTheoryTheory.Comp.IsLat Λ)
    (g1 g2 : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (v0 : HeightOneSpectrum (𝓞 F))
    (hst : ∀ q, q ≠ v0 → ∀ z ∈ Formalism.L2.Geo.Def.PC.latV q Λ,
      ((bc (prV (E := E) q) (g2⁻¹ * g1) : GL (Fin n) (E ⊗[F] q.adicCompletion F)) :
        Matrix (Fin n) (Fin n) (E ⊗[F] q.adicCompletion F)) *ᵥ z ∈ Formalism.L2.Geo.Def.PC.latV q Λ)
    (N : ℤ) (hN : N ≠ 0)
    (hM : ∀ z ∈ Formalism.L2.Geo.Def.PC.latV v0 Λ,
      (fun i => inclE (F := F) (v0.adicCompletion F) ((N : ℤ) : E) *
        ((((bc (prV (E := E) v0) (g2⁻¹ * g1) : GL (Fin n) (E ⊗[F] v0.adicCompletion F)) :
          Matrix (Fin n) (Fin n) (E ⊗[F] v0.adicCompletion F)) *ᵥ z) i)) ∈ Formalism.L2.Geo.Def.PC.latV v0 Λ)
    (s : 𝓞 F) (hs : v0.valuation F (algebraMap (𝓞 F) F s / (N : F)) ≤ 1)
    (x : Fin n → E) (hx : x ∈ Formalism.UG.CS.globLat g1 Λ) :
    (algebraMap (𝓞 F) (𝓞 E) s) • x ∈ Formalism.UG.CS.globLat g2 Λ := by
  set a : E := algebraMap F E (algebraMap (𝓞 F) F s) with ha
  have hcoe : algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) s) = a := rfl
  have hxs : (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (((algebraMap (𝓞 F) (𝓞 E) s) • x) i)) =
      inclE (F := F) (FiniteAdeleRing (𝓞 F) F) a • (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i)) := by
    funext i
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, Algebra.smul_def, hcoe, map_mul]
  set y : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F :=
    ((g1⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i))
    with hy
  have hyl : y ∈ Formalism.L2.Geo.Def.PC.latA (F := F) Λ := hx
  show ((g2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ
      (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (((algebraMap (𝓞 F) (𝓞 E) s) • x) i)) ∈
    Formalism.L2.Geo.Def.PC.latA (F := F) Λ
  have e2 : ((g2⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ
      (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i)) =
      ((g2⁻¹ * g1 : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ y := by
    rw [hy, mulVec_mulVec, ← Units.val_mul, mul_assoc, mul_inv_cancel, mul_one]
  rw [hxs, Matrix.mulVec_smul, e2]
  apply Formalism.L2.Geo.Def.PC.lg Λ hΛ.2
  intro q
  have hz := Formalism.L2.Geo.Def.PC.pr_lat q Λ y hyl
  have e3 : (fun i => prV (E := E) q ((inclE (F := F) (FiniteAdeleRing (𝓞 F) F) a •
      (((g2⁻¹ * g1 : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ y)) i)) =
      fun i => inclE (F := F) (q.adicCompletion F) a *
        ((((bc (prV (E := E) q) (g2⁻¹ * g1) : GL (Fin n) (E ⊗[F] q.adicCompletion F)) :
          Matrix (Fin n) (Fin n) (E ⊗[F] q.adicCompletion F)) *ᵥ (fun j => prV (E := E) q (y j))) i) := by
    rw [← Formalism.L2.Geo.Def.PC.pr_mulVec]
    funext i
    rw [Pi.smul_apply, smul_eq_mul, map_mul]
    rfl
  rw [e3]
  by_cases hq : q = v0
  · subst hq
    have ho : algebraMap F (q.adicCompletion F) (algebraMap (𝓞 F) F s / (N : F)) ∈ q.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, Formalism.UG.P.levelaf_valued_algebraMap]
      exact hs
    have hmem : (1 : E) ⊗ₜ[F] algebraMap F (q.adicCompletion F) (algebraMap (𝓞 F) F s / (N : F)) ∈
        tensInt (F := F) (q.adicCompletion F) (intOE E) (q.adicCompletionIntegers F).toSubring :=
      Subring.subset_closure (Or.inr ⟨⟨_, ho⟩, rfl⟩)
    have hNF : ((N : ℤ) : F) ≠ 0 := Int.cast_ne_zero.2 hN
    have hid : inclE (F := F) (q.adicCompletion F) a =
        ((1 : E) ⊗ₜ[F] algebraMap F (q.adicCompletion F) (algebraMap (𝓞 F) F s / (N : F))) *
          inclE (F := F) (q.adicCompletion F) ((N : ℤ) : E) := by
      rw [ha, show ((N : ℤ) : E) = algebraMap F E ((N : ℤ) : F) from (map_intCast _ N).symm,
        inclE_algebraMap', inclE_algebraMap', Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← map_mul,
        div_mul_cancel₀ _ hNF]
    have := Submodule.smul_mem (Formalism.L2.Geo.Def.PC.latV q Λ) (⟨_, hmem⟩ : Formalism.L2.Geo.Def.PC.SV E q) (hM _ hz)
    convert this using 1
    funext i
    rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, hid, mul_assoc]
  · have hmem : inclE (F := F) (q.adicCompletion F) a ∈
        tensInt (F := F) (q.adicCompletion F) (intOE E) (q.adicCompletionIntegers F).toSubring :=
      Subring.subset_closure (Or.inl ⟨⟨a, ⟨algebraMap (𝓞 F) (𝓞 E) s, hcoe⟩⟩, rfl⟩)
    have := Submodule.smul_mem (Formalism.L2.Geo.Def.PC.latV q Λ) (⟨_, hmem⟩ : Formalism.L2.Geo.Def.PC.SV E q) (hst q hq _ hz)
    convert this using 1
    funext i
    rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul]

end Gen

section F0

open Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0

variable {D : D7} {u : D.what₂.Word}

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem kappa_stab_dl (T : Forms0 D u) (κ : T.cls0.lev.U) :
    κ.1 ∈ stabGL (Formalism.L2.Geo.Def.PC.latA (F := D.host.F)
      (Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D 0 (Nat.zero_le _)) T.cls0.lev.Lb)) := by
  have hLb : Formalism.L2.GlobalTheoryTheory.Comp.IsLat T.cls0.lev.Lb := ⟨T.cls0.lev.Lb_fin, T.cls0.lev.Lb_span⟩
  have hΛ := dual_base_lattice_full T.cls0
  have hκ := level_stabilises_base_lattice T κ
  have hU := ((T.cls0.lev.U_eq _).1 κ.2).1
  have hfix : ∀ g : GL (Fin (D.R.N 0)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F),
      g ∈ stabGL (Formalism.L2.Geo.Def.PC.latA (F := D.host.F) T.cls0.lev.Lb) → Formalism.UG.CS.globLat g T.cls0.lev.Lb = T.cls0.lev.Lb := by
    intro g hg
    conv_rhs => rw [← Formalism.L2.GlobalTheoryTheory.Comp.glob_one (F := D.host.F) hLb]
    ext x
    show ((g⁻¹ : GL (Fin (D.R.N 0)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) *ᵥ _ ∈ Formalism.L2.Geo.Def.PC.latA (F := D.host.F) T.cls0.lev.Lb ↔
      ((((1 : GL (Fin (D.R.N 0)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)))⁻¹ : GL (Fin (D.R.N 0)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) *ᵥ _ ∈ Formalism.L2.Geo.Def.PC.latA (F := D.host.F) T.cls0.lev.Lb
    rw [inv_one, Units.val_one, one_mulVec]
    exact ((inv_mem hg) _).symm
  have h1 := Formalism.L2.GlobalTheoryTheory.Comp.glob_dl_le (sigD D) (gramN D 0 (Nat.zero_le _)) T.cls0.lev.Lb κ.1 hU
  have h2 := Formalism.L2.GlobalTheoryTheory.Comp.glob_dl_le (sigD D) (gramN D 0 (Nat.zero_le _)) T.cls0.lev.Lb κ.1⁻¹ (inv_mem hU)
  rw [hfix _ hκ] at h1
  rw [hfix _ (inv_mem hκ)] at h2
  have h3 := Formalism.L2.GlobalTheoryTheory.Comp.glob_mono κ.1 h2
  rw [Formalism.L2.GlobalTheoryTheory.Comp.glob_inv_glob hΛ] at h3
  have heq := le_antisymm h1 h3
  have hst : κ.1⁻¹ ∈ stabGL (Formalism.L2.Geo.Def.PC.latA (F := D.host.F)
      (Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D 0 (Nat.zero_le _)) T.cls0.lev.Lb)) := by
    intro y
    have := Formalism.L2.GlobalTheoryTheory.Comp.mem_hat_glob hΛ κ.1 y
    rw [heq] at this
    exact this
  simpa using inv_mem hst

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem lattices_away_from_place (T : Forms0 D u) : AwayLat0 T := by
  intro v v' hvv c c' γ η κ h1 h2
  have hΛ := dual_base_lattice_full T.cls0
  have hκ := kappa_stab_dl T κ
  have hne : (T.atT.eV v).1 ≠ (T.atT.eV v').1 := fun h => hvv (T.atT.eV.injective (Subtype.ext h.symm))
  have hc : Ld D u 0 (Nat.zero_le _) c = Formalism.UG.CS.globLat (T.cls0.y c).1
      (Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D 0 (Nat.zero_le _)) T.cls0.lev.Lb) := dual_class_lattice_eq_global T.cls0 c
  have hc' : mulLat γ.1.1 (Ld D u 0 (Nat.zero_le _) c') = Formalism.UG.CS.globLat
      (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 * (T.cls0.y c').1)
      (Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D 0 (Nat.zero_le _)) T.cls0.lev.Lb) := by
    ext x
    rw [mem_mul_lattice_iff, dual_class_lattice_eq_global T.cls0 c']
    have := Formalism.UG.P.csEquiv_mem (Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D 0 (Nat.zero_le _)) T.cls0.lev.Lb) γ.1
      (T.cls0.y c').1 1 (one_mem _) x
    rw [mul_one] at this
    exact this.symm
  have hG1 : (T.cls0.y c).1⁻¹ *
      (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 * (T.cls0.y c').1) = η.1 * κ.1 := by
    rw [h2]; group
  have hG2 : (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 * (T.cls0.y c').1)⁻¹ *
      (T.cls0.y c).1 = κ.1⁻¹ * η.1⁻¹ := by
    rw [h2]; group
  have hS := fun q => Formalism.L2.Geo.Def.PC.stab_pr _ κ.1 hκ q
  obtain ⟨N1, hN1, hM1⟩ := loc_bound (T.atT.eV v).1 _ hΛ
    ((bc (prV (E := D.host.E) (T.atT.eV v).1) ((T.cls0.y c).1⁻¹ *
      (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 * (T.cls0.y c').1)) : GL _ _) : Matrix _ _ _)
  obtain ⟨N2, hN2, hM2⟩ := loc_bound (T.atT.eV v).1 _ hΛ
    ((bc (prV (E := D.host.E) (T.atT.eV v).1) ((bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 *
      (T.cls0.y c').1)⁻¹ * (T.cls0.y c).1) : GL _ _) : Matrix _ _ _)
  obtain ⟨s1, hs1p, hs1⟩ := exists_not_mem_valuation_div_le_one _ _ hne N1 hN1
  obtain ⟨s2, hs2p, hs2⟩ := exists_not_mem_valuation_div_le_one _ _ hne N2 hN2
  have hnP : ∀ s : 𝓞 D.host.F, s ∉ (T.atT.eV v').1.asIdeal →
      algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s ∉ T.atT.Pv v' := by
    intro s hs h
    exact hs ((T.atT.res_v v' s).2 (RingHom.mem_ker.1 h))
  apply le_antisymm
  · intro x hx
    obtain ⟨t, ht, htx⟩ := (rlv_mem_locP _ _ _).1 hx
    rw [hc'] at htx
    have := away_core _ hΛ _ _ (T.atT.eV v).1 (fun q hq z hz => by
        rw [hG1, map_mul, h1 q hq, one_mul]; exact ((hS q) z).1 hz) N1 hN1 hM1 s1 hs1 _ htx
    rw [← hc, smul_smul] at this
    exact (rlv_mem_locP _ _ _).2 ⟨_, fun h => (Ideal.IsPrime.mem_or_mem inferInstance h).elim (hnP s1 hs1p) ht, this⟩
  · intro x hx
    obtain ⟨t, ht, htx⟩ := (rlv_mem_locP _ _ _).1 hx
    rw [hc] at htx
    have := away_core _ hΛ _ _ (T.atT.eV v).1 (fun q hq z hz => by
        rw [hG2, map_mul, map_inv, map_inv, h1 q hq, inv_one, mul_one]; exact ((inv_mem (hS q)) z).1 hz)
      N2 hN2 hM2 s2 hs2 _ htx
    rw [← hc', smul_smul] at this
    exact (rlv_mem_locP _ _ _).2 ⟨_, fun h => (Ideal.IsPrime.mem_or_mem inferInstance h).elim (hnP s2 hs2p) ht, this⟩

end F0

end PI.UnitaryGroupMassFormula.IAT

end
