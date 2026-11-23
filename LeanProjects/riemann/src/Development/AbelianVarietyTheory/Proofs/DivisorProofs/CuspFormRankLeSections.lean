import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeVolSlopeOfTendsto
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagComponentsBijectModuliComponentsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArcZeroCuspSec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TendstoPowMulExp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueRuleOfRegular
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrPtOfEigFrame
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThetaDictionaryComparison
import Development.AbelianVarietyTheory.Definitions.Foundations.CanonicalExponents
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentsPeterssonOrthogonalAndMasses

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField Filter Topology
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

namespace GlobalTheory.CovHt.RankInj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem val_mem_H0 {Z : Model Xo c β} {F : Type} [Field F] {e : F ≃+* c.F} (C : FlagCpt Z e)
    {σ : c.F →+* ℂ} {N : ℕ} {U : Unf Xo c σ N} (hσ : GoodEmb c σ) (hU : IsUnf U) (la : ∀ k, Wt (U.X k).Ψ N)
    (hχ : ∀ k, ∀ γ ∈ (U.X k).Γ, (U.X k).χ (la k) γ = 1) {ex : Ix Dw → ℤ} (h0 : ex none = 0) {g : Rul Xo c}
    (hg : g ∈ GlobalTheory.AllWt.secZ Xo c ex) (hS : ∀ k, rdU U g k ∈ (U.X k).SS (la k)) :
    C.val g ∈ C.Y.H0 (C.LEx ex) ∧ C.Y.vanishOn (C.LEx ex) (C.val g) C.Ybd := by
  haveI : IsLocalRing (CAt σ) := inferInstanceAs (IsLocalRing ℂ)
  refine GlobalTheory.T.exists_affine_equation_holomorphic_limit F (σ.comp e.toRingHom) C.Y _ C.bd _ C.bd_eff (fun y hy =>
    GlobalTheory.ShFam.OpenReg.regularAt_open E H Dw l Xo c O β Z F e C _ h0 _ hg y fun h => hy ((C.bd_supp y).2 h))
    fun y _ V hV => ?_
  obtain ⟨W, hW, hy, φ, fr, t, hWV, hx, hT, ht⟩ := GlobalTheory.T.exists_affine_eigenframe_flag E H Dw l Xo c O β Z F e C y V hV
  refine ⟨W, hW, hy, _, hWV, fun y' hy' => isEqn_LEx C _ (ht y' hy'), fun p q ψ r hψ hs hin hout hpq hq => ?_⟩
  have hφ : ∀ u ∈ Metric.ball (0 : ℂ) r, (ψ u).comp φ = σ := fun u hu => by
    have h1 := hs u hu
    rw [← C.π_str, ← Category.assoc _ C.π, ← Category.assoc _ (genStr Z), hx, OpenReg.spMap_comp, OpenReg.spMap_comp] at h1
    have h2 : (ψ u).comp (φ.comp e.toRingHom) = σ.comp e.toRingHom :=
      congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
    ext z
    simpa using RingHom.congr_fun h2 (e.symm z)
  have hb : IsBdArc Z σ φ _ ψ r := ⟨⟨hψ, hx, hφ⟩, fun s => (C.bd_supp _).1 (hin s),
    fun u hu h s h' => hout u hu h s ((C.bd_supp _).2 h')⟩
  have hy' : ∀ u : ℂ, u ∈ Metric.ball (0 : ℂ) r ∧ u ≠ 0 → ∃ y : FrPt Xo c (CAt σ), Matches fr (ψ u) y := fun u hu =>
    GlobalTheory.T.exists_frame_point_eigenframe E H Dw l Xo c O β Z σ _ φ _ fr (ψ u) hx (hφ u hu.1) (hb.2.2 u hu.1 hu.2)
  have hr : ((r / 2 : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) r ∧ ((r / 2 : ℝ) : ℂ) ≠ 0 := by
    have := hψ.1
    refine ⟨?_, by exact_mod_cast (half_pos this).ne'⟩
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg (half_pos this).le]
    exact half_lt_self this
  haveI : Nonempty (FrPt Xo c (CAt σ)) := ⟨(hy' _ hr).choose⟩
  choose! yy hyy using hy'
  have hv : ∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 →
      ψ u q ≠ 0 ∧ toC (evR Xo c g (yy u)) * ψ u q = ψ u p := fun u hu h =>
    ⟨hq u hu h, (GlobalTheory.T.eigenframe_generic_affine_open E H Dw l Xo c O β Z F e C W hW _ φ fr t _ _ σ (ψ u) (yy u) p q hT h0 hg
      (hφ u hu) (hyy u ⟨hu, h⟩) hpq).symm⟩
  refine (GlobalTheory.KoecherArc.tendsto_val Z hσ hU la hχ h0 hg hS fr hb (fun u hu h => hyy u ⟨hu, h⟩) p q hv).congr' ?_
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (0 : ℂ) hψ.1)] with u h hu
  exact (eq_div_iff (hv u hu h).1).2 (hv u hu h).2

end GlobalTheory.CovHt.RankInj

namespace GlobalTheory.CovHt.RankInj

open GlobalTheory.AllWt GlobalTheory.CovHt.Link

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ}

theorem exOf_none (la : GlobalTheory.AllWt.Weight S.Dw) : exOf S.Dw la 0 none = 0 := by
  show (wtOf S.Dw la 0).2 = 0
  rw [wtOf_snd, mul_zero]

theorem val_mem_Lw (Φ : s.Flag) (k : s.Comp) (la : GlobalTheory.AllWt.Weight S.Dw) {g : Rul s.Xo κ.c}
    (hg : g ∈ cuspW s.Xo κ.c (unf s) (wtOf S.Dw la 0)) : (Φ.C k).val g ∈ (Φ.C k).Y.H0 ((Φ.C k).Lw la) := by
  have hσ : GoodEmb κ.c κ.σ₀ := rfl
  have hu := s.unf κ.σ₀ hσ
  obtain ⟨h1, h2⟩ := mem_cuspW.1 hg
  exact (val_mem_H0 (Φ.C k) hσ ((GlobalTheory.ThetaDictCompare.isUnf_toU _).2 hu.1) (modelWt (unf s κ.σ₀) (wtOf S.Dw la 0))
    (fun k γ _ => hu.2.2.1 k _ γ) (exOf_none la) h1 (GlobalTheory.CuspSecFin.mem_SS_of_mem_holSub _ _ (h2 _ hσ))).1

theorem val_zero {Φ : s.Flag} (k : s.Comp) : (Φ.C k).val 0 = 0 := by
  have L := FlagCpt.fromTest_and_val_laws _ _ _ _ _ _ _ _ _ _ _ (Φ.C k)
  have := L.2.2.2.2 0 0
  rwa [smul_zero, map_zero, zero_mul] at this

theorem eq_zero_of_val (Φ : s.Flag) (k : s.Comp) (Z : Comp s.Xo κ.c) (hZ : Over Φ k Z)
    (la : GlobalTheory.AllWt.Weight S.Dw) {g : Rul s.Xo κ.c} (hg : g ∈ cuspOn (unf s) Z (wtOf S.Dw la 0))
    (h : (Φ.C k).val g = 0) : g = 0 := by
  obtain ⟨q, hq⟩ := GlobalTheory.T.flag_components_biject_moduli_components D A N j S κ s Φ
  have disj := Formalism.L2.Pj.CompSplitPfD.cspD_comp_disj s.Xo κ.c
  have hZk : Z = q k := by
    by_contra hne
    have s0 : Sp (Φ.C k).Y.Fn := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Φ.C k).Y.Fn)
    exact Set.disjoint_left.1 (disj _ _ hne) (hZ s0) (hq k s0)
  obtain ⟨hgW, hgZ⟩ := Submodule.mem_inf.1 hg
  have hs : ∀ i, (Φ.C i).val g = 0 := fun i => by
    by_cases hik : i = k
    · subst hik; exact h
    · letI := (constF κ.e (Φ.C i).Y).toAlgebra
      refine (mem_suppOn.1 hgZ) _ (Φ.C i).y0 fun t ht => ?_
      have hne : q i ≠ Z := by rw [hZk]; exact q.injective.ne hik
      exact Set.disjoint_left.1 (disj _ _ hne) (hq i t) ht
  have hsec := (mem_cuspW.1 hgW).1
  have hex := exOf_none (S := S) la
  obtain ⟨f, -, hf⟩ := existsUnique_rule_of_regular _ _ _ _ _ _ _ _ _ _ _ _ _ _ Φ (exOf S.Dw la 0) hex
    (fun i => (Φ.C i).val g) fun i y hy =>
      GlobalTheory.ShFam.OpenReg.regularAt_open _ _ _ _ _ _ _ _ _ _ _ (Φ.C i) _ hex _ hsec y hy
  exact (hf g ⟨hsec, fun i => rfl⟩).trans (hf 0 ⟨Submodule.zero_mem _, fun i => (val_zero i).trans (hs i).symm⟩).symm

theorem rank_le : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (k : s.Comp) (Z : Comp s.Xo κ.c), Over Φ k Z → ∀ la : AllWt.Weight S.Dw, (∀ τ, Antitone (la τ)) → Cardinal.toENat (Module.rank κ.c.F (cuspOn (unf s) Z (wtOf S.Dw la 0))) ≤ Cardinal.toENat (Module.rank D.what₂.LL ((Φ.C k).Y.H0 ((Φ.C k).Lw la))) := by
  intro D A N j S κ s Φ k Z hZ la _
  have L := FlagCpt.fromTest_and_val_laws _ _ _ _ _ _ _ _ _ _ _ (Φ.C k)
  let jm : cuspOn (unf s) Z (wtOf S.Dw la 0) →+ (Φ.C k).Y.H0 ((Φ.C k).Lw la) :=
    { toFun := fun g => ⟨(Φ.C k).val g, val_mem_Lw Φ k la (cuspOn_le _ _ _ g.2)⟩
      map_zero' := Subtype.ext (val_zero k)
      map_add' := fun a b => Subtype.ext (L.2.2.2.1 a b) }
  have hj : Function.Injective jm := (injective_iff_map_eq_zero jm).2 fun g hg =>
    Subtype.ext (eq_zero_of_val Φ k Z hZ la g.2 (congrArg Subtype.val hg))
  have key := lift_rank_le_of_injective_injectiveₛ (R := κ.c.F) (R' := D.what₂.LL)
    (M := cuspOn (unf s) Z (wtOf S.Dw la 0)) (M' := (Φ.C k).Y.H0 ((Φ.C k).Lw la)) κ.e jm κ.e.injective hj
    (fun r m => Subtype.ext (by
      show (Φ.C k).val (κ.e r • (m : Rul s.Xo κ.c)) = r • (Φ.C k).val m
      rw [L.2.2.2.2, Algebra.smul_def]
      simp [constF]))
  rw [Cardinal.lift_id, Cardinal.lift_id] at key
  exact Cardinal.toENat.monotone' key

end GlobalTheory.CovHt.RankInj

end
