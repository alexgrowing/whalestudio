import Mathlib
import Development.AutomorphicArithmetic.DivisorFrames.LevChiEqOneOfGoodPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSystemOf
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FamilySplitOperatorsEqLabelOperatorsModels
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalHeckeConjPlaceEqDualLabel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open Formalism.CohomologicalDescent.DepthNonnegative (NablaT)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.FrameAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem UpperTheory.sum_eq_of_dual_sums {G ι κ : Type} {M : Type} [AddCommGroup M] [Module ℂ M] (R : Finset ι) (B : Finset κ)
    (u : ι → G) (v : κ → G) (Fm : G → M)
    (h : ∀ ℓ : Module.Dual ℂ M, ∑ a ∈ B, ℓ (Fm (v a)) = ∑ γ ∈ R, ℓ (Fm (u γ))) :
    ∑ γ ∈ R, Fm (u γ) = ∑ a ∈ B, Fm (v a) := by
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro ℓ
  rw [map_sub, map_sum, map_sum, sub_eq_zero]
  exact (h ℓ).symm

private theorem UpperTheory.dual_invariant_of_trivial_character {G : Type} [Group G] {M : Type} [AddCommGroup M] [Module ℂ M] (J : Subgroup G) (χ : J →* ℂˣ)
    (Fm : G → M) (hF : ∀ (κ : J) g, Fm (g * κ) = ((χ κ : ℂˣ) : ℂ) • Fm g) (ℓ : Module.Dual ℂ M) (g : G) (k : J)
    (hk : χ k = 1) : ℓ (Fm (g * k)) = ℓ (Fm g) := by
  rw [hF, hk, Units.val_one, one_smul]

private theorem UpperTheory.hecke_single_eq_sum {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ)
    (F : Bridge.Gf V → ℂ) (g : Bridge.Gf V) :
    GlobalTheory.Hk3.hkF V P (Finsupp.single d 1) F g =
      ∑ γ ∈ GlobalTheory.Hk3.rep V P d, F (g * (Formalism.L2.Theta.finHom V).rangeRestrict γ) := by
  have e1 : GlobalTheory.Hk3.hkF V P (Finsupp.single d 1) F g =
      (1 : ℂ) • ∑ γ ∈ GlobalTheory.Hk3.rep V P d, F (g * (Formalism.L2.Theta.finHom V).rangeRestrict γ) :=
    Finsupp.sum_single_index
      (h := fun d (z : ℂ) => z • ∑ γ ∈ GlobalTheory.Hk3.rep V P d, F (g * (Formalism.L2.Theta.finHom V).rangeRestrict γ))
      (zero_smul ℂ _)
  exact e1.trans (one_smul ℂ _)

private theorem UpperTheory.level_character_trivial {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))
    (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank)
    (hc' : Formalism.IndefR.Lev.IsBaseFrame V β Λ 1) (P : HeightOneSpectrum (𝓞 D.host.E))
    (h1 : ((1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal)
    (hoff : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P) :
    ∀ y : (levEnv V β L).J, GlobalTheory.Hk3.IsLocElt V P y → (levEnv V β L).χ y = 1 := by
  have hl := fun e f' he => (GlobalTheory.LevSplit.lev_split V β Λ 1 (Formalism.IndefR.Lev.flag1L L) hc').2 P e f' he h1 hoff
  rintro ⟨y, hy⟩ ⟨e, f', a, he, ha, hxa, hs⟩
  obtain rfl : y = (Formalism.L2.Theta.finHom V).rangeRestrict a := Subtype.ext hxa
  exact Units.ext ((hl e f' he).2.1 a ⟨ha, hy⟩ hs)

private theorem UpperTheory.hecke_offprime_sum {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))
    (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank)
    (hβ : ∃ c : ℕ, Formalism.IndefR.Lev.IsBaseFrame V β Λ (1 ^ c)) (P : HeightOneSpectrum (𝓞 D.host.E))
    (hoff : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P)
    (d : List ℤ) (x : Bridge.Gf V) (B : Finset (Bridge.Gf V)) (hd : d.Pairwise (fun a b => b ≤ a))
    (hx : GlobalTheory.Hk3.IsLabElt V P d x) (hB : ∀ a ∈ B, GlobalTheory.Hk3.IsLocElt V P a) (hDC : Bridge.IsDC (levEnv V β L).J x B) :
    ∃ R : Finset (Formalism.L2.Theta.GA D V),
      GlobalTheory.Hk3.SphOp V (Formalism.DivisionValues.conjPl P) (Formalism.IndefR.Mult.dualLab d) R ∧
      ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (Fm : Bridge.Gf V → M),
        (∀ (κ : (levEnv V β L).J) g, Fm (g * κ) = (((levEnv V β L).χ κ : ℂˣ) : ℂ) • Fm g) → ∀ g,
        ∑ γ ∈ R, Fm (g * (Formalism.L2.Theta.finHom V).rangeRestrict γ) = ∑ a ∈ B, Fm (g * a) := by
  refine hβ.elim fun c hc => ?_
  have hc' : Formalism.IndefR.Lev.IsBaseFrame V β Λ 1 := (one_pow c : (1 : ℕ) ^ c = 1) ▸ hc
  have h1 : ((1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    rw [Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top
  have hχ := UpperTheory.level_character_trivial V β Λ L hc' P h1 hoff
  have H := GlobalTheory.T.doubleCosetOperator_eq_labelOperator_localReps V β Λ 1 L hc' P h1 hoff d x B hd hx hB hDC
  have hs : GlobalTheory.Hk3.SphOp V (Formalism.DivisionValues.conjPl (Formalism.DivisionValues.conjPl P)) d (GlobalTheory.Hk3.rep V P d) := by
    rw [GlobalTheory.SphConj.conjPl_conjPl]
    exact GlobalTheory.SphLabelOps.sphOp_rep H.1
  refine ⟨GlobalTheory.Hk3.rep V P d, GlobalTheory.SphConj.sphOp_conj V _ d _ hs, fun M _ _ Fm hF g => ?_⟩
  refine UpperTheory.sum_eq_of_dual_sums _ _ (fun γ => g * (Formalism.L2.Theta.finHom V).rangeRestrict γ) (fun a => g * a) Fm fun ℓ => ?_
  have h2 := H.2 ℂ (fun h => ℓ (Fm h)) (fun h k hk => UpperTheory.dual_invariant_of_trivial_character _ _ Fm hF ℓ h k (hχ k hk))
  exact (congrFun h2 g).trans (UpperTheory.hecke_single_eq_sum V P d (fun h => ℓ (Fm h)) g)

theorem UpperTheory.exists_sphericalHeckeRep_splitLabel_of_offLevelPlace :
    ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
        {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (j : Fin D.R.m) (t : p.P.T) (Q : (blk p j t).Pl) (k : ℕ), 1 ≤ k → k ≤ (Vc D j).rank →
        (∀ a ∈ hkA p j t (Q, k), GlobalTheory.Hk3.IsLocElt (Vc D j) (plOf p j t Q) a) ∧
        ∃ R : Finset (Formalism.L2.Theta.GA D (Vc D j)),
          GlobalTheory.Hk3.SphOp (Vc D j) (labOf p j t Q) (Formalism.IndefR.Mult.dualLab (Formalism.IndefR.Mult.splitLab (Vc D j).rank k)) R ∧
          ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (Fm : Bridge.Gf (Vc D j) → M),
            (∀ (κ : levJ p j t) g, Fm (g * κ) = ((levChi p j t κ : ℂˣ) : ℂ) • Fm g) → ∀ g,
            ∑ γ ∈ R, Fm (g * (Formalism.L2.Theta.finHom (Vc D j)).rangeRestrict γ) = ∑ a ∈ hkA p j t (Q, k), Fm (g * a) := by
  intro D L hT Gi Gl Kc Y cX ex Csz p j t Q k hpos hk
  obtain ⟨hg, -, -⟩ := (GlobalTheory.GoodPrimes.good_primes p.R.toRealDat (p.P.face p.Dcf p.Spf p.Del p.h0 Csz).lv2
    p.charW.base.lev).2.2.2 p.charW.base.fam t Q.1 Q.2
  have hs := fun x => GlobalTheory.T.split_hecke_element_label_zeros_then_neg_ones (Vc D j) p.R.pl _ ((Q, k) : _ × ℕ) x
  have hloc : ∀ a ∈ hkA p j t (Q, k), GlobalTheory.Hk3.IsLocElt (Vc D j) (plOf p j t Q) a :=
    fun a ha => (hs a).2.1 ((p.R.B.L j t).hecke.hA_loc (Q, k) ⟨hpos, hk⟩ a ha)
  exact ⟨hloc, UpperTheory.hecke_offprime_sum (Vc D j) (p.R.βV j) (p.R.ΛV j) (p.R.datVt j t) (p.charW.base.lev.βV j) (plOf p j t Q) hg
    _ ((p.R.B.L j t).hecke.hx (Q, k)) (hkA p j t (Q, k)) (hs 1).2.2
    ((hs _).1 hk ((p.R.B.L j t).hecke.hx_ok (Q, k) ⟨hpos, hk⟩)) hloc ((p.R.B.L j t).hecke.hDC (Q, k) ⟨hpos, hk⟩)⟩
