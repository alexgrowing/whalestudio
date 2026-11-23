import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FacWithCsNonneg
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsCharsPrime
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.OrthonormalBaseFrameNeg
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.ProjectiveLattices.CuspMulOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SlopeRec

open NumberField Finset Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Indef.Tree GlobalTheory.IndefiniteRowSideFullHecke.DescentConstants Formalism.HN
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
open Formalism.L2.Pj hiding kap
open GlobalTheory.CompHt hiding rhoB
open GlobalTheory.LevDesc GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters

variable {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (Q : ParamsT D L P)

section Deep

variable (T : CoreJ D) (j : ℕ) {l : Level T.Q.H} (Xo : Moduli (T.Q.Dw j) l) (c : Coeff l)
  (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r)

structure IsDeep : Prop where
  level : l.M = levDeep D L ∧ l.A = 1 ∧ T.Q.l.Dvd l
  le : T.Q.c.F ≤ c.F
  galois : letI := (GlobalTheory.IndefiniteRowSideFullHecke.HalfLatticeTypes.incl (T := T) le).toAlgebra; IsGalois T.Q.c.F c.F
  geo : FnAlgClosed Xo c
  typeNorm : KPsiIn (Dw := T.Q.Dw j) c
  size : Real.log (Module.finrank ℚ c.F) ≤ (numAt Q j).dP ∧ Real.log (rootDiscr c.F) ≤ (numAt Q j).rP
  unif : ∀ σ, GoodEmb c σ → GlobalTheory.IndefiniteRowSideFullHecke.HalfLatticeTypes.IsUnifAt (U σ) (D.sp.W j) (dict σ) (T.iota j)
  chi : ∀ σ, GoodEmb c σ → ∀ k la, ∀ γ ∈ ((U σ).X k).Γ, ((U σ).X k).χ la γ = 1

variable (L) in

structure IsDeepLevel : Prop where
  level : l.M = levDeep D L ∧ l.A = 1 ∧ T.Q.l.Dvd l
  le : T.Q.c.F ≤ c.F
  galois : letI := (GlobalTheory.IndefiniteRowSideFullHecke.HalfLatticeTypes.incl (T := T) le).toAlgebra; IsGalois T.Q.c.F c.F
  geo : FnAlgClosed Xo c
  typeNorm : KPsiIn (Dw := T.Q.Dw j) c
  unif : ∀ σ, GoodEmb c σ → GlobalTheory.IndefiniteRowSideFullHecke.HalfLatticeTypes.IsUnifAt (U σ) (D.sp.W j) (dict σ) (T.iota j)
  chi : ∀ σ, GoodEmb c σ → ∀ k la, ∀ γ ∈ ((U σ).X k).Γ, ((U σ).X k).χ la γ = 1

variable {T j} in

theorem exists_isDeepLevel (L : SizeData₂ D) (hT : LawsJ T) (hj : InR D j) (h5 : 5 ≤ D.host.splitBound)
    (h15 : Nat.Coprime 15 (D.host.g 0 * D.host.g 1)) {n : ℕ} (hn : n ≠ 0) :
    ∃ (l : Level T.Q.H) (Xo : Moduli (T.Q.Dw j) l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r)
      (dict : ∀ σ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r),
      IsDeepLevel L T j Xo c U dict ∧ IsTypeLevel l ∧ ∃ ζ : c.F, IsPrimitiveRoot ζ n := by
  have hpos := GlobalTheory.CovTop.Inhab.rank_pos T.toCore hT.pins j hj
  obtain ⟨l, hl, ht⟩ := exists_deepLevel L hT.pins h5 h15
  obtain ⟨Xo⟩ := GlobalTheory.Moduli.moduli_scheme_exists _ _ (T.Q.Dw j) l hpos
  obtain ⟨c, le, h1, h2, h3, h4⟩ := exists_deepField T hpos Xo hn
  obtain ⟨U, dict, h6, h7⟩ := exists_unif hT hj hl.2.1 Xo c
  exact ⟨l, Xo, c, U, dict, ⟨hl, le, h1, h2, h3, h6, h7⟩, ht, h4⟩

variable {Q T j Xo c U dict}

theorem IsDeepLevel.isDeep (h : IsDeepLevel L T j Xo c U dict)
    (hs : Real.log (Module.finrank ℚ c.F) ≤ (numAt Q j).dP ∧ Real.log (rootDiscr c.F) ≤ (numAt Q j).rP) :
    IsDeep Q T j Xo c U dict :=
  ⟨h.level, h.le, h.galois, h.geo, h.typeNorm, hs, h.unif, h.chi⟩

theorem exists_isDeep_of_field (hT : LawsJ T) (hj : InR D j) (hl : l.M = levDeep D L ∧ l.A = 1 ∧ T.Q.l.Dvd l)
    (le : T.Q.c.F ≤ c.F) (hG : letI := (GlobalTheory.IndefiniteRowSideFullHecke.HalfLatticeTypes.incl (T := T) le).toAlgebra; IsGalois T.Q.c.F c.F)
    (hF : FnAlgClosed Xo c) (hK : KPsiIn (Dw := T.Q.Dw j) c)
    (hs : Real.log (Module.finrank ℚ c.F) ≤ (numAt Q j).dP ∧ Real.log (rootDiscr c.F) ≤ (numAt Q j).rP) :
    ∃ U dict, IsDeep Q T j Xo c U dict := by
  obtain ⟨U, dict, h6, h7⟩ := exists_unif hT hj hl.2.1 Xo c
  exact ⟨U, dict, hl, le, hG, hF, hK, hs, h6, h7⟩

theorem ringCost_le_o {K : Type} [Field K] [NumberField K]
    (hs : Real.log (Module.finrank ℚ K) ≤ (numAt Q j).dP ∧ Real.log (rootDiscr K) ≤ (numAt Q j).rP) :
    GlobalTheory.IndefiniteRowSideFullHecke.HalfLatticeTypes.ringCost K ≤ (numAt Q j).o :=
  add_le_add hs.1 hs.2

theorem htPrimes_eq_badPrimes (hM : l.M = levDeep D L) (hA : l.A = 1) (B : ℝ) :
    htPrimes l B = ↑(badPrimes D L B) := by
  have h2 : l.M ≠ 0 := by have := l.three_le; omega
  rw [GlobalTheory.CompHt.htPrimes_eq, badPrimes, Level.M', hA, Nat.lcm_one_right, ← hM,
    Nat.primeFactors_mul (mul_ne_zero two_ne_zero (Int.natAbs_ne_zero.2 (discr_ne_zero _))) h2]

end Deep

section Restrict

variable {K M M' : Type} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup M'] [Module K M']

open Classical in

def restrictOr (φ : M →ₗ[K] M') (C : Submodule K M) (C' : Submodule K M') : C →ₗ[K] C' :=
  if h : ∀ x ∈ C, φ x ∈ C' then φ.restrict h else 0

theorem coe_restrictOr {φ : M →ₗ[K] M'} {C : Submodule K M} {C' : Submodule K M'} (h : ∀ x ∈ C, φ x ∈ C') (x : C) :
    (restrictOr φ C C' x : M') = φ x := by
  rw [restrictOr, dif_pos h]; rfl

end Restrict

section Keeps

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r}

theorem mul_mem_cuspW {G G' : WTZ E} (hG : Even G.2) (hG' : Even G'.2) {f g : Rul Xo c} (hf : f ∈ cuspW Xo c U G)
    (hg : g ∈ cuspW Xo c U G') : f * g ∈ cuspW Xo c U (G + G') := by
  rw [mem_cuspW] at hf hg ⊢
  refine ⟨?_, fun σ hσ => ?_⟩
  · rw [show exZ Dw (G + G') = exZ Dw G + exZ Dw G' from funext fun i => exZ_add _ _ _]
    exact mul_mem_secZ hf.1 hg.1
  · rw [AllWt.rdU_mul, show modelWt (U σ) (G + G') = fun k => modelWt (U σ) G k + modelWt (U σ) G' k from
      funext (modelWt_add (U σ) hG hG')]
    exact holSub_mul siegelSpaceAlgebra_holds (hf.2 σ hσ) (hg.2 σ hσ)

theorem levPh_mem_cuspW {G G' : WTZ E} (hG : Even G.2) (hG' : Even G'.2) (hK : KeepsCusp U (G + G'))
    (hK' : KeepsCusp U G') {S : Subgroup (GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms.LevelAut Dw l)} (χ : S →* (c.F)ˣ) {u f : Rul Xo c}
    (hu : u ∈ cuspW Xo c U G') (hf : f ∈ cuspW Xo c U G) (h : S) : levPh Xo c S χ u f h ∈ cuspW Xo c U (G + G') := by
  rw [levPh_apply, levTr_apply]
  exact Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (hK _ _ (mul_mem_cuspW hG hG' hf (hK' _ _ hu)))

variable (U) in

def IsMultiplier (x : ℝ) (S : Subgroup (GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms.LevelAut Dw l)) (G : WTZ E) (B : ℝ) (u : cuspW Xo c U G) : Prop :=
  u ∈ latW U G ∧ (∀ Z : Comp Xo c, genVal Z (levDet Xo c S u) ≠ 0) ∧
    ∀ σ, GoodEmb c σ → ∀ z : Σ k, Frame ((U σ).X k).Ψ r, z.2 ∈ ((U σ).X z.1).dom → homN (U σ) x G u z ≤ Real.exp B

end Keeps

theorem typeOp_mem_cuspW {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
    {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {G : WTZ D.host.E} (hK : KeepsCusp U G)
    (hl : IsTypeLevel l) (fr : TypeFrame Dw l) (e : MonoidAlgebra c.F (LevelGroup D.host)) {f : Rul Xo c}
    (hf : f ∈ cuspW Xo c U G) : typeOp Xo c hl fr e f ∈ cuspW Xo c U G := by
  rw [typeOp, algOp, Finsupp.linearCombination_apply, Finsupp.sum, LinearMap.sum_apply]
  exact Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (hK _ _ hf)

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure LiftData (T : CoreJ D) (i : Fin D.R.m) : Type 1 where

  l : Level T.Q.H
  typeLevel : IsTypeLevel l

  Xo : Moduli (T.Q.Dw ((i : ℕ) + 1)) l

  c : Coeff l

  U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r

  dict : ∀ σ, GA D (D.sp.W ((i : ℕ) + 1)) → Σ k, Frame ((U σ).X k).Ψ D.R.r

  fr : TypeFrame (T.Q.Dw ((i : ℕ) + 1)) l

  ψ : ∀ v : Sq D.host, AddChar (ZMod (D.host.g v.1)) c.F

  om : ∀ k : Fin 2, (ZMod (D.host.g k))ˣ →* (c.F)ˣ

  u₀ : cuspW Xo c U (gTw T.Q ((i : ℕ) + 1))

theorem inR_succ (i : Fin D.R.m) : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩

namespace LiftData

variable {T : CoreJ D} {i : Fin D.R.m} (Y : LiftData T i)

abbrev Hb : Subgroup (GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms.LevelAut (T.Q.Dw ((i : ℕ) + 1)) Y.l) := grpHR Y.fr

abbrev V (G : WTZ D.host.E) : Submodule Y.c.F (Rul Y.Xo Y.c) := cuspW Y.Xo Y.c Y.U G

def NN : Submodule (𝓞 Y.c.F) (Y.V (gKap T.Q ((i : ℕ) + 1))) := latN Y.fr Y.U _ Y.ψ

def Ph : Y.V (gKapMinus T.Q ((i : ℕ) + 1)) →ₗ[Y.c.F] (Y.Hb → Y.V (gKap T.Q ((i : ℕ) + 1))) :=
  LinearMap.pi fun h => restrictOr (LinearMap.proj h ∘ₗ levPh Y.Xo Y.c Y.Hb (chiHR Y.fr Y.ψ) Y.u₀) _ _

def eGood : Y.V (gKap T.Q ((i : ℕ) + 1)) →ₗ[Y.c.F] Y.V (gKap T.Q ((i : ℕ) + 1)) :=
  restrictOr (goodOp Y.Xo Y.c Y.typeLevel Y.fr Y.om i) _ _

structure Good : Prop where
  deep : IsDeep Q T ((i : ℕ) + 1) Y.Xo Y.c Y.U Y.dict
  roots : HasLevelRoots D.host T.Q.c.F
  generic : IsGenericFamily Y.ψ
  generator : IsGeneratorFamily Y.om
  mult : (i : ℕ) + 1 < D.R.m →
    IsMultiplier Y.U (xiR D) Y.Hb (gTw T.Q ((i : ℕ) + 1)) (numAt Q ((i : ℕ) + 1)).U0 Y.u₀

theorem coe_Ph (hK : KeepsCusp Y.U (gKap T.Q ((i : ℕ) + 1))) (hK' : KeepsCusp Y.U (gTw T.Q ((i : ℕ) + 1)))
    (f : Y.V (gKapMinus T.Q ((i : ℕ) + 1))) (h : Y.Hb) :
    (Y.Ph f h : Rul Y.Xo Y.c) =
      levTr Y.Xo Y.c Y.Hb (chiHR Y.fr Y.ψ) ((f : Rul Y.Xo Y.c) * pull Y.Xo Y.c h (Y.u₀ : Rul Y.Xo Y.c)) := by
  refine coe_restrictOr (φ := LinearMap.proj h ∘ₗ levPh Y.Xo Y.c Y.Hb (chiHR Y.fr Y.ψ) Y.u₀) (fun x hx => ?_) f
  have e := thetaExp_kap (Dw := T.Q.Dw ((i : ℕ) + 1)) ((i : ℕ) + 1)
  have := levPh_mem_cuspW (G := gKapMinus T.Q ((i : ℕ) + 1)) (G' := gTw T.Q ((i : ℕ) + 1)) (even_wtOf _ _)
    (even_wtOf _ _) (e ▸ hK) hK' (chiHR Y.fr Y.ψ) Y.u₀.2 hx h
  rwa [e] at this

theorem coe_eGood (hK : KeepsCusp Y.U (gKap T.Q ((i : ℕ) + 1))) (f : Y.V (gKap T.Q ((i : ℕ) + 1))) :
    (Y.eGood f : Rul Y.Xo Y.c) = goodOp Y.Xo Y.c Y.typeLevel Y.fr Y.om i f :=
  coe_restrictOr (fun _ hx => typeOp_mem_cuspW hK _ _ _ hx) f

variable (h : T.Q.Pins) (hK : KeepsCusp Y.U (gKap T.Q ((i : ℕ) + 1))) (he : IsIdempotentElem (goodIdemTw Y.om i))
include h hK he

theorem eGood_eGood (f : Y.V (gKap T.Q ((i : ℕ) + 1))) : Y.eGood (Y.eGood f) = Y.eGood f := by
  have hpq : 1 ≤ (T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q := by
    rw [(sig_eq h (inR_succ i)).2.2]
    have := D.R.m_add_three_le_k
    simp only [Ranks.r]; omega
  refine Subtype.ext ?_
  rw [Y.coe_eGood hK, Y.coe_eGood hK]
  exact LinearMap.congr_fun (isIdempotentElem_typeOp Y.typeLevel Y.fr hpq he).eq _

theorem good_bad_eq :
    Y.NN ⊓ (LinearMap.range Y.eGood).restrictScalars (𝓞 Y.c.F) = latGood Y.typeLevel Y.fr Y.U _ Y.ψ Y.om i ∧
      Y.NN ⊓ (LinearMap.ker Y.eGood).restrictScalars (𝓞 Y.c.F) = latBad Y.typeLevel Y.fr Y.U _ Y.ψ Y.om i := by
  have hpq : 1 ≤ (T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q := by
    rw [(sig_eq h (inR_succ i)).2.2]
    have := D.R.m_add_three_le_k
    simp only [Ranks.r]; omega
  refine ⟨Submodule.ext fun F => ?_, Submodule.ext fun F => ?_⟩
  · rw [mem_latGood_iff _ _ _ _ _ _ _ hpq he, ← Y.coe_eGood hK, Subtype.coe_inj]
    refine and_congr_right fun _ => ⟨?_, fun hF => ⟨F, hF⟩⟩
    rintro ⟨f, rfl⟩
    exact Y.eGood_eGood h hK he f
  · rw [mem_latBad_iff _ _ _ _ _ _ _ hpq he, ← Y.coe_eGood hK, ZeroMemClass.coe_eq_zero]
    rfl

end LiftData

variable {T : CoreJ D} (h : T.Q.Pins) {i : Fin D.R.m} (Y : LiftData T i) [StarRing Y.c.F] (CI C2 : ℝ)

def facOf : SlopeBoundLiftData Y.c.F (pageOf Q) :=
  facWith Q Y.U Y.dict h (inR_succ i) CI C2 (mixVals Y.Xo Y.c (bZero Q ((i : ℕ) + 1))) Y.Hb Y.NN Y.Ph Y.eGood
    (Nat.card (LevelGroup D.host))

theorem facOf_eq : facOf Q h Y CI C2 = facWith Q Y.U Y.dict h (inR_succ i) CI C2
    (mixVals Y.Xo Y.c (bZero Q ((i : ℕ) + 1))) Y.Hb Y.NN Y.Ph Y.eGood (Nat.card (LevelGroup D.host)) := rfl

theorem facOf_q : (facOf Q h Y CI C2).q' = D.R.m - ((i : ℕ) + 1) := rfl

theorem facOf_q_ne_zero_iff : (facOf Q h Y CI C2).q' ≠ 0 ↔ (i : ℕ) + 1 < D.R.m := by
  rw [facOf_q]; omega

theorem one_le_facOf_g : 1 ≤ (facOf Q h Y CI C2).g := Nat.card_pos (α := LevelGroup D.host)

theorem facOf_NN_le : (facOf Q h Y CI C2).NN ≤ (facOf Q h Y CI C2).Mk :=
  Submodule.map_mono (latN_le Y.fr Y.U _ Y.ψ)

theorem facOf_good_bad (hG : HasGram (nrmAt Y.U Y.dict (gKap T.Q ((i : ℕ) + 1))))
    (hK : KeepsCusp Y.U (gKap T.Q ((i : ℕ) + 1))) (he : IsIdempotentElem (goodIdemTw Y.om i)) :
    (facOf Q h Y CI C2).good = latCo (nrmAt Y.U Y.dict (gKap T.Q ((i : ℕ) + 1)))
        (latGood Y.typeLevel Y.fr Y.U _ Y.ψ Y.om i) ∧
      (facOf Q h Y CI C2).bad = latCo (nrmAt Y.U Y.dict (gKap T.Q ((i : ℕ) + 1)))
        (latBad Y.typeLevel Y.fr Y.U _ Y.ψ Y.om i) := by
  rw [← (Y.good_bad_eq h hK he).1, ← (Y.good_bad_eq h hK he).2]
  exact ⟨facWith_good Q h _ CI C2 _ _ _ _ _ _ hG, facWith_bad Q h _ CI C2 _ _ _ _ _ _ hG⟩

theorem facOf_o_le (hs : Real.log (Module.finrank ℚ Y.c.F) ≤ (numAt Q ((i : ℕ) + 1)).dP ∧
      Real.log (rootDiscr Y.c.F) ≤ (numAt Q ((i : ℕ) + 1)).rP)
    (ho : (numAt Q ((i : ℕ) + 1)).o ≤ (numAt Q ((i : ℕ) + 1)).PPpp) :
    (facOf Q h Y CI C2).o' ≤ (pageOf Q).PPpp :=
  (ringCost_le_o hs).trans (ho.trans (PPpp_le Q (inR_succ i).1 (inR_succ i).2))

theorem LiftData.exists_deep (L : SizeData₂ D) (hT : LawsJ T) (i : Fin D.R.m) (h5 : 5 ≤ D.host.splitBound)
    (h15 : Nat.Coprime 15 (D.host.g 0 * D.host.g 1)) :
    ∃ Y : LiftData T i, IsDeepLevel L T ((i : ℕ) + 1) Y.Xo Y.c Y.U Y.dict ∧ IsGenericFamily Y.ψ ∧
      IsGeneratorFamily Y.om := by
  obtain ⟨l, Xo, c, U, dict, h1, ht, ζ, hζ⟩ := exists_isDeepLevel L hT (inR_succ i) h5 h15
    (n := ∏ k, D.host.g k * (D.host.g k - 1)) (Finset.prod_pos fun k _ => Nat.mul_pos (D.host.g_prime k).pos
      (Nat.sub_pos_of_lt (D.host.g_prime k).one_lt)).ne'
  obtain ⟨⟨ψ, hψ⟩, om, hom⟩ := exists_chars hζ
  obtain ⟨fr⟩ := ht.nonempty_typeFrame (sig_eq hT.pins (inR_succ i)).2.2
  exact ⟨⟨l, ht, Xo, c, U, dict, fr, ψ, om, 0⟩, h1, hψ, hom⟩

theorem LiftData.exists_good_of_field (hT : LawsJ T) (i : Fin D.R.m) (hi : (i : ℕ) + 1 = D.R.m) {l : Level T.Q.H}
    (hl : l.M = levDeep D L ∧ l.A = 1 ∧ T.Q.l.Dvd l) (ht : IsTypeLevel l) (Xo : Moduli (T.Q.Dw ((i : ℕ) + 1)) l)
    (c : Coeff l) (le : T.Q.c.F ≤ c.F)
    (hG : letI := (GlobalTheory.IndefiniteRowSideFullHecke.HalfLatticeTypes.incl (T := T) le).toAlgebra; IsGalois T.Q.c.F c.F)
    (hF : FnAlgClosed Xo c) (hK : KPsiIn (Dw := T.Q.Dw ((i : ℕ) + 1)) c)
    (hs : Real.log (Module.finrank ℚ c.F) ≤ (numAt Q ((i : ℕ) + 1)).dP ∧
      Real.log (rootDiscr c.F) ≤ (numAt Q ((i : ℕ) + 1)).rP)
    (hr : HasLevelRoots D.host T.Q.c.F) {ζ : c.F} (hζ : IsPrimitiveRoot ζ (∏ k, D.host.g k * (D.host.g k - 1))) :
    ∃ Y : LiftData T i, Y.Good Q := by
  obtain ⟨U, dict, h1⟩ := exists_isDeep_of_field (Xo := Xo) hT (inR_succ i) hl le hG hF hK hs
  obtain ⟨⟨ψ, hψ⟩, om, hom⟩ := exists_chars hζ
  obtain ⟨fr⟩ := ht.nonempty_typeFrame (sig_eq hT.pins (inR_succ i)).2.2
  exact ⟨⟨l, ht, Xo, c, U, dict, fr, ψ, om, 0⟩, h1, hr, hψ, hom, fun h => absurd hi h.ne⟩

open Classical in

def LiftData.ofCore (hT : LawsJ T) (i : Fin D.R.m) (ψ : ∀ v : Sq D.host, AddChar (ZMod (D.host.g v.1)) T.Q.c.F)
    (om : ∀ k : Fin 2, (ZMod (D.host.g k))ˣ →* (T.Q.c.F)ˣ)
    (u₀ : cuspW (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.U ((i : ℕ) + 1)) (gTw T.Q ((i : ℕ) + 1))) : LiftData T i where
  l := T.Q.l
  typeLevel := (isTypeLevel_of_pin hT.pins.2.1).1
  Xo := T.Q.Xo _
  c := T.Q.c
  U := T.U _
  dict σ g := if hσ : GoodEmb T.Q.c σ then T.dict _ σ (cast (congrArg (GA D) (hT.spaceW _ (inR_succ i) σ hσ)).symm g)
    else T.dict _ σ 1
  fr := ((isTypeLevel_of_pin hT.pins.2.1).1.nonempty_typeFrame (sig_eq hT.pins (inR_succ i)).2.2).some
  ψ := ψ
  om := om
  u₀ := u₀

theorem isUnifAt_core (hT : LawsJ T) {j : ℕ} (hj : InR D j) {σ : T.Q.c.F →+* ℂ} (hσ : GoodEmb T.Q.c σ) {V : HSp D}
    (hV : T.V j σ = V) : GlobalTheory.IndefiniteRowSideFullHecke.HalfLatticeTypes.IsUnifAt (T.U j σ) V
      (fun g => T.dict j σ (cast (congrArg (GA D) hV.symm) g)) (T.iota j) := by
  subst hV
  obtain ⟨hr, g, e, F, ik, φ, th, b1, b2, b3, b4⟩ := hT.adPin j hj σ hσ
  obtain ⟨th', hr', c1, c2⟩ := hT.dictU j hj σ hσ
  obtain ⟨_, hm⟩ := hT.modelW j hj σ hσ
  obtain rfl : th' = th := funext fun k => funext fun τ => GlobalTheory.LettersCheck.isInfEmb_unique _ _ _ (c1 k τ) (b3 k τ)
  refine ⟨hT.unf j hj σ hσ, hr, T.Kf j σ, th', T.x₀ j σ, g, e, F, ik, φ, hm, hT.familyUniformisationBasePointOrthogonal j hj σ hσ, ?_, b3, c2, b1, b2, b4⟩
  rw [hT.pins.2.1.1]
  exact hT.levelK j hj σ hσ

theorem LiftData.ofCore_unif (hT : LawsJ T) (i : Fin D.R.m) (ψ om u₀) (σ : T.Q.c.F →+* ℂ) (hσ : GoodEmb T.Q.c σ) :
    GlobalTheory.IndefiniteRowSideFullHecke.HalfLatticeTypes.IsUnifAt ((LiftData.ofCore hT i ψ om u₀).U σ) (D.sp.W ((i : ℕ) + 1))
      ((LiftData.ofCore hT i ψ om u₀).dict σ) (T.iota ((i : ℕ) + 1)) := by
  have e : (LiftData.ofCore hT i ψ om u₀).dict σ =
      fun g => T.dict _ σ (cast (congrArg (GA D) (hT.spaceW _ (inR_succ i) σ hσ).symm) g) :=
    funext fun _ => dif_pos hσ
  rw [e]
  exact isUnifAt_core hT (inR_succ i) hσ (hT.spaceW _ (inR_succ i) σ hσ)

example (hT : LawsJ T) (hκ : DV.KapDef D) (i : Fin D.R.m) (ψ om u₀) :
    (LiftData.ofCore hT i ψ om u₀).V (gKap T.Q ((i : ℕ) + 1)) =
      T.cuspA ((i : ℕ) + 1) (wtA (Formalism.IndefR.FWT.kapTop D i)) (Formalism.IndefR.FWT.kapTop D i).n := by
  rw [gKap, thetaExp_kap_kapTop hT.pins hκ]
  exact cuspW_wtZ _ _

example (hrd : 1 ≤ D.host.rdE) : 0 ≤ (facOf Q h Y CI C2).mv := by
  have h1 : 0 ≤ lrd D := Real.log_nonneg hrd
  have h2 : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  show 0 ≤ shift D
  unfold shift
  positivity

end GlobalTheory.SlopeRec
