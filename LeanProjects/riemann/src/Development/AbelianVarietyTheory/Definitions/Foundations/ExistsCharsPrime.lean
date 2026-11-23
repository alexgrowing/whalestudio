import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FacWithCsNonneg
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HalfLatticeTypes
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCoeffTypeNormsPrincipal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SlopeRec

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.IndefiniteRowSideFullHecke.DescentConstants
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj hiding kap
open GlobalTheory.LevDesc GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.JoinChr Formalism.L2.Host in
set_option maxHeartbeats 1000000 in

theorem exists_unif {T : CoreJ D} (hT : LawsJ T) {j : ℕ} (hj : InR D j) {l : Level T.Q.H} (hA : l.A = 1)
    (Xo : Moduli (T.Q.Dw j) l) (c : Coeff l) :
    ∃ (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r),
      (∀ σ, GoodEmb c σ → GlobalTheory.IndefiniteRowSideFullHecke.HalfLatticeTypes.IsUnifAt (U σ) (D.sp.W j) (dict σ) (T.iota j)) ∧
      ∀ σ, GoodEmb c σ → ∀ k la, ∀ γ ∈ ((U σ).X k).Γ, ((U σ).X k).χ la γ = 1 := by
  have hpos := GlobalTheory.CovTop.Inhab.rank_pos T.toCore hT.pins j hj
  have hW : (D.sp.W j).rank = D.R.r := D.sp.W_rank j hj.1 hj.2
  have hι := (GlobalTheory.TupleCover.iotaOK_and_frame T hT j hj _ T.good_σ₀ _ (hT.spaceW j hj _ T.good_σ₀) hW).1
  obtain ⟨Kf, hKf⟩ := (GlobalTheory.Member.PrincLevel.exists_levelK_and_nhds D (D.sp.W j) l.M).1
  have hpk : ∀ σ, GoodEmb c σ → ∃ (U : Unf Xo c σ D.R.r) (dict : GA D (D.sp.W j) → Σ k, Frame (U.X k).Ψ D.R.r),
      GlobalTheory.IndefiniteRowSideFullHecke.HalfLatticeTypes.IsUnifAt U (D.sp.W j) dict (T.iota j) ∧ ∀ k la γ, (U.X k).χ la γ = 1 := fun σ hσ => by
    obtain ⟨C, hC, hCι⟩ := (GlobalTheory.Member.exists_ctx D _ _ _ Xo c σ (D.sp.W j) D.R.r hW _ hι hpos hA hσ).1
    obtain ⟨un, dict, mu, -, -, hP⟩ := GlobalTheory.Member.exists_pkgLaws D _ _ _ _ _ _ _ _ C hC Kf hKf 1
      ⟨continuous_const, fun _ => rfl⟩ (fun _ => rfl)
    rw [hCι] at hP
    obtain ⟨g, e, F, ik, φ, th, b1, b2, b3⟩ := hP.dictLaws
    exact ⟨C.unf un, dict, ⟨hP.unf, hW, Kf, th, C.x₀, g, e, F, ik, φ, hP.modelW, hP.familyUniformisationBasePointOrthogonal, hKf, b1, b2, hι.emb,
      ⟨1, fun x y => by simpa using hι.isom x y⟩, b3⟩, hP.chi1⟩
  have hall : ∀ σ, ∃ (U : Unf Xo c σ D.R.r) (dict : GA D (D.sp.W j) → Σ k, Frame (U.X k).Ψ D.R.r), GoodEmb c σ →
      GlobalTheory.IndefiniteRowSideFullHecke.HalfLatticeTypes.IsUnifAt U (D.sp.W j) dict (T.iota j) ∧ ∀ k la γ, (U.X k).χ la γ = 1 := fun σ => by
    by_cases hσ : GoodEmb c σ
    · obtain ⟨U, dict, h⟩ := hpk σ hσ
      exact ⟨U, dict, fun _ => h⟩
    · obtain ⟨U, dict, -⟩ := hpk c.F.val.toRingHom rfl
      obtain ⟨y⟩ := GlobalTheory.nonempty_frPt_complex GlobalTheory.closing_of_abelianSchemeLaws GlobalTheory.abelianSchemeLaws_all.2.secTwist _ _ _ _
        Xo c hpos σ
      exact ⟨{ Comp := Unit, X := fun _ => U.X (dict 1).1, un := fun _ _ => y }, fun _ => ⟨(), fun _ => 0⟩,
        fun h => absurd h hσ⟩
  choose U dict hP using hall
  exact ⟨U, dict, fun σ hσ => (hP σ hσ).1, fun σ hσ k la γ _ => (hP σ hσ).2 k la γ⟩

theorem exists_deepLevel (L : SizeData₂ D) {Q : Par D} (hQ : Q.Pins) (h5 : 5 ≤ D.host.splitBound)
    (h15 : Nat.Coprime 15 (D.host.g 0 * D.host.g 1)) :
    ∃ l : Level Q.H, (l.M = levDeep D L ∧ l.A = 1 ∧ Q.l.Dvd l) ∧ IsTypeLevel l := by
  obtain ⟨s, hs⟩ := GlobalTheory.CovTop.Inhab.exists_root h5
  obtain ⟨I, hK, hp, hI⟩ := GlobalTheory.CovTop.Inhab.exists_half Q.H s (by rw [hQ.1.1]; exact hs) (expC D L)
  obtain ⟨l, l1, l2, -, -, -, l6⟩ := GlobalTheory.CoverHalf.exists_coverLevel Q.l hQ.2.1.2 (15 ^ expC D L) I (Odd.pow (by decide))
    (by rw [hQ.2.1.1]; exact h15.pow_left _) hK hp hI
  rw [hQ.2.1.1] at l2
  exact ⟨l, ⟨by rw [l2, levDeep, ← mul_pow]; norm_num, l6, l1⟩,
    (isTypeLevel_of_eq l6 l2 (h15.symm.pow_right _)).1⟩

theorem exists_deepField (T : CoreJ D) {j : ℕ} (hpos : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q) {l : Level T.Q.H}
    (Xo : Moduli (T.Q.Dw j) l) {n : ℕ} (hn : n ≠ 0) :
    ∃ (c : Coeff l) (le : T.Q.c.F ≤ c.F),
      (letI := (GlobalTheory.IndefiniteRowSideFullHecke.HalfLatticeTypes.incl (T := T) le).toAlgebra; IsGalois T.Q.c.F c.F) ∧ FnAlgClosed Xo c ∧
        KPsiIn (Dw := T.Q.Dw j) c ∧ ∃ ζ : c.F, IsPrimitiveRoot ζ n := by
  have hζ := Complex.isPrimitiveRoot_exp n hn
  haveI := T.Q.c.fin
  haveI := IntermediateField.adjoin.finiteDimensional (K := ℚ) (hζ.isIntegral (Nat.pos_of_ne_zero hn)).tower_top
  obtain ⟨c₀, h₀⟩ := GlobalTheory.TupleCover.exists_coeff_ge l
    (T.Q.c.F ⊔ IntermediateField.adjoin ℚ {Complex.exp (2 * Real.pi * Complex.I / n)})
  obtain ⟨c₁, h₁, hc₁⟩ := (GlobalTheory.GeomIrr.compNe_and_exists_fnAlgClosed _ _ _ _ Xo c₀ hpos).2
  obtain ⟨c₂, h₂, hc₂⟩ := GlobalTheory.exists_coeff_typeNorms_principal _ _ (T.Q.Dw j) l c₁
  haveI := c₂.fin
  let N : IntermediateField ℚ ℂ := IntermediateField.normalClosure ℚ c₂.F ℂ
  have hN : c₂.F ≤ N := IntermediateField.le_normalClosure c₂.F
  let c : Coeff l := ⟨N, inferInstance, fun τ a => hN (c₂.conj τ a), hN c₂.zeta_mem, c₂.le.trans hN⟩
  have h0 : c₀.F ≤ N := h₁.trans (h₂.trans hN)
  have le : T.Q.c.F ≤ c.F := le_sup_left.trans (h₀.trans h0)
  refine ⟨c, le, ?_, hc₁ c (h₂.trans hN), hc₂ c hN,
    ⟨_, h0 (h₀ (le_sup_right (a := T.Q.c.F) (IntermediateField.mem_adjoin_simple_self ℚ _)))⟩, ?_⟩
  · letI := (GlobalTheory.IndefiniteRowSideFullHecke.HalfLatticeTypes.incl (T := T) le).toAlgebra
    haveI : IsScalarTower ℚ T.Q.c.F c.F := IsScalarTower.of_algebraMap_eq fun x => by simp
    haveI : Normal ℚ c.F := by
      haveI : Algebra.IsAlgebraic ℚ c₂.F := inferInstance
      exact (Algebra.IsAlgebraic.isNormalClosure_normalClosure (F := ℚ) (K := c₂.F) (L := ℂ)
        fun x => IsAlgClosed.splits _).normal
    haveI : IsGalois ℚ c.F := ⟨⟩
    exact IsGalois.tower_top_of_isGalois ℚ T.Q.c.F c.F
  · exact IsPrimitiveRoot.of_map_of_injective (f := c.F.val) hζ c.F.val.injective

theorem exists_chars_prime {K : Type} [Field K] {g : ℕ} [Fact g.Prime] {ζ : K} (h : IsPrimitiveRoot ζ (g * (g - 1))) :
    (∃ ψ : AddChar (ZMod g) K, ψ ≠ 1) ∧ ∃ om : (ZMod g)ˣ →* Kˣ, Function.Injective om := by
  have hg : g.Prime := Fact.out
  have h1 : 0 < g - 1 := Nat.sub_pos_of_lt hg.one_lt
  have hp := Nat.mul_pos hg.pos h1
  constructor
  · have hz : IsPrimitiveRoot (ζ ^ (g - 1)) g := h.pow hp (mul_comm _ _)
    refine ⟨AddChar.zmodChar g hz.pow_eq_one, fun e => ?_⟩
    have := DFunLike.congr_fun e ((1 : ℕ) : ZMod g)
    rw [AddChar.zmodChar_apply', pow_one, AddChar.one_apply] at this
    exact hz.ne_one hg.one_lt this
  · have hz : IsPrimitiveRoot (ζ ^ g) (g - 1) := h.pow hp rfl
    have hu := hz.isUnit_unit h1.ne'
    have hc : Nat.card (ZMod g)ˣ = Nat.card (Subgroup.zpowers (hz.isUnit h1.ne').unit) := by
      rw [Nat.card_zpowers, ← hu.eq_orderOf, Nat.card_eq_fintype_card, ZMod.card_units]
    exact ⟨(Subgroup.subtype _).comp (mulEquivOfCyclicCardEq hc).toMonoidHom,
      Subtype.val_injective.comp (mulEquivOfCyclicCardEq hc).injective⟩

theorem exists_chars {K : Type} [Field K] {ζ : K} (h : IsPrimitiveRoot ζ (∏ k, D.host.g k * (D.host.g k - 1))) :
    (∃ ψ : ∀ v : Sq D.host, AddChar (ZMod (D.host.g v.1)) K, IsGenericFamily ψ) ∧
      ∃ om : ∀ k : Fin 2, (ZMod (D.host.g k))ˣ →* Kˣ, IsGeneratorFamily om := by
  have hk : ∀ k : Fin 2, (∃ ψ : AddChar (ZMod (D.host.g k)) K, ψ ≠ 1) ∧
      ∃ om : (ZMod (D.host.g k))ˣ →* Kˣ, Function.Injective om := fun k => by
    obtain ⟨a, ha⟩ := Finset.dvd_prod_of_mem (fun k => D.host.g k * (D.host.g k - 1)) (Finset.mem_univ k)
    exact exists_chars_prime (h.pow (Finset.prod_pos fun k _ => Nat.mul_pos (D.host.g_prime k).pos
      (Nat.sub_pos_of_lt (D.host.g_prime k).one_lt)) (ha.trans (mul_comm _ _)))
  choose ψ hψ using fun k => (hk k).1
  choose om hom using fun k => (hk k).2
  exact ⟨⟨fun v => ψ v.1, fun v => hψ v.1⟩, om, hom⟩

end GlobalTheory.SlopeRec
