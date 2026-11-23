import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ComplEquivEvW
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels ComplexConjugate
open GlobalTheory.FunObj GlobalTheory.StdFrames GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.SplitTie
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem cpt_finAd {D : D7} (Q : Pl D.host.E) (z : AE D) :
    cpt (D := D) Q (toEAf D z) = GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D z) Q := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero, RingHom.map_zero, RingEquiv.map_zero]; rfl
  | tmul a x =>
    have h1 := congrArg (fun s : FiniteAdeleRing (𝓞 D.host.E) D.host.E => s Q) (toAd_spec D x a.2)
    have h2 := congrArg (fun s : FiniteAdeleRing (𝓞 D.host.E) D.host.E => s Q)
      ((GlobalTheory.LFun.toFinAd_tmul (F := D.host.F) a.2 x).trans (mul_comm _ _))
    exact h1.trans h2.symm
  | add a b ha hb => rw [RingHom.map_add, RingHom.map_add, RingHom.map_add, RingEquiv.map_add, ha, hb]; rfl

private theorem cpt_loc {D : D7} (w Q : Pl D.host.E) (y : (Kw w)ˣ) :
    cpt (D := D) Q (toEAf D (GlobalTheory.LFun.locIdele D.host.F w y : AE D)) =
      (Neutral.B1.finiteSingle D.host.E w (y : Kw w)) Q := by
  rw [cpt_finAd]
  exact congrArg (fun z : FiniteAdeleRing (𝓞 D.host.E) D.host.E => z Q) (GlobalTheory.LFun.finTens_locIdele (F := D.host.F) w y)

open Classical in
private theorem cpt_sum {D : D7} {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P) (Q : Pl D.host.E) :
    cpt (D := D) Q (toEAf D e) = if Q ∈ P then 1 else 0 := by
  obtain ⟨⟨es, hes, hsum⟩, -⟩ := he
  rw [hsum, map_sum (toEAf D), map_sum (cpt (D := D) Q)]
  split_ifs with hQ
  · rw [Finset.sum_eq_single Q (fun P hP hPQ => (cpt_of_isIdemAt (hes P hP)).2 Q (Ne.symm hPQ))
      (fun h => absurd hQ h)]
    exact (cpt_of_isIdemAt (hes Q hQ)).1
  · exact Finset.sum_eq_zero fun P hP => (cpt_of_isIdemAt (hes P hP)).2 Q (fun h => hQ (h ▸ hP))

private theorem cpt_prod {D : D7} {ι : Type} [Fintype ι] (w : ι → Pl D.host.E) (hw : Function.Injective w)
    (y : ∀ i, (Kw (w i))ˣ) :
    infPart D ((∏ i, GlobalTheory.LFun.locIdele D.host.F (w i) (y i) : (AE D)ˣ) : AE D) = 1 ∧
    (∀ i, cpt (D := D) (w i) (toEAf D ((∏ i, GlobalTheory.LFun.locIdele D.host.F (w i) (y i) : (AE D)ˣ) : AE D)) = y i) ∧
    ∀ Q, (∀ i, w i ≠ Q) → cpt (D := D) Q (toEAf D ((∏ i, GlobalTheory.LFun.locIdele D.host.F (w i) (y i) : (AE D)ˣ) : AE D)) = 1 := by
  refine ⟨?_, fun i => ?_, fun Q hQ => ?_⟩
  · rw [Units.coe_prod, map_prod (infPart D)]
    exact Finset.prod_eq_one fun i _ => GlobalTheory.LFun.infTens_locIdele (F := D.host.F) (w i) _
  · rw [Units.coe_prod, map_prod (toEAf D), map_prod (cpt (D := D) _), Finset.prod_eq_single i]
    · rw [cpt_loc, GlobalTheory.LFun.finSingle_self]
    · intro b _ hb
      rw [cpt_loc]
      exact GlobalTheory.LFun.finSingle_ne (fun h => hb (hw h).symm) _
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [Units.coe_prod, map_prod (toEAf D), map_prod (cpt (D := D) _)]
    exact Finset.prod_eq_one fun i _ => by
      rw [cpt_loc]
      exact GlobalTheory.LFun.finSingle_ne (hQ i).symm _

private theorem valued_evW {D : D7} {v : Pl D.host.F} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (z : Lev.EAf D) :
    Valued.v (GlobalTheory.BotMatch.evW τ z) = Valued.v (cpt (D := D) (splitPrime τ) z) := by
  rw [← GlobalTheory.BotMatch.complEquiv_evW, complEquiv_apply, SplitTie.valued_complMap]

theorem UpperTheory.unitChar_idempotentSum_eq_prod_unitInd :
    ∀ (D : D7) (ε : AE D) (Pw : Finset (Pl D.host.E)), IsIdemSum ε Pw → ∀ (ι : Type) [Fintype ι] (pl : ι → Pl D.host.F)
        (τ : ∀ i, D.host.E →ₐ[D.host.F] Fv D.host.F (pl i)), (∀ w, w ∈ Pw ↔ ∃ i, splitPrime (τ i) = w) →
        Function.Injective (fun i => splitPrime (τ i)) → ∀ (ν : (AE D)ˣ →* Circle) (n : ℕ) (N : Matrix (Fin n) (Fin n) (Lev.EAf D)),
          (∀ i, GlobalTheory.BotMatch.evW (τ i) N.det ∈ 𝒪[Fv D.host.F (pl i)]) →
          GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.unitChar ν ε N = ∏ i, GlobalTheory.StdPairCone.unitInd (chrW ν (τ i)) (GlobalTheory.BotMatch.evW (τ i) N.det) := by
  intro D ε Pw hε ι _ pl τ hPw hinj ν n N hN
  classical
  have hc : ∀ Q, cpt (D := D) Q (1 - toEAf D ε + toEAf D ε * N.det) = if Q ∈ Pw then cpt (D := D) Q N.det else 1 := by
    intro Q
    rw [RingHom.map_add, RingHom.map_sub, RingHom.map_mul, RingHom.map_one, cpt_sum hε]
    split_ifs <;> simp
  by_cases h : ∀ i, GlobalTheory.BotMatch.evW (τ i) N.det ≠ 0 ∧ valuation (Fv D.host.F (pl i)) (GlobalTheory.BotMatch.evW (τ i) N.det) = 1
  · let y : ∀ i, (Kw (D := D) (splitPrime (τ i)))ˣ := fun i =>
      Units.map (complMap (splitPrime_under (τ i))).toMonoidHom (Units.mk0 _ (h i).1)
    have hy : ∀ i, (y i : Kw (D := D) (splitPrime (τ i))) = cpt (D := D) (splitPrime (τ i)) N.det := fun i =>
      GlobalTheory.BotMatch.complEquiv_evW (τ i) N.det
    have hv : ∀ i, Valued.v (y i : Kw (D := D) (splitPrime (τ i))) = 1 := fun i => by
      rw [hy, ← valued_evW]
      exact (GlobalTheory.FlipMatch.isEquiv_Fv (pl i)).eq_one_iff_eq_one.1 (h i).2
    obtain ⟨x, hx⟩ : ∃ x : (AE D)ˣ, x = ∏ i, GlobalTheory.LFun.locIdele D.host.F (splitPrime (τ i)) (y i) := ⟨_, rfl⟩
    obtain ⟨h1, h2, h3⟩ := cpt_prod (fun i => splitPrime (τ i)) hinj y
    obtain ⟨-, h5, h6⟩ := cpt_prod (fun i => splitPrime (τ i)) hinj (fun i => (y i)⁻¹)
    have hxi : x⁻¹ = ∏ i, GlobalTheory.LFun.locIdele D.host.F (splitPrime (τ i)) (y i)⁻¹ := by
      rw [hx, ← Finset.prod_inv_distrib]
      exact Finset.prod_congr rfl fun i _ => (map_inv _ _).symm
    rw [← hx] at h1 h2 h3
    rw [← hxi] at h5 h6
    have hU : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.IsUnitDet ε N x := by
      refine ⟨h1, cpt_ext fun Q => ?_, (mem_OA_iff _).2 fun Q => ?_⟩
      · rw [hc]
        split_ifs with hQ
        · obtain ⟨i, rfl⟩ := (hPw Q).1 hQ
          exact (h2 i).trans (hy i)
        · exact h3 Q fun i hi => hQ ((hPw Q).2 ⟨i, hi⟩)
      · by_cases hQ : ∃ i, splitPrime (τ i) = Q
        · obtain ⟨i, rfl⟩ := hQ
          rw [h5 i, HeightOneSpectrum.mem_adicCompletionIntegers, Units.val_inv_eq_inv_val, map_inv₀, hv, inv_one]
        · rw [h6 Q fun i hi => hQ ⟨i, hi⟩]
          exact one_mem _
    have hex : ∃ x, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.IsUnitDet ε N x := ⟨x, hU⟩
    have he : hex.choose = x := Units.ext (ae_ext (hex.choose_spec.1.trans hU.1.symm) fun Q => by
      rw [hex.choose_spec.2.1, hU.2.1])
    rw [GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.unitChar, dif_pos hex, he, hx, map_prod ν, ← Finset.prod_inv_distrib]
    refine (map_prod Circle.coeHom _ _).trans (Finset.prod_congr rfl fun i _ => ?_)
    rw [GlobalTheory.StdPairCone.unitInd, dif_pos (h i)]
    rfl
  · obtain ⟨i, hi⟩ := not_forall.1 h
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [GlobalTheory.StdPairCone.unitInd, dif_neg hi]),
      GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.unitChar, dif_neg]
    rintro ⟨x, -, h2, h3⟩
    apply hi
    have h4 := (mem_OA_iff _).1 h3 (splitPrime (τ i))
    have h5 : cpt (D := D) (splitPrime (τ i)) (toEAf D (x : AE D)) = cpt (D := D) (splitPrime (τ i)) N.det := by
      rw [h2, hc, if_pos ((hPw _).2 ⟨i, rfl⟩)]
    have h6 : cpt (D := D) (splitPrime (τ i)) N.det * cpt (D := D) (splitPrime (τ i)) (toEAf D ((x⁻¹ : (AE D)ˣ) : AE D)) = 1 := by
      rw [← h5, ← RingHom.map_mul, ← RingHom.map_mul, Units.mul_inv, RingHom.map_one, RingHom.map_one]
    have h7 : Valued.v (cpt (D := D) (splitPrime (τ i)) N.det) ≤ 1 := by
      rw [← valued_evW]
      exact (GlobalTheory.FlipMatch.isEquiv_Fv (pl i)).le_one_iff_le_one.1 ((Valuation.mem_integer_iff _ _).1 (hN i))
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h4
    have h8 := congrArg Valued.v h6
    rw [map_mul, map_one] at h8
    have h9 : Valued.v (GlobalTheory.BotMatch.evW (τ i) N.det) = 1 := by
      rw [valued_evW]
      exact le_antisymm h7 (h8 ▸ mul_le_of_le_one_right' h4)
    exact ⟨fun h0 => by rw [h0, map_zero] at h9; exact zero_ne_one h9,
      (GlobalTheory.FlipMatch.isEquiv_Fv (pl i)).eq_one_iff_eq_one.2 h9⟩
