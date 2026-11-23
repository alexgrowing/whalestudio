import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqLatFrameOfIsSDFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompIncAAlgebraMap
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsVTOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelPlacesNotIsConjPlaceRealDat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Imports
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.XGeoPlace

theorem exists_prime_mem {A : Type} [CommRing A] (P : Ideal A) (hP : P.IsPrime) (n : ℕ) (hn : n ≠ 0)
    (h : (n : A) ∈ P) : ∃ ℓ : ℕ, ℓ.Prime ∧ (ℓ : A) ∈ P :=
  _root_.GlobalTheory.ExistsPrimeMem.exists_prime_mem P hP n hn h

theorem exists_prime_mem_pl {E : Type} [Field E] [NumberField E] (PP : HeightOneSpectrum (𝓞 E)) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ (ℓ : 𝓞 E) ∈ PP.asIdeal :=
  exists_prime_mem PP.asIdeal PP.isPrime _ (fun h => PP.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)) (Ideal.absNorm_mem _)

end GlobalTheory.XGeoPlace

theorem GlobalTheory.XGeoPlace.exists_place : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (PP : Pl (I.rec7 l Z).host.E), PP ∈ (pk W).Pg ∨ QAll W PP → ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k) (_ : MeasurableSpace k) (_ : BorelSpace k) (q : GlobalTheory.FinPl.SplitPt (I.rec7 l Z) k), Formalism.L2.NTheta.IsIdemAt q.e PP ∧ q.v = PP.under (𝓞 (I.rec7 l Z).host.F) ∧ q.UnitAA ∧ valuation k ((GlobalTheory.LocMod.ofSplit q).pr (GlobalTheory.XGeoStd.piE I l Z u)) = 1 := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u PP hPP
  have hC := hW.pk.bot.hyp.2.2.2.1

  have hnc : ¬ Lev.IsConjPl PP PP := by
    rcases hPP with hg | ⟨t, ht⟩
    · exact GlobalTheory.SeeConjPlaces.pg_not_isConjPl (pk W) W.Q.F.lv2 hC.lev hC.grp PP hg PP hg
    · exact (hC.lev.Q_pl t PP ht).2 PP ht
  obtain ⟨e, he⟩ := GlobalTheory.ParahoricLift.exists_isIdemAt hnc
  obtain ⟨k, _, _, _, _, q, hqe, hqv, hint, -⟩ := GlobalTheory.LocMod.SplitCompl.exists_place _ PP e he

  obtain ⟨ℓ, hℓ, hℓP, h2q, hd⟩ : ∃ ℓ : ℕ, ℓ.Prime ∧ (ℓ : 𝓞 (I.rec7 l Z).host.E) ∈ PP.asIdeal ∧
      (B.host.QS * B.host.q).Coprime ℓ ∧ B.host.d.Coprime ℓ := by
    rcases hPP with hg | ⟨t, ht⟩
    · have hgg := hW.lev.1.1 PP hg
      rw [Nat.cast_mul] at hgg
      obtain ⟨i, hi⟩ : ∃ i : Fin 2, ((B.host.g i : ℕ) : 𝓞 (I.rec7 l Z).host.E) ∈ PP.asIdeal := by
        rcases PP.isPrime.mem_or_mem hgg with h | h
        · exact ⟨0, h⟩
        · exact ⟨1, h⟩
      have hc : (B.host.g i).Coprime (B.host.QS * B.host.q * B.host.d) := by
        rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, B.g_cond i, Nat.gcd_one_left]
      refine ⟨B.host.g i, B.host.g_prime i, hi, (hc.coprime_dvd_right ⟨B.host.d, rfl⟩).symm,
        (hc.coprime_dvd_right (Dvd.intro_left _ rfl)).symm⟩
    · have hoff := (hC.lev.Q_off t PP ht).1
      obtain ⟨ℓ, hℓ, hℓP⟩ := GlobalTheory.XGeoPlace.exists_prime_mem_pl PP
      have key : ∀ m : ℕ, m ∣ B.host.QS * B.host.q * B.host.d * (I.rec7 l Z).sp.T → m.Coprime ℓ := fun m hm =>
        Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hℓ).2 fun hdv =>
          hoff (Ideal.mem_of_dvd _ (Nat.cast_dvd_cast (hdv.trans hm)) hℓP))
      exact ⟨ℓ, hℓ, hℓP, key _ ⟨B.host.d * (I.rec7 l Z).sp.T, by ring⟩, key _ ⟨B.host.QS * B.host.q * (I.rec7 l Z).sp.T, by ring⟩⟩
  have hv : (ℓ : 𝓞 (I.rec7 l Z).host.F) ∈ q.v.asIdeal := by
    rw [hqv, HeightOneSpectrum.under_asIdeal, Ideal.mem_comap, map_natCast]
    exact hℓP
  have hcc : (Ideal.absNorm (I.rec7 l Z).host.ccK).Coprime ℓ := by
    show Nat.Coprime (Ideal.absNorm B.host.ccK) _
    rw [B.ccK_top, Ideal.absNorm_top]
    exact Nat.coprime_one_left _
  have hU : q.UnitAA := GlobalTheory.SeeSaw.StdOff.unitAA_of q hℓ hv h2q hd hcc

  have hT : (((B.T u : ℕ)) : 𝓞 (I.rec7 l Z).host.E) ∉ PP.asIdeal := by
    rcases hPP with hg | ⟨t, ht⟩
    · exact Formalism.L2.Col.T_notMem_vGs l.pr u ⟨PP, (hW.lev.2.1 PP).1 hg⟩
    · exact (hC.lev.Q_off t PP ht).2 u
  set π : 𝓞 (I.rec7 l Z).host.E := X.piT u with hπdef
  have hπ : π ∉ PP.asIdeal := fun h => hT (by
    have h2 := PP.asIdeal.mul_mem_left (B.fields.conjO ((B.primes X).piT u)) h
    have h3 : (B.primes X).piT u * B.fields.conjO ((B.primes X).piT u) ∈ PP.asIdeal := by
      rw [mul_comm]
      exact h2
    rw [l.pr.piT_norm u] at h3
    exact h3)
  have hπ0 : (π : (I.rec7 l Z).host.E) ≠ 0 := fun h0 => hπ (by
    rw [show π = 0 from RingOfIntegers.coe_injective (by simpa using h0)]
    exact zero_mem _)
  have e1 : (GlobalTheory.XGeoStd.piE I l Z u) = (π : (I.rec7 l Z).host.E) := rfl
  have hin1 := (hint (π : (I.rec7 l Z).host.E)).2 ⟨π, 1, fun h => PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simp⟩
  have hin2 := (hint (π : (I.rec7 l Z).host.E)⁻¹).2 ⟨1, π, hπ, by simp [hπ0]⟩
  have hinv : (GlobalTheory.LocMod.ofSplit q).pr ((π : (I.rec7 l Z).host.E)⁻¹) = ((GlobalTheory.LocMod.ofSplit q).pr (π : (I.rec7 l Z).host.E))⁻¹ := by
    show ((GlobalTheory.LocMod.ofSplit q).π.comp (incA (I.rec7 l Z))) _ = (((GlobalTheory.LocMod.ofSplit q).π.comp (incA (I.rec7 l Z))) _)⁻¹
    exact map_inv₀ _ _
  have hne : (GlobalTheory.LocMod.ofSplit q).pr (π : (I.rec7 l Z).host.E) ≠ 0 := by
    show ((GlobalTheory.LocMod.ofSplit q).π.comp (incA (I.rec7 l Z))) (π : (I.rec7 l Z).host.E) ≠ 0
    exact (map_ne_zero _).2 hπ0
  rw [hinv] at hin2
  rw [Valuation.mem_integer_iff] at hin1 hin2
  refine ⟨k, inferInstance, inferInstance, inferInstance, inferInstance, borel k, @BorelSpace.mk _ _ (borel k) rfl, q, hqe ▸ he, hqv, hU, ?_⟩
  rw [e1]
  rw [map_inv₀] at hin2
  exact le_antisymm hin1 ((inv_le_one₀ (zero_lt_iff.2 ((map_ne_zero _).2 hne))).1 hin2)
