import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.GradedSeries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompletionLines
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankCyclotomicExtAndCyclotomicCharSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConcretePeriodDeRhamModuleFinrankLe
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfIsCrystallineSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankDcrisLetterDeRhamComponentEqDim
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqOfExhaustive
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyClosedOfDictClosed
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapDcrisEqDdRCrystallineUnramified
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankSpanImageEqCard
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanIsLinesOfGraded
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ISupIndepDdRE

noncomputable section

namespace GlobalTheory.SenLines.AllRoots

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.AdmLoc GlobalTheory.SenLines TensorProduct

theorem zeta_isPrimitiveRoot {l : ℕ} [Fact l.Prime] (P : LocPrime l) {s : ℕ} (hs : 1 ≤ s) :
    IsPrimitiveRoot (P.ζQ s) (l ^ s) := by
  obtain ⟨m, rfl⟩ : ∃ m, s = m + 1 := ⟨s - 1, by omega⟩
  have hpow : ∀ k, P.ζQ (k + 1) ^ l ^ k = P.ζQ 1 := by
    intro k
    induction k with
    | zero => simp
    | succ j ih => rw [pow_succ', pow_mul, P.ζQ_succ, ih]
  have h1 : ¬ P.ζQ (m + 1) ^ l ^ m = 1 := by rw [hpow]; exact P.ζQ_one
  have h2 : P.ζQ (m + 1) ^ l ^ (m + 1) = 1 := by
    rw [pow_succ, pow_mul, hpow, P.ζQ_succ, P.ζQ_zero]
  rw [← orderOf_eq_prime_pow h1 h2]
  exact IsPrimitiveRoot.orderOf _

theorem exists_isPt {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P)
    {K : FinExt l} {s : ℕ} {LL : FinExt l} (h : Good K s LL)
    (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (ζ : ↥LL.1) (hζ : IsPrimitiveRoot ζ (l ^ s)) :
    ∃ τ : ↥(Ks K s) →ₐ[ℚ_[l]] ↥LL.1, H.IsPt h i ζ τ := by
  have hs : 1 ≤ s := h.1
  have hLL := h.2.2.2
  have hprim := zeta_isPrimitiveRoot P hs
  have : NeZero (l ^ s) := ⟨(pow_pos (Fact.out : l.Prime).pos s).ne'⟩
  let Φ : Om l →ₐ[ℚ_[l]] Om l := ((H.W K s LL h).emb i).liftNormal (Om l)
  have hΦ : ∀ x : ↥(K0 K), Φ (x : Om l) = (((H.W K s LL h).emb i x : ↥LL.1) : Om l) := fun x =>
    AlgHom.liftNormal_commutes ((H.W K s LL h).emb i) (Om l) x
  have hζ' : IsPrimitiveRoot (ζ : Om l) (l ^ s) := hζ.map_of_injective (f := LL.1.val) Subtype.val_injective
  obtain ⟨a, -, ha⟩ := (hprim.map_of_injective (f := Φ) Φ.injective).eq_pow_of_pow_eq_one hζ'.pow_eq_one
  rw [← map_pow] at ha
  have hpa : IsPrimitiveRoot (P.ζQ s ^ a) (l ^ s) :=
    IsPrimitiveRoot.of_map_of_injective (f := Φ) (ha ▸ hζ') Φ.injective
  have hconj : IsConjRoot ↥(K0 K) (P.ζQ s ^ a) (P.ζQ s) := by
    unfold IsConjRoot
    rw [GlobalTheory.Cyc.minpoly_unramifiedSubfield_eq_cyclotomic K s hs _ hprim, GlobalTheory.Cyc.minpoly_unramifiedSubfield_eq_cyclotomic K s hs _ hpa]
  obtain ⟨σ, hσ⟩ := hconj.exists_algEquiv
  let τ₀ : ↥(Ks K s) →ₐ[ℚ_[l]] Om l := (Φ.comp (σ.restrictScalars ℚ_[l]).toAlgHom).comp (Ks K s).val
  let τ : ↥(Ks K s) →ₐ[ℚ_[l]] ↥LL.1 := τ₀.codRestrict LL.1.toSubalgebra (hLL τ₀)
  have hτ : ∀ y : ↥(Ks K s), ((τ y : ↥LL.1) : Om l) = Φ (σ (y : Om l)) := fun _ => rfl
  refine ⟨τ, fun x y hxy => Subtype.ext ?_, fun y hy => Subtype.ext ?_⟩
  · rw [hτ, hxy, show σ (x : Om l) = x from σ.commutes x, hΦ]
  · rw [hτ, hy, hσ, ha]

theorem linesAt_of_latticeAtLevels {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {H : LocHW l P}
    {E : LocFon l P AI H} {C : LocCmpT l P AI H E} (hT : LocTied l P AI)
    (h4 : GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.LatticeAtLevels l P AI H E C) {K LL : FinExt l} (hA : CaseA K LL)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (U : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Multiset ℤ)
    (hc : CrysWith (P.PD K) (H.W K 1 LL hA.2.2).emb T.ρ U) (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K)))
    (ζ : ↥LL.1) (hζ : IsPrimitiveRoot ζ l) : LinesAt (H.W K 1 LL hA.2.2) T i ζ (U i) := by
  obtain ⟨τ, hpt⟩ := exists_isPt H hA.2.2 i ζ (by rwa [pow_one])
  have hbij : Function.Bijective (algebraMap ↥(K0 K) ↥K.1) :=
    ⟨(algebraMap ↥(K0 K) ↥K.1).injective, fun x => ⟨⟨x.1, x.2, hA.1 x.2⟩, rfl⟩⟩
  have hτ : (GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.resEmb hA.2.2 τ).comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) =
      (H.W K 1 LL hA.2.2).emb i := AlgHom.ext fun x => hpt.1 x _ rfl
  let e : ↥(K0 K) ≃ₐ[ℚ_[l]] ↥K.1 := AlgEquiv.ofBijective (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) hbij
  have hcard : Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = Module.finrank ℚ_[l] ↥K.1 := by
    rw [← Nat.card_congr (e.arrowCongr AlgEquiv.refl), ← Nat.card_eq_of_bijective _ (H.W K 1 LL hA.2.2).emb_bij,
      Nat.card_zmod, e.toLinearEquiv.finrank_eq]
  obtain ⟨hdr, hspan⟩ := GlobalTheory.Per.CrisDR.isDR_of_isCrys l P AI hT K LL T.V T.ρ hc.1
  have hfil := GlobalTheory.Per.DdREqDcris.FildR_eq (P.PD K) T.ρ hbij.2
    (GlobalTheory.Per.DdREqDcris.map_Dcris_eq (P.PD K) T.ρ hbij.2 hspan) (GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.resEmb hA.2.2 τ)
  rw [hτ] at hfil
  have hr := (GlobalTheory.Per.LetterDim.tied_letter_component_finrank l P AI hT K LL T.V T.ρ).2 hcard hdr
    (GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.resEmb hA.2.2 τ)
  have := (GlobalTheory.Per.TiedDdR.ddR_finrank_le l P AI hT K LL T.V T.ρ).1
  have : FiniteDimensional ↥LL.1 ↥(DdRE (P.PD K) T.ρ (GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.resEmb hA.2.2 τ)) :=
    Submodule.finiteDimensional_of_le (S₂ := DdR (P.PD K) T.ρ) inf_le_left
  obtain ⟨u, d, hu, hd, hs⟩ := GlobalTheory.Per.Sen.adapted_basis_jumps (DdRE (P.PD K) T.ρ (GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.resEmb hA.2.2 τ))
    (FildR (P.PD K) T.ρ (GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.resEmb hA.2.2 τ)) (U i) _ hr
    (fun a b hab => inf_le_inf_left _ (GlobalTheory.Per.FilCount.filV_antitone (P.PD K) hab)) (fun a => inf_le_left)
    (fun x hx => (GlobalTheory.Per.FilCount.filV_exhaustive (P.PD K) (LL := ↥LL.1) x).imp fun a ha => ⟨hx, ha⟩)
    (fun x hx => GlobalTheory.Cmp.JumpDict.filV_sep (P.PD K) (LL := ↥LL.1) x fun a => (hx a).2)
    (hc.2 i _ fun x => congrArg (fun f => f x) hτ)
  refine ⟨u, d, hu, hd, GlobalTheory.SenLines.SplitFil.spanIsLines_of_graded _ u d _
    ((H.W K 1 LL hA.2.2).levN_supp T i ζ) hs ?_⟩
  refine ((h4 K 1 LL hA.2.2 T hc.1 i ζ).2.1 τ hpt).2.trans (congrArg _ (funext fun a => ?_))
  exact GlobalTheory.Per.FilLetUnram.toDR_FilLet _ T i _ a hbij.2 hτ (hfil a)

theorem completionLines_of_latticeAtLevels :
    (∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
      ∀ (H : LocHW l P) (F : LocFon l P AI H) (C : LocCmpT l P AI H F),
        GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.LatticeAtLevels l P AI H F C) →
    GlobalTheory.SenLines.CompletionLines :=
  fun h4 l _ P AI hT H F C _ _ hA U T hc _ i ζ hζ =>
    linesAt_of_latticeAtLevels hT (h4 l P AI hT H F C) hA T U hc i ζ hζ

end GlobalTheory.SenLines.AllRoots
