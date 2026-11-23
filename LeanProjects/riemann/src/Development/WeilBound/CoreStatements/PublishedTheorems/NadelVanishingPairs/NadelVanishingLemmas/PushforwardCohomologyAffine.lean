import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CohomologyVanishingIntersections
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.PassageDown

theorem exists_cover_of_isCompact {X : Scheme.{0}} {H : LB X} (h : IsAmpleLB H) {V : X.Opens}
    (hV : IsCompact (V : Set X)) : ∃ (r : ℕ) (e : Fin r → ℕ) (σ : ∀ a, (lbPow H (e a)).Sec),
      (∀ a, 0 < e a) ∧ (∀ a, IsAffineOpen (nonzeroLocus (σ a))) ∧ ⨆ a, nonzeroLocus (σ a) = V := by
  classical
  have key : ∀ x : V, ∃ n : ℕ, 1 ≤ n ∧ ∃ s : (lbPow H n).Sec, (x : X) ∈ nonzeroLocus s ∧
      nonzeroLocus s ≤ V ∧ IsAffineOpen (nonzeroLocus s) := fun x => h.exists_affine_le x.2
  choose n hn s hxs hsV hsA using key
  obtain ⟨t, ht⟩ := hV.elim_finite_subcover (fun x : V => (nonzeroLocus (s x) : Set X))
    (fun x => (nonzeroLocus (s x)).isOpen) (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hxs _⟩)
  refine ⟨t.card, fun a => n (t.equivFin.symm a), fun a => s (t.equivFin.symm a),
    fun a => hn _, fun a => hsA _, ?_⟩
  apply le_antisymm
  · exact iSup_le fun a => hsV _
  · intro y hy
    have hy' := ht hy
    simp only [Set.mem_iUnion] at hy'
    obtain ⟨i, hi, hyi⟩ := hy'
    rw [TopologicalSpace.Opens.mem_iSup]
    obtain ⟨j, hj⟩ : ∃ j, t.equivFin.symm j = ⟨i, hi⟩ := ⟨_, Equiv.symm_apply_apply _ _⟩
    refine ⟨j, ?_⟩
    show y ∈ nonzeroLocus (s ↑(t.equivFin.symm j))
    rw [hj]
    exact hyi

end GlobalTheory.PassageDown

private theorem passage_cohOn_lemma {X Y : Scheme.{0}} (s : Y ⟶ X) (F : Y.Modules) (V : X.Opens)
    {ι : Type} [LinearOrder ι] [Finite ι] (U : ι → X.Opens) (hV : V ≤ ⨆ i, U i)
    (hP : CechAcyclicMod V U ((Scheme.Modules.pushforward s).obj F))
    (hF : CechAcyclicMod (s ⁻¹ᵁ V) (fun i => s ⁻¹ᵁ U i) F) (n : ℕ) :
    Nonempty (cohOn ((Scheme.Modules.pushforward s).obj F) V n ≃+ cohOn F (s ⁻¹ᵁ V) n) := by
  have hV' : s ⁻¹ᵁ V ≤ ⨆ i, s ⁻¹ᵁ U i := by
    intro y hy
    have hy' := hV hy
    rw [TopologicalSpace.Opens.mem_iSup] at hy' ⊢
    exact hy'
  let φ := cechCubePushforwardIso V U (R := ℤ) F (g := s) (fun r => by simp)
  haveI : IsIso (cechComplexMap φ.hom) :=
    isIso_cechComplexMap _ (fun t _ => ConcreteCategory.bijective_of_isIso (φ.hom.app t))
  let e1 := cechAbHEquivH' hV (cechAcyclicMod_iff.1 hP) n
  let e2 := cechAbHEquivH' hV' (cechAcyclicMod_iff.1 hF) n
  let e3 := cechAbHEquiv ℤ ((Scheme.Modules.pushforward s).obj F) V U n
  let e4 := cechAbHEquiv ℤ F (s ⁻¹ᵁ V) (fun i => s ⁻¹ᵁ U i) n
  let e5 := (HomologicalComplex.homologyMapIso (asIso (cechComplexMap φ.hom)) n).toLinearEquiv.toAddEquiv
  exact ⟨e1.symm.trans (e3.trans (e5.trans (e4.symm.trans e2)))⟩

theorem GlobalTheory.passage_down_of_twist_vanishing : ∀ (X Y : Scheme.{0}) [CompactSpace X] [X.IsSeparated] [CompactSpace Y] [Y.IsSeparated] (s : Y ⟶ X) (F : Y.Modules) [F.IsQuasicoherent] (H : LB X), IsAmpleLB H → (∀ j, 0 < j → ∀ᶠ c : ℕ in atTop, Subsingleton (coh (twist F (lbPow (H.pull s) c)) j)) → (∀ i, Nonempty (coh ((Scheme.Modules.pushforward s).obj F) i ≃+ coh F i)) ∧ ∀ U : X.Opens, IsAffineOpen U → ∀ j, 0 < j → Subsingleton (cohOn F (s ⁻¹ᵁ U) j) := by
  intro X Y _ _ _ _ s F _ H hH hvan
  haveI : SheafOfModules.IsQuasicoherent ((Scheme.Modules.pushforward s).obj F) :=
    GlobalTheory.QCoh.isQuasicoherent_pushforward s F
  have key : ∀ V : X.Opens, IsCompact (V : Set X) → ∀ n,
      Nonempty (cohOn ((Scheme.Modules.pushforward s).obj F) V n ≃+ cohOn F (s ⁻¹ᵁ V) n) := by
    intro V hV n
    obtain ⟨r, e, σ, he, hA, hcov⟩ := GlobalTheory.PassageDown.exists_cover_of_isCompact hH hV
    have hle : ∀ a, nonzeroLocus (σ a) ≤ V := fun a => hcov ▸ le_iSup (fun a => nonzeroLocus (σ a)) a
    have hint : ∀ t : Finset (Fin r), t.Nonempty → IsAffineOpen (⨅ a ∈ t, nonzeroLocus (σ a)) :=
      fun t ht => GlobalTheory.MumfordSupport.isAffineOpen_biInf_of_isSeparated (R := Γ(X, ⊤)) X.toSpecΓ hA t ht
    apply passage_cohOn_lemma s F V (fun a => nonzeroLocus (σ a)) hcov.ge
    · exact cechAcyclicMod_of_isAffineOpen (isAffineOpen_cechOpen_of_le hle hint) _
    · intro t ht q
      rw [← preimage_cechOpen, cechOpen_of_nonempty hle ht]
      exact subsingleton_cohOn_preimage_iInf_nonzeroLocus X Y s F H hH.isLB (q + 1)
        (hvan _ (Nat.succ_pos q)) r e σ he t ht
  refine ⟨fun i => ?_, fun U hU j hj => ?_⟩
  · obtain ⟨f⟩ := key ⊤ (by rw [TopologicalSpace.Opens.coe_top]; exact isCompact_univ) i
    exact ⟨f⟩
  · obtain ⟨f⟩ := key U hU.isCompact j
    haveI : Subsingleton (cohOn ((Scheme.Modules.pushforward s).obj F) U j) := by
      refine subsingleton_cohOn_of_cechAcyclic (ι := Unit) (U := fun _ => U)
        (le_iSup (fun _ : Unit => U) ()) ?_ (by rw [Fintype.card_unit]; exact hj)
      refine cechAcyclicMod_of_isAffineOpen (isAffineOpen_cechOpen_of_le (fun _ => le_rfl) ?_) _
      intro t ht
      obtain ⟨i, hi⟩ := ht
      rwa [show (⨅ _ ∈ t, U) = U from le_antisymm (biInf_le _ hi) (le_iInf₂ fun _ _ => le_rfl)]
    exact f.symm.toEquiv.subsingleton
