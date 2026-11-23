import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsChartFromCoordinatesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FilteredCohomologyRestrictionBijectiveStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechRefinementCohomologyBijectiveStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CohomologyVanishingAlongIdealFiltrationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteModulesSerreClassStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequenceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineCoverCohomologyFiniteStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineCoverHigherCohomologyVanishesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechVanishingFromCoverStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSmoothCoordinateCoverStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordinatesRestrictAffineOpenStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartIsGoodStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartDividedPowersGradedConstantStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheafFiltrationPropertyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatBaseChangeCohomologyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InOpenOfThickeningMorphismStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InOpenFiniteInfIffStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubMemOfMk
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoverCupActionBasisStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGradedFormOnAffineChartStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
namespace GlobalTheory.CompanionTheory.GrCech

theorem capO_affine {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} (U : Cov q) (n : ℕ)
    (i : Fin (n + 1) → U.ι) : IsAffineOpen (capO U.U i) := by
  classical
  have h := U.inter (Finset.univ.image i) ⟨i 0, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  have e : (⨅ α ∈ Finset.univ.image i, U.U α) = capO U.U i := by
    refine le_antisymm (le_iInf fun a => ?_) (le_iInf₂ fun α hα => ?_)
    · exact iInf₂_le (i a) (Finset.mem_image_of_mem _ (Finset.mem_univ _))
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hα
      exact capO_le U.U i a
  rwa [e] at h

theorem inU_capO {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
    {κ : O →+* R ⧸ I} {ι : Type} (U : ι → X.Opens) {n : ℕ} (i : Fin n → ι) (T : Thick (nlFun γ p X q κ)) :
    InU (capO U i) T ↔ ∀ a, InU (U (i a)) T := by
  have h := GlobalTheory.T.inOpen_finite_inf_iff (γ := γ) (p := p) (q := q) (κ := κ) (fun a => U (i a)) Finset.univ T
  simpa [capO] using h

theorem capT_eq {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
    {κ : O →+* R ⧸ I} {ι : Type} (Q : ObjectProperty (Thick (nlFun γ p X q κ))) (U : ι → X.Opens) {n : ℕ} (i : Fin (n + 1) → ι) :
    capT (fun α => St Q {U α}) i = St Q {capO U i} := by
  funext T
  refine propext ⟨fun h => ⟨(h 0).1, capO U i, rfl, (inU_capO U i T).2 fun a => ?_⟩, ?_⟩
  · obtain ⟨-, V, hV, hT⟩ := h a
    rw [Set.mem_singleton_iff.1 hV] at hT
    exact hT
  · rintro ⟨hq, V, hV, hT⟩ a
    rw [Set.mem_singleton_iff.1 hV] at hT
    exact ⟨hq, _, rfl, (inU_capO U i T).1 hT a⟩

end GlobalTheory.CompanionTheory.GrCech

namespace GlobalTheory.CompanionTheory.GrCech

theorem inU_mono {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
    {κ : O →+* R ⧸ I} {V W : X.Opens} (h : V ≤ W) {T : Thick (nlFun γ p X q κ)} (hT : InU V T) : InU W T :=
  fun x hx => h (hT hx)

theorem vb_cech (hLoc : KH.LocGr) (hPoly : KH.PolyTf) {O : Type} [CommRing O] (l s : ℕ) (hb : TFBase (dividedPowersBot O) l s)
    {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (U : Cov q) (r : ℕ) (hr : r < s) :
    Nonempty (VB (fun W : X.Opens => strV q W) U.U (CrystallineSemistableComparison.Pb.cechH (grF (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥)) r)
      (fun α => St (TF l s) {U.U α}) r)) := by
  classical
  have isF : ∀ Q : ObjectProperty (Thick (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥))), IsFil (sP Q) (sFil Q) :=
    fun Q => GlobalTheory.T.sheaf_filtration_property Q
  choose ω hω using fun α => GlobalTheory.T.exists_graded_form_on_affine_chart hLoc hPoly l s hb q (U.c α) r hr
  have hT : ∀ {n : ℕ} (i : Fin (n + 1) → U.ι) (T : Thick (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥))), capT (fun α => St (TF l s) {U.U α}) i T → InU (capO U.U i) T := by
    intro n i T h
    rw [capT_eq] at h
    obtain ⟨-, V, hV, hT⟩ := h
    rwa [Set.mem_singleton_iff.1 hV] at hT
  have hle : ∀ {n : ℕ} (i : Fin (n + 1) → U.ι) (a : Fin (n + 1)),
      capT (fun α => St (γ := dividedPowersBot O) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (TF l s) {U.U α}) i ≤ St (TF l s) {U.U (i a)} := fun i a T h => h a
  have hpair : ∀ α β, IsAffineOpen (U.U α ⊓ U.U β) := by
    intro α β
    have h := U.inter {α, β} ⟨α, by simp⟩
    have e : (⨅ γ ∈ ({α, β} : Finset U.ι), U.U γ) = U.U α ⊓ U.U β := by
      rw [Finset.iInf_insert, Finset.iInf_singleton]
    rwa [e] at h
  have hl2 : ∀ {V W : X.Opens} (h : V ≤ W), St (γ := dividedPowersBot O) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (TF l s) {V} ≤ St (TF l s) {W} := by
    rintro V W h T ⟨hq, V', hV, hT⟩
    rw [Set.mem_singleton_iff.1 hV] at hT
    exact ⟨hq, W, rfl, inU_mono h hT⟩
  have hq2 : ∀ {V : X.Opens} (T), St (γ := dividedPowersBot O) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (TF l s) {V} T → InU V T := by
    rintro V T ⟨hq, V', hV, hT⟩
    rwa [Set.mem_singleton_iff.1 hV] at hT
  have hg0 := fun α β (k' : Idx r (U.d β)) => (hω α (U.U α ⊓ U.U β) (hpair α β) inf_le_left _ rfl (hl2 inf_le_left) (isF _) hq2
    ((resU _ (hl2 inf_le_right)).pull r (ω β k'))).exists
  choose g' hg' using hg0
  refine GlobalTheory.T.cover_cup_action_basis (fun W => strV q W) _ U.U _ r (fun α => Idx r (U.d α))
    (fun i => fHom (isF _) (hT i) r) (fun i a k => (resU _ (hle i a)).pull r (ω (i a) k)) (fun α β k k' => g' α β k' k)
    ?_ ?_ ?_ ?_ ?_
  · intro n i a h
    exact hω (i a) (capO U.U i) (capO_affine U n i) (capO_le U.U i a) _ (capT_eq _ _ i) (hle i a) (isF _) (hT i) h
  · intro n i c h
    exact fAct_str (isF _) (hT i) r c h
  · intro n i j f h
    exact res_fAct (isF _) (hT _) r (isF _) (hT i) (capO_comp U.U i j.succAbove) _ f h
  · intro n i j a k
    exact res_res _ _ _ r _
  · intro n i a a' k'
    have hle2 : capT (fun α => St (γ := dividedPowersBot O) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (TF l s) {U.U α}) i ≤ St (TF l s) {U.U (i a) ⊓ U.U (i a')} := by
      intro T h
      exact ⟨(h a).1, _, rfl, le_preimage_inf (pt T) (hq2 T (hle i a T h)) (hq2 T (hle i a' T h))⟩
    have h1 := congrArg ((resU _ hle2).pull r) (hg' (i a) (i a') k')
    rw [res_res, map_sum] at h1
    refine h1.trans (Finset.sum_congr rfl fun k _ => ?_)
    refine (res_fAct (isF _) hq2 r (isF _) (hT i) (le_inf (capO_le U.U i a) (capO_le U.U i a')) hle2 _ _).trans ?_
    change fAct _ _ r _ _ = fAct _ _ r _ _
    rw [res_res]

theorem main_nl (hLoc : KH.LocGr) (hPoly : KH.PolyTf) {O : Type} [CommRing O] [IsNoetherianRing O] (l s : ℕ) (hb : TFBase (dividedPowersBot O) l s) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) [IsProper q] (U : Cov q) (r : ℕ) (hr : r < s) (p : ℕ) :
    Module.Finite O ((CrystallineSemistableComparison.Pb.cechH (grF (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥)) r)
      (fun α => St (TF l s) {U.U α}) r).cx.H p) := by
  obtain ⟨V⟩ := vb_cech hLoc hPoly l s hb q U r hr
  exact GlobalTheory.T.affine_cover_cohomology_finite q U.U U.cover (capO_affine U) _ V p

set_option maxHeartbeats 1000000 in

theorem main_thm : KH.LocGr → KH.PolyTf → KH.GlobSerreSt → KH.GlobVanSt → ∀ {O : Type} [CommRing O] [IsNoetherianRing O] (l s : ℕ) (hb : TFBase (dividedPowersBot O) l s) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) [IsProper q] (U : Cov q) (r : ℕ) (hr : r < s) (p : ℕ),
    Module.Finite O ((CrystallineSemistableComparison.Pb.cechH (Pb.sq (thFil (smFun X q) r) (thFil (smFun X q) ((r : ℤ) + 1)))
      (fun α => St (γ := dividedPowersBot O) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (TF l s) {U.U α}) r).cx.H p) := by
  intro hLoc hPoly _ _ O _ _ l s hb X q _ U r hr p
  exact main_nl hLoc hPoly l s hb q U r hr p

end GlobalTheory.CompanionTheory.GrCech
