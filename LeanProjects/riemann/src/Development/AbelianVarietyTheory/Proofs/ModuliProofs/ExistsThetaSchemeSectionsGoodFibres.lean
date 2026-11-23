import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ProjectiveRepresentationPullbackCoordinates
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLocalMultiplicationPullbackThetaEmbeddingI
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SecCoordBcScaleUnique
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SpMapCompRingHomComp
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFlatProjectiveThroughPointsGoodFibresStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothAndGeomConnectedOfVeryDense
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaEmbeddingSectionsBaseChangeAffineStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionSectionCoordsThetaTimesRootsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLocalMultiplicationPullbackThetaEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EmbeddedAbelianVarietyCutOutByTorsionFormsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaCosetNonvanishingOfHasThStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM.FamilyScheme

theorem spMap_id (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 (Sp R) := Spec.map_id _

theorem exists_retraction {K R' : Type} [Field K] [CommRing R'] (φ : K →+* R') (hφ : IsOpenImmersion (spMap φ))
    (p : Sp K) (hp : p ∈ Set.range (spMap φ)) : ∃ ψ : R' →+* K, ψ.comp φ = RingHom.id K := by
  haveI : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  haveI : IsIso (spMap φ) := isIso_of_isOpenImmersion_of_opensRange_eq_top _ (by
    rw [eq_top_iff]
    intro q _
    rw [Subsingleton.elim q p]
    exact hp)
  refine ⟨(Spec.preimage (inv (spMap φ))).hom, ?_⟩
  have h : spMap ((Spec.preimage (inv (spMap φ))).hom.comp φ) = spMap (RingHom.id K) := by
    rw [spMap_id, spMap_comp]
    have : spMap (Spec.preimage (inv (spMap φ))).hom = inv (spMap φ) := Spec.map_preimage _
    rw [this, IsIso.inv_hom_id]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem secCoord_of_local {X : Scheme.{0}} {M : LB X} (hM : M.IsLB) {I : Type} {th : I → M.Sec} {K R' : Type} [Field K]
    [CommRing R'] {y : Sp K ⟶ X} {v : I → K} (φ : K →+* R') (hφ : IsOpenImmersion (spMap φ)) (p : Sp K)
    (hp : p ∈ Set.range (spMap φ)) (h : SecCoord M th (spMap φ ≫ y) (fun i => φ (v i))) : SecCoord M th y v := by
  obtain ⟨ψ, hψ⟩ := exists_retraction φ hφ p hp
  have h1 := (Coord.secCoord_bc_scale_unique X M I th R' _ _ hM h).1 K ψ
  rw [← Category.assoc, ← spMap_comp, hψ, spMap_id, Category.id_comp] at h1
  have e : (fun i => ψ (φ (v i))) = v := funext fun i => RingHom.congr_fun hψ (v i)
  rwa [e] at h1

theorem projRep_congr {R σ : Type} [CommRing R] {I : Ideal (MvPolynomial σ R)} {Z : Scheme.{0}} {s : Z ⟶ Sp R}
    {M M' : LB Z} {th : σ → M.Sec} {th' : σ → M'.Sec} (hM' : M'.IsLB) (h : ProjRep I s M th)
    (e : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ Z) (w : σ → T), SecCoord M' th' y w ↔ SecCoord M th y w) :
    ProjRep I s M' th' := by
  refine ⟨hM', fun T _ β x v hx hv => h.2.1 T β x v hx ((e T x v).1 hv), fun T _ β v hu hF => ?_⟩
  simp only [e]
  exact h.2.2 T β v hu hF

theorem exists_emb (l1 : Out.Laws) (l2 : Out.Laws2) {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)}
    {K : Type} [Field K] {s : Sp K ⟶ Sp o} (t : TObj g (N' ^ 2) J b s) (m : ℕ) (v : Ix g (N' ^ 2) → K)
    (hm : m ^ 2 ∣ N') (h2 : 2 ≤ m) (hth : t.HasTh (𝟙 _) v) :
    ∃ σ, t.Emb m (Over.mk (𝟙 _)) σ ∧
      ProjRep (idealOf (fst (Over.mk (𝟙 (Sp K))) t.A).left _ σ (𝟙 _)) (fst (Over.mk (𝟙 (Sp K))) t.A).left _ σ := by
  obtain ⟨R', _, φ, σ, hφ, hp, hE, hP⟩ := GlobalTheory.T.exists_local_multiplicationPullback_theta_embedding l1 l2 o g N' J b _ s t m K (𝟙 _) v hm h2 hth
    (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K)
  obtain ⟨ψ, hψ⟩ := exists_retraction φ hφ _ hp
  let h : Over.mk (𝟙 (Sp K)) ⟶ Over.mk (spMap φ ≫ 𝟙 (Sp K)) := Over.homMk (spMap ψ) (by
    show spMap ψ ≫ spMap φ ≫ 𝟙 _ = 𝟙 _
    rw [Category.comp_id, ← spMap_comp, hψ, spMap_id])
  obtain ⟨σ', hE', hc⟩ := GlobalTheory.T.thetaEmbeddingSections_baseChange_affine l2 o g N' J b _ s t m _ _ h σ
    (inferInstanceAs (IsAffine (Spec _))) (inferInstanceAs (IsAffine (Spec _))) hE
  refine ⟨σ', hE', ?_⟩
  obtain ⟨th', hP', hc'⟩ := RepBC.projRep_baseChange R' K _ ψ _ _ _ _ _ (h ▷ t.A).left _ σ hP
    (EmbedLocal.isPullback_whisker t.A h)
  exact ideals_homogeneous.2.2 K _ _ _ _ _ σ' (projRep_congr (LB.isLB_linComb t.isLB _ _) hP'
    fun T _ y w => (hc T y w).trans (hc' T y w).symm)

section Unit
variable {S : Scheme.{0}} (A : Over S)

def unitInv : A ⟶ Over.mk (𝟙 S) ⊗ A := lift (Over.homMk A.hom (by simp)) (𝟙 A)

theorem unitInv_snd : (unitInv A).left ≫ (snd (Over.mk (𝟙 S)) A).left = 𝟙 _ := by
  rw [← Over.comp_left, unitInv, lift_snd]; rfl

theorem to_base_ext {T : Over S} (f f' : T ⟶ Over.mk (𝟙 S)) : f = f' :=
  Over.mkIdTerminal.hom_ext f f'

theorem snd_unitInv : (snd (Over.mk (𝟙 S)) A).left ≫ (unitInv A).left = 𝟙 _ := by
  rw [← Over.comp_left]
  have : snd (Over.mk (𝟙 S)) A ≫ unitInv A = 𝟙 _ :=
    CartesianMonoidalCategory.hom_ext _ _ (to_base_ext _ _) (by simp [unitInv])
  rw [this]; rfl

theorem unitInv_fst : (unitInv A).left ≫ (fst (Over.mk (𝟙 S)) A).left = A.hom := by
  rw [← Over.comp_left, unitInv, lift_fst]; rfl

theorem pt_unitInv (z : Over.mk (𝟙 S) ⟶ A) : z.left ≫ (unitInv A).left = (lift (𝟙 (Over.mk (𝟙 S))) z).left := by
  rw [← Over.comp_left]
  congr 1
  exact CartesianMonoidalCategory.hom_ext _ _ (to_base_ext _ _) (by simp [unitInv])

theorem isPullback_unitInv : IsPullback (unitInv A).left A.hom (fst (Over.mk (𝟙 S)) A).left (𝟙 S) := by
  haveI : IsIso (unitInv A).left := ⟨_, unitInv_snd A, snd_unitInv A⟩
  exact IsPullback.of_horiz_isIso ⟨by rw [unitInv_fst, Category.comp_id]⟩

def chartPullUnit (L : LB A.left) (k : ℕ) (a : ℤ) (ha : a = k) :
    ChartPull (lbPow L k) (Out.LPow A L a (Over.mk (𝟙 S))) (unitInv A).left :=
  have le : ∀ j : PUnit → L.ι, LB.wchart L (fun _ : PUnit => 𝟙 A.left) j ≤ (unitInv A).left ⁻¹ᵁ
      LB.wchart L (fun _ : Fin 1 => (snd (Over.mk (𝟙 S)) A).left) (fun _ => j PUnit.unit) :=
    fun j y hy => Set.mem_iInter.2 fun _ => by
      have h1 : y ∈ L.U (j PUnit.unit) := Set.mem_iInter.1 hy PUnit.unit
      show ((unitInv A).left ≫ (snd (Over.mk (𝟙 S)) A).left) y ∈ L.U (j PUnit.unit)
      rw [unitInv_snd]; exact h1
  { idx := fun j _ => j PUnit.unit
    le := le
    g := fun y j j' hj hj' => by
      refine (gm_linComb L (fun _ : PUnit => 𝟙 A.left) (fun _ => (k : ℤ)) (𝟙 _) y j j' hj hj').trans
        (Eq.trans ?_ (gm_linComb L (fun _ : Fin 1 => (snd (Over.mk (𝟙 S)) A).left) (fun _ => a) (unitInv A).left y _ _
          (le j hj) (le j' hj')).symm)
      rw [Fintype.prod_unique, Fintype.prod_unique, unitInv_snd, Category.comp_id, ha] }

end Unit

theorem prop_pullback_snd (P : MorphismProperty Scheme.{0}) [P.IsStableUnderBaseChange] {X Z S S' : Scheme.{0}}
    {φ : X ⟶ Z} {a : X ⟶ S'} {s : Z ⟶ S} {x : S' ⟶ S} (h : IsPullback φ a s x) (ha : P a) : P (pullback.snd s x) :=
  P.of_isPullback (IsPullback.of_horiz_isIso (fst := h.isoPullback.inv) (snd := pullback.snd s x) (f := a) (g := 𝟙 S')
    ⟨by rw [h.isoPullback_inv_snd, Category.comp_id]⟩) ha

theorem exists_section {R σ : Type} [CommRing R] [IsReduced R] {I : Ideal (MvPolynomial σ R)} {Z : Over (Sp R)}
    {M : LB Z.left} {th : σ → M.Sec} (hP : ProjRep I Z.hom M th) (p : σ → R) {P : Set (Ideal R)} (hvd : VeryDense P)
    (h : ∀ q ∈ P, ∃ (K : Type) (_ : Field K) (x : R →+* K) (y : Sp K ⟶ Z.left), RingHom.ker x = q ∧
      y ≫ Z.hom = spMap x ∧ SecCoord M th y (fun a => x (p a))) :
    ∃ sc : Out.baseOver (Sp R) ⟶ Z, SecCoord M th sc.left p := by
  have hu : Ideal.span (Set.range p) = ⊤ := by
    by_contra hne
    obtain ⟨q, hq, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨q', hq', hpr, hqq, -⟩ := hvd q 1 hq.isPrime ((Ideal.ne_top_iff_one q).1 hq.ne_top)
    obtain ⟨K, _, x, y, hx, hy, hc⟩ := h q' hq'
    have h1 := (hP.2.1 K x y _ hy hc).1
    have h2 : Ideal.span (Set.range fun a => x (p a)) ≤ ⊥ := by
      rw [Ideal.span_le]
      rintro _ ⟨a, rfl⟩
      have h3 : p a ∈ RingHom.ker x := by
        rw [hx]
        exact hqq (hle (Ideal.subset_span ⟨a, rfl⟩))
      exact h3
    rw [h1] at h2
    exact absurd (top_le_iff.1 h2) bot_ne_top
  have hF : ∀ F ∈ I, MvPolynomial.eval₂ (RingHom.id R) p F = 0 := by
    intro F hF
    apply IsNilpotent.eq_zero
    rw [nilpotent_iff_mem_prime]
    intro q hq
    by_contra hn
    obtain ⟨q', hq', hpr, hqq, hf⟩ := hvd q _ hq hn
    obtain ⟨K, _, x, y, hx, hy, hc⟩ := h q' hq'
    have h1 := (hP.2.1 K x y _ hy hc).2 F hF
    apply hf
    rw [← hx, RingHom.mem_ker, MvPolynomial.eval₂_comp_left, RingHom.comp_id]
    exact h1
  obtain ⟨y, ⟨hy, hc⟩, -⟩ := hP.2.2 R (RingHom.id R) p hu hF
  exact ⟨Over.homMk y (hy.trans (spMap_id R)), hc⟩

theorem pt_unique {R σ : Type} [CommRing R] {I : Ideal (MvPolynomial σ R)} {Z : Scheme.{0}} {s : Z ⟶ Sp R}
    {M : LB Z} {th : σ → M.Sec} (hP : ProjRep I s M th) {T : Type} [CommRing T] {β : R →+* T} {y y' : Sp T ⟶ Z}
    {w : σ → T} (hy : y ≫ s = spMap β) (hy' : y' ≫ s = spMap β) (hc : SecCoord M th y w) (hc' : SecCoord M th y' w) :
    y = y' := by
  obtain ⟨h1, h2⟩ := hP.2.1 T β y w hy hc
  exact (hP.2.2 T β w h1 h2).unique ⟨hy, hc⟩ ⟨hy', hc'⟩

theorem span_theta (l1 : Out.Laws) (l2 : Out.Laws2) {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)}
    {K : Type} [Field K] {s : Sp K ⟶ Sp o} (t : TObj g (N' ^ 2) J b s) (n : ℕ) (v : Ix g (N' ^ 2) → K)
    (h2 : 2 ≤ n) (hn : n ∣ N') (hth : t.HasTh (𝟙 _) v) : Ideal.span (Set.range v) = ⊤ := by
  obtain ⟨c, hc⟩ := GlobalTheory.T.thetaCosetNonvanishing_of_hasTh l1 l2 o g N' J b _ s t n K (𝟙 _) v ⊥ h2 hn hth Ideal.isPrime_bot 0
  exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨_, rfl⟩) (Ne.isUnit fun h => hc (Ideal.mem_bot.2 h))

theorem fibre_of_unit {R K σ : Type} [CommRing R] [CommRing K] {x : R →+* K} {Z : Scheme.{0}} {s : Z ⟶ Sp R} {M : LB Z}
    {th : σ → M.Sec} (A : Over (Sp K)) (L : LB A.left) (k : ℕ) (a : ℤ) (ha : a = k)
    (th' : σ → (Out.LPow A L a (Over.mk (𝟙 (Sp K)))).Sec) (φ₀ : (Over.mk (𝟙 (Sp K)) ⊗ A).left ⟶ Z)
    (h1 : IsPullback φ₀ (fst (Over.mk (𝟙 (Sp K))) A).left s (spMap x))
    (h2 : LBIso (Out.LPow A L a (Over.mk (𝟙 (Sp K)))) (M.pull φ₀))
    (h3 : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ A).left) (w : σ → T),
      SecCoord _ th' y w ↔ SecCoord M th (y ≫ φ₀) w) :
    ∃ φ : A.left ⟶ Z, IsPullback φ A.hom s (spMap x) ∧
      (∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ A).left) (w : σ → T),
        SecCoord _ th' y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) A).left ≫ φ) w) ∧
      LBIso (lbPow L k) (M.pull φ) ∧
      ∀ (z : Over.mk (𝟙 (Sp K)) ⟶ A) (w : σ → K), SecCoord _ th' (lift (𝟙 (Over.mk (𝟙 (Sp K)))) z).left w →
        SecCoord M th (z.left ≫ φ) w := by
  refine ⟨(unitInv A).left ≫ φ₀, ?_, fun T _ y w => ?_, ?_, fun z w hz => ?_⟩
  · have := (isPullback_unitInv A).paste_horiz h1
    rwa [Category.id_comp] at this
  · have e : (snd (Over.mk (𝟙 (Sp K))) A).left ≫ (unitInv A).left ≫ φ₀ = φ₀ := by
      rw [← Category.assoc, snd_unitInv, Category.id_comp]
    rw [e]
    exact h3 T y w
  · exact LBIso.chartPull (chartPullUnit A L k a ha) (chartPullSame M _ _ _ (unitInv A).left fun _ => rfl) h2
  · have e : z.left ≫ (unitInv A).left ≫ φ₀ = (lift (𝟙 (Over.mk (𝟙 (Sp K)))) z).left ≫ φ₀ := by
      rw [← Category.assoc, pt_unitInv]
    rw [e]
    exact (h3 K _ w).1 hz

theorem exists_scheme_sections_fibres : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R), VeryDense (objPrimes b Mat κ β v) → ∃ (Z : Over (Sp R)) (I : Ideal (MvPolynomial (Ix g ((n ^ j) ^ 2)) R)) (M : LB Z.left) (th : Ix g ((n ^ j) ^ 2) → M.Sec) (sc : Ix g ((n ^ j) ^ 2) → (Out.baseOver (Sp R) ⟶ Z)) (p : Ix g ((n ^ j) ^ 2) → Ix g ((n ^ j) ^ 2) → R), (ProjRep I Z.hom M th ∧ SmoothOfRelativeDimension g Z.hom ∧ GeometricallyConnected Z.hom ∧ (∀ h, SecCoord M th (sc h).left (p h))) ∧ (∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)), t'.Shape Mat κ → t'.HasTh (𝟙 _) (fun a => x (v a)) → ∃ φ : t'.A.left ⟶ Z.left, (IsPullback φ t'.A.hom Z.hom (spMap x) ∧ (∃ σ, t'.Emb (n ^ 2) (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t'.A).left) (w : Ix g ((n ^ j) ^ 2) → T), SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t'.A).left ≫ φ) w) ∧ LBIso (lbPow t'.L ((n ^ 2) ^ 2)) (M.pull φ) ∧ ∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left)) := by
  intro l1 l2 g J _ Mat κ n hn hodd
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.T.embeddedAbelianVariety_cutOut_by_torsionForms l1 l2 g J Mat κ n hn hodd
  refine ⟨max j₀ 4, fun j hj o _ b R _ _ _ β v hvd => ?_⟩
  have hj4 : 4 ≤ j := le_of_max_le_right hj
  have hdiv : (n ^ 2) ^ 2 ∣ n ^ j := by rw [← pow_mul]; exact pow_dvd_pow n hj4
  have hnd : n ∣ n ^ j := dvd_pow_self n (by omega)
  have h2 : 2 ≤ n ^ 2 := hn.two_le.trans (Nat.le_self_pow two_ne_zero n)
  haveI : NeZero ((n ^ j) ^ 2) := ⟨pow_ne_zero 2 (pow_ne_zero j hn.ne_zero)⟩
  obtain ⟨Hh, _, hh, Q, d, hcut⟩ := hj₀ j (le_of_max_le_left hj) o b
  obtain ⟨e, idx, hco⟩ := GlobalTheory.T.torsion_sectionCoords_theta_times_roots l1 l2 g (n ^ 2) (n ^ j) hodd.pow hdiv
  obtain ⟨p, hp⟩ : ∃ p : Ix g ((n ^ j) ^ 2) → Ix g ((n ^ j) ^ 2) → R,
      ∀ h a, p h a = β (b.ζ ^ e a h : oˣ) * v (idx a h) := ⟨_, fun _ _ => rfl⟩
  have hcut' : ∀ (K : Type) [Field K] [IsAlgClosed K] (β' : o →+* K) (s : Sp K ⟶ Sp o), s = spMap β' →
      ∀ (t : TObj g ((n ^ j) ^ 2) J b s) σ (p : Hh → Ix g ((n ^ j) ^ 2) → K), t.Emb (n ^ 2) (Over.mk (𝟙 _)) σ →
      (∀ h, SecCoord _ σ (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab (hh h) ^ n ^ j)).left (p h)) →
      CutBy (idealOf (fst (Over.mk (𝟙 (Sp K))) t.A).left _ σ (𝟙 _)) Q d p := by
    intro K _ _ β' s hs
    subst hs
    exact hcut K β'
  have fib : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)),
      t'.HasTh (𝟙 _) (fun a => x (v a)) → ∃ σ, t'.Emb (n ^ 2) (Over.mk (𝟙 _)) σ ∧
      ProjRep (idealOf (fst (Over.mk (𝟙 (Sp K))) t'.A).left _ σ (𝟙 _)) (fst (Over.mk (𝟙 (Sp K))) t'.A).left _ σ ∧
      (∀ h, SecCoord _ σ (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t'.lab h ^ n ^ j)).left (fun a => x (p h a))) ∧
      CutBy (idealOf (fst (Over.mk (𝟙 (Sp K))) t'.A).left _ σ (𝟙 _)) Q d (fun h i => x (p (hh h) i)) := by
    intro K _ _ x t' hth
    obtain ⟨σ, hE, hP⟩ := exists_emb l1 l2 t' (n ^ 2) _ hdiv h2 hth
    have hc : ∀ h, SecCoord _ σ (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t'.lab h ^ n ^ j)).left (fun a => x (p h a)) := by
      intro h
      obtain ⟨R', _, φ, hφ, hpt, hs⟩ := hco o J b (Sp K) _ t' K (x.comp β) (𝟙 _) (fun a => x (v a)) σ
        (by rw [Category.id_comp, spMap_comp]) hth (span_theta l1 l2 t' n _ hn.two_le hnd hth) hE h
        (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t'.lab h ^ n ^ j)).left
        (congrArg (fun z => (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (z ^ n ^ j)).left)
          ((Category.id_comp (t'.lab h)).symm.trans (congrArg (· ≫ t'.lab h) (to_base_ext _ _))))
        (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K)
      refine secCoord_of_local hP.1 φ hφ _ hpt ?_
      simp only [hp, map_mul x]
      exact hs
    exact ⟨σ, hE, hP, hc, hcut' K (x.comp β) _ (spMap_comp β x).symm t' σ _ hE fun h => hc (hh h)⟩
  obtain ⟨Z, M, th, hZ, hproj, hflat, -, hφ⟩ := GlobalTheory.T.exists_flat_projective_through_points_goodFibres R _ Hh (fun h => p (hh h)) Q d
    (fun K _ x I => (∀ F ∈ I, ∀ e, MvPolynomial.homogeneousComponent e F ∈ I) ∧ CutBy I Q d (fun h i => x (p (hh h) i)))
    (fun _ _ _ _ h => h) (by
      intro q f hq hf
      obtain ⟨q', ⟨K, _, _, x, t', hx, -, hth⟩, h⟩ := hvd q f hq hf
      obtain ⟨σ, -, hP, -, hc⟩ := fib K x t' hth
      exact ⟨q', ⟨K, inferInstance, x, _, hx, ideals_homogeneous.1 K _ _ _ _ _ σ _ hP.1, hc⟩, h⟩)
  have key : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)),
      t'.HasTh (𝟙 _) (fun a => x (v a)) → ∃ φ : t'.A.left ⟶ Z.left, IsPullback φ t'.A.hom Z.hom (spMap x) ∧
      (∃ σ, t'.Emb (n ^ 2) (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T]
        (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t'.A).left) (w : Ix g ((n ^ j) ^ 2) → T),
        SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t'.A).left ≫ φ) w) ∧
      LBIso (lbPow t'.L ((n ^ 2) ^ 2)) (M.pull φ) ∧
      ∀ h, ((t'.lab h ^ n ^ j).left ≫ φ) ≫ Z.hom = spMap x ∧
        SecCoord M th ((t'.lab h ^ n ^ j).left ≫ φ) (fun a => x (p h a)) := by
    intro K _ _ x t' hth
    obtain ⟨σ, hE, hP, hs, hc⟩ := fib K x t' hth
    obtain ⟨φ₀, a1, a2, a3⟩ := hφ K x _ _ _ _ σ ⟨ideals_homogeneous.1 K _ _ _ _ _ σ _ hP.1, hc⟩ hP
    obtain ⟨φ, b1, b2, b3, b4⟩ := fibre_of_unit t'.A t'.L ((n ^ 2) ^ 2) _ (Nat.cast_pow (n ^ 2) 2).symm σ φ₀ a1 a2 a3
    refine ⟨φ, b1, ⟨σ, hE, b2⟩, b3, fun h => ⟨?_, b4 _ _ (hs h)⟩⟩
    rw [Category.assoc, b1.w, ← Category.assoc, Over.w]
    exact Category.id_comp _
  have hsm := GlobalTheory.smooth_and_geomConnected_of_veryDense R Z.left Z.hom g _ hvd hproj hflat (by
    rintro q ⟨K, _, _, x, t', hx, -, hth⟩
    obtain ⟨φ, h1, -⟩ := key K x t' hth
    exact ⟨K, inferInstance, x, hx,
      @prop_pullback_snd _ (smoothOfRelativeDimension_isStableUnderBaseChange g) _ _ _ _ _ _ _ _ h1 t'.dim,
      prop_pullback_snd @GeometricallyConnected h1 t'.ab.geomConnected⟩)
  have hsc : ∀ h, ∃ sc : Out.baseOver (Sp R) ⟶ Z, SecCoord M th sc.left (p h) := fun h =>
    exists_section hZ (p h) hvd (by
      rintro q ⟨K, _, _, x, t', hx, -, hth⟩
      obtain ⟨φ, -, -, -, h4⟩ := key K x t' hth
      exact ⟨K, inferInstance, x, _, hx, h4 h⟩)
  choose sc hsc using hsc
  refine ⟨Z, _, M, th, sc, p, ⟨hZ, hsm.1, hsm.2, hsc⟩, fun K _ _ x t' _ hth => ?_⟩
  obtain ⟨φ, h1, h2, h3, h4⟩ := key K x t' hth
  refine ⟨φ, h1, h2, h3, fun h => pt_unique hZ (h4 h).1 ?_ (h4 h).2
    ((Coord.secCoord_bc_scale_unique _ M _ th R _ _ hZ.1 (hsc h)).1 K x)⟩
  rw [Category.assoc, Over.w]
  exact Category.comp_id _

end GlobalTheory.ZM.FamilyScheme
end
