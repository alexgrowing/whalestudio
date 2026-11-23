import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TrivFlagMod
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.FlagMinor
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.PluckerCoord
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SameGenericSymm
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.OfSteps
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpVerticalFibre
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericProjClosureDim
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericProjClosureDivisor
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericDimGe
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFiniteBirationalLength
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleFiniteSupport
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.ContractRelevant
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PSemilocalFiniteRank
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ProjectionFormulaDegree
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XSDivcyclehomloc
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace PositivityTheory.Xgn.ModelPushforward

noncomputable section

section Loc

variable {R : Type} [CommRing R] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {L : Type} [Field L]

structure Rep (φ : MRing ι R →+* L) (𝒲 : Set (Ideal (MRing ι R))) (z : L) (F G : MRing ι R) :
    Prop where
  hom : ∃ b, IsMultiHomog F b ∧ IsMultiHomog G b
  ne : φ G ≠ 0
  avoid : ∀ W ∈ 𝒲, G ∉ W
  eq : z = φ F / φ G

def loc (φ : MRing ι R →+* L) (𝒲 : Set (Ideal (MRing ι R))) : Subring L :=
  Subring.closure {z | ∃ F G, Rep φ 𝒲 z F G}

variable {φ : MRing ι R →+* L} {𝒲 : Set (Ideal (MRing ι R))}

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem Rep.mem {z : L} {F G : MRing ι R} (h : Rep φ 𝒲 z F G) : z ∈ loc φ 𝒲 :=
  Subring.subset_closure ⟨F, G, h⟩

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem Rep.mul (hp : ∀ W ∈ 𝒲, W.IsPrime) {z z' : L} {F G F' G' : MRing ι R} (h : Rep φ 𝒲 z F G)
    (h' : Rep φ 𝒲 z' F' G') : Rep φ 𝒲 (z * z') (F * F') (G * G') := by
  obtain ⟨b, hF, hG⟩ := h.hom
  obtain ⟨b', hF', hG'⟩ := h'.hom
  refine ⟨⟨b + b', IsWeightedHomogeneous.mul hF hF', IsWeightedHomogeneous.mul hG hG'⟩, ?_, ?_, ?_⟩
  · rw [map_mul]; exact mul_ne_zero h.ne h'.ne
  · intro W hW hm
    exact ((hp W hW).mem_or_mem hm).elim (h.avoid W hW) (h'.avoid W hW)
  · rw [h.eq, h'.eq, map_mul, map_mul, div_mul_div_comm]

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem Rep.add (hp : ∀ W ∈ 𝒲, W.IsPrime) {z z' : L} {F G F' G' : MRing ι R} (h : Rep φ 𝒲 z F G)
    (h' : Rep φ 𝒲 z' F' G') : Rep φ 𝒲 (z + z') (F * G' + G * F') (G * G') := by
  obtain ⟨b, hF, hG⟩ := h.hom
  obtain ⟨b', hF', hG'⟩ := h'.hom
  refine ⟨⟨b + b', IsWeightedHomogeneous.add (IsWeightedHomogeneous.mul hF hG')
    (IsWeightedHomogeneous.mul hG hF'), IsWeightedHomogeneous.mul hG hG'⟩, (h.mul hp h').ne,
    (h.mul hp h').avoid, ?_⟩
  rw [h.eq, h'.eq, map_add, map_mul, map_mul, map_mul, div_add_div _ _ h.ne h'.ne]

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem rep_C (hp : ∀ W ∈ 𝒲, W.IsPrime) (r : R) : Rep φ 𝒲 (φ (C r)) (C r) 1 :=
  ⟨⟨0, isWeightedHomogeneous_C _ _, isWeightedHomogeneous_one _ _⟩, by simp,
    fun W hW => (Ideal.ne_top_iff_one W).mp (hp W hW).ne_top, by simp⟩

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem mem_loc (hp : ∀ W ∈ 𝒲, W.IsPrime) {z : L} : z ∈ loc φ 𝒲 ↔ ∃ F G, Rep φ 𝒲 z F G := by
  refine ⟨fun h => ?_, fun ⟨F, G, h⟩ => h.mem⟩
  induction h using Subring.closure_induction with
  | mem x hx => exact hx
  | zero => exact ⟨C 0, 1, by simpa using rep_C (φ := φ) hp 0⟩
  | one => exact ⟨C 1, 1, by simpa using rep_C (φ := φ) hp 1⟩
  | add x y _ _ hx hy =>
    obtain ⟨F, G, h⟩ := hx
    obtain ⟨F', G', h'⟩ := hy
    exact ⟨_, _, h.add hp h'⟩
  | neg x _ hx =>
    obtain ⟨F, G, h⟩ := hx
    exact ⟨_, _, by simpa using (rep_C (φ := φ) hp (-1)).mul hp h⟩
  | mul x y _ _ hx hy =>
    obtain ⟨F, G, h⟩ := hx
    obtain ⟨F', G', h'⟩ := hy
    exact ⟨_, _, h.mul hp h'⟩

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem loc_anti {𝒲' : Set (Ideal (MRing ι R))} (h : 𝒲 ⊆ 𝒲') : loc φ 𝒲' ≤ loc φ 𝒲 :=
  Subring.closure_mono fun _ ⟨F, G, hr⟩ => ⟨F, G, hr.hom, hr.ne, fun W hW => hr.avoid W (h hW), hr.eq⟩

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem exists_ev (hp : ∀ W ∈ 𝒲, W.IsPrime) {E : Type} [Field E] (ψ : MRing ι R →+* E)
    (h0 : ∀ F b, IsMultiHomog F b → φ F = 0 → ψ F = 0)
    (h1 : ∀ G b, IsMultiHomog G b → φ G ≠ 0 → (∀ W ∈ 𝒲, G ∉ W) → ψ G ≠ 0) :
    ∃ e : loc φ 𝒲 →+* E, ∀ (z : loc φ 𝒲) F G, Rep φ 𝒲 z F G → e z = ψ F / ψ G := by
  have hne : ∀ {z F G}, Rep φ 𝒲 z F G → ψ G ≠ 0 := fun h => by
    obtain ⟨b, -, hG⟩ := h.hom
    exact h1 _ b hG h.ne h.avoid
  have wd : ∀ {z F G F' G'}, Rep φ 𝒲 z F G → Rep φ 𝒲 z F' G' → ψ F / ψ G = ψ F' / ψ G' := by
    intro z F G F' G' h h'
    obtain ⟨b, hF, hG⟩ := h.hom
    obtain ⟨b', hF', hG'⟩ := h'.hom
    have e := h.eq.symm.trans h'.eq
    rw [div_eq_div_iff h.ne h'.ne] at e
    rw [div_eq_div_iff (hne h) (hne h'), ← sub_eq_zero, ← map_mul, ← map_mul, ← map_sub]
    refine h0 _ (b + b') ?_ (by rw [map_sub, map_mul, map_mul, e, sub_self])
    refine (weightedHomogeneousSubmodule R (blockWeight ι) (b + b')).sub_mem
      (IsWeightedHomogeneous.mul hF hG') ?_
    rw [add_comm]
    exact IsWeightedHomogeneous.mul hF' hG
  choose Fz Gz hz using fun z : loc φ 𝒲 => (mem_loc hp).mp z.2
  refine ⟨{ toFun := fun z => ψ (Fz z) / ψ (Gz z), map_one' := ?_, map_mul' := ?_,
            map_zero' := ?_, map_add' := ?_ }, fun z F G h => wd (hz z) h⟩
  · rw [wd (hz 1) (show Rep φ 𝒲 _ (C 1) 1 by simpa using rep_C (φ := φ) hp 1)]; simp
  · intro a b
    rw [wd (hz (a * b)) ((hz a).mul hp (hz b)), map_mul, map_mul, div_mul_div_comm]
  · rw [wd (hz 0) (show Rep φ 𝒲 _ (C 0) 1 by simpa using rep_C (φ := φ) hp 0)]; simp
  · intro a b
    rw [wd (hz (a + b)) ((hz a).add hp (hz b)), map_add, map_mul, map_mul, map_mul,
      div_add_div _ _ (hne (hz a)) (hne (hz b))]

def ffield (φ : MRing ι R →+* L) : Subfield L where
  toSubring := loc φ ∅
  inv_mem' := by
    intro z hz
    obtain ⟨F, G, h⟩ := (mem_loc (by simp)).mp hz
    by_cases hF : φ F = 0
    · have : z = 0 := by rw [h.eq, hF, zero_div]
      rw [this, inv_zero]
      exact (loc φ ∅).zero_mem
    · obtain ⟨b, hb, hb'⟩ := h.hom
      exact Rep.mem (F := G) (G := F) ⟨⟨b, hb', hb⟩, hF, by simp, by rw [h.eq, inv_div]⟩

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem mem_ffield {z : L} : z ∈ ffield φ ↔ ∃ F G, Rep φ ∅ z F G :=
  mem_loc (by simp)

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem div_mem_ffield {F G : MRing ι R} {b : K → ℕ} (hF : IsMultiHomog F b)
    (hG : IsMultiHomog G b) : φ F / φ G ∈ ffield φ := by
  by_cases h : φ G = 0
  · rw [h, div_zero]; exact (ffield φ).zero_mem
  · exact mem_ffield.mpr ⟨F, G, ⟨b, hF, hG⟩, h, by simp, rfl⟩

def dehom (φ : MRing ι R →+* L) (c : ∀ k, ι k) : MRing ι R →+* L :=
  eval₂Hom (φ.comp C) fun v => φ (X v) / φ (X ⟨v.1, c v.1⟩)

theorem dehom_eq {c : ∀ k, ι k} (hc : ∀ k, φ (X ⟨k, c k⟩) ≠ 0) {F : MRing ι R} {b : K → ℕ}
    (hF : IsMultiHomog F b) : dehom φ c F = φ F / φ (powMonomial b c) := by
  let _ : Algebra R L := (φ.comp C).toAlgebra
  have h := GenericProjClosureDivisor.pointConeMap_of_homog
    (fun v : Σ k, ι k => φ (X v) / φ (X ⟨v.1, c v.1⟩)) hF
  have key : (eval fun k => φ (X ⟨k, c k⟩)).comp
      (pointConeMap R (fun v : Σ k, ι k => φ (X v) / φ (X ⟨v.1, c v.1⟩))).toRingHom = φ := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun v => ?_)
    · simp [pointConeMap, MvPolynomial.algebraMap_apply]
      rfl
    · simp [pointConeMap, hc]
  have h2 := congrArg (eval fun k => φ (X ⟨k, c k⟩)) h
  have h3 : (eval fun k => φ (X ⟨k, c k⟩))
      (pointConeMap R (fun v : Σ k, ι k => φ (X v) / φ (X ⟨v.1, c v.1⟩)) F) = φ F :=
    RingHom.congr_fun key F
  have hm : φ (powMonomial b c) ≠ 0 := by
    simp only [powMonomial, map_prod, map_pow]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
  rw [eq_div_iff hm, ← h3, h2]
  simp only [powMonomial, map_prod, map_pow, map_mul, eval_C, eval_X]
  rfl

omit [DecidableEq K] [∀ k, Fintype (ι k)] in
theorem powMonomial_notMem {W : Ideal (MRing ι R)} (hW : W.IsPrime) {c : ∀ k, ι k}
    (hc : ∀ k, (X ⟨k, c k⟩ : MRing ι R) ∉ W) (e : K → ℕ) : (powMonomial e c : MRing ι R) ∉ W :=
  W.primeCompl.prod_mem fun k _ => W.primeCompl.pow_mem (hc k) _

structure Setup (φ : MRing ι R →+* L) (P : Ideal (MRing ι R)) (𝒲 : Set (Ideal (MRing ι R))) :
    Prop where
  mp : IsMultiProjPrime P
  ker : ∀ F b, IsMultiHomog F b → (φ F = 0 ↔ F ∈ P)
  fin : 𝒲.Finite
  mpW : ∀ W ∈ 𝒲, IsMultiProjPrime W
  le : ∀ W ∈ 𝒲, P ≤ W

variable {P : Ideal (MRing ι R)}

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem Setup.prime (S : Setup φ P 𝒲) : ∀ W ∈ 𝒲, W.IsPrime := fun W hW => (S.mpW W hW).isPrime

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem Setup.single (S : Setup φ P 𝒲) {W : Ideal (MRing ι R)} (hW : W ∈ 𝒲) : Setup φ P {W} :=
  ⟨S.mp, S.ker, Set.finite_singleton W, fun _ h => h ▸ S.mpW W hW, fun _ h => h ▸ S.le W hW⟩

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem Setup.ne (S : Setup φ P 𝒲) {W : Ideal (MRing ι R)} (hW : W ∈ 𝒲) {G : MRing ι R}
    {b : K → ℕ} (hG : IsMultiHomog G b) (hGW : G ∉ W) : φ G ≠ 0 :=
  fun h => hGW (S.le W hW ((S.ker G b hG).mp h))

omit [∀ k, Fintype (ι k)] in
theorem Setup.avoid (S : Setup φ P 𝒲) (b : K → ℕ) :
    ∃ (e : K → ℕ) (H : MRing ι R), IsMultiHomog H (b + e) ∧ φ H ≠ 0 ∧ ∀ W ∈ 𝒲, H ∉ W := by
  classical
  obtain ⟨e, H, hH, hle, hav⟩ := exists_form_avoid_primes (insert P S.fin.toFinset) (by
    intro W hW
    rcases Finset.mem_insert.mp hW with rfl | hW
    · exact ⟨S.mp.isPrime, S.mp.multiHomog, S.mp.relevant⟩
    · have := S.mpW W (S.fin.mem_toFinset.mp hW)
      exact ⟨this.isPrime, this.multiHomog, this.relevant⟩) b
  obtain ⟨e', rfl⟩ := exists_add_of_le hle
  exact ⟨e', H, hH, fun h => hav P (Finset.mem_insert_self _ _) ((S.ker H _ hH).mp h),
    fun W hW => hav W (Finset.mem_insert_of_mem (S.fin.mem_toFinset.mpr hW))⟩

omit [∀ k, Fintype (ι k)] in

theorem Setup.clear (S : Setup φ P 𝒲) (b : K → ℕ) {Q : Ideal (MRing ι R)}
    (hQ : IsMultiProjPrime Q) :
    ∃ u H : MRing ι R, u ∉ Q ∧ (∃ e, IsMultiHomog u e) ∧
      ∀ F, IsMultiHomog F b → Rep φ 𝒲 (φ (F * u) / φ H) (F * u) H := by
  obtain ⟨e, H, hH, h0, hav⟩ := S.avoid b
  obtain ⟨i, hi⟩ := powMonomial_not_mem hQ.isPrime hQ.relevant e
  exact ⟨_, H, hi, ⟨e, isMultiHomog_powMonomial e i⟩, fun F hF =>
    ⟨⟨b + e, IsWeightedHomogeneous.mul hF (isMultiHomog_powMonomial e i), hH⟩, h0, hav, rfl⟩⟩

def qm (W : Ideal (MRing ι R)) [W.IsPrime] : MRing ι R →+* FractionRing (MRing ι R ⧸ W) :=
  (algebraMap (MRing ι R ⧸ W) _).comp (Ideal.Quotient.mk W)

omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in
theorem qm_eq_zero (W : Ideal (MRing ι R)) [W.IsPrime] (F : MRing ι R) : qm W F = 0 ↔ F ∈ W := by
  simp only [qm, RingHom.comp_apply, IsFractionRing.to_map_eq_zero_iff,
    Ideal.Quotient.eq_zero_iff_mem]

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem Setup.exists_res (S : Setup φ P 𝒲) {W : Ideal (MRing ι R)} (hW : W ∈ 𝒲) {E : Type}
    [Field E] (ψ : MRing ι R →+* E) (hψ : ∀ F, ψ F = 0 ↔ F ∈ W) :
    ∃ e : loc φ 𝒲 →+* E, ∀ (z : loc φ 𝒲) F G, Rep φ 𝒲 z F G → e z = ψ F / ψ G :=
  exists_ev S.prime ψ (fun F b hF h => (hψ F).mpr (S.le W hW ((S.ker F b hF).mp h)))
    (fun G _ _ _ h h' => h W hW ((hψ G).mp h'))

def IsVan (φ : MRing ι R →+* L) (𝒲 : Set (Ideal (MRing ι R))) (W : Ideal (MRing ι R))
    (𝔪 : Ideal (loc φ 𝒲)) : Prop :=
  ∀ (z : loc φ 𝒲) F G, Rep φ 𝒲 z F G → (z ∈ 𝔪 ↔ F ∈ W)

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem isVan_ker {W : Ideal (MRing ι R)} (hW : W ∈ 𝒲) {E : Type}
    [Field E] {ψ : MRing ι R →+* E} (hψ : ∀ F, ψ F = 0 ↔ F ∈ W) {e : loc φ 𝒲 →+* E}
    (he : ∀ (z : loc φ 𝒲) F G, Rep φ 𝒲 z F G → e z = ψ F / ψ G) :
    IsVan φ 𝒲 W (RingHom.ker e) := by
  intro z F G h
  rw [RingHom.mem_ker, he z F G h, div_eq_zero_iff, hψ, hψ]
  exact ⟨fun h' => h'.resolve_right (h.avoid W hW), Or.inl⟩

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem Setup.exists_van (S : Setup φ P 𝒲) {W : Ideal (MRing ι R)} (hW : W ∈ 𝒲) :
    ∃ 𝔪 : Ideal (loc φ 𝒲), 𝔪.IsPrime ∧ IsVan φ 𝒲 W 𝔪 := by
  have := S.prime W hW
  obtain ⟨e, he⟩ := S.exists_res hW (qm W) (qm_eq_zero W)
  exact ⟨_, RingHom.ker_isPrime e, isVan_ker hW (qm_eq_zero W) he⟩

omit [∀ k, Fintype (ι k)] in
theorem IsVan.le_of_le (S : Setup φ P 𝒲) {W W' : Ideal (MRing ι R)} (hW : W ∈ 𝒲) (hW' : W' ∈ 𝒲)
    {𝔪 𝔪' : Ideal (loc φ 𝒲)} (h : IsVan φ 𝒲 W 𝔪) (h' : IsVan φ 𝒲 W' 𝔪') (hle : 𝔪 ≤ 𝔪') :
    W ≤ W' := by
  intro a ha
  rw [← sum_weightedHomogeneousComponent (blockWeight _) a]
  refine finsum_induction (· ∈ W') W'.zero_mem (fun _ _ => W'.add_mem) (fun c => ?_)
  have hac := (S.mpW W hW).multiHomog a ha c
  obtain ⟨u, H, hu, -, hr⟩ := S.clear c (S.mpW W' hW')
  have hr' := hr _ (weightedHomogeneousComponent_isWeightedHomogeneous (w := blockWeight ι) c a)
  have h1 := (h ⟨_, hr'.mem⟩ _ _ hr').mpr (W.mul_mem_right _ hac)
  exact ((S.prime W' hW').mem_or_mem ((h' ⟨_, hr'.mem⟩ _ _ hr').mp (hle h1))).resolve_right hu

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem Setup.max_eq (S : Setup φ P 𝒲) (hne : 𝒲.Nonempty) (𝔪 : 𝒲 → Ideal (loc φ 𝒲))
    (hp : ∀ W, (𝔪 W).IsPrime) (hv : ∀ W, IsVan φ 𝒲 W.1 (𝔪 W)) (M : Ideal (loc φ 𝒲))
    (hM : M.IsMaximal) : ∃ W, M = 𝔪 W := by
  let _ : Fintype 𝒲 := S.fin.fintype
  have hsub : (M : Set (loc φ 𝒲)) ⊆ ⋃ W ∈ ((Finset.univ : Finset 𝒲) : Set 𝒲), (𝔪 W : Set _) := by
    intro z hz
    by_contra hc
    simp only [Finset.coe_univ, Set.mem_univ, Set.iUnion_true, Set.mem_iUnion, not_exists,
      SetLike.mem_coe] at hc
    obtain ⟨F, G, hr⟩ := (mem_loc S.prime).mp z.2
    obtain ⟨b, hF, hG⟩ := hr.hom
    have hFW : ∀ W ∈ 𝒲, F ∉ W := fun W hW h => hc ⟨W, hW⟩ ((hv ⟨W, hW⟩ z F G hr).mpr h)
    have hF0 := S.ne hne.some_mem hF (hFW _ hne.some_mem)
    have hinv : Rep φ 𝒲 _ G F := ⟨⟨b, hG, hF⟩, hF0, hFW, rfl⟩
    refine hM.ne_top (M.eq_top_of_isUnit_mem hz (IsUnit.of_mul_eq_one ⟨_, hinv.mem⟩ ?_))
    apply Subtype.ext
    change (z : L) * (φ G / φ F) = 1
    rw [hr.eq, div_mul_div_cancel₀ hr.ne, div_self hF0]
  obtain ⟨W, -, hle⟩ := (Ideal.subset_union_prime (f := 𝔪) ⟨hne.some, hne.some_mem⟩
    ⟨hne.some, hne.some_mem⟩ (fun W _ _ _ => hp W)).mp hsub
  exact ⟨W, hM.eq_of_le (hp W).ne_top hle⟩

theorem isLocalization_subring {B D : Subring L} (h : B ≤ D) (𝔪 : Ideal B) [𝔪.IsPrime]
    (h1 : ∀ s : B, s ∉ 𝔪 → ∃ t ∈ D, (s : L) * t = 1)
    (h2 : ∀ z ∈ D, ∃ a s : B, s ∉ 𝔪 ∧ z * (s : L) = a) :
    letI := (Subring.inclusion h).toAlgebra
    IsLocalization.AtPrime D 𝔪 := by
  let _ := (Subring.inclusion h).toAlgebra
  refine (isLocalization_iff _ _).mpr ⟨fun s => ?_, fun z => ?_, fun {x y} hxy => ?_⟩
  · obtain ⟨t, ht, e⟩ := h1 s.1 s.2
    exact IsUnit.of_mul_eq_one ⟨t, ht⟩ (Subtype.ext e)
  · obtain ⟨a, s, hs, e⟩ := h2 z z.2
    exact ⟨(a, ⟨s, hs⟩), Subtype.ext e⟩
  · refine ⟨1, ?_⟩
    have h' := congrArg Subtype.val hxy
    have hxy' : x = y := Subtype.ext h'
    rw [hxy']

omit [∀ k, Fintype (ι k)] in
theorem Setup.isLocalization (S : Setup φ P 𝒲) {W : Ideal (MRing ι R)} (hW : W ∈ 𝒲)
    {𝔪 : Ideal (loc φ 𝒲)} [𝔪.IsPrime] (hv : IsVan φ 𝒲 W 𝔪) :
    letI := (Subring.inclusion (loc_anti (φ := φ) (Set.singleton_subset_iff.mpr hW))).toAlgebra
    IsLocalization.AtPrime (loc φ {W}) 𝔪 := by
  refine isLocalization_subring _ 𝔪 (fun s hs => ?_) (fun z hz => ?_)
  · obtain ⟨F, G, hr⟩ := (mem_loc S.prime).mp s.2
    obtain ⟨b, hF, hG⟩ := hr.hom
    have hFW : F ∉ W := fun h => hs ((hv _ F G hr).mpr h)
    have hF0 := S.ne hW hF hFW
    have hinv : Rep φ {W} _ G F := ⟨⟨b, hG, hF⟩, hF0, fun _ h => h ▸ hFW, rfl⟩
    refine ⟨_, hinv.mem, ?_⟩
    rw [hr.eq, div_mul_div_cancel₀ hr.ne, div_self hF0]
  · obtain ⟨F, G, hr⟩ := (mem_loc (S.single hW).prime).mp hz
    obtain ⟨b, hF, hG⟩ := hr.hom
    obtain ⟨u, H, hu, -, hc⟩ := S.clear b (S.mpW W hW)
    refine ⟨⟨_, (hc F hF).mem⟩, ⟨_, (hc G hG).mem⟩, fun h => ?_, ?_⟩
    · exact ((S.prime W hW).mem_or_mem ((hv ⟨_, (hc G hG).mem⟩ _ _ (hc G hG)).mp h)).elim
        (hr.avoid W rfl) hu
    · change z * (φ (G * u) / φ H) = φ (F * u) / φ H
      rw [hr.eq, map_mul, map_mul, ← mul_div_assoc, ← mul_assoc, div_mul_cancel₀ _ hr.ne]

end Loc

section Abstract

theorem finite_of_local {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.IsIntegral A B] (T : Set B) (hT : T.Finite)
    (h : ∀ M : Ideal B, M.IsMaximal → ∀ b : B,
      ∃ c ∈ Algebra.adjoin A T, c ∉ M ∧ c * b ∈ Algebra.adjoin A T) :
    Module.Finite A B := by
  have htop : Algebra.adjoin A T = ⊤ := by
    rw [eq_top_iff]
    intro b _
    set D := Algebra.adjoin A T
    let I : Ideal D :=
      { carrier := {c | (c : B) * b ∈ D}
        add_mem' := fun {x y} hx hy => by
          change ((x : B) + y) * b ∈ D
          rw [add_mul]; exact D.add_mem hx hy
        zero_mem' := by
          change (0 : B) * b ∈ D
          rw [zero_mul]; exact D.zero_mem
        smul_mem' := fun c x hx => by
          change ((c : B) * x) * b ∈ D
          rw [mul_assoc]; exact D.mul_mem c.2 hx }
    by_contra hb
    have hI : I ≠ ⊤ := fun h => hb (by
      have h1 : (1 : D) ∈ I := h ▸ Submodule.mem_top
      have h2 : (1 : B) * b ∈ D := h1
      rwa [one_mul] at h2)
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal I hI
    have : Algebra.IsIntegral D B := Algebra.IsIntegral.tower_top A
    obtain ⟨M, hM, hc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := B) m (by
      rw [(RingHom.injective_iff_ker_eq_bot (algebraMap D B)).mp Subtype.val_injective]
      exact bot_le)
    obtain ⟨c, hc1, hc2, hc3⟩ := h M hM b
    have h4 : (⟨c, hc1⟩ : D) ∈ m := hle hc3
    rw [← hc] at h4
    exact hc2 h4
  have : Algebra.FiniteType A B := ⟨⟨hT.toFinset, by simpa using htop⟩⟩
  exact Algebra.IsIntegral.finite

theorem finrank_eq_relfinrank {A B L : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Algebra A B] [Field L] (ρ : B →+* L) (hρ : Function.Injective ρ)
    (hinj : Function.Injective (algebraMap A B)) {K₀ E : Subfield L} (hKE : K₀ ≤ E)
    (hA : ∀ a, ρ (algebraMap A B a) ∈ K₀) (hB : ∀ b, ρ b ∈ E)
    (fracA : ∀ x ∈ K₀, ∃ a a', x = ρ (algebraMap A B a) / ρ (algebraMap A B a'))
    (fracB : ∀ x ∈ E, ∃ b b', x = ρ b / ρ b') :
    Module.finrank A B = K₀.relfinrank E := by
  rw [Subfield.relfinrank_eq_finrank_of_le hKE]
  set Lf := Subfield.extendScalars hKE
  let _ : Algebra A K₀ := ((ρ.comp (algebraMap A B)).codRestrict K₀ hA).toAlgebra
  let _ : Algebra B Lf := (ρ.codRestrict Lf (fun b => hB b)).toAlgebra
  let _ : Algebra A Lf := ((algebraMap B Lf).comp (algebraMap A B)).toAlgebra
  have _ : IsScalarTower A B Lf := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have _ : IsScalarTower A K₀ Lf := IsScalarTower.of_algebraMap_eq (fun a => Subtype.ext rfl)
  have _ : IsFractionRing A K₀ := by
    refine GroundTheory.Heights₂.Heights.FieldNumbers.isFractionRing_of_div
      (fun a b h => hinj (hρ (congrArg Subtype.val h :))) ?_
    rintro ⟨x, hx⟩
    obtain ⟨a, a', rfl⟩ := fracA x hx
    exact ⟨a, a', Subtype.ext rfl⟩
  have _ : IsFractionRing B Lf := by
    refine GroundTheory.Heights₂.Heights.FieldNumbers.isFractionRing_of_div
      (fun a b h => hρ (congrArg Subtype.val h :)) ?_
    rintro ⟨x, hx⟩
    obtain ⟨a, a', rfl⟩ := fracB x hx
    exact ⟨a, a', Subtype.ext rfl⟩
  exact (IsFractionRing.finrank_eq A K₀ B Lf).symm

theorem ord_ringEquiv {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B) (a : A) :
    Ring.ord B (e a) = Ring.ord A a := by
  let _ : Algebra A B := e.toRingHom.toAlgebra
  let f : A ≃ₐ[A] B := AlgEquiv.ofRingEquiv (f := e) (fun _ => rfl)
  unfold Ring.ord
  rw [← Module.length_eq_of_surjective (R := B) (S := A) (M := B ⧸ Ideal.span {e a}) e.surjective]
  exact (Ideal.quotientEquivAlg (Ideal.span {a}) (Ideal.span {e a}) f (by
    rw [Ideal.map_span, Set.image_singleton]; rfl)).toLinearEquiv.length_eq.symm

variable {L : Type} [Field L]

abbrev inclAlg {A B : Subring L} (h : A ≤ B) : Algebra A B := (Subring.inclusion h).toAlgebra

theorem isIntegral_of_valuation {A B : Subring L} (h : A ≤ B)
    (hV : ∀ V : ValuationSubring L, A ≤ V.toSubring → B ≤ V.toSubring) :
    letI := inclAlg h
    Algebra.IsIntegral A B := by
  let _ := inclAlg h
  have : IsScalarTower A B L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  refine ⟨fun b => ?_⟩
  have hmem : (b : L) ∈ ⨅ V : {V : ValuationSubring L // (A : Set L) ⊆ V.toSubring},
      V.1.toSubring := by
    rw [Subring.mem_iInf]
    rintro ⟨V, hV'⟩
    exact hV V hV' b.2
  rw [iInf_valuationSubring_superset, Subring.closure_eq] at hmem
  exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom A B L) Subtype.val_injective).mp hmem

theorem not_isField_of_integral {A B : Subring L} (h : A ≤ B) (hdim : ringKrullDim A = 1)
    (hint : letI := inclAlg h; Algebra.IsIntegral A B) : ¬ ∀ b ∈ B, b⁻¹ ∈ B := by
  intro hB
  let _ := inclAlg h
  have hf : IsField B := ⟨⟨0, 1, zero_ne_one⟩, mul_comm, fun {a} ha =>
    ⟨⟨_, hB a a.2⟩, Subtype.ext (mul_inv_cancel₀ fun h0 => ha (Subtype.ext h0))⟩⟩
  have hA : IsField A := isField_of_isIntegral_of_isField (Subring.inclusion_injective h) hf
  rw [ringKrullDim_eq_zero_of_isField hA] at hdim
  exact absurd hdim (by decide)

theorem finite_subring {A B : Subring L} (h : A ≤ B)
    (hint : letI := inclAlg h; Algebra.IsIntegral A B) (T : Set L) (hT : T.Finite) (hTB : T ⊆ B)
    (hl : ∀ M : Ideal B, M.IsMaximal → ∀ b : B, ∃ c : B, (c : L) ∈ Subring.closure ((A : Set L) ∪ T) ∧
      c ∉ M ∧ (c : L) * b ∈ Subring.closure ((A : Set L) ∪ T)) :
    letI := inclAlg h
    Module.Finite A B := by
  let _ := inclAlg h
  have key : ∀ x ∈ Subring.closure ((A : Set L) ∪ T), ∃ c : B, (c : L) = x ∧
      c ∈ Algebra.adjoin A ((↑) ⁻¹' T : Set B) := by
    intro x hx
    induction hx using Subring.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · exact ⟨algebraMap A B ⟨x, hx⟩, rfl, Subalgebra.algebraMap_mem _ _⟩
      · exact ⟨⟨x, hTB hx⟩, rfl, Algebra.subset_adjoin hx⟩
    | zero => exact ⟨0, rfl, zero_mem _⟩
    | one => exact ⟨1, rfl, one_mem _⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, rfl, hc⟩ := hx
      obtain ⟨d, rfl, hd⟩ := hy
      exact ⟨c + d, rfl, add_mem hc hd⟩
    | neg x _ hx =>
      obtain ⟨c, rfl, hc⟩ := hx
      exact ⟨-c, rfl, neg_mem hc⟩
    | mul x y _ _ hx hy =>
      obtain ⟨c, rfl, hc⟩ := hx
      obtain ⟨d, rfl, hd⟩ := hy
      exact ⟨c * d, rfl, mul_mem hc hd⟩
  refine finite_of_local ((↑) ⁻¹' T : Set B) (hT.preimage Subtype.val_injective.injOn) ?_
  intro M hM b
  obtain ⟨c, h1, h2, h3⟩ := hl M hM b
  obtain ⟨c', e', hc'⟩ := key _ h1
  obtain ⟨d', f', hd'⟩ := key _ h3
  obtain rfl : c' = c := Subtype.ext e'
  obtain rfl : d' = c' * b := Subtype.ext f'
  exact ⟨c', hc', h2, hd'⟩

theorem rank_subring {A B : Subring L} (h : A ≤ B) {K₀ E : Subfield L} (hKE : K₀ ≤ E)
    (hA : ∀ a ∈ A, a ∈ K₀) (hB : ∀ b ∈ B, b ∈ E)
    (fracA : ∀ x ∈ K₀, ∃ a ∈ A, ∃ a' ∈ A, x = a / a')
    (fracB : ∀ x ∈ E, ∃ b ∈ B, ∃ b' ∈ B, x = b / b') :
    letI := inclAlg h
    Module.finrank A B = K₀.relfinrank E := by
  let _ := inclAlg h
  refine finrank_eq_relfinrank B.subtype Subtype.val_injective (Subring.inclusion_injective h) hKE
    (fun a => hA a a.2) (fun b => hB b b.2) (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨a, ha, a', ha', e⟩ := fracA x hx
    exact ⟨⟨a, ha⟩, ⟨a', ha'⟩, e⟩
  · obtain ⟨a, ha, a', ha', e⟩ := fracB x hx
    exact ⟨⟨a, ha⟩, ⟨a', ha'⟩, e⟩

theorem res_subring {A B : Subring L} (h : A ≤ B) [IsLocalRing A]
    (hfin : letI := inclAlg h; Module.Finite A B) {E : Type} [Field E] (e : B →+* E)
    (hmax : (RingHom.ker e).IsMaximal) {K₀ E₀ : Subfield E} (hKE : K₀ ≤ E₀)
    (hA : ∀ a (ha : a ∈ A), e ⟨a, h ha⟩ ∈ K₀) (hB : ∀ b, e b ∈ E₀)
    (fracA : ∀ x ∈ K₀, ∃ a, ∃ ha : a ∈ A, x = e ⟨a, h ha⟩)
    (fracB : ∀ x ∈ E₀, ∃ b b', x = e b / e b') :
    letI := inclAlg h
    Module.length A (B ⧸ RingHom.ker e) = (K₀.relfinrank E₀ : ℕ∞) := by
  let _ := inclAlg h
  rw [FiniteBirationalLength.length_quot_maximal_eq_inertiaDeg]
  have hm : (RingHom.ker e).under A = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _)
  have : (RingHom.ker e).LiesOver (IsLocalRing.maximalIdeal A) := ⟨hm.symm⟩
  rw [Ideal.inertiaDeg_eq_of_isMaximal (IsLocalRing.maximalIdeal A)]
  congr 1
  refine finrank_eq_relfinrank (RingHom.kerLift e) (RingHom.kerLift_injective e)
    (FaithfulSMul.algebraMap_injective _ _) hKE (fun a => ?_) (fun b => ?_) (fun x hx => ?_)
    (fun x hx => ?_)
  · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact hA a a.2
  · obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact hB b
  · obtain ⟨a, ha, rfl⟩ := fracA x hx
    refine ⟨Ideal.Quotient.mk _ ⟨a, ha⟩, 1, ?_⟩
    rw [map_one, map_one, div_one]
    rfl
  · obtain ⟨b, b', rfl⟩ := fracB x hx
    exact ⟨Ideal.Quotient.mk _ b, Ideal.Quotient.mk _ b', rfl⟩

theorem sum_subring {A B : Subring L} (h : A ≤ B) [IsLocalRing A] [IsNoetherianRing A]
    (hdim : ringKrullDim A = 1) (hfin : letI := inclAlg h; Module.Finite A B) {I : Type} [Fintype I]
    (𝔪 : I → Ideal B) (hmax : ∀ i, (𝔪 i).IsMaximal) (hinj : Function.Injective 𝔪)
    (hsurj : ∀ M : Ideal B, M.IsMaximal → ∃ i, M = 𝔪 i) (D : I → Subring L) (hBD : ∀ i, B ≤ D i)
    (hloc : ∀ i, haveI := (hmax i).isPrime; letI := inclAlg (hBD i)
      IsLocalization.AtPrime (D i) (𝔪 i))
    (n : I → ℕ) (hn : ∀ i, letI := inclAlg h; Module.length A (B ⧸ 𝔪 i) = n i) (δ : ℕ)
    (hδ : letI := inclAlg h; Module.finrank A B = δ) (α : L) (hα : α ∈ A) (h0 : α ≠ 0) :
    ∑ i, Ring.ord (D i) ⟨α, hBD i (h hα)⟩ * (n i : ℕ∞) = (δ : ℕ∞) * Ring.ord A ⟨α, hα⟩ := by
  let _ := inclAlg h
  let _ := fun i => inclAlg (hBD i)
  have : Module.IsTorsionFree A B :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (Subring.inclusion_injective h)
  have h1 := ReciprocityTheory.ChartRestriction.G.AI.dimOneTorsionFreeFormula A B ⟨α, hα⟩ hdim (fun h' => h0 (congrArg Subtype.val h'))
  have h2 := GroundTheory.Heights₂.Heights.FieldNumbers.FiniteAlgebraLengthSum.proof A B I 𝔪 hmax hinj hsurj
    (fun i => D i) hloc ⟨α, hα⟩
  rw [← hδ, ← h1, h2]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hn i]
  rfl

end Abstract

section Pair

variable {R : Type} [CommRing R] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {L : Type} [Field L]
  {φ : MRing ι R →+* L} {𝒲 : Set (Ideal (MRing ι R))} {P : Ideal (MRing ι R)}

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem le_of_forms {I J : Ideal (MRing ι R)} (hI : IsMultiHomogIdeal I)
    (h : ∀ F b, IsMultiHomog F b → F ∈ I → F ∈ J) : I ≤ J := by
  intro a ha
  rw [← sum_weightedHomogeneousComponent (blockWeight _) a]
  exact finsum_induction (· ∈ J) J.zero_mem (fun _ _ => J.add_mem) (fun c =>
    h _ c (weightedHomogeneousComponent_isWeightedHomogeneous _ _) (hI a ha c))

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem homX (v : Σ k, ι k) : IsMultiHomog (X v : MRing ι R) (Pi.single v.1 1) :=
  isWeightedHomogeneous_X R (blockWeight ι) v

theorem Setup.exists_centre (S : Setup φ P 𝒲) (V : ValuationSubring L) (hV : ∀ r, φ (C r) ∈ V) :
    ∃ y, IsMultiProjPrime y ∧ P ≤ y ∧ ∀ F G b, IsMultiHomog F b → IsMultiHomog G b → G ∉ y →
      φ F / φ G ∈ V ∧ (F ∈ y ↔ φ F / φ G ∈ V.nonunits) := by
  have hmax : ∀ k, ∃ i, φ (X ⟨k, i⟩) ≠ 0 ∧
      ∀ j, V.valuation (φ (X ⟨k, j⟩)) ≤ V.valuation (φ (X ⟨k, i⟩)) := by
    intro k
    obtain ⟨i₀, hi₀⟩ := S.mp.relevant k
    obtain ⟨i, -, hmx⟩ := Finset.exists_max_image Finset.univ
      (fun j => V.valuation (φ (X ⟨k, j⟩))) ⟨i₀, Finset.mem_univ _⟩
    refine ⟨i, fun h0 => hi₀ ((S.ker _ _ (homX _)).mp ?_), fun j => hmx j (Finset.mem_univ _)⟩
    have := hmx i₀ (Finset.mem_univ _)
    rw [h0, map_zero, le_zero_iff] at this
    exact (Valuation.zero_iff _).mp this
  choose c hc hcmax using hmax
  have hchart : ∀ p, dehom φ c p ∈ V := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a => rw [dehom, eval₂Hom_C]; exact hV a
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p v hp =>
      rw [map_mul]
      refine mul_mem hp ?_
      rw [dehom, eval₂Hom_X', ← V.valuation_le_one_iff, map_div₀]
      have h0 : V.valuation (φ (X ⟨v.1, c v.1⟩)) ≠ 0 := by
        rw [Ne, Valuation.zero_iff]; exact hc v.1
      exact (div_le_one₀ (zero_lt_iff.mpr h0)).mpr (hcmax v.1 v.2)
  let χ : MRing ι R →+* V := (dehom φ c).codRestrict V hchart
  have hχ : ∀ p, (χ p : L) = dehom φ c p := fun p => rfl
  let ρ : MRing ι R →+* IsLocalRing.ResidueField V := (IsLocalRing.residue V).comp χ
  let _ : Algebra R (IsLocalRing.ResidueField V) := (ρ.comp C).toAlgebra
  have hρ : ∀ F, aeval (fun v => ρ (X v)) F = ρ F := fun F =>
    RingHom.congr_fun (show (aeval (fun v => ρ (X v))).toRingHom = ρ from
      MvPolynomial.ringHom_ext (fun r => aeval_C _ r) (fun v => aeval_X _ v)) F
  have hyform : ∀ F b, IsMultiHomog F b → (F ∈ pointIdeal R (fun v => ρ (X v)) ↔ ρ F = 0) :=
    fun F b hF => ⟨fun h => hρ F ▸ GenericProjClosureDivisor.aeval_eq_zero_of_mem h,
      fun h => GenericProjClosureDivisor.mem_of_homog hF ((hρ F).trans h)⟩
  have hmon : ∀ b, φ (powMonomial b c) ≠ 0 := fun b => by
    simp only [powMonomial, map_prod, map_pow]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
  refine ⟨pointIdeal R (fun v => ρ (X v)),
    GenericProjClosureDim.isMultiProjPrime_pointIdeal _ (fun k => ⟨c k, ?_⟩), ?_, ?_⟩
  · have h1 : χ (X ⟨k, c k⟩) = 1 := by
      apply Subtype.ext
      rw [hχ, dehom, eval₂Hom_X']
      exact div_self (hc k)
    simp only [ρ, RingHom.comp_apply, h1, map_one]
    exact one_ne_zero
  · refine le_of_forms S.mp.multiHomog fun F b hF h => (hyform F b hF).mpr ?_
    have h0 : χ F = 0 := by
      apply Subtype.ext
      rw [hχ, dehom_eq hc hF, (S.ker F b hF).mpr h, zero_div]
      rfl
    simp only [ρ, RingHom.comp_apply, h0, map_zero]
  · intro f g b hf hg hgy
    have hgu : IsUnit (χ g) := by
      rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
      exact fun h => hgy ((hyform g b hg).mpr h)
    have hg0 : (χ g : L) ≠ 0 := fun h => hgu.ne_zero (Subtype.ext h)
    have hquot : φ f / φ g = ((χ f * ↑hgu.unit⁻¹ : V) : L) := by
      have e1 : φ f / φ g = (χ f : L) / (χ g : L) := by
        rw [hχ, hχ, dehom_eq hc hf, dehom_eq hc hg, div_div_div_cancel_right₀ (hmon b)]
      have e2 : (χ g : L) * ((↑hgu.unit⁻¹ : V) : L) = 1 := by
        rw [← Subring.coe_mul, IsUnit.mul_val_inv]; rfl
      rw [e1, div_eq_iff hg0, Subring.coe_mul, mul_assoc, mul_comm _ (χ g : L), e2, mul_one]
    rw [hquot, ValuationSubring.coe_mem_nonunits_iff, ← IsLocalRing.residue_eq_zero_iff, map_mul,
      hyform f b hf]
    refine ⟨Subtype.mem _, ?_⟩
    have hu : IsLocalRing.residue V (↑hgu.unit⁻¹ : V) ≠ 0 :=
      (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr (Units.isUnit _)
    simp only [ρ, RingHom.comp_apply, mul_eq_zero]
    exact ⟨Or.inl, fun h => h.resolve_right hu⟩

omit [∀ k, Fintype (ι k)] in
theorem Setup.frac (S : Setup φ P 𝒲) {W : Ideal (MRing ι R)} (hW : W ∈ 𝒲)
    {𝔪 : Ideal (loc φ 𝒲)} (hv : IsVan φ 𝒲 W 𝔪) (z : L) (hz : z ∈ loc φ {W}) :
    ∃ a s : loc φ 𝒲, s ∉ 𝔪 ∧ z * (s : L) = a := by
  obtain ⟨F, G, hr⟩ := (mem_loc (S.single hW).prime).mp hz
  obtain ⟨b, hF, hG⟩ := hr.hom
  obtain ⟨u, H, hu, -, hc⟩ := S.clear b (S.mpW W hW)
  refine ⟨⟨_, (hc F hF).mem⟩, ⟨_, (hc G hG).mem⟩, fun h => ?_, ?_⟩
  · exact ((S.prime W hW).mem_or_mem ((hv ⟨_, (hc G hG).mem⟩ _ _ (hc G hG)).mp h)).elim
      (hr.avoid W rfl) hu
  · change z * (φ (G * u) / φ H) = φ (F * u) / φ H
    rw [hr.eq, map_mul, map_mul, ← mul_div_assoc, ← mul_assoc, div_mul_cancel₀ _ hr.ne]

theorem Setup.finite (S : Setup φ P 𝒲) (hne : 𝒲.Nonempty) {A : Subring L} (h : A ≤ loc φ 𝒲)
    (hC : ∀ r, φ (C r) ∈ A) (hint : letI := inclAlg h; Algebra.IsIntegral A (loc φ 𝒲)) :
    letI := inclAlg h
    Module.Finite A (loc φ 𝒲) := by
  have : Finite 𝒲 := S.fin.to_subtype
  choose 𝔪 hp hv using fun W : 𝒲 => S.exists_van W.2
  choose c hc using fun W : 𝒲 => (S.mpW W.1 W.2).relevant
  have hc0 : ∀ W k, φ (X ⟨k, c W k⟩) ≠ 0 := fun W k => S.ne W.2 (homX _) (hc W k)
  have hrat : ∀ (W : 𝒲) (v : Σ k, ι k), φ (X v) / φ (X ⟨v.1, c W v.1⟩) ∈ loc φ {W.1} := fun W v =>
    Rep.mem (F := X v) (G := X ⟨v.1, c W v.1⟩) ⟨⟨_, homX v, homX ⟨v.1, c W v.1⟩⟩, hc0 W v.1,
      fun _ h => h ▸ hc W v.1, rfl⟩
  choose a s hs has using fun (W : 𝒲) v => S.frac W.2 (hv W) _ (hrat W v)
  set T : Set L := Set.range (fun p : 𝒲 × (Σ k, ι k) => (a p.1 p.2 : L)) ∪
    Set.range (fun p : 𝒲 × (Σ k, ι k) => (s p.1 p.2 : L)) with hT
  have hTB : T ⊆ loc φ 𝒲 := by
    rintro _ (⟨p, rfl⟩ | ⟨p, rfl⟩)
    · exact (a p.1 p.2).2
    · exact (s p.1 p.2).2
  refine finite_subring h hint T ((Set.finite_range _).union (Set.finite_range _)) hTB ?_
  intro M hM b
  set D := Subring.closure ((A : Set L) ∪ T)
  have hDB : D ≤ loc φ 𝒲 := Subring.closure_le.mpr (Set.union_subset h hTB)
  obtain ⟨W, rfl⟩ := S.max_eq hne 𝔪 hp hv M hM
  have hnm : ∀ {x y : loc φ 𝒲}, x ∉ 𝔪 W → y ∉ 𝔪 W → x * y ∉ 𝔪 W :=
    fun hx hy hxy => ((hp W).mem_or_mem hxy).elim hx hy
  have claim : ∀ p, ∃ d : loc φ 𝒲, d ∉ 𝔪 W ∧ (d : L) ∈ D ∧ (d : L) * dehom φ (c W) p ∈ D := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C r =>
      refine ⟨1, (Ideal.ne_top_iff_one _).mp (hp W).ne_top, D.one_mem, ?_⟩
      rw [OneMemClass.coe_one, one_mul, dehom, eval₂Hom_C]
      exact Subring.subset_closure (Or.inl (hC r))
    | add p q hp hq =>
      obtain ⟨d, h1, h2, h3⟩ := hp
      obtain ⟨d', h1', h2', h3'⟩ := hq
      refine ⟨d * d', hnm h1 h1', D.mul_mem h2 h2', ?_⟩
      have e : ((d * d' : loc φ 𝒲) : L) * dehom φ (c W) (p + q) =
          (d : L) * dehom φ (c W) p * d' + d * (d' * dehom φ (c W) q) := by
        rw [map_add, Subring.coe_mul]; ring
      rw [e]
      exact D.add_mem (D.mul_mem h3 h2') (D.mul_mem h2 h3')
    | mul_X p v hp =>
      obtain ⟨d, h1, h2, h3⟩ := hp
      refine ⟨d * s W v, hnm h1 (hs W v), D.mul_mem h2
        (Subring.subset_closure (Or.inr (Or.inr ⟨(W, v), rfl⟩))), ?_⟩
      have e : ((d * s W v : loc φ 𝒲) : L) * dehom φ (c W) (p * X v) =
          (d : L) * dehom φ (c W) p * a W v := by
        rw [map_mul, Subring.coe_mul, ← has W v]
        simp only [dehom, eval₂Hom_X']
        ring
      rw [e]
      exact D.mul_mem h3 (Subring.subset_closure (Or.inr (Or.inl ⟨(W, v), rfl⟩)))
  obtain ⟨F, G, hr⟩ := (mem_loc S.prime).mp b.2
  obtain ⟨e, hF, hG⟩ := hr.hom
  obtain ⟨d, h1, h2, h3⟩ := claim F
  obtain ⟨d', h1', h2', h3'⟩ := claim G
  have hm0 : φ (powMonomial e (c W)) ≠ 0 := S.ne W.2 (isMultiHomog_powMonomial e _)
    (powMonomial_notMem (S.prime _ W.2) (hc W) e)
  have hy : Rep φ 𝒲 _ (powMonomial e (c W)) G :=
    ⟨⟨e, isMultiHomog_powMonomial e _, hG⟩, hr.ne, hr.avoid, rfl⟩
  have hG0 := hr.ne
  refine ⟨d * ⟨_, hDB h3'⟩, D.mul_mem h2 h3', hnm h1 fun hx => h1' ?_, ?_⟩
  · have e1 : d' = ⟨_, hDB h3'⟩ * ⟨_, hy.mem⟩ := by
      apply Subtype.ext
      change (d' : L) = (d' : L) * dehom φ (c W) G * (φ (powMonomial e (c W)) / φ G)
      rw [dehom_eq (hc0 W) hG]
      field_simp
    rw [e1]
    exact Ideal.mul_mem_right _ _ hx
  · have e2 : ((d * ⟨_, hDB h3'⟩ : loc φ 𝒲) : L) * b = d' * (d * dehom φ (c W) F) := by
      change (d : L) * ((d' : L) * dehom φ (c W) G) * b = _
      rw [hr.eq, dehom_eq (hc0 W) hG, dehom_eq (hc0 W) hF]
      field_simp
    rw [e2]
    exact D.mul_mem h2' h3

omit [∀ k, Fintype (ι k)] in
theorem Setup.ffield_frac (S : Setup φ P 𝒲) (x : L) (hx : x ∈ ffield φ) :
    ∃ a ∈ loc φ 𝒲, ∃ a' ∈ loc φ 𝒲, x = a / a' := by
  obtain ⟨F, G, hr⟩ := mem_ffield.mp hx
  obtain ⟨b, hF, hG⟩ := hr.hom
  obtain ⟨u, H, hu, ⟨e, hue⟩, hc⟩ := S.clear b S.mp
  refine ⟨_, (hc F hF).mem, _, (hc G hG).mem, ?_⟩
  have hu0 : φ u ≠ 0 := fun h => hu ((S.ker u e hue).mp h)
  rw [hr.eq, div_div_div_cancel_right₀ (hc F hF).ne, map_mul, map_mul, mul_div_mul_right _ _ hu0]

variable {K₀ : Type} [Fintype K₀] [DecidableEq K₀] {ι₀ : K₀ → Type} [∀ k, Fintype (ι₀ k)]

structure Proj (r : MRing ι₀ R →+* MRing ι R) : Prop where
  hom : ∃ τ : (K₀ → ℕ) → K → ℕ, ∀ F b, IsMultiHomog F b → IsMultiHomog (r F) (τ b)
  map_C : ∀ a, r (C a) = C a
  comap : ∀ y, IsMultiProjPrime y → IsMultiProjPrime (y.comap r)

variable {r : MRing ι₀ R →+* MRing ι R}

omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K₀] [∀ k, Fintype (ι₀ k)] in
theorem Rep.proj (hr : Proj r) {𝒲₀ : Set (Ideal (MRing ι₀ R))} (h𝒲 : ∀ W ∈ 𝒲, W.comap r ∈ 𝒲₀)
    {z : L} {F G : MRing ι₀ R} (h : Rep (φ.comp r) 𝒲₀ z F G) : Rep φ 𝒲 z (r F) (r G) := by
  obtain ⟨τ, hτ⟩ := hr.hom
  obtain ⟨b, hF, hG⟩ := h.hom
  exact ⟨⟨τ b, hτ F b hF, hτ G b hG⟩, h.ne, fun W hW => h.avoid _ (h𝒲 W hW), h.eq⟩

omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K₀] [∀ k, Fintype (ι₀ k)] in
theorem Proj.loc_le (hr : Proj r) {𝒲₀ : Set (Ideal (MRing ι₀ R))}
    (h𝒲 : ∀ W ∈ 𝒲, W.comap r ∈ 𝒲₀) : loc (φ.comp r) 𝒲₀ ≤ loc φ 𝒲 :=
  Subring.closure_mono fun _ ⟨_, _, h⟩ => ⟨_, _, h.proj hr h𝒲⟩

omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K₀] [∀ k, Fintype (ι₀ k)] in
theorem Proj.ffield_le (hr : Proj r) : ffield (φ.comp r) ≤ ffield φ := by
  intro x hx
  obtain ⟨F, G, h⟩ := mem_ffield.mp hx
  exact mem_ffield.mpr ⟨_, _, h.proj hr (by simp)⟩

omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K₀] [∀ k, Fintype (ι₀ k)] in
theorem Setup.proj (S : Setup φ P 𝒲) (hr : Proj r) {W : Ideal (MRing ι₀ R)}
    (hW : IsMultiProjPrime W) (hPW : P.comap r ≤ W) : Setup (φ.comp r) (P.comap r) {W} := by
  obtain ⟨τ, hτ⟩ := hr.hom
  exact ⟨hr.comap P S.mp, fun F b hF => S.ker _ _ (hτ F b hF), Set.finite_singleton W,
    fun _ h => h ▸ hW, fun _ h => h ▸ hPW⟩

omit [∀ k, Fintype (ι₀ k)] in
theorem Setup.integral (S : Setup φ P 𝒲) (hr : Proj r) {W : Ideal (MRing ι₀ R)}
    (hW : IsMultiProjPrime W) (hPW : P.comap r ≤ W) (hfib : ∀ W' ∈ 𝒲, W'.comap r ∈ ({W} : Set _))
    (hy : ∀ y, IsMultiProjPrime y → P ≤ y → y.comap r ≤ W → y = P ∨ y ∈ 𝒲) :
    letI := inclAlg (hr.loc_le (φ := φ) hfib)
    Algebra.IsIntegral (loc (φ.comp r) {W}) (loc φ 𝒲) := by
  refine isIntegral_of_valuation _ fun V hV => ?_
  have S₀ := S.proj hr hW hPW
  obtain ⟨τ, hτ⟩ := hr.hom
  obtain ⟨y, hmp, hPy, hcen⟩ := S.exists_centre V fun a => by
    rw [← hr.map_C]
    exact hV (rep_C (φ := φ.comp r) S₀.prime a).mem
  have hy₀ := hr.comap y hmp
  have hle : y.comap r ≤ W := by
    refine le_of_forms hy₀.multiHomog fun F b hF hFy => ?_
    by_contra hFW
    obtain ⟨i, hi⟩ := powMonomial_not_mem hy₀.isPrime hy₀.relevant b
    have hm := isMultiHomog_powMonomial (R := R) b i
    have hF0 : φ (r F) ≠ 0 := S₀.ne (Set.mem_singleton W) hF hFW
    have hm0 : φ (r (powMonomial b i)) ≠ 0 := fun h => hi (hPy ((S.ker _ _ (hτ _ _ hm)).mp h))
    have h1 : φ (r (powMonomial b i)) / φ (r F) ∈ V :=
      hV (Rep.mem (φ := φ.comp r) (F := powMonomial b i) (G := F)
        ⟨⟨b, hm, hF⟩, hF0, fun _ h => h ▸ hFW, rfl⟩)
    have h2 := (hcen _ _ _ (hτ _ _ hF) (hτ _ _ hm) hi).2.mp hFy
    rw [ValuationSubring.mem_nonunits_iff] at h2
    have h3 := (V.valuation_le_one_iff _).mpr h1
    have h4 := mul_lt_one_of_lt_of_le h2 h3
    rw [← map_mul, div_mul_div_cancel₀ hm0, div_self hF0, map_one] at h4
    exact lt_irrefl _ h4
  intro z hz
  obtain ⟨F, G, h⟩ := (mem_loc S.prime).mp hz
  obtain ⟨b, hF, hG⟩ := h.hom
  rw [h.eq]
  refine (hcen F G b hF hG ?_).1
  rcases hy y hmp hPy hle with rfl | h'
  · exact fun hm => h.ne ((S.ker G b hG).mpr hm)
  · exact h.avoid y h'

omit [∀ k, Fintype (ι₀ k)] in
theorem Setup.local_sum (S : Setup φ P 𝒲) [Fintype 𝒲] (hr : Proj r) {W : Ideal (MRing ι₀ R)}
    (hW : IsMultiProjPrime W) (hPW : P.comap r ≤ W) (hfib : ∀ W' ∈ 𝒲, W'.comap r ∈ ({W} : Set _))
    (hy : ∀ y, IsMultiProjPrime y → P ≤ y → y.comap r ≤ W → y = P ∨ y ∈ 𝒲)
    (hanti : ∀ W₁ ∈ 𝒲, ∀ W₂ ∈ 𝒲, W₁ ≤ W₂ → W₁ = W₂)
    [IsLocalRing (loc (φ.comp r) {W})] [IsNoetherianRing (loc (φ.comp r) {W})]
    (hdim : ringKrullDim (loc (φ.comp r) {W}) = 1)
    (E : 𝒲 → Type) [∀ W', Field (E W')] (ψ : ∀ W', MRing ι R →+* E W')
    (hψ : ∀ (W' : 𝒲) F, ψ W' F = 0 ↔ F ∈ W'.1) (α : L) (hα : α ∈ loc (φ.comp r) {W}) (h0 : α ≠ 0)
    (hα' : ∀ W' : 𝒲, α ∈ loc φ {W'.1}) :
    ∑ W' : 𝒲, Ring.ord (loc φ {W'.1}) ⟨α, hα' W'⟩ *
        (((ffield ((ψ W').comp r)).relfinrank (ffield (ψ W')) : ℕ) : ℕ∞) =
      (((ffield (φ.comp r)).relfinrank (ffield φ) : ℕ) : ℕ∞) *
        Ring.ord (loc (φ.comp r) {W}) ⟨α, hα⟩ := by
  have S₀ := S.proj hr hW hPW
  have hAB := hr.loc_le (φ := φ) hfib
  have hint := S.integral hr hW hPW hfib hy
  have hne : 𝒲.Nonempty := by
    by_contra hc
    rw [Set.not_nonempty_iff_eq_empty] at hc
    refine not_isField_of_integral hAB hdim hint ?_
    rw [hc]
    exact fun b hb => (ffield φ).inv_mem hb
  have hfin := S.finite hne hAB (fun a => by
    rw [← hr.map_C]
    exact (rep_C (φ := φ.comp r) S₀.prime a).mem) hint
  choose e he using fun W' : 𝒲 => S.exists_res W'.2 (ψ W') (hψ W')
  have hv : ∀ W' : 𝒲, IsVan φ 𝒲 W'.1 (RingHom.ker (e W')) := fun W' =>
    isVan_ker W'.2 (hψ W') (he W')
  have hp : ∀ W' : 𝒲, (RingHom.ker (e W')).IsPrime := fun W' => RingHom.ker_isPrime _
  have hcov := S.max_eq hne _ hp hv
  have hsep : ∀ W₁ W₂ : 𝒲, RingHom.ker (e W₁) ≤ RingHom.ker (e W₂) → W₁ = W₂ := fun W₁ W₂ h =>
    Subtype.ext (hanti _ W₁.2 _ W₂.2 (IsVan.le_of_le S W₁.2 W₂.2 (hv W₁) (hv W₂) h))
  have hmax : ∀ W' : 𝒲, (RingHom.ker (e W')).IsMaximal := by
    intro W'
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ (hp W').ne_top
    obtain ⟨W'', rfl⟩ := hcov M hM
    obtain rfl := hsep W' W'' hle
    exact hM
  refine sum_subring hAB hdim hfin (fun W' => RingHom.ker (e W')) hmax
    (fun W₁ W₂ h => hsep W₁ W₂ (le_of_eq h)) hcov (fun W' => loc φ {W'.1})
    (fun W' => loc_anti (Set.singleton_subset_iff.mpr W'.2))
    (fun W' => haveI := hp W'; S.isLocalization W'.2 (hv W')) _ (fun W' => ?_) _ ?_ α hα h0
  · refine res_subring hAB hfin (e W') (hmax W') hr.ffield_le (fun a ha => ?_) (fun b => ?_)
      (fun x hx => ?_) (fun x hx => ?_)
    · obtain ⟨F, G, h⟩ := (mem_loc S₀.prime).mp ha
      obtain ⟨b, hF, hG⟩ := h.hom
      rw [he W' ⟨a, hAB ha⟩ _ _ (h.proj hr hfib)]
      exact div_mem_ffield (φ := (ψ W').comp r) hF hG
    · obtain ⟨F, G, h⟩ := (mem_loc S.prime).mp b.2
      obtain ⟨b', hF, hG⟩ := h.hom
      rw [he W' b _ _ h]
      exact div_mem_ffield hF hG
    · obtain ⟨F, G, h⟩ := mem_ffield.mp hx
      obtain ⟨b, hF, hG⟩ := h.hom
      have hGW : G ∉ W := by
        rw [← Set.mem_singleton_iff.mp (hfib _ W'.2)]
        exact fun hm => h.ne ((hψ W' _).mpr hm)
      have h' : Rep (φ.comp r) {W} _ F G :=
        ⟨⟨b, hF, hG⟩, S₀.ne (Set.mem_singleton W) hG hGW, fun _ h => h ▸ hGW, rfl⟩
      refine ⟨_, h'.mem, ?_⟩
      rw [he W' ⟨_, hAB h'.mem⟩ _ _ (h'.proj hr hfib), h.eq]
      rfl
    · obtain ⟨F, G, h⟩ := mem_ffield.mp hx
      obtain ⟨b, hF, hG⟩ := h.hom
      obtain ⟨u, H, hu, -, hc⟩ := S.clear b (S.mpW _ W'.2)
      refine ⟨⟨_, (hc F hF).mem⟩, ⟨_, (hc G hG).mem⟩, ?_⟩
      have hu0 : ψ W' u ≠ 0 := fun h => hu ((hψ W' u).mp h)
      have hH0 : ψ W' H ≠ 0 := fun h => (hc F hF).avoid _ W'.2 ((hψ W' H).mp h)
      rw [he W' ⟨_, (hc F hF).mem⟩ _ _ (hc F hF), he W' ⟨_, (hc G hG).mem⟩ _ _ (hc G hG), h.eq,
        div_div_div_cancel_right₀ hH0, map_mul, map_mul, mul_div_mul_right _ _ hu0]
  · exact rank_subring hAB hr.ffield_le (fun a ha => loc_anti (Set.empty_subset _) ha)
      (fun a ha => loc_anti (Set.empty_subset _) ha) S₀.ffield_frac S.ffield_frac

end Pair

section Transfer

variable {R : Type} [CommRing R] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {L : Type} [Field L]
  {φ : MRing ι R →+* L} {𝒲 : Set (Ideal (MRing ι R))} {P : Ideal (MRing ι R)}

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem Setup.exists_equiv' {W : Ideal (MRing ι R)} (S : Setup φ P {W}) {L₀ : Type} [Field L₀]
    {φ₀ : MRing ι R →+* L₀} (S₀ : Setup φ₀ P {W}) :
    ∃ e : loc φ₀ {W} ≃+* loc φ {W}, ∀ (z : loc φ₀ {W}) F G, Rep φ₀ {W} z F G →
      (e z : L) = φ F / φ G := by
  have hW := Set.mem_singleton W
  obtain ⟨e, he⟩ := exists_ev (φ := φ₀) S.prime φ
    (fun F b hF h => (S.ker F b hF).mpr ((S₀.ker F b hF).mp h))
    (fun G b hG _ h => S.ne hW hG (h W hW))
  have hmem : ∀ z, e z ∈ loc φ {W} := by
    intro z
    obtain ⟨F, G, h⟩ := (mem_loc S.prime).mp z.2
    obtain ⟨b, hF, hG⟩ := h.hom
    exact Rep.mem (F := F) (G := G) ⟨⟨b, hF, hG⟩, S.ne hW hG (h.avoid W hW), h.avoid, he z F G h⟩
  have hinj : Function.Injective e := by
    refine (injective_iff_map_eq_zero e).mpr fun z hz => ?_
    obtain ⟨F, G, h⟩ := (mem_loc S.prime).mp z.2
    obtain ⟨b, hF, hG⟩ := h.hom
    rw [he z F G h, div_eq_zero_iff] at hz
    have hF0 := (S.ker F b hF).mp (hz.resolve_right (S.ne hW hG (h.avoid W hW)))
    apply Subtype.ext
    rw [h.eq, (S₀.ker F b hF).mpr hF0, zero_div]
    rfl
  have hbij : Function.Bijective (e.codRestrict (loc φ {W}) hmem) := by
    refine ⟨fun a b h => hinj (congrArg Subtype.val h), fun z => ?_⟩
    obtain ⟨F, G, h⟩ := (mem_loc S.prime).mp z.2
    obtain ⟨b, hF, hG⟩ := h.hom
    have h' : Rep φ₀ {W} _ F G := ⟨h.hom, S₀.ne hW hG (h.avoid W hW), h.avoid, rfl⟩
    exact ⟨⟨_, h'.mem⟩, Subtype.ext ((he ⟨_, h'.mem⟩ F G h').trans h.eq.symm)⟩
  exact ⟨RingEquiv.ofBijective _ hbij, he⟩

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem Setup.exists_equiv {W : Ideal (MRing ι R)} (S : Setup φ P {W}) [P.IsPrime] :
    ∃ e : homLocRing P W ≃+* loc φ {W}, ∀ (z : homLocRing P W) F G b, IsMultiHomog F b →
      IsMultiHomog G b → G ∉ W → (z : FractionRing (MRing ι R ⧸ P)) = qm P F / qm P G →
      (e z : L) = φ F / φ G := by
  have hW := Set.mem_singleton W
  have hne : ∀ G, G ∉ W → qm P G ≠ 0 := fun G hG h => hG (S.le W hW ((qm_eq_zero P G).mp h))
  have heq : homLocRing P W = loc (qm P) {W} := by
    unfold homLocRing loc
    congr 1
    ext z
    constructor
    · rintro ⟨b, F, G, hF, hG, hGW, rfl⟩
      exact ⟨F, G, ⟨b, hF, hG⟩, hne G hGW, fun _ h => h ▸ hGW, rfl⟩
    · rintro ⟨F, G, h⟩
      obtain ⟨b, hF, hG⟩ := h.hom
      exact ⟨b, F, G, hF, hG, h.avoid W hW, h.eq⟩
  rw [heq]
  obtain ⟨e, he⟩ := S.exists_equiv' (φ₀ := qm P)
    ⟨S.mp, fun F _ _ => qm_eq_zero P F, S.fin, S.mpW, S.le⟩
  exact ⟨e, fun z F G b hF hG hGW hz =>
    he z F G ⟨⟨b, hF, hG⟩, hne G hGW, fun _ h => h ▸ hGW, hz⟩⟩

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem ffield_comp {E : Type} [Field E] (θ : L →+* E) : ffield (θ.comp φ) = (ffield φ).map θ := by
  ext x
  constructor
  · intro hx
    obtain ⟨F, G, h⟩ := mem_ffield.mp hx
    obtain ⟨b, hF, hG⟩ := h.hom
    exact ⟨_, div_mem_ffield hF hG, by rw [map_div₀, h.eq]; rfl⟩
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨F, G, h⟩ := mem_ffield.mp hz
    obtain ⟨b, hF, hG⟩ := h.hom
    rw [h.eq, map_div₀]
    exact div_mem_ffield (φ := θ.comp φ) hF hG

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem ffield_map {R₀ : Type} [CommRing R₀] (π : R₀ →+* R) (hπ : Function.Surjective π) :
    ffield (φ.comp (MvPolynomial.map π)) = ffield φ := by
  have lift : ∀ (F : MRing ι R) b, IsMultiHomog F b →
      ∃ F₀ : MRing ι R₀, IsMultiHomog F₀ b ∧ MvPolynomial.map π F₀ = F := by
    intro F b hF
    obtain ⟨F₁, rfl⟩ := MvPolynomial.map_surjective π hπ F
    refine ⟨_, weightedHomogeneousComponent_isWeightedHomogeneous (w := blockWeight ι) b F₁, ?_⟩
    rw [← weightedHomogeneousComponent_map]
    exact IsWeightedHomogeneous.weightedHomogeneousComponent_same hF
  have push : ∀ (F : MRing ι R₀) b, IsMultiHomog F b → IsMultiHomog (MvPolynomial.map π F) b := by
    intro F b hF d hd
    apply hF
    intro h0
    rw [coeff_map, h0, map_zero] at hd
    exact hd rfl
  ext x
  constructor
  · intro hx
    obtain ⟨F, G, h⟩ := mem_ffield.mp hx
    obtain ⟨b, hF, hG⟩ := h.hom
    rw [h.eq]
    exact div_mem_ffield (push F b hF) (push G b hG)
  · intro hx
    obtain ⟨F, G, h⟩ := mem_ffield.mp hx
    obtain ⟨b, hF, hG⟩ := h.hom
    obtain ⟨F₀, hF₀, rfl⟩ := lift F b hF
    obtain ⟨G₀, hG₀, rfl⟩ := lift G b hG
    rw [h.eq]
    exact div_mem_ffield (φ := φ.comp (MvPolynomial.map π)) hF₀ hG₀

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem homFrac_eq {F : Type} [Field F] (Q : Ideal (MRing ι F)) [Q.IsPrime] :
    (GroundTheory.Heights₂.Heights.FieldNumbers.homFracDegZero Q).toSubfield = ffield (qm Q) := by
  apply le_antisymm
  · unfold GroundTheory.Heights₂.Heights.FieldNumbers.homFracDegZero
    rw [IntermediateField.adjoin_toSubfield, Subfield.closure_le]
    rintro x (⟨c, rfl⟩ | ⟨b, f, g, hf, hg, -, rfl⟩)
    · rw [IsScalarTower.algebraMap_apply F (MRing ι F ⧸ Q)]
      exact (rep_C (φ := qm Q) (𝒲 := ∅) (by simp) c).mem
    · exact div_mem_ffield (φ := qm Q) hf hg
  · intro x hx
    obtain ⟨f, g, h⟩ := mem_ffield.mp hx
    obtain ⟨b, hf, hg⟩ := h.hom
    exact IntermediateField.subset_adjoin _ _
      ⟨b, f, g, hf, hg, fun hm => h.ne ((qm_eq_zero Q g).mpr hm), h.eq⟩

theorem ffield_aeval {O : Type} [CommRing O] [Algebra O L] (y : (Σ k, ι k) → L)
    (hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) :
    ffield (aeval y : MRing ι O →ₐ[O] L).toRingHom = fnField O y := by
  set φ := (aeval y : MRing ι O →ₐ[O] L).toRingHom
  have hX : ∀ v, φ (X v) = y v := fun v => aeval_X y v
  have hC : ∀ a, φ (C a) = algebraMap O L a := fun a => aeval_C y a
  apply le_antisymm
  · choose c hc using hy
    have hc' : ∀ k, φ (X ⟨k, c k⟩) ≠ 0 := fun k => by rw [hX]; exact hc k
    have hd : ∀ p, dehom φ c p ∈ fnField O y := by
      intro p
      induction p using MvPolynomial.induction_on with
      | C a =>
        rw [dehom, eval₂Hom_C, RingHom.comp_apply, hC]
        exact Subfield.subset_closure (Or.inl ⟨a, rfl⟩)
      | add p q hp hq => rw [map_add]; exact add_mem hp hq
      | mul_X p v hp =>
        rw [map_mul]
        refine mul_mem hp ?_
        rw [dehom, eval₂Hom_X', hX, hX]
        exact Subfield.subset_closure (Or.inr ⟨⟨v.1, v.2, c v.1⟩, rfl⟩)
    intro x hx
    obtain ⟨F, G, h⟩ := mem_ffield.mp hx
    obtain ⟨b, hF, hG⟩ := h.hom
    have hmon : φ (powMonomial b c) ≠ 0 := by
      simp only [powMonomial, map_prod, map_pow]
      exact Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc' k)
    rw [h.eq, ← div_div_div_cancel_right₀ hmon, ← dehom_eq hc' hF, ← dehom_eq hc' hG]
    exact div_mem (hd F) (hd G)
  · unfold fnField
    rw [Subfield.closure_le]
    rintro x (⟨a, rfl⟩ | ⟨q, rfl⟩)
    · rw [← hC]
      exact (rep_C (φ := φ) (𝒲 := ∅) (by simp) a).mem
    · dsimp only
      rw [← hX, ← hX]
      exact div_mem_ffield (homX ⟨q.1, q.2.1⟩) (homX ⟨q.1, q.2.2⟩)

theorem loc_facts {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {φ : MRing ι O →+* L} {P W : Ideal (MRing ι O)} (S : Setup φ P {W}) {c : K → ℕ}
    {f g : MRing ι O} (hf : IsMultiHomog f c) (hfP : f ∉ P)
    (hW : W ∈ (P ⊔ Ideal.span {f}).minimalPrimes) (hg : IsMultiHomog g c) (hgW : g ∉ W)
    (hα : φ f / φ g ∈ loc φ {W}) :
    IsLocalRing (loc φ {W}) ∧ IsNoetherianRing (loc φ {W}) ∧ ringKrullDim (loc φ {W}) = 1 ∧
      Ring.ord (loc φ {W}) ⟨_, hα⟩ = ((divCycle P f W).toNat : ℕ∞) := by
  have := S.mp.isPrime
  have hrel := (S.mpW W rfl).relevant
  obtain ⟨e, he⟩ := S.exists_equiv
  obtain ⟨h1, h2, h3⟩ := A_s_divcyclehomloc.homLocRingLocal O K ι P S.mp c f hf hfP W hW hrel
  have hz : qm P f / qm P g ∈ homLocRing P W := Subring.subset_closure ⟨c, f, g, hf, hg, hgW, rfl⟩
  have h4 := t_s_divcyclehomloc O K ι P S.mp c f hf hfP W hW hrel g hg hgW hz
  refine ⟨e.isLocalRing, isNoetherianRing_of_ringEquiv _ e,
    (ringKrullDim_eq_of_ringEquiv e).symm.trans h3, ?_⟩
  have e1 : (⟨_, hα⟩ : loc φ {W}) = e ⟨_, hz⟩ := Subtype.ext (he ⟨_, hz⟩ f g c hf hg hgW rfl).symm
  rw [e1, ord_ringEquiv]
  have : W.IsPrime := hW.1.1
  have htop : multAt (P ⊔ Ideal.span {f}) W ≠ ⊤ := length_localizedQuot_ne_top _ W hW
  unfold divCycle
  rw [dif_pos ⟨hW, hrel⟩, Int.toNat_natCast, ENat.coe_toNat htop]
  exact h4.symm

omit [DecidableEq K] in
theorem divCycle_ne_zero {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {P W : Ideal (MRing ι O)} {f : MRing ι O}
    (hW : W ∈ (P ⊔ Ideal.span {f}).minimalPrimes) (hrel : IsRelevant W) : divCycle P f W ≠ 0 := by
  have : W.IsPrime := hW.1.1
  unfold divCycle
  rw [dif_pos ⟨hW, hrel⟩]
  have := localizedQuot_nontrivial_of_le (P ⊔ Ideal.span {f}) W hW.1.2
  have h0 : multAt (P ⊔ Ideal.span {f}) W ≠ 0 :=
    (Module.length_pos (R := Localization.AtPrime W)
      (M := LocalizedModule W.primeCompl (MRing ι O ⧸ (P ⊔ Ideal.span {f})))).ne'
  have htop := length_localizedQuot_ne_top _ W hW
  exact_mod_cast (ENat.toNat_pos h0 htop).ne'

omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in
theorem divCycle_supp {P W : Ideal (MRing ι R)} {f : MRing ι R} (h : divCycle P f W ≠ 0) :
    W ∈ (P ⊔ Ideal.span {f}).minimalPrimes ∧ IsRelevant W := by
  by_contra hc
  exact h (by unfold divCycle; rw [dif_neg hc])

omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in
theorem divCycle_nonneg (P W : Ideal (MRing ι R)) (f : MRing ι R) : 0 ≤ divCycle P f W := by
  unfold divCycle
  split_ifs <;> positivity

end Transfer

section Blocks

open GroundTheory.Heights₂.Heights.FieldNumbers

variable {K K' : Type} [Fintype K] [DecidableEq K] [Fintype K'] [DecidableEq K'] (j : K ↪ K')
  (ι' : K' → Type) [∀ k, Fintype (ι' k)]

def rr (R : Type) [CommRing R] : MRing (fun k => ι' (j k)) R →+* MRing ι' R :=
  (rename (blockIncl j ι') : MRing (fun k => ι' (j k)) R →ₐ[R] MRing ι' R).toRingHom

omit [Fintype K] [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem proj_rr (R : Type) [CommRing R] : Proj (rr j ι' R) where
  hom := ⟨fun b => Function.extend j b 0, fun F b hF => by
    have h := GroundTheory.Heights₂.Heights.FieldNumbers.ContractRelevant.rename_weightedHomogeneousComponent (g := blockIncl j ι') (j := j) (fun _ => rfl)
      j.injective (blockIncl_injective j ι') b F
    rw [IsWeightedHomogeneous.weightedHomogeneousComponent_same hF] at h
    change IsMultiHomog (rename (blockIncl j ι') F) _
    rw [h]
    exact weightedHomogeneousComponent_isWeightedHomogeneous _ _⟩
  map_C a := rename_C _ a
  comap y hy := GroundTheory.Heights₂.Heights.FieldNumbers.ContractRelevant.isMultiProjPrime_comap_rename (g := blockIncl j ι') (j := j) (fun _ => rfl)
    j.injective (blockIncl_injective j ι') (by
      rintro ⟨k', i⟩ ⟨k, rfl⟩
      exact ⟨⟨k, i⟩, rfl⟩) hy

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}

theorem mem_special (hϖ : Irreducible ϖ) {K₁ : Type} [Fintype K₁] [DecidableEq K₁] {ι : K₁ → Type}
    {W : Ideal (MRing ι O)} (hW : (C ϖ : MRing ι O) ∈ W) (F : MRing ι O) :
    MvPolynomial.map (IsLocalRing.residue O) F ∈ specialIdeal W ↔ F ∈ W := by
  refine mem_map_iff_of_ker_le (MvPolynomial.map_surjective _ IsLocalRing.residue_surjective) ?_ F
  rw [ker_map_residue_eq_span hϖ, Ideal.span_le, Set.singleton_subset_iff]
  exact hW

omit [Fintype K] [Fintype K'] [∀ k, Fintype (ι' k)] [IsDomain O] [IsDiscreteValuationRing O] in
theorem C_mem_comap (W : Ideal (MRing ι' O)) :
    (C ϖ : MRing (fun k => ι' (j k)) O) ∈ W.comap (rr j ι' O) ↔ (C ϖ : MRing ι' O) ∈ W := by
  rw [Ideal.mem_comap, (proj_rr j ι' O).map_C]

omit [∀ k, Fintype (ι' k)] in
theorem contract_special (hϖ : Irreducible ϖ) {W : Ideal (MRing ι' O)}
    (hW : (C ϖ : MRing ι' O) ∈ W) :
    contractPrime j (specialIdeal W) = specialIdeal (W.comap (rr j ι' O)) := by
  ext y
  obtain ⟨z, rfl⟩ := MvPolynomial.map_surjective _ (IsLocalRing.residue_surjective (R := O)) y
  rw [mem_special hϖ ((C_mem_comap j ι' W).mpr hW), Ideal.mem_comap, ← mem_special hϖ hW,
    contractPrime, Ideal.mem_comap, ← map_rename]
  rfl

attribute [local instance] MvPolynomial.algebraMvPolynomial in
theorem mem_genFib {K₁ : Type} {ι : K₁ → Type} {P : Ideal (MRing ι O)} (hP : P.IsPrime)
    (hT : P.comap (C : O →+* MRing ι O) = ⊥) (F : MRing ι O) :
    MvPolynomial.map (algebraMap O (FractionRing O)) F ∈ genFib P ↔ F ∈ P := by
  let M : Submonoid (MRing ι O) := (nonZeroDivisors O).map (C (σ := Σ k, ι k))
  have : IsLocalization M (MRing ι (FractionRing O)) :=
    MvPolynomial.isLocalization (nonZeroDivisors O) (FractionRing O)
  have hdisj : Disjoint (M : Set (MRing ι O)) P := by
    rw [Set.disjoint_left]
    rintro _ ⟨m, hm, rfl⟩ hmP
    have : m ∈ P.comap (C : O →+* MRing ι O) := hmP
    rw [hT, Ideal.mem_bot] at this
    exact nonZeroDivisors.ne_zero hm this
  have hunder : (genFib P).comap (MvPolynomial.map (algebraMap O (FractionRing O))) = P :=
    IsLocalization.under_map_of_isPrime_disjoint M (MRing ι (FractionRing O)) hP hdisj
  rw [← Ideal.mem_comap, hunder]

omit [IsDomain O] [IsDiscreteValuationRing O] in
attribute [local instance] MvPolynomial.algebraMvPolynomial in
theorem exists_denom {K₁ : Type} {ι : K₁ → Type} (a : MRing ι (FractionRing O)) :
    ∃ (a₀ : MRing ι O) (u : MRing ι (FractionRing O)), IsUnit u ∧
      a * u = MvPolynomial.map (algebraMap O (FractionRing O)) a₀ := by
  let M : Submonoid (MRing ι O) := (nonZeroDivisors O).map (C (σ := Σ k, ι k))
  have : IsLocalization M (MRing ι (FractionRing O)) :=
    MvPolynomial.isLocalization (nonZeroDivisors O) (FractionRing O)
  obtain ⟨⟨a₀, s⟩, h⟩ := IsLocalization.surj M a
  exact ⟨a₀, _, IsLocalization.map_units _ s, h⟩

omit [Fintype K] [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem contract_generic {y : Ideal (MRing ι' O)} (hy : y.IsPrime)
    (hT : y.comap (C : O →+* MRing ι' O) = ⊥) :
    contractPrime j (genFib y) = genFib (y.comap (rr j ι' O)) := by
  have hT' : (y.comap (rr j ι' O)).comap (C : O →+* _) = ⊥ := by
    rw [← hT]
    ext a
    exact C_mem_comap j ι' y
  ext a
  obtain ⟨a₀, u, hu, h⟩ := exists_denom a
  rw [← Ideal.mul_unit_mem_iff_mem _ hu, ← Ideal.mul_unit_mem_iff_mem (genFib _) hu, h,
    mem_genFib (Ideal.comap_isPrime _ _) hT', Ideal.mem_comap, ← mem_genFib hy hT,
    contractPrime, Ideal.mem_comap, ← map_rename]
  rfl

theorem special_mp (hϖ : Irreducible ϖ) {K₁ : Type} [Fintype K₁] [DecidableEq K₁] {ι : K₁ → Type}
    [∀ k, Fintype (ι k)] {W : Ideal (MRing ι O)} (hmp : IsMultiProjPrime W)
    (hW : (C ϖ : MRing ι O) ∈ W) : IsMultiProjPrime (specialIdeal W) := by
  obtain ⟨hsp, -, hrel, -⟩ := SpecialIdealCorresp.proof O ϖ hϖ K₁ ι W W hmp.isPrime hW
  exact ⟨hsp, SpecialIdealMultiHomog.proof O K₁ ι W hmp.multiHomog, hrel.mp hmp.relevant⟩

theorem eq_of_le_le {x : WithBot ℕ∞} {N : ℕ} (h1 : x + 1 ≤ ((N + 1 : ℕ) : WithBot ℕ∞))
    (h2 : ((N + 1 : ℕ) : WithBot ℕ∞) ≤ x + 1) : x = N := by
  induction x using WithBot.recBotCoe with
  | bot => exact absurd h2 (by simp)
  | coe a =>
    induction a using ENat.recTopCoe with
    | top =>
      exfalso
      have h3 : ((⊤ : ℕ∞) + 1 : ℕ∞) ≤ ((N + 1 : ℕ) : ℕ∞) := by exact_mod_cast h1
      simp at h3
    | coe a =>
      have h3 : a + 1 ≤ N + 1 := by exact_mod_cast h1
      have h4 : N + 1 ≤ a + 1 := by exact_mod_cast h2
      exact_mod_cast (by omega : a = N)

variable {j ι'} {P' : Ideal (MRing ι' O)} {d : ℕ}

theorem eq_of_comap_eq (hP' : IsModelOver P' d) (hP : IsModelOver (P'.comap (rr j ι' O)) d)
    {y : Ideal (MRing ι' O)} (hy : IsMultiProjPrime y) (hle : P' ≤ y)
    (hc : y.comap (rr j ι' O) = P'.comap (rr j ι' O)) : y = P' := by
  by_contra hne
  have hT : y.comap (C : O →+* MRing ι' O) = ⊥ := by
    rw [← hP.noTorsion, ← hc]
    ext a
    exact (C_mem_comap j ι' y).symm
  obtain ⟨g1, g2, -⟩ := GenericFibProps.proof O K' ι' y hy hT
  have hgy : IsMultiProjPrime (genFib y) := ⟨g1, g2, fun k => by
    obtain ⟨i, hi⟩ := hy.relevant k
    refine ⟨i, fun h => hi ((mem_genFib hy.isPrime hT _).mp ?_)⟩
    rwa [map_X]⟩
  have h1 := ContractRelDimLe.proof (FractionRing O) K K' j ι' _ hgy
  rw [contract_generic j ι' hy.isPrime hT, hc] at h1
  have := hy.isPrime
  have := hP'.multiProj.isPrime
  have d1 := GenericDimBound.full O K' ι' y hy hT
  have d2 := DimStrictDrop.proof _ P' y (lt_of_le_of_ne hle (Ne.symm hne))
  rw [hP'.dim, show d + 1 + Fintype.card K' = (d + Fintype.card K') + 1 by omega] at d2
  have h2 := relDim_lt_of_dim_lt _ _ (lt_of_two_drops d1 d2)
  have d3 := GenericDimBound.full O K _ _ hP.multiProj hP.noTorsion
  have d4 := GenericDimGe.proof O K _ _ hP.multiProj.isPrime hP.noTorsion
  rw [hP.dim, show d + 1 + Fintype.card K = (d + Fintype.card K) + 1 by omega] at d3 d4
  rw [relDim_eq_of_dim _ _ (eq_of_le_le d3 d4)] at h1
  exact lt_irrefl _ (lt_of_le_of_lt h1 h2)

open Classical in

def srd (j : K ↪ K') (W' : Ideal (MRing ι' O)) : ℕ :=
  if h : (specialIdeal W').IsPrime then haveI := h; relDeg j (specialIdeal W') else 0

omit [Fintype K] [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem relDeg_eq (W' : Ideal (MRing ι' O)) [h : (specialIdeal W').IsPrime] :
    (ffield (((qm (specialIdeal W')).comp (MvPolynomial.map (IsLocalRing.residue O))).comp
      (rr j ι' O))).relfinrank
      (ffield ((qm (specialIdeal W')).comp (MvPolynomial.map (IsLocalRing.residue O)))) =
      srd j W' := by
  have hres := IsLocalRing.residue_surjective (R := O)
  have e1 : ((qm (specialIdeal W')).comp (MvPolynomial.map (IsLocalRing.residue O))).comp
      (rr j ι' O) = ((contractFracMap j (specialIdeal W')).toRingHom.comp
        (qm (contractPrime j (specialIdeal W')))).comp (MvPolynomial.map (IsLocalRing.residue O)) := by
    refine RingHom.ext fun F => ?_
    refine Eq.trans ?_ (contractFracMap_algebraMap j ι' (specialIdeal W') _).symm
    rw [← map_rename]
    rfl
  rw [e1, ffield_map _ hres, ffield_map _ hres, ffield_comp, ← homFrac_eq, ← homFrac_eq, srd,
    dif_pos h]
  rfl

end Blocks

section Main

open GroundTheory.Heights₂.Heights.FieldNumbers

variable {K K' : Type} [Fintype K] [DecidableEq K] [Fintype K'] [DecidableEq K'] {j : K ↪ K'}
  {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}
  {P' : Ideal (MRing ι' O)} {d : ℕ} {c : K → ℕ} {f : MRing (fun k => ι' (j k)) O}
  {W : Ideal (MRing (fun k => ι' (j k)) O)}

theorem relDim_special (hϖ : Irreducible ϖ) {K₁ : Type} [Fintype K₁] [DecidableEq K₁]
    {ι : K₁ → Type} [∀ k, Fintype (ι k)] {P W : Ideal (MRing ι O)} (hP : IsModelOver P d)
    {c : K₁ → ℕ} {f : MRing ι O} (hf : IsMultiHomog f c) (hfP : f ∉ P)
    (hW : divCycle P f W ≠ 0) (hϖW : (C ϖ : MRing ι O) ∈ W) : relDim (specialIdeal W) = (d : ℕ) := by
  apply relDim_eq_of_dim
  rw [SpecialQuotDim.proof O ϖ hϖ K₁ ι W hϖW, ComponentDim.proof O ϖ hϖ K₁ ι P d hP c f hf hfP W hW hϖW]

theorem fibre_minimal (hϖ : Irreducible ϖ) (hP' : IsModelOver P' d)
    (hP : IsModelOver (P'.comap (rr j ι' O)) d) (hf : IsMultiHomog f c)
    (hfP : f ∉ P'.comap (rr j ι' O)) (hϖW : (C ϖ : MRing (fun k => ι' (j k)) O) ∈ W)
    (hW : divCycle (P'.comap (rr j ι' O)) f W ≠ 0) {W' : Ideal (MRing ι' O)}
    (hmp : IsMultiProjPrime W') (hle : P' ≤ W') (hc : W'.comap (rr j ι' O) = W) :
    W' ∈ (P' ⊔ Ideal.span {rr j ι' O f}).minimalPrimes := by
  obtain ⟨hmin, hrel⟩ := divCycle_supp hW
  obtain ⟨τ, hτ⟩ := (proj_rr j ι' O).hom
  have := hmp.isPrime
  have hfW : f ∈ W := hmin.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))
  have hJ : P' ⊔ Ideal.span {rr j ι' O f} ≤ W' :=
    sup_le hle ((Ideal.span_singleton_le_iff_mem _).mpr (by rw [← hc] at hfW; exact hfW))
  obtain ⟨Q, hQ, hQW⟩ := Ideal.exists_minimalPrimes_le hJ
  have hQp : Q.IsPrime := hQ.1.1
  by_cases hne : Q = W'
  · exact hne ▸ hQ
  exfalso
  have hQrel : IsRelevant Q := fun k => (hmp.relevant k).imp fun i hi h => hi (hQW h)
  have h1 : W ≤ Q.comap (rr j ι' O) := by
    refine hmin.2 ⟨Ideal.comap_isPrime _ _, sup_le (Ideal.comap_mono (le_sup_left.trans hQ.1.2))
      ((Ideal.span_singleton_le_iff_mem _).mpr ?_)⟩ (hc ▸ Ideal.comap_mono hQW)
    exact hQ.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))
  have hϖQ : (C ϖ : MRing ι' O) ∈ Q := (C_mem_comap j ι' Q).mp (h1 hϖW)
  have d1 := ComponentDim.proof O ϖ hϖ K' ι' P' d hP' _ _ (hτ f c hf) hfP Q
    (divCycle_ne_zero hQ hQrel) hϖQ
  have d2 := DimStrictDrop.proof _ Q W' (lt_of_le_of_ne hQW hne)
  rw [d1] at d2
  have d3 := withBot_lt_natCast_of_add_one_le _ _ d2
  rw [← SpecialQuotDim.proof O ϖ hϖ K' ι' W' (hQW hϖQ)] at d3
  have d4 := ContractRelDimLe.proof _ K K' j ι' _ (special_mp hϖ hmp (hQW hϖQ))
  rw [contract_special j ι' hϖ (hQW hϖQ), hc, relDim_special hϖ hP hf hfP hW hϖW] at d4
  exact lt_irrefl _ (lt_of_le_of_lt d4 (relDim_lt_of_dim_lt _ _ d3))

open Classical in
theorem fibre_degree (hϖ : Irreducible ϖ) (hP' : IsModelOver P' d)
    (hP : IsModelOver (P'.comap (rr j ι' O)) d) (hf : IsMultiHomog f c)
    (hfP : f ∉ P'.comap (rr j ι' O)) (hϖW : (C ϖ : MRing (fun k => ι' (j k)) O) ∈ W)
    (hW : divCycle (P'.comap (rr j ι' O)) f W ≠ 0) {L : Type} [Field L] (φ : MRing ι' O →+* L)
    (hφ : ∀ F b, IsMultiHomog F b → (φ F = 0 ↔ F ∈ P')) :
    (∑ᶠ W' : Ideal (MRing ι' O), if W'.comap (rr j ι' O) = W then
        divCycle P' (rr j ι' O f) W' * (srd j W' : ℤ) else 0) =
      (((ffield (φ.comp (rr j ι' O))).relfinrank (ffield φ) : ℕ) : ℤ) *
        divCycle (P'.comap (rr j ι' O)) f W := by
  obtain ⟨hmin, hrel⟩ := divCycle_supp hW
  have hr := proj_rr j ι' O
  obtain ⟨τ, hτ⟩ := hr.hom
  obtain ⟨hWp, -, hPW, hWh⟩ := divCycle_ne_zero_facts hP.multiProj.multiHomog hf hW
  have hWmp : IsMultiProjPrime W := ⟨hWp, hWh, hrel⟩
  let 𝒲 : Set (Ideal (MRing ι' O)) :=
    {W' | IsMultiProjPrime W' ∧ P' ≤ W' ∧ W'.comap (rr j ι' O) = W}
  have hm : ∀ W' ∈ 𝒲, W' ∈ (P' ⊔ Ideal.span {rr j ι' O f}).minimalPrimes := fun W' h =>
    fibre_minimal hϖ hP' hP hf hfP hϖW hW h.1 h.2.1 h.2.2
  have S : Setup φ P' 𝒲 := ⟨hP'.multiProj, hφ,
    (Ideal.finite_minimalPrimes_of_isNoetherianRing _ _).subset hm, fun _ h => h.1, fun _ h => h.2.1⟩
  let _ : Fintype 𝒲 := S.fin.fintype
  have hfib : ∀ W' ∈ 𝒲, W'.comap (rr j ι' O) ∈ ({W} : Set _) := fun _ h => h.2.2
  have hy : ∀ y, IsMultiProjPrime y → P' ≤ y → y.comap (rr j ι' O) ≤ W → y = P' ∨ y ∈ 𝒲 := by
    intro y hy hPy hyW
    by_cases h1 : y.comap (rr j ι' O) = W
    · exact Or.inr ⟨hy, hPy, h1⟩
    refine Or.inl (eq_of_comap_eq hP' hP hy hPy ?_)
    by_contra h2
    have := hy.isPrime
    have := hP.multiProj.isPrime
    have d1 := DimStrictDrop.proof _ _ W (lt_of_le_of_ne hyW h1)
    have d2 := DimStrictDrop.proof _ (P'.comap (rr j ι' O)) (y.comap (rr j ι' O))
      (lt_of_le_of_ne (Ideal.comap_mono hPy) (Ne.symm h2))
    rw [hP.dim, show d + 1 + Fintype.card K = (d + Fintype.card K) + 1 by omega] at d2
    have d3 := lt_of_two_drops d1 d2
    rw [ComponentDim.proof O ϖ hϖ K _ _ d hP c f hf hfP W hW hϖW] at d3
    exact lt_irrefl _ d3
  have hanti : ∀ W₁ ∈ 𝒲, ∀ W₂ ∈ 𝒲, W₁ ≤ W₂ → W₁ = W₂ := fun W₁ h₁ W₂ h₂ h =>
    le_antisymm h ((hm W₂ h₂).2 (hm W₁ h₁).1 h)
  obtain ⟨i, hi⟩ := powMonomial_not_mem hWp hrel c
  have hg := isMultiHomog_powMonomial (R := O) c i
  set g : MRing (fun k => ι' (j k)) O := powMonomial c i
  have S₀ := S.proj hr hWmp hPW
  have hg0 : φ (rr j ι' O g) ≠ 0 := S₀.ne (Set.mem_singleton W) hg hi
  have hf0 : φ (rr j ι' O f) ≠ 0 := fun h => hfP ((S₀.ker f c hf).mp h)
  have hrep : Rep (φ.comp (rr j ι' O)) {W} _ f g := ⟨⟨c, hf, hg⟩, hg0, fun _ h => h ▸ hi, rfl⟩
  obtain ⟨l1, l2, l3, l4⟩ := loc_facts S₀ hf hfP hmin hg hi hrep.mem
  have hϖ' : ∀ W' : 𝒲, (C ϖ : MRing ι' O) ∈ W'.1 := fun W' =>
    (C_mem_comap j ι' W'.1).mp (by rw [W'.2.2.2]; exact hϖW)
  have hsp : ∀ W' : 𝒲, (specialIdeal W'.1).IsPrime := fun W' =>
    (special_mp hϖ W'.2.1 (hϖ' W')).isPrime
  have hα' : ∀ W' : 𝒲, φ (rr j ι' O f) / φ (rr j ι' O g) ∈ loc φ {W'.1} := fun W' =>
    loc_anti (Set.singleton_subset_iff.mpr W'.2) (hrep.proj hr hfib).mem
  have key := S.local_sum hr hWmp hPW hfib hy hanti l3
    (fun W' => FractionRing (MRing ι' (IsLocalRing.ResidueField O) ⧸ specialIdeal W'.1))
    (fun W' => (qm (specialIdeal W'.1)).comp (MvPolynomial.map (IsLocalRing.residue O)))
    (fun W' F => (qm_eq_zero _ _).trans (mem_special hϖ (hϖ' W') F)) _ hrep.mem
    (div_ne_zero hf0 hg0) hα'
  have hterm : ∀ W' : 𝒲, Ring.ord (loc φ {W'.1}) ⟨_, hα' W'⟩ =
      ((divCycle P' (rr j ι' O f) W'.1).toNat : ℕ∞) := fun W' =>
    (loc_facts (S.single W'.2) (hτ f c hf) hfP (hm _ W'.2) (hτ g c hg)
      (fun h => hi (by rw [← W'.2.2.2]; exact h)) (hα' W')).2.2.2
  have key2 : ∑ W' : 𝒲, ((divCycle P' (rr j ι' O f) W'.1).toNat : ℕ∞) * (srd j W'.1 : ℕ∞) =
      (((ffield (φ.comp (rr j ι' O))).relfinrank (ffield φ) : ℕ) : ℕ∞) *
        ((divCycle (P'.comap (rr j ι' O)) f W).toNat : ℕ∞) := by
    rw [← l4, ← key]
    refine Finset.sum_congr rfl fun W' _ => ?_
    rw [← hterm W', ← relDeg_eq W'.1]
    rfl
  have key3 : ∑ W' : 𝒲, (divCycle P' (rr j ι' O f) W'.1).toNat * srd j W'.1 =
      (ffield (φ.comp (rr j ι' O))).relfinrank (ffield φ) *
        (divCycle (P'.comap (rr j ι' O)) f W).toNat := by
    apply Nat.cast_injective (R := ℕ∞)
    rw [Nat.cast_sum, Nat.cast_mul, ← key2]
    exact Finset.sum_congr rfl fun _ _ => Nat.cast_mul _ _
  have key4 := congrArg (Nat.cast : ℕ → ℤ) key3
  simp only [Nat.cast_sum, Nat.cast_mul, Int.toNat_of_nonneg (divCycle_nonneg _ _ _)] at key4
  rw [← key4, finsum_eq_sum_of_support_subset _ (s := 𝒲.toFinset),
    Finset.sum_set_coe 𝒲 (f := fun W' => divCycle P' (rr j ι' O f) W' * (srd j W' : ℤ))]
  · refine Finset.sum_congr rfl fun W' h => ?_
    rw [if_pos (Set.mem_toFinset.mp h).2.2]
  · intro W' h
    rw [Function.mem_support] at h
    rw [Set.coe_toFinset]
    split_ifs at h with h1
    · obtain ⟨a1, a2, a3, a4⟩ := divCycle_ne_zero_facts hP'.multiProj.multiHomog (hτ f c hf)
        (left_ne_zero_of_mul h)
      exact ⟨⟨a1, a4, a2⟩, a3, h1⟩
    · exact absurd rfl h

open Classical in
theorem fibre_num (hϖ : Irreducible ϖ) (hP' : IsModelOver P' d)
    (hP : IsModelOver (P'.comap (rr j ι' O)) d) (hf : IsMultiHomog f c)
    (hfP : f ∉ P'.comap (rr j ι' O)) (hϖW : (C ϖ : MRing (fun k => ι' (j k)) O) ∈ W)
    {L : Type} [Field L] (φ : MRing ι' O →+* L)
    (hφ : ∀ F b, IsMultiHomog F b → (φ F = 0 ↔ F ∈ P')) (a : Fin d → K → ℤ) :
    (∑ᶠ W' : Ideal (MRing ι' O), if W'.comap (rr j ι' O) = W then
        divCycle P' (rr j ι' O f) W' *
          vNum W' (fun i => GroundTheory.Heights₂.Heights.FieldNumbers.pullDeg j (a i)) else 0) =
      (((ffield (φ.comp (rr j ι' O))).relfinrank (ffield φ) : ℕ) : ℤ) *
        (divCycle (P'.comap (rr j ι' O)) f W * vNum W a) := by
  have hr := proj_rr j ι' O
  obtain ⟨τ, hτ⟩ := hr.hom
  have key : ∀ W' : Ideal (MRing ι' O), divCycle P' (rr j ι' O f) W' ≠ 0 →
      W'.comap (rr j ι' O) = W → IsMultiProjPrime W' ∧ P' ≤ W' ∧
      IsMultiProjPrime (specialIdeal W') ∧ relDim (specialIdeal W') = (d : ℕ) ∧
        contractPrime j (specialIdeal W') = specialIdeal W := by
    intro W' hW' hcomap
    obtain ⟨hWp, hWrel, hle, hWh⟩ := divCycle_ne_zero_facts hP'.multiProj.multiHomog (hτ f c hf) hW'
    have hϖ' : (C ϖ : MRing ι' O) ∈ W' := (C_mem_comap j ι' W').mp (by rw [hcomap]; exact hϖW)
    exact ⟨⟨hWp, hWh, hWrel⟩, hle, special_mp hϖ ⟨hWp, hWh, hWrel⟩ hϖ',
      relDim_special hϖ hP' (hτ f c hf) hfP hW' hϖ', by rw [contract_special j ι' hϖ hϖ', hcomap]⟩
  by_cases hW : divCycle (P'.comap (rr j ι' O)) f W ≠ 0
  · have hdimW := relDim_special hϖ hP hf hfP hW hϖW
    have hterm : ∀ W' : Ideal (MRing ι' O),
        (if W'.comap (rr j ι' O) = W then divCycle P' (rr j ι' O f) W' *
          vNum W' (fun i => GroundTheory.Heights₂.Heights.FieldNumbers.pullDeg j (a i)) else 0) =
        (if W'.comap (rr j ι' O) = W then
          divCycle P' (rr j ι' O f) W' * (srd j W' : ℤ) else 0) * vNum W a := by
      intro W'
      split_ifs with h1
      · by_cases h0 : divCycle P' (rr j ι' O f) W' = 0
        · simp [h0]
        obtain ⟨-, -, hmp, hrd, hcon⟩ := key W' h0 h1
        have hpf' := (GlobalTheory.CompanionTheory.FieldNumbers.projectionFormulaDegree (IsLocalRing.ResidueField O) K K' j ι'
          (specialIdeal W') hmp d hrd (by rw [hcon]; exact hdimW) a).2
        rw [mul_assoc]
        congr 1
        unfold vNum srd
        rw [dif_pos hmp.isPrime, hpf', hcon]
      · simp
    rw [finsum_congr hterm, ← finsum_mul, fibre_degree hϖ hP' hP hf hfP hϖW hW φ hφ, mul_assoc]
  · rw [not_not] at hW
    rw [hW, zero_mul, mul_zero]
    refine finsum_eq_zero_of_forall_eq_zero fun W' => ?_
    split_ifs with h1
    · by_cases h0 : divCycle P' (rr j ι' O f) W' = 0
      · rw [h0, zero_mul]
      obtain ⟨hmp', hle, hmp, hrd, hcon⟩ := key W' h0 h1
      obtain ⟨hWmin', -⟩ := divCycle_supp h0
      have hWmp := hr.comap W' hmp'
      have hPW : P'.comap (rr j ι' O) ≤ W'.comap (rr j ι' O) := Ideal.comap_mono hle
      have hxW : f ∈ W'.comap (rr j ι' O) :=
        hWmin'.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))
      rw [h1] at hWmp hPW hxW
      have := hWmp.isPrime
      have hJW : P'.comap (rr j ι' O) ⊔ Ideal.span {f} ≤ W :=
        sup_le hPW ((Ideal.span_singleton_le_iff_mem _).mpr hxW)
      have hnmin : W ∉ (P'.comap (rr j ι' O) ⊔ Ideal.span {f}).minimalPrimes :=
        fun hWmin => divCycle_ne_zero hWmin hWmp.relevant hW
      obtain ⟨Q, hQ, hQW⟩ := Ideal.exists_minimalPrimes_le hJW
      have hQp : Q.IsPrime := hQ.1.1
      have hQW' : Q < W := lt_of_le_of_ne hQW (fun h => hnmin (h ▸ hQ))
      have hPQ : P'.comap (rr j ι' O) < Q := lt_of_le_of_ne (le_sup_left.trans hQ.1.2) (fun h =>
        hfP (h ▸ hQ.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))))
      have := hP.multiProj.isPrime
      have hd1 := DimStrictDrop.proof _ Q W hQW'
      have hd2 := DimStrictDrop.proof _ _ Q hPQ
      rw [hP.dim, show d + 1 + Fintype.card K = (d + Fintype.card K) + 1 by omega] at hd2
      have hlt := lt_of_two_drops hd1 hd2
      have hltW : relDim (specialIdeal W) < ((d : ℕ) : WithBot (WithTop ℤ)) :=
        relDim_lt_of_dim_lt _ _ (by rw [SpecialQuotDim.proof O ϖ hϖ K _ W hϖW]; exact hlt)
      have hz := ProjectionFormulaContracted.full (IsLocalRing.ResidueField O) K K'
        j ι' (specialIdeal W') hmp d hrd (by rw [hcon]; exact hltW) a
      unfold vNum
      rw [hz, mul_zero]
    · rfl

open Classical in
theorem push (hϖ : Irreducible ϖ) (hP' : IsModelOver P' d)
    (hP : IsModelOver (P'.comap (rr j ι' O)) d) (hf : IsMultiHomog f c)
    (hfP : f ∉ P'.comap (rr j ι' O)) {L : Type} [Field L] (φ : MRing ι' O →+* L)
    (hφ : ∀ F b, IsMultiHomog F b → (φ F = 0 ↔ F ∈ P')) (a : Fin d → K → ℤ) :
    cycEval (fun W' => if (C ϖ : MRing ι' O) ∈ W' then
        vNum W' (fun i => GroundTheory.Heights₂.Heights.FieldNumbers.pullDeg j (a i)) else 0)
        (divCycle P' (rr j ι' O f)) =
      (((ffield (φ.comp (rr j ι' O))).relfinrank (ffield φ) : ℕ) : ℤ) *
        cycEval (fun W => if (C ϖ : MRing (fun k => ι' (j k)) O) ∈ W then vNum W a else 0)
          (divCycle (P'.comap (rr j ι' O)) f) := by
  have hZ : (Function.support (divCycle P' (rr j ι' O f))).Finite :=
    DivCycleFiniteSupport.proof O K' ι' _ _
  set δ : ℤ := (((ffield (φ.comp (rr j ι' O))).relfinrank (ffield φ) : ℕ) : ℤ) with hδ
  set g : Ideal (MRing ι' O) → ℤ := fun W' =>
    divCycle P' (rr j ι' O f) W' * (if (C ϖ : MRing ι' O) ∈ W' then
      vNum W' (fun i => GroundTheory.Heights₂.Heights.FieldNumbers.pullDeg j (a i)) else 0) with hg_def
  have hg : Function.support g ⊆ hZ.toFinset := fun W' hW' =>
    hZ.mem_toFinset.mpr (Function.support_mul_subset_left _ _ hW')
  have key : ∀ W : Ideal (MRing (fun k => ι' (j k)) O),
      (∑ W' ∈ hZ.toFinset with W'.comap (rr j ι' O) = W, g W') =
        δ * (divCycle (P'.comap (rr j ι' O)) f W *
          (if (C ϖ : MRing (fun k => ι' (j k)) O) ∈ W then vNum W a else 0)) := by
    intro W
    by_cases hW : (C ϖ : MRing (fun k => ι' (j k)) O) ∈ W
    · rw [if_pos hW, hδ, ← fibre_num hϖ hP' hP hf hfP hW φ hφ a,
        finsum_eq_sum_of_support_subset _ (s := hZ.toFinset), Finset.sum_filter]
      · refine Finset.sum_congr rfl fun W' _ => ?_
        by_cases h1 : W'.comap (rr j ι' O) = W
        · rw [if_pos h1, if_pos h1, hg_def]
          dsimp only
          rw [if_pos ((C_mem_comap j ι' W').mp (by rw [h1]; exact hW))]
        · rw [if_neg h1, if_neg h1]
      · intro W' hW'
        refine hZ.mem_toFinset.mpr ?_
        rw [Function.mem_support] at hW' ⊢
        intro h0
        apply hW'
        simp [h0]
    · rw [if_neg hW, mul_zero, mul_zero]
      refine Finset.sum_eq_zero fun W' hW' => ?_
      have h1 := (Finset.mem_filter.mp hW').2
      rw [hg_def]
      dsimp only
      rw [if_neg (fun h => hW (h1 ▸ (C_mem_comap j ι' W').mpr h)), mul_zero]
  unfold cycEval
  rw [mul_finsum]
  calc (∑ᶠ W', g W') = ∑ W' ∈ hZ.toFinset, g W' := finsum_eq_sum_of_support_subset g hg
    _ = ∑ᶠ W, ∑ W' ∈ hZ.toFinset with W'.comap (rr j ι' O) = W, g W' :=
        (finsum_sum_filter _ _ _).symm
    _ = _ := finsum_congr key

end Main

theorem pullDeg_eq {K K' : Type} (a : K → ℤ) :
    pullDeg (K' := K') a =
      GroundTheory.Heights₂.Heights.FieldNumbers.pullDeg (Function.Embedding.inl : K ↪ K ⊕ K') a := by
  funext o
  cases o with
  | inl k => exact ((Function.Embedding.inl : K ↪ K ⊕ K').injective.extend_apply a 0 k).symm
  | inr k =>
    rw [GroundTheory.Heights₂.Heights.FieldNumbers.pullDeg, Function.extend_apply' _ _ _ (by simp)]
    rfl

theorem vNumL_map {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {K K₁ : Type}
    [DecidableEq K₁] {ι : K₁ → Type} (W : Ideal (MRing ι O)) (l : List (K → ℤ))
    (t : (K → ℤ) → K₁ → ℤ) : vNumL W (l.map t) = vNum W (fun i => t (l.get i)) := by
  unfold vNumL vNum intNum mixedDiff
  rw [List.ofFn_get, show (fun i => t (l.get i)) = t ∘ l.get from rfl, ← List.map_ofFn,
    List.ofFn_get]

theorem form_mem_point {O : Type} [CommRing O] {L : Type} [Field L] [Algebra O L] {K : Type}
    [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → L)
    (F : MRing ι O) (b : K → ℕ) (hF : IsMultiHomog F b) : aeval y F = 0 ↔ F ∈ pointIdeal O y :=
  ⟨GenericProjClosureDivisor.mem_of_homog hF, GenericProjClosureDivisor.aeval_eq_zero_of_mem⟩

theorem adjoin_rank {L : Type} [Field L] {A B : Subfield L} (h : A ≤ B) :
    A.relfinrank B = Module.finrank A (IntermediateField.adjoin A (B : Set L)) := by
  rw [Subfield.relfinrank_eq_finrank_of_le h]
  have e : IntermediateField.adjoin A (B : Set L) = Subfield.extendScalars h :=
    le_antisymm (IntermediateField.adjoin_le_iff.mpr fun _ hx => hx)
      (fun _ hx => IntermediateField.subset_adjoin _ _ hx)
  rw [e]

end

end PositivityTheory.Xgn.ModelPushforward

theorem PositivityTheory.Xgn.model_pushforward_fibre_degree : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (ϖ : O), Irreducible ϖ → ∀ d : ℕ, IsModelOver (pointIdeal O x) d → ∀ (Ω₁ : Type) [Field Ω₁] [Algebra O Ω₁] [Algebra Ω Ω₁] [IsScalarTower O Ω Ω₁] (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω₁), IsModelOver (pointIdeal O (bcCoord x z)) d → ∀ (c : K → ℕ) (f : MRing ι O), IsMultiHomog f c → f ∉ (pointIdeal O x) → ∀ l : List (K → ℤ), l.length = d → (open Classical in cycEval (fun W => if (C ϖ : MRing (Sum.elim ι ι') O) ∈ W then vNumL W (l.map (pullDeg (K' := K'))) else 0) (divCycle (pointIdeal O (bcCoord x z)) (rename (liftVar ι') f))) = (modelDeg O x z : ℤ) * (open Classical in cycEval (fun W => if (C ϖ : MRing ι O) ∈ W then vNumL W l else 0) (divCycle (pointIdeal O x) f)) := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x ϖ hϖ d hP Ω₁ _ _ _ _ K' _ _ ι' _ z hP' c f hf hfP l hl
  subst hl
  let j : K ↪ K ⊕ K' := Function.Embedding.inl
  let r : MRing ι O →+* MRing (Sum.elim ι ι') O := PositivityTheory.Xgn.ModelPushforward.rr j (Sum.elim ι ι') O
  have hr : PositivityTheory.Xgn.ModelPushforward.Proj r := PositivityTheory.Xgn.ModelPushforward.proj_rr j (Sum.elim ι ι') O
  let φ : MRing (Sum.elim ι ι') O →+* Ω₁ := (aeval (bcCoord x z) : _ →ₐ[O] Ω₁).toRingHom
  have hφ : ∀ F b, IsMultiHomog F b → (φ F = 0 ↔ F ∈ pointIdeal O (bcCoord x z)) :=
    PositivityTheory.Xgn.ModelPushforward.form_mem_point _
  have hcomp : φ.comp r = (aeval (fun p => algebraMap Ω Ω₁ (x p)) : MRing ι O →ₐ[O] Ω₁).toRingHom :=
    RingHom.ext fun F => aeval_rename (k := liftVar ι') (g := bcCoord x z) (p := F)
  have hval : ∀ F, φ (r F) = algebraMap Ω Ω₁ (aeval x F) := fun F =>
    (RingHom.congr_fun hcomp F).trans (MvPolynomial.aeval_algebraMap_apply Ω₁ x F)
  have hcm : (pointIdeal O (bcCoord x z)).comap r = pointIdeal O x := by
    obtain ⟨τ, hτ⟩ := hr.hom
    have key : ∀ F b, IsMultiHomog F b →
        (F ∈ (pointIdeal O (bcCoord x z)).comap r ↔ F ∈ pointIdeal O x) := fun F b hF => by
      rw [Ideal.mem_comap, ← hφ _ _ (hτ F b hF), hval, map_eq_zero,
        PositivityTheory.Xgn.ModelPushforward.form_mem_point x F b hF]
    exact le_antisymm
      (PositivityTheory.Xgn.ModelPushforward.le_of_forms (hr.comap _ hP'.multiProj).multiHomog
        fun F b hF h => (key F b hF).mp h)
      (PositivityTheory.Xgn.ModelPushforward.le_of_forms hP.multiProj.multiHomog fun F b hF h => (key F b hF).mpr h)
  have hnz' : ∀ k, ∃ i, bcCoord x z ⟨k, i⟩ ≠ 0 := fun k =>
    (hP'.multiProj.relevant k).imp fun i hi h => hi
      ((PositivityTheory.Xgn.ModelPushforward.form_mem_point _ _ _ (PositivityTheory.Xgn.ModelPushforward.homX _)).mp
        ((aeval_X _ _).trans h))
  have hdeg : (PositivityTheory.Xgn.ModelPushforward.ffield (φ.comp r)).relfinrank (PositivityTheory.Xgn.ModelPushforward.ffield φ) =
      modelDeg O x z := by
    have hle := hr.ffield_le (φ := φ)
    have e1 : PositivityTheory.Xgn.ModelPushforward.ffield (φ.comp r) = fnField O (fun p => algebraMap Ω Ω₁ (x p)) := by
      rw [hcomp]
      exact PositivityTheory.Xgn.ModelPushforward.ffield_aeval _ (fun k => hnz' (Sum.inl k))
    have e2 : PositivityTheory.Xgn.ModelPushforward.ffield φ = fnField O (bcCoord x z) :=
      PositivityTheory.Xgn.ModelPushforward.ffield_aeval _ hnz'
    rw [e1, e2] at hle ⊢
    exact PositivityTheory.Xgn.ModelPushforward.adjoin_rank hle
  have hP₀ : IsModelOver ((pointIdeal O (bcCoord x z)).comap r) l.length := hcm ▸ hP
  have hf₀ : f ∉ (pointIdeal O (bcCoord x z)).comap r := hcm ▸ hfP
  have main := PositivityTheory.Xgn.ModelPushforward.push (j := j) (ι' := Sum.elim ι ι') (f := f) (c := c) hϖ hP' hP₀
    hf hf₀ φ hφ l.get
  rw [← hdeg, ← hcm]
  simp only [PositivityTheory.Xgn.ModelPushforward.vNumL_map, PositivityTheory.Xgn.ModelPushforward.pullDeg_eq]
  exact main
