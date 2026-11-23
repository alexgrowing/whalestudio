import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingStalkGeneric
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GlobalTheory.SS.Ord

section Algebra

theorem multilinear_mem {S P Q I : Type} [CommRing S] [AddCommGroup P] [Module S P] [AddCommGroup Q]
    [Module S Q] [Fintype I] [DecidableEq I] (f : MultilinearMap S (fun _ : I => P) Q) (G : Set P)
    (N : Submodule S Q) (h : ∀ v : I → P, (∀ i, v i ∈ G) → f v ∈ N) (v : I → P)
    (hv : ∀ i, v i ∈ Submodule.span S G) : f v ∈ N := by
  have key : ∀ s : Finset I, ∀ v : I → P, (∀ i, v i ∈ Submodule.span S G) → (∀ i, i ∉ s → v i ∈ G) → f v ∈ N := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact fun v _ h' => h v fun i => h' i (by simp)
    | insert a s ha ih =>
      intro v h1 h2
      have : Submodule.span S G ≤ N.comap (f.toLinearMap v a) := by
        refine Submodule.span_le.2 fun g hg => ?_
        refine ih (Function.update v a g) (fun i => ?_) (fun i hi => ?_)
        · by_cases e : i = a
          · subst e; simpa using Submodule.subset_span hg
          · simpa [Function.update_of_ne e] using h1 i
        · by_cases e : i = a
          · subst e; simpa using hg
          · rw [Function.update_of_ne e]; exact h2 i (by simp [e, hi])
      simpa using this (h1 a)
  exact key Finset.univ v hv (by simp)

theorem det_mem {B S L I : Type} [CommRing B] [CommRing S] [CommRing L] [Fintype I] [DecidableEq I]
    (ρ : B →+* S) (φ : S →+* L) (δ : I → L →+ L) (hδ : ∀ i a b, δ i (a * b) = a * δ i b + b * δ i a)
    (hloc : ∀ x : S, ∃ (b c : B), IsUnit (ρ c) ∧ x * ρ c = ρ b)
    (N : AddSubgroup L) (hN : ∀ s : S, ∀ x ∈ N, φ s * x ∈ N)
    (h : ∀ t : I → B, (Matrix.of fun i j => δ i (φ (ρ (t j)))).det ∈ N) (t : I → S) :
    (Matrix.of fun i j => δ i (φ (t j))).det ∈ N := by
  letI := φ.toAlgebra
  let N' : Submodule S L := { N with smul_mem' := fun s x hx => hN s x hx }
  let f : MultilinearMap S (fun _ : I => I → L) L :=
    (Matrix.detRowAlternating (n := I) (R := L)).toMultilinearMap.restrictScalars S
  have hf : ∀ v : I → I → L, f v = (Matrix.of fun i j => v j i).det := fun v =>
    (Matrix.det_transpose (Matrix.of v)).symm
  let col : S → I → L := fun x i => δ i (φ x)
  have := multilinear_mem f (Set.range (col ∘ ρ)) N' (fun v hv => by
    choose t ht using hv
    have := h t
    rw [hf]
    simp only [← ht]
    exact this) (fun j => col (t j)) (fun j => by
      obtain ⟨b, c, ⟨u, hu⟩, e⟩ := hloc (t j)
      have : col (t j) = (u⁻¹ : Sˣ).val • (col (ρ b) - t j • col (ρ c)) := by
        funext i
        have e1 : φ (u⁻¹ : Sˣ).val * φ (ρ c) = 1 := by rw [← map_mul, ← hu]; simp
        show δ i (φ (t j)) = φ (u⁻¹ : Sˣ).val * (δ i (φ (ρ b)) - φ (t j) * δ i (φ (ρ c)))
        rw [← e, map_mul, hδ]
        linear_combination (-δ i (φ (t j))) * e1
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.subset_span ⟨b, rfl⟩)
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩))))
  rw [hf] at this
  exact this

theorem exists_pow_mul_mem {R B L I : Type} [CommRing R] [CommRing B] [CommRing L] [Fintype I]
    (c : R →+* B) (hc : c.FiniteType) (φ : B →+* L) (p : B) (δ : I → L →+ L)
    (hδ : ∀ i a b, δ i (a * b) = a * δ i b + b * δ i a) (h0 : ∀ i r, δ i (φ (c r)) = 0)
    (hloc : ∀ x : L, ∃ (k : ℕ) (b : B), φ b = φ p ^ k * x) :
    ∃ N : ℕ, ∀ i b, ∃ s, φ s = φ p ^ N * δ i (φ b) := by
  letI := c.toAlgebra
  obtain ⟨T, hT⟩ := (show Algebra.FiniteType R B from hc).1
  choose k a hk using hloc
  refine ⟨(Finset.univ ×ˢ T).sup fun q : I × B => k (δ q.1 (φ q.2)), fun i b => ?_⟩
  have hb : b ∈ Algebra.adjoin R (T : Set B) := hT ▸ trivial
  induction hb using Algebra.adjoin_induction with
  | mem x hx =>
    have : k (δ i (φ x)) ≤ (Finset.univ ×ˢ T).sup fun q : I × B => k (δ q.1 (φ q.2)) :=
      Finset.le_sup (f := fun q : I × B => k (δ q.1 (φ q.2))) (b := (i, x)) (by simpa using hx)
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le this
    exact ⟨p ^ m * a (δ i (φ x)), by rw [hm, map_mul, hk, map_pow]; ring⟩
  | algebraMap r => exact ⟨0, by rw [show algebraMap R B r = c r from rfl, h0]; simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs⟩ := hx
    obtain ⟨s', hs'⟩ := hy
    exact ⟨s + s', by simp only [map_add, hs, hs']; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨s, hs⟩ := hx
    obtain ⟨s', hs'⟩ := hy
    exact ⟨x * s' + y * s, by simp only [map_add, map_mul, hδ, hs, hs']; ring⟩

theorem exists_prime_iInf {B : Type} [CommRing B] {p : B} (hp : Prime p) (h0 : p ∈ nonZeroDivisors B) :
    ∃ J : Ideal B, J.IsPrime ∧ p ∉ J ∧ ∀ b, (∀ n : ℕ, p ^ n ∣ b) → b ∈ J := by
  classical
  have hcan : ∀ (n : ℕ) (a b : B), p ^ n * a = p ^ n * b → a = b := fun n a b h =>
    (mul_cancel_left_mem_nonZeroDivisors (pow_mem h0 n)).1 h
  have hmem : ∀ b, b ∈ (⨅ n : ℕ, Ideal.span {p ^ n}) ↔ ∀ n : ℕ, p ^ n ∣ b := fun b => by
    simp [Ideal.mem_iInf, Ideal.mem_span_singleton]
  have hnot : p ∉ (⨅ n : ℕ, Ideal.span {p ^ n}) := fun h => by
    obtain ⟨c, hc⟩ := (hmem p).1 h 2
    exact hp.not_dvd_one ⟨c, hcan 1 _ _ (by linear_combination hc)⟩
  have hdec : ∀ b, b ∉ (⨅ n : ℕ, Ideal.span {p ^ n}) → ∃ (n : ℕ) (a : B), b = p ^ n * a ∧ ¬ p ∣ a := by
    intro b hb
    rw [hmem, not_forall] at hb
    have h1 : Nat.find hb ≠ 0 := fun e => by simpa [e] using Nat.find_spec hb
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero h1
    obtain ⟨a, ha⟩ := not_not.1 (Nat.find_min hb (m := m) (by omega))
    refine ⟨m, a, ha, fun ⟨e, he⟩ => Nat.find_spec hb ⟨e, ?_⟩⟩
    rw [hm, ha, he, pow_succ, _root_.mul_assoc]
  refine ⟨⨅ n : ℕ, Ideal.span {p ^ n}, ⟨fun e => hnot (e ▸ trivial), fun {x y} hxy => ?_⟩, hnot,
    fun b hb => (hmem b).2 hb⟩
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨m, a, ha, ha'⟩ := hdec x hcon.1
  obtain ⟨n, b, hb, hb'⟩ := hdec y hcon.2
  obtain ⟨c, hc⟩ := (hmem _).1 hxy (m + n + 1)
  have : a * b = p * c := hcan (m + n) _ _ (by rw [ha, hb] at hc; linear_combination hc)
  exact (hp.dvd_or_dvd ⟨c, this⟩).elim ha' hb'

end Algebra

section Basic
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A : Over (Sp K)}

abbrev rs (X : Scheme.{0}) {U V : X.Opens} (h : V ≤ U) : Γ(X, U) →+* Γ(X, V) :=
  (X.presheaf.map (homOfLE h).op).hom

def cst (M : Model R A) (U : M.Y.left.Opens) : R →+* Γ(M.Y.left, U) :=
  (M.Y.hom.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem j_cst (M : Model R A) (U : M.Y.left.Opens) (r : R) :
    (M.j.app U).hom (cst M U r) = cstK A _ (algebraMap R K r) := by
  have e := congrArg (fun q => q.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R K)))
  have h1 : M.Y.hom.appLE ⊤ U le_top ≫ M.j.app U = (M.j ≫ M.Y.hom).appLE ⊤ (M.j ⁻¹ᵁ U) le_top := by
    rw [Scheme.Hom.app_eq_appLE]; exact Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
  have h2 : (spMap (algebraMap R K)).appTop ≫ A.hom.appLE ⊤ (M.j ⁻¹ᵁ U) le_top
      = (A.hom ≫ spMap (algebraMap R K)).appLE ⊤ (M.j ⁻¹ᵁ U) le_top := by
    exact (Scheme.Hom.comp_appLE A.hom (spMap (algebraMap R K)) ⊤ _ _).symm
  have h3 : M.Y.hom.appLE ⊤ U le_top ≫ M.j.app U = (spMap (algebraMap R K)).appTop ≫ A.hom.appLE ⊤ (M.j ⁻¹ᵁ U) le_top := by
    rw [h1, h2]; simp only [M.j_hom]
  have h4 := congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) h3
  exact h4.trans (congrArg (A.hom.appLE ⊤ (M.j ⁻¹ᵁ U) le_top).hom e.symm)

theorem not_isUnit_cst [IsLocalRing R] (M : Model R A) (U : M.Y.left.Opens) (h : ((U : Set M.Y.left) ∩ M.sp).Nonempty)
    {π : R} (hπ : π ∈ IsLocalRing.maximalIdeal R) : ¬ IsUnit (cst M U π) := by
  intro hu
  obtain ⟨y, hy, hs⟩ := h
  have h1 : M.Y.left.basicOpen (cst M U π) = U := M.Y.left.basicOpen_of_isUnit hu
  have h2 : M.Y.left.basicOpen (cst M U π) = U ⊓ M.Y.hom ⁻¹ᵁ (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv π) :=
    Scheme.basicOpen_appLE M.Y.hom U ⊤ le_top ((Scheme.ΓSpecIso (CommRingCat.of R)).inv π)
  rw [h1, basicOpen_eq_of_affine (R := CommRingCat.of R) π] at h2
  have h4 := (h2.le hy).2
  have h6 : M.Y.hom y = IsLocalRing.closedPoint R := hs
  have h7 : π ∉ PrimeSpectrum.asIdeal (M.Y.hom y) := h4
  rw [h6] at h7
  exact h7 hπ

theorem j_app_injective [IsDomain R] [IsFractionRing R K] (M : Model R A) (U : M.Y.left.Opens) :
    Function.Injective (M.j.app U).hom := by
  have := M.smooth
  have : IsDominant (spMap (algebraMap R K)) :=
    ⟨PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _ |>.2 (by
      exact ((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R K)).le.trans bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (spMap (algebraMap R K))
  have : IsSchemeTheoreticallyDominant (pullback.fst M.Y.hom (spMap (algebraMap R K))) :=
    IsSchemeTheoreticallyDominant.of_isPullback (IsPullback.of_hasPullback M.Y.hom (spMap (algebraMap R K))).flip
  have : IsIso M.e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map M.e.inv))
  have : IsSchemeTheoreticallyDominant M.j := by unfold Model.j; infer_instance
  have : QuasiCompact M.j := by unfold Model.j; infer_instance
  exact M.j.app_injective U

theorem hasOrd_unique [IsDomain R] [IsLocalRing R] [IsFractionRing R K] {I : Type} [Fintype I] [DecidableEq I]
    (M : Model R A) (D : I → VF A) {π : R} (hπ : π ∈ IsLocalRing.maximalIdeal R) (h0 : π ≠ 0) {n m : ℤ}
    (hn : HasOrd M D π n) (hm : HasOrd M D π m) : n = m := by
  have key : ∀ {n m : ℤ}, HasOrd M D π n → HasOrd M D π m → ¬ n < m := by
    intro n m hn hm hlt
    obtain ⟨U, t, s, hU, hs, e⟩ := hn.2
    obtain ⟨s', e'⟩ := hm.1 U t
    obtain ⟨k, hk⟩ : ∃ k : ℕ, m = n + (k + 1 : ℕ) := ⟨(m - n - 1).toNat, by omega⟩
    have hp : algebraMap R K π ≠ 0 := by simpa using h0
    have hu : IsUnit (cstK A (M.j ⁻¹ᵁ U) (algebraMap R K π ^ n)) := (IsUnit.mk0 _ (zpow_ne_zero n hp)).map _
    rw [e, hk, zpow_add₀ hp, map_mul, _root_.mul_assoc, zpow_natCast, ← map_pow, ← j_cst, ← map_mul] at e'
    have := j_app_injective M U (hu.mul_left_cancel e')
    rw [this, pow_succ, map_mul] at hs
    exact not_isUnit_cst M U hU hπ (isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left hs))
  have := key hn hm
  have := key hm hn
  omega

theorem rs_rs (X : Scheme.{0}) {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (a : Γ(X, U)) :
    rs X h' (rs X h a) = rs X (h'.trans h) a := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl

theorem rs_cst (M : Model R A) {U V : M.Y.left.Opens} (h : V ≤ U) (r : R) :
    rs _ h (cst M U r) = cst M V r :=
  congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) (M.Y.hom.appLE_map le_top (homOfLE h).op)

theorem rs_cstK {U V : A.left.Opens} (h : V ≤ U) (c : K) : rs _ h (cstK A U c) = cstK A V c :=
  congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c)) (A.hom.appLE_map le_top (homOfLE h).op)

theorem rs_j (M : Model R A) {U V : M.Y.left.Opens} (h : V ≤ U) (b : Γ(M.Y.left, U)) :
    rs _ (M.j.preimage_mono h) ((M.j.app U).hom b) = (M.j.app V).hom (rs _ h b) :=
  (congrArg (fun q => q.hom b) (M.j.naturality (homOfLE h).op)).symm

theorem rs_jac {I : Type} [Fintype I] [DecidableEq I] (D : I → VF A) {U V : A.left.Opens} (h : V ≤ U)
    (t : I → Γ(A.left, U)) : rs _ h (jac D U t) = jac D V fun i => rs _ h (t i) := by
  rw [jac, jac, RingHom.map_det]
  congr 1
  ext i j
  exact ((D i).res U V h (t j)).symm

theorem isPullback_j (M : Model R A) : IsPullback M.j A.hom M.Y.hom (spMap (algebraMap R K)) := by
  have : IsIso M.e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map M.e.inv))
  refine IsPullback.of_iso_pullback ⟨M.j_hom⟩ (asIso M.e.inv.left) rfl ?_
  exact Over.w M.e.inv

theorem exists_j_eq_of_local [IsDomain R] [IsFractionRing R K] (M : Model R A) (U : M.Y.left.Opens)
    (f : Γ(A.left, M.j ⁻¹ᵁ U))
    (h : ∀ x ∈ U, ∃ (W : M.Y.left.Opens) (hW : W ≤ U), x ∈ W ∧
      ∃ s, (M.j.app W).hom s = rs _ (M.j.preimage_mono hW) f) : ∃ s, (M.j.app U).hom s = f := by
  choose W hW hx s hs using h
  have hc : U ≤ ⨆ x : U, W x.1 x.2 := fun x h => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, h⟩, hx x h⟩
  obtain ⟨g, hg, -⟩ := M.Y.left.sheaf.existsUnique_gluing' (fun x : U => W x.1 x.2) U
    (fun x => homOfLE (hW x.1 x.2)) hc (fun x => s x.1 x.2) (fun x y => by
      apply j_app_injective M
      refine (rs_j M inf_le_left _).symm.trans (Eq.trans ?_ (rs_j M inf_le_right _))
      rw [hs, hs, rs_rs, rs_rs])
  refine ⟨g, A.left.sheaf.eq_of_locally_eq' (fun x : U => M.j ⁻¹ᵁ W x.1 x.2) (M.j ⁻¹ᵁ U)
    (fun x => homOfLE (M.j.preimage_mono (hW x.1 x.2)))
    (fun y h => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨M.j y, h⟩, hx _ h⟩) _ _ fun x => ?_⟩
  refine (rs_j M (hW x.1 x.2) g).trans (Eq.trans ?_ (hs x.1 x.2))
  exact congrArg _ (hg x)

end Basic

section Dvr
variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {K : Type} [Field K] [Algebra R K]
  [IsFractionRing R K] {A : Over (Sp K)} {π : R}

theorem isOpenImmersion_j (M : Model R A) : IsOpenImmersion M.j :=
  DvrModel.isOpenImmersion_generic (isPullback_j M)

omit [IsFractionRing R K] in

theorem mem_basicOpen_cst (hπ : Irreducible π) (M : Model R A) (U : M.Y.left.Opens) (x : M.Y.left) :
    x ∈ M.Y.left.basicOpen (cst M U π) ↔ x ∈ U ∧ x ∉ M.sp := by
  rw [← rs_cst M (le_top : U ≤ ⊤)]
  refine (SetLike.ext_iff.1 (M.Y.left.basicOpen_res (cst M ⊤ π) (homOfLE (le_top : U ≤ ⊤)).op) x).trans ?_
  refine and_congr_right fun _ => ?_
  have e : cst M ⊤ π = M.Y.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv π) :=
    congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv π)) (M.Y.hom.app_eq_appLE (U := ⊤)).symm
  rw [e]
  exact not_iff_not.1 (by rw [not_not]; exact DvrModel.notMem_basicOpen_iff M.Y.hom hπ x)

theorem mem_range_j (M : Model R A) (x : M.Y.left) : x ∈ Set.range M.j ↔ x ∉ M.sp := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have := isOpenImmersion_j M
  refine (SetLike.ext_iff.1 (DvrModel.opensRange_generic hπ (isPullback_j M)) x).trans ?_
  exact not_iff_not.1 (by rw [not_not]; exact DvrModel.notMem_basicOpen_iff M.Y.hom hπ x)

theorem j_app_surjective (M : Model R A) {U : M.Y.left.Opens} (h : ∀ x ∈ U, x ∉ M.sp) :
    Function.Surjective (M.j.app U).hom := by
  have := isOpenImmersion_j M
  have := M.j.isIso_app U (fun x hx => (mem_range_j M x).2 (h x hx))
  exact (ConcreteCategory.bijective_of_isIso (M.j.app U)).2

theorem isUnit_j_cst (hπ : Irreducible π) (M : Model R A) (U : M.Y.left.Opens) :
    IsUnit ((M.j.app U).hom (cst M U π)) := by
  rw [j_cst]
  exact (IsUnit.mk0 _ (by simpa using hπ.ne_zero)).map _

theorem cst_mem_nonZeroDivisors (hπ : Irreducible π) (M : Model R A) (U : M.Y.left.Opens) :
    cst M U π ∈ nonZeroDivisors Γ(M.Y.left, U) := by
  refine mem_nonZeroDivisors_iff_left.2 fun z hz => j_app_injective M U ?_
  have := congrArg (M.j.app U).hom hz
  rw [map_mul, map_zero] at this
  rw [map_zero]
  exact (isUnit_j_cst hπ M U).mul_right_eq_zero.1 this

theorem exists_pow_mul_eq (hπ : Irreducible π) (M : Model R A) {U : M.Y.left.Opens} (hU : IsAffineOpen U)
    (f : Γ(A.left, M.j ⁻¹ᵁ U)) :
    ∃ (k : ℕ) (b : Γ(M.Y.left, U)), (M.j.app U).hom b = (M.j.app U).hom (cst M U π) ^ k * f := by
  have hW := M.Y.left.basicOpen_le (cst M U π)
  have hl := hU.isLocalization_basicOpen (cst M U π)
  obtain ⟨x, hx⟩ := j_app_surjective M (U := M.Y.left.basicOpen (cst M U π))
    (fun x hx => ((mem_basicOpen_cst hπ M U x).1 hx).2) (rs _ (M.j.preimage_mono hW) f)
  obtain ⟨⟨b, _, k, rfl⟩, e⟩ := IsLocalization.surj (Submonoid.powers (cst M U π)) x
  have hle : M.j ⁻¹ᵁ U ≤ M.j ⁻¹ᵁ M.Y.left.basicOpen (cst M U π) := fun y hy =>
    (mem_basicOpen_cst hπ M U _).2 ⟨hy, (mem_range_j M _).1 ⟨y, rfl⟩⟩
  refine ⟨k, b, ?_⟩
  have e' : x * rs _ hW (cst M U π ^ k) = rs _ hW b := e
  have := congrArg (fun z => rs _ hle ((M.j.app _).hom z)) e'
  simp only [map_mul, hx, ← rs_j M hW, rs_rs] at this
  have hid : ∀ z : Γ(A.left, M.j ⁻¹ᵁ U), rs A.left (le_refl (M.j ⁻¹ᵁ U)) z = z := fun z => by
    simp [rs]
  simp only [hid, map_pow] at this
  rw [← this, _root_.mul_comm]

omit [IsFractionRing R K] in

theorem prime_cst (hπ : Irreducible π) (M : Model R A) (hM : M.Irr) {U : M.Y.left.Opens} (hU : IsAffineOpen U)
    (h : ((U : Set M.Y.left) ∩ M.sp).Nonempty) : Prime (cst M U π) := by
  have := M.smooth
  obtain ⟨x, hx, hs⟩ := h
  have hp := IsPullback.of_hasPullback M.Y.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) :=
    IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective
  have hr : Set.range (pullback.fst M.Y.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) = M.sp :=
    Set.ext fun x => DvrModel.mem_range_special hp x
  have hc : _root_.IsConnected (Set.univ : Set ↑(pullback M.Y.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))) := by
    have hi := (pullback.fst M.Y.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).isClosedEmbedding.isInducing
    refine ⟨?_, hi.isPreconnected_image.1 ?_⟩
    · obtain ⟨y, -⟩ := hr.ge hs
      exact ⟨y, trivial⟩
    · rw [Set.image_univ, hr]; exact hM.isConnected.isPreconnected
  have := connectedSpace_iff_univ.2 hc
  have := isIntegral_of_smooth_field (pullback.snd M.Y.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
  exact DvrModel.prime_res hπ hp hU hx hs

omit [IsFractionRing R K] in

theorem nonempty_basicOpen_inter (hπ : Irreducible π) (M : Model R A) (hM : M.Irr) {U : M.Y.left.Opens}
    (hU : IsAffineOpen U) (h : ((U : Set M.Y.left) ∩ M.sp).Nonempty) {b : Γ(M.Y.left, U)}
    (hb : ¬ cst M U π ∣ b) : ((M.Y.left.basicOpen b : Set M.Y.left) ∩ M.sp).Nonempty := by
  have hp := prime_cst hπ M hM hU h
  let p : PrimeSpectrum Γ(M.Y.left, U) := ⟨Ideal.span {cst M U π}, (Ideal.span_singleton_prime hp.ne_zero).2 hp⟩
  refine ⟨hU.fromSpec p, (hU.fromSpec_preimage_basicOpen b).ge ?_, ?_⟩
  · exact fun h => hb (Ideal.mem_span_singleton.1 h)
  · by_contra hn
    have : hU.fromSpec p ∈ M.Y.left.basicOpen (cst M U π) :=
      (mem_basicOpen_cst hπ M U _).2 ⟨hU.range_fromSpec.le ⟨p, rfl⟩, hn⟩
    exact (hU.fromSpec_preimage_basicOpen _).le this (Ideal.mem_span_singleton_self _)

omit [IsFractionRing R K] in

theorem dvd_of_dvd_rs (hπ : Irreducible π) (M : Model R A) (hM : M.Irr) {U W : M.Y.left.Opens}
    (hU : IsAffineOpen U) (hW : W ≤ U) (h : ((W : Set M.Y.left) ∩ M.sp).Nonempty) {b : Γ(M.Y.left, U)}
    (hb : cst M W π ∣ rs _ hW b) : cst M U π ∣ b := by
  by_contra hn
  obtain ⟨x, hx, hx'⟩ := nonempty_basicOpen_inter hπ M hM hU (h.mono fun x hx => ⟨hW hx.1, hx.2⟩) hn
  obtain ⟨y, hy, hy'⟩ := h
  obtain ⟨z, hz, hz1, hz2⟩ := hM.2 _ _ (M.Y.left.basicOpen b).isOpen W.isOpen ⟨x, hx', hx⟩ ⟨y, hy', hy⟩
  have h1 : z ∈ M.Y.left.basicOpen (rs _ hW b) := (M.Y.left.basicOpen_res b (homOfLE hW).op).ge ⟨hz2, hz1⟩
  obtain ⟨c, hc⟩ := hb
  rw [hc, Scheme.basicOpen_mul] at h1
  exact ((mem_basicOpen_cst hπ M W z).1 h1.1).2 hz

theorem exists_j_eq_of_rs (hπ : Irreducible π) (M : Model R A) (hM : M.Irr) {U W : M.Y.left.Opens}
    (hU : IsAffineOpen U) (hW : W ≤ U) (h : ((W : Set M.Y.left) ∩ M.sp).Nonempty)
    (f : Γ(A.left, M.j ⁻¹ᵁ U)) (s : Γ(M.Y.left, W)) (hs : (M.j.app W).hom s = rs _ (M.j.preimage_mono hW) f) :
    ∃ b, (M.j.app U).hom b = f := by
  obtain ⟨k, b, hb⟩ := exists_pow_mul_eq hπ M hU f
  induction k generalizing b with
  | zero => exact ⟨b, by simpa using hb⟩
  | succ k ih =>
    have h1 : rs _ hW b = cst M W π ^ (k + 1) * s := j_app_injective M W (by
      rw [← rs_j M hW, hb, map_mul, map_pow, map_mul, map_pow, hs, rs_j M hW, rs_cst])
    obtain ⟨c, rfl⟩ := dvd_of_dvd_rs hπ M hM hU hW h (b := b) ⟨cst M W π ^ k * s, by rw [h1]; ring⟩
    refine ih c ((isUnit_j_cst hπ M U).mul_left_cancel ?_)
    rw [← map_mul, hb]; ring

end Dvr

section Order
variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {K : Type} [Field K] [Algebra R K]
  [IsFractionRing R K] {A : Over (Sp K)} {π : R} {I : Type} [Fintype I] [DecidableEq I]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in

theorem jac_mem_basicOpen (M : Model R A) (D : I → VF A) {U : M.Y.left.Opens} (hU : IsAffineOpen U)
    (g : Γ(M.Y.left, U)) (N : AddSubgroup Γ(A.left, M.j ⁻¹ᵁ M.Y.left.basicOpen g))
    (hN : ∀ s, ∀ x ∈ N, (M.j.app (M.Y.left.basicOpen g)).hom s * x ∈ N)
    (h : ∀ t : I → Γ(M.Y.left, U), rs _ (M.j.preimage_mono (M.Y.left.basicOpen_le g))
      (jac D (M.j ⁻¹ᵁ U) fun i => (M.j.app U).hom (t i)) ∈ N) (t : I → Γ(M.Y.left, M.Y.left.basicOpen g)) :
    jac D _ (fun i => (M.j.app (M.Y.left.basicOpen g)).hom (t i)) ∈ N := by
  have hl := hU.isLocalization_basicOpen g
  refine det_mem (rs _ (M.Y.left.basicOpen_le g)) (M.j.app _).hom (fun i => (D i).D _)
    (fun i => (D i).leibniz _) (fun x => ?_) N hN (fun t => ?_) t
  · obtain ⟨⟨b, c⟩, e⟩ := IsLocalization.surj (Submonoid.powers g) x
    exact ⟨b, c, IsLocalization.map_units _ c, e⟩
  · have := h t
    rw [rs_jac] at this
    simp only [rs_j M (M.Y.left.basicOpen_le g)] at this
    exact this

theorem exists_lower (hπ : Irreducible π) (M : Model R A) (D : I → VF A) {U : M.Y.left.Opens}
    (hU : IsAffineOpen U) : ∃ n : ℤ, ∀ t : I → Γ(M.Y.left, U), ∃ s : Γ(M.Y.left, U),
      jac D (M.j ⁻¹ᵁ U) (fun i => (M.j.app U).hom (t i)) =
        cstK A _ (algebraMap R K π ^ n) * (M.j.app U).hom s := by
  have := M.smooth
  have hf : (cst M U).FiniteType := (M.Y.hom.finiteType_appLE (isAffineOpen_top _) hU le_top).comp
    (RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).2)
  obtain ⟨N, hN⟩ := exists_pow_mul_mem (cst M U) hf (M.j.app U).hom (cst M U π) (fun i => (D i).D _)
    (fun i => (D i).leibniz _) (fun i r => by rw [j_cst]; exact (D i).const _ _) (exists_pow_mul_eq hπ M hU)
  choose s hs using hN
  refine ⟨-((N * Fintype.card I : ℕ) : ℤ), fun t => ⟨(Matrix.of fun i j => s i (t j)).det, ?_⟩⟩
  have hp : algebraMap R K π ≠ 0 := by simpa using hπ.ne_zero
  have e : (M.j.app U).hom (Matrix.of fun i j => s i (t j)).det =
      ((M.j.app U).hom (cst M U π) ^ N) ^ Fintype.card I *
        jac D (M.j ⁻¹ᵁ U) (fun i => (M.j.app U).hom (t i)) := by
    rw [jac, ← Matrix.det_smul, RingHom.map_det]
    congr 1
    ext i j
    exact hs i (t j)
  rw [e, j_cst, ← pow_mul, ← map_pow, ← _root_.mul_assoc, ← map_mul, zpow_neg, zpow_natCast,
    inv_mul_cancel₀ (pow_ne_zero _ hp), map_one, _root_.one_mul]

theorem exists_upper (hπ : Irreducible π) (M : Model R A) (hM : M.Irr) {D : I → VF A} (hD : IsFrame D)
    {U : M.Y.left.Opens} (hU : IsAffineOpen U) (h : ((U : Set M.Y.left) ∩ M.sp).Nonempty) :
    ∃ m : ℕ, ¬ ∀ t : I → Γ(M.Y.left, U), ∃ s : Γ(M.Y.left, U),
      jac D (M.j ⁻¹ᵁ U) (fun i => (M.j.app U).hom (t i)) =
        cstK A _ (algebraMap R K π ^ (m : ℤ)) * (M.j.app U).hom s := by
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  obtain ⟨J, hJ, hπJ, hJ'⟩ := exists_prime_iInf (prime_cst hπ M hM hU h) (cst_mem_nonZeroDivisors hπ M U)
  have h1 : ∀ t : I → Γ(M.Y.left, U), ∃ s ∈ J,
      (M.j.app U).hom s = jac D (M.j ⁻¹ᵁ U) (fun i => (M.j.app U).hom (t i)) := fun t => by
    obtain ⟨s, hs⟩ := hcon 0 t
    rw [Nat.cast_zero, zpow_zero, map_one, _root_.one_mul] at hs
    refine ⟨s, hJ' s fun n => ?_, hs.symm⟩
    obtain ⟨s', hs'⟩ := hcon n t
    refine ⟨s', j_app_injective M U ?_⟩
    rw [← hs, hs', map_mul, map_pow, j_cst, zpow_natCast, map_pow]
  let p : PrimeSpectrum Γ(M.Y.left, U) := ⟨J, hJ⟩
  have hx : hU.fromSpec p ∈ M.Y.left.basicOpen (cst M U π) := (hU.fromSpec_preimage_basicOpen _).ge hπJ
  obtain ⟨hxU, hxs⟩ := (mem_basicOpen_cst hπ M U _).1 hx
  obtain ⟨y, hy⟩ := (mem_range_j M _).2 hxs
  obtain ⟨V, t, hyV, ht⟩ := hD.2 y
  have := isOpenImmersion_j M
  obtain ⟨g, hg, hxg⟩ := hU.exists_basicOpen_le (V := M.j ''ᵁ V) ⟨hU.fromSpec p, y, hyV, hy⟩ hxU
  have hgJ : g ∉ J := (hU.fromSpec_preimage_basicOpen g).le hxg
  have hle : M.j ⁻¹ᵁ M.Y.left.basicOpen g ≤ V := (M.j.preimage_mono hg).trans (M.j.preimage_image_eq V).le
  have hsurj := j_app_surjective M (U := M.Y.left.basicOpen g) fun x hx => by
    obtain ⟨z, -, rfl⟩ := hg hx
    exact (mem_range_j M _).1 ⟨z, rfl⟩
  choose t' ht' using fun i => hsurj (rs _ hle (t i))
  let J' : Ideal Γ(M.Y.left, M.Y.left.basicOpen g) := J.map (rs _ (M.Y.left.basicOpen_le g))
  have key := jac_mem_basicOpen M D hU g (J'.toAddSubgroup.map (M.j.app _).hom.toAddMonoidHom)
    (by rintro s _ ⟨x, hx, rfl⟩; exact ⟨s * x, J'.mul_mem_left s hx, map_mul (M.j.app _).hom s x⟩)
    (fun t => by
      obtain ⟨s, hs, e⟩ := h1 t
      exact ⟨_, Ideal.mem_map_of_mem _ hs, by rw [← e, rs_j M (M.Y.left.basicOpen_le g)]; rfl⟩) t'
  obtain ⟨u, hu, e⟩ := key
  have hu' : IsUnit ((M.j.app (M.Y.left.basicOpen g)).hom u) := by
    have := ht.map (rs _ hle)
    rw [rs_jac] at this
    simp only [← ht'] at this
    exact e ▸ this
  have hu'' : IsUnit u := by
    obtain ⟨v, hv⟩ := hu'.exists_right_inv
    obtain ⟨w, rfl⟩ := hsurj v
    exact IsUnit.of_mul_eq_one w (j_app_injective M _ (by rw [map_mul, hv, map_one]))
  have hl := hU.isLocalization_basicOpen g
  have hdis : Disjoint (Submonoid.powers g : Set Γ(M.Y.left, U)) J := by
    rw [Set.disjoint_left]
    rintro _ ⟨k, rfl⟩ hk
    exact hgJ (hJ.mem_of_pow_mem k hk)
  have hpr := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers g)
    Γ(M.Y.left, M.Y.left.basicOpen g) J hJ hdis
  exact hpr.ne_top (Ideal.eq_top_of_isUnit_mem _ hu hu'')

theorem forall_of_affine (hπ : Irreducible π) (M : Model R A) (hM : M.Irr) (D : I → VF A)
    {U₀ : M.Y.left.Opens} (hU₀ : IsAffineOpen U₀) (h₀ : ((U₀ : Set M.Y.left) ∩ M.sp).Nonempty) {n : ℤ}
    (hn : ∀ t : I → Γ(M.Y.left, U₀), ∃ s : Γ(M.Y.left, U₀),
      jac D (M.j ⁻¹ᵁ U₀) (fun i => (M.j.app U₀).hom (t i)) =
        cstK A _ (algebraMap R K π ^ n) * (M.j.app U₀).hom s)
    (U : M.Y.left.Opens) (t : I → Γ(M.Y.left, U)) : ∃ s : Γ(M.Y.left, U),
      jac D (M.j ⁻¹ᵁ U) (fun i => (M.j.app U).hom (t i)) =
        cstK A _ (algebraMap R K π ^ n) * (M.j.app U).hom s := by
  have hp : algebraMap R K π ≠ 0 := by simpa using hπ.ne_zero
  have hinv : ∀ V : A.left.Opens, cstK A V (algebraMap R K π ^ n) * cstK A V (algebraMap R K π ^ n)⁻¹ = 1 :=
    fun V => by rw [← map_mul, mul_inv_cancel₀ (zpow_ne_zero n hp), map_one]
  suffices h : ∃ s, (M.j.app U).hom s = cstK A _ (algebraMap R K π ^ n)⁻¹ *
      jac D (M.j ⁻¹ᵁ U) (fun i => (M.j.app U).hom (t i)) by
    obtain ⟨s, hs⟩ := h
    exact ⟨s, by rw [hs, ← _root_.mul_assoc, hinv, _root_.one_mul]⟩
  refine exists_j_eq_of_local M U _ fun x hx => ?_
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := M.Y.left.isBasis_affineOpens.exists_subset_of_mem_open hx U.isOpen
  have hVU' : V ≤ U := hVU
  refine ⟨V, hVU', hxV, ?_⟩
  by_cases hs : ((V : Set M.Y.left) ∩ M.sp).Nonempty
  swap
  · exact j_app_surjective M (fun z hz hz' => hs ⟨z, hz, hz'⟩) _
  obtain ⟨a, ha, ha'⟩ := hs
  obtain ⟨b, hb, hb'⟩ := h₀
  obtain ⟨z, hz, hz1, hz2⟩ := hM.2 _ _ V.isOpen U₀.isOpen ⟨a, ha', ha⟩ ⟨b, hb', hb⟩
  obtain ⟨g, hg, hzg⟩ := hU₀.exists_basicOpen_le (V := V) ⟨z, hz1⟩ hz2
  let N : AddSubgroup Γ(A.left, M.j ⁻¹ᵁ M.Y.left.basicOpen g) :=
    ((AddMonoidHom.mulLeft (cstK A _ (algebraMap R K π ^ n))).comp
      (M.j.app (M.Y.left.basicOpen g)).hom.toAddMonoidHom).range
  have hN : ∀ x, x ∈ N ↔ ∃ s, cstK A _ (algebraMap R K π ^ n) * (M.j.app (M.Y.left.basicOpen g)).hom s = x :=
    fun x => Iff.rfl
  have key := jac_mem_basicOpen M D hU₀ g N
    (fun s x hx => by
      obtain ⟨y, rfl⟩ := (hN x).1 hx
      exact (hN _).2 ⟨s * y, by rw [map_mul]; ring⟩)
    (fun t => by
      obtain ⟨s, hs⟩ := hn t
      exact (hN _).2 ⟨rs _ (M.Y.left.basicOpen_le g) s, by
        rw [hs, map_mul, rs_cstK, rs_j M (M.Y.left.basicOpen_le g)]⟩)
    (fun i => rs _ (hg.trans hVU') (t i))
  obtain ⟨s, hs⟩ := (hN _).1 key
  refine exists_j_eq_of_rs hπ M hM hV hg ⟨z, hzg, hz⟩ _ s ?_
  rw [rs_rs, map_mul, rs_cstK, rs_jac]
  simp only [rs_j M (hg.trans hVU')]
  rw [← hs, ← _root_.mul_assoc, _root_.mul_comm (cstK A _ _⁻¹), hinv, _root_.one_mul]

theorem exists_hasOrd (hπ : Irreducible π) (M : Model R A) (hM : M.Irr) {D : I → VF A} (hD : IsFrame D) :
    ∃ n : ℤ, HasOrd M D π n := by
  have hp : algebraMap R K π ≠ 0 := by simpa using hπ.ne_zero
  obtain ⟨x, hx⟩ := hM.1
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := M.Y.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ x) isOpen_univ
  have h : ((U : Set M.Y.left) ∩ M.sp).Nonempty := ⟨x, hxU, hx⟩
  obtain ⟨m, hm⟩ := exists_upper hπ M hM hD hU h
  obtain ⟨n, hn, hmax⟩ := Int.exists_greatest_of_bdd (P := fun n : ℤ => ∀ t : I → Γ(M.Y.left, U),
    ∃ s : Γ(M.Y.left, U), jac D (M.j ⁻¹ᵁ U) (fun i => (M.j.app U).hom (t i)) =
        cstK A _ (algebraMap R K π ^ n) * (M.j.app U).hom s) ⟨m, fun n hn => by
      by_contra hlt
      obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = m + k := ⟨(n - m).toNat, by omega⟩
      refine hm fun t => ?_
      obtain ⟨s, hs⟩ := hn t
      exact ⟨cst M U π ^ k * s, by
        rw [hs, zpow_add₀ hp, map_mul, map_mul, map_pow, j_cst, zpow_natCast _ k, map_pow, _root_.mul_assoc]⟩⟩
    (exists_lower hπ M D hU)
  refine ⟨n, forall_of_affine hπ M hM D hU h hn, ?_⟩
  obtain ⟨t, ht⟩ := not_forall.1 (fun h => by have := hmax (n + 1) h; omega)
  obtain ⟨s, hs⟩ := hn t
  have hns : ¬ cst M U π ∣ s := by
    rintro ⟨c, rfl⟩
    exact ht ⟨c, by rw [hs, zpow_add_one₀ hp, map_mul, map_mul, j_cst, _root_.mul_assoc]⟩
  have hle := M.Y.left.basicOpen_le s
  refine ⟨M.Y.left.basicOpen s, fun i => rs _ hle (t i), rs _ hle s,
    nonempty_basicOpen_inter hπ M hM hU h hns, M.Y.left.toRingedSpace.isUnit_res_basicOpen s, ?_⟩
  have := congrArg (rs _ (M.j.preimage_mono hle)) hs
  rw [rs_jac, map_mul, rs_cstK, rs_j M hle] at this
  simpa only [rs_j M hle] using this

end Order

theorem existsUnique_hasOrd : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (π : R), Irreducible π → ∀ (A : Over (Sp K)) (I : Type) [Fintype I] [DecidableEq I] (D : I → VF A), IsFrame D → ∀ M : Model R A, M.Irr → ∃! n : ℤ, HasOrd M D π n := by
  intro R K _ _ _ _ _ _ π hπ A I _ _ D hD M hM
  exact existsUnique_of_exists_of_unique (exists_hasOrd hπ M hM hD)
    fun _ _ h h' => hasOrd_unique M D hπ.not_isUnit hπ.ne_zero h h'

end GlobalTheory.SS.Ord
end
