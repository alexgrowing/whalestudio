import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsMvPolynomialOfIteratedBackwardDifferenceVa
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.QCoh GlobalTheory.Twist GlobalTheory.CechPic

universe v

namespace GlobalTheory

section BaseChange

variable {R : Type*} (K : Type*) {G N : Type*} [CommRing R] [CommRing K] [Algebra R K]
  [AddCommGroup G] [Module R G] [AddCommGroup N] [Module R N] [Module K N] [IsScalarTower R K N]

theorem multilinearMap_ext_one_tmul {ι : Type*} [Finite ι]
    {Φ Ψ : MultilinearMap K (fun _ : ι ↦ K ⊗[R] G) N}
    (h : ∀ x : ι → G, Φ (fun i ↦ 1 ⊗ₜ x i) = Ψ fun i ↦ 1 ⊗ₜ x i) : Φ = Ψ := by
  refine MultilinearMap.ext_of_span_eq_top (g := fun _ (x : G) ↦ (1 : K) ⊗ₜ[R] x) (fun _ ↦ ?_) h
  rw [eq_top_iff]
  rintro z -
  induction z with
  | zero => exact zero_mem _
  | tmul a x =>
    rw [← mul_one a, ← smul_eq_mul, ← smul_tmul']
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
  | add a b ha hb => exact add_mem ha hb

theorem exists_linearMap_multilinearMap_baseChange (d : ℕ) :
    ∃ E : MultilinearMap R (fun _ : Fin d ↦ G) N →ₗ[R]
        MultilinearMap K (fun _ : Fin d ↦ K ⊗[R] G) N,
      ∀ φ x, E φ (fun i ↦ 1 ⊗ₜ x i) = φ x := by
  have (n : ℕ) : IsScalarTower R K (MultilinearMap K (fun _ : Fin n ↦ K ⊗[R] G) N) :=
    ⟨fun r a φ ↦ MultilinearMap.ext fun x ↦ smul_assoc r a (φ x)⟩
  induction d with
  | zero =>
    refine ⟨(MultilinearMap.constLinearEquivOfIsEmpty K K _ N).toLinearMap.restrictScalars R ∘ₗ
      (MultilinearMap.constLinearEquivOfIsEmpty R R _ N).symm.toLinearMap, fun φ x ↦ ?_⟩
    exact congrArg φ (Subsingleton.elim _ _)
  | succ d ih =>
    obtain ⟨E, hE⟩ := ih
    refine ⟨(multilinearCurryLeftEquiv K (fun _ : Fin (d + 1) ↦ K ⊗[R] G)
        N).symm.toLinearMap.restrictScalars R ∘ₗ
      (LinearMap.liftBaseChangeEquiv K).toLinearMap.restrictScalars R ∘ₗ
      LinearMap.compRight R E ∘ₗ
      (multilinearCurryLeftEquiv R (fun _ : Fin (d + 1) ↦ G) N).toLinearMap, fun φ x ↦ ?_⟩
    have h := hE (φ.curryLeft (x 0)) (Fin.tail x)
    rw [MultilinearMap.curryLeft_apply, Fin.cons_self_tail] at h
    rw [← h]
    simp [multilinearCurryLeftEquiv]
    rfl

theorem existsUnique_multilinearMap_baseChange {d : ℕ}
    (φ : MultilinearMap R (fun _ : Fin d ↦ G) N) :
    ∃! Φ : MultilinearMap K (fun _ : Fin d ↦ K ⊗[R] G) N, ∀ x, Φ (fun i ↦ 1 ⊗ₜ x i) = φ x :=
  have ⟨E, hE⟩ := exists_linearMap_multilinearMap_baseChange (R := R) K (G := G) (N := N) d
  ⟨E φ, hE φ, fun _ h ↦ multilinearMap_ext_one_tmul K fun x ↦ (h x).trans (hE φ x).symm⟩

end BaseChange

section Diff

variable {G M : Type*} [AddCommGroup G] [AddCommGroup M] {φ : G → M} {d : ℕ} {ι : Type*}
  [Fintype ι]

theorem DiffVanish.multiDiff_eq_of_le_card (h : DiffVanish (d + 1) φ) (hd : d ≤ Fintype.card ι)
    (g : ι → G) (x y : G) : multiDiff g φ x = multiDiff g φ y := by
  rw [← multiDiff_comp_equiv (Fintype.equivFin ι).symm]
  exact (h.mono (Nat.succ_le_succ hd)).multiDiff_eq _ x y

theorem DiffVanish.multiDiff_update_add_of_le_card [DecidableEq ι] (h : DiffVanish (d + 1) φ)
    (hd : d ≤ Fintype.card ι) (g : ι → G) (i : ι) (a b : G) :
    multiDiff (Function.update g i (a + b)) φ =
      multiDiff (Function.update g i a) φ + multiDiff (Function.update g i b) φ := by
  simp only [← multiDiff_comp_equiv (Fintype.equivFin ι).symm (Function.update g i _),
    Function.update_comp_equiv]
  exact (h.mono (Nat.succ_le_succ hd)).multiDiff_update_add _ _ a b

end Diff

section Vanish

variable {X : Scheme.{0}} {k : Type v} [Field k] [Algebra k Γ(X, ⊤)] {F : X.Modules}

theorem bwdDiff_chiPic_eq_chiPic_cut {L : LB X} (hL : L.IsLB) (s : L.Sec) [Mono (cutHom F hL s)]
    (h : FiniteCohTwists k F) : bwdDiff (cls L hL) (chiPic k F) = chiPic k (cut F hL s) := by
  funext c
  have e := congrFun (chiPic_shortExact (shortExact_cutComplex F hL s)
    (h.twist (isLB_lbZPow hL (-1))) (h.cut hL s)) c
  change chiPic k F c = chiPic k (twist F (lbZPow L (-1))) c + chiPic k (cut F hL s) c at e
  rw [chiPic_twist k F (isLB_lbZPow hL (-1)), cls_lbZPow hL, neg_one_zsmul, neg_add_eq_sub] at e
  rw [bwdDiff_apply, e, add_sub_cancel_left]

theorem IsAmpleLB.diffVanish_chiPic_of_suppDim_lt [IsLocallyNoetherian X] {A : LB X}
    (hA : IsAmpleLB A) [IsFiniteQC F] (h : FiniteCohTwists k F) {n : ℕ} (hn : suppDim F < n) :
    DiffVanish n (chiPic k F) := by
  induction n generalizing F with
  | zero =>
    rw [diffVanish_zero_iff]
    funext c
    obtain ⟨M, hM, rfl⟩ := cls_surj c
    exact chi_eq_zero_of_isZero k ((isZero_twist_iff hM).2 (suppDim_lt_zero_iff.1 hn))
  | succ n ih =>
    refine diffVanish_of_generators
      (S := {c | ∃ (L : LB X) (hL : L.IsLB) (s : L.Sec), Mono (cutHom F hL s) ∧ c = cls L hL})
      (eq_top_iff.2 fun c _ ↦ ?_) fun g hg ↦ ?_
    · obtain ⟨P, Q, hP, hQ, s, t, hs, ht, rfl⟩ := hA.exists_sub_of_mono_cutHom F c
      exact sub_mem (AddSubgroup.subset_closure ⟨P, hP, s, hs, rfl⟩)
        (AddSubgroup.subset_closure ⟨Q, hQ, t, ht, rfl⟩)
    · obtain ⟨L, hL, s, hs, e⟩ := hg 0
      rw [← Fin.cons_self_tail g, multiDiff_cons', e, bwdDiff_chiPic_eq_chiPic_cut hL s h]
      refine ih (h.cut hL s) ?_ _
      have := (suppDim_cut_add_one_le F hL s).trans_lt hn
      by_contra hc
      rw [not_lt] at hc
      refine this.not_ge ?_
      push_cast
      exact add_le_add_left hc 1

theorem IsAmpleLB.diffVanish_chiPic [IsLocallyNoetherian X] {A : LB X}
    (hA : IsAmpleLB A) [IsFiniteQC F] (h : FiniteCohTwists k F) {d : ℕ} (hd : suppDim F ≤ d) :
    DiffVanish (d + 1) (chiPic k F) :=
  hA.diffVanish_chiPic_of_suppDim_lt h (hd.trans_lt (by exact_mod_cast d.lt_succ_self))

end Vanish

section Proj

variable {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)] {f : X ⟶ Sp k}
  (hf : ∀ r, algebraMap k Γ(X, ⊤) r = f.appTop ((Scheme.ΓSpecIso (.of k)).inv r))
  (F : X.Modules) [IsFiniteQC F]
include hf

theorem IsAmpleLB.finiteCohTwists [IsProper f] {A : LB X} (hA : IsAmpleLB A) :
    FiniteCohTwists k F := fun _ hM ↦
  have := isFiniteQC_twist (F := F) hM
  hA.finiteCoh hf _

theorem IsAmpleLB.diffVanish_chiPic_of_isProper [IsProper f] {A : LB X} (hA : IsAmpleLB A) {d : ℕ}
    (hd : suppDim F ≤ d) : DiffVanish (d + 1) (chiPic k F) :=
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  hA.diffVanish_chiPic (hA.finiteCohTwists hf F) hd

theorem diffVanish_chiPic_of_isProjOver_of_lt (h : IsProjOver f) {n : ℕ} (hn : suppDim F < n) :
    DiffVanish n (chiPic k F) :=
  have := isNoetherian_of_isProjOver h
  have ⟨_, _, hA⟩ := isProper_and_exists_isAmpleLB_of_isProjOver h
  hA.diffVanish_chiPic_of_suppDim_lt (finiteCohTwists_of_isProjOver hf F h) hn

theorem diffVanish_chiPic_of_isProjOver (h : IsProjOver f) {d : ℕ} (hd : suppDim F ≤ d) :
    DiffVanish (d + 1) (chiPic k F) :=
  diffVanish_chiPic_of_isProjOver_of_lt hf F h (hd.trans_lt (by exact_mod_cast d.lt_succ_self))

theorem interNum_eq_zero_of_isProjOver (h : IsProjOver f) {ι : Type} [Fintype ι]
    (hn : suppDim F < Fintype.card ι) {L : ι → LB X} (hL : ∀ i, (L i).IsLB) :
    interNum k F L = 0 := by
  rw [interNum_eq_multiDiff k F hL,
    (diffVanish_chiPic_of_isProjOver_of_lt hf F h hn).multiDiff_eq_zero le_rfl, Pi.zero_apply]

end Proj

section Consequences

variable {X : Scheme.{0}} {k : Type v} [Field k] [Algebra k Γ(X, ⊤)] {F : X.Modules} {d : ℕ}
  {ι : Type} [Fintype ι] {L : ι → LB X} {M A B : LB X}

theorem isLB_update [DecidableEq ι] (hL : ∀ i, (L i).IsLB) (i : ι) (hM : M.IsLB) :
    ∀ j, (Function.update L i M j).IsLB := fun j ↦ by
  by_cases h : j = i
  · subst h; rwa [Function.update_self]
  · rw [Function.update_of_ne h]; exact hL j

theorem cls_update [DecidableEq ι] (hL : ∀ i, (L i).IsLB) (i : ι) (hM : M.IsLB) :
    (fun j ↦ cls _ (isLB_update hL i hM j)) =
      Function.update (fun j ↦ cls (L j) (hL j)) i (cls M hM) := by
  funext j
  by_cases h : j = i
  · subst h; simp only [Function.update_self]
  · simp only [Function.update_of_ne h]

namespace DiffVanish

theorem interNum_eq_zero {n : ℕ} (h : DiffVanish n (chiPic k F)) (hn : n ≤ Fintype.card ι)
    (hL : ∀ i, (L i).IsLB) : interNum k F L = 0 := by
  rw [interNum_eq_multiDiff k F hL, h.multiDiff_eq_zero hn, Pi.zero_apply]

variable (h : DiffVanish (d + 1) (chiPic k F))
include h

theorem chiPic_twist (hM : M.IsLB) : DiffVanish (d + 1) (chiPic k (twist F M)) := by
  rw [funext (GlobalTheory.chiPic_twist k F hM)]
  exact h.translate _

theorem chiPic_pushforward_of_isAffineHom {Y : Scheme.{0}} [Algebra k Γ(Y, ⊤)] {f : X ⟶ Y}
    (hf : ∀ r : k, f.appTop (algebraMap k Γ(Y, ⊤) r) = algebraMap k Γ(X, ⊤) r) [IsAffineHom f]
    [F.IsQuasicoherent] :
    DiffVanish (d + 1) (chiPic k ((Scheme.Modules.pushforward f).obj F)) := by
  rw [GlobalTheory.chiPic_pushforward_of_isAffineHom hf]
  exact h.comap _

theorem form_cls {P : Fin d → LB X} (hP : ∀ i, (P i).IsLB) :
    h.form (fun i ↦ cls (P i) (hP i)) = interNum k F P := by
  rw [interNum_eq_multiDiff k F hP, h.form_apply _ 0]

theorem multiDiff_chiPic (hd : d ≤ Fintype.card ι) (hL : ∀ i, (L i).IsLB) (c : Pic X) :
    multiDiff (fun i ↦ cls (L i) (hL i)) (chiPic k F) c = interNum k F L := by
  rw [interNum_eq_multiDiff k F hL, h.multiDiff_eq_of_le_card hd _ c 0]

theorem interNum_twist (hd : d ≤ Fintype.card ι) (hL : ∀ i, (L i).IsLB) (hM : M.IsLB) :
    interNum k (twist F M) L = interNum k F L := by
  rw [interNum_twist_eq_multiDiff k F hL hM, h.multiDiff_chiPic hd hL]

section Update

variable [DecidableEq ι] (hd : d ≤ Fintype.card ι) (hL : ∀ i, (L i).IsLB) (i : ι)
include hd hL

theorem interNum_update_of_cls_eq_add (hM : M.IsLB) (hA : A.IsLB) (hB : B.IsLB)
    (e : cls M hM = cls A hA + cls B hB) :
    interNum k F (Function.update L i M) =
      interNum k F (Function.update L i A) + interNum k F (Function.update L i B) := by
  rw [interNum_eq_multiDiff k F (isLB_update hL i hM),
    interNum_eq_multiDiff k F (isLB_update hL i hA),
    interNum_eq_multiDiff k F (isLB_update hL i hB), cls_update hL i hM, cls_update hL i hA,
    cls_update hL i hB, e,
    h.multiDiff_update_add_of_le_card hd, Pi.add_apply]

theorem interNum_update_tens (hA : A.IsLB) (hB : B.IsLB) :
    interNum k F (Function.update L i (tens A B)) =
      interNum k F (Function.update L i A) + interNum k F (Function.update L i B) :=
  h.interNum_update_of_cls_eq_add hd hL i (isLB_tens hA hB) hA hB (cls_tens hA hB _)

theorem interNum_update_of_cls_eq_sum {κ : Type*} (s : Finset κ) {P : κ → LB X}
    (hP : ∀ j, (P j).IsLB) (n : κ → ℤ) (hM : M.IsLB)
    (e : cls M hM = ∑ j ∈ s, n j • cls (P j) (hP j)) :
    interNum k F (Function.update L i M) =
      ∑ j ∈ s, n j * interNum k F (Function.update L i (P j)) := by
  let ψ : Pic X →+ ℤ := AddMonoidHom.mk'
    (fun c ↦ multiDiff (Function.update (fun j ↦ cls (L j) (hL j)) i c) (chiPic k F) 0)
    fun a b ↦ congrFun (h.multiDiff_update_add_of_le_card hd _ i a b) 0
  have hψ : ∀ (N : LB X) (hN : N.IsLB), interNum k F (Function.update L i N) = ψ (cls N hN) :=
    fun N hN ↦ by rw [interNum_eq_multiDiff k F (isLB_update hL i hN), cls_update hL i hN]; rfl
  rw [hψ M hM, e, map_sum]
  exact Finset.sum_congr rfl fun j _ ↦ by rw [map_zsmul, hψ _ (hP j), smul_eq_mul]

theorem interNum_update_of_cls_eq_zsmul (hM : M.IsLB) (hA : A.IsLB) (n : ℤ)
    (e : cls M hM = n • cls A hA) :
    interNum k F (Function.update L i M) = n * interNum k F (Function.update L i A) := by
  simpa using h.interNum_update_of_cls_eq_sum hd hL i (Finset.univ : Finset Unit)
    (P := fun _ ↦ A) (fun _ ↦ hA) (fun _ ↦ n) hM (by simpa using e)

end Update

theorem interNum_cons_of_cls_eq_add {e : ℕ} (he : d ≤ e + 1) {P : Fin e → LB X}
    (hP : ∀ i, (P i).IsLB) (hM : M.IsLB) (hA : A.IsLB) (hB : B.IsLB)
    (hc : cls M hM = cls A hA + cls B hB) :
    interNum k F (Fin.cons M P : Fin (e + 1) → LB X) =
      interNum k F (Fin.cons A P : Fin (e + 1) → LB X) +
        interNum k F (Fin.cons B P : Fin (e + 1) → LB X) := by
  rw [GlobalTheory.interNum_cons_of_cls_eq_add k F hM hA hB hP hc,
    h.interNum_eq_zero (by simpa using he) (isLB_cons hA (isLB_cons hB hP)), sub_zero]

theorem interNum_of_cls_eq_zsmul {P Q : Fin d → LB X} (hP : ∀ i, (P i).IsLB) (hQ : ∀ i, (Q i).IsLB)
    (n : Fin d → ℤ) (e : ∀ i, cls (Q i) (hQ i) = n i • cls (P i) (hP i)) :
    interNum k F Q = (∏ i, n i) * interNum k F P := by
  rw [← h.form_cls hQ, ← h.form_cls hP, funext e, MultilinearMap.map_smul_univ, smul_eq_mul]

theorem interNum_of_cls_eq_sum [DecidableEq ι] (hL : ∀ j, (L j).IsLB) {Q : Fin d → LB X}
    (hQ : ∀ i, (Q i).IsLB) (n : Fin d → ι → ℤ)
    (e : ∀ i, cls (Q i) (hQ i) = ∑ j, n i j • cls (L j) (hL j)) :
    interNum k F Q = ∑ a : Fin d → ι, (∏ i, n i (a i)) * interNum k F (L ∘ a) := by
  rw [← h.form_cls hQ, funext e, MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [MultilinearMap.map_smul_univ, smul_eq_mul, ← h.form_cls (P := L ∘ a) fun i ↦ hL (a i)]
  rfl

variable (K : Type*)

section Poly

variable [Field K] [CharZero K]

theorem exists_polynomial_chi (hA : A.IsLB) (hB : B.IsLB) :
    ∃ p : Polynomial K, p.natDegree ≤ d ∧
      (∀ (n : ℤ) (N : LB X) (hN : N.IsLB), cls N hN = cls A hA + n • cls B hB →
        p.eval (n : K) = chi k (twist F N)) ∧
      p.coeff d = (d.factorial : K)⁻¹ * interNum k F fun _ : Fin d ↦ B := by
  obtain ⟨p, h1, h2, h3⟩ := h.exists_polynomial_int K (cls B hB) (cls A hA)
  exact ⟨p, h1, fun n N hN e ↦ by rw [h2, ← e, chiPic_cls],
    by rw [h3, h.multiDiff_chiPic (by simp) fun _ ↦ hB]⟩

theorem exists_polynomial_chi_twistZ (hM : M.IsLB) :
    ∃ p : Polynomial K, p.natDegree ≤ d ∧ (∀ n : ℤ, p.eval (n : K) = chi k (twistZ F M n)) ∧
      p.coeff d = (d.factorial : K)⁻¹ * interNum k F fun _ : Fin d ↦ M := by
  obtain ⟨p, h1, h2, h3⟩ := h.exists_polynomial_chi K (LB.isLB_triv X) hM
  exact ⟨p, h1, fun n ↦ h2 n _ (isLB_lbZPow hM n) (by rw [cls_lbZPow hM, cls_triv, zero_add]), h3⟩

end Poly

section Ext

variable [CommRing K]

theorem existsUnique_interForm :
    ∃! Φ : MultilinearMap K (fun _ : Fin d ↦ K ⊗[ℤ] Pic X) K,
      ∀ (P : Fin d → LB X) (hP : ∀ i, (P i).IsLB),
        Φ (fun i ↦ 1 ⊗ₜ cls (P i) (hP i)) = interNum k F P := by
  refine (existsUnique_congr fun Φ ↦ ⟨fun H P hP ↦ ?_, fun H x ↦ ?_⟩).1
    (existsUnique_multilinearMap_baseChange K
      ((Algebra.linearMap ℤ K).compMultilinearMap h.form))
  · rw [H, ← h.form_cls hP]; rfl
  · choose P hP e using fun i ↦ cls_surj (x i)
    obtain rfl : x = fun i ↦ cls (P i) (hP i) := funext fun i ↦ (e i).symm
    rw [H, ← h.form_cls hP]; rfl

def interForm : MultilinearMap K (fun _ : Fin d ↦ K ⊗[ℤ] Pic X) K :=
  (h.existsUnique_interForm K).exists.choose

end Ext

end DiffVanish

end Consequences

end GlobalTheory
