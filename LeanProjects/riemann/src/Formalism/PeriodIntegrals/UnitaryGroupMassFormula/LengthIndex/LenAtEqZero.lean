import Mathlib
import Formalism.PeriodIntegrals.DivisionRowsRationalLattice
import Formalism.PeriodIntegrals.IdxCalc

noncomputable section

namespace PI.Dv.ProjAW

open NumberField IsDedekindDomain Formalism.BasicNotions

variable {K : Type} [Field K] [NumberField K] [StarRing K]

section Gen

variable (A : HLat K)

lemma mem_cutE (f : Module.End K A.V) (M : Submodule (𝓞 K) A.V) (x : A.V) :
    x ∈ cutE A f M ↔ x ∈ M ∧ x ∈ LinearMap.range f := Iff.rfl

lemma mem_imgE (f : Module.End K A.V) (M : Submodule (𝓞 K) A.V) (x : A.V) :
    x ∈ imgE A f M ↔ ∃ y ∈ M, f y = x := Iff.rfl

lemma idem_of {f : Module.End K A.V} (hf : f * f = f) {x : A.V} (hx : x ∈ LinearMap.range f) :
    f x = x := by
  obtain ⟨y, rfl⟩ := hx
  have h := LinearMap.congr_fun hf y
  simpa [Module.End.mul_apply] using h

lemma one_sub_idem {f : Module.End K A.V} (hf : f * f = f) : (1 - f) * (1 - f) = 1 - f := by
  rw [mul_sub, mul_one, sub_mul, one_mul, hf, sub_self, sub_zero]

lemma one_sub_int {f : Module.End K A.V} {n : ℕ}
    (hn : ∀ x ∈ A.L, ((n : ℕ) : 𝓞 K) • f x ∈ A.L) :
    ∀ x ∈ A.L, ((n : ℕ) : 𝓞 K) • (1 - f) x ∈ A.L := by
  intro x hx
  have h : ((n : ℕ) : 𝓞 K) • (1 - f) x = ((n : ℕ) : 𝓞 K) • x - ((n : ℕ) : 𝓞 K) • f x := by
    simp [smul_sub]
  rw [h]
  exact A.L.sub_mem (A.L.smul_mem _ hx) (hn x hx)

lemma part1 {f : Module.End K A.V} {n : ℕ} (hn : ∀ x ∈ A.L, ((n : ℕ) : 𝓞 K) • f x ∈ A.L) :
    ∀ x ∈ imgE A f A.L, ((n : ℕ) : 𝓞 K) • x ∈ cutE A f A.L := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (mem_imgE A f A.L x).1 hx
  refine (mem_cutE A f A.L _).2 ⟨hn y hy, ((n : ℕ) : 𝓞 K) • y, ?_⟩
  exact LinearMap.map_smul_of_tower f _ y

lemma part2 {f : Module.End K A.V} (hf : f * f = f) : cutE A f A.L ≤ imgE A f A.L := by
  intro x hx
  obtain ⟨hxL, hxr⟩ := (mem_cutE A f A.L x).1 hx
  exact (mem_imgE A f A.L x).2 ⟨x, hxL, idem_of A hf hxr⟩

lemma span_imgE (hG : A.Good) (f : Module.End K A.V) :
    Submodule.span K (imgE A f A.L : Set A.V) = LinearMap.range f := by
  have h : (imgE A f A.L : Set A.V) = f '' (A.L : Set A.V) := by
    simp only [imgE, Submodule.map_coe, LinearMap.coe_restrictScalars]
  rw [h, Submodule.span_image, hG.2.2, Submodule.map_top]

lemma span_cut_eq {f : Module.End K A.V} (hf : f * f = f) {n : ℕ} (hn0 : 0 < n)
    (hn : ∀ x ∈ A.L, ((n : ℕ) : 𝓞 K) • f x ∈ A.L) :
    Submodule.span K (imgE A f A.L : Set A.V) = Submodule.span K (cutE A f A.L : Set A.V) := by
  refine le_antisymm ?_ (Submodule.span_mono (part2 A hf))
  rw [Submodule.span_le]
  intro x hx
  have h1 := part1 A hn x hx
  have h2 : ((n : ℕ) : K) • x ∈ Submodule.span K (cutE A f A.L : Set A.V) := by
    have : ((n : ℕ) : K) • x = ((n : ℕ) : 𝓞 K) • x := by
      rw [Nat.cast_smul_eq_nsmul K, Nat.cast_smul_eq_nsmul (𝓞 K)]
    rw [this]
    exact Submodule.subset_span h1
  have hnz : ((n : ℕ) : K) ≠ 0 := by exact_mod_cast hn0.ne'
  have h3 := Submodule.smul_mem _ ((n : ℕ) : K)⁻¹ h2
  rwa [smul_smul, inv_mul_cancel₀ hnz, one_smul] at h3

lemma fg_img (hG : A.Good) (f : Module.End K A.V) : (imgE A f A.L).FG := hG.2.1.map _

lemma fg_cut (hG : A.Good) (f : Module.End K A.V) : (cutE A f A.L).FG :=
  Submodule.FG.of_le hG.2.1 inf_le_left

lemma rk_img (hG : A.Good) (f : Module.End K A.V) : Formalism.HN.rkK (imgE A f A.L) = dimE A f := by
  unfold Formalism.HN.rkK dimE
  rw [span_imgE A hG f]

def toQ (f : Module.End K A.V) :
    A.L →ₗ[𝓞 K] (↥(imgE A f A.L) ⧸ (cutE A f A.L).comap (imgE A f A.L).subtype) :=
  Submodule.mkQ _ ∘ₗ (f.restrictScalars (𝓞 K)).submoduleMap A.L

lemma toQ_surj (f : Module.End K A.V) : Function.Surjective (toQ A f) :=
  (Submodule.mkQ_surjective _).comp (LinearMap.submoduleMap_surjective _ _)

lemma mem_ker_toQ (f : Module.End K A.V) (a : A.L) :
    a ∈ LinearMap.ker (toQ A f) ↔ f a ∈ A.L := by
  rw [LinearMap.mem_ker]
  change Submodule.Quotient.mk _ = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  change f a ∈ A.L ∧ f a ∈ LinearMap.range f ↔ f a ∈ A.L
  exact ⟨fun h => h.1, fun h => ⟨h, a, rfl⟩⟩

lemma ker_toQ_eq (e : Module.End K A.V) :
    LinearMap.ker (toQ A e) = LinearMap.ker (toQ A (1 - e)) := by
  ext a
  rw [mem_ker_toQ, mem_ker_toQ]
  have h : (1 - e) (a : A.V) = (a : A.V) - e a := by simp
  rw [h]
  constructor
  · intro h1; exact A.L.sub_mem a.2 h1
  · intro h1
    have := A.L.sub_mem a.2 h1
    simpa using this

def quotEquiv (e : Module.End K A.V) :
    (↥(imgE A e A.L) ⧸ (cutE A e A.L).comap (imgE A e A.L).subtype) ≃ₗ[𝓞 K]
    (↥(imgE A (1 - e) A.L) ⧸ (cutE A (1 - e) A.L).comap (imgE A (1 - e) A.L).subtype) :=
  ((toQ A e).quotKerEquivOfSurjective (toQ_surj A e)).symm.trans
    ((Submodule.quotEquivOfEq _ _ (ker_toQ_eq A e)).trans
      ((toQ A (1 - e)).quotKerEquivOfSurjective (toQ_surj A (1 - e))))

end Gen

section Len

variable {V W : Type} [AddCommGroup V] [Module (𝓞 K) V] [AddCommGroup W] [Module (𝓞 K) W]

lemma lenAt_congr (w : HeightOneSpectrum (𝓞 K)) (M N : Submodule (𝓞 K) V) (M' N' : Submodule (𝓞 K) W)
    (φ : (↥M ⧸ N.comap M.subtype) ≃ₗ[𝓞 K] (↥M' ⧸ N'.comap M'.subtype)) :
    lenAt w M N = lenAt w M' N' := by
  unfold lenAt
  let _ : w.asIdeal.IsPrime := w.isPrime
  exact (IsLocalizedModule.mapEquiv w.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap w.asIdeal.primeCompl _)
    (LocalizedModule.mkLinearMap w.asIdeal.primeCompl _)
    (Localization.AtPrime w.asIdeal) φ).length_eq

lemma lenAt_eq_zero (w : HeightOneSpectrum (𝓞 K)) {M N : Submodule (𝓞 K) V} (h : M ≤ N) :
    lenAt w M N = 0 := by
  unfold lenAt
  let _ : w.asIdeal.IsPrime := w.isPrime
  have hs : Subsingleton (↥M ⧸ N.comap M.subtype) := ⟨fun a b => by
    refine Submodule.Quotient.induction_on _ a (fun a => ?_)
    refine Submodule.Quotient.induction_on _ b (fun b => ?_)
    have ha : (Submodule.Quotient.mk a : ↥M ⧸ N.comap M.subtype) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 (show a ∈ N.comap M.subtype from h a.2)
    have hb : (Submodule.Quotient.mk b : ↥M ⧸ N.comap M.subtype) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 (show b ∈ N.comap M.subtype from h b.2)
    rw [ha, hb]⟩
  rw [Module.length_eq_zero_iff]
  refine ⟨fun a b => ?_⟩
  induction a using LocalizedModule.induction_on with
  | h m s =>
    induction b using LocalizedModule.induction_on with
    | h m' s' =>
      rw [Subsingleton.elim m 0, Subsingleton.elim m' 0, LocalizedModule.zero_mk,
        LocalizedModule.zero_mk]

end Len

end PI.Dv.ProjAW
