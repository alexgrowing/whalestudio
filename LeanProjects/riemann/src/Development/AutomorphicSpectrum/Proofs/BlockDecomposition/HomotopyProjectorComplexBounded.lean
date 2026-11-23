import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsFiniteProjectiveComplexQuasiIso

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.PerfRetract

section Elements

variable {R : Type} [CommRing R] {K C E : ℕ → Type}
  [∀ p, AddCommGroup (K p)] [∀ p, AddCommGroup (C p)] [∀ p, AddCommGroup (E p)]
  [∀ p, Module R (K p)] [∀ p, Module R (C p)] [∀ p, Module R (E p)]

theorem qIsoAt_of_retract
    (dK : ∀ p, K p →ₗ[R] K (p + 1)) (dC : ∀ p, C p →ₗ[R] C (p + 1))
    (dE : ∀ p, E p →ₗ[R] E (p + 1))
    (φ : ∀ p, K p →ₗ[R] C p) (inc : ∀ p, C p →ₗ[R] E p) (r : ∀ p, E p →ₗ[R] C p)
    (h : ∀ p, E (p + 1) →ₗ[R] E p)
    (hc : ConeExact (K := K) (C := C) (fun p => dK p) (fun p => dC p) (fun p => φ p))
    (hri : ∀ p, r p ∘ₗ inc p = LinearMap.id)
    (hinc : ∀ p, inc (p + 1) ∘ₗ dC p = dE p ∘ₗ inc p)
    (hr : ∀ p, r (p + 1) ∘ₗ dE p = dC p ∘ₗ r p)
    (h0 : inc 0 ∘ₗ r 0 = LinearMap.id + h 0 ∘ₗ dE 0)
    (hs : ∀ p, inc (p + 1) ∘ₗ r (p + 1) =
      LinearMap.id + dE p ∘ₗ h p + h (p + 1) ∘ₗ dE (p + 1)) :
    QIsoAt (0 : R →ₗ[R] K 0) (dK 0) (0 : R →ₗ[R] E 0) (dE 0) (inc 0 ∘ₗ φ 0) ∧
    ∀ n, QIsoAt (dK n) (dK (n + 1)) (dE n) (dE (n + 1)) (inc (n + 1) ∘ₗ φ (n + 1)) := by
  have hri' : ∀ p x, r p (inc p x) = x := fun p x => LinearMap.congr_fun (hri p) x
  have hinc' : ∀ p x, inc (p + 1) (dC p x) = dE p (inc p x) := fun p x => LinearMap.congr_fun (hinc p) x
  have hr' : ∀ p x, r (p + 1) (dE p x) = dC p (r p x) := fun p x => LinearMap.congr_fun (hr p) x
  have h0' : ∀ x, inc 0 (r 0 x) = x + h 0 (dE 0 x) := fun x => LinearMap.congr_fun h0 x
  have hs' : ∀ p x, inc (p + 1) (r (p + 1) x) = x + dE p (h p x) + h (p + 1) (dE (p + 1) x) :=
    fun p x => LinearMap.congr_fun (hs p) x
  refine ⟨⟨?_, ?_⟩, fun n => ⟨?_, ?_⟩⟩
  · rintro x hx ⟨y, hy⟩
    have h1 : inc 0 (φ 0 x) = 0 := by simpa using hy.symm
    have h2 : φ 0 x = 0 := by rw [← hri' 0 (φ 0 x), h1, map_zero]
    exact ⟨0, by simpa using (hc.inj x h2 hx).symm⟩
  · intro z hz
    obtain ⟨x, hx, hx'⟩ := hc.zero (r 0 z) 0
      (by change dC 0 (r 0 z) = φ 1 0; rw [← hr', hz]; simp) (by simp)
    have hx2 : φ 0 x = r 0 z := hx
    refine ⟨x, 0, hx', ?_⟩
    simp [hx2, h0', hz]
  · rintro x hx ⟨y, hy⟩
    have hy' : dE n y = inc (n + 1) (φ (n + 1) x) := hy
    have h1 : dC n (r n y) = φ (n + 1) x := by rw [← hr', hy', hri']
    cases n with
    | zero =>
      obtain ⟨w, -, hw⟩ := hc.zero (r 0 y) x h1 hx
      exact ⟨w, hw⟩
    | succ m =>
      obtain ⟨-, w, -, hw⟩ := hc.succ m (r (m + 1) y) x h1 hx
      exact ⟨w, hw⟩
  · intro z hz
    obtain ⟨c, k, hck, hk⟩ := hc.succ n (r (n + 1) z) 0
      (by change dC (n + 1) (r (n + 1) z) = φ (n + 2) 0; rw [← hr', hz]; simp) (by simp)
    have hck' : dC n c + φ (n + 1) k = r (n + 1) z := hck
    refine ⟨k, h n z - inc n c, hk, ?_⟩
    have h3 : φ (n + 1) k = r (n + 1) z - dC n c := eq_sub_of_add_eq' hck'
    simp only [LinearMap.comp_apply, h3, map_sub, hs', hinc', hz, map_zero, add_zero]
    abel

end Elements

section Complex

variable {R : Type} [CommRing R] {E : ℕ → Type} [∀ n, AddCommGroup (E n)] [∀ n, Module R (E n)]

theorem finite_homology_of_surjective (C : CochainComplex (ModuleCat.{0} R) ℕ) (i j k : ℕ)
    (hi : (ComplexShape.up ℕ).prev j = i) (hk : (ComplexShape.up ℕ).next j = k)
    (W : Type) [AddCommGroup W] [Module R W] [Module.Finite R W]
    (f : W →ₗ[R] (LinearMap.ker (C.d j k).hom ⧸
      (LinearMap.range (C.d i j).hom).comap (LinearMap.ker (C.d j k).hom).subtype))
    (hf : Function.Surjective f) : Module.Finite R (C.homology j) := by
  have e := (C.homologyIsoSc' i j k hi hk ≪≫ (C.sc' i j k).moduleCatHomologyIso).toLinearEquiv
  have h1 : Module.Finite R (LinearMap.ker (C.d j k).hom ⧸
      (LinearMap.range (C.d i j).hom).comap (LinearMap.ker (C.d j k).hom).subtype) :=
    Module.Finite.of_surjective f hf
  have h2 : Module.Finite R (LinearMap.ker (C.d j k).hom ⧸
      LinearMap.range (C.sc' i j k).moduleCatToCycles) := by
    refine Module.Finite.equiv (Submodule.quotEquivOfEq
      ((LinearMap.range (C.d i j).hom).comap (LinearMap.ker (C.d j k).hom).subtype)
      (LinearMap.range (C.sc' i j k).moduleCatToCycles) ?_)
    ext x
    exact ⟨fun ⟨y, hy⟩ => ⟨y, Subtype.ext hy⟩, fun ⟨y, hy⟩ => ⟨y, congrArg Subtype.val hy⟩⟩
  have h3 : Module.Finite R (C.sc' i j k).moduleCatLeftHomologyData.H := h2
  exact Module.Finite.equiv e.symm

noncomputable def cyclesMap (d : ∀ n, E n →ₗ[R] E (n + 1))
    (C : CochainComplex (ModuleCat.{0} R) ℕ) (r : ∀ n, E n →ₗ[R] C.X n)
    (hr : ∀ p, r (p + 1) ∘ₗ d p = (C.d p (p + 1)).hom ∘ₗ r p) (j : ℕ) :
    LinearMap.ker (d j) →ₗ[R] LinearMap.ker (C.d j (j + 1)).hom :=
  (r j ∘ₗ (LinearMap.ker (d j)).subtype).codRestrict _ fun x => by
    have h1 := LinearMap.congr_fun (hr j) x.1
    simp only [LinearMap.comp_apply] at h1
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply, ← h1,
      LinearMap.mem_ker.1 x.2, map_zero]

theorem cyclesMap_surjective (d : ∀ n, E n →ₗ[R] E (n + 1))
    (C : CochainComplex (ModuleCat.{0} R) ℕ) (inc : ∀ n, C.X n →ₗ[R] E n)
    (r : ∀ n, E n →ₗ[R] C.X n) (hri : ∀ p, r p ∘ₗ inc p = LinearMap.id)
    (hinc : ∀ p, inc (p + 1) ∘ₗ (C.d p (p + 1)).hom = d p ∘ₗ inc p)
    (hr : ∀ p, r (p + 1) ∘ₗ d p = (C.d p (p + 1)).hom ∘ₗ r p) (j : ℕ) :
    Function.Surjective (cyclesMap d C r hr j) := by
  intro y
  have h1 := LinearMap.congr_fun (hinc j) y.1
  simp only [LinearMap.comp_apply] at h1
  refine ⟨⟨inc j y.1, ?_⟩, Subtype.ext ?_⟩
  · rw [LinearMap.mem_ker, ← h1, LinearMap.mem_ker.1 y.2, map_zero]
  · exact LinearMap.congr_fun (hri j) y.1

theorem finite_homology_of_retract (d : ∀ n, E n →ₗ[R] E (n + 1))
    (C : CochainComplex (ModuleCat.{0} R) ℕ) (inc : ∀ n, C.X n →ₗ[R] E n)
    (r : ∀ n, E n →ₗ[R] C.X n) (hri : ∀ p, r p ∘ₗ inc p = LinearMap.id)
    (hinc : ∀ p, inc (p + 1) ∘ₗ (C.d p (p + 1)).hom = d p ∘ₗ inc p)
    (hr : ∀ p, r (p + 1) ∘ₗ d p = (C.d p (p + 1)).hom ∘ₗ r p)
    (hf0 : Module.Finite R (LinearMap.ker (d 0)))
    (hfs : ∀ n, Module.Finite R (LinearMap.ker (d (n + 1)) ⧸
      (LinearMap.range (d n)).comap (LinearMap.ker (d (n + 1))).subtype)) (p : ℕ) :
    Module.Finite R (C.homology p) := by
  have hsurj := cyclesMap_surjective d C inc r hri hinc hr
  cases p with
  | zero =>
    refine finite_homology_of_surjective C 0 0 1 (by simp) (by simp) (LinearMap.ker (d 0))
      (Submodule.mkQ _ ∘ₗ cyclesMap d C r hr 0) ?_
    exact (Submodule.mkQ_surjective _).comp (hsurj 0)
  | succ p =>
    have := hfs p
    refine finite_homology_of_surjective C p (p + 1) (p + 1 + 1) (by simp) (by simp)
      (LinearMap.ker (d (p + 1)) ⧸
        (LinearMap.range (d p)).comap (LinearMap.ker (d (p + 1))).subtype)
      (Submodule.mapQ ((LinearMap.range (d p)).comap (LinearMap.ker (d (p + 1))).subtype)
        ((LinearMap.range (C.d p (p + 1)).hom).comap
          (LinearMap.ker (C.d (p + 1) (p + 1 + 1)).hom).subtype)
        (cyclesMap d C r hr (p + 1)) ?_) ?_
    · rintro x ⟨y, hy⟩
      refine ⟨r p y, ?_⟩
      have h1 := LinearMap.congr_fun (hr p) y
      simp only [LinearMap.comp_apply] at h1
      rw [← h1, hy]
      rfl
    · intro y
      obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
      obtain ⟨x, rfl⟩ := hsurj (p + 1) y
      exact ⟨Submodule.Quotient.mk x, rfl⟩

end Complex

section Main

variable {R : Type} [CommRing R]

theorem exists_model_of_complex_retract [IsNoetherianRing R] {E : ℕ → Type}
    [∀ n, AddCommGroup (E n)] [∀ n, Module R (E n)] (d : ∀ n, E n →ₗ[R] E (n + 1))
    (e : ∀ n, E n →ₗ[R] E n) (h : ∀ n, E (n + 1) →ₗ[R] E n) (B : ℕ)
    (he0 : e 0 = LinearMap.id + h 0 ∘ₗ d 0)
    (hes : ∀ n, e (n + 1) = LinearMap.id + d n ∘ₗ h n + h (n + 1) ∘ₗ d (n + 1))
    (C : CochainComplex (ModuleCat.{0} R) ℕ) (inc : ∀ n, C.X n →ₗ[R] E n)
    (r : ∀ n, E n →ₗ[R] C.X n) (hri : ∀ p, r p ∘ₗ inc p = LinearMap.id)
    (hinc : ∀ p, inc (p + 1) ∘ₗ (C.d p (p + 1)).hom = d p ∘ₗ inc p)
    (hr : ∀ p, r (p + 1) ∘ₗ d p = (C.d p (p + 1)).hom ∘ₗ r p)
    (hir : ∀ p, inc p ∘ₗ r p = e p)
    (hB : ∀ p, B < p → Limits.IsZero (C.X p)) (hflat : ∀ p, Module.Flat R (C.X p))
    (hfin : ∀ p, Module.Finite R (C.homology p)) :
    ∃ (Q : CochainComplex (ModuleCat.{0} R) ℕ) (ψ : ∀ n, Q.X n →ₗ[R] E n),
      (∀ n, Module.Finite R (Q.X n)) ∧ (∀ n, Module.Projective R (Q.X n)) ∧
      (∀ n, ψ (n + 1) ∘ₗ (Q.d n (n + 1)).hom = d n ∘ₗ ψ n) ∧
      ∀ M : ModuleCat.{0} R,
        QIsoAt (0 : R →ₗ[R] M ⊗[R] Q.X 0) ((Q.d 0 1).hom.lTensor M) (0 : R →ₗ[R] M ⊗[R] E 0)
          ((d 0).lTensor M) ((ψ 0).lTensor M) ∧
        ∀ n, QIsoAt ((Q.d n (n + 1)).hom.lTensor M) ((Q.d (n + 1) (n + 2)).hom.lTensor M)
          ((d n).lTensor M) ((d (n + 1)).lTensor M) ((ψ (n + 1)).lTensor M) := by
  obtain ⟨Q, φ, hQ0, hQfin, -, hQproj, hq, -, -⟩ :=
    GlobalTheory.exists_finite_projective_complex_quasiIso.{0, 0} C B hB hflat hfin
  have hQflat : ∀ p, Module.Flat R (Q.X p) := fun p => by
    have := hQproj p
    infer_instance
  refine ⟨Q, fun n => inc n ∘ₗ (φ.f n).hom, hQfin, hQproj, fun n => ?_, fun M => ?_⟩
  · refine LinearMap.ext fun x => ?_
    have h1 := LinearMap.congr_fun (hinc n) ((φ.f n).hom x)
    have h2 := GlobalTheory.cochain_comm_apply φ n (n + 1) x
    simp only [LinearMap.comp_apply] at h1 ⊢
    rw [← h1, h2]
  · have hc := GlobalTheory.coneExact_lTensor_of_quasiIso φ hQflat hflat B hQ0 hB M
    have key := qIsoAt_of_retract (R := R) (K := fun p => M ⊗[R] Q.X p)
      (C := fun p => M ⊗[R] C.X p) (E := fun p => M ⊗[R] E p)
      (fun p => (Q.d p (p + 1)).hom.lTensor M) (fun p => (C.d p (p + 1)).hom.lTensor M)
      (fun p => (d p).lTensor M) (fun p => (φ.f p).hom.lTensor M)
      (fun p => (inc p).lTensor M) (fun p => (r p).lTensor M) (fun p => (h p).lTensor M) hc
      (fun p => by rw [← LinearMap.lTensor_comp, hri, LinearMap.lTensor_id])
      (fun p => by rw [← LinearMap.lTensor_comp, ← LinearMap.lTensor_comp, hinc])
      (fun p => by rw [← LinearMap.lTensor_comp, ← LinearMap.lTensor_comp, hr])
      (by
        rw [← LinearMap.lTensor_comp, ← LinearMap.lTensor_comp, hir, he0, LinearMap.lTensor_add,
          LinearMap.lTensor_id])
      (fun p => by
        rw [← LinearMap.lTensor_comp, ← LinearMap.lTensor_comp, ← LinearMap.lTensor_comp, hir, hes,
          LinearMap.lTensor_add, LinearMap.lTensor_add, LinearMap.lTensor_id])
    simp only [LinearMap.lTensor_comp]
    exact key

theorem exists_finite_projective_model : ∀ {R : Type} [CommRing R] [IsNoetherianRing R] (E : ℕ → Type) [∀ n, AddCommGroup (E n)]
    [∀ n, Module R (E n)] [∀ n, Module.Flat R (E n)] (d : ∀ n, E n →ₗ[R] E (n + 1))
    (_ : ∀ n, d (n + 1) ∘ₗ d n = 0) (e : ∀ n, E n →ₗ[R] E n) (h : ∀ n, E (n + 1) →ₗ[R] E n) (B : ℕ)
    (_ : ∀ n, e n ∘ₗ e n = e n) (_ : ∀ n, e (n + 1) ∘ₗ d n = d n ∘ₗ e n)
    (_ : e 0 = LinearMap.id + h 0 ∘ₗ d 0)
    (_ : ∀ n, e (n + 1) = LinearMap.id + d n ∘ₗ h n + h (n + 1) ∘ₗ d (n + 1))
    (_ : ∀ n, B < n → e n = 0)
    (_ : Module.Finite R (LinearMap.ker (d 0)))
    (_ : ∀ n, Module.Finite R (LinearMap.ker (d (n + 1)) ⧸
      (LinearMap.range (d n)).comap (LinearMap.ker (d (n + 1))).subtype)),
    ∃ (Q : CochainComplex (ModuleCat.{0} R) ℕ) (ψ : ∀ n, Q.X n →ₗ[R] E n),
      (∀ n, Module.Finite R (Q.X n)) ∧ (∀ n, Module.Projective R (Q.X n)) ∧
      (∀ n, ψ (n + 1) ∘ₗ (Q.d n (n + 1)).hom = d n ∘ₗ ψ n) ∧
      ∀ M : ModuleCat.{0} R,
        QIsoAt (0 : R →ₗ[R] M ⊗[R] Q.X 0) ((Q.d 0 1).hom.lTensor M) (0 : R →ₗ[R] M ⊗[R] E 0)
          ((d 0).lTensor M) ((ψ 0).lTensor M) ∧
        ∀ n, QIsoAt ((Q.d n (n + 1)).hom.lTensor M) ((Q.d (n + 1) (n + 2)).hom.lTensor M)
          ((d n).lTensor M) ((d (n + 1)).lTensor M) ((ψ (n + 1)).lTensor M) := by
  intro R _ _ E _ _ _ d hdd e h B hee hed he0 hes hB hf0 hfs
  have hrange : ∀ n (x : E n), x ∈ LinearMap.range (e n) → e n x = x := by
    rintro n _ ⟨y, rfl⟩
    exact LinearMap.congr_fun (hee n) y
  let dN : ∀ n, LinearMap.range (e n) →ₗ[R] LinearMap.range (e (n + 1)) := fun n =>
    (d n ∘ₗ (LinearMap.range (e n)).subtype).codRestrict _ (by
      rintro ⟨_, y, rfl⟩
      exact ⟨d n y, LinearMap.congr_fun (hed n) y⟩)
  have hdN : ∀ n (x : LinearMap.range (e n)), ((dN n x : LinearMap.range (e (n + 1))) : E (n + 1)) =
      d n x := fun _ _ => rfl
  let C : CochainComplex (ModuleCat.{0} R) ℕ :=
    CochainComplex.of (fun n => ModuleCat.of R (LinearMap.range (e n)))
      (fun n => ModuleCat.ofHom (dN n)) (fun n => by
        refine ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext ?_)
        exact LinearMap.congr_fun (hdd n) x.1)
  have hCd : ∀ p, C.d p (p + 1) = ModuleCat.ofHom (dN p) := fun p => by
    simp [C, CochainComplex.of_d]
  let inc : ∀ n, C.X n →ₗ[R] E n := fun n => (LinearMap.range (e n)).subtype
  let r : ∀ n, E n →ₗ[R] C.X n := fun n => (e n).rangeRestrict
  have hri : ∀ p, r p ∘ₗ inc p = LinearMap.id := fun p => by
    refine LinearMap.ext fun x => Subtype.ext ?_
    exact hrange p _ x.2
  have hinc : ∀ p, inc (p + 1) ∘ₗ (C.d p (p + 1)).hom = d p ∘ₗ inc p := fun p => by
    rw [hCd]
    rfl
  have hr : ∀ p, r (p + 1) ∘ₗ d p = (C.d p (p + 1)).hom ∘ₗ r p := fun p => by
    rw [hCd]
    refine LinearMap.ext fun x => Subtype.ext ?_
    exact LinearMap.congr_fun (hed p) x
  have hflat : ∀ p, Module.Flat R (C.X p) := fun p =>
    Module.Flat.of_retract (inc p) (r p) (hri p)
  refine exists_model_of_complex_retract d e h B he0 hes C inc r hri hinc hr (fun _ => rfl)
    (fun p hp => ?_) hflat (finite_homology_of_retract d C inc r hri hinc hr hf0 hfs)
  refine ModuleCat.isZero_iff_subsingleton.2 ?_
  change Subsingleton (LinearMap.range (e p))
  rw [hB p hp, LinearMap.range_zero]
  infer_instance

end Main

end GlobalTheory.CompanionTheory.PerfRetract
