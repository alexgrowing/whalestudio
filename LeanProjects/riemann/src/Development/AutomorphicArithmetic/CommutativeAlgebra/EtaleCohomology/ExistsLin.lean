import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.ExistsGlRep
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.AdmissiblePi
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.NegVan
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.GoodOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.BrauerTraceSplitting.HeckeCl
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.BrauerTraceSplitting.AnnModel
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtSideGoodHolds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.LocTowerHolds
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.EtaleDualityTraceIsomorphism

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N UpperTheory.Gal.Int.Geo UpperTheory.Gal.Seam UpperTheory.Gal.crystallineComparison UpperTheory.Ru.crystallineComparison
open GlobalTheory.GalV (HTower Htot hop galV galTot pullTot)
open Module TensorProduct

section Alg

open TensorProduct

private theorem deg_bound {F L : Type*} [Field F] [Field L] [Algebra F L] {A : ℤ → Type*} [∀ n, AddCommGroup (A n)]
    [∀ n, Module F (A n)] (hneg : ∀ n : ℤ, n < 0 → Subsingleton (A n)) (y : L ⊗[F] DirectSum ℤ A) :
    ∃ N : ℕ, ∀ N' : ℕ, N ≤ N' →
      y ∈ Submodule.baseChange L (⨆ j : Fin N', LinearMap.range (DirectSum.lof F ℤ A ((j : ℕ) : ℤ))) := by
  have hx : ∀ x : DirectSum ℤ A, ∃ N : ℕ, ∀ N' : ℕ, N ≤ N' →
      x ∈ ⨆ j : Fin N', LinearMap.range (DirectSum.lof F ℤ A ((j : ℕ) : ℤ)) := fun x => by
    induction x using DirectSum.induction_on with
    | zero => exact ⟨0, fun _ _ => zero_mem _⟩
    | of i z =>
      rcases lt_or_ge i 0 with hi | hi
      · haveI := hneg i hi
        refine ⟨0, fun _ _ => ?_⟩
        rw [Subsingleton.elim z 0, map_zero]
        exact zero_mem _
      · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hi
        refine ⟨k + 1, fun N' hN' => ?_⟩
        exact Submodule.mem_iSup_of_mem (⟨k, by omega⟩ : Fin N') ⟨z, rfl⟩
    | add a b ha hb =>
      obtain ⟨Na, ha⟩ := ha
      obtain ⟨Nb, hb⟩ := hb
      exact ⟨max Na Nb, fun N' h => add_mem (ha N' (le_trans (le_max_left _ _) h)) (hb N' (le_trans (le_max_right _ _) h))⟩
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, fun _ _ => zero_mem _⟩
  | tmul t x =>
    obtain ⟨N, hN⟩ := hx x
    exact ⟨N, fun N' h => Submodule.tmul_mem_baseChange_of_mem t (hN N' h)⟩
  | add a b ha hb =>
    obtain ⟨Na, ha⟩ := ha
    obtain ⟨Nb, hb⟩ := hb
    exact ⟨max Na Nb, fun N' h => add_mem (ha N' (le_trans (le_max_left _ _) h)) (hb N' (le_trans (le_max_right _ _) h))⟩

private theorem exists_lin {F L : Type*} [Field F] [Field L] [Algebra F L] {V W : Type*} [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W] (Φ : V →ₗ[F] W) {a : ℕ} (y : Fin a → L ⊗[F] W)
    (hy : ∀ i, y i ∈ LinearMap.range (Φ.baseChange L)) :
    ∃ b : (Fin a → L) →ₗ[L] L ⊗[F] V, ∀ x, Φ.baseChange L (b x) = ∑ i, x i • y i := by
  choose w hw using hy
  refine ⟨Fintype.linearCombination L w, fun x => ?_⟩
  simp only [Fintype.linearCombination_apply, map_sum, map_smul, hw]

private theorem lin_inj {F L : Type*} [Field F] [Field L] [Algebra F L] {V W : Type*} [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W] (Φ : V →ₗ[F] W) {a : ℕ} (y : Fin a → L ⊗[F] W) (hl : LinearIndependent L y)
    (b : (Fin a → L) →ₗ[L] L ⊗[F] V) (hb : ∀ x, Φ.baseChange L (b x) = ∑ i, x i • y i) : Function.Injective b := by
  refine (injective_iff_map_eq_zero b).2 fun x hx => ?_
  have h0 : ∑ i, x i • y i = 0 := by rw [← hb, hx, map_zero]
  funext i
  exact Fintype.linearIndependent_iff.1 hl x h0 i

private theorem lin_equiv {F L : Type*} [Field F] [Field L] [Algebra F L] {V W : Type*} [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W] (Φ : V →ₗ[F] W) (hΦ : Function.Injective (Φ.baseChange L)) {a : ℕ} (y : Fin a → L ⊗[F] W)
    (b : (Fin a → L) →ₗ[L] L ⊗[F] V) (hb : ∀ x, Φ.baseChange L (b x) = ∑ i, x i • y i)
    (r : V →ₗ[F] V) (g : W →ₗ[F] W) (hc : g ∘ₗ Φ = Φ ∘ₗ r) (R : Matrix (Fin a) (Fin a) L)
    (hR : ∀ j, g.baseChange L (y j) = ∑ i, R i j • y i) (x : Fin a → L) :
    b (R.mulVec x) = r.baseChange L (b x) := by
  apply hΦ
  have h1 : Φ.baseChange L (r.baseChange L (b x)) = g.baseChange L (Φ.baseChange L (b x)) := by
    have := LinearMap.congr_fun (congrArg (LinearMap.baseChange L) hc) (b x)
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp] at this
    exact this.symm
  rw [h1, hb, hb, map_sum]
  simp only [map_smul, hR, Matrix.mulVec, dotProduct, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [mul_comm]

private theorem lin_eig {F L : Type*} [Field F] [Field L] [Algebra F L] [CharZero L] {V W : Type*} [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W] (Φ : V →ₗ[F] W) (hΦ : Function.Injective (Φ.baseChange L)) {a : ℕ} (y : Fin a → L ⊗[F] W)
    (b : (Fin a → L) →ₗ[L] L ⊗[F] V) (hb : ∀ x, Φ.baseChange L (b x) = ∑ i, x i • y i)
    (t : V →ₗ[F] V) (h : W →ₗ[F] W) (m : ℕ) (hm : m ≠ 0) (hc : h ∘ₗ Φ = (m : F) • (Φ ∘ₗ t)) (θ ϑ : L) (hθ : θ = m * ϑ)
    (hy : ∀ i, h.baseChange L (y i) = θ • y i) (x : Fin a → L) :
    t.baseChange L (b x) = ϑ • b x := by
  apply hΦ
  have h1 : h.baseChange L (Φ.baseChange L (b x)) = (m : L) • Φ.baseChange L (t.baseChange L (b x)) := by
    have := LinearMap.congr_fun (congrArg (LinearMap.baseChange L) hc) (b x)
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_smul, LinearMap.baseChange_comp] at this
    rw [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.comp_apply] at this
    rw [this, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  have h2 : h.baseChange L (Φ.baseChange L (b x)) = θ • Φ.baseChange L (b x) := by
    rw [hb, map_sum]
    simp only [map_smul, hy, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  rw [h2, hθ, mul_smul] at h1
  have hm' : (m : L) ≠ 0 := Nat.cast_ne_zero.2 hm
  rw [map_smul]
  exact (smul_right_injective _ hm' h1).symm

private theorem sum_comp {F : Type*} [Field F] {I : Type*} [Fintype I] [DecidableEq I] {U : I → Type*} [∀ i, AddCommGroup (U i)]
    [∀ i, Module F (U i)] {W : Type*} [AddCommGroup W] [Module F W] (φ : ∀ i, U i →ₗ[F] W) (h : W →ₗ[F] W)
    (c : F) (t : ∀ i, U i →ₗ[F] U i) (t' : (∀ i, U i) →ₗ[F] ∀ i, U i) (ht : ∀ x i, t' x i = t i (x i))
    (hc : ∀ i, h ∘ₗ φ i = c • (φ i ∘ₗ t i)) :
    h ∘ₗ (∑ i, φ i ∘ₗ LinearMap.proj i) = c • ((∑ i, φ i ∘ₗ LinearMap.proj i) ∘ₗ t') := by
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.proj_apply, map_sum, ht, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => by
    have := LinearMap.congr_fun (hc i) (x i)
    simpa using this

private def piRep {F G : Type*} [Field F] [Group G] {I : Type*} {U : I → Type*} [∀ i, AddCommGroup (U i)] [∀ i, Module F (U i)]
    (ρ : ∀ i, Representation F G (U i)) : Representation F G (∀ i, U i) where
  toFun g := LinearMap.pi fun i => ρ i g ∘ₗ LinearMap.proj i
  map_one' := by
    refine LinearMap.ext fun x => funext fun i => ?_
    simp
  map_mul' g h := by
    refine LinearMap.ext fun x => funext fun i => ?_
    simp

end Alg

section Alg2

open TensorProduct

private theorem e_facts {F : Type*} [Field F] {A : ℤ → Type*} [∀ n, AddCommGroup (A n)] [∀ n, Module F (A n)] (N : ℕ)
    (d : Fin N → ℕ) (β : ∀ i : Fin N, Module.Basis (Fin (d i)) F (A ((i : ℕ) : ℤ)))
    (e : (∀ i : Fin N, Fin (d i) → F) →ₗ[F] DirectSum ℤ A)
    (he : e = ∑ i : Fin N, (DirectSum.lof F ℤ A ((i : ℕ) : ℤ)) ∘ₗ (β i).equivFun.symm.toLinearMap ∘ₗ LinearMap.proj i) :
    Function.Injective e ∧ (⨆ j : Fin N, LinearMap.range (DirectSum.lof F ℤ A ((j : ℕ) : ℤ))) ≤ LinearMap.range e := by
  classical
  constructor
  · refine (injective_iff_map_eq_zero e).2 fun x hx => ?_
    funext i
    have h1 : DirectSum.component F ℤ A ((i : ℕ) : ℤ) (e x) = (β i).equivFun.symm (x i) := by
      rw [he]
      simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply, map_sum]
      rw [Finset.sum_eq_single i]
      · simp [DirectSum.component.lof_self]
      · intro k _ hk
        have hne : ((i : ℕ) : ℤ) ≠ ((k : ℕ) : ℤ) := fun h => hk (Fin.ext (by exact_mod_cast h.symm))
        simp [DirectSum.component.of, hne]
        intro h
        exact absurd (Fin.ext h) hk
      · simp
    rw [hx, map_zero] at h1
    have := (β i).equivFun.symm.injective (h1.symm.trans (map_zero _).symm)
    simpa using this
  · refine iSup_le fun j => ?_
    rintro _ ⟨v, rfl⟩
    refine ⟨Pi.single j ((β j).equivFun v), ?_⟩
    rw [he]
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hk
      simp [Pi.single_eq_of_ne hk]
    · simp

private theorem comp_facts {F L : Type*} [Field F] [Field L] [Algebra F L] {V D W : Type*} [AddCommGroup V] [Module F V]
    [AddCommGroup D] [Module F D] [AddCommGroup W] [Module F W] (e : V →ₗ[F] D) (he : Function.Injective e)
    (p : D →ₗ[F] W) (hp : Function.Injective (p.baseChange L)) :
    Function.Injective ((p ∘ₗ e).baseChange L) ∧
      ∀ (P : Submodule F D), P ≤ LinearMap.range e → ∀ z ∈ P.baseChange L,
        p.baseChange L z ∈ LinearMap.range ((p ∘ₗ e).baseChange L) := by
  have hc : (p ∘ₗ e).baseChange L = p.baseChange L ∘ₗ e.baseChange L := LinearMap.baseChange_comp _ _
  refine ⟨?_, fun P hP z hz => ?_⟩
  · rw [hc]
    have h2 : Function.Injective (e.baseChange L) := by
      rw [LinearMap.baseChange_eq_ltensor]
      exact Module.Flat.lTensor_preserves_injective_linearMap e he
    exact hp.comp h2
  · have h3 : z ∈ LinearMap.range (e.baseChange L) := by
      have h4 : P.baseChange L ≤ LinearMap.range (e.baseChange L) := by
        rw [Submodule.baseChange_eq_span, Submodule.span_le]
        rintro _ ⟨x, hx, rfl⟩
        obtain ⟨v, rfl⟩ := hP hx
        exact ⟨(1 : L) ⊗ₜ[F] v, by simp⟩
      exact h4 hz
    obtain ⟨w, rfl⟩ := h3
    exact ⟨w, by rw [hc]; rfl⟩

end Alg2

section Core

open TensorProduct

private theorem core {F L : Type*} [Field F] [Field L] [Algebra F L] [CharZero L] {A : ℤ → Type*} [∀ n, AddCommGroup (A n)]
    [∀ n, Module F (A n)] (hneg : ∀ n : ℤ, n < 0 → Subsingleton (A n)) {W : Type*} [AddCommGroup W] [Module F W]
    (p : DirectSum ℤ A →ₗ[F] W) (hp : Function.Injective (p.baseChange L)) {a : ℕ} (y : Fin a → L ⊗[F] W)
    (hl : LinearIndependent L y) (hy : ∀ i, y i ∈ LinearMap.range (p.baseChange L)) :
    ∃ N : ℕ, ∀ (d : Fin N → ℕ) (β : ∀ i : Fin N, Module.Basis (Fin (d i)) F (A ((i : ℕ) : ℤ))),
      ∃ b : (Fin a → L) →ₗ[L] L ⊗[F] (∀ i : Fin N, Fin (d i) → F), Function.Injective b ∧
        (∀ (r : ∀ i : Fin N, (Fin (d i) → F) →ₗ[F] (Fin (d i) → F))
          (r' : (∀ i : Fin N, Fin (d i) → F) →ₗ[F] ∀ i : Fin N, Fin (d i) → F), (∀ x i, r' x i = r i (x i)) →
          ∀ g : W →ₗ[F] W, (∀ (i : Fin N) u, g (p (DirectSum.lof F ℤ A ((i : ℕ) : ℤ) ((β i).equivFun.symm u))) =
            p (DirectSum.lof F ℤ A ((i : ℕ) : ℤ) ((β i).equivFun.symm (r i u)))) →
          ∀ R : Matrix (Fin a) (Fin a) L, (∀ j, g.baseChange L (y j) = ∑ i, R i j • y i) →
          ∀ x, b (R.mulVec x) = r'.baseChange L (b x)) ∧
        (∀ (t : ∀ i : Fin N, (Fin (d i) → F) →ₗ[F] (Fin (d i) → F))
          (t' : (∀ i : Fin N, Fin (d i) → F) →ₗ[F] ∀ i : Fin N, Fin (d i) → F), (∀ x i, t' x i = t i (x i)) →
          ∀ (h : W →ₗ[F] W) (m : ℕ), m ≠ 0 → (∀ (i : Fin N) u, h (p (DirectSum.lof F ℤ A ((i : ℕ) : ℤ) ((β i).equivFun.symm u))) =
            (m : F) • p (DirectSum.lof F ℤ A ((i : ℕ) : ℤ) ((β i).equivFun.symm (t i u)))) →
          ∀ θ ϑ : L, θ = m * ϑ → (∀ i, h.baseChange L (y i) = θ • y i) →
          ∀ x, t'.baseChange L (b x) = ϑ • b x) := by
  classical
  choose z hz using hy
  choose Nf hNf using fun i => deg_bound (F := F) (L := L) hneg (z i)
  refine ⟨Finset.univ.sup Nf, fun d β => ?_⟩
  have hle : ∀ i, Nf i ≤ Finset.univ.sup Nf := fun i => Finset.le_sup (f := Nf) (Finset.mem_univ i)
  generalize Finset.univ.sup Nf = N at d β hle
  let e : (∀ i : Fin N, Fin (d i) → F) →ₗ[F] DirectSum ℤ A :=
    ∑ i : Fin N, (DirectSum.lof F ℤ A ((i : ℕ) : ℤ)) ∘ₗ (β i).equivFun.symm.toLinearMap ∘ₗ LinearMap.proj i
  obtain ⟨heI, heR⟩ := e_facts N d β e rfl
  obtain ⟨hΦ, hR⟩ := comp_facts (L := L) e heI p hp
  let φ : ∀ i : Fin N, (Fin (d i) → F) →ₗ[F] W := fun i =>
    p ∘ₗ (DirectSum.lof F ℤ A ((i : ℕ) : ℤ)) ∘ₗ (β i).equivFun.symm.toLinearMap
  have hφ : p ∘ₗ e = ∑ i : Fin N, φ i ∘ₗ LinearMap.proj i := by
    refine LinearMap.ext fun x => ?_
    simp [e, φ, map_sum]
  have hy' : ∀ i, y i ∈ LinearMap.range ((p ∘ₗ e).baseChange L) := fun i => by
    rw [← hz i]
    exact hR _ heR _ (hNf i N (hle i))
  obtain ⟨b, hb⟩ := exists_lin (L := L) (p ∘ₗ e) y hy'
  refine ⟨b, lin_inj (p ∘ₗ e) y hl b hb, fun r r' hr g hg R hRg x => ?_, fun t t' ht h m hm hh θ ϑ hθ hyh x => ?_⟩
  · have hc : g ∘ₗ (p ∘ₗ e) = (p ∘ₗ e) ∘ₗ r' := by
      have := sum_comp φ g (1 : F) r r' hr (fun i => LinearMap.ext fun u => by
        simpa [φ] using hg i u)
      rw [one_smul, ← hφ] at this
      exact this
    exact lin_equiv (p ∘ₗ e) hΦ y b hb r' g hc R hRg x
  · have hc : h ∘ₗ (p ∘ₗ e) = (m : F) • ((p ∘ₗ e) ∘ₗ t') := by
      have := sum_comp φ h (m : F) t t' ht (fun i => LinearMap.ext fun u => by
        simpa [φ] using hh i u)
      rw [← hφ] at this
      exact this
    exact lin_eig (p ∘ₗ e) hΦ y b hb t' h m hm hc θ ϑ hθ hyh x

end Core

private theorem basis_rel {F V : Type*} [Field F] [AddCommGroup V] [Module F V] {d : ℕ} (β : Module.Basis (Fin d) F V)
    (r : (Fin d → F) →ₗ[F] (Fin d → F)) (s : V →ₗ[F] V) (h : ∀ v, r (β.equivFun v) = β.equivFun (s v)) (u : Fin d → F) :
    s (β.equivFun.symm u) = β.equivFun.symm (r u) := by
  have h1 := h (β.equivFun.symm u)
  rw [LinearEquiv.apply_symm_apply] at h1
  rw [h1, LinearEquiv.symm_apply_apply]

private theorem gal_inTot {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (M : Model l K) (j : ℕ)
    (g : K.fixingSubgroup) (v : M.V j) :
    galTot l (PadicAlgCl l) M.q (IntermediateField.fixingSubgroupEquiv K g) (Br.inTot M j v) = Br.inTot M j (M.act j g v) :=
  DirectSum.lmap_lof _ _ _

theorem UpperTheory.Ru.crystallineComparison.geoLoc :
    UpperTheory.Ru.crystallineComparison.GeoLoc := by
  intro hF hCr l _ P AI hT K _ _ f hf hc H θ hN C hOn n ϑ hCg a ρ₁ hMat
  haveI : FiniteDimensional ℚ_[l] K.1 := K.2
  obtain ⟨hinj, hle, heq⟩ := UpperTheory.Gal.Seam.pieceIn_holds l K.1 (Om l) H θ hN C hOn
  have hSm : (mod C).Sm := ⟨goodOf l K.1 (mod C) C.smooth C.proj, C.smooth⟩
  have hfin : ∀ j, FiniteDimensional ℚ_[l] ((mod C).V j) := fun j => (UpperTheory.Gal.KunnethLefschetz.Top.etSide_sm_holds l K.1).fin (mod C) hSm j
  obtain ⟨ϖ, Tc, γ, m, hϖ, hPt, hTc⟩ := hCg
  have hr : ∀ i, (Tc i).r ≫ (mod C).p = (Tc i).p ≫ (mod C).p := fun i => (hTc i).1
  have hA : ∀ i, ∃ A : ∀ j : ℕ, (mod C).V j →ₗ[ℚ_[l]] (mod C).V j, ∀ j, IsHk (mod C) (Tc i) (hr i) j (A j) ∧
      ∀ v, hop l H (PadicAlgCl l) (γ i) (pullTot l (sch.map (toMod C)) (Br.inTot (mod C) j v)) =
        (m i : ℚ_[l]) • pullTot l (sch.map (toMod C)) (Br.inTot (mod C) j (A j v)) := fun i => by
    obtain ⟨d, hd⟩ := hN.2.2 (γ i)
    exact Br.heckeCl l K.1 (Om l) H θ C (Tc i) (hr i) (γ i) (m i) d hd (hTc i).2.1
  choose A hAk using hA
  obtain ⟨b₀, hb₀⟩ := hMat
  obtain ⟨N, hcore⟩ := core (F := ℚ_[l]) (L := Om l) (A := fun n : ℤ => HQ l (mod C).spc n 0) (fun n hn => negVan l _ n hn)
    (pullTot l (sch.map (toMod C))) hinj (fun i => (b₀ i).1)
    (b₀.linearIndependent.map' (Submodule.subtype _) (Submodule.ker_subtype _)) (fun i => hle (b₀ i).2)
  obtain ⟨d, ⟨β⟩⟩ : ∃ d : Fin N → ℕ, Nonempty (∀ i : Fin N, Module.Basis (Fin (d i)) ℚ_[l] ((mod C).V i)) :=
    ⟨fun i => Module.finrank ℚ_[l] ((mod C).V i), ⟨fun i => haveI := hfin i; Module.finBasis ℚ_[l] ((mod C).V i)⟩⟩
  have hcr := fun i : Fin N => crysCopy hCr l P AI hT K (mod C) hSm i (d i) (β i)
  choose ρc hρ hcrys using hcr
  obtain ⟨Tk, hTk⟩ : ∃ Tk : ∀ i : Fin N, ℕ → End ℚ_[l] (Fin (d i) → ℚ_[l]), ∀ (i : Fin N) (k : Fin (n + 1)),
      Tk i k = (β i).equivFun.toLinearMap ∘ₗ A k i ∘ₗ (β i).equivFun.symm.toLinearMap :=
    ⟨fun i k => if h : k ≤ n then (β i).equivFun.toLinearMap ∘ₗ A ⟨k, Nat.lt_succ_of_le h⟩ i ∘ₗ (β i).equivFun.symm.toLinearMap else 0,
      fun i k => dif_pos (Nat.le_of_lt_succ k.2)⟩
  have hTv : ∀ (i : Fin N) (k : Fin (n + 1)) v, Tk i k ((β i).equivFun v) = (β i).equivFun (A k i v) := fun i k v => by
    rw [hTk]
    simp
  have hann : ∀ i : Fin N, AnnD (σCr P K) (ψCr P f) (l ^ f) n (ρc i) (Tk i) := fun i =>
    Br.annModel hF l P AI hT K f hf hc ϖ hϖ (mod C) hSm n i Tc hr hPt (fun k => A k i) (fun k => (hAk k i).1) _ (β i).equivFun (ρc i) (hρ i)
      (Tk i) (fun k v => hTv i k v)
  obtain ⟨ρ', hρ'⟩ : ∃ ρ' : Representation ℚ_[l] ↥(GK K) (∀ i : Fin N, Fin (d i) → ℚ_[l]), ∀ g x i, ρ' g x i = ρc i g (x i) :=
    ⟨piRep ρc, fun _ _ _ => rfl⟩
  obtain ⟨T', hT'⟩ : ∃ T' : ℕ → End ℚ_[l] (∀ i : Fin N, Fin (d i) → ℚ_[l]), ∀ j x i, T' j x i = Tk i j (x i) :=
    ⟨fun k => LinearMap.pi fun i => Tk i k ∘ₗ LinearMap.proj i, fun _ _ _ => rfl⟩
  have hPi := annPi l P K (Fin N) (fun i => Fin (d i) → ℚ_[l]) ρc f (l ^ f) n Tk ρ' T' hρ' hT'
  obtain ⟨b, hbI, hbG, hbT⟩ := hcore d β
  refine ⟨∀ i : Fin N, Fin (d i) → ℚ_[l], inferInstance, inferInstance, inferInstance, ρ', T', b, hPi.1 hcrys, hPi.2 hann,
    hbI, fun g x => ?_, fun j hj x => ?_⟩
  · refine hbG (fun i => ρc i g) (ρ' g) (hρ' g) (galTot l (PadicAlgCl l) H.q (IntermediateField.fixingSubgroupEquiv K.1 g))
      (fun i u => ?_) _ (fun j => hb₀ _ j) x
    have h2 := basis_rel (β i) (ρc i g) ((mod C).act i g) (hρ i g) u
    have h3 := gal_inTot (mod C) i g ((β i).equivFun.symm u)
    rw [h2] at h3
    exact (LinearMap.congr_fun (heq (IntermediateField.fixingSubgroupEquiv K.1 g)) _).trans
      (congrArg (pullTot l (sch.map (toMod C))) h3)
  · have hk : j < n + 1 := Nat.lt_succ_of_le hj
    refine hbT (fun i => Tk i j) (T' j) (hT' j) (hop l H (PadicAlgCl l) (γ ⟨j, hk⟩)) (m ⟨j, hk⟩) (hTc ⟨j, hk⟩).2.1.1.ne'
      (fun i u => ?_) (θ (γ ⟨j, hk⟩)) (ϑ j) (hTc ⟨j, hk⟩).2.2 (fun i => ?_) x
    · have h2 := basis_rel (β i) (Tk i j) (A ⟨j, hk⟩ i) (hTv i ⟨j, hk⟩) u
      have h1 := (hAk ⟨j, hk⟩ i).2 ((β i).equivFun.symm u)
      rw [h2] at h1
      exact h1
    · exact Module.End.mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 (b₀ i).2 (γ ⟨j, hk⟩))
