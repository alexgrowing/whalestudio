import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubPairRight
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsHomLocBijectiveGrSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFinsetSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulEqZeroOfMem
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

theorem grSum_induction {ι R : Type*} [CommRing R] {A : ℤ → Type*} [∀ n, AddCommGroup (A n)]
    [∀ n, Module R (A n)] {x : ι → ∀ n, A n →ₗ[R] A (n + 1)} {hx : OperatorsCommute x}
    {C : GrSum hx → Prop} (m : GrSum hx) (h0 : C 0) (hof : ∀ n a, C (GrSum.of hx n a))
    (hadd : ∀ a b, C a → C b → C (a + b)) : C m :=
  DirectSum.induction_on (β := A) (motive := C) m h0 hof hadd

section Tower

variable {ι : Type} [LinearOrder ι] {R : Type} [CommRing R] {g : ℕ} {ρ : Fin g → R}
  {T : ℕ → ℤ → Finset ι → Type} [∀ e t S, AddCommGroup (T e t S)] [∀ e t S, Module R (T e t S)]
  {res : ∀ e t (S S' : Finset ι), S ⊆ S' → T e t S →ₗ[R] T e t S'}
  {p : ∀ e t S, T (e + 1) t S →ₗ[R] T e t S}
  {mm : ι → ∀ e t S, T e t S →ₗ[R] T e (t + 1) S}

namespace TowerAx

def mulKer (H : TowerAx ρ res p mm) (e : ℕ) (t : ℤ) (S : Finset ι) (hS : S.Nonempty) (r : R)
    (hr : r ∈ Ideal.span (Set.range ρ) ^ (e + 1)) : T (e + 1) t S →ₗ[R] Ks p e t S :=
  LinearMap.codRestrict _ (r • LinearMap.id) fun y => by
    have h := Submodule.smul_mem_smul hr (Submodule.mem_top (x := y))
    rw [← H.ker_eq e t S hS] at h
    exact (mem_Ks hS).2 h

@[simp]
theorem coe_mulKer (H : TowerAx ρ res p mm) (e : ℕ) (t : ℤ) (S : Finset ι) (hS : S.Nonempty)
    (r : R) (hr : r ∈ Ideal.span (Set.range ρ) ^ (e + 1)) (y : T (e + 1) t S) :
    (H.mulKer e t S hS r hr y : T (e + 1) t S) = r • y := rfl

variable (hc : ∀ e S, OperatorsCommute (ι := ι) (R := R) (A := fun t => T e t S)
  fun j t => mm j e t S)

def mulTot (H : TowerAx ρ res p mm) (hc : ∀ e S, OperatorsCommute (ι := ι) (R := R)
    (A := fun t => T e t S) fun j t => mm j e t S) (e : ℕ) (S : Finset ι) (hS : S.Nonempty) (r : R)
    (hr : r ∈ Ideal.span (Set.range ρ) ^ (e + 1)) : GrSum (hc (e + 1) S) →+ H.Tot hc S :=
  DirectSum.toAddMonoid fun t =>
    ((H.ops hc S).of e t).comp (H.mulKer e t S hS r hr).toAddMonoidHom

theorem mulTot_of (H : TowerAx ρ res p mm) (e : ℕ) (S : Finset ι) (hS : S.Nonempty) (r : R)
    (hr : r ∈ Ideal.span (Set.range ρ) ^ (e + 1)) (t : ℤ) (y : T (e + 1) t S) :
    H.mulTot hc e S hS r hr (GrSum.of (hc (e + 1) S) t y) =
      (H.ops hc S).of e t (H.mulKer e t S hS r hr y) :=
  DirectSum.toAddMonoid_of (β := fun t => T (e + 1) t S)
    (fun t => ((H.ops hc S).of e t).comp (H.mulKer e t S hS r hr).toAddMonoidHom) t y

theorem mulTot_X_smul (H : TowerAx ρ res p mm) (e : ℕ) (S : Finset ι) (hS : S.Nonempty) (r : R)
    (hr : r ∈ Ideal.span (Set.range ρ) ^ (e + 1)) (j : ι) (m : GrSum (hc (e + 1) S)) :
    H.mulTot hc e S hS r hr ((MvPolynomial.X j : MvPolynomial ι R) • m) =
      (MvPolynomial.X j : MvPolynomial ι (MvPolynomial (Fin g) R)) •
        H.mulTot hc e S hS r hr m := by
  induction m using grSum_induction with
  | h0 => simp
  | hof t y =>
    rw [GrSum.X_smul_of, mulTot_of, mulTot_of, BiOps.X_smul_of]
    congr 1
    apply Subtype.ext
    change r • mm j (e + 1) t S y = mm j (e + 1) t S (r • y)
    rw [map_smul]
  | hadd a b ha hb => rw [smul_add, map_add, map_add, smul_add, ha, hb]

theorem mulTot_X_pow_smul (H : TowerAx ρ res p mm) (e : ℕ) (S : Finset ι) (hS : S.Nonempty)
    (r : R) (hr : r ∈ Ideal.span (Set.range ρ) ^ (e + 1)) (j : ι) (k : ℕ)
    (m : GrSum (hc (e + 1) S)) :
    H.mulTot hc e S hS r hr ((MvPolynomial.X j : MvPolynomial ι R) ^ k • m) =
      (MvPolynomial.X j : MvPolynomial ι (MvPolynomial (Fin g) R)) ^ k •
        H.mulTot hc e S hS r hr m := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', pow_succ', mul_smul, mul_smul, mulTot_X_smul, ih]

theorem mulKer_res (H : TowerAx ρ res p mm) (e : ℕ) (t : ℤ) {S S' : Finset ι} (h : S ⊆ S')
    (hS : S.Nonempty) (r : R) (hr : r ∈ Ideal.span (Set.range ρ) ^ (e + 1)) (a : T (e + 1) t S) :
    H.mulKer e t S' (hS.mono h) r hr (res (e + 1) t S S' h a) =
      H.resK e t h (H.mulKer e t S hS r hr a) := by
  apply Subtype.ext
  rw [coe_resK, coe_mulKer, coe_mulKer, map_smul]

theorem exists_X_pow_smul_mem_range (H : TowerAx ρ res p mm)
    (hyp : ∀ e S j t (b : T e t (insert j S)), S.Nonempty → ∃ (k : ℕ) (t' : ℤ) (a : T e t' S),
      GrSum.of (hc e (insert j S)) t' (res e t' S (insert j S) (Finset.subset_insert j S) a) =
        (MvPolynomial.X j : MvPolynomial ι R) ^ k • GrSum.of (hc e (insert j S)) t b)
    (S : Finset ι) (j : ι) (hS : S.Nonempty) (e : ℕ) (t : ℤ) (w : T (e + 1) t (insert j S))
    (hw : w ∈ Ideal.span (Set.range ρ) ^ (e + 1) • (⊤ : Submodule R (T (e + 1) t (insert j S)))) :
    ∃ (h : w ∈ Ks p e t (insert j S)) (k : ℕ),
      (MvPolynomial.X j : MvPolynomial ι (MvPolynomial (Fin g) R)) ^ k •
          (H.ops hc (insert j S)).of e t ⟨w, h⟩ ∈
        LinearMap.range (H.resTot hc S (insert j S) (Finset.subset_insert j S)) := by
  have hS' : (insert j S).Nonempty := Finset.insert_nonempty j S
  induction hw using Submodule.smul_induction_on' with
  | smul r hr y _ =>
    obtain ⟨k, t', a, hk⟩ := hyp (e + 1) S j t y hS
    refine ⟨(H.mulKer e t _ hS' r hr y).2, k, (H.ops hc S).of e t' (H.mulKer e t' S hS r hr a), ?_⟩
    have h1 := congrArg (H.mulTot hc e (insert j S) hS' r hr) hk
    rw [mulTot_X_pow_smul, mulTot_of, mulTot_of, mulKer_res H e t' (Finset.subset_insert j S) hS]
      at h1
    rw [resTot_of]
    exact h1
  | add x _ y _ hx hy =>
    obtain ⟨hx', k₁, hk₁⟩ := hx
    obtain ⟨hy', k₂, hk₂⟩ := hy
    refine ⟨add_mem hx' hy', k₁ + k₂, ?_⟩
    have hsum : (H.ops hc (insert j S)).of e t ⟨x + y, add_mem hx' hy'⟩ =
        (H.ops hc (insert j S)).of e t ⟨x, hx'⟩ + (H.ops hc (insert j S)).of e t ⟨y, hy'⟩ :=
      map_add ((H.ops hc (insert j S)).of e t) ⟨x, hx'⟩ ⟨y, hy'⟩
    rw [hsum, smul_add]
    refine add_mem ?_ ?_
    · rw [add_comm, pow_add, mul_smul]
      exact Submodule.smul_mem _ _ hk₁
    · rw [pow_add, mul_smul]
      exact Submodule.smul_mem _ _ hk₂

end TowerAx

end Tower

theorem tower_kernels_lift_after_X_pow : ∀ (ι : Type) [LinearOrder ι] (R : Type) [CommRing R] (g : ℕ) (ρ : Fin g → R) (T : ℕ → ℤ → Finset ι → Type) [∀ e t S, AddCommGroup (T e t S)] [∀ e t S, Module R (T e t S)] (res : ∀ e t (S S' : Finset ι), S ⊆ S' → T e t S →ₗ[R] T e t S') (p : ∀ e t S, T (e + 1) t S →ₗ[R] T e t S) (mm : ι → ∀ e t S, T e t S →ₗ[R] T e (t + 1) S) (hc : ∀ e S, OperatorsCommute (ι := ι) (R := R) (A := fun t => T e t S) fun j t => mm j e t S) (H : TowerAx ρ res p mm), (∀ e S j t (b : T e t (insert j S)), S.Nonempty → ∃ (k : ℕ) (t' : ℤ) (a : T e t' S), GrSum.of (hc e (insert j S)) t' (res e t' S (insert j S) (Finset.subset_insert j S) a) = (MvPolynomial.X j : MvPolynomial ι R) ^ k • GrSum.of (hc e (insert j S)) t b) → ∀ (S : Finset ι) (j : ι) (b : H.Tot hc (insert j S)), S.Nonempty → ∃ k : ℕ, (MvPolynomial.X j : MvPolynomial ι (MvPolynomial (Fin g) R)) ^ k • b ∈ LinearMap.range (H.resTot hc S (insert j S) (Finset.subset_insert j S)) := by
  intro ι _ R _ g ρ T _ _ res p mm hc H hyp S j b hS
  have hS' : (insert j S).Nonempty := Finset.insert_nonempty j S
  induction b using (H.ops hc (insert j S)).induction with
  | h0 => exact ⟨0, by simp⟩
  | hof e t a =>
    have ha : (a : T (e + 1) t (insert j S)) ∈
        Ideal.span (Set.range ρ) ^ (e + 1) •
          (⊤ : Submodule R (T (e + 1) t (insert j S))) := by
      rw [← H.ker_eq e t _ hS']
      exact (mem_Ks hS').1 a.2
    obtain ⟨_, k, hk⟩ := H.exists_X_pow_smul_mem_range hc hyp S j hS e t a ha
    exact ⟨k, hk⟩
  | hadd x y hx hy =>
    obtain ⟨k₁, hk₁⟩ := hx
    obtain ⟨k₂, hk₂⟩ := hy
    refine ⟨k₁ + k₂, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [add_comm, pow_add, mul_smul]
      exact Submodule.smul_mem _ _ hk₁
    · rw [pow_add, mul_smul]
      exact Submodule.smul_mem _ _ hk₂

end GlobalTheory.CompanionTheory.FormalAlg.Lift
