import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.EpsilonEtaTensorDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.OneLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.EntryZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.CommutingMatrixOffdiagZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.Rho1MapReductionLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.FinrankCentralizerW1Le
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.DualN
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.AdExExt
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.GaloisLiftMemFirstOrderDeformations
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.TwistedCocycleApplyOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.FinAm

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem card_inv_le {A R Γ : Type} [CommRing A] [CommRing R] [Algebra A R] [Finite R] [Group Γ] {n : ℕ}
    {V : Submodule A (Matrix (Fin n) (Fin n) R)} (r : Representation A Γ V) (S : Set (Matrix (Fin n) (Fin n) R))
    (h : ∀ y : V, (∀ g, r g y = y) → (y : Matrix (Fin n) (Fin n) R) ∈ S) : Nat.card r.invariants ≤ S.ncard := by
  rw [← Nat.card_coe_set_eq]
  refine Nat.card_le_card_of_injective
    (fun y : r.invariants => (⟨((y : V) : Matrix (Fin n) (Fin n) R),
      h (y : V) ((Representation.mem_invariants r _).1 y.2)⟩ : S)) ?_
  intro a b hab
  have e := congrArg Subtype.val hab
  exact Subtype.ext (Subtype.ext e)

private theorem cancel_pow {s b K u w : ℕ} (hK : 0 < K) (h : s * K ^ u ≤ b * K ^ (w + u)) : s ≤ b * K ^ w := by
  rw [pow_add, ← mul_assoc] at h
  exact Nat.le_of_mul_le_mul_right h (pow_pos hK u)

private theorem sum_exp {V : Type} [Fintype V] (m n ν d q c₁ c₂ c₀ : ℕ) (d' dv C : V → ℕ) (Cq : Fin q → ℕ)
    (h1 : ∑ v, d' v = d) (h2 : ∑ v, dv v = d) :
    c₁ + c₂ + ∑ v, (m * (n * (d' v + 1) + ν * (1 + dv v)) + C v) +
      ∑ j : Option (Fin q), (j.elim c₀ fun i => m * n + Cq i) =
    (m * (n * d + n * q) + (c₁ + c₂ + c₀ + ∑ v, C v + ∑ j, Cq j)) + (m * (n + ν) * Fintype.card V + m * ν * d) := by
  rw [Fintype.sum_option]
  simp only [Option.elim, mul_add, add_mul, mul_one, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_fin, h1, h2]
  ring

theorem UpperTheory.V.Pa.W1_bound_arithmetic_rank_two :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (n : ℕ) (x : NP G0.frame n) (k : Kap x) (al : Fin T.q → Fin n → x.A) (d : ℕ) (D0 : Subgroup G0.G₀) (_ : ArSys T d D0) (d' : L.Vl → ℕ), l ≠ 2 → ∑ v, d' v = d → (∀ v, Nonempty (LocAb l (L.Gv v) (L.Iv v) (d' v))) → PhiCond G0.Γ l → (∀ g : G0.G₀, (g : G0.Γ) ∈ PL l T.H.toSubgroup → x.ρ g = 1) → x.N4 D0 → T.Eig x al → Detects k (Set.range T.sg) → T.B1 k (n * d + n * T.q) := by
  intro l _ L G0 T n x k al d D0 A d' hl hd' hLoc hphi hPL hN4 hEig hDet
  obtain ⟨c₁, hc₁⟩ := h0G l L G0 G0 (Glob.Hom.refl G0) n x k hl
  obtain ⟨c₂, hc₂⟩ := dualN l L G0 T n x k hl hphi hPL hDet
  obtain ⟨c₀, hc₀⟩ := h0v0 l G0.frame n x k D0 hN4
  have hq := fun j => h0q l G0.frame n x k (T.sg j) (al j) (hEig j).1 (hEig j).2
  choose Cq hCq using hq
  have hv : ∀ v, ∃ C, ∀ m, Finite (k.Zb (x.Am m) v) ∧ Nat.card (k.Zb (x.Am m) v) ≤
      Nat.card x.K ^ (m * (n * (d' v + 1) + nu n x.a k.g * (1 + A.dv v)) + C) := by
    intro v
    refine locV l G0.frame n x k v (A.dv v) (d' v) ?_ (hLoc v).some
    have h0 := (A.counts 0).locV v
    rw [A.dv_eq 0] at h0
    convert h0 using 2
    refine MonoidHom.ext fun g => ?_
    show G0.ε (G0.φ v g : G0.Γ) = (T.GN 0).ε ((T.GN 0).φ v g : (T.GN 0).Γ)
    rw [← (T.h 0).ε]
    exact congrArg G0.ε ((T.h 0).φ v g).symm
  choose Cv hCv using hv
  refine ⟨c₁ + c₂ + c₀ + ∑ v, Cv v + ∑ j, Cq j, fun m => ?_⟩
  filter_upwards [hc₂ m, phEq l L G0 T n x k m hphi hPL] with N hN2 hNph
  have r1 := rho1 l G0.frame n x k (x.Am m)
  have inv_eq : ∀ g σ : G0.G₀, k.ρ1 (x.Am m) g = k.ρ1 (x.Am m) σ →
      k.ρ1 (x.Am m) g⁻¹ = k.ρ1 (x.Am m) σ⁻¹ := by
    intro g σ e
    calc k.ρ1 (x.Am m) g⁻¹ = k.ρ1 (x.Am m) g⁻¹ * k.ρ1 (x.Am m) (σ * σ⁻¹) := by
          rw [mul_inv_cancel, r1.1, mul_one]
      _ = k.ρ1 (x.Am m) (g⁻¹ * g) * k.ρ1 (x.Am m) σ⁻¹ := by
          rw [r1.2.1, r1.2.1, e, mul_assoc]
      _ = k.ρ1 (x.Am m) σ⁻¹ := by
          rw [inv_mul_cancel, r1.1, one_mul]
  have hok1 := (ok1 l L (T.GN N) G0 (T.h N) n x k (x.Am m) 1).1
  simp only [MonoidHom.one_apply, map_one] at hok1
  obtain ⟨rep, hrep⟩ := adEx l (T.GN N).frame x.A (DD (x.Am m) k.g) n
    (fun g => k.ρ1 (x.Am m) ((T.h N).p₀ g)) (fun _ => 1) (k.M1 (x.Am m)) hok1
  let χ' : (T.GN N).Γ →* x.A := (algebraMap ℤ_[l] x.A : ℤ_[l] →* x.A).comp
    ((Units.coeHom ℤ_[l]).comp (G0.ε.comp (T.h N).p))
  obtain ⟨rep', hrep'⟩ := adEx l (T.GN N).frame x.A (DD (x.Am m) k.g) n
    (fun g => k.ρ1 (x.Am m) ((T.h N).p₀ g)) (fun g => epsD k (x.Am m) ((T.h N).p g)) (k.EpsilonEtaTensorDual (x.Am m))
    (ok1 l L (T.GN N) G0 (T.h N) n x k (x.Am m) χ').2.1
  have hKpos : 0 < Nat.card x.K := by
    haveI := x.fin
    exact Nat.card_pos
  haveI : Finite (DD (x.Am m) k.g) := (finAm l G0.frame n x m k.g).2.2.1
  have hsum : ∑ v, A.dv v = d := by
    rw [← A.dv_eq N]
    exact (A.a N).sum_dv
  have hsurj0 : ∀ g : G0.G₀, ∃ g' : (T.GN N).G₀, (T.h N).p₀ g' = g := by
    intro g
    obtain ⟨y, hy⟩ := (T.h N).surj (g : G0.Γ)
    have hy1 : y ∈ (T.GN N).η.ker := by
      rw [MonoidHom.mem_ker, ← (T.h N).η, hy]
      exact g.2
    exact ⟨⟨y, hy1⟩, Subtype.ext hy⟩
  have hinv : ∀ j : Option (Fin T.q),
      Nat.card (Representation.invariants (rep'.comp ((A.a N).ι (Sum.inr (Sum.inr j))))) ≤
        Nat.card x.K ^ (j.elim c₀ fun i => m * n + Cq i) := by
    intro j
    cases j with
    | none =>
      refine (card_inv_le _ {Y | Y ∈ k.EpsilonEtaTensorDual (x.Am m) ∧ ∀ g ∈ D0, epsD k (x.Am m) ↑g •
        (k.ρ1 (x.Am m) g * Y * k.ρ1 (x.Am m) g⁻¹) = Y} ?_).trans (hc₀ m)
      intro y hy
      refine ⟨y.2, fun g hg => ?_⟩
      rw [← A.d0 N] at hg
      obtain ⟨t, rfl⟩ := hg
      have hy' : rep' ((A.a N).φq none t : (T.GN N).Γ) y = y := hy t
      have e := hrep'.1 ((A.a N).φq none t) y
      rw [hy'] at e
      beta_reduce at e
      rw [map_inv] at e
      rw [MonoidHom.comp_apply]
      exact e.symm
    | some i =>
      refine (card_inv_le _ {Y | Y ∈ k.EpsilonEtaTensorDual (x.Am m) ∧
        k.ρ1 (x.Am m) (T.sg i) * Y * k.ρ1 (x.Am m) (T.sg i)⁻¹ = Y} ?_).trans (hCq i m)
      intro y hy
      refine ⟨y.2, ?_⟩
      obtain ⟨t, ht⟩ := A.ph N i
      have hy' : rep' ((A.a N).φq (some i) t : (T.GN N).Γ) y = y := hy t
      rw [ht] at hy'
      have e := hrep'.1 (T.ph N i) y
      rw [hy'] at e
      beta_reduce at e
      rw [map_inv, inv_eq _ _ (hNph i).1, (hNph i).1, (hNph i).2.1, one_smul] at e
      exact e.symm
  have h0inv : Nat.card rep.invariants ≤ Nat.card x.K ^ c₁ := by
    refine (card_inv_le rep {Y | Y ∈ k.M1 (x.Am m) ∧ Yᵀ = -Y ∧
      ∀ g : G0.G₀, k.ρ1 (x.Am m) g * Y * k.ρ1 (x.Am m) g⁻¹ = Y} ?_).trans (hc₁ m)
    intro y hy
    refine ⟨y.2, ?_, fun g => ?_⟩
    · have e := hrep.2 y
      rw [hy, one_smul] at e
      have e2 := congrArg Matrix.transpose e
      rw [Matrix.transpose_neg, Matrix.transpose_transpose] at e2
      exact e2
    · obtain ⟨g', rfl⟩ := hsurj0 g
      have e := hrep.1 g' y
      rw [hy] at e
      beta_reduce at e
      rw [one_smul, map_inv] at e
      exact e.symm
  have hdual : Finite (Zl rep') → {y | y ∈ Zl rep' ∧ ∀ j : Fin T.q,
      y ∘ ((A.a N).ι (Sum.inr (Sum.inr (some j)))) ∈
        Bl (rep'.comp ((A.a N).ι (Sum.inr (Sum.inr (some j)))))}.ncard ≤
      Nat.card (Bl rep') * Nat.card x.K ^ c₂ := by
    intro hfinZ
    refine le_trans (Set.ncard_le_ncard ?_ ?_) (hN2 rep' hrep' hfinZ)
    · intro y hy
      refine ⟨hy.1, fun j => ?_⟩
      obtain ⟨Y, hY⟩ := (mem_Bl _).1 (hy.2 j)
      obtain ⟨t1, ht1⟩ := A.ph N j
      obtain ⟨t2, ht2⟩ := A.ta N j
      refine ⟨Y, ?_, ?_⟩
      · rw [← ht1]
        exact hY t1
      · rw [← ht2]
        exact hY t2
    · exact (Set.toFinite (Zl rep' : Set _)).subset (fun y hy => hy.1)
  obtain ⟨hfin, hle⟩ := oneLevel l L (T.GN N) G0 (T.h N) n x k m T.q d (A.a N) rep rep'
    (fun v => m * (n * (d' v + 1) + nu n x.a k.g * (1 + A.dv v)) + Cv v)
    (fun j => j.elim c₀ fun i => m * n + Cq i) c₁ c₂ hl (A.counts N) hrep hrep'
    (fun v => hCv v m) hinv h0inv hdual
  rw [sum_exp m n (nu n x.a k.g) d T.q c₁ c₂ c₀ d' A.dv Cv Cq hd' hsum] at hle
  exact ⟨hfin, cancel_pow hKpos hle⟩
