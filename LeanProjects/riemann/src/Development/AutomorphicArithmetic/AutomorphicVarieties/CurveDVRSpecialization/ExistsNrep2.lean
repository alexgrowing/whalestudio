import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RatTorsionFree
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.HostFrameEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.PropagationTheoremGL2
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.ExistsNrep3

open NumberField IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr UpperTheory.V

namespace UpperTheory.V.Pr.LkPt2

open Matrix

section Mat

variable {A : Type} [CommRing A]

private def Bl (X : Matrix (Fin 3) (Fin 3) A) : Prop := X 0 1 = 0 ∧ X 1 0 = 0 ∧ X 1 2 = 0 ∧ X 2 1 = 0

private theorem c00 (X : Matrix (Fin 3) (Fin 3) A) : corner X 0 0 = X 0 0 := rfl
private theorem c01 (X : Matrix (Fin 3) (Fin 3) A) : corner X 0 1 = X 0 2 := rfl
private theorem c10 (X : Matrix (Fin 3) (Fin 3) A) : corner X 1 0 = X 2 0 := rfl
private theorem c11 (X : Matrix (Fin 3) (Fin 3) A) : corner X 1 1 = X 2 2 := rfl

private theorem corner_mul {X : Matrix (Fin 3) (Fin 3) A} (hX : Bl X) (Y : Matrix (Fin 3) (Fin 3) A) :
    corner (X * Y) = corner X * corner Y := by
  obtain ⟨h1, h2, h3, h4⟩ := hX
  ext i j
  fin_cases i <;> fin_cases j <;> simp [c00, c01, c10, c11, Matrix.mul_apply, Fin.sum_univ_three, h1, h4]

private theorem corner_one : corner (1 : Matrix (Fin 3) (Fin 3) A) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [c00, c01, c10, c11]

private theorem corner_sub (X : Matrix (Fin 3) (Fin 3) A) (a : A) :
    corner (X - a • (1 : Matrix (Fin 3) (Fin 3) A)) = corner X - a • (1 : Matrix (Fin 2) (Fin 2) A) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [c00, c01, c10, c11]

private theorem block_sub {X : Matrix (Fin 3) (Fin 3) A} (hX : Bl X) (a : A) :
    Bl (X - a • (1 : Matrix (Fin 3) (Fin 3) A)) := by
  obtain ⟨h1, h2, h3, h4⟩ := hX
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [*]

private theorem corner_J (X : Matrix (Fin 3) (Fin 3) A) :
    corner (Jmat A 3 * Xᵀ * Jmat A 3) = Jmat A 2 * (corner X)ᵀ * Jmat A 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [c00, c01, c10, c11, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, Jmat, Fin.rev]

private theorem ch2 (S : Matrix (Fin 2) (Fin 2) A) (y : A) :
    ((S.trace - y) • (1 : Matrix (Fin 2) (Fin 2) A) - S) * (S - y • 1) = (S - y • 1).det • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two, Matrix.trace_fin_two] <;> ring

private theorem drop_mid {H : Type} [Group H] (σ : H →* Matrix (Fin 2) (Fin 2) A) (ψ : H →* Aˣ) (t : H) (y : A)
    (Z : Matrix (Fin 2) (Fin 2) A) (hu : IsUnit (σ t - y • 1).det)
    (h : ∀ a, (σ a - (ψ a : A) • 1) * ((σ t - y • 1) * Z) = 0) (a : H) : (σ a - (ψ a : A) • 1) * Z = 0 := by
  have e : (σ a - (ψ a : A) • 1) * (((σ t).trace - y) • (1 : Matrix (Fin 2) (Fin 2) A) - σ t) =
      ((σ t).trace - y) • (σ a - (ψ a : A) • 1) - (σ (a * t) - (ψ (a * t) : A) • 1) +
        (ψ a : A) • (σ t - (ψ t : A) • 1) := by
    rw [map_mul, map_mul, Units.val_mul, Matrix.mul_sub, Matrix.sub_mul (σ a) _ (σ t), Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, Matrix.one_mul, smul_sub (ψ a : A), smul_smul]
    abel
  have e2 : (σ t - y • 1).det • ((σ a - (ψ a : A) • 1) * Z) = 0 := by
    calc _ = (σ a - (ψ a : A) • 1) * ((((σ t).trace - y) • (1 : Matrix (Fin 2) (Fin 2) A) - σ t) * (σ t - y • 1)) * Z := by
          rw [ch2, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
      _ = 0 := by
          rw [← Matrix.mul_assoc, e, Matrix.mul_assoc, Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul,
            h, h, h]
          simp
  exact (hu.smul_eq_zero).1 e2

end Mat

private theorem w_eq (i : Fin 2) : Fr.w 2 i = Fr.w 3 (![0, 2] i) := by fin_cases i <;> rfl

private theorem w_eq' (i : Fin 2) : Fr.w 2 i = wt1 (![0, 2] i) := by fin_cases i <;> rfl

private theorem ne_of {i j : Fin 2} (h : i ≠ j) : (![0, 2] i : Fin 3) ≠ ![0, 2] j := by
  revert h; fin_cases i <;> fin_cases j <;> decide

private theorem ex_block {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Fr.Frame l (ResidueField O)}
    (f3 : ∀ v, ∃ g, F.Ψ (F.loc v g) ^ 2 ≠ 1) {A : Type} [CommRing A] [IsLocalRing A] [Algebra O A]
    [IsLocalHom (algebraMap O A)] (ρ : Fr.NRep F 3 A) (hρ : IsLiftA O ρ) (hb : ∀ g, Bl (ρ.r g)) :
    ∃ ρ' : Fr.NRep F 2 A, IsLiftA O ρ' ∧ (∀ g, ρ'.r g = corner (ρ.r g)) ∧ ∀ v i, ρ'.ψ v i = ρ.ψ v (![0, 2] i) := by
  let σ : F.G0 →* Matrix (Fin 2) (Fin 2) A :=
    { toFun := fun g => corner (ρ.r g)
      map_one' := by rw [map_one, corner_one]
      map_mul' := fun g h => by rw [map_mul, corner_mul (hb g)] }
  have hσ : ∀ g, σ g = corner (ρ.r g) := fun _ => rfl
  refine ⟨⟨σ, fun v i => ρ.ψ v (![0, 2] i), fun g => ?_, fun i j h => ρ.diag _ _ (ne_of h), fun v g => ?_⟩,
    ⟨⟨fun i j => hρ.cont.1 _ _, fun v i => hρ.cont.2 v _⟩, ⟨fun g i => ?_, fun v i g => ?_⟩,
      fun g i j h => hρ.diag g _ _ (ne_of h)⟩, fun _ => rfl, fun _ _ => rfl⟩
  · rw [hσ, hσ, ρ.pol, corner_J]
  · obtain ⟨t, ht⟩ := f3 v
    have hu : IsUnit (σ (F.loc0 v t) - (ρ.ψ v 1 t : A) • (1 : Matrix (Fin 2) (Fin 2) A)).det := by
      rw [← residue_ne_zero_iff_isUnit]
      have a0 := hρ.bar.1 (F.loc0 v t) 0
      have a2 := hρ.bar.1 (F.loc0 v t) 2
      have b1 := hρ.bar.2 v 1 t
      have c0 := hρ.diag (F.loc0 v t) 0 2 (by decide)
      rw [Fr.NRep.map_r] at a0 a2 c0
      rw [Fr.NRep.map_ψ] at b1
      have w0 : Fr.w 3 0 = 1 := rfl
      have w1 : Fr.w 3 1 = 0 := rfl
      have w2 : Fr.w 3 2 = -1 := rfl
      rw [w0, zpow_one] at a0
      rw [w1, zpow_zero, Units.val_one, map_one] at b1
      rw [w2, _root_.zpow_neg_one] at a2
      have hne : F.Ψ (F.loc0 v t : F.Γ) ≠ 1 := fun e => ht (by
        show F.Ψ (F.loc0 v t : F.Γ) ^ 2 = 1
        rw [e, one_pow])
      have key : ∀ u : (ResidueField O)ˣ, u ≠ 1 → ResidueField.map (algebraMap O A) u - 1 ≠ 0 := fun u hu e => by
        rw [sub_eq_zero, ← map_one (ResidueField.map (algebraMap O A))] at e
        exact hu (Units.ext ((ResidueField.map (algebraMap O A)).injective e))
      have : residue A (σ (F.loc0 v t) - (ρ.ψ v 1 t : A) • (1 : Matrix (Fin 2) (Fin 2) A)).det =
          (residue A (ρ.r (F.loc0 v t) 0 0) - residue A (ρ.ψ v 1 t)) *
            (residue A (ρ.r (F.loc0 v t) 2 2) - residue A (ρ.ψ v 1 t)) -
            residue A (ρ.r (F.loc0 v t) 0 2) * residue A (ρ.r (F.loc0 v t) 2 0) := by
        simp [Matrix.det_fin_two, hσ, c00, c01, c10, c11]
      rw [this, a0, a2, b1, c0, zero_mul, sub_zero]
      exact mul_ne_zero (key _ hne) (key _ (inv_ne_one.2 hne))
    have := drop_mid (σ.comp (F.loc0 v)) (ρ.ψ v 0) t (ρ.ψ v 1 t : A)
      (σ (F.loc0 v (g 1)) - (ρ.ψ v 2 (g 1) : A) • 1) hu (fun a => by
        have h := congrArg corner (ρ.ord v ![a, t, g 1])
        simp only [Fr.ordProd, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one] at h
        rw [corner_mul (block_sub (hb _) _), corner_mul (block_sub (hb _) _), corner_sub, corner_sub, corner_sub] at h
        exact h) (g 0)
    simp only [Fr.ordProd, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]
    exact this
  · rw [w_eq]
    exact hρ.bar.1 g _
  · rw [w_eq]
    exact hρ.bar.2 v _ g

end UpperTheory.V.Pr.LkPt2

open UpperTheory.V.Pr.LkPt2 in
theorem UpperTheory.V.Pr.exists_nrep2 :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
      {L : Type} [Field L] [NumberField L] [Algebra L Ω] {Φ : Fr.Frame l (ResidueField O)} (k : GalLink η Ψ σ g₁ B M L Φ) [CharP (ResidueField O) l] {C₀ : ℕ}, Φ.Ok C₀ → l ∣ M → σ * σ = 1 →
    ∀ {A : Type} [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [Algebra O A] [IsLocalHom (algebraMap O A)] (r : G ℚ Ω →* GG 3 A), OrdPt l η Ψ σ g₁ B r → Block η r → ∃ ρ : Fr.NRep Φ 2 A, IsLiftA O ρ ∧ (∀ s : G L Ω, ρ.r (k.p0 s) = corner (r (Base.galEmb ℚ L Ω s)).mat) ∧
      ∀ v i, ∀ g ∈ Φ.Iv v, (ρ.ψ v i g : A) = algebraMap O A ((Ψ (k.j v g) ^ Fr.w 2 i : Oˣ) : O) := by
  intro Ω _ _ _ l _ O _ _ η Ψ σ g₁ B M L _ _ _ Φ k _ C₀ hok hM hσ A _ _ _ _ _ _ r hr hb
  obtain ⟨ρ, h1, h2, h3⟩ := exists_nrep3 k hok hM hσ r hr
  have hbl : ∀ g, Bl (ρ.r g) := fun g => by
    obtain ⟨u, hu⟩ := k.p_surj g.1
    have hη : η u = 1 := by rw [← k.del, hu]; exact g.2
    have hm : u.1 ∈ (Base.galEmb ℚ L Ω).range := by
      rw [Base.range_galEmb, k.gal]
      exact ⟨u.2, hη⟩
    obtain ⟨s, hs⟩ := hm
    have e : g = k.p0 s := Subtype.ext (hu.symm.trans (congrArg k.p (Subtype.ext hs.symm)))
    rw [e, h2, hs]
    exact ⟨hb _ hη _ _ (by decide), hb _ hη _ _ (by decide), hb _ hη _ _ (by decide), hb _ hη _ _ (by decide)⟩
  obtain ⟨ρ', a1, a2, a3⟩ := ex_block hok.f3 ρ h1 hbl
  refine ⟨ρ', a1, fun s => by rw [a2, h2], fun v i g hg => ?_⟩
  rw [a3, h3 v _ g hg, w_eq']
  rfl
