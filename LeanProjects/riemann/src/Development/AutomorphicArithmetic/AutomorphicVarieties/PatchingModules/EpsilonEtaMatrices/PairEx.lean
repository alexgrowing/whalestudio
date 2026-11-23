import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.EpsilonEtaTensorDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.AuxiliaryVectorCutByHermitianLinearForm
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.DdSumZero
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem blk_nd {A R N : Type} [CommRing A] [CommRing R] [Algebra A R] [AddCommGroup N] (T : R →+ N) (n a : ℕ)
    (V1 V2 U1 U2 : Submodule A R) (h1 : ∀ x ∈ V1, (∀ y ∈ U1, T (x * y) = 0) → x = 0)
    (h2 : ∀ x ∈ V2, (∀ y ∈ U2, T (x * y) = 0) → x = 0) (Z : Matrix (Fin n) (Fin n) R) (hZ : Z ∈ blkMat n a V1 V2)
    (h : ∀ Y ∈ blkMat n a U1 U2, T (trace (Z * Y)) = 0) : Z = 0 := by
  have tr : ∀ (i j : Fin n) (y : R), trace (Z * single j i y) = Z i j * y := by
    intro i j y
    rw [trace_mul_single]; simp
  have mem : ∀ (i j : Fin n) (y : R), ((((i : ℕ) < a) ↔ ((j : ℕ) < a)) → y ∈ U1) →
      (¬ (((i : ℕ) < a) ↔ ((j : ℕ) < a)) → y ∈ U2) → single j i y ∈ blkMat n a U1 U2 := by
    intro i j y e1 e2 p q
    by_cases e : j = p ∧ i = q
    · obtain ⟨rfl, rfl⟩ := e
      rw [single_apply_same]
      exact ⟨fun e => e1 e.symm, fun e => e2 fun e' => e e'.symm⟩
    · rw [single_apply_of_ne _ _ _ _ _ e]
      exact ⟨fun _ => zero_mem _, fun _ => zero_mem _⟩
  refine Matrix.ext fun i j => ?_
  by_cases e : ((i : ℕ) < a) ↔ ((j : ℕ) < a)
  · refine h1 _ ((hZ i j).1 e) fun y hy => ?_
    rw [← tr]
    exact h _ (mem i j y (fun _ => hy) fun e' => absurd e e')
  · refine h2 _ ((hZ i j).2 e) fun y hy => ?_
    rw [← tr]
    exact h _ (mem i j y (fun e' => absurd e' e) fun _ => hy)

private def etaH (X : Type) [CommRing X] (g : ℕ) : DD X g →+ X where
  toFun u := u.eta
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem etaH_apply (X : Type) [CommRing X] (g : ℕ) (u : DD X g) : etaH X g u = u.eta := rfl

section
variable {A X N : Type} [CommRing A] [CommRing X] [Algebra A X] [AddCommGroup N] {g : ℕ} (τ : X →+ N)
  (hτ : ∀ y, (∀ z, τ (y * z) = 0) → y = 0)
include hτ

private theorem nd1 : ∀ x ∈ ddPart A X g true false false false,
    (∀ y ∈ ddPart A X g false false false true, (τ.comp (etaH X g)) (x * y) = 0) → x = 0 := by
  rintro x ⟨-, a2, a3, a4⟩ h
  refine DD.ext (hτ _ fun z => ?_) (a2 rfl) (a3 rfl) (a4 rfl)
  have := h ⟨0, 0, 0, z⟩ ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, by simp⟩
  rw [AddMonoidHom.comp_apply, etaH_apply] at this
  simpa using this

private theorem nd2 : ∀ x ∈ ddPart A X g false false false true,
    (∀ y ∈ ddPart A X g true false false false, (τ.comp (etaH X g)) (x * y) = 0) → x = 0 := by
  rintro x ⟨a1, a2, a3, -⟩ h
  refine DD.ext (a1 rfl) (a2 rfl) (a3 rfl) (hτ _ fun z => ?_)
  have := h ⟨z, 0, 0, 0⟩ ⟨by simp, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
  rw [AddMonoidHom.comp_apply, etaH_apply] at this
  simpa using this

private theorem nd3 : ∀ x ∈ ddPart A X g false true false false,
    (∀ y ∈ ddPart A X g false false true false, (τ.comp (etaH X g)) (x * y) = 0) → x = 0 := by
  rintro x ⟨a1, -, a3, a4⟩ h
  refine DD.ext (a1 rfl) (funext fun j => hτ _ fun z => ?_) (a3 rfl) (a4 rfl)
  have := h ⟨0, 0, Pi.single j z, 0⟩ ⟨fun _ => rfl, fun _ => rfl, by simp, fun _ => rfl⟩
  rw [AddMonoidHom.comp_apply, etaH_apply] at this
  simpa [Pi.single_apply] using this

private theorem nd4 : ∀ x ∈ ddPart A X g false false true false,
    (∀ y ∈ ddPart A X g false true false false, (τ.comp (etaH X g)) (x * y) = 0) → x = 0 := by
  rintro x ⟨a1, a2, -, a4⟩ h
  refine DD.ext (a1 rfl) (a2 rfl) (funext fun j => hτ _ fun z => ?_) (a4 rfl)
  have := h ⟨0, Pi.single j z, 0, 0⟩ ⟨fun _ => rfl, by simp, fun _ => rfl, fun _ => rfl⟩
  rw [AddMonoidHom.comp_apply, etaH_apply] at this
  simpa [Pi.single_apply] using this

end

theorem UpperTheory.V.Pa.pairEx :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (k : Kap x) (m : ℕ), ∃ b : k.M1 (x.Am m) →+ k.EpsilonEtaTensorDual (x.Am m) →+ ZMod l, ∀ (rep : Representation x.A G.Γ (k.M1 (x.Am m))) (rep' : Representation x.A G.Γ (k.EpsilonEtaTensorDual (x.Am m))), IsAd G.frame (fun g => k.ρ1 (x.Am m) (h.p₀ g)) (fun _ => 1) (k.M1 (x.Am m)) rep → IsAd G.frame (fun g => k.ρ1 (x.Am m) (h.p₀ g)) (fun g => epsD k (x.Am m) (h.p g)) (k.EpsilonEtaTensorDual (x.Am m)) rep' → IsDualPair G.ε rep rep' b := by
  intro l _ L G G0 h n x k m
  obtain ⟨τ, hτ, hs⟩ := pair1 l G0.frame n x m
  obtain ⟨r1, r2, -⟩ := rho1 l G0.frame n x k (x.Am m)
  set T : DD (x.Am m) k.g →+ ZMod l := τ.comp (etaH (x.Am m) k.g) with hT
  let b : k.M1 (x.Am m) →+ k.EpsilonEtaTensorDual (x.Am m) →+ ZMod l := AddMonoidHom.mk' (fun Z => AddMonoidHom.mk'
    (fun Y => T (trace ((Z : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)) * (Y : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)))))
    fun Y Y' => by rw [Submodule.coe_add, Matrix.mul_add, trace_add, map_add])
    fun Z Z' => by
      refine AddMonoidHom.ext fun Y => ?_
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
      rw [Submodule.coe_add, Matrix.add_mul, trace_add, map_add]
  have hb : ∀ Z Y, b Z Y = T (trace ((Z : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)) *
      (Y : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)))) := fun _ _ => rfl
  have hE : ∀ (γ : G.Γ) (u : DD (x.Am m) k.g), T (epsD k (x.Am m) (h.p γ) * u) = epsBar G.ε γ * T u := by
    intro γ u
    have e : (epsD k (x.Am m) (h.p γ) * u).eta =
        algebraMap x.A (x.Am m) (algebraMap ℤ_[l] x.A (G0.ε (h.p γ) : ℤ_[l])) * u.eta := by
      show (DD.C (algebraMap x.A (x.Am m) (algebraMap ℤ_[l] x.A (G0.ε (h.p γ) : ℤ_[l]))) * u).eta = _
      simp
    show τ (epsD k (x.Am m) (h.p γ) * u).eta = _ * τ u.eta
    rw [e, hs, h.ε]; rfl
  refine ⟨b, fun rep rep' ⟨p1, p2⟩ ⟨q1, q2⟩ => ⟨fun Z hZ => Subtype.ext ?_, fun Y hY => Subtype.ext ?_, ?_⟩⟩
  · exact blk_nd T n x.a _ _ _ _ (nd1 τ hτ) (nd3 τ hτ) _ Z.2 fun Y hY => hZ ⟨Y, hY⟩
  · refine blk_nd T n x.a _ _ _ _ (nd2 τ hτ) (nd4 τ hτ) _ Y.2 fun Z hZ => ?_
    rw [trace_mul_comm]
    exact hY ⟨Z, hZ⟩
  · have e0 : ∀ (g : G.frame.G₀) Z Y, b (rep g Z) (rep' g Y) = epsBar G.ε g * b Z Y := by
      intro g Z Y
      rw [hb, hb, p1, q1, ← hE]
      have i1 : k.ρ1 (x.Am m) (h.p₀ g⁻¹) * k.ρ1 (x.Am m) (h.p₀ g) = 1 := by
        rw [← r2, ← map_mul, inv_mul_cancel, map_one, r1]
      congr 1
      beta_reduce
      generalize k.ρ1 (x.Am m) (h.p₀ g⁻¹) = s at i1 ⊢
      generalize k.ρ1 (x.Am m) (h.p₀ g) = r at i1 ⊢
      rw [one_smul, Matrix.mul_smul, trace_smul, smul_eq_mul]
      congr 1
      rw [← Matrix.mul_assoc, trace_mul_comm]
      simp only [← Matrix.mul_assoc]
      rw [i1, Matrix.one_mul, Matrix.mul_assoc _ s, i1, Matrix.mul_one]
    have ec : ∀ Z Y, b (rep G.c Z) (rep' G.c Y) = epsBar G.ε G.c * b Z Y := by
      intro Z Y
      rw [hb, hb, p2, q2, ← hE]
      congr 1
      beta_reduce
      rw [one_smul, Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_smul, trace_smul, smul_eq_mul,
        ← transpose_mul, trace_transpose, trace_mul_comm]
    intro γ Z Y
    by_cases hγ : γ ∈ G.η.ker
    · exact e0 ⟨γ, hγ⟩ Z Y
    · have hm : γ * G.c ∈ G.η.ker := by
        rw [MonoidHom.mem_ker] at hγ ⊢
        rcases Int.units_eq_one_or (G.η γ) with e | e
        · exact absurd e hγ
        · rw [map_mul, e, G.η_c]; simp
      have e : γ = γ * G.c * G.c := by rw [mul_assoc, G.c_sq, mul_one]
      have := e0 ⟨_, hm⟩ (rep G.c Z) (rep' G.c Y)
      rw [ec, ← mul_assoc] at this
      rw [e, map_mul rep, map_mul rep', Module.End.mul_apply, Module.End.mul_apply]
      refine this.trans ?_
      simp only [epsBar, map_mul, Units.val_mul]
