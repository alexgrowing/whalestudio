import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormSubgroupOpen

noncomputable def UpperTheory.Reformulated.B.RestrictAutomorphism.zlW :
    (l : ℕ) → [inst : Fact (Nat.Prime l)] → (R : Type) → [inst_1 : CommRing R] → [CharP R l] → ℤ_[l] →+* WittVector l R :=
    fun (l : ℕ) [Fact (Nat.Prime l)] (R : Type) [CommRing R] [CharP R l] ↦
      (WittVector.map (ZMod.castHom (dvd_refl l) R)).comp (WittVector.equiv l).symm.toRingHom

namespace UpperTheory.Reformulated.B.RestrictAutomorphism

private theorem hom_unique {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [CharP R p]
    (φ ψ : ℤ_[p] →+* WittVector p R) : φ = ψ := by
  ext1 x
  rw [← sub_eq_zero]
  ext i
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec (i + 1) x)
  have hx : x = y * (p : ℤ_[p]) ^ (i + 1) + (x.appr (i + 1) : ℤ_[p]) := by
    rw [hy]; ring
  have h : φ x - ψ x = (φ y - ψ y) * (p : WittVector p R) ^ (i + 1) := by
    conv_lhs => rw [hx]
    simp only [map_add, map_mul, map_pow, map_natCast]
    ring
  rw [h, WittVector.mul_pow_charP_coeff_zero _ (Nat.lt_succ_self i), WittVector.zero_coeff]

private theorem pow_pow_mul {p : ℕ} {R : Type} [CommRing R] {y : R} {m : ℕ}
    (h : y ^ p ^ m = y) (n : ℕ) : y ^ p ^ (m * n) = y := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, h]

private def algPart (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [CharP R p] : Subring R where
  carrier := {y | ∃ m : ℕ, 0 < m ∧ y ^ p ^ m = y}
  one_mem' := ⟨1, one_pos, one_pow _⟩
  zero_mem' := ⟨1, one_pos, zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)⟩
  mul_mem' := by
    rintro a b ⟨m, hm, ha⟩ ⟨n, hn, hb⟩
    refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
    rw [mul_pow, pow_pow_mul ha, mul_comm m n, pow_pow_mul hb]
  add_mem' := by
    rintro a b ⟨m, hm, ha⟩ ⟨n, hn, hb⟩
    refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
    rw [add_pow_char_pow, pow_pow_mul ha, mul_comm m n, pow_pow_mul hb]
  neg_mem' := by
    rintro a ⟨m, hm, ha⟩
    refine ⟨m, hm, ?_⟩
    have h := map_neg (iterateFrobenius R p m) a
    rwa [iterateFrobenius_def, iterateFrobenius_def, ha] at h

private theorem map_mem_algPart {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [CharP R p]
    (σ : R ≃+* R) {y : R} (hy : y ∈ algPart p R) : σ y ∈ algPart p R := by
  obtain ⟨m, hm, h⟩ := hy
  exact ⟨m, hm, by rw [← map_pow, h]⟩

private def restrictAut (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] [CharP R p]
    (σ : R ≃+* R) : algPart p R ≃+* algPart p R where
  toFun y := ⟨σ y, map_mem_algPart σ y.2⟩
  invFun y := ⟨σ.symm y, map_mem_algPart σ.symm y.2⟩
  left_inv y := Subtype.ext (σ.symm_apply_apply _)
  right_inv y := Subtype.ext (σ.apply_symm_apply _)
  map_mul' a b := Subtype.ext (map_mul σ (a : R) b)
  map_add' a b := Subtype.ext (map_add σ (a : R) b)

private def restrictHom (p : ℕ) [Fact p.Prime] {G : Type} [Group G] {R : Type} [CommRing R]
    [CharP R p] (ρ : G →* R ≃+* R) : G →* algPart p R ≃+* algPart p R where
  toFun g := restrictAut p (ρ g)
  map_one' := by
    ext y
    show ρ 1 (y : R) = y
    rw [map_one]; rfl
  map_mul' g h := by
    ext y
    show ρ (g * h) (y : R) = ρ g (ρ h y)
    rw [map_mul]; rfl

end UpperTheory.Reformulated.B.RestrictAutomorphism

theorem UpperTheory.Reformulated.B.RestrictAutomorphism.exists_alg :
    ∀ {p : ℕ} [hp : Fact (Nat.Prime p)] {G : Type} [inst : Group G] {R : Type} [inst_1 : CommRing R] (ρ : G →* R ≃+* R)
      [inst_2 : TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [IsDomain R] [inst_6 : CharP R p],
      (∀ (y : R) (m : ℕ), (0 : ℕ) < m → y ^ p ^ m = y → ∀ᶠ (g : G) in nhds (1 : G), ((ρ : G → R ≃+* R) g : R → R) y = y) →
        ∀ {r : ℕ} (M : G →* Matrix (Fin r) (Fin r) ℤ_[p]),
          Continuous (⇑M : G → Matrix (Fin r) (Fin r) ℤ_[p]) →
            (∀ (g : G),
                (∀ (m : ℕ), (0 : ℕ) < m → ∀ (y : R), y ^ p ^ m = y → ((ρ : G → R ≃+* R) g : R → R) y = y) →
                  (M : G → Matrix (Fin r) (Fin r) ℤ_[p]) g = (1 : Matrix (Fin r) (Fin r) ℤ_[p])) →
              ∃ (W : Matrix (Fin r) (Fin r) (WittVector p R)),
                IsUnit W.det ∧
                  (∀ (g : G),
                      ((M : G → Matrix (Fin r) (Fin r) ℤ_[p]) g).map (⇑(UpperTheory.Reformulated.B.RestrictAutomorphism.zlW p R) : ℤ_[p] → WittVector p R) *
                          W.map (⇑(WittVector.map ((ρ : G → R ≃+* R) g).toRingHom) : WittVector p R → WittVector p R) =
                        W) ∧
                    ∀ (i j : Fin r) (n : ℕ), ∃ (m : ℕ), (0 : ℕ) < m ∧ (W i j).coeff n ^ p ^ m = (W i j).coeff n := by
  intro p hp G _ R _ ρ _ _ _ _ _ hopen r M hM hker
  haveI : CharP (algPart p R) p := inferInstance
  obtain ⟨V, hV, hVeq⟩ := UpperTheory.Reformulated.B.WittVectorTrivializingMatrix.exists_alg (p := p) (restrictHom p ρ)
    (fun y m hm hy => (hopen y m hm (by simpa using congrArg Subtype.val hy)).mono
      fun g hg => Subtype.ext hg)
    M hM
    (fun g hg => hker g fun m hm y hy =>
      congrArg Subtype.val (hg m hm ⟨y, m, hm, hy⟩ (Subtype.ext (by simpa using hy))))
  let ι : WittVector p (algPart p R) →+* WittVector p R := WittVector.map (algPart p R).subtype
  refine ⟨V.map ι, ?_, fun g => ?_, fun i j n => ?_⟩
  · have h := hV.map ι
    rwa [RingHom.map_det] at h
  · have h := congrArg (fun A => A.map ι) (hVeq g (restrictHom p ρ g).toRingHom fun _ _ _ _ => rfl)
    have h1 : (M g).map (zlW p R) =
        ((M g).map (UpperTheory.Reformulated.B.WittVectorTrivializingMatrix.zlW p (algPart p R))).map ι := by
      rw [hom_unique (zlW p R) (ι.comp (UpperTheory.Reformulated.B.WittVectorTrivializingMatrix.zlW p (algPart p R))),
        RingHom.coe_comp, Matrix.map_map]
    have h2 : (V.map ι).map (WittVector.map (ρ g).toRingHom) =
        (V.map (WittVector.map (restrictHom p ρ g).toRingHom)).map ι := by
      ext i j n
      simp only [Matrix.map_apply, ι, WittVector.map_coeff]
      rfl
    rw [h1, h2, ← Matrix.map_mul]
    exact h
  · simp only [Matrix.map_apply, ι, WittVector.map_coeff]
    exact ((V i j).coeff n).2
