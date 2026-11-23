import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrLink
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicColumnLatticeEqSpanPartTransportedFrameStatement
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G.SpanMoved

theorem natSmul_mem (I : AutInst) (T : Submodule (IntAf I.F I.E) (VA I)) (n : ℕ) {t : VA I} (ht : t ∈ T) :
    (n : I.E ⊗[I.F] Af I.F) • t ∈ T := by
  rw [Nat.cast_smul_eq_nsmul]
  exact nsmul_mem ht n

def satG (I : AutInst) (g : ℕ) (T : Submodule (IntAf I.F I.E) (VA I)) :
    Submodule (IntAf I.F I.E) (VA I) where
  carrier := {x | ∃ N : ℕ, Nat.Coprime N g ∧ (N : I.E ⊗[I.F] Af I.F) • x ∈ T}
  zero_mem' := ⟨1, Nat.coprime_one_left g, by simp⟩
  add_mem' := by
    rintro x y ⟨N, hN, hx⟩ ⟨M, hM, hy⟩
    refine ⟨N * M, Nat.coprime_mul_iff_left.2 ⟨hN, hM⟩, ?_⟩
    have e : ((N * M : ℕ) : I.E ⊗[I.F] Af I.F) • (x + y) =
        (M : I.E ⊗[I.F] Af I.F) • ((N : I.E ⊗[I.F] Af I.F) • x) +
          (N : I.E ⊗[I.F] Af I.F) • ((M : I.E ⊗[I.F] Af I.F) • y) := by
      rw [smul_add, smul_smul, smul_smul, Nat.cast_mul, mul_comm (M : I.E ⊗[I.F] Af I.F)]
    rw [e]
    exact add_mem (natSmul_mem I T M hx) (natSmul_mem I T N hy)
  smul_mem' := by
    rintro r x ⟨N, hN, hx⟩
    refine ⟨N, hN, ?_⟩
    have e : (N : I.E ⊗[I.F] Af I.F) • (r • x) = r • ((N : I.E ⊗[I.F] Af I.F) • x) :=
      smul_comm _ _ _
    rw [e]
    exact T.smul_mem r hx

theorem mem_of_coprime_smul (I : AutInst) (g n : ℕ) (hn : Nat.Coprime n g)
    (T : Submodule (IntAf I.F I.E) (VA I)) (hT : mL I g ≤ T) {v : VA I} (hv : v ∈ I.Lf)
    (hnv : (n : I.E ⊗[I.F] Af I.F) • v ∈ T) : v ∈ T := by
  have hg : (g : ℤ) • v ∈ T := by
    have h : (g : I.E ⊗[I.F] Af I.F) • v ∈ mL I g := Submodule.subset_span ⟨v, hv, rfl⟩
    rw [Nat.cast_smul_eq_nsmul] at h
    rw [natCast_zsmul]
    exact hT h
  have hn' : (n : ℤ) • v ∈ T := by
    rw [Nat.cast_smul_eq_nsmul] at hnv
    rw [natCast_zsmul]
    exact hnv

  have key : v = Nat.gcdA n g • ((n : ℤ) • v) + Nat.gcdB n g • ((g : ℤ) • v) := by
    rw [smul_smul, smul_smul, ← add_smul, mul_comm (Nat.gcdA n g), mul_comm (Nat.gcdB n g),
      ← Nat.gcd_eq_gcd_ab, Nat.Coprime.gcd_eq_one hn, Nat.cast_one, one_smul]
  rw [key]
  exact add_mem (zsmul_mem hn' _) (zsmul_mem hg _)

private theorem mem_satG_iff_exists_coprime_smul_mem (I : AutInst) (g : ℕ) (T : Submodule (IntAf I.F I.E) (VA I)) (x : VA I) :
    x ∈ satG I g T ↔ ∃ N : ℕ, Nat.Coprime N g ∧ (N : I.E ⊗[I.F] Af I.F) • x ∈ T := Iff.rfl

private theorem mem_satG_of_mem (I : AutInst) (g : ℕ) (T : Submodule (IntAf I.F I.E) (VA I)) {x : VA I}
    (hx : x ∈ T) : x ∈ satG I g T :=
  (mem_satG_iff_exists_coprime_smul_mem I g T x).2 ⟨1, Nat.coprime_one_left g, by rw [Nat.cast_one, one_smul]; exact hx⟩

private theorem map_mem_mL_of_preserves_Lf (I : AutInst) (g : ℕ) (φ : VA I →ₗ[I.E ⊗[I.F] Af I.F] VA I)
    (hφ : ∀ y ∈ I.Lf, φ y ∈ I.Lf) {x : VA I} (hx : x ∈ mL I g) : φ x ∈ mL I g := by
  have h : mL I g ≤ (mL I g).comap (φ.restrictScalars (IntAf I.F I.E)) := by
    conv_lhs => unfold mL
    rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    show φ ((g : I.E ⊗[I.F] Af I.F) • y) ∈ mL I g
    rw [φ.map_smul]
    exact Submodule.subset_span ⟨φ y, hφ y hy, rfl⟩
  exact h hx

theorem map_mem_satG (I : AutInst) (g : ℕ)
    (φ : VA I →ₗ[I.E ⊗[I.F] Af I.F] VA I) (hφ : ∀ y ∈ I.Lf, φ y ∈ I.Lf) (S S' : Set (VA I))
    (hS : ∀ s ∈ S, φ s ∈ satG I g (Submodule.span (IntAf I.F I.E) S' ⊔ mL I g))
    {w : VA I} (hw : InMod I g S w) :
    φ w ∈ satG I g (Submodule.span (IntAf I.F I.E) S' ⊔ mL I g) := by
  have hle : Submodule.span (IntAf I.F I.E) S ⊔ mL I g ≤
      (satG I g (Submodule.span (IntAf I.F I.E) S' ⊔ mL I g)).comap (φ.restrictScalars (IntAf I.F I.E)) := by
    refine sup_le ?_ ?_
    · rw [Submodule.span_le]
      intro s hs
      exact hS s hs
    · intro x hx
      exact mem_satG_of_mem I g _ (Submodule.mem_sup_right (map_mem_mL_of_preserves_Lf I g φ hφ hx))
  exact hle hw

theorem map_inAt (I : AutInst) (g : ℕ)
    (φ : VA I →ₗ[I.E ⊗[I.F] Af I.F] VA I) (hφ : ∀ y ∈ I.Lf, φ y ∈ I.Lf)
    (T : Submodule (IntAf I.F I.E) (VA I)) (hT : mL I g ≤ T) {d : VA I} (hd : InAt I g g d) :
    φ d ∈ satG I g T := by
  obtain ⟨N, hN, hNd⟩ := hd
  refine (mem_satG_iff_exists_coprime_smul_mem I g T _).2 ⟨N, hN, ?_⟩
  rw [← φ.map_smul]
  exact hT (map_mem_mL_of_preserves_Lf I g φ hφ hNd)

theorem span_moved : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (c : ℕ) (p : VA X.B.I →ₗ[X.B.I.E ⊗[X.B.I.F] Af X.B.I.F] VA X.B.I), c ≡ 1 [MOD X.B.g] → (∀ y ∈ X.B.I.Lf, (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p y ∈ X.B.I.Lf) → (∀ a, p (incl X.B.I (X.eR a)) = 0 ∧ p (incl X.B.I (X.fR a)) = 0) → p (incl X.B.I (X.zR u)) = 0 → ∀ v ∈ X.B.I.Lf, p v = v → InMod X.B.I X.B.g (Set.range (fun i => (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bw i)) ∪ Set.range (fun i => (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bwd i))) v := by
  intro D X u c p hc hpL hef hzR v hv hpv
  have hcg : Nat.Coprime c X.B.g := by
    unfold Nat.Coprime
    rw [Nat.ModEq.gcd_eq hc, Nat.gcd_one_left]
  let V := X.B.I.fmat (X.xu u)

  let ψ : VA X.B.I →ₗ[X.B.I.E ⊗[X.B.I.F] Af X.B.I.F] VA X.B.I :=
    (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (p ∘ₗ Matrix.mulVecLin V)
  have hψ : ∀ y, ψ y = (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (V *ᵥ y) := fun y => rfl
  have hVVi : ∀ y, V *ᵥ (X.B.I.fmat (X.xu u)⁻¹ *ᵥ y) = y := by
    intro y
    rw [Matrix.mulVec_mulVec]
    simp [V, Formalism.MainNotions.S.AutInst.fmat, InvMemClass.coe_inv]
  have hK : ∀ y, y ∈ X.B.I.Lf ↔ V *ᵥ y ∈ X.B.I.Lf := X.xu_K u
  have hViL : ∀ y ∈ X.B.I.Lf, X.B.I.fmat (X.xu u)⁻¹ *ᵥ y ∈ X.B.I.Lf := fun y hy =>
    (hK _).2 (by rw [hVVi]; exact hy)
  have hψL : ∀ y ∈ X.B.I.Lf, ψ y ∈ X.B.I.Lf := fun y hy => by
    rw [hψ]
    exact hpL _ ((hK y).1 hy)
  let S' : Set (VA X.B.I) :=
    Set.range (fun i => (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bw i)) ∪
      Set.range (fun i => (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p (X.B.I.fmat (X.xu u) *ᵥ X.bwd i))
  let T := Submodule.span (IntAf X.B.I.F X.B.I.E) S' ⊔ mL X.B.I X.B.g
  have hT : mL X.B.I X.B.g ≤ T := le_sup_right

  have hS : ∀ s ∈ Set.range X.e0 ∪ Set.range X.f0 ∪ {X.z0} ∪ Set.range X.bw ∪ Set.range X.bwd,
      ψ s ∈ satG X.B.I X.B.g T := by
    rintro s ((((⟨a, rfl⟩ | ⟨a, rfl⟩) | hs) | ⟨i, rfl⟩) | ⟨i, rfl⟩)
    ·
      have hfix : V *ᵥ incl X.B.I (X.eR a) = incl X.B.I (X.eR a) := (X.xu_fix u a).1
      have h0 : ψ (incl X.B.I (X.eR a)) = 0 := by rw [hψ, hfix, (hef a).1, smul_zero]
      have hd : InAt X.B.I X.B.g X.B.g (X.e0 a - incl X.B.I (X.eR a)) := (X.basisApprox a).1
      have h := map_inAt X.B.I X.B.g ψ hψL T hT hd
      rwa [map_sub, h0, sub_zero] at h
    ·
      have hfix : V *ᵥ incl X.B.I (X.fR a) = incl X.B.I (X.fR a) := (X.xu_fix u a).2
      have h0 : ψ (incl X.B.I (X.fR a)) = 0 := by rw [hψ, hfix, (hef a).2, smul_zero]
      have hd : InAt X.B.I X.B.g X.B.g (X.f0 a - incl X.B.I (X.fR a)) := (X.basisApprox a).2
      have h := map_inAt X.B.I X.B.g ψ hψL T hT hd
      rwa [map_sub, h0, sub_zero] at h
    ·
      rw [Set.mem_singleton_iff] at hs
      subst hs
      have h0 : ψ (X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u)) = 0 := by
        rw [hψ, hVVi, hzR, smul_zero]
      have hd : InAt X.B.I X.B.g X.B.g (X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u) - X.z0) :=
        X.xu_z u
      have h := map_inAt X.B.I X.B.g ψ hψL T hT hd
      rw [map_sub, h0, zero_sub] at h
      simpa using neg_mem h
    · exact mem_satG_of_mem X.B.I X.B.g T
        (Submodule.mem_sup_left (Submodule.subset_span (Or.inl ⟨i, rfl⟩)))
    · exact mem_satG_of_mem X.B.I X.B.g T
        (Submodule.mem_sup_left (Submodule.subset_span (Or.inr ⟨i, rfl⟩)))

  have hmap := map_mem_satG X.B.I X.B.g ψ hψL _ S' hS (X.latticeSpan _ (hViL v hv))
  obtain ⟨N, hN, hNv⟩ := (mem_satG_iff_exists_coprime_smul_mem _ _ _ _).1 hmap
  rw [hψ, hVVi, hpv, smul_smul, ← Nat.cast_mul] at hNv
  exact mem_of_coprime_smul X.B.I X.B.g (N * c) (Nat.Coprime.mul_left hN hcg) T hT hv hNv

end GlobalTheory.St.G.SpanMoved
