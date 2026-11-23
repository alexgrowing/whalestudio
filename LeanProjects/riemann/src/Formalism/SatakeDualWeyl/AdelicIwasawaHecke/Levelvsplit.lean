import Formalism.SatakeDualWeyl.StatementC
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Stabstd

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.UG.P

section Gen

variable {A R : Type} [CommRing A] [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

theorem levelvsplit_coe_bc (f : R →+* A) (u : GL n R) :
    ((bc (n := n) f u : GL n A) : Matrix n n A) = (u : Matrix n n R).map f := by
  rfl

theorem levelvsplit_mem_range_iff (f : R →+* A) (hf : Function.Injective f) (g : GL n A) :
    g ∈ (bc (n := n) f).range ↔
      (∀ i j, (g : Matrix n n A) i j ∈ Set.range f) ∧
        ∀ i j, ((g⁻¹ : GL n A) : Matrix n n A) i j ∈ Set.range f := by
  constructor
  · intro hg
    obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hg
    refine ⟨fun i j => ⟨(u : Matrix n n R) i j, rfl⟩, fun i j => ⟨((u⁻¹ : GL n R) : Matrix n n R) i j, ?_⟩⟩
    rw [← map_inv (bc (n := n) f) u]
    rfl
  · rintro ⟨h1, h2⟩
    choose M hM using h1
    choose N hN using h2
    have hinj : Function.Injective (f.mapMatrix : Matrix n n R →+* Matrix n n A) := by
      intro X Y h
      ext i j
      have h' := congrArg (fun Z : Matrix n n A => Z i j) h
      exact hf h'
    have hMg : f.mapMatrix (Matrix.of M) = (g : Matrix n n A) := by
      ext i j
      exact hM i j
    have hNg : f.mapMatrix (Matrix.of N) = ((g⁻¹ : GL n A) : Matrix n n A) := by
      ext i j
      exact hN i j
    have e1 : Matrix.of M * Matrix.of N = 1 := hinj (by rw [map_mul, map_one, hMg, hNg, Units.mul_inv])
    have e2 : Matrix.of N * Matrix.of M = 1 := hinj (by rw [map_mul, map_one, hMg, hNg, Units.inv_mul])
    exact MonoidHom.mem_range.mpr ⟨⟨Matrix.of M, Matrix.of N, e1, e2⟩, Units.ext hMg⟩

end Gen

section Split

variable {B K : Type} [CommRing B] [CommRing K] {n : Type} [Fintype n] [DecidableEq n]

theorem levelvsplit_unitary (τ : B →+* B) (φ : B ≃+* K × K)
    (hτ : ∀ x, φ (τ x) = swapR K (φ x)) (J' : Matrix n n B) (h : GL n B) (hh : h ∈ UJ τ J') :
    ((h : Matrix n n B).map ((RingHom.snd K K).comp φ.toRingHom))ᵀ *
        J'.map ((RingHom.fst K K).comp φ.toRingHom) *
        (h : Matrix n n B).map ((RingHom.fst K K).comp φ.toRingHom) =
      J'.map ((RingHom.fst K K).comp φ.toRingHom) := by
  have hh' : Formalism.UG.cT τ (h : Matrix n n B) * J' * (h : Matrix n n B) = J' := hh
  have key : (Formalism.UG.cT τ (h : Matrix n n B)).map ((RingHom.fst K K).comp φ.toRingHom) =
      ((h : Matrix n n B).map ((RingHom.snd K K).comp φ.toRingHom))ᵀ := by
    ext i j
    simp [Formalism.UG.cT, hτ, Formalism.UG.swapR]
  have h2 := congrArg (fun M : Matrix n n B => M.map ((RingHom.fst K K).comp φ.toRingHom)) hh'
  simp only [Matrix.map_mul] at h2
  rw [key] at h2
  exact h2

theorem levelvsplit_solve (A Ainv P1 P1i P2 : Matrix n n K) (hA : A * Ainv = 1)
    (hP : P1 * P1i = 1) (hrel : P2ᵀ * A * P1 = A) : P2 = (A * P1i * Ainv)ᵀ := by
  have h1 : P2ᵀ * A = A * P1i := by
    calc P2ᵀ * A = P2ᵀ * A * (P1 * P1i) := by rw [hP, Matrix.mul_one]
      _ = P2ᵀ * A * P1 * P1i := by simp only [Matrix.mul_assoc]
      _ = A * P1i := by rw [hrel]
  have h2 : P2ᵀ = A * P1i * Ainv := by
    calc P2ᵀ = P2ᵀ * (A * Ainv) := by rw [hA, Matrix.mul_one]
      _ = P2ᵀ * A * Ainv := by rw [Matrix.mul_assoc]
      _ = A * P1i * Ainv := by rw [h1]
  rw [← h2, Matrix.transpose_transpose]

theorem levelvsplit_int_mul {S : Type} [SetLike S K] [SubringClass S K] (O : S)
    (M N : Matrix n n K) (hM : ∀ i j, M i j ∈ O) (hN : ∀ i j, N i j ∈ O) :
    ∀ i j, (M * N) i j ∈ O := by
  intro i j
  rw [Matrix.mul_apply]
  exact sum_mem fun k _ => mul_mem (hM i k) (hN k j)

end Split

theorem level_subgroup_split : Formalism.UG.LevelVSplit := by
  intro F E _ _ _ _ _ n _ _ σ J v φ hσ hS hu g hg
  obtain ⟨u, huO, huA⟩ := hu
  have hOr : ∀ x : v.adicCompletion F,
      x ∈ Set.range (v.adicCompletionIntegers F).toSubring.subtype ↔
        x ∈ v.adicCompletionIntegers F :=
    fun x => ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩
  have hSr : ∀ x, x ∈ Set.range (algebraMap
      ↥(tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring)
      (E ⊗[F] v.adicCompletion F)) ↔
        x ∈ tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring :=
    fun x => ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩
  have hinjS : Function.Injective (algebraMap
      ↥(tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring)
      (E ⊗[F] v.adicCompletion F)) := Subtype.val_injective
  have hinjO : Function.Injective (v.adicCompletionIntegers F).toSubring.subtype :=
    Subtype.val_injective
  rw [GLint, levelvsplit_mem_range_iff _ hinjO] at huO ⊢
  simp only [hOr] at huO ⊢
  obtain ⟨huO1, huO2⟩ := huO
  have hstab : g ∈ levelV σ J v ↔ g ∈ stabGL (stdLat (n := n)
      ↥(tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring)) :=
    ⟨fun h => h.2, fun h => ⟨hg, h⟩⟩
  rw [hstab, stabilizer_standard_lattice _ _ _ hinjS, levelvsplit_mem_range_iff _ hinjS]
  simp only [hSr, hS]
  rw [← map_inv, levelvsplit_coe_bc, levelvsplit_coe_bc]
  have hJu : (J.map (inclE (F := F) (v.adicCompletion F))).map
      ((RingHom.fst _ _).comp φ.toRingHom) = (u : Matrix n n (v.adicCompletion F)) := by
    rw [huA]; ext i j; rfl
  have rel1 := levelvsplit_unitary _ φ hσ _ g hg
  have rel2 := levelvsplit_unitary _ φ hσ _ g⁻¹ (inv_mem hg)
  rw [hJu] at rel1 rel2
  have hg1 : (g : Matrix n n _).map ((RingHom.fst _ _).comp φ.toRingHom) *
      ((g⁻¹ : GL n _) : Matrix n n _).map ((RingHom.fst _ _).comp φ.toRingHom) = 1 := by
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hg2 : ((g⁻¹ : GL n _) : Matrix n n _).map ((RingHom.fst _ _).comp φ.toRingHom) *
      (g : Matrix n n _).map ((RingHom.fst _ _).comp φ.toRingHom) = 1 := by
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  have hA : (u : Matrix n n (v.adicCompletion F)) * ((u⁻¹ : GL n _) : Matrix n n _) = 1 :=
    u.mul_inv
  have s1 := levelvsplit_solve _ _ _ _ _ hA hg1 rel1
  have s2 := levelvsplit_solve _ _ _ _ _ hA hg2 rel2
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun i j => (h1 i j).1, fun i j => (h2 i j).1⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j => ⟨h1 i j, ?_⟩, fun i j => ⟨h2 i j, ?_⟩⟩
    · have e := congrFun (congrFun s1 i) j
      have hint := levelvsplit_int_mul _ _ _
        (levelvsplit_int_mul _ _ _ huO1 (fun a b => h2 a b)) huO2 j i
      have : ((g : Matrix n n _).map ((RingHom.snd _ _).comp φ.toRingHom)) i j ∈
          v.adicCompletionIntegers F := by
        rw [e]; exact hint
      exact this
    · have e := congrFun (congrFun s2 i) j
      have hint := levelvsplit_int_mul _ _ _
        (levelvsplit_int_mul _ _ _ huO1 (fun a b => h1 a b)) huO2 j i
      have : (((g⁻¹ : GL n _) : Matrix n n _).map ((RingHom.snd _ _).comp φ.toRingHom)) i j ∈
          v.adicCompletionIntegers F := by
        rw [e]; exact hint
      exact this

end Formalism.UG.P
