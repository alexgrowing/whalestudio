import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.IwMemMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsIwahoriTorusProjection
open IsLocalRing Matrix UpperTheory.V.Hi

theorem UpperTheory.exists_iwahori_character_extending_torus_character :
    ∀ (G : Type) [Group G] (I : Iwa G) (B : Type) [CommGroup B] (c : ℕ) (φ : I.T →* B), (∀ t : I.T, (t : G) ∈ I.Tc c → φ t = 1) → ∃ ψ : I.Iw c →* B, ∀ b : I.Iw c, ((b : G) ∈ I.N → ψ b = 1) ∧ ((b : G) ∈ I.Nm c → ψ b = 1) ∧ ∀ hb : (b : G) ∈ I.T, ψ b = φ ⟨b, hb⟩ := by
  intro G _ I B _ c φ hφ
  obtain ⟨tt, h1, htt⟩ := UpperTheory.exists_iwahori_torus_projection G I
  have hle : ∀ b ∈ I.Iw c, b ∈ I.Iw 0 := by
    intro b hb
    obtain ⟨x, hx, t, ht, y, hy, h⟩ := (UpperTheory.V.Hi.iwMem G I c b).1.1 hb
    exact (UpperTheory.V.Hi.iwMem G I 0 b).1.2 ⟨x, hx, t, ht, y, I.Nm_anti (Nat.zero_le c) hy, h⟩
  have key : ∀ b ∈ I.Iw 0, ∀ x ∈ I.N, ∀ t : I.T, ∀ y ∈ I.Nm c,
      φ (tt (b * (x * t * y))) = φ (tt b) * φ t := by
    intro b hb x hx t y hy
    have hx0 : x ∈ I.Iw 0 :=
      (UpperTheory.V.Hi.iwMem G I 0 x).1.2 ⟨x, hx, 1, one_mem _, 1, one_mem _, by simp⟩
    have ht0 : (t : G) ∈ I.Iw 0 :=
      (UpperTheory.V.Hi.iwMem G I 0 t).1.2 ⟨1, one_mem _, t, t.2, 1, one_mem _, by simp⟩
    have hbx := mul_mem hb hx0
    obtain ⟨s, hs, e⟩ := (htt _ (mul_mem hbx ht0)).2.2 c y hy
    have e0 : b * (x * t * y) = b * x * t * y := by group
    rw [e0, e, map_mul, hφ s hs, mul_one, ((htt _ hbx).1 t).2, (htt b hb).2.1 x hx, map_mul]
  have key1 : ∀ x ∈ I.N, ∀ t : I.T, ∀ y ∈ I.Nm c, φ (tt (x * t * y)) = φ t := by
    intro x hx t y hy
    have := key 1 (one_mem _) x hx t y hy
    rwa [one_mul, h1, map_one, one_mul] at this
  refine ⟨MonoidHom.mk' (fun b => φ (tt b)) ?_, fun b => ⟨fun hb => ?_, fun hb => ?_, fun hb => ?_⟩⟩
  · intro a b
    obtain ⟨x, hx, t, ht, y, hy, h⟩ := (UpperTheory.V.Hi.iwMem G I c b).1.1 b.2
    have e1 := key a (hle _ a.2) x hx ⟨t, ht⟩ y hy
    have e2 := key1 x hx ⟨t, ht⟩ y hy
    show φ (tt ((a : G) * b)) = φ (tt a) * φ (tt b)
    rw [h, e2]
    exact e1
  · simpa using key1 b hb 1 1 (one_mem _)
  · simpa using key1 1 (one_mem _) 1 b hb
  · simpa using key1 1 (one_mem _) ⟨b, hb⟩ 1 (one_mem _)
