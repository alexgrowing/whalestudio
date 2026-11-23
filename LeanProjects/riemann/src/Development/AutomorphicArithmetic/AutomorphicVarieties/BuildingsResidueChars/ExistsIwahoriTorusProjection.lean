import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.SpStab
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.IwahoriProUnipotentFiniteIndex
open IsLocalRing Matrix UpperTheory.V.Hi

private theorem torus_uniq {G : Type} [Group G] (I : Iwa G) {y y' x x' : G} {t t' : I.T} (hy : y ∈ I.Nm 0)
    (hy' : y' ∈ I.Nm 0) (hx : x ∈ I.N) (hx' : x' ∈ I.N) (h : y * t * x = y' * t' * x') : t' = t := by
  have h1 : x = (t : G)⁻¹ * y⁻¹ * (y' * t' * x') := by rw [← h]; group
  have h0 := (I.uniq (x * x'⁻¹) (I.N_le (mul_mem hx (inv_mem hx'))) ((t' : G)⁻¹ * t)
    (I.T_le (mul_mem (inv_mem t'.2) t.2)) ((t : G)⁻¹ * (y'⁻¹ * y) * (t : G)⁻¹⁻¹)
    (I.T_Nm 0 _ (inv_mem t.2) _ (mul_mem (inv_mem hy') hy)) (by rw [h1]; group)).2
  exact Subtype.ext (inv_mul_eq_one.1 h0)

private theorem torus_ex {G : Type} [Group G] (I : Iwa G) {b : G} (hb : b ∈ I.Iw 0) :
    ∃ t : I.T, ∃ y ∈ I.Nm 0, ∃ x ∈ I.N, b = y * t * x := by
  obtain ⟨x, hx, t, ht, y, hy, h⟩ := (UpperTheory.V.Hi.iwMem G I 0 b⁻¹).1.1 (inv_mem hb)
  refine ⟨⟨t⁻¹, inv_mem ht⟩, y⁻¹, inv_mem hy, x⁻¹, inv_mem hx, ?_⟩
  rw [← inv_inv b, h]
  group

private theorem torus_fn {G : Type} [Group G] (I : Iwa G) :
    ∃ tt : G → I.T, ∀ (t : I.T), ∀ y ∈ I.Nm 0, ∀ x ∈ I.N, tt (y * t * x) = t := by
  classical
  refine ⟨fun b => if h : ∃ t : I.T, ∃ y ∈ I.Nm 0, ∃ x ∈ I.N, b = y * t * x then h.choose else 1, ?_⟩
  intro t y hy x hx
  have h : ∃ t' : I.T, ∃ y' ∈ I.Nm 0, ∃ x' ∈ I.N, y * t * x = y' * t' * x' := ⟨t, y, hy, x, hx, rfl⟩
  simp only [dif_pos h]
  obtain ⟨y', hy', x', hx', e⟩ := h.choose_spec
  exact torus_uniq I hy hy' hx hx' e

theorem UpperTheory.exists_iwahori_torus_projection :
    ∀ (G : Type) [Group G] (I : Iwa G), ∃ tt : G → I.T, tt 1 = 1 ∧ ∀ b ∈ I.Iw 0, (∀ s : I.T, tt (s * b) = s * tt b ∧ tt (b * s) = tt b * s) ∧ (∀ x ∈ I.N, tt (b * x) = tt b) ∧ ∀ c, ∀ y ∈ I.Nm c, ∃ s : I.T, (s : G) ∈ I.Tc c ∧ tt (b * y) = tt b * s := by
  intro G _ I
  obtain ⟨tt, htt⟩ := torus_fn I
  refine ⟨tt, by simpa using htt 1 1 (one_mem _) 1 (one_mem _), fun b hb => ?_⟩
  obtain ⟨t, y, hy, x, hx, rfl⟩ := torus_ex I hb
  rw [htt t y hy x hx]
  refine ⟨fun s => ⟨?_, ?_⟩, fun x' hx' => ?_, fun c y' hy' => ?_⟩
  · rw [← htt (s * t) _ (I.T_Nm 0 s s.2 y hy) x hx]
    congr 1
    rw [Subgroup.coe_mul]
    group
  · rw [← htt (t * s) y hy _ (I.T_N _ (inv_mem s.2) x hx)]
    congr 1
    rw [Subgroup.coe_mul]
    group
  · rw [mul_assoc]
    exact htt t y hy _ (mul_mem hx hx')
  · obtain ⟨x2, hx2, s, hs, y2, hy2, h⟩ := I.swap c y'⁻¹ (inv_mem hy') x⁻¹ (inv_mem hx)
    refine ⟨⟨s⁻¹, inv_mem (I.Tc_le c hs)⟩, inv_mem hs, ?_⟩
    rw [← htt (t * ⟨s⁻¹, inv_mem (I.Tc_le c hs)⟩) _
      (mul_mem hy (I.T_Nm 0 t t.2 _ (inv_mem (I.Nm_anti (Nat.zero_le c) hy2)))) _ (inv_mem hx2)]
    congr 1
    have e : x * y' = (x2 * s * y2)⁻¹ := by rw [← h]; group
    rw [mul_assoc, e, Subgroup.coe_mul]
    group
