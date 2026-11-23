import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HeckePairTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHkMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwLeviSum
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

section SlopeTestRemainingChoices

variable {G : Type} [Group G]

private theorem mem_stab (I : Subgroup G) (z g : G) :
    g ∈ MulAction.stabilizer G (z : G ⧸ I) ↔ z⁻¹ * g * z ∈ I := by
  rw [MulAction.mem_stabilizer_iff, MulAction.Quotient.smul_coe, eq_comm, QuotientGroup.eq, smul_eq_mul, mul_assoc]

private theorem ncard_orb (I K : Subgroup G) (q : G ⧸ I) :
    (MulAction.orbit K q).ncard = (MulAction.stabilizer G q).relIndex K := by
  rw [← MulAction.index_stabilizer]
  rfl

private theorem count (I : Subgroup G) (x y : G)
    (hA : ∀ g ∈ I, (x * y)⁻¹ * g * (x * y) ∈ I → x⁻¹ * g * x ∈ I)
    (hB : ∀ b ∈ I, ∃ b' ∈ I, x * b' * x⁻¹ ∈ I ∧ y⁻¹ * (b'⁻¹ * b) * y ∈ I) :
    (MulAction.orbit I ((x * y : G) : G ⧸ I)).ncard =
      (MulAction.orbit I (x : G ⧸ I)).ncard * (MulAction.orbit I (y : G ⧸ I)).ncard := by
  have h1 : MulAction.orbit (MulAction.stabilizer G (x : G ⧸ I) ⊓ I : Subgroup G) ((x * y : G) : G ⧸ I) =
      (fun q : G ⧸ I => x • q) '' MulAction.orbit I (y : G ⧸ I) := by
    ext q
    constructor
    · rintro ⟨⟨g, hg, hg'⟩, rfl⟩
      refine ⟨_, ⟨⟨x⁻¹ * g * x, (mem_stab I x g).1 hg⟩, rfl⟩, ?_⟩
      show ((x * (x⁻¹ * g * x * y) : G) : G ⧸ I) = ((g * (x * y) : G) : G ⧸ I)
      congr 1
      group
    · rintro ⟨_, ⟨⟨b, hb⟩, rfl⟩, rfl⟩
      obtain ⟨b', hb', h1, h2⟩ := hB b hb
      refine ⟨⟨x * b' * x⁻¹, (mem_stab I x _).2 (by simpa [mul_assoc] using hb'), h1⟩, ?_⟩
      show ((x * b' * x⁻¹ * (x * y) : G) : G ⧸ I) = ((x * (b * y) : G) : G ⧸ I)
      rw [QuotientGroup.eq]
      convert h2 using 1
      group
  have h2 := ncard_orb I (MulAction.stabilizer G (x : G ⧸ I) ⊓ I) ((x * y : G) : G ⧸ I)
  rw [h1, Set.ncard_image_of_injective _ (MulAction.injective x)] at h2
  rw [h2, ncard_orb, ncard_orb, mul_comm, ← Subgroup.inf_relIndex_right (MulAction.stabilizer G (x : G ⧸ I)),
    ← Subgroup.inf_relIndex_right _ (MulAction.stabilizer G (x : G ⧸ I) ⊓ I),
    Subgroup.relIndex_mul_relIndex _ _ _ inf_le_right inf_le_right,
    ← Subgroup.inf_relIndex_right (MulAction.stabilizer G ((x * y : G) : G ⧸ I))]
  congr 1
  refine le_antisymm (fun g hg => ⟨hg.1, ?_, hg.2⟩) fun g hg => ⟨hg.1, hg.2.2⟩
  exact (mem_stab I x g).2 (hA g hg.2 ((mem_stab I _ g).1 hg.1))

private theorem split_mem {I : Subgroup G} (F : LeviFact I) {u j : G} (hu : u ∈ F.Uf) (hj : j ∈ F.Mf) (h : u * j ∈ I) :
    u ∈ I ∧ j ∈ I := by
  obtain ⟨u', hu', j', hj', l, hl, e⟩ := F.fact _ h
  have := F.uniq (j'⁻¹ * (u'⁻¹ * u) * j'⁻¹⁻¹) (F.M_U _ (inv_mem hj'.1) _ (mul_mem (inv_mem hu'.1) hu)) (j'⁻¹ * j)
    (mul_mem (inv_mem hj'.1) hj) l⁻¹ (inv_mem hl.1) (by
      calc _ = j'⁻¹ * u'⁻¹ * (u * j) * l⁻¹ := by group
        _ = 1 := by rw [e]; group)
  have h2 : j = j' := (inv_mul_eq_one.1 this.2).symm
  have h3 : j ∈ I := h2 ▸ hj'.2
  exact ⟨by simpa using mul_mem h (inv_mem h3), h3⟩

end SlopeTestRemainingChoices

theorem UpperTheory.V.AlgebraTools.leviMul :
    ∀ (A G M : Type) [CommRing A] [Group G] [AddCommGroup M] [Module A M] (ρ : Representation A G M) (I : Subgroup G) (F : LeviFact I) (m m' : G), HeckePair I → F.Pos m → F.Pos m' → (F.NormJ m ∨ F.NormJ m') → F.Pos (m * m') ∧ hk ρ I m * hk ρ I m' = hk ρ I (m * m') := by
  intro A G M _ _ _ _ ρ I F m m' hI hm hm' hN
  have hP : F.Pos (m * m') := by
    refine ⟨mul_mem hm.1 hm'.1, fun u hu => ?_, fun l hl => ?_⟩
    · have := hm.2.1 _ ⟨F.M_U _ hm'.1 u hu.1, hm'.2.1 u hu⟩
      convert this using 1
      group
    · have := hm'.2.2 (m⁻¹ * l * m) ⟨by simpa using F.M_L _ (inv_mem hm.1) l hl.1, hm.2.2 l hl⟩
      convert this using 1
      group
  have hB : ∀ b ∈ I, ∃ b' ∈ I, m * b' * m⁻¹ ∈ I ∧ m'⁻¹ * (b'⁻¹ * b) * m' ∈ I := by
    intro b hb
    obtain ⟨u, hu, j, hj, l, hl, rfl⟩ := F.fact b hb
    rcases hN with hN | hN
    · refine ⟨u * j, mul_mem hu.2 hj.2, ?_, ?_⟩
      · convert mul_mem (hm.2.1 u hu) (hN j hj).1 using 1
        group
      · convert hm'.2.2 l hl using 1
        group
    · refine ⟨u, hu.2, hm.2.1 u hu, ?_⟩
      convert mul_mem (hN j hj).2 (hm'.2.2 l hl) using 1
      group
  have hA : ∀ g ∈ I, (m * m')⁻¹ * g * (m * m') ∈ I → m⁻¹ * g * m ∈ I := by
    intro g hg h
    obtain ⟨u, hu, j, hj, l, hl, rfl⟩ := F.fact g hg
    have hU : (m * m')⁻¹ * u * (m * m') ∈ F.Uf := by
      simpa using F.M_U _ (inv_mem hP.1) u hu.1
    have hJ : (m * m')⁻¹ * j * (m * m') ∈ F.Mf := mul_mem (mul_mem (inv_mem hP.1) hj.1) hP.1
    obtain ⟨h1, h2⟩ := split_mem F hU hJ (by
      convert mul_mem h (inv_mem (hP.2.2 l hl)) using 1
      group)
    have h3 : m⁻¹ * u * m ∈ I := by
      convert hm'.2.1 _ ⟨hU, h1⟩ using 1
      group
    have h4 : m⁻¹ * j * m ∈ I := by
      rcases hN with hN | hN
      · exact (hN j hj).2
      · convert (hN _ ⟨hJ, h2⟩).1 using 1
        group
    convert mul_mem (mul_mem h3 h4) (hm.2.2 l hl) using 1
    group
  refine ⟨hP, hkMul A G M ρ I m m' hI (fun b hb => ?_) (count I m m' hA hB)⟩
  obtain ⟨b', -, h1, h2⟩ := hB b hb
  exact ⟨_, h1, _, h2, by group⟩
