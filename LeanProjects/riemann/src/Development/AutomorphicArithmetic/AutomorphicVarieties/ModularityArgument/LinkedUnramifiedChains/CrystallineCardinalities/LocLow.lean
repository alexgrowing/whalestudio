import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.UnitStep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.CjFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.DualCard
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.WtCut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.OkFin

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J

namespace UpperTheory.V.Z.J

private def triG (A : Type) [CommRing A] : AddSubgroup (Matrix (Fin 3) (Fin 3) A) where
  carrier := {X | UpT X}
  add_mem' := fun {a b} ha hb i j h => by
    rw [Matrix.add_apply, ha i j h, hb i j h, add_zero]
  zero_mem' := fun _ _ _ => rfl
  neg_mem' := fun {a} ha i j h => by rw [Matrix.neg_apply, ha i j h, neg_zero]

private theorem triG_card (A : Type) [CommRing A] [Finite A] : Nat.card A ^ 6 ≤ Nat.card (triG A) := by
  classical
  let f : ({p : Fin 3 × Fin 3 // p.1 ≤ p.2} → A) → triG A := fun g =>
    ⟨fun i j => if h : i ≤ j then g ⟨(i, j), h⟩ else 0, by
      show UpT _
      intro i j hij
      simp [not_le.mpr hij]⟩
  have hf : Function.Injective f := by
    intro g g' hgg
    funext p
    have := congrArg (fun x : triG A => (x : Matrix (Fin 3) (Fin 3) A) p.1.1 p.1.2) hgg
    simpa [f, p.2] using this
  have h1 := Nat.card_le_card_of_injective f hf
  rw [Nat.card_fun] at h1
  have h6 : Nat.card {p : Fin 3 × Fin 3 // p.1 ≤ p.2} = 6 := by
    rw [Nat.card_eq_fintype_card]; decide
  rwa [h6] at h1

private def zcG {D N : Type} [Group D] [TopologicalSpace D] [AddCommGroup N] (ρ : Representation ℤ D N) :
    AddSubgroup (D → N) where
  carrier := Zc ρ
  add_mem' := fun {a b} ha hb => ⟨ha.1.add hb.1, fun s t => by
    simp only [Pi.add_apply, ha.2 s t, hb.2 s t, map_add]; abel⟩
  zero_mem' := ⟨IsLocallyConstant.const 0, fun s t => by simp⟩
  neg_mem' := fun {a} ha => ⟨ha.1.neg, fun s t => by
    simp only [Pi.neg_apply, ha.2 s t, map_neg]; abel⟩

private theorem local_lower_triangular_cohomology (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] [Finite A] (D : Type) [Group D]
    [TopologicalSpace D] [IsTopologicalGroup D] (I : Subgroup D) (ε : D →* ℤ_[l]ˣ) (d k : ℕ) (hk : 0 < k)
    (hA : ∀ x : A, l ^ k • x = 0) (hLE : LE l D ε d) (hI : GenI l I d)
    (c : D → Matrix (Fin 3) (Fin 3) A → Matrix (Fin 3) (Fin 3) A)
    (ρ : Representation ℤ D (Matrix (Fin 3) (Fin 3) A)) (hc : ∀ s X, ρ s X = c s X) (ho : IsOpen (ρ.ker : Set D))
    (hT : ∀ s X, UpT X → UpT (c s X) ∧ ∀ i, c s X i i = X i i)
    (W : Set (D → Matrix (Fin 3) (Fin 3) A))
    (hW : ∀ z, z ∈ W ↔ IsLocallyConstant z ∧ (∀ s s', z (s * s') = z s + c s (z s')) ∧ (∀ s, UpT (z s)) ∧
      ∀ s ∈ I, ∀ i, z s i i = 0) :
    W.Finite ∧ Nat.card A ^ (6 + 3 * d) ≤ W.ncard := by
  classical
  have hAm : ∀ x : Matrix (Fin 3) (Fin 3) A, l ^ k • x = 0 := fun x => by
    ext i j; simp [hA]
  have hWZ : W ⊆ Zc ρ := fun z hz => by
    obtain ⟨h1, h2, -, -⟩ := (hW z).1 hz
    exact ⟨h1, fun s t => by rw [h2, hc]⟩
  have hWfin : W.Finite := ((hLE k hk _ ρ hAm ho).1).subset hWZ
  refine ⟨hWfin, ?_⟩
  have hmem : ∀ s (x : triG A), ρ s x.1 ∈ triG A := fun s x => by
    show UpT _
    rw [hc]; exact (hT s x.1 x.2).1
  let f : D → (triG A →+ triG A) := fun s =>
    { toFun := fun x => ⟨ρ s x.1, hmem s x⟩
      map_zero' := Subtype.ext (map_zero (ρ s))
      map_add' := fun x y => Subtype.ext (map_add (ρ s) x.1 y.1) }
  let ρ' : Representation ℤ D (triG A) :=
    { toFun := fun s => (f s).toIntLinearMap
      map_one' := LinearMap.ext fun x => Subtype.ext (by
        show ρ 1 x.1 = x.1
        rw [map_one]; rfl)
      map_mul' := fun s t => LinearMap.ext fun x => Subtype.ext (by
        show ρ (s * t) x.1 = ρ s (ρ t x.1)
        rw [map_mul]; rfl) }
  have hρ' : ∀ s (x : triG A), (ρ' s x).1 = ρ s x.1 := fun s x => rfl
  have hker' : IsOpen (ρ'.ker : Set D) := by
    refine Subgroup.isOpen_mono (fun s hs => ?_) ho
    rw [MonoidHom.mem_ker] at hs ⊢
    exact LinearMap.ext fun x => Subtype.ext (by rw [hρ', hs]; rfl)
  have hNk : ∀ x : triG A, l ^ k • x = 0 := fun x =>
    Subtype.ext (by rw [AddSubgroup.coe_nsmul, hAm]; rfl)
  obtain ⟨hZfin, hZcard⟩ := hLE k hk (triG A) ρ' hNk hker'
  have h0 : (0 : D → triG A) ∈ Zc ρ' := ⟨IsLocallyConstant.const 0, fun s t => by simp⟩
  have hpos : 0 < (Zc ρ').ncard := (Set.ncard_pos hZfin).mpr ⟨0, h0⟩
  have hHom : 0 < (HomMu l k ε ρ').ncard := by
    rcases Nat.eq_zero_or_pos (HomMu l k ε ρ').ncard with h | h
    · rw [hZcard, h, mul_zero] at hpos; exact absurd hpos (lt_irrefl 0)
    · exact h
  have hbig : Nat.card A ^ (6 + 6 * d) ≤ (Zc ρ').ncard := by
    rw [hZcard]
    calc Nat.card A ^ (6 + 6 * d) = (Nat.card A ^ 6) ^ (1 + d) := by
          rw [← pow_mul]; congr 1; ring
      _ ≤ Nat.card (triG A) ^ (1 + d) := Nat.pow_le_pow_left (triG_card A) _
      _ ≤ _ := Nat.le_mul_of_pos_right _ hHom
  let Z := zcG ρ'
  haveI : Finite Z := hZfin.to_subtype
  let p : Fin 3 → (triG A →+ A) := fun j =>
    { toFun := fun x => x.1 j j, map_zero' := rfl, map_add' := fun x y => rfl }
  have hp : ∀ z ∈ Z, IsLocallyConstant z ∧
      ∀ (j : Fin 3) (s s' : D), p j (z (s * s')) = p j (z s) + p j (z s') := by
    intro z hz
    have hz' : z ∈ Zc ρ' := hz
    refine ⟨hz'.1, fun j s s' => ?_⟩
    show (z (s * s')).1 j j = (z s).1 j j + (z s').1 j j
    rw [hz'.2 s s']
    show (z s).1 j j + (ρ s (z s').1) j j = _
    rw [hc, (hT s _ (z s').2).2 j]
  have hcut := wtCut l D I d k 3 A (triG A) hI hA Z inferInstance p hp
  have hZc : Nat.card Z = (Zc ρ').ncard := Nat.card_coe_set_eq (Zc ρ')
  have hSW : {z | z ∈ Z ∧ ∀ (j : Fin 3), ∀ s ∈ I, p j (z s) = 0}.ncard ≤ W.ncard := by
    refine Set.ncard_le_ncard_of_injOn (fun z s => (z s).1) ?_ ?_ hWfin
    · rintro z ⟨hz, hI0⟩
      have hz' : z ∈ Zc ρ' := hz
      rw [hW]
      refine ⟨hz'.1.comp _, fun s s' => ?_, fun s => (z s).2, fun s hs i => hI0 i s hs⟩
      show (z (s * s')).1 = (z s).1 + c s (z s').1
      rw [hz'.2 s s', ← hc]; rfl
    · intro z _ z' _ h
      funext s; exact Subtype.ext (congrFun h s)
  have hApos : 0 < Nat.card A ^ (3 * d) := pow_pos Nat.card_pos _
  refine Nat.le_of_mul_le_mul_right ?_ hApos
  calc Nat.card A ^ (6 + 3 * d) * Nat.card A ^ (3 * d) = Nat.card A ^ (6 + 6 * d) := by
        rw [← pow_add]; congr 1; ring
    _ ≤ (Zc ρ').ncard := hbig
    _ = Nat.card Z := hZc.symm
    _ ≤ _ := hcut
    _ ≤ W.ncard * Nat.card A ^ (3 * d) := Nat.mul_le_mul_right _ hSW

end UpperTheory.V.Z.J

theorem UpperTheory.V.Z.J.locLow :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (D : Type) [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [CompactSpace D] (I : Subgroup D) (ε : D →* ℤ_[l]ˣ) (d : ℕ) (t : D →* GL (Fin 3) O), (l : O) ≠ 0 → LE l D ε d → GenI l I d → TriRep t → ∀ k, 0 < k → (ZF (l := l) I k t).Finite ∧ Nat.card (Ok l O k) ^ (6 + 3 * d) ≤ (ZF (l := l) I k t).ncard := by
  intro l _ O _ _ _ _ _ D _ _ _ _ I ε d t hl hLE hI ht k hk
  obtain ⟨hf, -, hA, -⟩ := okFin l O hl
  obtain ⟨⟨ρ, hc, ho⟩, -, hT, -⟩ := cjFacts l O D t k hl ht
  haveI := hf k
  exact local_lower_triangular_cohomology l (Ok l O k) D I ε d k hk (hA k) hLE hI (cj k t) ρ hc ho
    (fun s X hX => ⟨(hT s X hX).1, (hT s X hX).2.1⟩) _ (fun _ => Iff.rfl)
