import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.CuspOrTwoAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.FormsFiniteGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F UpperTheory.V.Z.Tf.GOne

private theorem add_le_of_strictAnti {n : ℕ} {t : Fin n → ℤ} (ht : StrictAnti t) (d : ℕ) :
    ∀ a b : Fin n, (b : ℕ) = a + d → t b + d ≤ t a := by
  induction d with
  | zero =>
    intro a b h
    have : b = a := Fin.ext (by simpa using h)
    simp [this]
  | succ d ih =>
    intro a b h
    have hb := b.2
    have h1 := ih a ⟨a + d, by omega⟩ rfl
    have h2 : t b < t ⟨a + d, by omega⟩ := ht (Fin.lt_def.2 (by simp; omega))
    push_cast
    omega

private theorem exists_weight {n : ℕ} (m : Multiset ℂ) (hc : Multiset.card m = n) (hn : m.Nodup)
    (hz : ∀ z ∈ m, ∃ k : ℤ, z = (k : ℂ) + ((n : ℂ) - 1) / 2) : ∃ lam : Formalism.BasicNotions.DomWeight n, m = infOfWeight lam := by
  classical
  choose! f hf using hz
  let s : Finset ℤ := m.toFinset.image f
  have hinj : Set.InjOn f m.toFinset := fun a ha b hb e => by
    rw [hf a (by simpa using ha), hf b (by simpa using hb), e]
  have hcs : s.card = n := by
    rw [Finset.card_image_of_injOn hinj, Multiset.toFinset_card_of_nodup hn, hc]
  let e := s.orderEmbOfFin hcs
  let t : Fin n → ℤ := fun k => e k.rev
  have ht : StrictAnti t := fun a b h => e.strictMono (Fin.rev_lt_rev.2 h)
  refine ⟨⟨fun k => t k + (k : ℕ), fun a b hab => ?_⟩, ?_⟩
  · have hab' : (a : ℕ) ≤ b := hab
    have := add_le_of_strictAnti ht ((b : ℕ) - a) a b (by omega)
    have e1 : (((b : ℕ) - (a : ℕ) : ℕ) : ℤ) = (b : ℕ) - (a : ℕ) := by omega
    simp only
    omega
  · have h1 : (Finset.univ.val.map fun k : Fin n => e k) = s.val :=
      congrArg Finset.val (Finset.map_orderEmbOfFin_univ s hcs)
    have h2 : s.val = m.map f := by
      rw [Finset.image_val_of_injOn hinj, Multiset.toFinset_val, Multiset.dedup_eq_self.2 hn]
    have h3 : m = (m.map f).map fun k : ℤ => (k : ℂ) + ((n : ℂ) - 1) / 2 := by
      rw [Multiset.map_map]
      conv_lhs => rw [← Multiset.map_id m]
      exact Multiset.map_congr rfl fun z hz => hf z hz
    refine h3.trans ?_
    rw [← h2, ← h1, Multiset.map_map, infOfWeight]
    conv_lhs => rw [← Finset.map_univ_equiv Fin.revPerm, Finset.map_val, Multiset.map_map]
    refine Multiset.map_congr rfl fun k _ => ?_
    simp only [Function.comp, Function.Embedding.coeFn_mk, Equiv.coe_toEmbedding, Fin.revPerm_apply]
    push_cast
    ring

theorem UpperTheory.V.Z.Tf.GOne.onePre :
    OnePre := by
  intro E _ _ _ n hn π hr hd
  have hl : ∀ w, ∃ σ, IsLocCompGL π.V w σ := fun w =>
    (GlobalTheory.CuspRep.LocEx.exists_isLocComp UpperTheory.V.Af.formsFiniteGL E n π w).imp fun σ h =>
      ((cuspSub_iff π).2.1 w σ).2 h.1
  choose σ hσ using hl
  refine ⟨⟨1, fun _ => n, by simp, fun _ => π.V, fun _ w => σ w, fun _ τ => (CG.mk π).infChar τ,
    fun _ => hn, fun _ => hd, fun _ w => hσ w, fun _ τ => ?_⟩, ⟨rfl, fun _ => ⟨rfl, rfl⟩⟩, fun τ => ?_⟩
  · exact ((cuspSub_iff π).2.2 τ _).2 (GlobalTheory.CuspRep.ParLaws.hasInfChar_infChar (CG.mk π) τ)
  · obtain ⟨h1, h2⟩ := hr τ
    obtain ⟨lam, hlam⟩ := exists_weight _ ((CG.mk π).card_infChar τ) h1 h2
    exact ⟨lam, by simpa using hlam⟩
