import Formalism.LocalToGlobal.GlobalTheory.GL4.PMsDual

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions NumberField Formalism.MainNotions.flipTwoThree

section Keys

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def keyOf (S : HSpace E) (b : Module.Basis (Fin S.rank) E S.V) (L : Submodule (𝓞 E) S.V) :
    Matrix (Fin S.rank) (Fin S.rank) E × Submodule (𝓞 E) (Fin S.rank → E) :=
  (fun i j => S.hT (b i) (b j), L.map ((b.equivFun : S.V →ₗ[E] (Fin S.rank → E)).restrictScalars (𝓞 E)))

theorem equivFun_equiv (S : HSpace E) (b b' : Module.Basis (Fin S.rank) E S.V) (x : S.V) :
    b'.equivFun (b.equiv b' (Equiv.refl _) x) = b.equivFun x := by
  have h : (b'.equivFun.toLinearMap ∘ₗ (b.equiv b' (Equiv.refl _)).toLinearMap) = b.equivFun.toLinearMap := by
    refine b.ext fun i => ?_
    simp [Module.Basis.equiv_apply]
  exact LinearMap.congr_fun h x

theorem isoLat_of_key (S : HSpace E) (b b' : Module.Basis (Fin S.rank) E S.V) (L L' : Submodule (𝓞 E) S.V)
    (h : keyOf S b L = keyOf S b' L') : IsoLat S L L' := by
  obtain ⟨hG, hC⟩ := Prod.ext_iff.1 h
  set γ := b.equiv b' (Equiv.refl _) with hγ
  refine ⟨γ, fun x y => ?_, fun x => ?_⟩
  · have hB : (S.hT.compl₂ γ.toLinearMap).comp γ.toLinearMap = S.hT := by
      refine LinearMap.ext_basis b b fun i j => ?_
      have := congrFun (congrFun hG i) j
      simp only [keyOf] at this
      simp only [LinearMap.comp_apply, LinearMap.compl₂_apply, LinearEquiv.coe_coe, hγ,
        Module.Basis.equiv_apply, Equiv.refl_apply]
      exact this.symm
    have := LinearMap.congr_fun₂ hB x y
    simpa using this
  · have hfun := equivFun_equiv S b b' x
    constructor
    · intro hx
      have hm : b.equivFun x ∈ (keyOf S b L).2 := Submodule.mem_map_of_mem (f := _) hx
      rw [h] at hm
      obtain ⟨x', hx', hxe⟩ := Submodule.mem_map.1 hm
      have : x' = γ x := b'.equivFun.injective (by rw [hfun]; exact hxe)
      rw [← this]; exact hx'
    · intro hx
      have hm : b'.equivFun (γ x) ∈ (keyOf S b' L').2 := Submodule.mem_map_of_mem (f := _) hx
      rw [← h, hfun] at hm
      obtain ⟨x', hx', hxe⟩ := Submodule.mem_map.1 hm
      have : x' = x := b.equivFun.injective hxe
      rw [← this]; exact hx'

def KeyBound (S : HSpace E) (q : ℕ) (B : ℝ) : Prop :=
  ∃ K : Finset (Matrix (Fin S.rank) (Fin S.rank) E × Submodule (𝓞 E) (Fin S.rank → E)),
    Real.log K.card ≤ B ∧
    ∀ L : Submodule (𝓞 E) S.V, Submodule.IsLattice E L → LatT S q L →
      ∃ b : Module.Basis (Fin S.rank) E S.V, keyOf S b L ∈ K

theorem iso_reps_of_keyBound (S : HSpace E) (q : ℕ) (B : ℝ) (hK : KeyBound S q B) {ι : Type} [Fintype ι]
    (L : ι → Submodule (𝓞 E) S.V) (hL : ∀ c, Submodule.IsLattice E (L c) ∧ LatT S q (L c)) :
    ∃ R : Finset ι, (∀ c, ∃ r ∈ R, IsoLat S (L c) (L r)) ∧ Real.log R.card ≤ B := by
  classical
  obtain ⟨K, hKB, hKL⟩ := hK
  have hB : 0 ≤ B := le_trans (Real.log_natCast_nonneg _) hKB
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨∅, fun c => (IsEmpty.false c).elim, by simpa using hB⟩
  choose b hb using fun c => hKL (L c) (hL c).1 (hL c).2
  let k : ι → _ := fun c => keyOf S (b c) (L c)
  refine ⟨(Finset.univ.image k).image (Function.invFun k), fun c => ?_, ?_⟩
  · refine ⟨Function.invFun k (k c), Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ (Finset.mem_univ c)), ?_⟩
    exact isoLat_of_key S (b c) (b _) (L c) (L _) (Function.invFun_eq (f := k) ⟨c, rfl⟩).symm
  · have h1 : ((Finset.univ.image k).image (Function.invFun k)).card ≤ K.card := by
      refine le_trans Finset.card_image_le (Finset.card_le_card ?_)
      intro κ hκ
      obtain ⟨c, _, rfl⟩ := Finset.mem_image.1 hκ
      exact hb c
    rcases Nat.eq_zero_or_pos ((Finset.univ.image k).image (Function.invFun k)).card with h0 | h0
    · rw [h0, Nat.cast_zero, Real.log_zero]; exact hB
    · refine le_trans (Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast h1)) hKB

end Keys

section KeysRecord

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem isoCount_of_keys (D : D7) (C₀ : ℝ)
    (h : ∀ u : D.what₂.Word,
      (∀ i ≤ D.R.m, KeyBound (D.sp.X i) (Tu D u ^ (2 * D.R.f)) (msLat D u C₀ (D.R.N i))) ∧
      KeyBound D.sp.X' 1 (msLat D u C₀ (D.R.N D.R.m - 1))) : IsoCount D C₀ := by
  intro u
  exact ⟨fun i hi ι _ L hL => iso_reps_of_keyBound _ _ _ ((h u).1 i hi) L hL,
    fun ι _ L hL => iso_reps_of_keyBound _ _ _ (h u).2 L hL⟩

theorem msCount_of_keys (D : D7) (C₀ : ℝ) (hC : 1 ≤ C₀)
    (h : ∀ u : D.what₂.Word,
      (∀ i ≤ D.R.m, KeyBound (D.sp.X i) (Tu D u ^ (2 * D.R.f)) (msLat D u C₀ (D.R.N i))) ∧
      KeyBound D.sp.X' 1 (msLat D u C₀ (D.R.N D.R.m - 1))) : MsCount D C₀ :=
  msCount_of_isoCount D C₀ hC (isoCount_of_keys D C₀ h)

end KeysRecord

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
