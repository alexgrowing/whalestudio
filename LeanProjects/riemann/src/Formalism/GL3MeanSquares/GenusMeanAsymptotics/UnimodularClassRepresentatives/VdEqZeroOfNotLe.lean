import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AlgebraMapIntCastSmul
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LinearIndependentOfGramDetNeZero

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.LocF

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem aniso_of_totPosDef {h : V →ₗ⋆[K] V →ₗ[K] K} (hd : IsTotPosDef h) :
    ∀ x, h x x = 0 → x = 0 := by
  intro x hx
  by_contra hne
  obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have := hd x hne φ
  rw [hx, map_zero] at this
  simp at this

theorem exists_gram {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {n : ℕ} (x : Fin n → V) (hx : ∀ i, x i ∈ L) :
    ∃ g : Matrix (Fin n) (Fin n) (𝓞 K), (∀ i j, algebraMap (𝓞 K) K (g i j) = h (x i) (x j)) ∧
      algebraMap (𝓞 K) K g.det = (Matrix.of fun i j => h (x i) (x j)).det := by
  choose g hg using fun i j => Submodule.mem_one.mp (hLi (x i) (hx i) (x j) (hx j))
  refine ⟨Matrix.of g, hg, ?_⟩
  rw [RingHom.map_det]
  congr 1
  ext i j
  exact hg i j

theorem discrIdeal_ne_bot [FiniteDimensional K V] {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hd : ∀ x, h x x = 0 → x = 0) {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L)
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) : discrIdeal h L ≠ ⊥ := by
  choose n hn hnx using fun i => Formalism.HermitianLatticesTheory.traceReal_mult L hL (finBasis K V i)
  have hli : LinearIndependent K (fun i => n i • finBasis K V i) := by
    have h1 := (finBasis K V).linearIndependent.units_smul
      (fun i => Units.mk0 (n i : K) (by exact_mod_cast hn i))
    convert h1 using 1
    funext i
    rw [Pi.smul_apply', Units.smul_def, Units.val_mk0, Int.cast_smul_eq_zsmul]
  obtain ⟨g, -, hdet⟩ := exists_gram hLi _ hnx
  intro hbot
  have hmem : g.det ∈ discrIdeal h L := Ideal.subset_span ⟨_, hnx, hdet⟩
  rw [hbot, Ideal.mem_bot] at hmem
  apply gram_det_ne_zero h hd _ hli
  rw [← hdet, hmem, map_zero]

theorem vd_eq_zero_of_not_le {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)}
    (hn : ¬ discrIdeal h L ≤ extP K 𝔭) : vd h L 𝔭 = 0 := by
  unfold vd
  have h1 : {e : ℕ | discrIdeal h L ≤ extP K 𝔭 ^ e} = {0} := by
    ext e
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · intro he
      by_contra h0
      exact hn (he.trans (Ideal.pow_le_self h0))
    · rintro rfl
      rw [pow_zero, Ideal.one_eq_top]
      exact le_top
  rw [h1, csSup_singleton]

theorem not_le_of_vd_eq_zero {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)}
    (hD : discrIdeal h L ≠ ⊥) (hE : extP K 𝔭 ≠ ⊤) (h0 : vd h L 𝔭 = 0) :
    ¬ discrIdeal h L ≤ extP K 𝔭 := by
  intro hle
  have hb : BddAbove {e : ℕ | discrIdeal h L ≤ extP K 𝔭 ^ e} := by
    by_contra hnb
    rw [not_bddAbove_iff] at hnb
    apply hD
    rw [eq_bot_iff, ← Ideal.iInf_pow_eq_bot_of_isDomain (extP K 𝔭) hE]
    refine le_iInf fun k => ?_
    obtain ⟨e, he, hke⟩ := hnb k
    exact he.trans (Ideal.pow_le_pow_right hke.le)
  have h1 : 1 ≤ vd h L 𝔭 := le_csSup hb (by simpa using hle)
  omega

end Formalism.HermitianLattices.Ext.L3.LocF
