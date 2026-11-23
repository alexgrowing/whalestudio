import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LayerLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.PartModel
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.SignLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.EigV
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.VLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsOnto

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

theorem UpperTheory.V.HV.redPrime :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ), Chr.HasLevel E N H → ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ¬ l ∣ H.index →
      ∀ (c : Coef l) [HasEnoughRootsOfUnity c.O (Nat.totient N)] (Ω' : Type) [Field Ω'] [Algebra E Ω'] [IsAlgClosure E Ω'] (D : LData E Ω' l)
        (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (e : ℕ), e ≠ 0 → ∀ T : Finset (DirichletCharacter c.O N), (T : Set _) = Chr.evenSet c.O H e →
        plusLen D e * eO l c.O ≤ ∑ ψ ∈ T, Vlen Ω c e ψ := by
  intro E _ _ _ N _ H hH l _ hl2 hlH c _ Ω' _ _ _ D Ω _ _ _ e he T hT
  haveI := c.dvr
  haveI := c.fin
  obtain ⟨σ, hσ, hplus, -⟩ := Chr.partModel E N H hH l c.O Ω' D Ω e
  haveI hroots : HasEnoughRootsOfUnity c.O (Monoid.exponent ((ZMod N)ˣ ⧸ H)) := by
    have hdvd : Monoid.exponent ((ZMod N)ˣ ⧸ H) ∣ Nat.totient N := by
      refine Group.exponent_dvd_nat_card.trans ?_
      rw [← Subgroup.index_eq_card, ← ZMod.card_units_eq_totient, ← Nat.card_eq_fintype_card]
      exact Subgroup.index_dvd_card H
    exact HasEnoughRootsOfUnity.of_dvd c.O hdvd
  rw [hplus]
  refine (Chr.signLe Ω N H l c.O hl2 e e σ hσ T (by rw [hT])).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun χ hχ => ?_
  have hχ' : χ ∈ Chr.evenSet c.O H e := by
    have : χ ∈ (T : Set _) := hχ
    rwa [hT] at this
  have hker : H ≤ (MulChar.toUnitHom χ).ker := hχ'.1
  obtain ⟨hopen, -⟩ := Chr.clsFacts ℚ Ω N
  have hsurj := (Chr.clsOnto Ω N).1
  have hUopen : IsOpen ((Chr.levH ℚ Ω H : Subgroup (G ℚ Ω)) : Set (G ℚ Ω)) := by
    refine Subgroup.isOpen_mono ?_ hopen
    intro g hg
    show Chr.cls ℚ Ω N g ∈ H
    rw [MonoidHom.mem_ker.mp hg]
    exact H.one_mem
  have hUker : Chr.levH ℚ Ω H ≤ (Chr.dirG ℚ Ω χ).ker := by
    intro g hg
    exact hker hg
  have hidx : (Chr.levH ℚ Ω H).index = H.index :=
    Subgroup.index_comap_of_surjective H hsurj
  have hHidx : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rw [Chr.eigV ℚ Ω l c.O e (Chr.dirG ℚ Ω χ) (Chr.levH ℚ Ω H) hUopen hUker (by rwa [hidx])]
  have hψopen : IsOpen ((Chr.dirG ℚ Ω χ).ker : Set (G ℚ Ω)) :=
    Subgroup.isOpen_mono hUker hUopen
  have hpow : Chr.dirG ℚ Ω χ ^ H.index = 1 := by
    refine MonoidHom.ext fun g => ?_
    have hm : (Chr.cls ℚ Ω N g) ^ H.index ∈ H := Subgroup.pow_index_mem H _
    have := hker hm
    rw [MonoidHom.mem_ker, map_pow] at this
    rw [MonoidHom.pow_apply, MonoidHom.one_apply]
    exact this
  exact ((Chr.vLe Ω l c.O N e H.index (Chr.dirG ℚ Ω χ) (NeZero.ne N) he hHidx hψopen hpow).2 hlH)
