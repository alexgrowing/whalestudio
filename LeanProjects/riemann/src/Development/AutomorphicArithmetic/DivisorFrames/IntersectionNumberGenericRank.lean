import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.VertCmp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntersectionNumberEqGenericRankMulProjCurve
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.Toroidal
open GlobalTheory.VertCmp
open scoped Classical

private theorem UpperTheory.withBot_enat_lt_of_add_one_le {x : WithBot ℕ∞} {d : ℕ} (h : x + 1 ≤ (d : WithBot ℕ∞)) :
    x < (d : WithBot ℕ∞) := by
  induction x using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe (d : ℕ∞)
  | coe x =>
    have h' : x + 1 ≤ (d : ℕ∞) := by exact_mod_cast h
    have hx : x ≠ ⊤ := by
      rintro rfl
      simp at h'
    have : x < (d : ℕ∞) := (ENat.add_one_le_iff hx).1 h'
    exact_mod_cast this

private theorem UpperTheory.suppDim_lt_of_genRank_zero {Z : Scheme.{0}} [IsIntegral Z] {d : ℕ}
    (hd : topologicalKrullDim Z ≤ (d : WithBot ℕ∞)) {F : Z.Modules} [QCoh.IsFiniteQC F]
    (h : VB.genRank F = 0) : QCoh.suppDim F < (d : WithBot ℕ∞) := by
  have := topologicalKrullDim_add_one_le (QCoh.isClosed_support F) isClosed_univ
    fun x _ => ⟨genericPoint Z, trivial, VB.genRank_eq_zero_iff.1 h, genericPoint_specializes x⟩
  have e : topologicalKrullDim (Set.univ : Set Z) = topologicalKrullDim Z := by
    rw [← QCoh.suppDim_structureModule, QCoh.suppDim, QCoh.support_structureModule]
  rw [e] at this
  exact UpperTheory.withBot_enat_lt_of_add_one_le (this.trans hd)

theorem UpperTheory.intersection_number_generic_rank :
    ∀ (κ : Type) [Field κ] (Z : Scheme.{0}) [IsIntegral Z] [Algebra κ Γ(Z, ⊤)], IsProjOver (strHom κ Z) → ∀ (d : ℕ), topologicalKrullDim Z ≤ (d : WithBot ℕ∞) → ∀ (L : Fin d → LB Z), (∀ j, (L j).IsLB) → ∀ (G : Z.Modules), GlobalTheory.QCoh.IsFiniteQC G → interNum κ G L = (GlobalTheory.VB.genRank G : ℤ) * interNum κ (structureModule Z) L := by
  intro κ _ Z _ _ hp d hd L hL
  have hf := algebraMap_eq_strHom κ Z
  have h1 : ∀ {F : Z.Modules} [QCoh.IsFiniteQC F], FiniteCohTwists κ F :=
    fun {F} _ => finiteCohTwists_of_isProjOver hf F hp
  obtain ⟨_, A, hA⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hp
  suffices H : ∀ (r : ℕ) (G : Z.Modules) [QCoh.IsFiniteQC G], VB.genRank G = r →
      interNum κ G L = r * interNum κ (structureModule Z) L from
    fun G _ => H _ G rfl
  intro r
  induction r with
  | zero =>
    intro G _ h
    have : QCoh.suppDim G < Fintype.card (Fin d) := by
      rw [Fintype.card_fin]
      exact UpperTheory.suppDim_lt_of_genRank_zero hd h
    rw [interNum_eq_zero_of_isProjOver hf G hp this hL]
    simp
  | succ r ih =>
    intro G _ h
    obtain ⟨n, hn⟩ := (hA.eventually_isGloballyGenerated_twist G).exists
    have hM := isLB_lbPow hA.isLB n
    have := Twist.isFiniteQC_twist (F := G) hM
    have hr : VB.genRank (twist G (lbPow A n)) = r + 1 := (VB.genRank_twist hM).trans h
    obtain ⟨s, hs⟩ := VB.exists_germ_ne_zero hn (by omega)
    have := VB.mono_sectionHom s hs
    have e₁ : interNum κ (twist G (lbPow A n)) L = interNum κ G L :=
      (diffVanish_chiPic_of_isProjOver (d := d) hf G hp
        ((QCoh.suppDim_le G).trans hd)).interNum_twist (by simp) hL hM
    have e₂ := interNum_cokernel (k := κ) (QCoh.sectionHom s) hL h1 h1
    have e₃ := VB.genRank_cokernel (QCoh.sectionHom s)
    rw [(VB.isVB_structureModule Z).genRank_eq, hr] at e₃
    rw [ih _ (by omega)] at e₂
    push_cast
    linarith
