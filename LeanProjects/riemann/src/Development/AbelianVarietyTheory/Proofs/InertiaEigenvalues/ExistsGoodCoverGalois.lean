import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteDimensionalZeta
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RationalRayLevels
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.MainNotions.StandardLattice Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverGalois

theorem fieldRange_of_normal (L : IntermediateField ℚ ℂ) [hN : Normal ℚ L] (f : L →+* ℂ) :
    f.toRatAlgHom.fieldRange = L :=
  @AlgHom.fieldRange_of_normal ℚ ℂ _ _ _ L (by convert hN; exact Subsingleton.elim _ _) f.toRatAlgHom

theorem exists_goodCover_galois (D : D7) {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type}
    {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
    (hJ : LawsJ T) (i : Fin D.R.m) (hj : InR D ((i : ℕ) + 1)) (n pd : ℕ) (I : Ideal (𝓞 D.host.E))
    (haux : GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.IsAuxiliarySplitSquarefreeLevel D T.Q.l.M pd)
    (hK : I = Ideal.span {x | x ∈ I ∧ x ∈ Algebra.adjoin ℤ {T.Q.H.w0}})
    (hprod : I * I.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = Ideal.span {(pd : 𝓞 D.host.E)})
    (hsup : I ⊔ I.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = ⊤)
    (L : IntermediateField ℚ ℂ) [FiniteDimensional ℚ L] [Normal ℚ L] (hle : T.Q.c.F ≤ L)
    (hz : zeta (T.Q.l.M * pd) ∈ L) (hsm : GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SmallIn R i (L.val : L →+* ℂ))
    (hray : GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.RayIn D (T.Q.l.M * pd) L.toSubfield) :
    ∃ C : Cover T ((i : ℕ) + 1) T.σ₀, C.d.pd = pd ∧ C.d.I = I ∧ C.σ₂.fieldRange = L.toSubfield ∧
      GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.GoodCover T R i C n := by
  have hσ : GoodEmb T.Q.c T.σ₀ := T.toCore.good_σ₀
  obtain ⟨hodd, -, -, hcop, -⟩ := id haux
  have hnum := GlobalTheory.T.numerical_consequences_of_pins D T.Q hJ.toLawsM.pins
  have hA : T.Q.l.A = 1 := hnum.2.1
  have hpq : 1 ≤ (T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q := by
    have := hnum.2.2.2.2.2.2 _ hj; omega
  obtain ⟨l₂, hd, hM, hMb, hA₂⟩ := (GlobalTheory.exists_level_mul_split _ T.Q.H T.Q.l).1 pd I hodd hcop hK hprod hsup
  obtain ⟨Xo₂⟩ := GlobalTheory.T.exists_moduli_scheme_polarized_abelian_level _ T.Q.H (T.Q.Dw ((i : ℕ) + 1)) l₂ hpq
  let c' : Coeff T.Q.l :=
    { F := L, fin := inferInstance, conj := fun τ a => hle (T.Q.c.conj τ a)
      zeta_mem := hle T.Q.c.zeta_mem, le := T.Q.c.le.trans hle }
  have hM' : l₂.M' = T.Q.l.M * pd := by
    rw [Level.M', hA₂, hA, hM, Nat.lcm_one_right]
  let c₂ : Coeff l₂ :=
    { F := c'.F, fin := c'.fin, conj := c'.conj
      zeta_mem := by rw [hM']; exact hz
      le := by have h := c'.le; unfold KA at h ⊢; rw [hA₂]; exact h }
  obtain ⟨d, hdpd, hdI, hdl, -, -, -, hlev, -⟩ := GlobalTheory.LevelCover.exists_deltaDat_isLev _ T.Q.H (T.Q.Dw ((i : ℕ) + 1)) T.Q.l
    (T.Q.Xo ((i : ℕ) + 1)) c' hpq 0 pd I l₂ Xo₂ c₂ rfl hd hM hcop hMb hsup
  obtain ⟨σ', hσ'⟩ := GlobalTheory.CoverExists.exists_ext_of_le (K := T.Q.c.F) (L := L) hle T.σ₀
  let σ₂ : d.c₂.F →+* ℂ := σ'.comp (d.eF.symm : d.c₂.F →+* c'.F)
  have hσ₂ : σ₂.comp ((d.eF : c'.F →+* d.c₂.F).comp (incF T.Q.c c' hle)) = T.σ₀ := by
    rw [← hσ']; ext x; simp [σ₂, incF]
  have hA1 : d.l₂.A = 1 := by rw [hdl, hA₂, hA]
  obtain ⟨U₂, dict₂, hU⟩ := GlobalTheory.T.exists_levelCover_uniformisation_dictionary D T hJ _ hj T.σ₀ hσ c' hle d σ₂ hlev hA1 hσ₂

  have hrange : (σ'.toRatAlgHom).fieldRange = L := fieldRange_of_normal L σ'
  have hsurj : ∀ y : L, ∃ z : d.c₂.F, σ₂ z = (y : ℂ) := by
    intro y
    have hy : (y : ℂ) ∈ (σ'.toRatAlgHom).fieldRange := by rw [hrange]; exact y.2
    obtain ⟨x, hx⟩ := AlgHom.mem_fieldRange.1 hy
    exact ⟨d.eF x, by simp [σ₂, ← hx]⟩
  have hfr : σ₂.fieldRange = L.toSubfield := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      have : σ' (d.eF.symm z) ∈ (σ'.toRatAlgHom).fieldRange := AlgHom.mem_fieldRange.2 ⟨_, rfl⟩
      rw [hrange] at this
      exact this
    · intro hx
      obtain ⟨z, hz'⟩ := hsurj ⟨x, hx⟩
      exact ⟨z, hz'⟩
  have hsm₂ : GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SmallIn R i σ₂ := by
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · obtain ⟨y, hy⟩ := hsm.1 v hv
      obtain ⟨z, hz'⟩ := hsurj y
      exact ⟨z, hz'.trans hy⟩
    · obtain ⟨y, hy⟩ := hsm.2 v hv
      obtain ⟨z, hz'⟩ := hsurj y
      exact ⟨z, hz'.trans hy⟩
  let C₀ : Cover T ((i : ℕ) + 1) T.σ₀ := ⟨c', hle, d, σ₂, U₂, dict₂, fun _ => 1⟩
  have hdom : ∀ m, Even m → Dom (0 : (D.host.E →+* ℂ) × ℕ → ℕ) m := fun m hm =>
    ⟨fun _ _ _ _ => le_rfl, hm⟩
  have hauxd : GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.IsAuxiliarySplitSquarefreeLevel D T.Q.l.M d.pd := hdpd ▸ haux
  by_cases hn : Even n
  · obtain ⟨cc₂, hcc⟩ := GlobalTheory.T.uniformisedLevelCover_exists_constants_dominantWeights D T hJ _ hj T.σ₀ hσ C₀ (hU _) n
    refine ⟨⟨c', hle, d, σ₂, U₂, dict₂, cc₂⟩, hdpd, hdI, hfr, hU cc₂, hcc, hauxd, hsm₂, ?_⟩
    show GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.RayIn D (T.Q.l.M * d.pd) σ₂.fieldRange
    rw [hfr, hdpd]; exact hray
  · obtain ⟨cc₂, hcc⟩ := GlobalTheory.T.uniformisedLevelCover_exists_constants_dominantWeights D T hJ _ hj T.σ₀ hσ C₀ (hU _) 0
    refine ⟨⟨c', hle, d, σ₂, U₂, dict₂, cc₂⟩, hdpd, hdI, hfr, hU cc₂, fun a ha => absurd ha.2 hn, hauxd, hsm₂, ?_⟩
    show GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.RayIn D (T.Q.l.M * d.pd) σ₂.fieldRange
    rw [hfr, hdpd]; exact hray

end GlobalTheory.CoverGalois
