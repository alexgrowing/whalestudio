import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterDeRham
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyClosedOfDictClosed
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.LocTied6
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitDetEmbMat
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneNotMemFilOne
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal
open scoped Classical

namespace GlobalTheory.CompanionTheory.DeRhamChar

open Module GroundTheory.PAdicHodge

variable {l : ℕ} [Fact l.Prime]

theorem exists_inv_fil (a : ℤ) (x : Formalism.Per6.BdR l) (h1 : x ∈ Formalism.Per6.FilD l a) (h2 : x ∉ Formalism.Per6.FilD l (a + 1)) :
    ∃ y ∈ Formalism.Per6.FilD l (-a), x * y = 1 := by
  have hϖ := IsPerfectoidField.maximalIdeal_eq_span_varpi ℂ_[l] l
  have hne := IsPerfectoidField.algebraMap_ne_zero_of_maximalIdeal_eq_span hϖ
  obtain ⟨b, rfl⟩ := (IsPerfectoidField.mem_fil_iff hϖ).1 h1
  have hb : IsUnit b := by
    by_contra hb
    have hm : b ∈ IsLocalRing.maximalIdeal _ := (IsLocalRing.mem_maximalIdeal _).2 hb
    rw [hϖ, Ideal.mem_span_singleton] at hm
    obtain ⟨c, rfl⟩ := hm
    refine h2 ((IsPerfectoidField.mem_fil_iff hϖ).2 ⟨c, ?_⟩)
    rw [map_mul, zpow_add₀ hne, zpow_one, mul_assoc]
  obtain ⟨u, rfl⟩ := hb
  refine ⟨_, (IsPerfectoidField.mem_fil_iff hϖ).2 ⟨((u⁻¹ : (Formalism.Per6.BdRp l)ˣ) : Formalism.Per6.BdRp l), rfl⟩, ?_⟩
  have h3 : algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l) (u : Formalism.Per6.BdRp l) *
      algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l) ((u⁻¹ : (Formalism.Per6.BdRp l)ˣ) : Formalism.Per6.BdRp l) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have h4 := mul_inv_cancel₀ (zpow_ne_zero a hne)
  rw [zpow_neg]
  generalize algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l) (u : Formalism.Per6.BdRp l) = A at *
  generalize algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l) ((u⁻¹ : (Formalism.Per6.BdRp l)ˣ) : Formalism.Per6.BdRp l) = A' at *
  generalize (algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l) (IsPerfectoidField.varpi ℂ_[l] l) ^ a)⁻¹ = C at *
  generalize algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l) (IsPerfectoidField.varpi ℂ_[l] l) ^ a = D at *
  linear_combination (A * A') * h4 + h3

theorem exists_gal (K : FinExt l) {LL : Type} [Field LL] [Algebra ℚ_[l] LL] (τ : ↥K.1 →ₐ[ℚ_[l]] LL)
    (σ σ' : LL →ₐ[ℚ_[l]] Om l) (h : σ.comp τ = K.1.val) (h' : σ'.comp τ = K.1.val) :
    ∃ g : ↥(GK K), ∀ x, (g : GQ l) (σ x) = σ' x := by
  letI : Algebra LL (Om l) := σ.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ_[l] LL (Om l) := .of_algebraMap_eq fun x => (σ.commutes x).symm
  haveI : Normal ℚ_[l] (Om l) := IsAlgClosure.normal ℚ_[l] (Om l)
  let g₀ : Om l →ₐ[ℚ_[l]] Om l := σ'.liftNormal (Om l)
  have hg₀ : ∀ x, g₀ (σ x) = σ' x := fun x => AlgHom.liftNormal_commutes σ' (Om l) x
  let g : GQ l := AlgEquiv.ofBijective g₀ (Algebra.IsAlgebraic.algHom_bijective g₀)
  refine ⟨⟨g, ?_⟩, hg₀⟩
  rw [GK, IntermediateField.mem_fixingSubgroup_iff]
  intro c hc
  have h1 : σ (τ ⟨c, hc⟩) = c := DFunLike.congr_fun h ⟨c, hc⟩
  have h2 : σ' (τ ⟨c, hc⟩) = c := DFunLike.congr_fun h' ⟨c, hc⟩
  change g₀ c = c
  rw [← h1, hg₀, h1, h2]

section

variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O)

theorem repE_toGL1 (LL' : FinExt l) (ψ : ↥Gw →* (↥LL'.1)ˣ) (g : ↥(GK Bw.Kw)) (v : Fin 1 → ↥LL'.1) :
    Bw.repE LL' ((PositivityTheory.HodgeLocalCharacter.HLC.toGL1 ↥LL'.1).comp ψ) g v = ((ψ (Bw.e.symm g) : (↥LL'.1)ˣ) : ↥LL'.1) • v := by
  ext i
  rw [Subsingleton.elim i 0]
  simp [LocBridge.repE, PositivityTheory.HodgeLocalCharacter.HLC.toGL1, Matrix.mulVec, dotProduct]

theorem card_emb_le (LL' : FinExt l) (hLL : Bw.LL.1 ≤ LL'.1) [Fintype (↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1)] :
    Fintype.card (↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1) = finrank ℚ_[l] ↥Bw.Kw.1 := by
  haveI : FiniteDimensional ℚ_[l] ↥Bw.Kw.1 := Bw.Kw.2
  rw [← AlgHom.card ℚ_[l] ↥Bw.Kw.1 (Om l)]
  exact Fintype.card_congr
    { toFun := fun τ => LL'.1.val.comp τ
      invFun := fun τ => τ.codRestrict LL'.1.toSubalgebra fun x => hLL (Bw.LL_split τ x)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

end

end GlobalTheory.CompanionTheory.DeRhamChar

open GlobalTheory.CompanionTheory.DeRhamChar Module GlobalTheory.Cmp.JumpDict GroundTheory.PAdicHodge in
theorem GlobalTheory.CompanionTheory.DeRhamChar.isdRJ_inv : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied6 l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O),
      GlobalTheory.Pst.Induces Bw →
    ∀ (LL' : FinExt l), Bw.LL.1 ≤ LL'.1 → ∀ (ψ : ↥(Dec (F := E) A) →* (↥LL'.1)ˣ)
      (J : (↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1) → ℤ),
      PositivityTheory.HodgeLocalCharacter.HLC.IsdRJ Bw P LL' ψ J → PositivityTheory.HodgeLocalCharacter.HLC.IsdRJ Bw P LL' ψ⁻¹ (-J) := by
  intro E Ω _ _ _ _ _ l _ P AI hT w A _ O _ _ _ Bw _ LL' hLL ψ J hJ
  obtain ⟨T⟩ := hT
  haveI : IsDomain P.R.BdR := T.eD.toMulEquiv.isDomain (Formalism.Per6.BdR l)
  haveI : FiniteDimensional ℚ_[l] ↥LL'.1 := LL'.2
  haveI : FiniteDimensional ℚ_[l] ↥Bw.Kw.1 := Bw.Kw.2
  have hOm : ∀ x : Om l, algebraMap (Om l) P.R.BdR x ∈ (P.PD Bw.Kw).Fil 0 := fun x => by
    obtain ⟨y, hy, -⟩ := T.om x
    rw [T.fil, hy]
    exact (IsPerfectoidField.mem_fil_iff (IsPerfectoidField.maximalIdeal_eq_span_varpi ℂ_[l] l)).2
      ⟨y, by simp⟩
  have hval : ∀ (a : ℤ) (x : P.R.BdR), x ∈ (P.PD Bw.Kw).Fil a → x ∉ (P.PD Bw.Kw).Fil (a + 1) →
      ∃ y ∈ (P.PD Bw.Kw).Fil (-a), x * y = 1 := fun a x h1 h2 => by
    obtain ⟨y, hy, hxy⟩ := exists_inv_fil a (T.eD x) ((T.fil _ _ _).1 h1) (fun h => h2 ((T.fil _ _ _).2 h))
    refine ⟨T.eD.symm y, (T.fil _ _ _).2 (by simpa using hy), T.eD.injective ?_⟩
    simpa using hxy
  have hmult : ∀ (τ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1) a,
      multV (P.PD Bw.Kw) (Bw.repE LL' ((PositivityTheory.HodgeLocalCharacter.HLC.toGL1 ↥LL'.1).comp ψ⁻¹)) τ a = if a = -J τ then 1 else 0 :=
    fun τ a => multV_inv (P.PD Bw.Kw) (GK Bw.Kw).subtype Bw.Kw.1.val (fun _ => rfl)
      (fun g x => by rw [P.PD_actdR]; exact P.actQdR_Om _ x)
      (fun g c => (IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 c c.2) hOm hval
      (χ := ψ.comp Bw.e.symm.toMonoidHom) (χ' := ψ⁻¹.comp Bw.e.symm.toMonoidHom)
      (fun g v => repE_toGL1 Bw LL' ψ g v) (fun g v => repE_toGL1 Bw LL' ψ⁻¹ g v)
      (fun g => by simp) τ
      (fun σ σ' h h' => exists_gal Bw.Kw τ σ σ' h h') (J τ) (fun a => hJ.2 τ a) a
  refine ⟨?_, fun τ a => hmult τ a⟩
  have := finrank_ddR_of_one_jump (P.PD Bw.Kw) (card_emb_le Bw LL' hLL)
    (Bw.repE LL' ((PositivityTheory.HodgeLocalCharacter.HLC.toGL1 ↥LL'.1).comp ψ⁻¹)) (fun τ => ⟨-J τ, hmult τ⟩)
  simpa [LocBridge.IsdRE] using this
