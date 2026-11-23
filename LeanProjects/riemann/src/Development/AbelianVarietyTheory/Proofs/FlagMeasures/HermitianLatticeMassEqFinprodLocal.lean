import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalExtend
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommonStabilizerStabilizersCommensurableVolume
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrongApproxStabStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelIndexComapPairOfDenseImageStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarInvVolumeRelIndexPiUnivEqFinprodStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NumberFieldLatticeDeterminedByLocalLatticesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoordinateLatticeUniqueTermAlmostAllPlacesStatement

noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.MassProduct

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E)

theorem uniformiser_mem_jacobson (ϖ : 𝒪[F]) (h : Irreducible ϖ) (w : L.O)
    (hw : (w : E) = algebraMap F E (ϖ : F)) : w ∈ (⊥ : Ideal L.O).jacobson := by
  let f : 𝒪[F] →+* L.O := (algebraMap 𝒪[F] E).codRestrict L.O
    (fun x => (L.O_def _).2 isIntegral_algebraMap)
  letI : Algebra 𝒪[F] L.O := f.toAlgebra
  haveI : IsScalarTower 𝒪[F] L.O E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.IsIntegral 𝒪[F] L.O := by
    refine ⟨fun x => ?_⟩
    have h1 : IsIntegral 𝒪[F] (x : E) := (L.O_def (x : E)).1 x.2
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom 𝒪[F] L.O E) Subtype.val_injective).1 h1
  refine Ideal.mem_sInf.2 ?_
  rintro P ⟨-, hP⟩
  haveI := hP
  have hmax : (P.comap (algebraMap 𝒪[F] L.O)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
  have hm : ϖ ∈ P.comap (algebraMap 𝒪[F] L.O) := by
    rw [IsLocalRing.eq_maximalIdeal hmax]
    exact (IsLocalRing.mem_maximalIdeal _).2 h.not_isUnit
  have he : algebraMap 𝒪[F] L.O ϖ = w := by
    apply Subtype.ext
    rw [hw]
    rfl
  rw [Ideal.mem_comap, he] at hm
  exact hm

theorem stabilises_of_close {n : ℕ} (Λ : Submodule L.O (Fin n → E)) (hΛ : Λ.FG) (ϖ : 𝒪[F])
    (h : Irreducible ϖ) (m : (Fin n → E) ≃ₗ[E] (Fin n → E))
    (hm : ∀ x ∈ Λ, ∃ y ∈ Λ, m x - x = algebraMap F E (ϖ : F) • y) :
    m ∈ MulAction.stabilizer ((Fin n → E) ≃ₗ[E] (Fin n → E)) Λ := by
  have hO : algebraMap F E (ϖ : F) ∈ L.O := (L.O_def _).2 (by
    have : IsIntegral 𝒪[F] (algebraMap 𝒪[F] E ϖ) := isIntegral_algebraMap
    exact this)
  let w : L.O := ⟨_, hO⟩
  have hw : w ∈ (⊥ : Ideal L.O).jacobson := uniformiser_mem_jacobson L ϖ h w rfl
  have hle : m • Λ ≤ Λ := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, e⟩ := hm x hx
    have : m x = x + w • y := by
      rw [eq_add_of_sub_eq' e]
      rfl
    change m x ∈ Λ
    rw [this]
    exact Λ.add_mem hx (Λ.smul_mem w hy)
  have hge : Λ ≤ m • Λ := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := Ideal.span {w}) hΛ
      ((Ideal.span_singleton_le_iff_mem _).2 hw) ?_
    intro x hx
    obtain ⟨y, hy, e⟩ := hm x hx
    have hx' : x = m x - w • y := by
      have : m x = x + w • y := by
        rw [eq_add_of_sub_eq' e]
        rfl
      rw [this]; abel
    rw [hx']
    refine Submodule.sub_mem_sup ?_ ?_
    · exact Submodule.smul_mem_pointwise_smul x m Λ hx
    · exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self w) hy
  exact MulAction.mem_stabilizer_iff.2 (le_antisymm hle hge)

end Local

section Global

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
variable (A : Places F E sig) (n : ℕ)

def extMap (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) (p : HeightOneSpectrum (𝓞 F)) :
    (Fin n → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin n → (A.loc p).Ep) :=
  ((RatExt.rational_extend A n p).2.2.1 g).choose

theorem extMap_spec (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) (p : HeightOneSpectrum (𝓞 F)) :
    A.Ext p g (extMap A n g p) :=
  ((RatExt.rational_extend A n p).2.2.1 g).choose_spec.1

theorem extMap_unique {g : (Fin n → E) ≃ₗ[E] (Fin n → E)} {p : HeightOneSpectrum (𝓞 F)}
    {g' : (Fin n → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin n → (A.loc p).Ep)} (h : A.Ext p g g') :
    g' = extMap A n g p :=
  ((RatExt.rational_extend A n p).2.2.1 g).choose_spec.2 g' h

def extHom : ((Fin n → E) ≃ₗ[E] (Fin n → E)) →*
    ∀ p, (Fin n → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin n → (A.loc p).Ep) where
  toFun g := extMap A n g
  map_one' := funext fun p => (extMap_unique A n (g := 1) (g' := 1) fun _ => rfl).symm
  map_mul' a b := funext fun p => (extMap_unique A n (g := a * b)
    (g' := extMap A n a p * extMap A n b p) (fun x => by
      change extMap A n a p (extMap A n b p (A.bc p x)) = A.bc p (a (b x))
      rw [extMap_spec A n b p x, extMap_spec A n a p (b x)])).symm

theorem comap_pi (K : ∀ p, Subgroup ((Fin n → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin n → (A.loc p).Ep))) :
    (Subgroup.pi Set.univ K).comap (extHom A n) = A.rat K := by
  ext g
  constructor
  · intro h p
    exact ⟨extMap A n g p, (Subgroup.mem_pi _).1 h p (Set.mem_univ p), extMap_spec A n g p⟩
  · intro h
    refine (Subgroup.mem_pi _).2 fun p _ => ?_
    obtain ⟨g', hg, he⟩ := h p
    have e : extMap A n g p = g' := (extMap_unique A n he).symm
    change extMap A n g p ∈ K p
    rw [e]
    exact hg

end Global

theorem mass_eq_finprod : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), 4 * r + 7 ≤ k →
    ∀ Λ : G.Lt, Submodule.IsLattice E Λ →
    {p | (G.S p).St ⊓ MulAction.stabilizer (G.S p).GLV (A.lat p Λ) ≠ (G.S p).K0}.Finite ∧
      G.mu Λ = ∏ᶠ p, (G.S p).mu (A.lat p Λ) := by
  intro F E _ _ _ _ _ sig A r k G hk Λ hΛ
  obtain ⟨-, hlat, hcoord⟩ := GlobalTheory.T.numberField_lattice_determined_by_local_lattices A (k + 2 * r + 1) Λ hΛ
  have hstd := GlobalTheory.T.coordinateLattice_unique_term_almost_all_places A r k G hk
  let U : ∀ p, Subgroup (G.S p).GLV :=
    fun p => (G.S p).St ⊓ MulAction.stabilizer (G.S p).GLV (A.lat p Λ)
  let K : ∀ p, Subgroup (G.S p).GLV := fun p => (G.S p).K0
  have hfin : {p | U p ≠ K p}.Finite := by
    refine (hstd.union hcoord).subset ?_
    intro p hp
    by_contra hcon
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hcon
    obtain ⟨h1, h2⟩ := hcon
    apply hp
    change (G.S p).St ⊓ MulAction.stabilizer (G.S p).GLV (A.lat p Λ) = (G.S p).K0
    rw [h2]
    exact h1.2.2.1
  have hKSt : ∀ p, K p ≤ (G.S p).St := fun p x hx => hx.1.1
  have hUSt : ∀ p, U p ≤ (G.S p).St := fun p x hx => hx.1

  let c : ∀ p, ((A.loc p).Fp)ˣ := fun p =>
    if U p ≠ K p then
      haveI := (A.loc p).lf
      Units.mk0 (((G.S p).ϖ : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp)
        (fun h0 => (G.S p).ϖ_irr.ne_zero (Subtype.ext h0))
    else 1
  have hc : {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = c p}.Finite := by
    refine hfin.subset ?_
    intro p hp
    by_contra hcon
    apply hp
    have hu : U p = K p := not_not.1 hcon
    have h1 : c p = 1 := if_neg (not_not.2 hu)
    exact ⟨1, by rw [h1]; simp⟩
  let φ := extHom A (k + 2 * r + 1)
  have hdense : ∀ g, g ∈ Subgroup.pi Set.univ K ∨ g ∈ Subgroup.pi Set.univ U →
      ∃ γ, (φ γ)⁻¹ * g ∈ Subgroup.pi Set.univ K ⊓ Subgroup.pi Set.univ U := by
    intro g hg
    have hgSt : ∀ p, g p ∈ (G.S p).St := by
      intro p
      rcases hg with h | h
      · exact hKSt p ((Subgroup.mem_pi _).1 h p (Set.mem_univ p))
      · exact hUSt p ((Subgroup.mem_pi _).1 h p (Set.mem_univ p))
    have hgfin : {p | g p ∉ (G.S p).K0}.Finite := by
      rcases hg with h | h
      · refine Set.finite_empty.subset ?_
        intro p hp
        exact hp ((Subgroup.mem_pi _).1 h p (Set.mem_univ p))
      · refine hfin.subset ?_
        intro p hp he
        apply hp
        have := (Subgroup.mem_pi _).1 h p (Set.mem_univ p)
        rw [he] at this
        exact this
    obtain ⟨γ, -, hγ⟩ := GlobalTheory.T.exists_mem_St_approximating_local_elements A r k G Λ hΛ c hc g hgSt hgfin
    refine ⟨γ, ?_⟩
    have key : ∀ p, (g p)⁻¹ * φ γ p ∈ K p ⊓ U p := by
      intro p
      obtain ⟨h1, h2⟩ := hγ p (φ γ p) (extMap_spec A _ γ p)
      refine ⟨h1, ?_⟩
      by_cases he : U p = K p
      · rw [he]; exact h1
      · refine ⟨hKSt p h1, ?_⟩
        haveI := (A.loc p).lf
        have hcp : ((c p : ((A.loc p).Fp)ˣ) : (A.loc p).Fp) = (((G.S p).ϖ : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) := by
          have h3 : c p = Units.mk0 (((G.S p).ϖ : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp)
              (fun h0 => (G.S p).ϖ_irr.ne_zero (Subtype.ext h0)) := if_pos he
          rw [h3]
          rfl
        refine stabilises_of_close (A.L p) (A.lat p Λ) (hlat p).1 (G.S p).ϖ (G.S p).ϖ_irr _ ?_
        intro x hx
        obtain ⟨y, hy, e⟩ := h2 x hx
        refine ⟨y, hy, ?_⟩
        rw [← hcp]
        exact e
    have key2 : ∀ p, ((φ γ)⁻¹ * g) p ∈ K p ⊓ U p := by
      intro p
      have := (K p ⊓ U p).inv_mem (key p)
      simpa [mul_inv_rev] using this
    exact ⟨(Subgroup.mem_pi _).2 fun p _ => (key2 p).1, (Subgroup.mem_pi _).2 fun p _ => (key2 p).2⟩
  obtain ⟨hKU, hUK⟩ := GlobalTheory.T.relIndex_comap_pair_of_dense_image φ (Subgroup.pi Set.univ K) (Subgroup.pi Set.univ U) hdense
  have hidx : ∀ p, (K p).relIndex (U p) ≠ 0 ∧ (U p).relIndex (K p) ≠ 0 := by
    intro p
    haveI := (A.loc p).lf
    haveI := (A.loc p).char0
    obtain ⟨a, b, -⟩ := (GlobalTheory.HL.volSt (A.L p) r k (G.S p)).1 (A.lat p Λ) (hlat p)
    exact ⟨a, b⟩
  have hKU' : {p | K p ≠ U p}.Finite := hfin.subset fun p hp h => hp h.symm
  obtain ⟨-, -, hprod⟩ := GlobalTheory.T.haarInvVolumeRelIndex_pi_univ_eq_finprod K U hKU' hidx
  refine ⟨hfin, ?_⟩
  have e1 : G.K0 = (Subgroup.pi Set.univ K).comap φ := (comap_pi A _ K).symm
  have e2 : G.stabL Λ = (Subgroup.pi Set.univ U).comap φ := (comap_pi A _ U).symm
  have hmu : G.mu Λ = invVol (Subgroup.pi Set.univ K) (Subgroup.pi Set.univ U) := by
    unfold GFrames.mu invVol
    rw [e1, e2, hKU, hUK]
  rw [hmu, hprod]
  rfl

end GlobalTheory.HL.MassProduct
