import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.ReducibleThreeDim
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.IsPtOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.RootOfCharpoly
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.TanCocIsBK
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.BlochKatoNonpositiveWeight
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.CoboundaryLemmaNoColumn
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.PtShape
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.NormO

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem norm_lt_one_of_nonunit {l : ℕ} [Fact l.Prime] (c : Coef l) (b : c.O) (hb : ¬ IsUnit b) :
    ‖(b : PadicAlgCl l)‖ < 1 := by
  haveI := c.dvr
  haveI := c.fin
  by_cases h0 : b = 0
  · subst h0
    simp
  have hv0 : IsDiscreteValuationRing.addVal c.O b ≠ 0 := fun h =>
    hb (IsDiscreteValuationRing.addVal_eq_zero_iff.mp h)
  have hvt : IsDiscreteValuationRing.addVal c.O b ≠ ⊤ := fun h =>
    h0 (IsDiscreteValuationRing.addVal_eq_top_iff.mp h)
  have hk : (IsDiscreteValuationRing.addVal c.O b).toNat ≠ 0 := by
    intro h
    rw [ENat.toNat_eq_zero] at h
    tauto
  have key := normO l c.O b h0
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hr : ((l : ℝ)⁻¹) ^ (IsDiscreteValuationRing.addVal c.O b).toNat < 1 :=
    pow_lt_one₀ (by positivity) (inv_lt_one_of_one_lt₀ hl) hk
  by_contra hge
  push_neg at hge
  have h1 := one_le_pow₀ (n := (eO l c.O).toNat) hge
  linarith

private theorem isLocPt_toBar {l : ℕ} [Fact l.Prime] {c : Coef l} {R : Type} [CommRing R] [Algebra c.O R]
    [IsCO c.O R] (x : R →ₐ[c.O] c.O) : IsLocPt (toBar x) := by
  intro y hy
  have hsurj : Function.Surjective x := fun a => ⟨algebraMap c.O R a, x.commutes a⟩
  have hmax : (Ideal.comap (x : R →+* c.O) (IsLocalRing.maximalIdeal c.O)).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ hsurj
  have heq := IsLocalRing.eq_maximalIdeal hmax
  have hy' : y ∈ Ideal.comap (x : R →+* c.O) (IsLocalRing.maximalIdeal c.O) := heq ▸ hy
  have hxy : x y ∈ IsLocalRing.maximalIdeal c.O := hy'
  exact norm_lt_one_of_nonunit c (x y) ((IsLocalRing.mem_maximalIdeal _).mp hxy)

private theorem map_reducible_three_dim {G R S : Type} [Group G] [CommRing R] [CommRing S] (f : R →+* S) (η : G →* ℤˣ)
    (Ψ : G →* Rˣ) : (GG.map f).comp (r0 η Ψ) = r0 η ((Units.map f.toMonoidHom).comp Ψ) := by
  ext g : 1
  apply SemidirectProduct.ext
  · apply Units.ext
    ext i j
    simp only [MonoidHom.comp_apply, GG.map, r0, MonoidHom.coe_mk, OneHom.coe_mk,
      SemidirectProduct.map_left, GeneralLinearGroup.map_apply, tor_val, RingHom.mapMatrix_apply]
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.map_apply, Matrix.diagonal_apply_eq]
      exact congrArg Units.val (map_zpow (Units.map (f : R →* S)) (Ψ g) (wt1 i))
    · simp [Matrix.diagonal_apply_ne _ hij]
  · simp [GG.map, r0]

private theorem coboundary_of_mem_B1 {Γ κ : Type} [Group Γ] [CommRing κ] (r : Γ →* GG 3 κ)
    (γ : Γ → Matrix (Fin 3) (Fin 3) κ) (h : γ ∈ ReciprocityTheory.Gal.B1 (adRep r)) : ∃ X, γ = cob r X := by
  obtain ⟨X, hX⟩ := LinearMap.mem_range.mp h
  refine ⟨-X, ?_⟩
  funext g
  rw [← hX]
  show adRep r g X - X = -X - adRep r g (-X)
  rw [map_neg]
  abel

private theorem isPush_push {O Γ R κ : Type} [CommRing O] [Group Γ] [CommRing R] [Algebra O R] [CommRing κ]
    [Algebra O κ] (f : R →ₐ[O] κ) (r : Γ →* GG 3 R) : IsPush (f.comp (entAlg O r).val) r (push f r) := by
  intro g
  refine ⟨rfl, fun a b => ⟨?_, rfl⟩⟩
  unfold entAlg
  exact Algebra.subset_adjoin ⟨g, a, b, rfl⟩

theorem UpperTheory.V.Th.ptHyp_of :
    Th.InpU → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) {U : D.ULoc} {g₁ : G ℚ Ω}, D.Marked g₁ → ∀ (S : D.Ring U g₁), ∀ [IsCMField K] (ι : Qbar l ≃+* ℂ), Aut.AutB D ι g₁ → Aut.LemW D ι g₁ →
      ∀ x₀ : S.R →ₐ[c.O] c.O, IsBase D.η D.Ψ S.r.hom x₀ → PtHyp D.η S.r.hom x₀ := by
  intro hI Ω _ _ _ K _ _ _ l _ c N _ e ψ D U g₁ hM S _ ι hB hW x₀ hx
  have h0 : push (toBar x₀) S.r.hom = r0 D.η D.ΨQ := by
    have e1 : push (toBar x₀) S.r.hom =
        (GG.map (algebraMap c.O (PadicAlgCl l))).comp (push x₀ S.r.hom) := rfl
    rw [e1, show push x₀ S.r.hom = r0 D.η D.Ψ from hx, map_reducible_three_dim]
    rfl
  refine ⟨fun f hf hU hL => ?_, fun j hj F hF hw => ?_, fun f hf F hF => ?_⟩
  · rw [h0]
    exact pt_fixed hI.toCohInp D hM (isPt_push D hM S f hf) hU hL
  · have h1 := tanCoc_isBK hI.toCohInp D hM S F (hF ▸ isLocPt_toBar x₀)
    rw [hF, h0] at h1
    rw [h0]
    exact coboundary_of_mem_B1 _ _ (bloch_kato_nonpositive_weight hI.toCohInp D j hj _ h1.1 hw h1.2)
  · have h1 := tanCoc_isBK hI.toCohInp D hM S F (hF ▸ hf.1)
    rw [hF] at h1
    have hp := isPt_push D hM S f hf.1
    have hz : Af.BlochKatoSelmerVanishes l (adRep (push f S.r.hom)) := by
      rcases (twoPt_shape S D.gd.l_odd hM f hf).1 with h | h
      · exact hI.rigI D hM S f hf.1 hp.mult ι h (hB U S _ _ hp.mult (isPush_push f _) h)
      · exact Th.blochKatoSelmer_adRep_vanishes_of_typeII_modular hI D hM S f hf.1 ι h
          (hW U S _ _ (isPush_push f _) h (typeII_facts hI.toCohInp D hM hp h).1)
    exact coboundary_of_mem_B1 _ _ (hz _ h1.1 h1.2)
