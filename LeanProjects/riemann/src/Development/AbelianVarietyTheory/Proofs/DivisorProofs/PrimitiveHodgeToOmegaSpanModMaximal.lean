import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsCharZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamFreeBaseChangeRigid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaBaseChangeBijectiveOfIsNilpotent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeToOmegaCanonicalExtensionBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHodgeFiltrationToPDivOmegaLinearMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveHodgeToPdivisibleOmegaSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRelativeDimensionAbelianVarietyField
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem sup_smul_top_eq_top_of_span {R M N : Type} [CommRing R] (I : Ideal R) [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module (R ⧸ I) N] (om : M →ₛₗ[algebraMap R (R ⧸ I)] N)
    (hinj : Function.Injective (PDiv.liftSemi om)) (S : Submodule R M)
    (hall : ∀ y : N, y ∈ Submodule.span (R ⧸ I) (om '' (S : Set M))) :
    S ⊔ I • (⊤ : Submodule R M) = ⊤ := by
  let f := TensorProduct.mk R (R ⧸ I) M 1
  have hsf : ∀ x, PDiv.liftSemi om (f x) = om x := fun x => by simp [f]
  have hmemK : ∀ x, f x ∈ Submodule.span (R ⧸ I) (f '' (S : Set M)) := by
    intro x
    have h1 : PDiv.liftSemi om (f x) ∈ Submodule.map (PDiv.liftSemi om)
        (Submodule.span (R ⧸ I) (f '' (S : Set M))) := by
      have himg : (⇑(PDiv.liftSemi om) ∘ ⇑f) '' (S : Set M) = om '' (S : Set M) :=
        Set.image_congr fun a _ => hsf a
      rw [Submodule.map_span, ← Set.image_comp, himg, hsf]
      exact hall _
    obtain ⟨z, hz, hzx⟩ := Submodule.mem_map.1 h1
    have hz' : z = f x := hinj hzx
    subst hz'
    exact hz
  let Q : Submodule (R ⧸ I) ((R ⧸ I) ⊗[R] M) :=
    { carrier := Submodule.map f S
      add_mem' := fun ha hb => Submodule.add_mem _ ha hb
      zero_mem' := Submodule.zero_mem _
      smul_mem' := by
        intro a z hz
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
        obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hz
        refine Submodule.mem_map.2 ⟨r • w, Submodule.smul_mem _ r hw, ?_⟩
        rw [map_smul]
        exact (algebraMap_smul (R ⧸ I) r (f w)).symm }
  have hQ : Submodule.span (R ⧸ I) (f '' (S : Set M)) ≤ Q := by
    rw [Submodule.span_le]
    rintro _ ⟨a, ha, rfl⟩
    exact Submodule.mem_map_of_mem ha
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.1 (hQ (hmemK x))
  have hxy : x - y ∈ I • (⊤ : Submodule R M) := by
    have h0 : f (x - y) = 0 := by rw [map_sub, hyx, sub_self]
    have h2 := congrArg (TensorProduct.quotTensorEquivQuotSMul M I) h0
    rw [map_zero] at h2
    simp only [f, TensorProduct.mk_apply] at h2
    rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero] at h2
    exact h2
  have hx : x = y + (x - y) := by abel
  rw [hx]
  exact Submodule.add_mem_sup hy hxy

theorem psi_sup_smul_top_eq_top : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (p : ℕ) [Fact p.Prime]  (R : Type) [CommRing R] (N : ℕ), (p : R) ^ N = 0 → ∀ (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (G : PDivGroup p R) (t : G.TorsionTower A) (ψ : PrimitiveSubmodule A →ₗ[R] G.omega), (∀ c : PrimitiveSubmodule A, IsCan t c.1 (G.rigOfOmega (ψ c))) → ∀ I : Ideal R, I.IsMaximal → LinearMap.range ψ ⊔ I • (⊤ : Submodule R G.omega) = ⊤ := by
  intro hH p _ R _ N hN A _ g hA hg G t ψ hψ I hI
  obtain ⟨-, hBC, -⟩ := GlobalTheory.abelianDeRham_free_baseChange_rigid hH
  letI : Field (R ⧸ I) := Ideal.Quotient.field I
  have hNk : ((p : ℕ) : R ⧸ I) ^ N = 0 := by
    rw [← map_natCast (algebraMap R (R ⧸ I)), ← map_pow, hN, map_zero]
  have hk0 : ((p : ℕ) : R ⧸ I) = 0 := pow_eq_zero_iff'.1 hNk |>.1
  letI : GrpObj ((Over.pullback (spMap (algebraMap R (R ⧸ I)))).obj A) := Functor.grpObjObj
  have h := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_pullback A (spMap (algebraMap R (R ⧸ I)))
  have hAk : IsAbelianScheme ((Over.pullback (spMap (algebraMap R (R ⧸ I)))).obj A) :=
    GlobalTheory.isAbelianScheme_pullback_obj _ A hA
  obtain ⟨gk, hgk⟩ := GlobalTheory.AbVarRelDim.exists_relDim (R ⧸ I) _ hAk
  obtain ⟨ψk, hψk⟩ := GlobalTheory.T.exists_hodgeFiltration_to_pDivOmega_linearMap p (R ⧸ I) N hNk _ hAk (G.baseChange (R ⧸ I)) (t.baseChange h)
  have hsurj := GlobalTheory.T.primitive_hodge_to_pdivisible_omega_surjective hH p (R ⧸ I) hk0 _ gk hAk hgk _ _ ψk hψk
  have hbc := GlobalTheory.T.hodgeToOmega_canonical_extension_base_change p R (R ⧸ I) N hN A _ _ h hA hAk G _ t (t.baseChange h) ψ ψk hψ hψk
  rw [t.semiHom_baseChange h] at hbc
  have hF := (hBC R A g hA hg (R ⧸ I) _ _ h).2
  have hom := GlobalTheory.PDivGroup.omega_baseChange_bijective_of_isNilpotent p R (R ⧸ I) ⟨N, hN⟩ G

  let T : Submodule (R ⧸ I) (G.baseChange (R ⧸ I)).omega :=
    Submodule.span (R ⧸ I) ((G.toBase (R ⧸ I)).omega '' (LinearMap.range ψ : Set G.omega))
  have hle : PrimitiveSubmodule ((Over.pullback (spMap (algebraMap R (R ⧸ I)))).obj A) ≤
      Submodule.map (PrimitiveSubmodule _).subtype (T.comap ψk) := by
    refine hF.le.trans (Submodule.span_le.2 ?_)
    rintro _ ⟨c, hc, rfl⟩
    have hc' : (GlobalTheory.Published.AbelianDeRham.bcMor h).pull c ∈
        PrimitiveSubmodule ((Over.pullback (spMap (algebraMap R (R ⧸ I)))).obj A) :=
      hF ▸ Submodule.subset_span ⟨c, hc, rfl⟩
    refine ⟨⟨_, hc'⟩, ?_, rfl⟩
    show ψk ⟨_, hc'⟩ ∈ T
    rw [hbc ⟨c, hc⟩ hc']
    exact Submodule.subset_span ⟨ψ ⟨c, hc⟩, LinearMap.mem_range_self _ _, rfl⟩
  have hall : ∀ y, y ∈ T := by
    intro y
    obtain ⟨c, rfl⟩ := hsurj y
    obtain ⟨c', hc', he⟩ := Submodule.mem_map.1 (hle c.2)
    have : c' = c := Subtype.ext he
    subst this
    exact hc'
  exact sup_smul_top_eq_top_of_span I _ hom.1 _ hall

end GlobalTheory.PtExt
