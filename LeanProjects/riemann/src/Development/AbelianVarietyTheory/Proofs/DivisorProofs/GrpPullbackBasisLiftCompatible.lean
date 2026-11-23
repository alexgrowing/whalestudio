import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameTangentVectorsOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
open GlobalTheory ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.LieBasisRing

open GlobalTheory.KSExist.FrameLift

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem isSplitting_embS {l : Level H} (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] :
    EigenSplit.IsSplitting fun σ : E →+* ℂ => (algebraMap c.F S).comp (embK c σ) := by
  refine EigenSplit.isSplitting_of_isDomain (S := c.F) (σ := fun σ : E →+* ℂ => embK c σ) (fun σ σ' e => ?_)
    (NumberField.Embeddings.card E ℂ) _ ?_
  · have e' : embF c σ = embF c σ' := IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) e
    ext x
    have := congrArg (fun f : E →+* c.F => ((f x : c.F) : ℂ)) e'
    exact this
  · have : IsUnit ((NumberField.discr E : ℤ) : c.F) :=
      isUnit_iff_ne_zero.2 (by exact_mod_cast NumberField.discr_ne_zero E)
    simpa using this.map (algebraMap c.F S)

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X}
  {A : Over (Sp S)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left}

theorem isCombAt_of_isLieComb (hπ : IsGrpPullback A Xo.univ.t.G x π) {n : ℕ} (v : Fin n → (epsR S ⟶ A))
    (cf : Fin n → S) (w : epsR S ⟶ A) (h : IsLieComb cf v w) :
    IsCombAt x (fun i => (v i).left ≫ π) cf (w.left ≫ π) := by
  obtain ⟨u, hu, rfl⟩ := h
  refine ⟨fun i => pushHom hπ (epsR S) (u i), fun i => ?_, (push_prod hπ u).symm⟩
  show (u i).left ≫ π = _
  rw [hu i, Category.assoc]
  rfl

end GlobalTheory.LieBasisRing

namespace GlobalTheory.LieBasisRing

theorem span_eq_top {S : Type} [CommRing S] {A : Over (Sp S)} [GrpObj A] [IsCommMonObj A] {O : Type} [CommRing O]
    (a : OAct O A) {ι : Type} [Fintype ι] [DecidableEq ι] {χ : ι → O →+* S} (hχ : EigenSplit.IsSplitting χ)
    {m : ι → ℕ} (ub : ∀ σ, Fin (m σ) → (epsR S ⟶ A)) (hub : ∀ σ k, IsTangent (ub σ k))
    (hbasis : ∀ σ (w : epsR S ⟶ A), IsTangent w → (∀ z, w ≫ a.act z = GlobalTheory.GrpTangent.epsScale (χ σ z) ≫ w) →
      ∃ cf, IsLieComb cf (ub σ) w) :
    Submodule.span S (Set.range fun k : Σ σ, Fin (m σ) => Serre.Lie.mk a (ub k.1 k.2) (hub _ _)) = ⊤ := by
  let ρ : O →+* Module.End S (Serre.Lie a) := Module.toModuleEnd S (S := O) (Serre.Lie a)
  rw [eq_top_iff]
  intro x _
  rw [← EigenSplit.sum_proj hχ ρ x]
  refine Submodule.sum_mem _ fun σ _ => ?_
  have hx := EigenSplit.proj_mem hχ ρ σ x
  obtain ⟨cf, hcf⟩ := hbasis σ (EigenSplit.proj hχ ρ σ x).hom (EigenSplit.proj hχ ρ σ x).isTangent fun z =>
    congrArg Serre.Lie.hom (EigenSplit.mem_eigenSub.1 hx z)
  have e : EigenSplit.proj hχ ρ σ x = ∑ i, cf i • Serre.Lie.mk a (ub σ i) (hub σ i) :=
    Serre.Lie.ext ((Serre.Lie.isLieComb_iff cf (fun i => Serre.Lie.mk a (ub σ i) (hub σ i)) _).1 hcf)
  rw [e]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨σ, i⟩, rfl⟩)

theorem linearIndependent {S : Type} [CommRing S] {A : Over (Sp S)} [GrpObj A] [IsCommMonObj A] {O : Type}
    [CommRing O] (a : OAct O A) {ι : Type} [Fintype ι] [DecidableEq ι] {χ : ι → O →+* S}
    (hχ : EigenSplit.IsSplitting χ) {m : ι → ℕ} (ub : ∀ σ, Fin (m σ) → (epsR S ⟶ A))
    (hub : ∀ σ k, IsTangent (ub σ k))
    (heig : ∀ σ k z, ub σ k ≫ a.act z = GlobalTheory.GrpTangent.epsScale (χ σ z) ≫ ub σ k)
    (huniq : ∀ σ (w : epsR S ⟶ A), IsTangent w → (∀ z, w ≫ a.act z = GlobalTheory.GrpTangent.epsScale (χ σ z) ≫ w) →
      ∀ cf cf', IsLieComb cf (ub σ) w → IsLieComb cf' (ub σ) w → cf = cf') :
    LinearIndependent S fun k : Σ σ, Fin (m σ) => Serre.Lie.mk a (ub k.1 k.2) (hub _ _) := by
  let ρ : O →+* Module.End S (Serre.Lie a) := Module.toModuleEnd S (S := O) (Serre.Lie a)
  let v : (Σ σ, Fin (m σ)) → Serre.Lie a := fun k => Serre.Lie.mk a (ub k.1 k.2) (hub _ _)
  have hmem : ∀ k, v k ∈ EigenSplit.eigenSub ρ (χ k.1) := fun k =>
    EigenSplit.mem_eigenSub.2 fun z => Serre.Lie.ext (heig k.1 k.2 z)
  rw [Fintype.linearIndependent_iff]
  intro g hg k
  obtain ⟨σ, i⟩ := k
  have h1 := congrArg (EigenSplit.proj hχ ρ σ) hg
  rw [map_sum, map_zero, Fintype.sum_sigma] at h1
  have h2 : ∑ j, g ⟨σ, j⟩ • v ⟨σ, j⟩ = 0 := by
    rw [← h1, Finset.sum_eq_single σ]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, EigenSplit.proj_of_mem hχ (hmem ⟨σ, j⟩)]
    · intro σ' _ hσ'
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [map_smul, EigenSplit.proj_of_mem_ne hχ hσ' (hmem ⟨σ', j⟩), smul_zero]
    · intro h; exact absurd (Finset.mem_univ σ) h
  have hw : ∑ j, g ⟨σ, j⟩ • v ⟨σ, j⟩ ∈ EigenSplit.eigenSub ρ (χ σ) :=
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hmem ⟨σ, j⟩)
  have c1 : IsLieComb (fun j => g ⟨σ, j⟩) (ub σ) (∑ j, g ⟨σ, j⟩ • v ⟨σ, j⟩).hom :=
    (Serre.Lie.isLieComb_iff _ (fun j => v ⟨σ, j⟩) _).2 rfl
  have c0 : IsLieComb (0 : Fin (m σ) → S) (ub σ) (∑ j, g ⟨σ, j⟩ • v ⟨σ, j⟩).hom :=
    (Serre.Lie.isLieComb_iff _ (fun j => v ⟨σ, j⟩) _).2 (by rw [h2]; simp)
  have := huniq σ _ (Serre.Lie.isTangent _) (fun z => congrArg Serre.Lie.hom (EigenSplit.mem_eigenSub.1 hw z))
    _ _ c1 c0
  exact congrFun this i

end GlobalTheory.LieBasisRing

namespace GlobalTheory.LieBasisRing

open GlobalTheory.KSExist.FrameLift

theorem lifts_basis_mod_fil : GlobalTheory.Published.AbelianDeRham → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S]
    [Algebra c.F S] (y : FrPt Xo c S) {A : Over (Sp S)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left},
    IsGrpPullback A Xo.univ.t.G y.x π →
    ∀ (ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR S ⟶ A)), (∀ σ k, (ub σ k).left ≫ π = y.u σ k) →
    ∀ (hb : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) → HdR A), (∀ k, IsLieImage (hb k) (ub k.1 k.2)) →
    Submodule.span S (Set.range hb) ⊔ Fil A = ⊤ ∧
      LinearIndependent S (fun k => (Submodule.Quotient.mk (hb k) : HdR A ⧸ Fil A)) := by
  intro P E _ _ _ H Dw l Xo c S _ _ y A _ π hπ ub hub hb hhb
  classical
  have hA := PolPull.isAbelianScheme_of_isGrpPullback (ObjDim.isAbelianScheme Xo.univ) hπ
  have gA := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ.1
    (ObjDim.smoothOfRelativeDimension Xo.univ)
  have : IsCommMonObj A := hA.comm
  obtain ⟨a, ha⟩ := GlobalTheory.OActPull.exists_oAct_of_isGrpPullback Xo.univ.t.act hπ
  have htan : ∀ σ k, IsTangent (ub σ k) := fun σ k => (tan_iff hπ _).1 (by rw [hub]; exact y.tan σ k)
  have heig : ∀ σ k z, ub σ k ≫ a.act z =
      GlobalTheory.GrpTangent.epsScale (((algebraMap c.F S).comp (embK c σ)) z) ≫ ub σ k := fun σ k z =>
    (eig_iff hπ (ha z) _ _).1 (by rw [hub]; exact y.eig σ k z)
  have eu : ∀ σ, y.u σ = fun i => (ub σ i).left ≫ π := fun σ => funext fun i => (hub σ i).symm
  have hbasis : ∀ σ (w : epsR S ⟶ A), IsTangent w →
      (∀ z, w ≫ a.act z = GlobalTheory.GrpTangent.epsScale (((algebraMap c.F S).comp (embK c σ)) z) ≫ w) →
      ∃ cf, IsLieComb cf (ub σ) w := by
    intro σ w ht he
    obtain ⟨cf, hcf, -⟩ := y.basis σ (w.left ≫ π) ((tan_iff hπ w).2 ht)
      (fun z => (eig_iff hπ (ha z) w _).2 (he z))
    rw [eu σ] at hcf
    exact ⟨cf, isLieComb_of_isCombAt hπ _ cf w hcf⟩
  have huniq : ∀ σ (w : epsR S ⟶ A), IsTangent w →
      (∀ z, w ≫ a.act z = GlobalTheory.GrpTangent.epsScale (((algebraMap c.F S).comp (embK c σ)) z) ≫ w) →
      ∀ cf cf', IsLieComb cf (ub σ) w → IsLieComb cf' (ub σ) w → cf = cf' := by
    intro σ w ht he cf cf' h h'
    obtain ⟨cf₀, -, hu⟩ := y.basis σ (w.left ≫ π) ((tan_iff hπ w).2 ht)
      (fun z => (eig_iff hπ (ha z) w _).2 (he z))
    have k := isCombAt_of_isLieComb hπ _ cf w h
    have k' := isCombAt_of_isLieComb hπ _ cf' w h'
    rw [← eu σ] at k k'
    exact (hu cf k).trans (hu cf' k').symm
  have L := (P.2.1 S A _ hA gA).1
  let v : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) → Serre.Lie a := fun k => Serre.Lie.mk a (ub k.1 k.2) (htan _ _)
  have hχ := isSplitting_embS (E := E) c S
  have hspan : Submodule.span S (Set.range v) = ⊤ := span_eq_top a hχ ub htan hbasis
  have hind : LinearIndependent S v := linearIndependent a hχ ub htan heig huniq
  have hv : (fun k => (Submodule.Quotient.mk (hb k) : HdR A ⧸ Fil A)) = (L.quotEquiv a).symm ∘ v := by
    funext k
    rw [Function.comp_apply, LinearEquiv.eq_symm_apply, LieExact.quotEquiv_mk, L.toLie_eq_iff]
    exact hhb k
  refine ⟨?_, hv ▸ hind.map' _ (L.quotEquiv a).symm.ker⟩
  have h1 : Submodule.map (Fil A).mkQ (Submodule.span S (Set.range hb)) = ⊤ := by
    rw [Submodule.map_span, ← Set.range_comp]
    change Submodule.span S (Set.range fun k => (Submodule.Quotient.mk (hb k) : HdR A ⧸ Fil A)) = ⊤
    rw [hv, Set.range_comp, eq_top_iff]
    intro q _
    have hq : (L.quotEquiv a) q ∈ Submodule.span S (Set.range v) := hspan ▸ Submodule.mem_top
    simpa using hq
  have h2 := congrArg (Submodule.comap (Fil A).mkQ) h1
  rwa [Submodule.comap_map_mkQ, Submodule.comap_top, sup_comm] at h2

end GlobalTheory.LieBasisRing
