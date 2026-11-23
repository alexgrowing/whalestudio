import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkOfInjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FibreLawOfTestCartesian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorFieldPointThroughGenericPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.UnitGen

def gv {A : Type} [CommRing A] {X : Scheme.{0}} (f : Sp A ⟶ X) (V : X.Opens) (h : ⊤ ≤ f ⁻¹ᵁ V) (c : Γ(X, V)) : A :=
  (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom (((Sp A).presheaf.map (homOfLE h).op).hom ((f.app V).hom c))

theorem gs_gv {A : Type} [CommRing A] {X : Scheme.{0}} (f : Sp A ⟶ X) (V : X.Opens) (h : ⊤ ≤ f ⁻¹ᵁ V) (c : Γ(X, V))
    (z : Sp A) : gs f z V c = stalkOf z (gv f V h c) := by
  rw [gs_eq f z V (h trivial)]
  simp only [stalkOf, gv, RingHom.comp_apply]
  rw [Iso.hom_inv_id_apply]
  exact (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm

theorem gs_spMap_top {A B : Type} [CommRing A] [CommRing B] (ψ : A →+* B) (e : Γ(Sp A, ⊤)) (z : Sp B) :
    gs (spMap ψ) z ⊤ e = stalkOf z (ψ ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom e)) := by
  rw [gs_eq _ z ⊤ trivial]
  simp only [stalkOf, RingHom.comp_apply]
  have := congrArg (fun q => q.hom e) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
  rw [← this, Iso.hom_inv_id_apply]
  rfl

theorem gs_comp_gv {A B : Type} [CommRing A] [CommRing B] (ψ : A →+* B) {X : Scheme.{0}} (f : Sp A ⟶ X) (V : X.Opens)
    (h : ⊤ ≤ f ⁻¹ᵁ V) (c : Γ(X, V)) (z : Sp B) : gs (spMap ψ ≫ f) z V c = stalkOf z (ψ (gv f V h c)) := by
  rw [← gs_pull (spMap ψ) f z V (h trivial) c, ← gs_res (spMap ψ) z h trivial, gs_spMap_top]
  rfl

theorem sp_field_eq {F : Type} [Field F] (a b : Sp F) : a = b :=
  PrimeSpectrum.ext (by haveI := a.isPrime; haveI := b.isPrime; rw [Ideal.eq_bot_of_prime a.asIdeal, Ideal.eq_bot_of_prime b.asIdeal])

end GlobalTheory.Mum.UnitGen

open GlobalTheory.Mum.UnitGen in

theorem GlobalTheory.Mum.UnitGen.value_unit_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ) (s : SecK C.P.L.L C.α k), ∃ x y : R, y ≠ 0 ∧ ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (a : W) (σ : SecK C.P.L.L T.β k), (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs p z ⊤ (scal T.G.hom a) * sval s p' z J) → ∀ J, Good C.P.L.L (cpt W) J → stalkOf (cpt W) (T.φ y) * sval σ (unitW T.G) (cpt W) J = stalkOf (cpt W) (a * T.φ x) * (val C.P.L.rig T.ξ (cpt W) J).val ^ k := by
  intro R _ _ _ hB D C k s
  have hL : C.P.L.L.IsLB := C.P.L.isLB
  have hrg : C.P.L.rig.IsGen := C.P.L.rigGen
  have hE : eSec C.A.A ≫ C.α = C.gp ≫ eSec C.G := GlobalTheory.ZJ.eSec_comp_of_isGrpPullback C.α_cart
  obtain ⟨i₀, hi₀⟩ := exists_chart hL ((C.gp ≫ eSec C.G) (cpt (FractionRing R)))
  have hs₀ : ⊤ ≤ (eSec C.A.A) ⁻¹ᵁ LB.wchart C.P.L.L (fun _ : Fin 1 => C.α) (fun _ => i₀) :=
    (top_le_iff_cpt _ _).2 (Set.mem_iInter.2 fun _ => by
      rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, hE]; exact hi₀)
  have hr₀ : ⊤ ≤ C.gp ⁻¹ᵁ LB.wchart C.P.L.L (fun _ : PUnit => eSec C.G) (fun _ => i₀) :=
    (top_le_iff_cpt _ _).2 (Set.mem_iInter.2 fun _ => by
      rw [Set.mem_preimage, ← Scheme.Hom.comp_apply]; exact hi₀)
  set cs : FractionRing R := gv (eSec C.A.A) _ hs₀ (s.f (fun _ => i₀)) with hcs
  set cr : FractionRing R := gv C.gp _ hr₀ (C.P.L.rig.s (fun _ => i₀)).val with hcr
  have hcr0 : IsUnit cr := ((((C.P.L.rig.s (fun _ => i₀)).isUnit.map (C.gp.app _).hom).map _).map _)
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := R) (cs / cr ^ k)
  refine ⟨x, y, nonZeroDivisors.ne_zero hy, ?_⟩
  intro W _ _ _ T a σ hσ J hJ

  have hinj : Function.Injective ((algebraMap W (FractionRing W)).comp T.φ) :=
    (IsFractionRing.injective W (FractionRing W)).comp T.inj
  obtain ⟨ga, hga, hgp⟩ := Modif.factor_gp R C.toModif (FractionRing W) ((algebraMap W _).comp T.φ) (jK W ≫ T.ξ) hinj (by
    rw [Category.assoc, T.ξ_π]
    exact (Spec.map_comp _ _).symm)
  have hjK : jK W = spMap (algebraMap W (FractionRing W)) := rfl
  have hU : unitW T.G ≫ T.β = T.ξ ≫ eSec C.G := GlobalTheory.ZJ.eSec_comp_of_isGrpPullback T.cart
  set g : Sp (FractionRing W) := cpt (FractionRing W)
  set p : Sp (FractionRing W) ⟶ T.G.left := jK W ≫ unitW T.G with hp
  set p' : Sp (FractionRing W) ⟶ C.A.A.left := spMap ga ≫ eSec C.A.A with hp'
  have hr : jK W ≫ T.ξ ≫ eSec C.G = spMap ga ≫ C.gp ≫ eSec C.G := by rw [← Category.assoc, hgp, Category.assoc]
  have hpp : p ≫ T.β = p' ≫ C.α := by
    rw [hp, hp', Category.assoc, Category.assoc, hU, hE, hr]
  set I := J (T.ξ ≫ eSec C.G) with hIdef
  have hI : (T.ξ ≫ eSec C.G) (cpt W) ∈ C.P.L.L.U I := hJ _
  have hItop : ⊤ ≤ (T.ξ ≫ eSec C.G) ⁻¹ᵁ C.P.L.L.U I := (top_le_iff_cpt _ _).2 hI
  have hpI : (p ≫ T.β) g ∈ C.P.L.L.U I := by
    rw [hp, Category.assoc, hU, Scheme.Hom.comp_apply]; exact hItop trivial
  have hpi₀ : (p ≫ T.β) g ∈ C.P.L.L.U i₀ := by
    rw [hp, Category.assoc, hU, ← Category.assoc, hgp, Category.assoc, Scheme.Hom.comp_apply,
      sp_field_eq ((spMap ga) g) (cpt (FractionRing R))]
    exact hi₀
  obtain ⟨J', hJ', hJ'e⟩ := exists_good C.P.L.L hL g (K := PUnit) (fun _ => p ≫ T.β) (fun _ => I) (fun _ _ _ => rfl)
    (fun _ => hpI)
  have e1 := hσ _ p p' hpp g J' hJ'
  rw [sval_of σ p g J' (fun _ => I) (fun _ => hJ'e ⟨⟩),
    sval_of s p' g J' (fun _ => I) (fun _ => by rw [← hpp]; exact hJ'e ⟨⟩)] at e1

  have hσtop : ⊤ ≤ unitW T.G ⁻¹ᵁ LB.wchart C.P.L.L (fun _ : Fin 1 => T.β) (fun _ => I) :=
    (top_le_iff_cpt _ _).2 (Set.mem_iInter.2 fun _ => by
      rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, hU]; exact hI)
  have hρtop : ⊤ ≤ T.ξ ⁻¹ᵁ LB.wchart C.P.L.L (fun _ : PUnit => eSec C.G) (fun _ => I) :=
    (top_le_iff_cpt _ _).2 (Set.mem_iInter.2 fun _ => by
      rw [Set.mem_preimage, ← Scheme.Hom.comp_apply]; exact hI)
  set σv : W := gv (unitW T.G) _ hσtop (σ.f (fun _ => I)) with hσv
  set ρv : W := gv T.ξ _ hρtop (C.P.L.rig.s (fun _ => I)).val with hρv
  have eσ : gs p g (LB.wchart C.P.L.L (fun _ : Fin 1 => T.β) (fun _ => I)) (σ.f (fun _ => I)) =
      stalkOf g (algebraMap W _ σv) := by
    rw [hp, hjK]; exact gs_comp_gv _ _ _ hσtop _ g
  have hu : unitW T.G ≫ T.G.hom = 𝟙 _ := by simpa [unitW, eSec] using Over.w (η[T.G])
  have ea : gs p g ⊤ (scal T.G.hom a) = stalkOf g (algebraMap W _ a) := by
    have h1 : p ≫ T.G.hom = spMap (algebraMap W (FractionRing W)) := by
      rw [hp, Category.assoc, hu, Category.comp_id]
    have h2 := gs_pull p T.G.hom g ⊤ trivial ((Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom a)
    rw [h1, gs_spMap_top, Iso.inv_hom_id_apply] at h2
    exact h2

  have hrp : (jK W ≫ T.ξ) ≫ eSec C.G = p ≫ T.β := by rw [hp, Category.assoc, Category.assoc, hU]
  have hp'i₀ : p' g ∈ LB.wchart C.P.L.L (fun _ : Fin 1 => C.α) (fun _ => i₀) := Set.mem_iInter.2 fun _ => by
    rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, ← hpp]; exact hpi₀
  have hp'I : p' g ∈ LB.wchart C.P.L.L (fun _ : Fin 1 => C.α) (fun _ => I) := Set.mem_iInter.2 fun _ => by
    rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, ← hpp]; exact hpI
  have hri₀ : (jK W ≫ T.ξ) g ∈ LB.wchart C.P.L.L (fun _ : PUnit => eSec C.G) (fun _ => i₀) := Set.mem_iInter.2 fun _ => by
    rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, hrp]; exact hpi₀
  have hrI : (jK W ≫ T.ξ) g ∈ LB.wchart C.P.L.L (fun _ : PUnit => eSec C.G) (fun _ => I) := Set.mem_iInter.2 fun _ => by
    rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, hrp]; exact hpI
  have e2 := sec_trans s p' g hp'i₀ hp'I
  have orbitMap_conj_smul_zero : gs p' g (LB.wchart C.P.L.L (fun _ : Fin 1 => C.α) (fun _ => i₀)) (s.f (fun _ => i₀)) = stalkOf g (ga cs) := by
    rw [hp']; exact gs_comp_gv ga _ _ hs₀ _ g
  have e3 := gen_trans hrg (jK W ≫ T.ξ) g hri₀ hrI
  have eB0 : (gm (jK W ≫ T.ξ) g (LB.wchart C.P.L.L (fun _ : PUnit => eSec C.G) (fun _ => i₀)) (C.P.L.rig.s (fun _ => i₀))).val = stalkOf g (ga cr) := by
    refine (gs_unit (jK W ≫ T.ξ) g _ hri₀ _).symm.trans ?_
    rw [hgp]; exact gs_comp_gv ga _ _ hr₀ _ g
  have eB : (gm (jK W ≫ T.ξ) g (LB.wchart C.P.L.L (fun _ : PUnit => eSec C.G) (fun _ => I)) (C.P.L.rig.s (fun _ => I))).val = stalkOf g (algebraMap W _ ρv) := by
    refine (gs_unit (jK W ≫ T.ξ) g _ hrI _).symm.trans ?_
    rw [hjK]; exact gs_comp_gv _ _ _ hρtop _ g
  have et : trF (L := C.P.L.L) (fun _ : Fin 1 => C.α) (fun _ => ((k : ℕ) : ℤ)) p' g (fun _ => i₀) (fun _ => I) =
      (trF (L := C.P.L.L) (fun _ : PUnit => eSec C.G) (fun _ => 1) (jK W ≫ T.ξ) g (fun _ => i₀) (fun _ => I)) ^ k := by
    simp only [trF]
    rw [show p' ≫ C.α = (jK W ≫ T.ξ) ≫ eSec C.G from hpp.symm.trans hrp.symm]
    simp

  rw [eσ, ea] at e1
  rw [orbitMap_conj_smul_zero, et] at e2
  have e3v := congrArg Units.val e3
  rw [Units.val_mul, eB0, eB] at e3v
  have hy0 : algebraMap R (FractionRing R) y ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
  have hxy' : algebraMap R _ x * cr ^ k = cs * algebraMap R _ y := by
    rw [div_eq_div_iff hy0 (pow_ne_zero _ hcr0.ne_zero)] at hxy; exact hxy
  have hXY := congrArg (fun q => stalkOf g (ga q)) hxy'
  simp only [map_mul, map_pow, hga, RingHom.comp_apply] at hXY
  rw [e3v, e2, Units.val_pow_eq_pow_val] at hXY
  have hW : T.φ y * σv = a * T.φ x * ρv ^ k := by
    apply ((stalkOf_injective g).comp (IsFractionRing.injective W (FractionRing W)))
    simp only [Function.comp_apply, map_mul, map_pow]
    refine ((trF (L := C.P.L.L) (fun _ : PUnit => eSec C.G) (fun _ => 1) (jK W ≫ T.ξ) g (fun _ => i₀)
      (fun _ => I)).isUnit.pow k).mul_left_inj.1 ?_
    rw [e1]
    linear_combination (-(stalkOf g (algebraMap W (FractionRing W) a))) * hXY
  have eBc : (gm T.ξ (cpt W) (LB.wchart C.P.L.L (fun _ : PUnit => eSec C.G) (fun _ => I)) (C.P.L.rig.s (fun _ => I))).val = stalkOf (cpt W) ρv :=
    (gs_unit T.ξ (cpt W) _ (hρtop trivial) _).symm.trans (gs_gv _ _ hρtop _ _)
  have eσc : gs (unitW T.G) (cpt W) (LB.wchart C.P.L.L (fun _ : Fin 1 => T.β) (fun _ => I)) (σ.f (fun _ => I)) =
      stalkOf (cpt W) σv := gs_gv _ _ hσtop _ _
  rw [sval_of σ (unitW T.G) (cpt W) J (fun _ => I) (fun _ => by rw [hU])]
  erw [eσc]
  rw [val_of C.P.L.rig T.ξ (cpt W) J (fun _ => I) (fun _ => rfl), eBc, ← map_mul, ← map_pow, ← map_mul, hW]
