import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CombinatorialCechAcyclic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinsetSystemInjectiveExtensionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinsetSystemScalarTowerExtStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PmExactnessOfExPStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExPOfCompatibleEquivStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MonomialFormsBasisStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeFormsMapInjectiveStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelativeFormsMapMemSpanStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MonomialFormInRelativeImageStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartEmptyBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartSingletonBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartExtendBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartBaseChangeMapUniqueStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartFormsBaseChangeStatement

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4
open CrystallineSemistableComparison.Onto

variable {K : Type} [Field K] {n d : ℕ}

theorem exists_theta {A : Type} [CommRing A] [Algebra K A] (C : ChartRings K A n d) :
    ∃ (θ : ∀ S, R0 K n d S →ₐ[K] C.R S) (hθ : ∀ S b, θ S (poly n K S b) = toR C S (phi C b)),
      (∀ {S T : Finset (Fin d)} (h : S ⊆ T) y, C.res h (θ S y) = θ T (incl (cone_mono h) y)) ∧
      ∀ S, IsBaseChange (Aa C) (thetaLin C (θ S) (hθ S)) := by
  have key : ∀ S, ∃ (θ : R0 K n d S →ₐ[K] C.R S) (hθ : ∀ b, θ (poly n K S b) = toR C S (phi C b)),
      IsBaseChange (Aa C) (thetaLin C θ hθ) := by
    intro S
    rcases S.eq_empty_or_nonempty with rfl | ⟨k, hk⟩
    · exact GlobalTheory.T.chart_empty_base_change C
    · obtain ⟨θ₁, h₁, hu, hb⟩ := GlobalTheory.T.chart_singleton_base_change C k
      exact GlobalTheory.T.chart_extend_base_change C S k hk θ₁ h₁ hu hb
  choose θ hθ bc using key
  refine ⟨θ, hθ, ?_, bc⟩
  intro S T h y
  have := GlobalTheory.T.chart_base_change_map_unique C ((C.res h).comp (θ S)) ((θ T).comp (incl (cone_mono h)))
    (fun b => by rw [AlgHom.comp_apply, hθ, res_toR]) (fun b => by rw [AlgHom.comp_apply, incl_poly h, hθ]) (θ T) (hθ T) (bc T)
  exact DFunLike.congr_fun this y

theorem Tset_ne_univ (g : Gam n d) (D : Finset (E n d)) (h : good g D) : Tset g D ≠ Finset.univ := by
  intro hu
  have hneg : ∀ j, g (Sum.inr j) ≤ 0 := fun j => by
    have : j ∈ Tset g D := hu ▸ Finset.mem_univ j
    rcases (Finset.mem_filter.1 this).2 with h | h
    · exact h.le
    · exact h.1.le
  have : tdeg g ≤ 0 := Finset.sum_nonpos fun j _ => hneg j
  have := h.2
  omega

theorem model_ex (a : ℕ) : ExP (fun S : Finset (Fin d) => relOm K (I0 n K S) a)
    (fun {S T} h => relMap (incl (cone_mono h)) (cone_ideal_map_mono (S := S) (T := T) h) a) := by
  obtain ⟨b, hb⟩ := GlobalTheory.T.monomial_forms_basis (K := K) (n := n) (d := d) a
  refine GlobalTheory.T.finset_system_injective_extension (K := K) b (fun p => good p.1 p.2.1) (fun p => Tset p.1 p.2.1) (fun p h => Tset_ne_univ _ _ h) _ _
    (fun S => ((omMap (K := K) (incl (le_top : (cone S : AddSubmonoid (Gam n d)) ≤ ⊤)) a).toAddMonoidHom).comp
      (relOm K (I0 n K S) a).subtype.toAddMonoidHom) ?_ ?_ ?_
  · intro S x y hxy
    exact Subtype.ext (GlobalTheory.T.cone_forms_map_injective S a hxy)
  · intro S S' h x
    change omMap _ a (omMap _ a (x : Om K (R0 K n d S) a)) = omMap _ a (x : Om K (R0 K n d S) a)
    rw [omMap_comp, incl_comp]
  · intro S w
    have hset : (b '' {l | good l.1 l.2.1 ∧ Tset l.1 l.2.1 ⊆ S}) =
        {w | ∃ (g : Gam n d) (D : {D : Finset (E n d) // D.card = a}), good g D.1 ∧ Tset g D.1 ⊆ S ∧ w = monW K g D} := by
      ext w
      constructor
      · rintro ⟨p, hp, rfl⟩
        exact ⟨p.1, p.2, hp.1, hp.2, hb p⟩
      · rintro ⟨g, D, h1, h2, rfl⟩
        exact ⟨(g, D), ⟨h1, h2⟩, hb _⟩
    rw [hset]
    constructor
    · rintro ⟨x, rfl⟩
      exact GlobalTheory.T.relative_forms_map_mem_span S a _ x.2
    · intro hw
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨g, D, h1, h2, rfl⟩ := hw
        obtain ⟨ω, hω, e⟩ := GlobalTheory.T.monomial_form_in_relative_image (K := K) S a g D h1 h2
        exact ⟨⟨ω, hω⟩, e⟩
      | zero => exact ⟨0, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨x', rfl⟩ := hx
        obtain ⟨y', rfl⟩ := hy
        exact ⟨x' + y', map_add _ _ _⟩
      | smul c x _ hx =>
        obtain ⟨x', rfl⟩ := hx
        exact ⟨c • x', map_smul (omMap (K := K) (incl (le_top : (cone S : AddSubmonoid (Gam n d)) ≤ ⊤)) a) c _⟩

theorem h4a : ChartFormsCechExact := by
  intro K _ _ A _ _ n d hd C a P e he
  obtain ⟨θ, hθ, nat, bc⟩ := exists_theta C
  haveI := etale_Aa C
  have h1 := model_ex (K := K) (n := n) (d := d) a
  have h2 : ExP (fun S => relA C S a) (fun {S T} h => relMap (C.res h) (res_mem_I C (S := S) (T := T) h) a) := by
    refine GlobalTheory.T.finset_system_scalar_tower_ext (B := Bp K n d) (A := Aa C) (fun S => relOm K (I0 n K S) a) (fun S => relA C S a) _ ?_ _ ?_
      (fun S => psi C (θ S) (hθ S) a) (fun S => GlobalTheory.T.chart_forms_base_change C (θ S) (hθ S) (bc S) a) ?_ h1
    · intro S T h
      refine ⟨map_add _, fun b ω => Subtype.ext ?_⟩
      change omMap (incl (cone_mono h)) a ((b • ω : relOm K (I0 n K S) a) : Om K (R0 K n d S) a) =
        ((b • relMap (incl (cone_mono h)) (cone_ideal_map_mono h) a ω : relOm K (I0 n K T) a) : Om K (R0 K n d T) a)
      have e1 : ∀ (U : Finset (Fin d)) (ω' : relOm K (I0 n K U) a), ((b • ω' : relOm K (I0 n K U) a) : Om K (R0 K n d U) a) =
          poly n K U b • (ω' : Om K (R0 K n d U) a) := fun U ω' =>
        (algebraMap_smul (R0 K n d U) b (ω' : Om K (R0 K n d U) a)).symm
      rw [e1, e1, omMap_smul, incl_poly h]
      rfl
    · intro S T h
      refine ⟨map_add _, fun c y => Subtype.ext ?_⟩
      change omMap (C.res h) a (toR C S c • (y : relOm K (C.I S) a).1) = toR C T c • omMap (C.res h) a (y : relOm K (C.I S) a).1
      rw [omMap_smul]
      exact congrArg (· • omMap (C.res h) a (y : relOm K (C.I S) a).1) (res_toR C h c)
    · intro S T h ω
      refine Subtype.ext ?_
      change omMap (C.res h) a (omMap (θ S) a (ω : Om K (R0 K n d S) a)) =
        omMap (θ T) a (omMap (incl (cone_mono h)) a (ω : Om K (R0 K n d S) a))
      have e2 : (C.res h).comp (θ S) = (θ T).comp (incl (cone_mono h)) := AlgHom.ext fun y => nat h y
      rw [omMap_comp, omMap_comp, e2]
  refine GlobalTheory.T.pm_exactness_of_exP P (GlobalTheory.T.exP_of_compatible_equiv _ _ (fun {S T} h => relMap (C.res h) (res_mem_I C (S := S) (T := T) h) a) _
    (fun S => ((e S).symm.toAddEquiv : relA C S a ≃+ P.M S)) ?_ h2)
  intro S T h x
  apply (e T).injective
  refine Subtype.ext ?_
  have := he h ((e S).symm x)
  simp only [LinearEquiv.apply_symm_apply] at this
  have h3 := LinearEquiv.apply_symm_apply (e T) (relMap (C.res h) (res_mem_I C h) a x)
  exact (congrArg Subtype.val h3).trans this.symm

end GlobalTheory.CompanionTheory.SurjectionOntoH4
