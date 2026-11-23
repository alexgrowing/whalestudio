import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CentralEig2
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.EigAll

open NumberField IsDedekindDomain Matrix Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.GalOfCusp UpperTheory.V.Af
open GlobalTheory.DefU GlobalTheory.PRep GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

section SlopeTestRemainingChoices

open GlobalTheory.LFun
open Formalism.UG (IsUnifV Tj Ov diagJ GLint qV)

private theorem hecke_eq_sum {G : Type} [Group G] (K : Subgroup G) (h : G → ℂ) (h01 : ∀ g, h g ≠ 0 → h g = 1)
    (hfin : {q : G ⧸ K | h q.out ≠ 0}.Finite) : ∃ R : Finset G, (∀ g ∈ R, h g ≠ 0) ∧
      ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (x : V),
        heckeVec ρ K h x = ∑ g ∈ R, ρ g x := by
  refine ⟨hfin.toFinset.image Quotient.out, ?_, ?_⟩
  · intro g hg
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hg
    exact (Set.Finite.mem_toFinset hfin).1 hq
  · intro V _ _ ρ x
    rw [Finset.sum_image (fun a _ b _ e => Quotient.out_injective e)]
    have hsupp : (Function.support fun q : G ⧸ K => h q.out • ρ q.out x) ⊆ hfin.toFinset := by
      intro q hq
      simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
      intro h0
      exact hq (by simp [h0])
    have hsum : heckeVec ρ K h x = ∑ q ∈ hfin.toFinset, h q.out • ρ q.out x :=
      finsum_eq_sum_of_support_subset _ hsupp
    rw [hsum]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [h01 _ ((Set.Finite.mem_toFinset hfin).1 hq), one_smul]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem tj_one {L : Type} [Field L] {n : ℕ} {O : Subring L} {ϖ : L} {j : ℕ} (g : GL (Fin n) L)
    (hg : Tj ℂ n O ϖ j g ≠ 0) : Tj ℂ n O ϖ j g = 1 := by
  unfold Tj at hg ⊢
  exact Set.indicator_of_mem (Set.mem_of_indicator_ne_zero hg) _

private theorem comm_of_cLoc {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w) (z : UA E n) (hz : cLoc w z = 1)
    (y : UA E n) (hy : y ∈ locU n w) : y * z = z * y := by
  have hyf := (Subgroup.mem_inf.1 hy).1
  have hyo := (Subgroup.mem_inf.1 hy).2
  have hc : z * y * z⁻¹ * y⁻¹ ∈ locU n w := by
    refine Subgroup.mem_inf.2 ⟨?_, Subgroup.mem_iInf.2 fun u => Subgroup.mem_iInf.2 fun hu => ?_⟩
    · have h1 : cInf y = 1 := MonoidHom.mem_ker.1 hyf
      exact MonoidHom.mem_ker.2 (by simp [h1])
    · have h1 : cLoc u y = 1 := MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hyo u) hu)
      exact MonoidHom.mem_ker.2 (by simp [h1])
  have h1 := GlobalTheory.SplitPts.eq_one_of_cLoc hw ⟨_, hc⟩ (by simp [hz])
  have h2 : z * y * z⁻¹ * y⁻¹ = 1 := congrArg Subtype.val h1
  exact (mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h2)).symm

private noncomputable def repG {w : HeightOneSpectrum (𝓞 E)} (e : locU n w ≃ₜ* GL (Fin n) (w.adicCompletion E)) :
    Representation ℂ (GL (Fin n) (w.adicCompletion E)) (UA E n → ℂ) :=
  (RU E n).comp ((locU n w).subtype.comp e.symm.toMulEquiv.toMonoidHom)

private theorem satVec_of_mem {σ : Submodule ℂ (UA E n → ℂ)} (hσ : IsAutRepU σ) {w : HeightOneSpectrum (𝓞 E)}
    (hw : IsSplitAt w) (e : locU n w ≃ₜ* GL (Fin n) (w.adicCompletion E))
    (he : ∀ x : locU n w, e x = cLoc w (x : UA E n))
    (τ : SmIrr (GL (Fin n) (w.adicCompletion E))) {B : Multiset ℂˣ}
    (hc : IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ) (hB : HasSatGL w τ.ρ B)
    {φ : UA E n → ℂ} (hφ : φ ∈ σ) (hK : ∀ y ∈ locU n w, cLoc w y ∈ KGL w n → RU E n y φ = φ) (h0 : φ ≠ 0) :
    IsSatVecGL w (repG e) φ B := by
  obtain ⟨hirr, f, hf0, hfσ, hfe⟩ := hc
  have hpe : ∀ g, cLoc w ((e.symm g : locU n w) : UA E n) = g := fun g => by
    rw [← he, e.apply_symm_apply]
  have hrep : ∀ g, repG e g = RU E n ((e.symm g : locU n w) : UA E n) := fun g => rfl
  let C : Subgroup (UA E n) := Subgroup.centralizer (locU n w : Set (UA E n))
  let F : C → τ.V →ₗ[ℂ] (UA E n → ℂ) := fun c => (RU E n c.1) ∘ₗ f
  have hF : ∀ c v, F c v = RU E n c.1 (f v) := fun c v => rfl
  have hRm : ∀ (a b : UA E n) ψ, RU E n a (RU E n b ψ) = RU E n (a * b) ψ := fun a b ψ => by
    rw [map_mul]; rfl
  have hfg : ∀ g v, f (τ.ρ g v) = repG e g (f v) := fun g v => by
    have h1 := hfe (e.symm g) v
    rw [MonoidHom.comp_apply, Subgroup.subtype_apply, hpe] at h1
    exact h1
  have hFe : ∀ c g v, F c (τ.ρ g v) = repG e g (F c v) := by
    intro c g v
    rw [hF, hF, hfg, hrep, hRm, hRm]
    have hcomm := Subgroup.mem_centralizer_iff.1 c.2 _ (e.symm g).2
    rw [hcomm]
  let S : Submodule ℂ (UA E n → ℂ) := ⨆ c, LinearMap.range (F c)
  have hSσ : S ≤ σ := iSup_le fun c => by
    rintro _ ⟨v, rfl⟩
    exact hσ.stable _ _ (hfσ v)
  have hSst : ∀ x, ∀ ψ ∈ S, RU E n x ψ ∈ S := by
    intro x ψ hψ
    have hle : S ≤ S.comap (RU E n x) := iSup_le fun c => by
      rintro _ ⟨v, rfl⟩
      set g := cLoc w x with hg
      set x1 : UA E n := ((e.symm g : locU n w) : UA E n) with hx1
      have h2 : cLoc w (x1⁻¹ * x) = 1 := by
        rw [map_mul, map_inv, hx1, hpe, inv_mul_cancel]
      have hx2 : x1⁻¹ * x ∈ C := Subgroup.mem_centralizer_iff.2 fun y hy => comm_of_cLoc hw _ h2 y hy
      let c' : C := ⟨x1⁻¹ * x, hx2⟩ * c
      have e1 : F c' (τ.ρ g v) = RU E n x (F c v) := by
        have e2 : ((e.symm g : locU n w) : UA E n) * c'.1 = x * c.1 := by
          show x1 * (x1⁻¹ * x * c.1) = x * c.1
          group
        rw [hFe, hrep, hF, hF, hRm, hRm, e2]
      exact Submodule.mem_comap.2 (e1 ▸ Submodule.mem_iSup_of_mem c' ⟨_, rfl⟩)
    exact hle hψ
  have hS : S = σ := by
    refine (hσ.irred S hSσ hSst).resolve_left fun hb => hf0 ?_
    ext v : 1
    have h1 : F 1 v ∈ S := Submodule.mem_iSup_of_mem 1 ⟨v, rfl⟩
    rw [hb] at h1
    have h2 : F 1 v = f v := by
      rw [hF]; simp
    rw [← h2]
    simpa using h1
  have hφS : φ ∈ S := hS.symm ▸ hφ
  refine GlobalTheory.HeightCounting.Blocks.isSatVecGL_of_mem_iSup hirr hB F hFe hφS
    (GlobalTheory.LGrp.mem_fixed.2 fun k hk => hK _ (e.symm k).2 ?_) h0
  show cLoc w ((e.symm k : locU n w) : UA E n) ∈ KGL w n
  rw [hpe]
  exact hk

end SlopeTestRemainingChoices

theorem UpperTheory.Gal.CertificateRingHomMap.pSatVal_of :
    UpperTheory.Gal.CertificateRingHomMap.SatVal := by
  intro E _ _ _ n π W f hf hf0 w hw hK B hB
  obtain ⟨τ, hc, hS⟩ := hB
  have hmem := AutSub.mem_finPart.1 hf
  have hval : ∀ (k : finU E n) v, (algRep W k f).1 v = RU E n k.1 (f.1 v) := fun _ _ => rfl
  have hfix : ∀ v, ∀ y ∈ locU n w, cLoc w y ∈ GlobalTheory.LFun.KGL w n → RU E n y (f.1 v) = f.1 v := by
    intro v y hy hk
    have h1 : ((locF hw (cLoc w y)).1 : UA E n) = y := by
      have h2 : locE hw ⟨y, hy⟩ = cLoc w y := locE_apply hw ⟨y, hy⟩
      show (((locE hw).symm (cLoc w y) : locU n w) : UA E n) = y
      rw [← h2, (locE hw).symm_apply_apply]
    have h3 := hval (locF hw (cLoc w y)) v
    rw [hK _ hk, h1] at h3
    exact h3.symm
  have hsat : ∀ v, f.1 v ≠ 0 → GlobalTheory.LFun.IsSatVecGL w (repG (locE hw)) (f.1 v) B := fun v h0 =>
    satVec_of_mem π.isAut hw (locE hw) (locE_apply hw) τ hc hS (hmem v) (hfix v) h0
  have hrep : ∀ g v, repG (locE hw) g (f.1 v) = (((algRep W).comp (locF hw)) g f).1 v := fun _ _ => rfl
  obtain ⟨v₀, hv₀⟩ : ∃ v, f.1 v ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf0 (Subtype.ext (LinearMap.ext h))
  refine ⟨hf0, GlobalTheory.LGrp.mem_fixed.2 fun k hk => hK k hk, (hsat v₀ hv₀).2.2.1, fun ϖ hϖ j hj => ?_⟩
  have hcm := Formalism.UG.Final.GLintComm E w n
  have hT := GlobalTheory.LFun.Tj_mem_hecke (n := n) hϖ j
  obtain ⟨R, -, hRe⟩ := hecke_eq_sum (GlobalTheory.LFun.KGL w n) (Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j) tj_one
    (Formalism.UG.P.finite_support_cosets hcm hT.2)
  rw [hRe]
  refine Subtype.ext (LinearMap.ext fun v => ?_)
  by_cases h0 : f.1 v = 0
  · have hz : ∀ g, (((algRep W).comp (locF hw)) g f).1 v = 0 := fun g => by
      rw [← hrep, h0, map_zero]
    have e1 : (∑ g ∈ R, ((algRep W).comp (locF hw)) g f).1 v = ∑ g ∈ R, (((algRep W).comp (locF hw)) g f).1 v := by
      simp [AddSubmonoidClass.coe_finset_sum, LinearMap.sum_apply]
    rw [e1, Finset.sum_eq_zero fun g _ => hz g]
    simp [h0]
  · have h1 := (hsat v h0).2.2.2 ϖ hϖ j hj
    rw [hRe] at h1
    have e1 : (∑ g ∈ R, ((algRep W).comp (locF hw)) g f).1 v = ∑ g ∈ R, (((algRep W).comp (locF hw)) g f).1 v := by
      simp [AddSubmonoidClass.coe_finset_sum, LinearMap.sum_apply]
    rw [e1, Finset.sum_congr rfl fun g _ => (hrep g v).symm, h1]
    rfl
