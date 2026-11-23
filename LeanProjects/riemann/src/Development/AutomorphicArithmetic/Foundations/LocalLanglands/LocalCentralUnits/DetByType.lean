import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
import Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.ConjTorusSubApply
import Development.DiscreteGroups.GlobalIrreducibility.DzIsoKO
import Development.DiscreteGroups.GlobalIrreducibility.DzIsoRes
import Development.DiscreteGroups.GlobalIrreducibility.DzLCusp
import Development.DiscreteGroups.GlobalIrreducibility.DzKSchur
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdmissibleLabelWeightsOfGreenCuspidalParametrisa
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimpleIffIrreducibleStatement

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.GLq

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Zero.LLC.DetT

open PositivityTheory.Rg.DzCount PositivityTheory.Rg.DzCount.B.TorusConjugationFixed

private theorem top_of_stable {G : Type} [Group G] [TopologicalSpace G] (π : IrrRep G) (U : Submodule ℂ π.V)
    (hU : ∀ g, ∀ v ∈ U, π.ρ g v ∈ U) (h0 : ∃ v ∈ U, v ≠ 0) : U = ⊤ := by
  obtain ⟨v, hv, hne⟩ := h0
  have := π.irr
  rcases this.eq_bot_or_eq_top (⟨U, fun g v hv => hU g v hv⟩ : Subrepresentation π.ρ) with h | h
  · exfalso
    apply hne
    have hv' : v ∈ (⟨U, fun g v hv => hU g v hv⟩ : Subrepresentation π.ρ).toSubmodule := hv
    rw [h] at hv'
    exact (Submodule.mem_bot ℂ).mp hv'
  · exact congrArg Subrepresentation.toSubmodule h

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

private theorem equiv_of_typeMaps [Nontrivial W] {T : Representation ℂ (GL (Fin n) 𝓀[k]) W} (hT : FinCusp T)
    (π π' : IrrRep (GL (Fin n) k)) {ω : kˣ →* ℂˣ} (hω : HasCentralChar π.ρ ω) (hω' : HasCentralChar π'.ρ ω)
    {j : W →ₗ[ℂ] π.V} {j' : W →ₗ[ℂ] π'.V} (hj : IsTypeMap T π.ρ j) (hj' : IsTypeMap T π'.ρ j') :
    Nonempty (π.ρ.Equiv π'.ρ) := by
  classical
  set P := π.ρ.prod π'.ρ with hPdef
  let J : W →ₗ[ℂ] π.V × π'.V := j.prod j'
  have hJ : IsTypeMap T P J := by
    refine ⟨fun a b h => hj.1 (congrArg Prod.fst h), fun γ v => ?_⟩
    show (j (T (redK k (Fin n) γ) v), j' (T (redK k (Fin n) γ) v)) = P γ (j v, j' v)
    rw [hj.2, hj'.2, hPdef, Representation.prod_apply_apply]
  have hPω : HasCentralChar P ω := by
    intro z v
    rw [Representation.prod_apply_apply, hω z v.1, hω' z v.2]
    rfl
  have hPs : GlobalTheory.PRep.IsSmooth P := by
    intro v
    have := (π.smooth v.1).inter (π'.smooth v.2)
    convert this using 1
    ext γ
    simp [P, Representation.prod_apply_apply, Prod.ext_iff]
  set U : Submodule ℂ (π.V × π'.V) := Submodule.span ℂ {x | ∃ γ w, x = P γ (J w)} with hU
  have hUst : ∀ γ, ∀ x ∈ U, P γ x ∈ U := by
    intro γ x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨γ', w, rfl⟩ := hx
      apply Submodule.subset_span
      exact ⟨γ * γ', w, by rw [map_mul]; rfl⟩
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add]
      exact U.add_mem hx hy
    | smul c x _ hx =>
      rw [map_smul]
      exact U.smul_mem c hx
  have hkey : ∀ x ∈ U, x ∈ fixed P (KOne k (Fin n)) → x ∈ LinearMap.range J := by
    intro x hx hfx
    have hle : U ≤ LinearMap.range J ⊔ twKer P (KOne k (Fin n)) 1 := by
      rw [hU, Submodule.span_le]
      rintro _ ⟨γ, w, rfl⟩
      exact apply_mem_sup hT hPω hJ γ w
    obtain ⟨r, hr, t, ht, rfl⟩ := Submodule.mem_sup.mp (hle hx)
    have hrf := range_le_fixed hJ hr
    have htf : t ∈ fixed P (KOne k (Fin n)) := by
      have := (fixed P (KOne k (Fin n))).sub_mem hfx hrf
      simpa using this
    have ht0 : t = 0 := GlobalTheory.IwahoriInj.eq_zero_of_fixed hPs GlobalTheory.DepthZeroJac.isCompact_KOne htf ht
    rw [ht0, add_zero]
    exact hr
  have hJU : ∀ w, J w ∈ U := fun w => Submodule.subset_span ⟨1, w, by rw [map_one]; rfl⟩
  obtain ⟨w0, hw0⟩ := exists_ne (0 : W)
  have hinr : ∀ v' : π'.V, ((0 : π.V), v') ∈ U → v' = 0 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨v', hv'U, hv'0⟩ := hcon
    have hB : U.comap (LinearMap.inr ℂ π.V π'.V) = ⊤ := top_of_stable π' _ (by
        intro γ y hy
        have := hUst γ _ hy
        rw [LinearMap.inr_apply, Representation.prod_apply_apply, map_zero] at this
        exact this) ⟨v', hv'U, hv'0⟩
    have hmem : ((0 : π.V), j' w0) ∈ U := by
      have : j' w0 ∈ U.comap (LinearMap.inr ℂ π.V π'.V) := hB ▸ Submodule.mem_top
      exact this
    have hfix0 : ((0 : π.V), j' w0) ∈ fixed P (KOne k (Fin n)) := by
      rw [GlobalTheory.IwahoriInj.mem_fixed]
      intro h hh
      rw [Representation.prod_apply_apply, map_zero,
        GlobalTheory.IwahoriInj.mem_fixed.mp (range_le_fixed hj' ⟨w0, rfl⟩) h hh]
    obtain ⟨w1, hw1⟩ := hkey _ hmem hfix0
    have h1 : j w1 = 0 := congrArg Prod.fst hw1
    have h2 : j' w1 = j' w0 := congrArg Prod.snd hw1
    have : w1 = 0 := hj.1 (by rw [h1, map_zero])
    rw [this, map_zero] at h2
    exact hw0 (hj'.1 (by rw [← h2, map_zero]))
  have hinl : ∀ v : π.V, (v, (0 : π'.V)) ∈ U → v = 0 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨v, hvU, hv0⟩ := hcon
    have hB : U.comap (LinearMap.inl ℂ π.V π'.V) = ⊤ := top_of_stable π _ (by
        intro γ y hy
        have := hUst γ _ hy
        rw [LinearMap.inl_apply, Representation.prod_apply_apply, map_zero] at this
        exact this) ⟨v, hvU, hv0⟩
    have hmem : (j w0, (0 : π'.V)) ∈ U := by
      have : j w0 ∈ U.comap (LinearMap.inl ℂ π.V π'.V) := hB ▸ Submodule.mem_top
      exact this
    have hfix0 : (j w0, (0 : π'.V)) ∈ fixed P (KOne k (Fin n)) := by
      rw [GlobalTheory.IwahoriInj.mem_fixed]
      intro h hh
      rw [Representation.prod_apply_apply, map_zero,
        GlobalTheory.IwahoriInj.mem_fixed.mp (range_le_fixed hj ⟨w0, rfl⟩) h hh]
    obtain ⟨w1, hw1⟩ := hkey _ hmem hfix0
    have h1 : j' w1 = 0 := congrArg Prod.snd hw1
    have h2 : j w1 = j w0 := congrArg Prod.fst hw1
    have : w1 = 0 := hj'.1 (by rw [h1, map_zero])
    rw [this, map_zero] at h2
    exact hw0 (hj.1 (by rw [← h2, map_zero]))
  have hfst : U.map (LinearMap.fst ℂ π.V π'.V) = ⊤ := top_of_stable π _ (by
      rintro γ _ ⟨x, hx, rfl⟩
      refine ⟨P γ x, hUst γ x hx, ?_⟩
      rw [LinearMap.fst_apply, LinearMap.fst_apply, Representation.prod_apply_apply]) ⟨j w0, ⟨J w0, hJU w0, rfl⟩, fun h => hw0 (hj.1 (by rw [h, map_zero]))⟩
  have hsnd : U.map (LinearMap.snd ℂ π.V π'.V) = ⊤ := top_of_stable π' _ (by
      rintro γ _ ⟨x, hx, rfl⟩
      refine ⟨P γ x, hUst γ x hx, ?_⟩
      rw [LinearMap.snd_apply, LinearMap.snd_apply, Representation.prod_apply_apply]) ⟨j' w0, ⟨J w0, hJU w0, rfl⟩, fun h => hw0 (hj'.1 (by rw [h, map_zero]))⟩
  let Fst : U →ₗ[ℂ] π.V := (LinearMap.fst ℂ π.V π'.V).comp U.subtype
  let Snd : U →ₗ[ℂ] π'.V := (LinearMap.snd ℂ π.V π'.V).comp U.subtype
  have hFb : Function.Bijective Fst := by
    refine ⟨(injective_iff_map_eq_zero Fst).mpr fun x hx => ?_, fun v => ?_⟩
    · have h1 : (x : π.V × π'.V).1 = 0 := hx
      have h2 : (x : π.V × π'.V).2 = 0 := hinr _ (by
        have := x.2
        rw [← Prod.mk.eta (p := (x : π.V × π'.V)), h1] at this
        exact this)
      exact Subtype.ext (Prod.ext h1 h2)
    · have hv : v ∈ U.map (LinearMap.fst ℂ π.V π'.V) := hfst ▸ Submodule.mem_top
      obtain ⟨x, hx, rfl⟩ := hv
      exact ⟨⟨x, hx⟩, rfl⟩
  have hSb : Function.Bijective Snd := by
    refine ⟨(injective_iff_map_eq_zero Snd).mpr fun x hx => ?_, fun v => ?_⟩
    · have h2 : (x : π.V × π'.V).2 = 0 := hx
      have h1 : (x : π.V × π'.V).1 = 0 := hinl _ (by
        have := x.2
        rw [← Prod.mk.eta (p := (x : π.V × π'.V)), h2] at this
        exact this)
      exact Subtype.ext (Prod.ext h1 h2)
    · have hv : v ∈ U.map (LinearMap.snd ℂ π.V π'.V) := hsnd ▸ Submodule.mem_top
      obtain ⟨x, hx, rfl⟩ := hv
      exact ⟨⟨x, hx⟩, rfl⟩
  let e : π.V ≃ₗ[ℂ] π'.V := (LinearEquiv.ofBijective Fst hFb).symm.trans (LinearEquiv.ofBijective Snd hSb)
  refine ⟨Representation.Equiv.mk e (fun γ => ?_)⟩
  ext v
  set u := (LinearEquiv.ofBijective Fst hFb).symm v with hu
  have hu1 : (u : π.V × π'.V).1 = v := by
    have := (LinearEquiv.ofBijective Fst hFb).apply_symm_apply v
    rw [← hu] at this
    exact this
  have hsymm : (LinearEquiv.ofBijective Fst hFb).symm (π.ρ γ v) = ⟨P γ u, hUst γ _ u.2⟩ := by
    rw [LinearEquiv.symm_apply_eq]
    show π.ρ γ v = (P γ u).1
    rw [Representation.prod_apply_apply, hu1]
  show Snd ((LinearEquiv.ofBijective Fst hFb).symm (π.ρ γ v)) = π'.ρ γ (Snd u)
  rw [hsymm]
  show (P γ u).2 = _
  rw [Representation.prod_apply_apply]
  rfl

section Bridge

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]
  (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)

private def resEquiv : 𝓀[w.adicCompletion E] ≃+* ZMod g :=
  (Ideal.quotEquivOfEq (DiscreteGroups.sglob.DzIso.ker_redO i hi).symm).trans
    (RingHom.quotientKerEquivOfSurjective (DiscreteGroups.sglob.DzIso.redO_surjective i hi))

private theorem resEquiv_residue (y : 𝒪[w.adicCompletion E]) :
    resEquiv i hi (IsLocalRing.residue _ y) = DiscreteGroups.sglob.DzIso.redO i hi y := rfl

private def glMap (n : ℕ) : GL (Fin n) 𝓀[w.adicCompletion E] →* Gn g n :=
  GeneralLinearGroup.map (resEquiv i hi).toRingHom

private theorem glMap_redK {n : ℕ} (κ : GL (Fin n) ℤ_[g]) :
    glMap i hi n (redK (w.adicCompletion E) (Fin n) (DiscreteGroups.sglob.DzIso.toKO i hi n κ)) = GlobalTheory.GLp.red g n κ := by
  ext a b
  have h1 : ((glMap i hi n) (redK (w.adicCompletion E) (Fin n) (DiscreteGroups.sglob.DzIso.toKO i hi n κ)) : Matrix (Fin n) (Fin n) (ZMod g)) a b
      = resEquiv i hi ((redK (w.adicCompletion E) (Fin n) (DiscreteGroups.sglob.DzIso.toKO i hi n κ) : Matrix (Fin n) (Fin n) _) a b) := rfl
  rw [h1, redK_apply, resEquiv_residue]
  show PadicInt.toZMod (DiscreteGroups.sglob.DzIso.toInt i hi _) = PadicInt.toZMod ((κ : Matrix (Fin n) (Fin n) ℤ_[g]) a b)
  congr 1
  apply PadicInt.ext
  rw [DiscreteGroups.sglob.DzIso.coe_toInt]
  show i.symm (i _) = _
  simp only [RingEquiv.symm_apply_apply]
  rfl

private theorem finCusp_comp {n : ℕ} (τ : FDRep ℂ (Gn g n)) (hτ : IsCusp τ.character) :
    FinCusp (τ.ρ.comp (glMap i hi n)) := by
  classical
  intro s d e hne v hv
  obtain ⟨Q, a, ha, han, hQ⟩ := DiscreteGroups.sglob.DzLc.exists_perm_conj e hne
  have key : ∀ (h : Gn g n) (y : τ), τ.ρ h⁻¹ (τ.ρ h y) = y := by
    intro h y
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  set v' := τ.ρ (glMap i hi n Q)⁻¹ v with hv'
  have hfix : ∀ u ∈ GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks n a), τ.ρ u v' = v' := by
    intro u hu
    let x : GL (Fin n) 𝓀[w.adicCompletion E] := GeneralLinearGroup.map (resEquiv i hi).symm.toRingHom u
    have hx : x ∈ GlobalTheory.FiniteGL.unipRadical 𝓀[w.adicCompletion E] (GlobalTheory.FiniteGL.twoBlocks n a) := by
      intro p q hpq
      have h0 : ((u : Matrix (Fin n) (Fin n) (ZMod g)) - 1) p q = 0 := hu p q hpq
      have hc : ((x : Matrix (Fin n) (Fin n) 𝓀[w.adicCompletion E]) - 1) p q
          = (resEquiv i hi).symm (((u : Matrix (Fin n) (Fin n) (ZMod g)) - 1) p q) := by
        simp only [Matrix.sub_apply, Matrix.one_apply, map_sub]
        split_ifs <;> simp [x]
      rw [hc, h0, map_zero]
    have hux : glMap i hi n x = u := by
      ext p q
      simp [glMap, x]
    have h1 := hv _ (hQ x hx)
    simp only [MonoidHom.coe_comp, Function.comp_apply, map_mul, Module.End.mul_apply, hux] at h1
    rw [map_inv] at h1
    calc τ.ρ u v' = τ.ρ (glMap i hi n Q)⁻¹ (τ.ρ (glMap i hi n Q) (τ.ρ u v')) := (key _ _).symm
      _ = v' := by rw [hv', h1]
  have hsum := DiscreteGroups.sglob.DzLc.sum_unip_eq_zero τ hτ ha han
  have hs : (∑ u : GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks n a), τ.ρ u) v' = 0 := by
    rw [hsum]
    rfl
  rw [LinearMap.sum_apply] at hs
  simp only [fun u : GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks n a) => hfix u u.2,
    Finset.sum_const, Finset.card_univ] at hs
  have hv0 : v' = 0 := by
    rw [← Nat.cast_smul_eq_nsmul ℂ] at hs
    exact (smul_eq_zero.mp hs).resolve_left (by exact_mod_cast Fintype.card_ne_zero)
  have : v = τ.ρ (glMap i hi n Q) v' := by
    rw [hv', ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  rw [this, hv0, map_zero]

private theorem isTypeMap_of {n : ℕ} (τ : FDRep ℂ (Gn g n)) (hτ : IsCusp τ.character) {V : Type} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (φ : τ →ₗ[ℂ] V) (h0 : φ ≠ 0)
    (hφ : ∀ (κ : GL (Fin n) ℤ_[g]) (v : τ), φ (τ.ρ (GlobalTheory.GLp.red g n κ) v) =
      (π.comp (GeneralLinearGroup.map i.toRingHom)) (GlobalTheory.GLp.inc g n κ) (φ v)) :
    IsTypeMap (τ.ρ.comp (glMap i hi n)) π φ := by
  constructor
  · have hsimp := DiscreteGroups.sglob.DzType.Kon.simple_of_isIrr τ hτ.2.1
    have hirr := (GlobalTheory.T.simple_iff_irreducible.1 _ τ).mp hsimp
    rcases hirr.2 (LinearMap.ker φ) (by
        intro γ v hv
        obtain ⟨κ, rfl⟩ := GlobalTheory.GLp.Model.red_surjective n γ
        rw [LinearMap.mem_ker] at hv ⊢
        rw [hφ, hv, map_zero]) with h | h
    · exact LinearMap.ker_eq_bot.mp h
    · exact absurd (LinearMap.ker_eq_top.mp h) h0
  · intro γ v
    obtain ⟨κ, rfl⟩ := DiscreteGroups.sglob.DzIso.toKO_surjective i hi n γ
    show φ (τ.ρ (glMap i hi n (redK (w.adicCompletion E) (Fin n) (DiscreteGroups.sglob.DzIso.toKO i hi n κ))) v) = _
    rw [glMap_redK, hφ]
    rfl

end Bridge

end UpperTheory.Zero.LLC.DetT

open UpperTheory.Zero.LLC.DetT in
theorem UpperTheory.Zero.LLC.detByType :
    UpperTheory.Zero.LLC.DetByType := by
  intro E Ω _ _ _ _ _ A w _ g _ i hi n hn σ σ' τ τ' ω hτ hττ' hinf hinf' hω hω'
  obtain ⟨φ, hφ0, hφ⟩ := hinf
  obtain ⟨φ', hφ'0, hφ'⟩ := hinf'
  have hirr' : IsIrr τ'.character := hττ' ▸ hτ.2.1
  haveI := DiscreteGroups.sglob.DzType.Kon.simple_of_isIrr τ hτ.2.1
  haveI := DiscreteGroups.sglob.DzType.Kon.simple_of_isIrr τ' hirr'
  have hiso : Nonempty (τ ≅ τ') := GlobalTheory.Top.Lq.iso_of_char τ τ' (fun x => by rw [hττ'])
  obtain ⟨e, he⟩ := (GlobalTheory.T.simple_iff_irreducible.2 _ τ τ').mp hiso
  have hτc : IsCusp τ'.character := hττ' ▸ hτ
  haveI : Nontrivial τ.V := ((GlobalTheory.T.simple_iff_irreducible.1 _ τ).mp inferInstance).1
  let ψ : τ →ₗ[ℂ] σ'.V := φ'.comp e.toLinearMap
  have hψ0 : ψ ≠ 0 := by
    intro h
    apply hφ'0
    ext x
    have := LinearMap.congr_fun h (e.symm x)
    simpa [ψ] using this
  have hψ : ∀ (κ : GL (Fin n) ℤ_[g]) (v : τ), ψ (τ.ρ (GlobalTheory.GLp.red g n κ) v) =
      (σ'.ρ.comp (GeneralLinearGroup.map i.toRingHom)) (GlobalTheory.GLp.inc g n κ) (ψ v) := by
    intro κ v
    show φ' (e (τ.ρ (GlobalTheory.GLp.red g n κ) v)) = _
    rw [he, hφ']
    rfl
  have h1 := isTypeMap_of i hi τ hτ σ.ρ φ hφ0 hφ
  have h2 := isTypeMap_of i hi τ hτ σ'.ρ ψ hψ0 hψ
  obtain ⟨q⟩ := equiv_of_typeMaps (finCusp_comp i hi τ hτ) σ' σ hω' hω h2 h1
  show (⟨n, σ'.cl⟩ : GlobalTheory.LocGL.IrrGL _) = ⟨n, σ.cl⟩
  rw [GlobalTheory.SmGL.IrrRep.cl_eq_iff.mpr ⟨q⟩]
