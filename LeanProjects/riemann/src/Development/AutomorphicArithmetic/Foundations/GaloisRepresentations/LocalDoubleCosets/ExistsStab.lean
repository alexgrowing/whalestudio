import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.TracePow
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwKerWhitCharReflect
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.HeckeRepresentationSatake
import GroundTheory.AutomorphicForms.LocallyConstantCompact
import GroundTheory.AutomorphicForms.GLnLocal

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel Matrix MeasureTheory UpperTheory.ConvolutionTheory.Loc MulAction

namespace UpperTheory.Gal.LocD

section Abstract

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type} [AddCommGroup V] [Module ℂ V]

private theorem exists_stab {π : Representation ℂ G V} (hπ : IsSmooth π) (v : V) :
    ∃ K : Subgroup G, IsOpen (K : Set G) ∧ ∀ k ∈ K, π k v = v := by
  refine ⟨{ carrier := {g | π g v = v}, mul_mem' := ?_, one_mem' := ?_, inv_mem' := ?_ }, hπ v, fun k hk => hk⟩
  · intro a b (ha : π a v = v) (hb : π b v = v)
    show π (a * b) v = v
    rw [map_mul, Module.End.mul_apply, hb, ha]
  · show π 1 v = v
    simp
  · intro a (ha : π a v = v)
    show π a⁻¹ v = v
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul]
    simp

private theorem ker_isOpen {B : Subgroup G} {χ : B →* ℂˣ} {π : Representation ℂ G V} (hπ : IsSmooth π)
    {l : V →ₗ[ℂ] ℂ} (hl : l ≠ 0) (hb : ∀ (b : B) (v : V), l (π b v) = (χ b : ℂ) * l v) :
    IsOpen (χ.ker : Set B) := by
  obtain ⟨v₀, hv₀⟩ : ∃ v, l v ≠ 0 := by
    by_contra h
    push_neg at h
    exact hl (LinearMap.ext h)
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  have h1 : IsOpen ((↑) ⁻¹' {g : G | π g v₀ = v₀} : Set B) := (hπ v₀).preimage continuous_subtype_val
  refine Filter.mem_of_superset (h1.mem_nhds (by simp)) fun b hb' => ?_
  have h2 : π (b : G) v₀ = v₀ := hb'
  have h3 := hb b v₀
  rw [h2] at h3
  have h4 : (χ b : ℂ) = 1 := by
    have : ((χ b : ℂ) - 1) * l v₀ = 0 := by rw [sub_mul, ← h3]; ring
    rcases mul_eq_zero.1 this with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hv₀
  exact Units.ext h4

private theorem indF_stable (B : Subgroup G) (χ : B →* ℂˣ) (g : G) :
    ∀ f ∈ indF B χ, rightReg ℂ G ℂ g f ∈ indF B χ := by
  rintro f ⟨h, K, hK, hf⟩
  refine ⟨fun b x => ?_, K.comap (MulAut.conj g⁻¹).toMonoidHom, ?_, fun k hk x => ?_⟩
  · show f (b * x * g) = _ * f (x * g)
    rw [mul_assoc, h]
  · exact hK.preimage (by
      show Continuous fun x : G => g⁻¹ * x * g⁻¹⁻¹
      fun_prop)
  · show f (x * k * g) = f (x * g)
    have hk' : g⁻¹ * k * g⁻¹⁻¹ ∈ K := hk
    have := hf _ hk' (x * g)
    rw [← this]
    congr 1
    group

private def rho (B : Subgroup G) (χ : B →* ℂˣ) : Representation ℂ G (indF B χ) :=
  sub (rightReg ℂ G ℂ) (indF B χ) (indF_stable B χ)

private theorem rho_apply (B : Subgroup G) (χ : B →* ℂˣ) (g : G) (φ : indF B χ) (x : G) :
    ((rho B χ g φ : indF B χ) : G → ℂ) x = (φ : G → ℂ) (x * g) := rfl

private theorem rho_smooth (B : Subgroup G) (χ : B →* ℂˣ) : IsSmooth (rho B χ) := by
  intro φ
  obtain ⟨-, K, hK, hf⟩ := φ.2
  rw [isOpen_iff_mem_nhds]
  intro g (hg : rho B χ g φ = φ)
  have h1 : IsOpen ((fun x => g⁻¹ * x) ⁻¹' (K : Set G)) := hK.preimage (by fun_prop)
  refine Filter.mem_of_superset (h1.mem_nhds (by simp)) fun y hy => ?_
  have hy' : g⁻¹ * y ∈ K := hy
  show rho B χ y φ = φ
  refine Subtype.ext (funext fun x => ?_)
  rw [rho_apply]
  have h2 : (φ : G → ℂ) (x * y) = (φ : G → ℂ) (x * g) := by
    have := hf _ hy' (x * g)
    rw [← this]
    congr 1
    group
  rw [h2, ← rho_apply, hg]

private def iota {B : Subgroup G} {χ : B →* ℂˣ} {π : Representation ℂ G V} (hπ : IsSmooth π)
    (l : V →ₗ[ℂ] ℂ) (hb : ∀ (b : B) (v : V), l (π b v) = (χ b : ℂ) * l v) : V →ₗ[ℂ] indF B χ where
  toFun v := ⟨fun g => l (π g v), fun b g => by
      show l (π (b * g) v) = _
      rw [map_mul, Module.End.mul_apply, hb], by
      obtain ⟨K, hK, hk⟩ := exists_stab hπ v
      refine ⟨K, hK, fun k h g => ?_⟩
      show l (π (g * k) v) = _
      rw [map_mul, Module.End.mul_apply, hk k h]⟩
  map_add' a b := by
    refine Subtype.ext (funext fun g => ?_)
    simp
  map_smul' c a := by
    refine Subtype.ext (funext fun g => ?_)
    simp

private theorem iota_apply {B : Subgroup G} {χ : B →* ℂˣ} {π : Representation ℂ G V} (hπ : IsSmooth π)
    (l : V →ₗ[ℂ] ℂ) (hb : ∀ (b : B) (v : V), l (π b v) = (χ b : ℂ) * l v) (v : V) (g : G) :
    ((iota hπ l hb v : indF B χ) : G → ℂ) g = l (π g v) := rfl

private theorem iota_equiv {B : Subgroup G} {χ : B →* ℂˣ} {π : Representation ℂ G V} (hπ : IsSmooth π)
    (l : V →ₗ[ℂ] ℂ) (hb : ∀ (b : B) (v : V), l (π b v) = (χ b : ℂ) * l v) (g : G) (v : V) :
    iota hπ l hb (π g v) = rho B χ g (iota hπ l hb v) := by
  refine Subtype.ext (funext fun x => ?_)
  rw [rho_apply, iota_apply, iota_apply, map_mul, Module.End.mul_apply]

private theorem iota_inj {B : Subgroup G} {χ : B →* ℂˣ} {π : Representation ℂ G V} (hπ : IsSmooth π)
    (hirr : π.IsIrreducible) {l : V →ₗ[ℂ] ℂ} (hl : l ≠ 0)
    (hb : ∀ (b : B) (v : V), l (π b v) = (χ b : ℂ) * l v) : Function.Injective (iota hπ l hb) := by
  rw [← LinearMap.ker_eq_bot]
  let S : Subrepresentation π := ⟨LinearMap.ker (iota hπ l hb), fun g v hv => by
    rw [LinearMap.mem_ker] at hv ⊢
    rw [iota_equiv, hv, map_zero]⟩
  rcases hirr.eq_bot_or_eq_top S with h | h
  · exact congrArg Subrepresentation.toSubmodule h
  · exfalso
    refine hl (LinearMap.ext fun v => ?_)
    have hv : v ∈ S.toSubmodule := by rw [h]; trivial
    have h0 : iota hπ l hb v = 0 := hv
    have := congrArg (fun φ : indF B χ => (φ : G → ℂ) 1) h0
    simpa [iota_apply] using this

end Abstract

theorem core : FunInv → GLCells → GLFacts → Core := by
  intro hF hC hG E _ _ _ _ n σ q hq V _ _ π hπ hirr A hA χ hχ l c hl hlb hlA
  obtain ⟨hBc, hNc, ⟨K, hKo, hKc, hKBK⟩, hθ, hs⟩ := hG E n
  obtain ⟨hsc, hsq, hsB, hsN⟩ := hs σ q hq
  obtain ⟨hlc, hsc2, ht2, -, -⟩ := UpperTheory.V.Z.Tf.Orb.gLTop E n
  haveI : TotallyDisconnectedSpace (GL (Fin n) E) := inferInstance
  have hχo : IsOpen (χ.ker : Set (borel E (Fin n))) := ker_isOpen hπ hl hlb
  set ι := iota hπ l hlb with hι
  have hinj : Function.Injective ι := iota_inj hπ hirr hl hlb
  have key : ∀ v g, ((ι (A v) : indF (borel E (Fin n)) χ) : GL (Fin n) E → ℂ) (sg σ g) = c * l (π g v) := by
    intro v g
    rw [hι, iota_apply, ← hA g v, hlA]
  refine ⟨fun hA0 hc => hA0 (LinearMap.ext fun v => ?_), fun ψ hψ hψσ v => ?_⟩
  · refine hinj ?_
    rw [LinearMap.zero_apply, map_zero]
    refine Subtype.ext (funext fun g => ?_)
    obtain ⟨g', rfl⟩ : ∃ g', sg σ g' = g := by
      obtain ⟨r, hr⟩ : ∃ r, q = r + 1 := ⟨q - 1, by have := hq.pos; omega⟩
      refine ⟨(sg σ)^[r] g, ?_⟩
      have := hsq g
      rw [hr, Function.iterate_succ_apply'] at this
      exact this
    rw [key, hc, zero_mul]
    rfl
  · refine GlobalTheory.CompanionTheory.PRep.WhitExact.twKer_whitChar_reflect E ψ hψ n π (rho (borel E (Fin n)) χ) hπ
      (rho_smooth _ _) ι hinj (fun g v => iota_equiv hπ l hlb g v) _ ?_
    by_contra hnot
    obtain ⟨l₀, hne, hl₀⟩ := Submodule.exists_le_ker_of_notMem hnot
    obtain ⟨L, hL⟩ := LinearMap.exists_extend l₀
    have hLv : ∀ φ : indF (borel E (Fin n)) χ, L (φ : GL (Fin n) E → ℂ) = l₀ φ := fun φ =>
      LinearMap.congr_fun hL φ
    have heq : ∀ (u : unipB E (Fin n)), ∀ φ ∈ indF (borel E (Fin n)) χ,
        L (fun x => φ (x * u)) = ((whitChar ψ n u : ℂˣ) : ℂ) * L φ := by
      intro u φ hφ
      have h1 : rho (borel E (Fin n)) χ u ⟨φ, hφ⟩ - ((whitChar ψ n u : ℂˣ) : ℂ) • ⟨φ, hφ⟩ ∈
          twKer (rho (borel E (Fin n)) χ) (unipB E (Fin n)) (whitChar ψ n) :=
        Submodule.subset_span ⟨u, _, rfl⟩
      have h2 := hl₀ h1
      rw [LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, sub_eq_zero, ← hLv, ← hLv] at h2
      exact h2
    have hinv := hF (GL (Fin n) E) (borel E (Fin n)) (unipB E (Fin n)) hBc hNc K hKo hKc hKBK (sg σ) q hq.pos hsc hsq hsB
      (fun u hu => sg_mem_unipB σ hu) (hC E n σ) χ (whitChar ψ n) hχo (hθ ψ hψ) hχ (hsN ψ hψσ) L heq
    have h3 := hinv _ (ι (A v)).2
    have h4 : ((ι (A v) : indF (borel E (Fin n)) χ) : GL (Fin n) E → ℂ) ∘ sg σ =
        ((c • ι v : indF (borel E (Fin n)) χ) : GL (Fin n) E → ℂ) := by
      funext g
      exact key v g
    rw [h4, hLv, hLv, map_smul, smul_eq_mul] at h3
    apply hne
    rw [map_sub, map_sub, map_smul, map_smul, smul_eq_mul, ← h3]
    ring

end UpperTheory.Gal.LocD

end
