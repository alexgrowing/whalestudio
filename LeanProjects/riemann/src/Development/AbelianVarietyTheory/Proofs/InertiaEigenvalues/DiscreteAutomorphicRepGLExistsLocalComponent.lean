import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CapCommuteRtInfGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CommuteCapOfCommuteEop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasInfCharInfCharOfCommute
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EquivOfISupRange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsOpenIsCompact
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ResidualSpectrumByClass
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CuspidalMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DiscreteSpectrumResidual
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep Matrix GlobalTheory.PRep GlobalTheory.Published GlobalTheory.UnitaryBC
open GlobalTheory.CuspRep.LocEx

namespace GlobalTheory.DiscLocEx

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def opD {V : Submodule ℂ (Sm E a)} (hV : IsStable V) (o : Op E a) : Module.End ℂ V := (act o).restrict (hV o)

def finPartD {V : Submodule ℂ (Sm E a)} (hV : IsStable V) : Representation ℂ (GL (Fin a) (Af E)) V :=
  GlobalTheory.PRep.sub (finRep E a) V fun k => hV (.fin k)

def locRepD {V : Submodule ℂ (Sm E a)} (hV : IsStable V) (w : HeightOneSpectrum (𝓞 E)) :
    Representation ℂ (GL (Fin a) (w.adicCompletion E)) V :=
  (finPartD hV).comp (locGL E a w)

theorem isSmooth_finPartD {V : Submodule ℂ (Sm E a)} (hV : IsStable V) (ha : ∀ φ ∈ V, IsAutForm φ) :
    IsSmooth (finPartD hV) := fun φ => by
  convert (ha _ φ.2).level using 1
  ext k
  exact Subtype.ext_iff

theorem isSmooth_locRepD {V : Submodule ℂ (Sm E a)} (hV : IsStable V) (ha : ∀ φ ∈ V, IsAutForm φ)
    (w : HeightOneSpectrum (𝓞 E)) : IsSmooth (locRepD hV w) := fun φ =>
  (isSmooth_finPartD hV ha φ).preimage (CuspSub.continuous_locGL w)

theorem exists_scalarD {V : Submodule ℂ (Sm E a)} (hV : IsDiscrete V) {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a)
    (hc : ∀ o : Op E a, Commute z (act o)) : ∃ c : ℂ, ∀ φ ∈ V, z φ = c • φ := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 hV.ne_bot
  set U := Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a) with hU
  have hfin : FiniteDimensional ℂ U := (hV.aut φ hφ).zfin
  have hle : U ≤ V := Submodule.span_le.2 (by
    rintro _ ⟨y, hy, rfl⟩
    exact Zalg_stable (fun X => hV.stable (.lie X)) hy φ hφ)
  have hst : ∀ x ∈ U, z x ∈ U := fun x hx => by
    have : U ≤ U.comap z := Submodule.span_le.2 (by
      rintro _ ⟨y, hy, rfl⟩
      exact Submodule.subset_span ⟨z * y, mul_mem hz hy, rfl⟩)
    exact this hx
  have hφU : φ ∈ U := Submodule.subset_span ⟨1, one_mem _, rfl⟩
  have : Nontrivial U := ⟨⟨φ, hφU⟩, 0, fun h => h0 (congrArg Subtype.val h)⟩
  obtain ⟨c, hc'⟩ := Module.End.exists_eigenvalue (z.restrict hst)
  obtain ⟨v, hv⟩ := hc'.exists_hasEigenvector
  have hv1 : z v.1 = c • v.1 := congrArg Subtype.val hv.apply_eq_smul
  refine ⟨c, fun ψ hψ => ?_⟩
  rcases hV.irred (V ⊓ z.eigenspace c) inf_le_left (fun o x hx => ⟨hV.stable o x hx.1, by
    have h1 : z x = c • x := Module.End.mem_eigenspace_iff.1 hx.2
    refine Module.End.mem_eigenspace_iff.2 ?_
    rw [← map_smul, ← h1]
    exact LinearMap.congr_fun (hc o).eq x⟩) with h | h
  · have : v.1 ∈ V ⊓ z.eigenspace c := ⟨hle v.2, Module.End.mem_eigenspace_iff.2 hv1⟩
    rw [h] at this
    exact absurd (Subtype.ext ((Submodule.mem_bot ℂ).1 this)) hv.2
  · rw [← h] at hψ
    exact Module.End.mem_eigenspace_iff.1 hψ.2

theorem nullPart_opD {V : Submodule ℂ (Sm E a)} (hV : IsStable V) (w : HeightOneSpectrum (𝓞 E))
    (K : Subgroup (GL (Fin a) (w.adicCompletion E)))
    (o : Op E a) {x : V} (hx : x ∈ nullPart (locRepD hV w) K) : opD hV o x ∈ nullPart (locRepD hV w) K := by
  cases o with
  | fin k =>
    have h1 := nullPart_act _ K (GeneralLinearGroup.map (pLoc E w) k) (nullPart_comm _ K
      (finPartD hV ((locGL E a w (GeneralLinearGroup.map (pLoc E w) k))⁻¹ * k)) (fun g' y => by
      simp only [locRepD, MonoidHom.comp_apply]
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
        LocUniq.comm_locGL w (map_pLoc_inv_mul w k)]) hx)
    rwa [locRepD, MonoidHom.comp_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left] at h1
  | cpt k =>
    refine nullPart_comm _ K _ (fun g y => Subtype.ext ?_) hx
    change (rt E a (infGL E a (Unitary.toUnits k)) * rt E a (finGL E a (locGL E a w g))) y.1 =
      (rt E a (finGL E a (locGL E a w g)) * rt E a (infGL E a (Unitary.toUnits k))) y.1
    rw [← map_mul, ← map_mul, infGL_comm]
  | lie X =>
    refine nullPart_comm _ K _ (fun g y => Subtype.ext ?_) hx
    exact LinearMap.congr_fun (lie_rt_fin X (locGL E a w g)) y.1

theorem eq_bot_of_fixedD {V : Submodule ℂ (Sm E a)} (hV : IsDiscrete V) (w : HeightOneSpectrum (𝓞 E))
    {K : Subgroup (GL (Fin a) (w.adicCompletion E))} (hK : IsCompact (K : Set (GL (Fin a) (w.adicCompletion E))))
    {φ : V} (h0 : φ ≠ 0) (hφ : φ ∈ fixed (locRepD hV.stable w) K) (W : Submodule ℂ V)
    (hW : ∀ g, ∀ v ∈ W, locRepD hV.stable w g v ∈ W) (h : W ⊓ fixed (locRepD hV.stable w) K = ⊥) : W = ⊥ := by
  have hi := Submodule.map_injective_of_injective V.injective_subtype
  rcases hV.irred ((nullPart (locRepD hV.stable w) K).map V.subtype) (Submodule.map_subtype_le _ _) (by
    rintro o _ ⟨x, hx, rfl⟩
    exact ⟨_, nullPart_opD hV.stable w K o hx, rfl⟩) with h1 | h1
  · have h2 : nullPart (locRepD hV.stable w) K = ⊥ := hi (h1.trans (Submodule.map_bot _).symm)
    exact le_bot_iff.1 (h2 ▸ le_nullPart (isSmooth_locRepD hV.stable hV.aut w) hK W hW h)
  · have h2 : nullPart (locRepD hV.stable w) K = ⊤ := hi (h1.trans (Submodule.map_subtype_top _).symm)
    exact absurd (eq_zero_of_mem_nullPart (isSmooth_locRepD hV.stable hV.aut w) hK hφ (h2 ▸ Submodule.mem_top)) h0

def typePartD {V : Submodule ℂ (Sm E a)} (hV : IsStable V) (w : HeightOneSpectrum (𝓞 E))
    (L : Subgroup (GL (Fin a) (Af E)))
    {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Kinf E a) W) : Submodule ℂ V where
  carrier := {ψ | (∀ k ∈ L, GeneralLinearGroup.map (pLoc E w) k = 1 → finPartD hV k ψ = ψ) ∧
    ∀ g : GA E a, (fun k : Kinf E a => (cptRep E a k ψ.1).1 g) ∈ AutFin.coeffSpan ρ}
  add_mem' := fun hx hy => ⟨fun k h1 h2 => by rw [map_add, hx.1 k h1 h2, hy.1 k h1 h2],
    fun g => add_mem (hx.2 g) (hy.2 g)⟩
  zero_mem' := ⟨fun _ _ _ => map_zero _, fun _ => zero_mem _⟩
  smul_mem' := fun c _ hx => ⟨fun k h1 h2 => by rw [map_smul, hx.1 k h1 h2],
    fun g => Submodule.smul_mem _ c (hx.2 g)⟩

theorem typePartD_act {V : Submodule ℂ (Sm E a)} (hV : IsStable V) (w : HeightOneSpectrum (𝓞 E))
    (L : Subgroup (GL (Fin a) (Af E)))
    {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Kinf E a) W) (g : GL (Fin a) (w.adicCompletion E))
    (x : V) (hx : x ∈ typePartD hV w L ρ) : locRepD hV w g x ∈ typePartD hV w L ρ := by
  refine ⟨fun k h1 h2 => ?_, fun y => ?_⟩
  · rw [locRepD, MonoidHom.comp_apply, ← Module.End.mul_apply, ← map_mul, LocUniq.comm_locGL w h2, map_mul,
      Module.End.mul_apply, hx.1 k h1 h2]
  · convert hx.2 (y * finGL E a (locGL E a w g)) using 2 with k
    change x.1.1 (y * infGL E a _ * finGL E a _) = x.1.1 (y * finGL E a _ * infGL E a _)
    rw [mul_assoc, mul_assoc, infGL_comm]

theorem finiteDimensional_typePartD (h : AutomorphicFormsFiniteGL) {V : Submodule ℂ (Sm E a)} (hV : IsDiscrete V)
    (w : HeightOneSpectrum (𝓞 E))
    {L : Subgroup (GL (Fin a) (Af E))} (hL : IsOpen (L : Set (GL (Fin a) (Af E))))
    {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] {ρ : Representation ℂ (Kinf E a) W}
    (hρ : AutFin.IsContRep ρ) (K : Subgroup (GL (Fin a) (w.adicCompletion E)))
    (hK : IsOpen (K : Set (GL (Fin a) (w.adicCompletion E)))) :
    FiniteDimensional ℂ ↥(typePartD hV.stable w L ρ ⊓ fixed (locRepD hV.stable w) K) := by
  have hc : ∀ τ u, ∃ c : ℂ, ∀ φ ∈ V, cap τ u φ = c • φ := fun τ u =>
    exists_scalarD hV (z := cap τ u) (Algebra.subset_adjoin ⟨τ, u, rfl⟩) fun o => by
      cases o with
      | fin k => exact commute_cap_finRep τ u k
      | cpt k => exact GlobalTheory.CapAdInv.cap_commute_rt_infGL E a τ u _
      | lie X => exact commute_cap_lie τ u X
  choose c hc using hc
  have := h E a (L ⊓ (K ⊓ L.comap (locGL E a w)).comap (GeneralLinearGroup.map (pLoc E w)))
    (hL.inter ((hK.inter (hL.preimage (CuspSub.continuous_locGL w))).preimage (continuous_map_pLoc w))) W ρ hρ c
  refine FiniteDimensional.of_injective ((V.subtype ∘ₗ (typePartD hV.stable w L ρ ⊓
    fixed (locRepD hV.stable w) K).subtype).codRestrict
    (Submodule.span ℂ (AutFinGL.forms
      (L ⊓ (K ⊓ L.comap (locGL E a w)).comap (GeneralLinearGroup.map (pLoc E w))) ρ c))
    fun v => Submodule.subset_span ⟨hV.aut _ v.1.2, fun k hk => ?_, v.2.1.2, fun τ u => hc τ u _ v.1.2⟩)
    fun v v' e => Subtype.ext (Subtype.ext (by have e' := congrArg Subtype.val e; exact e'))
  have h1 := v.2.1.1 _ (L.mul_mem (L.inv_mem hk.2.2) hk.1) (map_pLoc_inv_mul w k)
  have h2 := mem_fix.1 v.2.2 _ hk.2.1
  have h3 : finPartD hV.stable k v.1 = v.1 := by
    rw [← mul_inv_cancel_left (locGL E a w (GeneralLinearGroup.map (pLoc E w) k)) k, map_mul, Module.End.mul_apply, h1]
    exact h2
  exact congrArg Subtype.val h3

theorem exists_irred_sub (h : AutomorphicFormsFiniteGL) {V : Submodule ℂ (Sm E a)} (hV : IsDiscrete V)
    (w : HeightOneSpectrum (𝓞 E)) :
    ∃ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), (∃ f : σ.V →ₗ[ℂ] V, f ≠ 0 ∧
      ∀ g v, f (σ.ρ g v) = locRepD hV.stable w g (f v)) ∧ IsAdmissible σ.ρ := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 hV.ne_bot
  have h0' : (⟨φ, hφ⟩ : V) ≠ 0 := fun e => h0 (congrArg Subtype.val e)
  have hL : IsOpen (stab (finPartD hV.stable) ⟨φ, hφ⟩ : Set (GL (Fin a) (Af E))) :=
    isSmooth_finPartD hV.stable hV.aut _
  obtain ⟨K, ho, hc, hK⟩ := exists_compact_open w _ hL
  have : FiniteDimensional ℂ (orbSpan φ) := (hV.aut φ hφ).kfin
  refine exists_irred (isSmooth_locRepD hV.stable hV.aut w) ho (eq_bot_of_fixedD hV w hc h0' (mem_fix.2 hK))
    (typePartD hV.stable w (stab (finPartD hV.stable) ⟨φ, hφ⟩) (sub (cptRep E a) (orbSpan φ) (orbSpan_stable φ)))
    (typePartD_act hV.stable w _ _)
    ((Submodule.ne_bot_iff _).2 ⟨⟨φ, hφ⟩, ⟨fun k hk _ => hk, ?_⟩, h0'⟩)
    (finiteDimensional_typePartD h hV w hL (isContRep_sub _ _))
  exact AutFinGL.type_of_map (sub (cptRep E a) (orbSpan φ) (orbSpan_stable φ)) (orbSpan φ).subtype (fun _ _ => rfl)
    ⟨φ, Submodule.subset_span ⟨1, by simp⟩⟩

end GlobalTheory.DiscLocEx

open GlobalTheory.DiscSpec GlobalTheory.SmGL in

theorem GlobalTheory.DiscLocEx.exists_isLocCompGL : AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E]
    [IsTotallyComplex E] (N : ℕ), ∀ (V : Submodule ℂ (Sm E N)), IsDiscrete V →
    ∀ w : HeightOneSpectrum (𝓞 E), ∃ σ' , IsLocCompGL V w σ' := by
  intro h E _ _ _ N V hV w
  obtain ⟨σ, ⟨f, hf0, hf⟩, -⟩ := GlobalTheory.DiscLocEx.exists_irred_sub h hV w
  refine ⟨σ, V.subtype ∘ₗ f, fun e => hf0 (LinearMap.ext fun v => Subtype.ext ?_), fun v => (f v).2,
    fun g v => congrArg Subtype.val (hf g v)⟩
  exact LinearMap.congr_fun e v
