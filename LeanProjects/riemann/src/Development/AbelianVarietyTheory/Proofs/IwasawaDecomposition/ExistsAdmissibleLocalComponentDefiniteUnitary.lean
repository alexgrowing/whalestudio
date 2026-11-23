import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryAdmissibleFiniteMultiplicityStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousRetractionOntoUnitaryLocalPointsStatement

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.DefU.LocAdm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem continuous_finGL : Continuous (finGL E n) := by
  refine Continuous.units_map _ ?_
  have hs : Continuous (sFin E : Af E → Ad E) :=
    (continuous_const.prodMk continuous_id : Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E))
  exact (continuous_const.add (continuous_id.matrix_map hs) :
    Continuous fun x : Matrix (Fin n) (Fin n) (Af E) => 1 - matN n (sFin E) 1 + x.map (sFin E))

theorem t2Space_finiteAdeleRing_cmField : T2Space (FiniteAdeleRing (𝓞 E) E) :=
  inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
    (fun v => (v.adicCompletionIntegers E : Set (v.adicCompletion E))) Filter.cofinite))

theorem t2Space_adeleRing_cmField : T2Space (Ad E) :=
  haveI := t2Space_finiteAdeleRing_cmField (E := E)
  haveI : T2Space (InfiniteAdeleRing E) := inferInstanceAs (T2Space ((v : InfinitePlace E) → v.Completion))
  inferInstanceAs (T2Space (InfiniteAdeleRing E × FiniteAdeleRing (𝓞 E) E))

theorem t2Space_adelicGL_cmField : T2Space (GA E n) :=
  haveI := t2Space_adeleRing_cmField (E := E)
  Units.isEmbedding_embedProduct.t2Space

theorem isClosed_UA : IsClosed ((UA E n : Subgroup (GA E n)) : Set (GA E n)) := by
  haveI := t2Space_adeleRing_cmField (E := E)
  show IsClosed {g : GA E n | ((g : Matrix (Fin n) (Fin n) (Ad E)).map (conjAd E))ᵀ * 1 * (g : Matrix (Fin n) (Fin n) (Ad E)) = 1}
  exact isClosed_eq (((Units.continuous_val.matrix_map GlobalTheory.ThetaPull.continuous_conjAd).matrix_transpose.matrix_mul
    continuous_const).matrix_mul Units.continuous_val) continuous_const

theorem locU_le_finU (w : HeightOneSpectrum (𝓞 E)) : locU n w ≤ finU E n := inf_le_left

theorem continuous_inclusion_locU (w : HeightOneSpectrum (𝓞 E)) :
    Continuous (Subgroup.inclusion (locU_le_finU (n := n) w)) :=
  Continuous.subtype_mk continuous_subtype_val _

theorem isClosed_of_retract (w : HeightOneSpectrum (𝓞 E)) (r : UA E n →* locU n w) (hr : Continuous r)
    (hx : ∀ x : locU n w, r x = x) : IsClosed ((locU n w : Subgroup (UA E n)) : Set (UA E n)) := by
  haveI := t2Space_adelicGL_cmField (E := E) (n := n)
  have e : ((locU n w : Subgroup (UA E n)) : Set (UA E n)) = {x | ((r x : locU n w) : UA E n) = x} := by
    ext x
    constructor
    · intro h
      exact congrArg Subtype.val (hx ⟨x, h⟩)
    · intro h
      change x ∈ locU n w
      rw [← show ((r x : locU n w) : UA E n) = x from h]
      exact (r x).2

  rw [e]
  exact isClosed_eq (continuous_subtype_val.comp hr) continuous_id

theorem isSmooth_loc (π : AutSub E n) (w : HeightOneSpectrum (𝓞 E)) :
    IsSmooth (π.rep.comp (locU n w).subtype) := fun v => by
  have h := (π.isAut.aut v.1 v.2).level
  convert h.preimage (continuous_inclusion_locU (n := n) w) using 1
  ext k
  exact Subtype.ext_iff

theorem exists_compact_open (w : HeightOneSpectrum (𝓞 E)) (r : UA E n →* locU n w) (hr : Continuous r)
    (hx : ∀ x : locU n w, r x = x) (L : Subgroup (finU E n)) (hL : IsOpen (L : Set (finU E n))) :
    ∃ K : Subgroup (locU n w), IsOpen (K : Set (locU n w)) ∧ IsCompact (K : Set (locU n w)) ∧
      K ≤ L.comap (Subgroup.inclusion (locU_le_finU w)) := by
  obtain ⟨U0, hU0o, hU0c⟩ := GlobalTheory.GLIntegral.exists_isOpen_isCompact E n
  let p : locU n w →* GL (Fin n) (Af E) :=
    (GeneralLinearGroup.map (pFin E)).comp ((UA E n).subtype.comp (locU n w).subtype)
  have hp : Continuous p := continuous_map_pFin.comp (continuous_subtype_val.comp continuous_subtype_val)
  let K : Subgroup (locU n w) := U0.comap p ⊓ L.comap (Subgroup.inclusion (locU_le_finU w))
  have hKo : IsOpen (K : Set (locU n w)) :=
    (hU0o.preimage hp).inter (hL.preimage (continuous_inclusion_locU w))
  have hι : Topology.IsClosedEmbedding (fun x : locU n w => ((x : UA E n) : GA E n)) :=
    isClosed_UA.isClosedEmbedding_subtypeVal.comp (isClosed_of_retract w r hr hx).isClosedEmbedding_subtypeVal
  refine ⟨K, hKo, IsCompact.of_isClosed_subset (hι.isCompact_preimage (hU0c.image continuous_finGL))
    (Subgroup.isClosed_of_isOpen K hKo) fun x hx => ⟨p x, (Subgroup.mem_inf.1 hx).1, ?_⟩, inf_le_right⟩
  have h1 : GeneralLinearGroup.map (pInf E) ((x : UA E n) : GA E n) = 1 := (Subgroup.mem_inf.1 x.2).1
  exact ga_ext (by rw [pInf_finGL, h1]) (by rw [pFin_finGL]; rfl)

theorem exists_admissible_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AutSub E n)
    (w : HeightOneSpectrum (𝓞 E)), ∃ σ : SmIrr (locU n w), IsAdmissible σ.ρ ∧
      IsCompAlong π.V (locU n w) (MonoidHom.id _) σ.ρ := by
  intro E _ _ _ n π w
  obtain ⟨r, hr, hrx, hrc⟩ := GlobalTheory.T.exists_continuous_retraction_onto_unitaryLocalPoints E n w
  have hadm := (GlobalTheory.T.definiteUnitary_admissible_finiteMultiplicity E n π).1
  let ρ : Representation ℂ (locU n w) π.V := π.rep.comp (locU n w).subtype
  let ρf : Representation ℂ (finU E n) π.V := π.rep.comp (finU E n).subtype
  have hρ : IsSmooth ρ := isSmooth_loc π w
  have hle := locU_le_finU (n := n) w
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.isAut.ne_bot
  let v0 : π.V := ⟨φ, hφ⟩
  have hv0 : v0 ≠ 0 := fun e => h0 (congrArg Subtype.val e)
  let L : Subgroup (finU E n) := LocEx.stab ρf v0
  have hLo : IsOpen (L : Set (finU E n)) := by
    convert (π.isAut.aut φ hφ).level using 1
    ext k
    exact Subtype.ext_iff
  have hLl : IsOpen ((L.comap (Subgroup.inclusion hle) : Subgroup (locU n w)) : Set (locU n w)) :=
    hLo.preimage (continuous_inclusion_locU w)
  obtain ⟨K, hKo, hKc, hKL⟩ := exists_compact_open w r hr hrx L hLo

  have hT : ∀ x : UA E n, ∀ (g : locU n w) (y : π.V),
      π.rep ((r x : UA E n)⁻¹ * x) (ρ g y) = ρ g (π.rep ((r x : UA E n)⁻¹ * x) y) := fun x g y => by
    change π.rep _ (π.rep (g : UA E n) y) = π.rep (g : UA E n) (π.rep _ y)
    rw [← Module.End.mul_apply, ← map_mul, (hrc x g).eq, map_mul, Module.End.mul_apply]
  have hst : ∀ x, ∀ y ∈ LocEx.nullPart ρ K, π.rep x y ∈ LocEx.nullPart ρ K := fun x y hy => by
    have h1 := LocEx.nullPart_act ρ K (r x) (LocEx.nullPart_comm ρ K (π.rep ((r x : UA E n)⁻¹ * x)) (hT x) hy)
    have e : π.rep x y = ρ (r x) (π.rep ((r x : UA E n)⁻¹ * x) y) := by
      change _ = π.rep (r x : UA E n) _
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
    rw [e]
    exact h1
  have hφK : v0 ∈ fixed ρ K := LocEx.mem_fix.2 fun k hk => hKL hk
  have h2 : ∀ W : Submodule ℂ π.V, (∀ g, ∀ v ∈ W, ρ g v ∈ W) → W ⊓ fixed ρ K = ⊥ → W = ⊥ := by
    intro W hW h
    rcases ((CuspRep.isIrreducible_iff _).1 π.isIrreducible_rep).2 (LocEx.nullPart ρ K) hst with h1 | h1
    · exact le_bot_iff.1 (h1 ▸ LocEx.le_nullPart hρ hKc W hW h)
    · exact absurd (LocEx.eq_zero_of_mem_nullPart hρ hKc hφK (h1 ▸ Submodule.mem_top)) hv0

  let M : Subgroup (UA E n) := L.map (finU E n).subtype ⊓ r.ker
  have hcomm : ∀ k ∈ M, ∀ g : locU n w, Commute k (g : UA E n) := fun k hk g => by
    have h := hrc k g
    rwa [MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 hk).2, OneMemClass.coe_one, inv_one, one_mul] at h
  have hU : ∀ g, ∀ v ∈ fixed π.rep M, ρ g v ∈ fixed π.rep M := fun g v hv => LocEx.mem_fix.2 fun k hk => by
    change π.rep k (π.rep (g : UA E n) v) = π.rep (g : UA E n) v
    rw [← Module.End.mul_apply, ← map_mul, (hcomm k hk g).eq, map_mul, Module.End.mul_apply,
      LocEx.mem_fix.1 hv k hk]
  have hU0 : fixed π.rep M ≠ ⊥ := (Submodule.ne_bot_iff _).2 ⟨v0, LocEx.mem_fix.2 fun k hk => by
    obtain ⟨k', hk', rfl⟩ := (Subgroup.mem_inf.1 hk).1
    exact hk', hv0⟩
  have hfin : ∀ K' : Subgroup (locU n w), IsOpen (K' : Set (locU n w)) →
      FiniteDimensional ℂ ↥(fixed π.rep M ⊓ fixed ρ K') := fun K' hK' => by
    let r' : finU E n →* locU n w := r.comp (finU E n).subtype
    let H : Subgroup (finU E n) := L ⊓ (K' ⊓ L.comap (Subgroup.inclusion hle)).comap r'
    have hHo : IsOpen (H : Set (finU E n)) := hLo.inter ((hK'.inter hLl).preimage (hr.comp continuous_subtype_val))
    haveI := hadm H hHo
    refine Submodule.finiteDimensional_of_le (S₂ := fixed ρf H) fun v hv => LocEx.mem_fix.2 fun k hk => ?_
    obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.1 hv
    obtain ⟨hkL, hkK, hkL'⟩ := And.intro (Subgroup.mem_inf.1 hk).1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hk).2)
    have hcM : (r k : UA E n)⁻¹ * k ∈ M := by
      refine Subgroup.mem_inf.2 ⟨⟨(Subgroup.inclusion hle (r' k))⁻¹ * k, L.mul_mem (L.inv_mem hkL') hkL, rfl⟩, ?_⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, hrx (r k), inv_mul_cancel]
    have e1 := LocEx.mem_fix.1 hv1 _ hcM
    have e2 : π.rep (r k : UA E n) v = v := LocEx.mem_fix.1 hv2 _ hkK
    change π.rep (k : UA E n) v = v
    rw [← mul_inv_cancel_left (r k : UA E n) (k : UA E n), map_mul, Module.End.mul_apply, e1, e2]
  obtain ⟨σ, ⟨f, hf0, hf⟩, hσ⟩ := LocEx.exists_irred hρ hKo h2 (fixed π.rep M) hU hU0 hfin
  refine ⟨σ, hσ, σ.irred, π.V.subtype ∘ₗ f, fun e => hf0 (LinearMap.ext fun v => Subtype.ext ?_), fun v => (f v).2,
    fun x v => ?_⟩
  · exact LinearMap.congr_fun e v
  · change (f (σ.ρ x v)).1 = _
    rw [hf]
    rfl

end GlobalTheory.DefU.LocAdm
