import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CapCommuteRtInfGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CommuteCapOfCommuteEop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasInfCharInfCharOfCommute
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EquivOfISupRange
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsOpenIsCompact
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep Matrix GlobalTheory.PRep GlobalTheory.Published

namespace GlobalTheory.CuspRep.LocEx

section Rep

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

theorem mem_fix {ρ : Representation ℂ G V} {K : Subgroup G} {v : V} : v ∈ fixed ρ K ↔ ∀ k ∈ K, ρ k v = v :=
  ⟨fun h k hk => by simpa using h ⟨k, hk⟩, fun h k => by simpa using h k k.2⟩

def stab (ρ : Representation ℂ G V) (v : V) : Subgroup G where
  carrier := {g | ρ g v = v}
  mul_mem' := fun {a b} ha hb => by
    change ρ (a * b) v = v
    rw [map_mul, Module.End.mul_apply, hb, ha]
  one_mem' := by simp
  inv_mem' := fun {a} ha => by
    change ρ a⁻¹ v = v
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul]; simp

def nullPart (ρ : Representation ℂ G V) (K : Subgroup G) : Submodule ℂ V := ⨅ g, (twKer ρ K 1).comap (ρ g)

theorem nullPart_act (ρ : Representation ℂ G V) (K : Subgroup G) (g : G) {x : V} (hx : x ∈ nullPart ρ K) :
    ρ g x ∈ nullPart ρ K := by
  simp only [nullPart, Submodule.mem_iInf, Submodule.mem_comap] at hx ⊢
  intro h
  rw [← Module.End.mul_apply, ← map_mul]
  exact hx _

theorem nullPart_comm (ρ : Representation ℂ G V) (K : Subgroup G) (T : Module.End ℂ V)
    (hT : ∀ g x, T (ρ g x) = ρ g (T x)) {x : V} (hx : x ∈ nullPart ρ K) : T x ∈ nullPart ρ K := by
  simp only [nullPart, Submodule.mem_iInf, Submodule.mem_comap] at hx ⊢
  intro h
  rw [← hT]
  have : twKer ρ K 1 ≤ (twKer ρ K 1).comap T := Submodule.span_le.2 (by
    rintro _ ⟨n, v, rfl⟩
    exact Submodule.subset_span ⟨n, T v, by rw [map_sub, map_smul, hT]⟩)
  exact this (hx h)

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem le_nullPart {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) {K : Subgroup G} (hK : IsCompact (K : Set G))
    (W : Submodule ℂ V) (hW : ∀ g, ∀ v ∈ W, ρ g v ∈ W) (h : W ⊓ fixed ρ K = ⊥) : W ≤ nullPart ρ K := by
  intro x hx
  simp only [nullPart, Submodule.mem_iInf, Submodule.mem_comap]
  intro g
  rw [← LocGL.idem_eq_zero_iff hρ hK, ← Submodule.mem_bot ℂ, ← h]
  refine ⟨?_, LocGL.idem_mem hρ hK _⟩
  obtain ⟨U, -, _, hU⟩ := LocGL.exists_normal_fix hρ hK (ρ g x)
  letI := Fintype.ofFinite (K ⧸ U)
  rw [LocGL.idem_eq_cosetSum hρ hK U hU]
  exact W.smul_mem _ (W.sum_mem fun q _ => hW _ _ (hW _ _ hx))

theorem eq_zero_of_mem_nullPart {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) {K : Subgroup G}
    (hK : IsCompact (K : Set G)) {x : V} (h1 : x ∈ fixed ρ K) (h2 : x ∈ nullPart ρ K) : x = 0 := by
  have h3 : ρ 1 x ∈ twKer ρ K 1 := (Submodule.mem_iInf _).1 h2 1
  rw [map_one] at h3
  exact Submodule.disjoint_def.1 (LocGL.isCompl_fixed_twKer hρ hK).disjoint x h1 h3

omit [IsTopologicalGroup G] in

theorem exists_irred {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) {K : Subgroup G} (hK : IsOpen (K : Set G))
    (h2 : ∀ W : Submodule ℂ V, (∀ g, ∀ v ∈ W, ρ g v ∈ W) → W ⊓ fixed ρ K = ⊥ → W = ⊥)
    (U : Submodule ℂ V) (hU : ∀ g, ∀ v ∈ U, ρ g v ∈ U) (h0 : U ≠ ⊥)
    (hfin : ∀ K' : Subgroup G, IsOpen (K' : Set G) → FiniteDimensional ℂ ↥(U ⊓ fixed ρ K')) :
    ∃ σ : SmIrr G, (∃ f : σ.V →ₗ[ℂ] V, f ≠ 0 ∧ ∀ g v, f (σ.ρ g v) = ρ g (f v)) ∧ IsAdmissible σ.ρ := by
  let S : Set (Submodule ℂ V) := {W | W ≤ U ∧ (∀ g, ∀ v ∈ W, ρ g v ∈ W) ∧ W ≠ ⊥}
  obtain ⟨W, ⟨hWU, hW, hW0⟩, hmin⟩ := (measure fun W : Submodule ℂ V => Module.finrank ℂ ↥(W ⊓ fixed ρ K)).wf.has_min S
    ⟨U, le_rfl, hU, h0⟩
  let X : Submodule ℂ V := InfSet.sInf {Y | (∀ g, ∀ v ∈ Y, ρ g v ∈ Y) ∧ W ⊓ fixed ρ K ≤ Y}
  have hX : ∀ g, ∀ v ∈ X, ρ g v ∈ X := fun g v hv =>
    Submodule.mem_sInf.2 fun Y hY => hY.1 g v (Submodule.mem_sInf.1 hv Y hY)
  have hXW : X ≤ W := sInf_le ⟨hW, inf_le_left⟩
  have hX0 : X ≠ ⊥ := fun e => hW0 (h2 W hW (le_bot_iff.1 (e ▸ le_sInf fun Y hY => hY.2)))
  have hsm : IsSmooth (sub ρ X hX) := fun v => by
    convert hρ v.1 using 1
    ext k
    exact Subtype.ext_iff
  have : Nontrivial X := Submodule.nontrivial_iff_ne_bot.2 hX0
  refine ⟨⟨X, sub ρ X hX, hsm, (isIrreducible_iff _).2 ⟨this, fun Y hY => ?_⟩⟩,
    ⟨X.subtype, fun e => hX0 ?_, fun _ _ => rfl⟩, hsm, fun K' hK' _ => ?_⟩
  · have hi := Submodule.map_injective_of_injective X.injective_subtype
    have hs : ∀ g, ∀ v ∈ Y.map X.subtype, ρ g v ∈ Y.map X.subtype := by
      rintro g _ ⟨v, hv, rfl⟩
      exact ⟨_, hY g v hv, rfl⟩
    refine or_iff_not_imp_left.2 fun hY0 => hi ?_
    have hle := (Submodule.map_subtype_le X Y).trans hXW
    have h3 := hmin _ ⟨hle.trans hWU, hs, fun e => hY0 (hi (e.trans (Submodule.map_bot _).symm))⟩
    have := hfin K hK
    have : FiniteDimensional ℂ ↥(W ⊓ fixed ρ K) := Submodule.finiteDimensional_of_le (inf_le_inf_right _ hWU)
    have h4 := Submodule.eq_of_le_of_finrank_le (inf_le_inf_right (fixed ρ K) hle) (not_lt.1 h3)
    rw [Submodule.map_subtype_top]
    exact le_antisymm (Submodule.map_subtype_le X Y) (sInf_le ⟨hs, h4 ▸ inf_le_left⟩)
  · rw [← X.range_subtype, e, LinearMap.range_zero]
  · have := hfin K' hK'
    refine FiniteDimensional.of_injective ((X.subtype ∘ₗ (fixed (sub ρ X hX) K').subtype).codRestrict
      (U ⊓ fixed ρ K') fun v => ⟨hWU (hXW v.1.2), mem_fix.2 fun k hk => congrArg Subtype.val (mem_fix.1 v.2 k hk)⟩)
      fun v v' e => Subtype.ext (Subtype.ext (by have e' := congrArg Subtype.val e; exact e'))

end Rep

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem continuous_map_pLoc (w : HeightOneSpectrum (𝓞 E)) :
    Continuous (GeneralLinearGroup.map (pLoc E w) : GL (Fin a) (Af E) → GL (Fin a) (w.adicCompletion E)) :=
  Continuous.units_map _ (continuous_id.matrix_map (RestrictedProduct.continuous_eval w))

theorem exists_compact_open (w : HeightOneSpectrum (𝓞 E)) (L : Subgroup (GL (Fin a) (Af E)))
    (hL : IsOpen (L : Set (GL (Fin a) (Af E)))) : ∃ K : Subgroup (GL (Fin a) (w.adicCompletion E)),
    IsOpen (K : Set (GL (Fin a) (w.adicCompletion E))) ∧ IsCompact (K : Set (GL (Fin a) (w.adicCompletion E))) ∧
      ∀ k ∈ K, locGL E a w k ∈ L := by
  obtain ⟨U, ho, hc⟩ := GlobalTheory.GLIntegral.exists_isOpen_isCompact E a
  have h : IsOpen (((U ⊓ L).comap (locGL E a w) : Subgroup _) : Set (GL (Fin a) (w.adicCompletion E))) :=
    (ho.inter hL).preimage (CuspSub.continuous_locGL w)
  exact ⟨_, h, (hc.image (continuous_map_pLoc w)).of_isClosed_subset (Subgroup.isClosed_of_isOpen _ h)
    fun k hk => ⟨_, hk.1, pLoc_locGL w k⟩, fun k hk => hk.2⟩

theorem map_pLoc_inv_mul (w : HeightOneSpectrum (𝓞 E)) (k : GL (Fin a) (Af E)) :
    GeneralLinearGroup.map (pLoc E w) ((locGL E a w (GeneralLinearGroup.map (pLoc E w) k))⁻¹ * k) = 1 := by
  rw [map_mul, map_inv, pLoc_locGL, inv_mul_cancel]

variable [IsTotallyComplex E]

theorem nullPart_op (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) (K : Subgroup (GL (Fin a) (w.adicCompletion E)))
    (o : Op E a) {x : π.V} (hx : x ∈ nullPart (π.locRep w) K) : π.op o x ∈ nullPart (π.locRep w) K := by
  cases o with
  | fin k =>
    have h1 := nullPart_act _ K (GeneralLinearGroup.map (pLoc E w) k) (nullPart_comm _ K
      (π.finPart ((locGL E a w (GeneralLinearGroup.map (pLoc E w) k))⁻¹ * k)) (fun g' y => by
      simp only [CuspSub.locRep, MonoidHom.comp_apply]
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
        LocUniq.comm_locGL w (map_pLoc_inv_mul w k)]) hx)
    rwa [CuspSub.locRep, MonoidHom.comp_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left] at h1
  | cpt k =>
    refine nullPart_comm _ K _ (fun g y => Subtype.ext ?_) hx
    change (rt E a (infGL E a (Unitary.toUnits k)) * rt E a (finGL E a (locGL E a w g))) y.1 =
      (rt E a (finGL E a (locGL E a w g)) * rt E a (infGL E a (Unitary.toUnits k))) y.1
    rw [← map_mul, ← map_mul, infGL_comm]
  | lie X =>
    refine nullPart_comm _ K _ (fun g y => Subtype.ext ?_) hx
    exact LinearMap.congr_fun (lie_rt_fin X (locGL E a w g)) y.1

theorem eq_bot_of_fixed (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E))
    {K : Subgroup (GL (Fin a) (w.adicCompletion E))} (hK : IsCompact (K : Set (GL (Fin a) (w.adicCompletion E))))
    {φ : π.V} (h0 : φ ≠ 0) (hφ : φ ∈ fixed (π.locRep w) K) (W : Submodule ℂ π.V)
    (hW : ∀ g, ∀ v ∈ W, π.locRep w g v ∈ W) (h : W ⊓ fixed (π.locRep w) K = ⊥) : W = ⊥ := by
  have hi := Submodule.map_injective_of_injective π.V.injective_subtype
  rcases π.irred ((nullPart (π.locRep w) K).map π.V.subtype) (Submodule.map_subtype_le _ _) (by
    rintro o _ ⟨x, hx, rfl⟩
    exact ⟨_, nullPart_op π w K o hx, rfl⟩) with h1 | h1
  · have h2 : nullPart (π.locRep w) K = ⊥ := hi (h1.trans (Submodule.map_bot _).symm)
    exact le_bot_iff.1 (h2 ▸ le_nullPart (π.isSmooth_locRep w) hK W hW h)
  · have h2 : nullPart (π.locRep w) K = ⊤ := hi (h1.trans (Submodule.map_subtype_top _).symm)
    exact absurd (eq_zero_of_mem_nullPart (π.isSmooth_locRep w) hK hφ (h2 ▸ Submodule.mem_top)) h0

def orbSpan (φ : Sm E a) : Submodule ℂ (Sm E a) := Submodule.span ℂ (Set.range fun k => cptRep E a k φ)

theorem orbSpan_stable (φ : Sm E a) (k : Kinf E a) (x : Sm E a) (hx : x ∈ orbSpan φ) : cptRep E a k x ∈ orbSpan φ := by
  have : orbSpan φ ≤ (orbSpan φ).comap (cptRep E a k) := Submodule.span_le.2 (by
    rintro _ ⟨k', rfl⟩
    exact Submodule.subset_span ⟨k * k', by simp⟩)
  exact this hx

theorem isContRep_sub (S : Submodule ℂ (Sm E a)) [FiniteDimensional ℂ S] (hS : ∀ k, ∀ x ∈ S, cptRep E a k x ∈ S) :
    AutFin.IsContRep (sub (cptRep E a) S hS) := by
  intro ℓ x
  have h : Submodule.span ℂ (Set.range fun g : GA E a =>
      ((LinearMap.proj g).comp ((Sm E a).subtype.comp S.subtype) : S →ₗ[ℂ] ℂ)) = ⊤ := by
    refine Submodule.span_eq_top_of_ne_zero fun z hz => ?_
    by_contra hc
    push Not at hc
    exact hz (Subtype.ext (Subtype.ext (funext fun g => hc _ ⟨g, rfl⟩)))
  have hl : ℓ ∈ (⊤ : Submodule ℂ (S →ₗ[ℂ] ℂ)) := Submodule.mem_top
  rw [← h] at hl
  induction hl using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨g, rfl⟩ := hy
    have h1 : Continuous fun k : Kinf E a => chart x.1.1 g (toL (Unitary.toUnits k).val) :=
      (x.1.2 g).continuousOn.comp_continuous (f := fun k : Kinf E a => toL (Unitary.toUnits k).val)
        continuous_subtype_val fun k => val_mem_invSet _
    simp only [chart_val] at h1
    exact h1
  | zero => exact continuous_const
  | add y z _ _ hy hz => exact hy.add hz
  | smul c y _ hy => exact hy.const_smul c

def typePart (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) (L : Subgroup (GL (Fin a) (Af E)))
    {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Kinf E a) W) : Submodule ℂ π.V where
  carrier := {ψ | (∀ k ∈ L, GeneralLinearGroup.map (pLoc E w) k = 1 → π.finPart k ψ = ψ) ∧
    ∀ g : GA E a, (fun k : Kinf E a => (cptRep E a k ψ.1).1 g) ∈ AutFin.coeffSpan ρ}
  add_mem' := fun hx hy => ⟨fun k h1 h2 => by rw [map_add, hx.1 k h1 h2, hy.1 k h1 h2],
    fun g => add_mem (hx.2 g) (hy.2 g)⟩
  zero_mem' := ⟨fun _ _ _ => map_zero _, fun _ => zero_mem _⟩
  smul_mem' := fun c _ hx => ⟨fun k h1 h2 => by rw [map_smul, hx.1 k h1 h2],
    fun g => Submodule.smul_mem _ c (hx.2 g)⟩

theorem typePart_act (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) (L : Subgroup (GL (Fin a) (Af E)))
    {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Kinf E a) W) (g : GL (Fin a) (w.adicCompletion E))
    (x : π.V) (hx : x ∈ typePart π w L ρ) : π.locRep w g x ∈ typePart π w L ρ := by
  refine ⟨fun k h1 h2 => ?_, fun y => ?_⟩
  · rw [CuspSub.locRep, MonoidHom.comp_apply, ← Module.End.mul_apply, ← map_mul, LocUniq.comm_locGL w h2, map_mul,
      Module.End.mul_apply, hx.1 k h1 h2]
  · convert hx.2 (y * finGL E a (locGL E a w g)) using 2 with k
    change x.1.1 (y * infGL E a _ * finGL E a _) = x.1.1 (y * finGL E a _ * infGL E a _)
    rw [mul_assoc, mul_assoc, infGL_comm]

theorem finiteDimensional_typePart (h : AutomorphicFormsFiniteGL) (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E))
    {L : Subgroup (GL (Fin a) (Af E))} (hL : IsOpen (L : Set (GL (Fin a) (Af E))))
    {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] {ρ : Representation ℂ (Kinf E a) W}
    (hρ : AutFin.IsContRep ρ) (K : Subgroup (GL (Fin a) (w.adicCompletion E)))
    (hK : IsOpen (K : Set (GL (Fin a) (w.adicCompletion E)))) :
    FiniteDimensional ℂ ↥(typePart π w L ρ ⊓ fixed (π.locRep w) K) := by
  have hc : ∀ τ u, ∃ c : ℂ, ∀ φ ∈ π.V, cap τ u φ = c • φ := fun τ u =>
    π.exists_scalar (z := cap τ u) (Algebra.subset_adjoin ⟨τ, u, rfl⟩) fun o => by
      cases o with
      | fin k => exact commute_cap_finRep τ u k
      | cpt k => exact GlobalTheory.CapAdInv.cap_commute_rt_infGL E a τ u _
      | lie X => exact commute_cap_lie τ u X
  choose c hc using hc
  have := h E a (L ⊓ (K ⊓ L.comap (locGL E a w)).comap (GeneralLinearGroup.map (pLoc E w)))
    (hL.inter ((hK.inter (hL.preimage (CuspSub.continuous_locGL w))).preimage (continuous_map_pLoc w))) W ρ hρ c
  refine FiniteDimensional.of_injective ((π.V.subtype ∘ₗ (typePart π w L ρ ⊓ fixed (π.locRep w) K).subtype).codRestrict
    (Submodule.span ℂ (AutFinGL.forms
      (L ⊓ (K ⊓ L.comap (locGL E a w)).comap (GeneralLinearGroup.map (pLoc E w))) ρ c))
    fun v => Submodule.subset_span ⟨(π.cusp _ v.1.2).1, fun k hk => ?_, v.2.1.2, fun τ u => hc τ u _ v.1.2⟩)
    fun v v' e => Subtype.ext (Subtype.ext (by have e' := congrArg Subtype.val e; exact e'))
  have h1 := v.2.1.1 _ (L.mul_mem (L.inv_mem hk.2.2) hk.1) (map_pLoc_inv_mul w k)
  have h2 := mem_fix.1 v.2.2 _ hk.2.1
  have h3 : π.finPart k v.1 = v.1 := by
    rw [← mul_inv_cancel_left (locGL E a w (GeneralLinearGroup.map (pLoc E w) k)) k, map_mul, Module.End.mul_apply, h1]
    exact h2
  exact congrArg Subtype.val h3

theorem exists_isLocComp (h : AutomorphicFormsFiniteGL) : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E]
    (a : ℕ) (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)),
    ∃ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), π.IsLocComp w σ ∧ IsAdmissible σ.ρ := by
  intro E _ _ _ a π w
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  have h0' : (⟨φ, hφ⟩ : π.V) ≠ 0 := fun e => h0 (congrArg Subtype.val e)
  have hL : IsOpen (stab π.finPart ⟨φ, hφ⟩ : Set (GL (Fin a) (Af E))) := π.isSmooth_finPart _
  obtain ⟨K, ho, hc, hK⟩ := exists_compact_open w _ hL
  have : FiniteDimensional ℂ (orbSpan φ) := (π.cusp φ hφ).1.kfin
  refine exists_irred (π.isSmooth_locRep w) ho (eq_bot_of_fixed π w hc h0' (mem_fix.2 hK))
    (typePart π w (stab π.finPart ⟨φ, hφ⟩) (sub (cptRep E a) (orbSpan φ) (orbSpan_stable φ))) (typePart_act π w _ _)
    ((Submodule.ne_bot_iff _).2 ⟨⟨φ, hφ⟩, ⟨fun k hk _ => hk, ?_⟩, h0'⟩)
    (finiteDimensional_typePart h π w hL (isContRep_sub _ _))
  exact AutFinGL.type_of_map (sub (cptRep E a) (orbSpan φ) (orbSpan_stable φ)) (orbSpan φ).subtype (fun _ _ => rfl)
    ⟨φ, Submodule.subset_span ⟨1, by simp⟩⟩

end GlobalTheory.CuspRep.LocEx
