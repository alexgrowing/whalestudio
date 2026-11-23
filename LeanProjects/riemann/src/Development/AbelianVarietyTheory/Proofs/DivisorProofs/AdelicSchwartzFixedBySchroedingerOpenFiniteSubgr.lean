import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulInvOf
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteAdeleVectorAnnihilatorsCompactOpenBasisStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CtxExists

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical Topology

noncomputable section

namespace GlobalTheory.WeilLevel

variable {F : Type} [Field F] [NumberField F] {N : ℕ}

theorem eventually_invariant {M : Type} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M] {Φ : M → ℂ}
    (h1 : IsLocallyConstant Φ) (h2 : HasCompactSupport Φ) : ∀ᶠ u in 𝓝 (0 : M), ∀ x, Φ (x + u) = Φ x := by
  have h : ∀ᶠ u in 𝓝 (0 : M), ∀ x ∈ tsupport Φ, Φ (x + u) = Φ x ∧ Φ (x - u) = Φ x := by
    apply h2.isCompact.eventually_forall_of_forall_eventually
    intro x _
    have a1 := (h1.comp_continuous (show Continuous fun z : M × M => z.2 + z.1 by fun_prop)).eventually_eq (0, x)
    have a2 := (h1.comp_continuous (show Continuous fun z : M × M => z.2 - z.1 by fun_prop)).eventually_eq (0, x)
    have a3 := (h1.comp_continuous (show Continuous fun z : M × M => z.2 by fun_prop)).eventually_eq (0, x)
    filter_upwards [a1, a2, a3] with z b1 b2 b3
    simp only [Function.comp, add_zero, sub_zero] at b1 b2 b3
    exact ⟨b1.trans b3.symm, b2.trans b3.symm⟩
  filter_upwards [h] with u hu x
  by_cases hx : x ∈ tsupport Φ
  · exact (hu x hx).1
  · by_cases hx' : x + u ∈ tsupport Φ
    · have := (hu _ hx').2
      rw [add_sub_cancel_right] at this
      exact this.symm
    · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']

theorem Bd_half_f (u y : Fin N → Af F) : Bd (Af F) (half F N) u y = u ⬝ᵥ y := by
  simp [Bd, half, dotProduct]

theorem annih_basis (hF : IsTotallyReal F) (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ) :
    (∀ K : Set (Fin N → Af F), IsCompact K → {y : Fin N → Af F | ∀ u ∈ K, ψ (pairA F 0 (u ⬝ᵥ y)) = 1} ∈ 𝓝 0) ∧
    ∀ U ∈ 𝓝 (0 : Fin N → Af F), ∃ L : AddSubgroup (Af F), IsOpen (L : Set (Af F)) ∧ IsCompact (L : Set (Af F)) ∧
      ∀ u : Fin N → Af F, (∀ l, u l ∈ L) → u ∈ U := by
  obtain ⟨lam, ν, hc⟩ := ctx_exists F hF ψ hψ N (half F N) (fun l => half_ne_zero l)
  obtain ⟨-, h2, h3⟩ := GlobalTheory.T.finiteAdeleVector_annihilators_compact_open_basis F N ψ lam ν (half F N) hc
  refine ⟨fun K hK => ?_, h3⟩
  have := h2 K hK
  simpa only [Bd_half_f] using this

def levelSub (L : AddSubgroup (Af F)) : AddSubgroup (VA F N) where
  carrier := {u | ∀ l, sndA F (u.1 l) ∈ L ∧ sndA F (u.2 l) ∈ L}
  zero_mem' := fun l => by simp
  add_mem' := fun ha hb l => by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, map_add]
    exact ⟨L.add_mem (ha l).1 (hb l).1, L.add_mem (ha l).2 (hb l).2⟩
  neg_mem' := fun ha l => by
    simp only [Prod.fst_neg, Prod.snd_neg, Pi.neg_apply, map_neg]
    exact ⟨L.neg_mem (ha l).1, L.neg_mem (ha l).2⟩

theorem isOpen_levelSub {L : AddSubgroup (Af F)} (hL : IsOpen (L : Set (Af F))) :
    IsOpen (levelSub (N := N) L : Set (VA F N)) := by
  have hs : Continuous fun z : AF F => sndA F z := continuous_snd
  have e : (levelSub (N := N) L : Set (VA F N)) =
      ⋂ l, ((fun u : VA F N => sndA F (u.1 l)) ⁻¹' L ∩ (fun u : VA F N => sndA F (u.2 l)) ⁻¹' L) := by
    ext u; simp [levelSub]
  rw [e]
  refine isOpen_iInter_of_finite fun l => IsOpen.inter ?_ ?_
  · exact hL.preimage (hs.comp ((continuous_apply l).comp continuous_fst))
  · exact hL.preimage (hs.comp ((continuous_apply l).comp continuous_snd))

end GlobalTheory.WeilLevel

namespace GlobalTheory.WeilLevel

variable {F : Type} [Field F] [NumberField F] {N : ℕ}

theorem adele_ext {z z' : AF F} (h1 : fstA F z = fstA F z') (h2 : sndA F z = sndA F z') : z = z' := Prod.ext h1 h2

theorem pure_level [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ) (hF : IsTotallyReal F) (hψ : IsCharAF F ψ)
    (f : SchwartzMap (Fin N → mixedEmbedding.mixedSpace F) ℂ) (g : (Fin N → Af F) → ℂ)
    (hg : g ∈ GlobalTheory.WeilM.SB (Fin N → Af F)) :
    ∃ U : AddSubgroup (VA F N), IsOpen (U : Set (VA F N)) ∧ ∀ u ∈ U, inf u.1 = 0 → inf u.2 = 0 →
      GlobalTheory.WeilM.schr ψ u (GlobalTheory.WeilM.pureA F f g) = GlobalTheory.WeilM.pureA F f g := by
  obtain ⟨hann, hbas⟩ := annih_basis (N := N) hF ψ hψ
  have hV := eventually_invariant hg.1 hg.2
  obtain ⟨L0, hL0o, hL0c, hL0V⟩ := hbas _ hV
  set c : Af F := algebraMap F (Af F) (1 / 2)
  have hK2 : IsCompact ((fun a : Fin N → Af F => c • a) '' {a | ∀ l, a l ∈ L0}) := by
    have : IsCompact {a : Fin N → Af F | ∀ l, a l ∈ L0} := by
      have := isCompact_univ_pi (fun _ : Fin N => hL0c)
      simpa [Set.pi] using this
    exact this.image (continuous_const_smul c)
  have hA1 := hann _ hg.2.isCompact
  have hA2 := hann _ hK2
  obtain ⟨L1, hL1o, -, hL1⟩ := hbas _ (Filter.inter_mem (Filter.inter_mem hV hA1) hA2)
  refine ⟨levelSub (L0 ⊓ L1), isOpen_levelSub (by rw [AddSubgroup.coe_inf]; exact hL0o.inter hL1o),
    fun u hu h1 h2 => ?_⟩
  set a : Fin N → Af F := fun l => sndA F (u.1 l)
  set b : Fin N → Af F := fun l => sndA F (u.2 l)
  have ha0 : ∀ l, a l ∈ L0 := fun l => (AddSubgroup.mem_inf.mp (hu l).1).1
  have ha1 : ∀ l, a l ∈ L1 := fun l => (AddSubgroup.mem_inf.mp (hu l).1).2
  have hb1 : ∀ l, b l ∈ L1 := fun l => (AddSubgroup.mem_inf.mp (hu l).2).2
  obtain ⟨⟨hVa, -⟩, -⟩ := hL1 a ha1
  obtain ⟨⟨-, hAb⟩, hA2b⟩ := hL1 b hb1
  have i1 : ∀ l, fstA F (u.1 l) = 0 := fun l => congrFun h1 l
  have i2 : ∀ l, fstA F (u.2 l) = 0 := fun l => congrFun h2 l
  funext x
  set xf : Fin N → Af F := fun i => (x i).2
  have ex : (fun i => ((x + u.1) i).2) = xf + a := by
    funext i; rfl
  have ex' : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((x + u.1) i).1) =
      fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1 := by
    funext i
    have : ((x + u.1) i).1 = (x i).1 := by
      show (x i).1 + (u.1 i).1 = (x i).1
      rw [show (u.1 i).1 = fstA F (u.1 i) from rfl, i1 i, add_zero]
    rw [this]
  simp only [GlobalTheory.WeilM.schr, GlobalTheory.WeilM.pureA]
  rw [ex, ex', hVa xf]
  by_cases hg0 : g xf = 0
  · rw [hg0]; simp
  have hxK : xf ∈ tsupport g := subset_tsupport g hg0
  have e : x ⬝ᵥ u.2 + ⅟(2 : AF F) * (u.1 ⬝ᵥ u.2) = pairA F 0 (xf ⬝ᵥ b) + pairA F 0 ((c • a) ⬝ᵥ b) := by
    apply adele_ext
    · simp only [map_add, map_mul]
      rw [show fstA F (x ⬝ᵥ u.2) = (fstA F).toRingHom (x ⬝ᵥ u.2) from rfl,
        show fstA F (u.1 ⬝ᵥ u.2) = (fstA F).toRingHom (u.1 ⬝ᵥ u.2) from rfl, RingHom.map_dotProduct, RingHom.map_dotProduct]
      have : (fstA F).toRingHom ∘ u.2 = 0 := funext i2
      rw [this, dotProduct_zero, dotProduct_zero, mul_zero, add_zero]
      rw [show ∀ p, fstA F (pairA F 0 p) = 0 from fun _ => rfl, show ∀ p, fstA F (pairA F 0 p) = 0 from fun _ => rfl, add_zero]
    · simp only [map_add, map_mul]
      rw [show sndA F (x ⬝ᵥ u.2) = (sndA F).toRingHom (x ⬝ᵥ u.2) from rfl,
        show sndA F (u.1 ⬝ᵥ u.2) = (sndA F).toRingHom (u.1 ⬝ᵥ u.2) from rfl, RingHom.map_dotProduct, RingHom.map_dotProduct,
        invOf_two_eq, AlgHom.commutes, smul_dotProduct, smul_eq_mul]
      rw [show ∀ p, sndA F (pairA F 0 p) = p from fun _ => rfl, show ∀ p, sndA F (pairA F 0 p) = p from fun _ => rfl]
      rfl
  rw [e, AddChar.map_add_eq_mul, hAb _ hxK, hA2b _ ⟨a, ha0, rfl⟩]
  ring

end GlobalTheory.WeilLevel

namespace GlobalTheory.WeilLevel

theorem schA_level : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ),
    IsTotallyReal F → IsCharAF F ψ → ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin N), ∃ U : AddSubgroup (VA F N),
      IsOpen (U : Set (VA F N)) ∧ ∀ u ∈ U, inf u.1 = 0 → inf u.2 = 0 → GlobalTheory.WeilM.schr ψ u Φ = Φ := by
  intro F _ _ N _ ψ hF hψ Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    exact pure_level ψ hF hψ f g hg
  | zero =>
    exact ⟨⊤, isOpen_univ, fun u _ _ _ => by funext x; simp [GlobalTheory.WeilM.schr]⟩
  | add Φ Φ' _ _ h h' =>
    obtain ⟨U, hU, hUΦ⟩ := h
    obtain ⟨U', hU', hUΦ'⟩ := h'
    refine ⟨U ⊓ U', by rw [AddSubgroup.coe_inf]; exact hU.inter hU', fun u hu h1 h2 => ?_⟩
    funext x
    have e1 := congrFun (hUΦ u (AddSubgroup.mem_inf.mp hu).1 h1 h2) x
    have e2 := congrFun (hUΦ' u (AddSubgroup.mem_inf.mp hu).2 h1 h2) x
    simp only [GlobalTheory.WeilM.schr, Pi.add_apply] at e1 e2 ⊢
    rw [mul_add, e1, e2]
  | smul c Φ _ h =>
    obtain ⟨U, hU, hUΦ⟩ := h
    refine ⟨U, hU, fun u hu h1 h2 => ?_⟩
    funext x
    have e1 := congrFun (hUΦ u hu h1 h2) x
    simp only [GlobalTheory.WeilM.schr, Pi.smul_apply, smul_eq_mul] at e1 ⊢
    rw [mul_left_comm, e1]

end GlobalTheory.WeilLevel

end
