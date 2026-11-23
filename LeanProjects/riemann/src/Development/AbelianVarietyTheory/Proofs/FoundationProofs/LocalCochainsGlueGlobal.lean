import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCyclotomicBlockCocyclesLeSha
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormLeOne

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.TwistTriv

variable {l : ℕ} [Fact l.Prime]

instance neZero_pow (n : ℕ) : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩

theorem norm_algebraMap_padicInt (a : ℤ_[l]) : ‖algebraMap ℤ_[l] (Qbar l) a‖ = ‖a‖ := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), norm_algebraMap']
  rfl

theorem norm_le_one (c : Coef l) (x : c.O) : ‖(x : Qbar l)‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.ScalarNormBound.norm_le_one
  | exact _root_.GlobalTheory.ScalarNormBound.norm_le_one
  | (apply _root_.GlobalTheory.ScalarNormBound.norm_le_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.ScalarNormBound.norm_le_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ScalarNormBound.norm_le_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ScalarNormBound.norm_le_one ..)

def nbhd (c : Coef l) (n : ℕ) : AddSubgroup c.O where
  carrier := {x | ‖(x : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖}
  zero_mem' := by
    show ‖((0 : c.O) : Qbar l)‖ ≤ _
    simp
  add_mem' {a b} ha hb := by
    show ‖(a : Qbar l) + b‖ ≤ _
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  neg_mem' {a} ha := by
    show ‖-(a : Qbar l)‖ ≤ _
    rw [norm_neg]; exact ha

theorem mem_nbhd {c : Coef l} {n : ℕ} {x : c.O} :
    x ∈ nbhd c n ↔ ‖(x : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ := Iff.rfl

def Red (c : Coef l) (n : ℕ) : Type := c.O ⧸ nbhd c n

instance (c : Coef l) (n : ℕ) : AddCommGroup (Red c n) := inferInstanceAs (AddCommGroup (c.O ⧸ nbhd c n))
instance (c : Coef l) (n : ℕ) : TopologicalSpace (Red c n) := ⊥
instance (c : Coef l) (n : ℕ) : DiscreteTopology (Red c n) := ⟨rfl⟩

def red (c : Coef l) (n : ℕ) : c.O →+ Red c n := QuotientAddGroup.mk' (nbhd c n)

theorem red_surjective (c : Coef l) (n : ℕ) : Function.Surjective (red c n) :=
  QuotientAddGroup.mk'_surjective _

theorem red_eq_zero_iff {c : Coef l} {n : ℕ} (x : c.O) : red c n x = 0 ↔ x ∈ nbhd c n :=
  QuotientAddGroup.eq_zero_iff x

theorem red_eq_iff (c : Coef l) (n : ℕ) (a b : c.O) :
    red c n a = red c n b ↔ Cg n (a : Qbar l) (b : Qbar l) := by
  rw [← sub_eq_zero, ← map_sub, red_eq_zero_iff]
  exact Iff.rfl

theorem cg_symm {n : ℕ} {a b : Qbar l} (h : Cg n a b) : Cg n b a := by
  unfold Cg at *; rwa [norm_sub_rev]

theorem cg_refl (n : ℕ) (a : Qbar l) : Cg n a a := by
  unfold Cg; rw [sub_self, norm_zero]; exact norm_nonneg _

theorem smul_mem_nbhd (c : Coef l) (n : ℕ) {a : ℤ_[l]} (ha : a ∈ Ideal.span {(l : ℤ_[l]) ^ n})
    (y : c.O) : a • y ∈ nbhd c n := by
  obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 ha
  rw [mem_nbhd, Subalgebra.coe_smul, Algebra.smul_def, norm_mul, map_mul, norm_mul, map_pow, map_natCast]
  have h1 : ‖algebraMap ℤ_[l] (Qbar l) w‖ ≤ 1 :=
    (norm_algebraMap_padicInt w).le.trans (PadicInt.norm_le_one w)
  have h2 := norm_le_one c y
  calc _ ≤ 1 * ‖((l : ℕ) : Qbar l) ^ n‖ * 1 := by gcongr
    _ = _ := by ring

theorem red_smul (c : Coef l) (n : ℕ) (a : ℤ_[l]) (y : c.O) :
    red c n (a • y) = (PadicInt.toZModPow n a).val • red c n y := by
  rw [← map_nsmul, ← sub_eq_zero, ← map_sub, red_eq_zero_iff]
  have e : a • y - (PadicInt.toZModPow n a).val • y =
      (a - ((PadicInt.toZModPow n a).val : ℤ_[l])) • y := by
    rw [sub_smul, Nat.cast_smul_eq_nsmul]
  rw [e]
  refine smul_mem_nbhd c n ?_ y
  rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]

theorem kill (c : Coef l) (n : ℕ) (y : Red c n) : (l ^ n) • y = 0 := by
  obtain ⟨x, rfl⟩ := red_surjective c n y
  rw [← map_nsmul, red_eq_zero_iff, ← Nat.cast_smul_eq_nsmul ℤ_[l], Nat.cast_pow]
  exact smul_mem_nbhd c n (Ideal.mem_span_singleton_self _) x

instance (c : Coef l) (n : ℕ) : Module (ZMod (l ^ n)) (Red c n) := AddCommGroup.zmodModule (kill c n)

instance (c : Coef l) (n : ℕ) : Finite (Red c n) := by
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin (R := ℤ_[l]) (M := c.O)
  refine Finite.of_surjective (fun z : Fin k → ZMod (l ^ n) => ∑ i, (z i).val • red c n (s i)) ?_
  intro y
  obtain ⟨x, rfl⟩ := red_surjective c n y
  have hx : x ∈ Submodule.span ℤ_[l] (Set.range s) := hs ▸ Submodule.mem_top
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ_[l]).1 hx
  refine ⟨fun i => PadicInt.toZModPow n (a i), ?_⟩
  show ∑ i, _ = _
  rw [← ha, map_sum]
  exact Finset.sum_congr rfl fun i _ => (red_smul c n (a i) (s i)).symm

theorem continuous_red_comp {X : Type*} [TopologicalSpace X] (c : Coef l) (n : ℕ) (f : X → c.O)
    (hf : Continuous fun x => (f x : Qbar l)) : Continuous fun x => red c n (f x) := by
  refine continuous_discrete_rng.2 fun y => ?_
  obtain ⟨z, rfl⟩ := red_surjective c n y
  have e : (fun x => red c n (f x)) ⁻¹' {red c n z} =
      (fun x => (f x : Qbar l)) ⁻¹' Metric.closedBall (z : Qbar l) ‖((l : ℕ) : Qbar l) ^ n‖ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Metric.mem_closedBall, dist_eq_norm]
    exact red_eq_iff c n (f x) z
  rw [e]
  have hne : ‖((l : ℕ) : Qbar l) ^ n‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  exact (IsUltrametricDist.isOpen_closedBall _ hne).preimage hf

def rho (c : Coef l) (n : ℕ) {Γ : Type*} [Group Γ] (μ : Γ →* (ZMod (l ^ n))ˣ) :
    Representation (ZMod (l ^ n)) Γ (Red c n) where
  toFun g := ((μ g : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) • LinearMap.id
  map_one' := by ext y; simp
  map_mul' g h := by ext y; simp [mul_smul]; exact smul_comm _ _ _

theorem rho_apply (c : Coef l) (n : ℕ) {Γ : Type*} [Group Γ] (μ : Γ →* (ZMod (l ^ n))ˣ) (g : Γ)
    (y : Red c n) : rho c n μ g y = ((μ g : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)).val • y := by
  show ((μ g : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) • y = _
  conv_lhs => rw [← ZMod.natCast_zmod_val ((μ g : (ZMod (l ^ n))ˣ) : ZMod (l ^ n))]
  exact Nat.cast_smul_eq_nsmul _ _ _

theorem contAction_rho (c : Coef l) (n : ℕ) {Γ : Type*} [Group Γ] [TopologicalSpace Γ]
    (μ : Γ →* (ZMod (l ^ n))ˣ) (hμ : Continuous μ) : ReciprocityTheory.Gal.ContAction (rho c n μ) := by
  have e : (fun p : Γ × Red c n => rho c n μ p.1 p.2) =
      (fun q : ZMod (l ^ n) × Red c n => q.1 • q.2) ∘
        (fun p : Γ × Red c n => (((μ p.1 : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)), p.2)) := rfl
  unfold ReciprocityTheory.Gal.ContAction
  rw [e]
  exact continuous_of_discreteTopology.comp
    (((Units.continuous_val.comp hμ).comp continuous_fst).prodMk continuous_snd)

end GlobalTheory.Ord2.TwistTriv

namespace GlobalTheory.Ord2.TwistTriv

theorem hom_eq_zero {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (S : Finset Pl)
    (Av : S → ValuationSubring Ω) (hAv : ∀ v, IsPlaceOver (Av v) v.1)
    {A : Type*} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    (f : G ℚ Ω → A) (hc : Continuous f) (hm : ∀ s t, f (s * t) = f s + f t)
    (hN : ∀ a ∈ NS Ω (S : Set Pl), f a = 0)
    (hD : ∀ v : S, ∀ g ∈ Dec (F := ℚ) (Av v), f g = 0) (s : G ℚ Ω) : f s = 0 := by
  have h1 : f 1 = 0 := by
    have := hm 1 1
    rw [mul_one] at this
    exact (add_eq_left.1 this.symm)
  have hinv : ∀ g, f g⁻¹ = - f g := fun g => by
    have := hm g⁻¹ g
    rw [inv_mul_cancel, h1] at this
    exact eq_neg_of_add_eq_zero_left this.symm
  have hconj : ∀ g x, f (g⁻¹ * x * g) = f x := fun g x => by
    rw [hm, hm, hinv]; abel
  let V : Subgroup (G ℚ Ω) :=
    { carrier := {g | f g = 0}
      one_mem' := h1
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at *; rw [hm, ha, hb, add_zero]
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at *; rw [hinv, ha, neg_zero] }
  have hV : IsOpen (V : Set (G ℚ Ω)) := (isOpen_discrete ({0} : Set A)).preimage hc
  have key := UpperTheory.V.CF.minkAbs Ω V hV ?_
  · have hs : s ∈ V := key ▸ Subgroup.mem_top s
    exact hs
  intro B x hx
  obtain ⟨h0, h2, -, -⟩ := UpperTheory.V.Kum.placeDict ℚ Ω
  by_cases hB : B = ⊤
  · subst hB
    rw [h0] at hx
    rw [Subgroup.mem_bot.1 hx]
    exact V.one_mem
  obtain ⟨w, hw⟩ := h2 B hB
  by_cases hwS : w ∈ S
  · obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver (hAv ⟨w, hwS⟩) hw
    subst hσ
    have hc' := GlobalTheory.Cut.ShaBound.conj_mem_Ine' hx
    show f x = 0
    rw [← hconj σ x]
    exact hD _ _ (Ine_le_Dec _ hc')
  · show f x = 0
    apply hN
    apply Subgroup.le_topologicalClosure
    apply Subgroup.subset_normalClosure
    simp only [Set.mem_iUnion]
    exact ⟨w, by simpa using hwS, B, hw, hx⟩

end GlobalTheory.Ord2.TwistTriv

namespace GlobalTheory.Ord2.TwistTriv

open GlobalTheory.Published GlobalTheory.Published.PoitouTate

theorem coboundary_of_locTriv : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    [IsAlgClosure ℚ Ω] (c : Coef l) (n : ℕ) (S : Finset Pl) (ξ : G ℚ Ω → G ℚ Ω → Qbar l), l ≠ 2 →
    ContainsAbove S l → Coc2 c n S ξ →
    (∀ v ∈ S, ∃ B : ValuationSubring Ω, IsPlaceOver B v ∧ Cob2 c n (Dec (F := ℚ) B) ξ) →
    ∃ u : G ℚ Ω → Qbar l, Continuous u ∧ (∀ s, u s ∈ c.O) ∧
      (∀ s, ∀ a ∈ (toGS Ω (S : Set Pl)).ker, Cg n (u (s * a)) (u s)) ∧
      ∀ s t, Cg n (ξ s t) (eps l s * u t - u (s * t) + u s) := by
  intro hlit l _ Ω _ _ _ c n S ξ hl2 hS hξ hloc
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨0, continuous_const, fun _ => c.O.zero_mem, fun s _ _ => cg_refl 0 _, fun s t => ?_⟩
    show ‖ξ s t - (eps l s * 0 - 0 + 0)‖ ≤ ‖((l : ℕ) : Qbar l) ^ 0‖
    rw [mul_zero, sub_zero, add_zero, sub_zero, pow_zero, norm_one]
    exact norm_le_one c ⟨ξ s t, hξ.int s t⟩
  classical
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_pow ℚ Ω l n
  obtain ⟨inv, -, hPT⟩ := hlit.pt ℚ Ω l n (Or.inl hl2) hn ζ hζ
  obtain ⟨μ, hμ⟩ := exists_lift_cycMod (F := ℚ) (Ω := Ω) (r := n) hS
  choose Bv hBv hCob using hloc
  set Av : S → ValuationSubring Ω := fun v => Bv v.1 v.2 with hAvdef
  have hAv : ∀ v : S, IsPlaceOver (Av v) v.1 := fun v => hBv v.1 v.2
  have hμc : Continuous μ := by
    rw [(QuotientGroup.isQuotientMap_mk _).continuous_iff]
    have e : (μ ∘ QuotientGroup.mk : G ℚ Ω → _) = cycMod ℚ Ω l n := by rw [← hμ]; rfl
    rw [e]; exact continuous_cycMod
  have hρ := contAction_rho c n μ hμc
  obtain ⟨-, ⟨⟨-, -, -, hcard⟩, -⟩, -⟩ := hPT S hS Av hAv μ hμ (Red c n) (rho c n μ) hρ
  have hsurj : Function.Surjective (toGS Ω (S : Set Pl)) := QuotientGroup.mk'_surjective _

  have heps : ∀ s (y : c.O), (((cycZ ℚ Ω l s : ℤ_[l]) • y : c.O) : Qbar l) = eps l s * y := by
    intro s y
    rw [Subalgebra.coe_smul, Algebra.smul_def, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)]
    rfl
  have hrho : ∀ s (y : c.O), rho c n μ (toGS Ω (S : Set Pl) s) (red c n y) =
      red c n ((cycZ ℚ Ω l s : ℤ_[l]) • y) := by
    intro s y
    rw [rho_apply, red_smul]
    have e := congrArg (fun u : (ZMod (l ^ n))ˣ => (u : ZMod (l ^ n))) (DFunLike.congr_fun hμ s)
    simp only [MonoidHom.coe_comp, Function.comp_apply] at e
    rw [e]
    rfl

  have htriv : ∀ g (φ : TDual (ZMod (l ^ n)) (Red c n)), twDual μ (rho c n μ) g φ = φ := by
    intro g φ
    ext m
    have hφ : ∀ (a : ZMod (l ^ n)) (m : Red c n), φ (a • m) = a * φ m := fun a m =>
      LinearMap.map_smul (φ : Module.Dual (ZMod (l ^ n)) (Red c n)) a m
    rw [twDual_apply]
    show ((μ g : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) * φ (((μ g⁻¹ : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) • m) = φ m
    rw [hφ, ← mul_assoc, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one,
      Units.val_one, one_mul]
  have hsha1 : ∀ x ∈ Sha1 (twDual μ (rho c n μ)) (locFam S Av) (continuous_locFam S Av), x = 0 := by
    intro x hx
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [Submodule.Quotient.mk_eq_zero]
    have hadd : ∀ g h, f.1 (g * h) = f.1 g + f.1 h := fun g h => by rw [f.2.2 g h, htriv]
    have h1 : f.1 1 = 0 := by
      have := hadd 1 1
      rw [mul_one] at this
      exact add_eq_left.1 this.symm
    have hD : ∀ v : S, ∀ g ∈ Dec (F := ℚ) (Av v), f.1 (toGS Ω (S : Set Pl) g) = 0 := by
      intro v g hg
      have hv := (Submodule.mem_iInf _).1 hx v
      rw [LinearMap.mem_ker, resH1, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hv
      obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 (Submodule.mem_comap.1 hv)
      have e := hm ⟨g, hg⟩
      simp only [Submodule.coe_subtype, restrictCocycles1_apply, MonoidHom.coe_comp, Function.comp_apply, htriv,
        sub_self] at e
      exact e
    have hzero := hom_eq_zero S Av hAv (fun s => f.1 (toGS Ω (S : Set Pl) s))
      (f.2.1.comp (continuous_toGS Ω _)) (fun s t => by rw [map_mul, hadd])
      (fun a ha => by
        have e : toGS Ω (S : Set Pl) a = 1 := (QuotientGroup.eq_one_iff a).2 ha
        show f.1 (toGS Ω (S : Set Pl) a) = 0
        rw [e]
        exact h1) hD
    have hf : f.1 = 0 := funext fun y => by
      obtain ⟨s, rfl⟩ := hsurj y
      exact hzero s
    show f.1 ∈ B1 _
    rw [hf]
    exact (B1 _).zero_mem
  have hone : Nat.card (Sha1 (twDual μ (rho c n μ)) (locFam S Av) (continuous_locFam S Av)) = 1 :=
    Nat.card_eq_one_iff_unique.2
      ⟨⟨fun a b => Subtype.ext ((hsha1 a a.2).trans (hsha1 b b.2).symm)⟩, ⟨0⟩⟩
  have hsub : Subsingleton (Sha2 (rho c n μ) (locFam S Av) (continuous_locFam S Av)) :=
    (Nat.card_eq_one_iff_unique.1 (hcard ▸ hone)).1

  let sec := Function.surjInv hsurj
  have hsec : ∀ x, toGS Ω (S : Set Pl) (sec x) = x := Function.surjInv_eq hsurj
  let xi : G ℚ Ω → G ℚ Ω → c.O := fun s t => ⟨ξ s t, hξ.int s t⟩
  let xb : GS Ω (S : Set Pl) × GS Ω (S : Set Pl) → Red c n := fun p => red c n (xi (sec p.1) (sec p.2))
  have hxb : ∀ s t, xb (toGS Ω (S : Set Pl) s, toGS Ω (S : Set Pl) t) = red c n (xi s t) := by
    intro s t
    have ha : s⁻¹ * sec (toGS Ω (S : Set Pl) s) ∈ (toGS Ω (S : Set Pl)).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hsec, inv_mul_cancel]
    have hb : t⁻¹ * sec (toGS Ω (S : Set Pl) t) ∈ (toGS Ω (S : Set Pl)).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hsec, inv_mul_cancel]
    have e := hξ.unr s t _ ha _ hb
    rw [mul_inv_cancel_left, mul_inv_cancel_left] at e
    exact (red_eq_iff c n (xi _ _) (xi s t)).2 e
  have hcont : Continuous xb := by
    have hq0 : IsOpenQuotientMap (toGS Ω (S : Set Pl)) := QuotientGroup.isOpenQuotientMap_mk
    have hq : Topology.IsQuotientMap (Prod.map (toGS Ω (S : Set Pl)) (toGS Ω (S : Set Pl))) :=
      (hq0.prodMap hq0).isQuotientMap
    rw [hq.continuous_iff]
    have e : xb ∘ Prod.map (toGS Ω (S : Set Pl)) (toGS Ω (S : Set Pl)) =
        fun p : G ℚ Ω × G ℚ Ω => red c n (xi p.1 p.2) := funext fun p => hxb p.1 p.2
    rw [e]
    exact continuous_red_comp c n (fun p : G ℚ Ω × G ℚ Ω => xi p.1 p.2) hξ.cont
  have hz : xb ∈ Z2 (rho c n μ) := by
    refine ⟨hcont, fun g h k => ?_⟩
    obtain ⟨r, rfl⟩ := hsurj g
    obtain ⟨s, rfl⟩ := hsurj h
    obtain ⟨t, rfl⟩ := hsurj k
    rw [← map_mul, ← map_mul, hxb, hxb, hxb, hxb, hrho]
    have e : red c n ((cycZ ℚ Ω l r : ℤ_[l]) • xi s t) - red c n (xi (r * s) t) + red c n (xi r (s * t)) -
        red c n (xi r s) = red c n ((cycZ ℚ Ω l r : ℤ_[l]) • xi s t + xi r (s * t)) -
          red c n (xi (r * s) t + xi r s) := by
      simp only [map_add]; abel
    rw [e, sub_eq_zero, red_eq_iff]
    show Cg n ((((cycZ ℚ Ω l r : ℤ_[l]) • xi s t : c.O) : Qbar l) + ξ r (s * t)) (ξ (r * s) t + ξ r s)
    rw [heps]
    exact hξ.coc r s t
  have hsha2 : (Submodule.Quotient.mk ⟨xb, hz⟩ : H2 (rho c n μ)) ∈
      Sha2 (rho c n μ) (locFam S Av) (continuous_locFam S Av) := by
    refine (Submodule.mem_iInf _).2 fun v => ?_
    rw [LinearMap.mem_ker, resH2, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]
    refine Submodule.mem_comap.2 ((separated_dvr_second_cohomology_mem _ _).2 ?_)
    obtain ⟨u, hu, huO, hcg⟩ := hCob v.1 v.2
    refine ⟨fun g => red c n ⟨u g, huO g⟩,
      continuous_red_comp c n (fun g : Dec (F := ℚ) (Av v) => (⟨u g, huO g⟩ : c.O))
        (continuousOn_iff_continuous_restrict.1 hu), ?_⟩
    funext p
    obtain ⟨g, h⟩ := p
    show rho c n μ (toGS Ω (S : Set Pl) g) (red c n ⟨u h, huO h⟩) - red c n ⟨u (g * h), huO _⟩ +
      red c n ⟨u g, huO g⟩ = xb (toGS Ω (S : Set Pl) g, toGS Ω (S : Set Pl) h)
    rw [hxb, hrho, ← map_sub, ← map_add, red_eq_iff]
    show Cg n ((((cycZ ℚ Ω l g : ℤ_[l]) • (⟨u h, huO h⟩ : c.O) : c.O) : Qbar l) - u (g * h) + u g) (ξ g h)
    rw [heps]
    exact cg_symm (hcg g g.2 h h.2)
  have h0 : (Submodule.Quotient.mk ⟨xb, hz⟩ : H2 (rho c n μ)) = 0 :=
    congrArg Subtype.val (Subsingleton.elim
      (⟨_, hsha2⟩ : Sha2 (rho c n μ) (locFam S Av) (continuous_locFam S Av)) ⟨0, zero_mem _⟩)
  rw [Submodule.Quotient.mk_eq_zero] at h0
  obtain ⟨cc, hcc, hd⟩ := (separated_dvr_second_cohomology_mem _ _).1 (Submodule.mem_comap.1 h0)

  have hrs := red_surjective c n
  obtain ⟨U, hUc, hUa, hU⟩ : ∃ U : G ℚ Ω → c.O, Continuous (fun s => (U s : Qbar l)) ∧
      (∀ s, ∀ a ∈ (toGS Ω (S : Set Pl)).ker, U (s * a) = U s) ∧
      ∀ s, red c n (U s) = cc (toGS Ω (S : Set Pl) s) := by
    refine ⟨fun s => Function.surjInv hrs (cc (toGS Ω (S : Set Pl) s)), ?_, fun s a ha => ?_,
      fun s => Function.surjInv_eq hrs _⟩
    · exact (continuous_of_discreteTopology (f := fun y : Red c n => ((Function.surjInv hrs y : c.O) : Qbar l))).comp
        (hcc.comp (continuous_toGS Ω _))
    · show Function.surjInv hrs (cc (toGS Ω (S : Set Pl) (s * a))) = _
      rw [map_mul, (MonoidHom.mem_ker).1 ha, mul_one]
  refine ⟨fun s => (U s : Qbar l), hUc, fun s => (U s).2, fun s a ha => ?_, fun s t => ?_⟩
  · show Cg n ((U (s * a) : c.O) : Qbar l) (U s)
    rw [hUa s a ha]
    exact cg_refl n _
  · have h1 := congrFun hd (toGS Ω (S : Set Pl) s, toGS Ω (S : Set Pl) t)
    simp only [d1_apply, Submodule.coe_subtype] at h1
    have key : red c n (xi s t) = red c n ((cycZ ℚ Ω l s : ℤ_[l]) • U t - U (s * t) + U s) := by
      rw [map_add, map_sub, ← hrho, hU, hU, hU, map_mul, ← hxb]
      exact h1.symm
    have e := (red_eq_iff c n _ _).1 key
    show Cg n (ξ s t) (eps l s * (U t : Qbar l) - U (s * t) + U s)
    rw [← heps]
    exact e

end GlobalTheory.Ord2.TwistTriv
