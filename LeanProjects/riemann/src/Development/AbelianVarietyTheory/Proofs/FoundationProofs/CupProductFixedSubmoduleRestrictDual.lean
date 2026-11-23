import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnramifiedH1CardInvariantsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedDualEvalBidualApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardKerMulCardEq

noncomputable section

namespace GlobalTheory.InertiaFixed

open ReciprocityTheory.Gal

section Gen

variable {R : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {D : Type} [Group D] [TopologicalSpace D]
  {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
  (ρ : Representation R D M) (J : Subgroup D)

def fix : Submodule R M where
  carrier := {m | ∀ σ ∈ J, ρ σ m = m}
  zero_mem' := fun σ _ => map_zero _
  add_mem' := fun {a b} ha hb σ hσ => by
    show ρ σ (a + b) = a + b
    rw [map_add, ha σ hσ, hb σ hσ]
  smul_mem' := fun c m hm σ hσ => by
    show ρ σ (c • m) = c • m
    rw [map_smul, hm σ hσ]

variable [hJ : J.Normal]

theorem fix_stable (g : D) : ∀ m ∈ fix ρ J, ρ g m ∈ fix ρ J := by
  intro m hm σ hσ
  have h1 : g⁻¹ * σ * g ∈ J := by simpa using hJ.conj_mem σ hσ g⁻¹
  have e : σ * g = g * (g⁻¹ * σ * g) := by group
  calc ρ σ (ρ g m) = ρ (σ * g) m := by rw [map_mul]; rfl
    _ = ρ (g * (g⁻¹ * σ * g)) m := by rw [e]
    _ = ρ g (ρ (g⁻¹ * σ * g) m) := by rw [map_mul]; rfl
    _ = ρ g m := by rw [hm _ h1]

def fixRep : Representation R D (fix ρ J) where
  toFun g := (ρ g).restrict (p := fix ρ J) (q := fix ρ J) (fix_stable ρ J g)
  map_one' := by
    refine LinearMap.ext fun m => Subtype.ext ?_
    show ρ 1 m = m
    rw [map_one]; rfl
  map_mul' g h := by
    refine LinearMap.ext fun m => Subtype.ext ?_
    show ρ (g * h) m = ρ g (ρ h m)
    rw [map_mul]; rfl

@[simp] theorem fixRep_apply (g : D) (m : fix ρ J) : ((fixRep ρ J g m : fix ρ J) : M) = ρ g m := rfl

theorem contAction_fixRep (h : ContAction ρ) : ContAction (fixRep ρ J) :=
  continuous_induced_rng.2 (h.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))

def resD : TDual R M →ₗ[R] TDual R (fix ρ J) where
  toFun φ := TDual.mk ((φ : M →ₗ[R] R) ∘ₗ (fix ρ J).subtype)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem resD_equiv (χ : D →* Rˣ) (g : D) (φ : TDual R M) :
    resD ρ J (twDual χ ρ g φ) = twDual χ (fixRep ρ J) g (resD ρ J φ) := rfl

theorem map_h1_mem_unramified {M' : Type} [AddCommGroup M'] [Module R M'] [TopologicalSpace M']
    [DiscreteTopology M'] (ρ' : Representation R D M') (u : M →ₗ[R] M')
    (he : ∀ g m, u (ρ g m) = ρ' g (u m)) (x : H1 ρ) (hx : x ∈ H1ur ρ J) :
    mapH1 ρ ρ' u continuous_of_discreteTopology he x ∈ H1ur ρ' J := by
  induction x using Submodule.Quotient.induction_on with | H f =>
  rw [H1ur, LinearMap.mem_ker] at hx ⊢
  change Submodule.Quotient.mk (restrictCocycles1 ρ J.subtype continuous_subtype_val f) = 0 at hx
  change Submodule.Quotient.mk (restrictCocycles1 ρ' J.subtype continuous_subtype_val
    (cocycles1MapOfEquivariant ρ ρ' u continuous_of_discreteTopology he f)) = 0
  rw [Submodule.Quotient.mk_eq_zero] at hx ⊢
  obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 hx
  refine (mem_coboundaries1 _ _).2 ⟨u m, fun σ => ?_⟩
  have e := hm σ
  change f.1 σ = ρ σ m - m at e
  change u (f.1 σ) = ρ' σ (u m) - u m
  rw [e, map_sub, he]

theorem exists_fix_of_mem_H1ur (h : ContAction ρ) (x : H1 ρ) (hx : x ∈ H1ur ρ J) :
    ∃ x' : H1 (fixRep ρ J), x' ∈ H1ur (fixRep ρ J) J ∧
      mapH1 (fixRep ρ J) ρ (fix ρ J).subtype continuous_of_discreteTopology (fun _ _ => rfl) x' = x := by
  induction x using Submodule.Quotient.induction_on with | H f =>
  rw [H1ur, LinearMap.mem_ker] at hx
  change Submodule.Quotient.mk (restrictCocycles1 ρ J.subtype continuous_subtype_val f) = 0 at hx
  rw [Submodule.Quotient.mk_eq_zero] at hx
  obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 hx
  let f' : D → M := fun g => f.1 g - (ρ g m - m)
  have hf'J : ∀ σ ∈ J, f' σ = 0 := fun σ hσ => by
    have e := hm ⟨σ, hσ⟩
    change f.1 σ = ρ σ m - m at e
    show f.1 σ - (ρ σ m - m) = 0
    rw [e, sub_self]
  have hcoc : ∀ g k, f' (g * k) = f' g + ρ g (f' k) := fun g k => by
    show f.1 (g * k) - (ρ (g * k) m - m) = f.1 g - (ρ g m - m) + ρ g (f.1 k - (ρ k m - m))
    rw [f.2.2 g k, map_mul, Module.End.mul_apply, map_sub, map_sub]
    abel
  have hfix : ∀ g, f' g ∈ fix ρ J := fun g σ hσ => by
    have h1 : g⁻¹ * σ * g ∈ J := by simpa using hJ.conj_mem σ hσ g⁻¹
    have e1 := hcoc σ g
    have e2 := hcoc g (g⁻¹ * σ * g)
    rw [hf'J σ hσ, zero_add] at e1
    rw [hf'J _ h1, map_zero, add_zero] at e2
    have : σ * g = g * (g⁻¹ * σ * g) := by group
    rw [← e1, this, e2]
  have hcont : Continuous f' :=
    f.2.1.sub ((h.comp (continuous_id.prodMk continuous_const)).sub continuous_const)
  let F : Z1 (fixRep ρ J) := ⟨fun g => ⟨f' g, hfix g⟩, continuous_induced_rng.2 hcont,
    fun g k => Subtype.ext (hcoc g k)⟩
  refine ⟨Submodule.Quotient.mk F, ?_, ?_⟩
  · rw [H1ur, LinearMap.mem_ker]
    change Submodule.Quotient.mk (restrictCocycles1 _ J.subtype continuous_subtype_val F) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    refine (mem_coboundaries1 _ _).2 ⟨0, fun σ => Subtype.ext ?_⟩
    show f' σ = ρ σ 0 - 0
    rw [hf'J σ.1 σ.2, map_zero, sub_zero]
  · change Submodule.Quotient.mk (cocycles1MapOfEquivariant _ _ _ continuous_of_discreteTopology (fun _ _ => rfl) F) =
      Submodule.Quotient.mk f
    rw [Submodule.Quotient.eq]
    refine (mem_coboundaries1 _ _).2 ⟨-m, fun g => ?_⟩
    show f' g - f.1 g = ρ g (-m) - -m
    show f.1 g - (ρ g m - m) - f.1 g = ρ g (-m) - -m
    rw [map_neg]
    abel

theorem cupProduct_fixedSubmodule_restrictDual (χ : D →* Rˣ) (h : ContAction ρ) (hN : ContAction (fixRep ρ J))
    (y : H1 (twDual χ ρ)) (x : H1 (fixRep ρ J)) :
    cupH1H1TwistedDual χ ρ (MonoidHom.id D) (h.comp' continuous_id) y
        (mapH1 (fixRep ρ J) ρ (fix ρ J).subtype continuous_of_discreteTopology (fun _ _ => rfl) x) =
      cupH1H1TwistedDual χ (fixRep ρ J) (MonoidHom.id D) (hN.comp' continuous_id)
        (mapH1 (twDual χ ρ) (twDual χ (fixRep ρ J)) (resD ρ J) continuous_of_discreteTopology
          (resD_equiv ρ J χ) y) x := by
  induction y using Submodule.Quotient.induction_on with | H y =>
  induction x using Submodule.Quotient.induction_on with | H x =>
  rfl

end Gen

theorem bijective_compr₂_iff {R A B C : Type} [CommRing R] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C] (b : A →ₗ[R] B →ₗ[R] C)
    (j : C ≃ₗ[R] R) : Function.Bijective (b.compr₂ j.toLinearMap) ↔ Function.Bijective b :=
  (LinearEquiv.congrRight (M := B) j).bijective.of_comp_iff' b

theorem mem_H1ur_of_perp {n : ℕ} [NeZero n] {D : Type} [Group D] [TopologicalSpace D]
    {M : Type} [AddCommGroup M] [Module (ZMod n) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (χ : D →* (ZMod n)ˣ) (ρ : Representation (ZMod n) D M) (h : ContAction ρ) (J : Subgroup D)
    (inv : H2 ((charRep χ).comp (MonoidHom.id D)) ≃ₗ[ZMod n] ZMod n)
    [Finite (H1 (ρ.comp (MonoidHom.id D)))] [Finite (H1 ((twDual χ ρ).comp (MonoidHom.id D)))]
    [Finite (H0 ((twDual χ ρ).comp (MonoidHom.id D)))]
    (hb : Function.Bijective (cupH1H1TwistedDual χ ρ (MonoidHom.id D) (h.comp' continuous_id)))
    (hbf : Function.Bijective (cupH1H1TwistedDual χ ρ (MonoidHom.id D) (h.comp' continuous_id)).flip)
    (h20 : Function.Bijective (cup20 χ ρ (MonoidHom.id D)))
    (hE : Nat.card (H1 ρ) = Nat.card (H0 ρ) * Nat.card (H2 ρ))
    (hLc : Nat.card (H1ur ρ J) = Nat.card (H0 ρ))
    (hU : Nat.card (H1ur (twDual χ ρ) J) = Nat.card (H0 (twDual χ ρ)))
    (orth : ∀ y ∈ H1ur (twDual χ ρ) J, ∀ x ∈ H1ur ρ J,
      cupH1H1TwistedDual χ ρ (MonoidHom.id D) (h.comp' continuous_id) y x = 0)
    (y : H1 (twDual χ ρ))
    (hy : ∀ x ∈ H1ur ρ J, cupH1H1TwistedDual χ ρ (MonoidHom.id D) (h.comp' continuous_id) y x = 0) :
    y ∈ H1ur (twDual χ ρ) J := by
  classical
  let cup := cupH1H1TwistedDual χ ρ (MonoidHom.id D) (h.comp' continuous_id)
  let L := H1ur ρ J
  let P : Submodule (ZMod n) (H1 ((twDual χ ρ).comp (MonoidHom.id D))) :=
    ⨅ x ∈ L, LinearMap.ker (cup.flip x)
  have memP : ∀ z, z ∈ P ↔ ∀ x ∈ L, cup z x = 0 := fun z => by
    simp only [P, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.flip_apply]
  let b := cup.compr₂ inv.toLinearMap
  have hbb : Function.Bijective b := (bijective_compr₂_iff cup inv).2 hb
  let bL := b.compl₂ (L.subtype : L →ₗ[ZMod n] H1 (ρ.comp (MonoidHom.id D)))
  have hk := GlobalTheory.ZModDual.card_ker_mul_card_eq n _ L bL
  have hkP : LinearMap.ker bL = P := by
    ext z
    rw [LinearMap.mem_ker, memP]
    constructor
    · intro hz x hx
      have := LinearMap.congr_fun hz ⟨x, hx⟩
      exact inv.map_eq_zero_iff.1 this
    · intro hz
      refine LinearMap.ext fun x => ?_
      show inv (cup z x.1) = 0
      rw [hz x.1 x.2, map_zero]
  have hk1 : Nat.card (LinearMap.ker bL.flip) = 1 := by
    have hz : ∀ a : LinearMap.ker bL.flip, a = 0 := fun a => by
      have ha := LinearMap.mem_ker.1 a.2
      have h0 : cup.flip a.1.1 = 0 := LinearMap.ext fun z => by
        have := LinearMap.congr_fun ha z
        exact inv.map_eq_zero_iff.1 this
      have h1 : a.1.1 = 0 := hbf.1 (h0.trans (map_zero _).symm)
      exact Subtype.ext (Subtype.ext h1)
    refine Nat.card_eq_one_iff_unique.2 ⟨⟨fun a c => by rw [hz a, hz c]⟩, ⟨0⟩⟩
  rw [hkP, hk1, one_mul] at hk
  have hY : Nat.card (H1 ((twDual χ ρ).comp (MonoidHom.id D))) =
      Nat.card (H1 (ρ.comp (MonoidHom.id D))) :=
    (Nat.card_eq_of_bijective b hbb).trans (GlobalTheory.ZModDual.card_dual_eq n _)
  have h2 : Nat.card (H2 (ρ.comp (MonoidHom.id D))) =
      Nat.card (H0 ((twDual χ ρ).comp (MonoidHom.id D))) :=
    (Nat.card_eq_of_bijective _ ((bijective_compr₂_iff _ inv).2 h20)).trans
      (GlobalTheory.ZModDual.card_dual_eq n _)
  have hpos : 0 < Nat.card (H0 ρ) := Nat.card_pos
  have hcard : Nat.card P = Nat.card (H1ur (twDual χ ρ) J) := by
    rw [hU]
    have e : Nat.card P * Nat.card (H0 ρ) = Nat.card (H0 (twDual χ ρ)) * Nat.card (H0 ρ) :=
      calc Nat.card P * Nat.card (H0 ρ) = Nat.card P * Nat.card L := by rw [hLc]
        _ = Nat.card (H1 ((twDual χ ρ).comp (MonoidHom.id D))) := hk
        _ = Nat.card (H1 (ρ.comp (MonoidHom.id D))) := hY
        _ = Nat.card (H0 ρ) * Nat.card (H2 ρ) := hE
        _ = Nat.card (H0 (twDual χ ρ)) * Nat.card (H0 ρ) := by
          rw [mul_comm]; exact congrArg (· * Nat.card (H0 ρ)) h2
    exact Nat.eq_of_mul_eq_mul_right hpos e
  have hUP : H1ur (twDual χ ρ) J ≤ P := fun z hz => (memP z).2 (fun x hx => orth z hz x hx)
  haveI : Finite P := Subtype.finite
  obtain ⟨u, hu⟩ := (Function.Injective.bijective_of_nat_card_le
    (Submodule.inclusion_injective hUP) hcard.le).2 ⟨y, (memP y).2 hy⟩
  have e := congrArg Subtype.val hu
  change (u : H1 ((twDual χ ρ).comp (MonoidHom.id D))) = y at e
  rw [← e]
  exact u.2

end GlobalTheory.InertiaFixed

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem unramified_h1_dual_iff_perp : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) (ρ : Representation (ZMod (l ^ r)) (Dec (F := F) A) M) (hρ : ContAction ρ), IsPlaceOver A v → 0 < r → ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → ∀ y : H1 (twDual ((cycMod F Ω l r).comp (Dec (F := F) A).subtype) ρ), y ∈ H1ur (twDual ((cycMod F Ω l r).comp (Dec (F := F) A).subtype) ρ) ((Ine (F := F) A).subgroupOf (Dec (F := F) A)) ↔ ∀ x ∈ H1ur ρ ((Ine (F := F) A).subgroupOf (Dec (F := F) A)), cupH1H1TwistedDual ((cycMod F Ω l r).comp (Dec (F := F) A).subtype) ρ (MonoidHom.id _) (hρ.comp' continuous_id) y x = 0 := by
  intro hL F Ω _ _ _ _ _ l _ r M _ _ _ _ _ A v ρ hρ hA hr hl y
  classical
  set χ := (cycMod F Ω l r).comp (Dec (F := F) A).subtype with hχdef
  set J := (Ine (F := F) A).subgroupOf (Dec (F := F) A) with hJdef
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  haveI : Finite (TDual (ZMod (l ^ r)) M) := GlobalTheory.DualSide.finite_TDual
  have hχ : ContAction (charRep χ) :=
    (((Units.continuous_val.comp GlobalTheory.Published.PoitouTate.continuous_cycMod).comp
      continuous_subtype_val).comp continuous_fst).mul continuous_snd
  have hρ' : ContAction (twDual χ ρ) := GlobalTheory.DualSide.contAction_twDual hχ hρ
  have orth : ∀ y ∈ H1ur (twDual χ ρ) J, ∀ x ∈ H1ur ρ J,
      cupH1H1TwistedDual χ ρ (MonoidHom.id _) (hρ.comp' continuous_id) y x = 0 := by
    intro y hy x hx
    obtain ⟨x', hx', rfl⟩ := GlobalTheory.InertiaFixed.exists_fix_of_mem_H1ur ρ J hρ x hx
    have hN := GlobalTheory.InertiaFixed.contAction_fixRep ρ J hρ
    rw [GlobalTheory.InertiaFixed.cupProduct_fixedSubmodule_restrictDual ρ J χ hρ hN]
    have uo := hL.uo F Ω l r (GlobalTheory.InertiaFixed.fix ρ J) A (GlobalTheory.InertiaFixed.fixRep ρ J) v hr hA hl
      (fun σ hσ => LinearMap.ext fun m => Subtype.ext (m.2 σ (Subgroup.mem_subgroupOf.2 hσ))) hN
    exact (uo.2 _).1 (GlobalTheory.InertiaFixed.map_h1_mem_unramified _ J _ _ _ y hy) x' hx'
  refine ⟨fun hy x hx => orth _ hy x hx, fun hy => ?_⟩
  obtain ⟨-, hfin1, -, -⟩ := hL.lf F Ω l r M A ρ v hr hA hρ
  have hfin0' := (hL.lf F Ω l r _ A (twDual χ ρ) v hr hA hρ').1
  have hfin1' := (hL.lf F Ω l r _ A (twDual χ ρ) v hr hA hρ').2.1
  obtain ⟨⟨inv⟩, -, hb, hbf, h20⟩ := hL.lt F Ω l r M A ρ v hr hA hρ
  haveI : Finite (H1 (ρ.comp (MonoidHom.id _))) := hfin1
  haveI : Finite (H1 ((twDual χ ρ).comp (MonoidHom.id _))) := hfin1'
  haveI : Finite (H0 ((twDual χ ρ).comp (MonoidHom.id _))) := hfin0'
  exact GlobalTheory.InertiaFixed.mem_H1ur_of_perp χ ρ hρ J inv hb hbf h20
    ((hL.le F Ω l r M A ρ v hr hA hρ).2 hl) (GlobalTheory.T.unramified_h1_card_invariants F Ω l r M A v ρ hρ hA)
    (GlobalTheory.T.unramified_h1_card_invariants F Ω l r (TDual (ZMod (l ^ r)) M) A v (twDual χ ρ) hρ' hA) orth _ hy

end GlobalTheory.Ord2
