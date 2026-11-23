import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoDualGen
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoAdicCont
import ReciprocityTheory.Hypotheses.GalCoh
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.LocCharPerfect

open UpperTheory.V.X

variable {l : ℕ} [Fact l.Prime]

theorem lev_kill (c : Coef l) (n : ℕ) (m : Lev ((l : c.O) ^ n)) : (l ^ n) • m = 0 := by
  obtain ⟨x, rfl⟩ := Lev.mk_surjective _ m
  rw [← map_nsmul, Lev.mk_eq_zero, nsmul_eq_mul, Nat.cast_pow]
  exact dvd_mul_right _ _

def levZMod (c : Coef l) (n : ℕ) : Module (ZMod (l ^ n)) (Lev ((l : c.O) ^ n)) :=
  AddCommGroup.zmodModule (lev_kill c n)

attribute [local instance] levZMod

theorem smul_eq_zero_of_dvd (c : Coef l) (n : ℕ) {d : c.O} (h : (l : c.O) ^ n ∣ d)
    (m : Lev ((l : c.O) ^ n)) : d • m = 0 := by
  obtain ⟨x, rfl⟩ := Lev.mk_surjective _ m
  rw [← map_smul, Lev.mk_eq_zero, smul_eq_mul]
  exact h.mul_right _

theorem lev_sub_smul (c : Coef l) (n : ℕ) (x y : c.O) (m : Lev ((l : c.O) ^ n)) :
    (x - y) • m = x • m - y • m := sub_smul x y m

theorem smul_congr (c : Coef l) (n : ℕ) {x y : c.O} (h : (l : c.O) ^ n ∣ x - y)
    (m : Lev ((l : c.O) ^ n)) : x • m = y • m := by
  rw [← sub_eq_zero, ← sub_smul]
  exact smul_eq_zero_of_dvd c n h m

theorem zmod_smul (c : Coef l) (n : ℕ) [NeZero (l ^ n)] (a : ZMod (l ^ n)) (m : Lev ((l : c.O) ^ n)) :
    a • m = ((a.val : ℕ) : c.O) • m := by
  conv_lhs => rw [← ZMod.natCast_zmod_val a]
  rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]

theorem padic_smul (c : Coef l) (n : ℕ) [NeZero (l ^ n)] (z : ℤ_[l]) (m : Lev ((l : c.O) ^ n)) :
    algebraMap ℤ_[l] c.O z • m = PadicInt.toZModPow n z • m := by
  rw [zmod_smul]
  refine smul_congr c n ?_ m
  have hk : z - (((PadicInt.toZModPow n z).val : ℕ) : ℤ_[l]) ∈ Ideal.span {(l : ℤ_[l]) ^ n} := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hk
  refine ⟨algebraMap ℤ_[l] c.O t, ?_⟩
  rw [← map_natCast (algebraMap ℤ_[l] c.O), ← map_sub, ← ht, map_mul, map_pow, map_natCast, mul_comm]

def scal (c : Coef l) (n : ℕ) {Γ : Type} [Group Γ] (χ : Γ →* c.Oˣ) :
    Representation (ZMod (l ^ n)) Γ (Lev ((l : c.O) ^ n)) where
  toFun g := (DistribSMul.toAddMonoidHom (Lev ((l : c.O) ^ n)) ((χ g : c.Oˣ) : c.O)).toZModLinearMap (l ^ n)
  map_one' := LinearMap.ext fun m => by
    show ((χ 1 : c.Oˣ) : c.O) • m = m
    rw [map_one, Units.val_one, one_smul]
  map_mul' g h := LinearMap.ext fun m => by
    show ((χ (g * h) : c.Oˣ) : c.O) • m = ((χ g : c.Oˣ) : c.O) • ((χ h : c.Oˣ) : c.O) • m
    rw [map_mul, Units.val_mul, mul_smul]

theorem scal_apply (c : Coef l) (n : ℕ) {Γ : Type} [Group Γ] (χ : Γ →* c.Oˣ) (g : Γ) (m : Lev ((l : c.O) ^ n)) :
    scal c n χ g m = ((χ g : c.Oˣ) : c.O) • m := rfl

def smulZ (c : Coef l) (n : ℕ) (x : c.O) : Lev ((l : c.O) ^ n) →ₗ[ZMod (l ^ n)] Lev ((l : c.O) ^ n) :=
  (DistribSMul.toAddMonoidHom (Lev ((l : c.O) ^ n)) x).toZModLinearMap (l ^ n)

theorem contAction_scal (c : Coef l) {Γ : Type} [Group Γ] [TopologicalSpace Γ] (θ' : Γ →* c.Oˣ)
    (hθ' : Continuous (fun g => ((θ' g : c.Oˣ) : c.O))) (n : ℕ) (h0 : ((l : c.O) ^ n) ≠ 0) :
    ContAction (scal c n θ') := by
  refine continuous_prod_of_discrete_right.2 fun m => ?_
  obtain ⟨x, rfl⟩ := Lev.mk_surjective _ m
  refine (((UpperTheory.V.X.So.adicCont l c).1 _ h0).comp (hθ'.mul (continuous_const (y := x)))).congr fun g => ?_
  show Lev.mk ((l : c.O) ^ n) (((θ' g : c.Oˣ) : c.O) * x) = ((θ' g : c.Oˣ) : c.O) • Lev.mk ((l : c.O) ^ n) x
  rw [← smul_eq_mul, map_smul]

end GlobalTheory.Ord2.LocCharPerfect

open GlobalTheory.Ord2.LocCharPerfect UpperTheory.V.X in
attribute [local instance] levZMod in
set_option maxHeartbeats 1000000 in

theorem GlobalTheory.Ord2.LocCharPerfect.perfect : LocalFiniteness → LocalTateDuality → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (A : ValuationSubring Ω), OverL l A → ∀ θ θ' : ↥(Dec (F := ℚ) A) →* c.Oˣ, Continuous (fun g => ((θ g : c.Oˣ) : c.O)) → Continuous (fun g => ((θ' g : c.Oˣ) : c.O)) → θ * θ' = (UpperTheory.V.Base.chiO ℚ Ω l c.O).comp (Dec (F := ℚ) A).subtype → ∀ n : ℕ, 1 ≤ n → ∀ b : ↥(Dec (F := ℚ) A) → c.O, Continuous b → (∀ s t, ((l : ℕ) : c.O) ^ n ∣ b (s * t) - (b s + ((θ s : c.Oˣ) : c.O) * b t)) → (∀ a : ↥(Dec (F := ℚ) A) → c.O, Continuous a → (∀ s t, ((l : ℕ) : c.O) ^ n ∣ a (s * t) - (a s + ((θ' s : c.Oˣ) : c.O) * a t)) → ∃ u : ↥(Dec (F := ℚ) A) → c.O, Continuous u ∧ ∀ s t, ((l : ℕ) : c.O) ^ n ∣ b s * (((θ' s : c.Oˣ) : c.O) * a t) - ((((θ s : c.Oˣ) : c.O) * ((θ' s : c.Oˣ) : c.O)) * u t - u (s * t) + u s)) → ∃ x : c.O, ∀ s, ((l : ℕ) : c.O) ^ n ∣ b s - (((θ s : c.Oˣ) : c.O) * x - x) := by
  intro hF hT l _ Ω _ _ _ c A hA θ θ' hθ hθ' hθθ n hn b hb hbc hcup
  classical
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hl0 : ((l : ℕ) : c.O) ≠ 0 := by
    intro h
    have h' := congrArg (fun x : c.O => (x : PadicAlgCl l)) h
    simp only [SubringClass.coe_natCast, ZeroMemClass.coe_zero, Nat.cast_eq_zero] at h'
    exact (Fact.out : l.Prime).ne_zero h'
  have ha0 : ((l : c.O) ^ n) ≠ 0 := pow_ne_zero _ hl0
  obtain ⟨v, hv, -⟩ := hA
  haveI : Finite (Lev ((l : c.O) ^ n)) :=
    (UpperTheory.V.X.So.levFacts l c.O _ ha0 (Lev ((l : c.O) ^ n)) ⟨LinearEquiv.refl _ _⟩).1
  obtain ⟨φ₀, hφ0, hφall⟩ := UpperTheory.V.X.So.dualGen l c.O _ ha0 n (Lev ((l : c.O) ^ n)) ⟨LinearEquiv.refl _ _⟩
  set rho := scal c n θ' with hrho
  have hc : ContAction rho := contAction_scal c θ' hθ' n ha0
  set χ := (cycMod ℚ Ω l n).comp (Dec (F := ℚ) A).subtype with hχ

  have hchi : ∀ s : ↥(Dec (F := ℚ) A), ((θ s : c.Oˣ) : c.O) * ((θ' s : c.Oˣ) : c.O) =
      algebraMap ℤ_[l] c.O (cycZ ℚ Ω l (s : G ℚ Ω) : ℤ_[l]) := fun s => by
    rw [← Units.val_mul, ← MonoidHom.mul_apply, hθθ]; rfl
  have hχs : ∀ (s : ↥(Dec (F := ℚ) A)) (m : Lev ((l : c.O) ^ n)),
      ((χ s : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) • m = (((θ s : c.Oˣ) : c.O) * ((θ' s : c.Oˣ) : c.O)) • m := by
    intro s m
    rw [hchi, padic_smul]; rfl
  have key : ∀ (s : ↥(Dec (F := ℚ) A)) (x : c.O) (m : Lev ((l : c.O) ^ n)),
      ((χ s : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) * φ₀ (x • rho s⁻¹ m) = φ₀ ((((θ s : c.Oˣ) : c.O) * x) • m) := by
    intro s x m
    rw [← smul_eq_mul, ← map_smul, hχs, scal_apply, smul_smul, smul_smul, map_inv]
    congr 2
    calc _ = (((θ s : c.Oˣ) : c.O) * x) * (((θ' s : c.Oˣ) : c.O) * (((θ' s)⁻¹ : c.Oˣ) : c.O)) := by ring
      _ = _ := by rw [Units.mul_inv, mul_one]

  let bs : ↥(Dec (F := ℚ) A) → TDual (ZMod (l ^ n)) (Lev ((l : c.O) ^ n)) :=
    fun s => TDual.mk (φ₀ ∘ₗ smulZ c n (b s))
  let sec := Function.surjInv (Lev.mk_surjective ((l : c.O) ^ n))
  have hsec : ∀ y, Lev.mk ((l : c.O) ^ n) (sec y) = y := Function.surjInv_eq _
  have hmk : Continuous (Lev.mk ((l : c.O) ^ n)) := (UpperTheory.V.X.So.adicCont l c).1 _ ha0
  have hbsc : Continuous bs := by
    refine ((continuous_of_discreteTopology (f := fun y : Lev ((l : c.O) ^ n) =>
      TDual.mk (φ₀ ∘ₗ smulZ c n (sec y)))).comp (hmk.comp hb)).congr fun s => ?_
    refine TDual.ext fun m => ?_
    show φ₀ (sec (Lev.mk ((l : c.O) ^ n) (b s)) • m) = φ₀ (b s • m)
    have hd : (l : c.O) ^ n ∣ sec (Lev.mk ((l : c.O) ^ n) (b s)) - b s := by
      rw [← Lev.mk_eq_zero, map_sub, hsec, sub_self]
    rw [smul_congr c n hd m]
  have hz : bs ∈ Z1 ((twDual χ rho).comp (MonoidHom.id _)) := by
    refine ⟨hbsc, fun s t => ?_⟩
    refine TDual.ext fun m => ?_
    show φ₀ (b (s * t) • m) = φ₀ (b s • m) + ((χ s : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) * φ₀ (b t • rho s⁻¹ m)
    rw [key, ← map_add, ← add_smul, smul_congr c n (hbc s t) m]
  obtain ⟨-, -, hbij, -, -⟩ := hT ℚ Ω l n (Lev ((l : c.O) ^ n)) A rho v (by omega) hv hc
  have h0 : (Submodule.Quotient.mk ⟨bs, hz⟩ : H1 ((twDual χ rho).comp (MonoidHom.id _))) = 0 := by
    refine hbij.1 (Eq.trans ?_ (LinearMap.map_zero _).symm)
    refine Submodule.linearMap_qext _ (LinearMap.ext fun y => ?_)
    let at' : ↥(Dec (F := ℚ) A) → c.O := fun t => sec (y.1 t)
    have hat : ∀ t, Lev.mk ((l : c.O) ^ n) (at' t) = y.1 t := fun t => hsec _
    have hac : Continuous at' := (continuous_of_discreteTopology (f := sec)).comp y.2.1
    have hacoc : ∀ s t, (l : c.O) ^ n ∣ at' (s * t) - (at' s + ((θ' s : c.Oˣ) : c.O) * at' t) := by
      intro s t
      have hm : Lev.mk ((l : c.O) ^ n) (((θ' s : c.Oˣ) : c.O) * at' t) = ((θ' s : c.Oˣ) : c.O) • Lev.mk ((l : c.O) ^ n) (at' t) := by
        rw [← smul_eq_mul, map_smul]
      rw [← Lev.mk_eq_zero, map_sub, map_add, hm, hat, hat, hat, y.2.2 s t]
      exact sub_self _
    obtain ⟨u, hu, hdiv⟩ := hcup at' hac hacoc
    change (Submodule.Quotient.mk (cupCocycleZ1Z1 _ _ _ _ _ _ _ _ _) : H2 _) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    refine ⟨fun t => φ₀ (Lev.mk ((l : c.O) ^ n) (u t)),
      (continuous_of_discreteTopology (f := ⇑φ₀)).comp (hmk.comp hu), funext fun p => ?_⟩
    obtain ⟨g, h⟩ := p
    have e1 : (((θ g : c.Oˣ) : c.O) * ((θ' g : c.Oˣ) : c.O)) • Lev.mk ((l : c.O) ^ n) (u h) -
        Lev.mk ((l : c.O) ^ n) (u (g * h)) + Lev.mk ((l : c.O) ^ n) (u g) =
        b g • ((θ' g : c.Oˣ) : c.O) • y.1 h := by
      rw [← hat h, ← map_smul, ← map_smul, ← map_smul, ← map_sub, ← map_add, smul_eq_mul, smul_eq_mul,
        smul_eq_mul]
      have := (Lev.mk_eq_zero _ _).2 (hdiv g h)
      rw [map_sub, sub_eq_zero] at this
      exact this.symm
    show ((χ g : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) * φ₀ (Lev.mk ((l : c.O) ^ n) (u h)) -
      φ₀ (Lev.mk ((l : c.O) ^ n) (u (g * h))) + φ₀ (Lev.mk ((l : c.O) ^ n) (u g)) =
      φ₀ (b g • ((θ' g : c.Oˣ) : c.O) • y.1 h)
    rw [← e1, map_add, map_sub, ← hχs, map_smul, smul_eq_mul]
  rw [Submodule.Quotient.mk_eq_zero] at h0
  obtain ⟨ψ, hψ⟩ := (mem_coboundaries1 _ _).1 (Submodule.mem_comap.1 h0)
  obtain ⟨x, hx⟩ := hφall ψ
  refine ⟨x, fun s => (hφ0 _).1 fun m => ?_⟩
  have e := congrArg (fun φ : TDual (ZMod (l ^ n)) (Lev ((l : c.O) ^ n)) => φ m) (hψ s)
  change φ₀ (b s • m) = ((χ s : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) * ψ (rho s⁻¹ m) - ψ m at e
  have hx' : ∀ m, (ψ : TDual (ZMod (l ^ n)) (Lev ((l : c.O) ^ n))) m = φ₀ (x • m) := hx
  rw [hx', hx', key] at e
  have h1 : (b s - (((θ s : c.Oˣ) : c.O) * x - x)) • m = b s • m - ((((θ s : c.Oˣ) : c.O) * x) • m - x • m) := by
    rw [lev_sub_smul, lev_sub_smul]
  refine (congrArg φ₀ h1).trans ?_
  rw [map_sub, map_sub, e, sub_self]
