import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSatAtConstOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivLocProdTriv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSatakeParameterSphericalUnramifiedUnitary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.CuspRep.LocEx Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC

namespace GlobalTheory.UnitaryBC.SatEx

section Abstract

variable {G H : Type} [Group G] [Group H]

def pull (π : Submodule ℂ (G → ℂ)) (hst : ∀ x, ∀ φ ∈ π, rightReg ℂ G ℂ x φ ∈ π) (j : H →* G) : Representation ℂ H π :=
  (sub (rightReg ℂ G ℂ) π hst).comp j

variable [TopologicalSpace H] {π : Submodule ℂ (G → ℂ)} {hst : ∀ x, ∀ φ ∈ π, rightReg ℂ G ℂ x φ ∈ π}
  {j : H →* G} {p : G →* H} {Z : Subgroup G}

theorem pull_eq_bot [IsTopologicalGroup H]
    (hirr : ∀ W ≤ π, (∀ x, ∀ φ ∈ W, rightReg ℂ G ℂ x φ ∈ W) → W = ⊥ ∨ W = π)
    (hdec : ∀ x, (j (p x))⁻¹ * x ∈ Z) (hZ : ∀ x ∈ Z, ∀ h, x * j h = j h * x) (hsm : IsSmooth (pull π hst j))
    {K : Subgroup H} (hK : IsCompact (K : Set H)) {φ : π} (h0 : φ ≠ 0) (hφ : φ ∈ fixed (pull π hst j) K)
    (W : Submodule ℂ π) (hW : ∀ g, ∀ v ∈ W, pull π hst j g v ∈ W) (h : W ⊓ fixed (pull π hst j) K = ⊥) : W = ⊥ := by
  have hi := Submodule.map_injective_of_injective π.injective_subtype
  have hst' : ∀ (x : G) (v : π), v ∈ nullPart (pull π hst j) K →
      sub (rightReg ℂ G ℂ) π hst x v ∈ nullPart (pull π hst j) K := by
    intro x v hv
    have h1 := nullPart_act (pull π hst j) K (p x) (nullPart_comm (pull π hst j) K
      (sub (rightReg ℂ G ℂ) π hst ((j (p x))⁻¹ * x)) (fun g y => by
        change sub (rightReg ℂ G ℂ) π hst _ (sub (rightReg ℂ G ℂ) π hst (j g) y) =
          sub (rightReg ℂ G ℂ) π hst (j g) (sub (rightReg ℂ G ℂ) π hst _ y)
        rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, hZ _ (hdec x)]) hv)
    have h2 : pull π hst j (p x) (sub (rightReg ℂ G ℂ) π hst ((j (p x))⁻¹ * x) v) =
        sub (rightReg ℂ G ℂ) π hst x v := by
      change sub (rightReg ℂ G ℂ) π hst (j (p x)) (sub (rightReg ℂ G ℂ) π hst _ v) = _
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
    rwa [h2] at h1
  rcases hirr ((nullPart (pull π hst j) K).map π.subtype) (Submodule.map_subtype_le _ _) (by
    rintro x _ ⟨v, hv, rfl⟩
    exact ⟨_, hst' x v hv, rfl⟩) with h1 | h1
  · have h2 : nullPart (pull π hst j) K = ⊥ := hi (h1.trans (Submodule.map_bot _).symm)
    exact le_bot_iff.1 (h2 ▸ le_nullPart hsm hK W hW h)
  · have h2 : nullPart (pull π hst j) K = ⊤ := hi (h1.trans (Submodule.map_subtype_top _).symm)
    exact absurd (eq_zero_of_mem_nullPart hsm hK hφ (h2 ▸ Submodule.mem_top)) h0

theorem exists_spherical [IsTopologicalGroup H]
    (hirr : ∀ W ≤ π, (∀ x, ∀ φ ∈ W, rightReg ℂ G ℂ x φ ∈ W) → W = ⊥ ∨ W = π)
    (hdec : ∀ x, (j (p x))⁻¹ * x ∈ Z) (hZ : ∀ x ∈ Z, ∀ h, x * j h = j h * x) (hsm : IsSmooth (pull π hst j))
    {K : Subgroup H} (hKo : IsOpen (K : Set H)) (hK : IsCompact (K : Set H)) {φ : π} (h0 : φ ≠ 0)
    (hφ : φ ∈ fixed (pull π hst j) K) (U : Submodule ℂ π) (hU : ∀ g, ∀ v ∈ U, pull π hst j g v ∈ U) (hφU : φ ∈ U)
    (hfin : ∀ K' : Subgroup H, IsOpen (K' : Set H) → FiniteDimensional ℂ ↥(U ⊓ fixed (pull π hst j) K')) :
    ∃ σ : SmIrr H, IsAdmissible σ.ρ ∧ GlobalTheory.LGrp.IsSpherical σ.ρ K ∧
      ∃ f : σ.V →ₗ[ℂ] π, f ≠ 0 ∧ ∀ g v, f (σ.ρ g v) = pull π hst j g (f v) := by
  have h2 := pull_eq_bot (hst := hst) hirr hdec hZ hsm hK h0 hφ
  obtain ⟨σ, ⟨f, hf0, hf⟩, ha⟩ := exists_irred hsm hKo h2 U hU ((Submodule.ne_bot_iff _).2 ⟨φ, hφU, h0⟩) hfin
  refine ⟨σ, ha, ?_, f, hf0, hf⟩
  have hker : LinearMap.ker f = ⊥ := by
    rcases ((CuspRep.isIrreducible_iff _).1 σ.irred).2 (LinearMap.ker f) (fun g v hv => by
      rw [LinearMap.mem_ker, hf, LinearMap.mem_ker.1 hv, map_zero]) with h | h
    · exact h
    · exact absurd (LinearMap.ker_eq_top.1 h) hf0
  have hr : LinearMap.range f ≠ ⊥ := by rwa [Ne, LinearMap.range_eq_bot]
  have hW : LinearMap.range f ⊓ fixed (pull π hst j) K ≠ ⊥ := fun e => hr (h2 _ (by
    rintro g _ ⟨v, rfl⟩
    exact ⟨_, hf g v⟩) e)
  obtain ⟨x, ⟨⟨u, rfl⟩, hx⟩, hx0⟩ := (Submodule.ne_bot_iff _).1 hW
  refine (Submodule.ne_bot_iff _).2 ⟨u, mem_fix.2 fun k hk => LinearMap.ker_eq_bot.1 hker ?_,
    fun e => hx0 (by rw [e, map_zero])⟩
  rw [hf]
  exact mem_fix.1 hx k hk

end Abstract

section Chart

variable {L : Type} [Field L] {n : ℕ} {s : L →+* L}

theorem conj_form (b : GL (Fin n) L) (hb : cT s b.1 * b.1 = antiJ L n) (x : GL (Fin n) L) :
    cT s (b⁻¹ * x * b).1 * antiJ L n * (b⁻¹ * x * b).1 = cT s b.1 * (cT s x.1 * x.1) * b.1 := by
  have h1 : cT s (b⁻¹).1 * cT s b.1 = 1 := by rw [← cT_mul, Units.mul_inv, cT_one]
  have h2 : b.1 * (b⁻¹).1 = 1 := Units.mul_inv b
  simp only [Units.val_mul, cT_mul, ← hb]
  calc cT s b.1 * (cT s x.1 * cT s (b⁻¹).1) * (cT s b.1 * b.1) * ((b⁻¹).1 * x.1 * b.1)
      = cT s b.1 * cT s x.1 * (cT s (b⁻¹).1 * cT s b.1) * (b.1 * (b⁻¹).1) * x.1 * b.1 := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1, h2]; simp only [Matrix.mul_one, Matrix.mul_assoc]

def toAnti (b : GL (Fin n) L) (hb : cT s b.1 * b.1 = antiJ L n) : UJ s (1 : Matrix (Fin n) (Fin n) L) ≃* GU s n where
  toFun x := ⟨b⁻¹ * x.1 * b, by
    have h : cT s x.1.1 * 1 * x.1.1 = 1 := x.2
    rw [Matrix.mul_one] at h
    change _ * _ * _ = _
    rw [conj_form b hb, h, Matrix.mul_one, hb]⟩
  invFun g := ⟨b * g.1 * b⁻¹, by
    have h := conj_form b hb (b * g.1 * b⁻¹)
    rw [show b⁻¹ * (b * g.1 * b⁻¹) * b = g.1 by group, show _ * _ * _ = _ from g.2, ← hb] at h
    have hc : IsUnit (cT s b.1) := IsUnit.of_mul_eq_one (cT s (b⁻¹).1) (by rw [← cT_mul, Units.inv_mul, cT_one])
    have h3 := hc.mul_right_inj.1 (b.isUnit.mul_left_inj.1 (show cT s b.1 * 1 * b.1 = cT s b.1 * (cT s (b * g.1 * b⁻¹).1 * (b * g.1 * b⁻¹).1) * b.1 by
      rw [Matrix.mul_one]; exact h))
    change _ * _ * _ = _
    rw [Matrix.mul_one]
    exact h3.symm⟩
  left_inv x := Subtype.ext (show b * (b⁻¹ * x.1 * b) * b⁻¹ = x.1 by group)
  right_inv g := Subtype.ext (show b⁻¹ * (b * g.1 * b⁻¹) * b = g.1 by group)
  map_mul' x y := Subtype.ext (show b⁻¹ * (x.1 * y.1) * b = (b⁻¹ * x.1 * b) * (b⁻¹ * y.1 * b) by group)

end Chart

section ChartTop

variable {L : Type} [Field L] [TopologicalSpace L] [IsTopologicalRing L] {n : ℕ} {s : L →+* L}

theorem continuous_toAnti (b : GL (Fin n) L) (hb : cT s b.1 * b.1 = antiJ L n) :
    Continuous (toAnti b hb) ∧ Continuous (toAnti b hb).symm :=
  ⟨((continuous_const.mul (continuous_subtype_val.comp continuous_id)).mul continuous_const).subtype_mk _,
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _⟩

end ChartTop

section Concrete

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem continuous_cLoc (w : HeightOneSpectrum (𝓞 E)) : Continuous (cLoc (E := E) (n := n) w) :=
  (Continuous.units_map _ (continuous_id.matrix_map
    ((RestrictedProduct.continuous_eval w).comp (continuous_snd : Continuous (pFin E))))).comp continuous_subtype_val

theorem cLoc_infU (w : HeightOneSpectrum (𝓞 E)) (y : infU E n) : cLoc w (y : UA E n) = 1 := by
  have h : (y.1.1.val).map (pFin E) = 1 := congrArg Units.val y.2
  refine Units.ext (Matrix.ext fun i k => ?_)
  have h2 := congrFun (congrFun h i) k
  change pLoc E w (pFin E (y.1.1.val i k)) = (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i k
  rw [show pFin E (y.1.1.val i k) = (1 : Matrix (Fin n) (Fin n) (Af E)) i k from h2, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

def coefMap (φ : UA E n → ℂ) :
    Module.Dual ℂ (Submodule.span ℂ (Set.range fun k : infU E n => RU E n k φ)) →ₗ[ℂ] (infU E n → ℂ) :=
  LinearMap.pi fun y => Module.Dual.eval ℂ _ ⟨RU E n y φ, Submodule.subset_span ⟨y, rfl⟩⟩

theorem coef_mem (φ : UA E n → ℂ) (g : UA E n) :
    (fun y : infU E n => φ (g * (y : UA E n))) ∈ LinearMap.range (coefMap φ) :=
  ⟨(LinearMap.proj g).comp (Submodule.subtype _), rfl⟩

def typeU (π : Submodule ℂ (UA E n → ℂ)) (w : HeightOneSpectrum (𝓞 E)) (L : Subgroup (finU E n))
    (C : Submodule ℂ (infU E n → ℂ)) : Submodule ℂ π where
  carrier := {ψ | (∀ k ∈ L, cLoc w (k : UA E n) = 1 → RU E n k ψ.1 = ψ.1) ∧
    ∀ g, (fun y : infU E n => ψ.1 (g * (y : UA E n))) ∈ C}
  add_mem' := fun {a b} hx hy => ⟨fun k h1 h2 => by
    rw [Submodule.coe_add, map_add, hx.1 k h1 h2, hy.1 k h1 h2], fun g => add_mem (hx.2 g) (hy.2 g)⟩
  zero_mem' := ⟨fun _ _ _ => map_zero _, fun _ => zero_mem _⟩
  smul_mem' := fun c a hx => ⟨fun k h1 h2 => by
    rw [Submodule.coe_smul, map_smul, hx.1 k h1 h2], fun g => Submodule.smul_mem _ c (hx.2 g)⟩

variable {π : Submodule ℂ (UA E n → ℂ)} {w : HeightOneSpectrum (𝓞 E)} {H : Type} [Group H]

theorem typeU_act {hst : ∀ x, ∀ φ ∈ π, rightReg ℂ (UA E n) ℂ x φ ∈ π} {L : Subgroup (finU E n)}
    {C : Submodule ℂ (infU E n → ℂ)} {j : H →* UA E n} (hZ : ∀ x, cLoc w x = 1 → ∀ h, x * j h = j h * x) (h : H)
    (v : π) (hv : v ∈ typeU π w L C) : pull π hst j h v ∈ typeU π w L C := by
  refine ⟨fun k h1 h2 => ?_, fun g => ?_⟩
  · change RU E n k (RU E n (j h) v.1) = RU E n (j h) v.1
    rw [← Module.End.mul_apply, ← map_mul, hZ _ h2, map_mul, Module.End.mul_apply, hv.1 k h1 h2]
  · have e : (fun y : infU E n => (pull π hst j h v).1 (g * (y : UA E n))) =
        fun y : infU E n => v.1 (g * j h * (y : UA E n)) := funext fun y => by
      change v.1 (g * y * j h) = _
      rw [mul_assoc, mul_assoc, hZ _ (cLoc_infU w y)]
    rw [e]
    exact hv.2 _

theorem finiteDimensional_typeU [TopologicalSpace H] (hπ : IsAutRepU π) {j : H →* UA E n} {p : UA E n →* H}
    (hjf : ∀ h, j h ∈ finU E n) (hjc : Continuous j) (hpc : Continuous p)
    (hdec : ∀ x, cLoc w ((j (p x))⁻¹ * x) = 1) {L : Subgroup (finU E n)} (hL : IsOpen (L : Set (finU E n)))
    {C : Submodule ℂ (infU E n → ℂ)}
    (hfin : ∀ L : Subgroup (finU E n), IsOpen (L : Set (finU E n)) → FiniteDimensional ℂ (Submodule.span ℂ
      {ψ : UA E n → ℂ | (∀ γ ∈ ratU E n, ∀ g, ψ (γ * g) = ψ g) ∧ (∀ k ∈ L, ∀ g, ψ (g * (k : UA E n)) = ψ g) ∧
        ∀ g, (fun y : infU E n => ψ (g * (y : UA E n))) ∈ C}))
    (K' : Subgroup H) (hK' : IsOpen (K' : Set H)) :
    FiniteDimensional ℂ ↥(typeU π w L C ⊓ fixed (pull π hπ.stable j) K') := by
  let jp : finU E n →* finU E n := ((j.comp p).comp (finU E n).subtype).codRestrict (finU E n) fun k => hjf _
  have hjp : Continuous jp := (hjc.comp (hpc.comp continuous_subtype_val)).subtype_mk _
  let L' : Subgroup (finU E n) := L ⊓ K'.comap (p.comp (finU E n).subtype) ⊓ L.comap jp
  have ho : IsOpen (L' : Set (finU E n)) :=
    (hL.inter (hK'.preimage (hpc.comp continuous_subtype_val))).inter (hL.preimage hjp)
  have := hfin L' ho
  refine FiniteDimensional.of_injective ((π.subtype ∘ₗ (typeU π w L C ⊓ fixed (pull π hπ.stable j) K').subtype).codRestrict
    (Submodule.span ℂ {ψ : UA E n → ℂ | (∀ γ ∈ ratU E n, ∀ g, ψ (γ * g) = ψ g) ∧
      (∀ k ∈ L', ∀ g, ψ (g * (k : UA E n)) = ψ g) ∧ ∀ g, (fun y : infU E n => ψ (g * (y : UA E n))) ∈ C})
    fun v => Submodule.subset_span ⟨(hπ.aut _ v.1.2).left, fun k hk g => ?_, v.2.1.2⟩)
    fun v v' e => Subtype.ext (Subtype.ext (by have e' := congrArg Subtype.val e; exact e'))
  have h1 : RU E n ((j (p k))⁻¹ * k) v.1.1 = v.1.1 :=
    v.2.1.1 ((jp k)⁻¹ * k) (L.mul_mem (L.inv_mem hk.2) hk.1.1) (hdec k)
  have h2 := mem_fix.1 v.2.2 _ hk.1.2
  have h3 : RU E n k v.1.1 = v.1.1 := by
    rw [show (k : UA E n) = j (p k) * ((j (p k))⁻¹ * k) from (mul_inv_cancel_left _ _).symm, map_mul,
      Module.End.mul_apply, h1]
    exact congrArg Subtype.val h2
  exact congrFun h3 g

end Concrete

theorem exists_hasSatAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E))
    (s : w.adicCompletion E →+* w.adicCompletion E) (ϖ : w.adicCompletion E) (q : ℕ),
    (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) → Formalism.UG.IsUnramInv ϖ s q →
    (∀ L : Subgroup (finU E n), IsOpen (L : Set (finU E n)) → ∀ C : Submodule ℂ (infU E n → ℂ),
      FiniteDimensional ℂ C → FiniteDimensional ℂ (Submodule.span ℂ {ψ : UA E n → ℂ |
        (∀ γ ∈ ratU E n, ∀ g, ψ (γ * g) = ψ g) ∧ (∀ k ∈ L, ∀ g, ψ (g * (k : UA E n)) = ψ g) ∧
          ∀ g, (fun y : infU E n => ψ (g * (y : UA E n))) ∈ C})) →
    (∃ ι : Formalism.UG.UJ s (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) →* UA E n, Continuous ι ∧
      (∀ g, ι g ∈ locU n w ∧ cLoc w (ι g) = g.1) ∧ (∀ x ∈ locU n w, cLoc w x = 1 → x = 1) ∧
        ∀ x g, cLoc w x = 1 → x * ι g = ι g * x) →
    ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → IsUnramU π w → ∃ α, HasSatAt π w s ϖ q α := by
  intro E _ _ _ n w s ϖ q hs hU hfin ⟨ι, hιc, hιl, hι1, hι2⟩ π hπ ⟨φ, hφ, h0, hφK⟩
  obtain ⟨b, hb, e⟩ : ∃ b ∈ GlobalTheory.LFun.KGL w n, cT s b.1 * b.1 = antiJ _ n := by
    obtain ⟨k, hk, e⟩ := GlobalTheory.LFun.InertChart.exists_congr_antiJ (B := 1) hU (one_mem _) (cT_one s)
    exact ⟨k, hk, by simpa using e⟩
  let cU : UA E n →* UJ s (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) :=
    (cLoc w).codRestrict _ fun x => by
      change cT s _ * 1 * _ = 1
      rw [Matrix.mul_one]
      exact cT_cLoc w s hs hU.2.1 x
  let a := toAnti b e
  let p : UA E n →* GU s n := a.toMonoidHom.comp cU
  let j : GU s n →* UA E n := ι.comp a.symm.toMonoidHom
  have hcj : ∀ g, cLoc w (j g) = (a.symm g).1 := fun g => (hιl _).2
  have hjl : ∀ g, j g ∈ locU n w := fun g => (hιl _).1
  have hdec : ∀ x, cLoc w ((j (p x))⁻¹ * x) = 1 := fun x => by
    rw [map_mul, map_inv, hcj]
    change ((a.symm (a (cU x))).1)⁻¹ * cLoc w x = 1
    rw [a.symm_apply_apply]
    exact inv_mul_cancel _
  have hZ : ∀ x, cLoc w x = 1 → ∀ h, x * j h = j h * x := fun x hx h => hι2 x _ hx
  have hpj : ∀ x ∈ locU n w, j (p x) = x := fun x hx =>
    (inv_mul_eq_one.1 (hι1 _ (mul_mem (inv_mem (hjl _)) hx) (hdec x)))
  have hjc : Continuous j := hιc.comp (continuous_toAnti b e).2
  have hpc : Continuous p := (continuous_toAnti b e).1.comp ((continuous_cLoc w).subtype_mk _)
  have hjf : ∀ h, j h ∈ finU E n := fun h => (hjl h).1
  have hsm : IsSmooth (pull π hπ.stable j) := fun v => by
    have h1 := (hπ.aut _ v.2).level.preimage (hjc.subtype_mk hjf)
    have h2 : {g : GU s n | pull π hπ.stable j g v = v} =
        (fun g => (⟨j g, hjf g⟩ : finU E n)) ⁻¹' {k : finU E n | RU E n k v.1 = v.1} :=
      Set.ext fun g => Subtype.ext_iff
    rw [h2]
    exact h1
  obtain ⟨hKo, hKc⟩ := GlobalTheory.T.isOpen_isCompact_unitaryIntegralPoints _ ϖ s q n hU
  have hKb : ∀ k ∈ KU s n, k.1 ∈ GlobalTheory.LFun.KGL w n := fun k hk => (Subgroup.mem_subgroupOf.1 hk).2
  have hφ' : (⟨φ, hφ⟩ : π) ∈ fixed (pull π hπ.stable j) (KU s n) := mem_fix.2 fun k hk => Subtype.ext
    (hφK _ (hjl k) (by
      rw [hcj]
      exact mul_mem (mul_mem hb (hKb k hk)) (inv_mem hb)))
  have h0' : (⟨φ, hφ⟩ : π) ≠ 0 := fun e => h0 (congrArg Subtype.val e)
  have hC : FiniteDimensional ℂ (LinearMap.range (coefMap φ)) := by
    have : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : infU E n => RU E n k φ)) := (hπ.aut φ hφ).kfin
    infer_instance
  let L₀ : Subgroup (finU E n) := stab ((RU E n).comp (finU E n).subtype) φ
  have hL₀ : IsOpen (L₀ : Set (finU E n)) := (hπ.aut φ hφ).level
  obtain ⟨σ, ha, hsph, f, hf0, hf⟩ := exists_spherical (p := p) (Z := (cLoc w).ker) hπ.irred hdec
    (fun x hx => hZ x hx) hsm hKo hKc h0' hφ' (typeU π w L₀ (LinearMap.range (coefMap φ)))
    (fun g v hv => typeU_act hZ g v hv) ⟨fun k hk _ => hk, fun g => coef_mem φ g⟩
    (finiteDimensional_typeU hπ hjf hjc hpc hdec hL₀ fun L hL => hfin L hL _ hC)
  obtain ⟨α, hα⟩ := GlobalTheory.LFun.ExSatU.exists_hasSatU E w ϖ s q n hU σ.V σ.ρ σ.irred ha hsph
  refine ⟨α, b, hb, e, p.comp (locU n w).subtype, fun x => rfl, σ, ⟨σ.irred, π.subtype ∘ₗ f, fun h => hf0
    (LinearMap.ext fun v => Subtype.ext (LinearMap.congr_fun h v)), fun v => (f v).2, fun x v => ?_⟩, hα⟩
  change (f (σ.ρ (p x) v)).1 = _
  rw [hf]
  change RU E n (j (p x)) (f v).1 = _
  rw [hpj _ x.2]
  rfl

end GlobalTheory.UnitaryBC.SatEx

end
