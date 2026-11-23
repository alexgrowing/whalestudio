import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier

namespace GlobalTheory.ShFam.FlagCheck

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {F : Type} [Field F] {Z : Model Xo c β} {e : F ≃+* c.F}

theorem join_over [Mono (genι Z)] (C : FlagCpt Z e) (τ : E →+* ℂ) (i : Fin (Dw.mult τ))
    (w : Sp (DualNumber C.Y.Fn) ⟶ Z.oF.t.G.left) (hw : w ≫ Z.m.φ = C.f0.v τ i) :
    w ≫ Z.oF.t.G.hom = spMap (algebraMap C.Y.Fn (DualNumber C.Y.Fn)) ≫
      (letI := (constF e C.Y).toAlgebra; GlobalTheory.AllWt.ptF C.y0) := by
  have := Z.jQ_open
  rw [← cancel_mono Z.jQ, ← cancel_mono (genι Z)]
  have h1 := (C.f0.tan τ i).1
  rw [← hw, Category.assoc, Z.m.cart.1.w] at h1
  have h2 := congrArg (· ≫ genι Z) C.y0_x
  simp only [Category.assoc] at h1 h2 ⊢
  rw [h2]
  exact h1

theorem mono_genι (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) : Mono (genι Y) := by
  have : Epi (CommRingCat.ofHom (algebraMap (𝓞 c.F) c.F)) :=
    IsLocalization.epi (nonZeroDivisors (𝓞 c.F)) c.F
  have : Mono (spMap (algebraMap (𝓞 c.F) c.F)) :=
    Scheme.Spec.map_mono (CommRingCat.ofHom (algebraMap (𝓞 c.F) c.F)).op
  infer_instance

theorem Lw_weightOf (C : FlagCpt Z e) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    C.Lw (GlobalTheory.AllWt.weightOf Dw (fun x => (a x : ℤ)) ((n / 2 : ℕ) : ℤ)) = C.LEx (exKey Dw a n) := by
  have h : GlobalTheory.AllWt.weightOf Dw (fun x => (a x : ℤ)) ((n / 2 : ℕ) : ℤ) =
      GlobalTheory.AllWt.weightOf Dw (fun x => (a x : ℤ) + ((n / 2 : ℕ) : ℤ)) 0 := by
    funext τ j
    simp only [GlobalTheory.AllWt.weightOf]
    split_ifs <;> ring
  rw [FlagCpt.Lw, h, GlobalTheory.AllWt.exOf_weightOf]
  simp only [FlagCpt.LEx, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  simp [exKey, keyEx, ex, exZ]

theorem exKey_none (a : (E →+* ℂ) × ℕ → ℕ) {n : ℕ} (hn : Even n) : exKey Dw a n none = 0 := by
  obtain ⟨m, rfl⟩ := hn
  simp only [exKey, keyEx, ex]
  omega

theorem dim_count (f p q : ℕ) :
    f * ((p + q) * (p + q - 1) / 2) = f * p * q + f * (p * (p - 1) / 2) + f * (q * (q - 1) / 2) := by
  have h : (p + q).choose 2 = p * q + p.choose 2 + q.choose 2 := by
    induction q with
    | zero => simp
    | succ q ih =>
      rw [← Nat.add_assoc, Nat.choose_succ_succ' (p + q), Nat.choose_succ_succ' q, ih]
      simp only [Nat.choose_one_right]; ring
  simp only [← Nat.choose_two_right, h]; ring

theorem genericPt_eq (Y : GlobalTheory.ProjVar.Var F) (y : Y.X) :
    genericPt Y = spMap (algebraMap (Y.X.presheaf.stalk y) Y.X.functionField) ≫ stalkPt Y y :=
  (Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec Y.X).specializes trivial)).symm

theorem cover {σ : c.F →+* ℂ} {N : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ N}
    (Φ : FlagTor Z e U) (z : gen Z) : ∃ i, z ∈ Set.range (Φ.C i).π := by
  let k := AlgebraicClosure ((gen Z).residueField z)
  let x : Sp k ⟶ gen Z := spMap (algebraMap ((gen Z).residueField z) k) ≫ (gen Z).fromSpecResidueField z
  let φ : c.F →+* k := (Spec.preimage (x ≫ genStr Z)).hom
  have hφ : x ≫ genStr Z = spMap φ := (Spec.map_preimage _).symm
  obtain ⟨g⟩ := GlobalTheory.ShFam.EigLoc.exists_eigFrame E H Dw l Xo c O β Z k φ x hφ
  obtain ⟨p, ⟨hp, -⟩, -⟩ := Φ.lifts k φ x hφ g
  let s : Sp k := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k)
  refine ⟨p.1, p.2 s, ?_⟩
  rw [← Scheme.Hom.comp_apply, hp]
  exact Scheme.fromSpecResidueField_apply z _

theorem comp_eq {σ : c.F →+* ℂ} {N : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ N} (Φ : FlagTor Z e U) {k : Type} [Field k]
    [IsAlgClosed k] {φ : c.F →+* k} {x : Sp k ⟶ gen Z} (hx : x ≫ genStr Z = spMap φ) (g : EigFrame Z φ (x ≫ genι Z))
    {i j : U.Comp} {p : Sp k ⟶ (Φ.C i).Y.X} {q : Sp k ⟶ (Φ.C j).Y.X} (hp : p ≫ (Φ.C i).π = x) (hq : q ≫ (Φ.C j).π = x)
    (cp : (Φ.C i).Carries p g) (cq : (Φ.C j).Carries q g) : i = j :=
  congrArg Sigma.fst ((Φ.lifts k φ x hx g).unique (y₁ := ⟨i, p⟩) (y₂ := ⟨j, q⟩) ⟨hp, cp⟩ ⟨hq, cq⟩)

theorem bd_eq_zero (C : FlagCpt Z e) (h : ∀ y, C.π y ∉ genBd Z) : C.bd = 0 := by
  refine CartierDiv.ext_of_isEqn fun y => ?_
  have h1 : y ∉ C.bd.supp := fun hy => h y ((C.bd_supp y).1 hy)
  obtain ⟨g', hg', hu⟩ := CartierDiv.notMem_supp_iff.1 h1
  refine ⟨1, hg'.iff_unitAt.2 ?_, CartierDiv.isEqn_zero y⟩
  simpa using hu.inv

theorem not_red_double (Y : GlobalTheory.ProjVar.Var F) (Δ : Y.Dv) (hΔ : Y.Eff Δ) (y : Y.X) (hy : y ∈ Y.supp Δ) :
    ¬ ∀ (y : Y.X) (g : Y.Fnˣ), (2 • Δ).IsEqn y g → ∀ (f : Y.Fn) (n : ℕ), RegAt y f → RegAt y (f ^ n / g) →
      RegAt y (f / g) := fun h => by
  obtain ⟨g, hg⟩ := Δ.exists_isEqn y
  have hr : RegAt y (g : Y.Fn) := by simpa using hg.regularAt_iff.1 (hΔ y)
  have h2 := h y (g ^ 2) (hg.nsmul 2) g 2 hr (by simpa using (unitAt_one y).regAt)
  have h3 : RegAt y (g : Y.Fn)⁻¹ := by
    convert h2 using 1
    rw [Units.val_pow_eq_pow_val]; field_simp
  refine CartierDiv.notMem_supp_iff.2 ⟨g, hg, ?_⟩ hy
  obtain ⟨a, ha⟩ := hr
  obtain ⟨b, hb⟩ := h3
  refine ⟨a, IsUnit.of_mul_eq_one b (IsFractionRing.injective _ Y.X.functionField ?_), by rw [one_mul]; exact ha⟩
  rw [map_mul, map_one]
  exact (congrArg₂ (· * ·) ha hb).trans (mul_inv_cancel₀ g.ne_zero)

end GlobalTheory.ShFam.FlagCheck
