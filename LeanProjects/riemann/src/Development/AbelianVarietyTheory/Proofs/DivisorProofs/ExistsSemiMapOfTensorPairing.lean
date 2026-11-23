import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SheafComplexPairingTensorUniversalPropertyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlueStatement

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped DirectSum TensorProduct

noncomputable section

namespace GlobalTheory.EtC.SemiTens

theorem res_map {R : Type} [CommRing R] {F G : Shv R} (f : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (z : Sec F U) :
    Sec.res g (Sec.map f z) = Sec.map f (Sec.res g z) := by
  have := congrArg (fun k => k.hom z) (f.hom.naturality g.op)
  simpa using this.symm

theorem map_zero' {R : Type} [CommRing R] {F G : Shv R} {U : Scheme.{0}} (z : Sec F U) :
    Sec.map (0 : F ⟶ G) z = 0 := by
  first
  | rfl
  | (show ((0 : F ⟶ G).hom.app (op U)).hom z = 0
     rw [Sheaf.Hom.zero_hom]; rfl)
  | (simp [Sec.map, Sheaf.zero_val])

variable {Q : ℕ} {R : Type} [CommRing R] {I J T : Cx (ZMod Q)} {I' J' K' : Cx R}

def pairHom (ν : Pair I' J' K') (ρ₁ : SemiMap I I') (ρ₂ : SemiMap J J') (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) :
    Sec (I.X s) U →+ Sec (J.X t) U →+ Sec (K'.X w) U :=
  AddMonoidHom.mk' (fun a => ((ν.mul U s t w h (ρ₁.app U s a)).toAddMonoidHom).comp (ρ₂.app U t))
    (fun a₁ a₂ => by ext b; simp)

theorem pairHom_smul (ν : Pair I' J' K') (ρ₁ : SemiMap I I') (ρ₂ : SemiMap J J') (U : Scheme.{0}) (s t w : ℤ)
    (h : s + t = w) (r : ULift.{1} (ZMod Q)) (a : Sec (I.X s) U) (b : Sec (J.X t) U) :
    pairHom ν ρ₁ ρ₂ U s t w h (r • a) b = pairHom ν ρ₁ ρ₂ U s t w h a (r • b) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, (n : ULift.{1} (ZMod Q)) = r :=
    ⟨(r.down.cast : ℤ), ULift.ext _ _ (by change ((r.down.cast : ℤ) : ZMod Q) = r.down; exact ZMod.intCast_zmod_cast _)⟩
  simp [pairHom, Int.cast_smul_eq_zsmul, map_zsmul, LinearMap.smul_apply]

def bmap (ν : Pair I' J' K') (ρ₁ : SemiMap I I') (ρ₂ : SemiMap J J') (U : Scheme.{0}) (w : ℤ) :
    Tens I J U w →+ Sec (K'.X w) U := by
  classical
  exact DirectSum.toAddMonoid fun p =>
    TensorProduct.liftAddHom (pairHom ν ρ₁ ρ₂ U p.1.1 p.1.2 w p.2) (pairHom_smul ν ρ₁ ρ₂ U p.1.1 p.1.2 w p.2)

theorem bmap_of (ν : Pair I' J' K') (ρ₁ : SemiMap I I') (ρ₂ : SemiMap J J') (U : Scheme.{0}) (w : ℤ)
    (p : {p : ℤ × ℤ // p.1 + p.2 = w}) (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    bmap ν ρ₁ ρ₂ U w (DirectSum.of _ p (a ⊗ₜ b)) = ν.mul U p.1.1 p.1.2 w p.2 (ρ₁.app U _ a) (ρ₂.app U _ b) := by
  unfold bmap
  rw [DirectSum.toAddMonoid_of]
  simp [pairHom]

theorem lift_of (τ : Pair I J T) (U : Scheme.{0}) (w : ℤ)
    (p : {p : ℤ × ℤ // p.1 + p.2 = w}) (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    τ.lift U w (DirectSum.of _ p (a ⊗ₜ b)) = τ.mul U p.1.1 p.1.2 w p.2 a b := by
  unfold Pair.lift
  rw [← DirectSum.lof_eq_of (ULift.{1} (ZMod Q)), DirectSum.toModule_lof]
  simp

theorem tensRes_of {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ)
    (p : {p : ℤ × ℤ // p.1 + p.2 = w}) (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    Tens.res g w (DirectSum.of _ p (a ⊗ₜ b)) = DirectSum.of _ p (Sec.res g a ⊗ₜ Sec.res g b) := by
  unfold Tens.res
  rw [← DirectSum.lof_eq_of (ULift.{1} (ZMod Q)), DirectSum.lmap_lof]
  simp [DirectSum.lof_eq_of]

theorem bmap_nat (ν : Pair I' J' K') (ρ₁ : SemiMap I I') (ρ₂ : SemiMap J J') {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ)
    (x : Tens I J U w) : Sec.res g (bmap ν ρ₁ ρ₂ U w x) = bmap ν ρ₁ ρ₂ V w (Tens.res g w x) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of p y =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rw [bmap_of, tensRes_of, bmap_of, ν.nat, ρ₁.nat, ρ₂.nat]
    | add y₁ y₂ h₁ h₂ => have e := congrArg₂ (· + ·) h₁ h₂; simpa only [map_add] using e
  | add x y hx hy => have e := congrArg₂ (· + ·) hx hy; simpa only [map_add] using e

end GlobalTheory.EtC.SemiTens

namespace GlobalTheory.EtC

open SemiTens in

theorem semiMap_of_tensorPair : ∀ (Q : ℕ) (R : Type) [CommRing R] {I J T : Cx (ZMod Q)} {I' J' K' : Cx R} (τ : Pair I J T),
    τ.IsTensor → ∀ (ν : Pair I' J' K') (ρ₁ : SemiMap I I') (ρ₂ : SemiMap J J'), ∃ σ : SemiMap T K',
    ∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
      σ.app U w (τ.mul U s t w h a b) = ν.mul U s t w h (ρ₁.app U s a) (ρ₂.app U t b) := by
  intro Q R _ I J T I' J' K' τ hτ ν ρ₁ ρ₂
  have H := fun w => GlobalTheory.T.sheafComplexPairing_tensor_universal_property (ZMod Q) R τ hτ w (K'.X w) (fun U => bmap ν ρ₁ ρ₂ U w)
    (fun V U g x => bmap_nat ν ρ₁ ρ₂ g w x)
  choose φ hnat hlift using H
  have hmul : ∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
      φ w U (τ.mul U s t w h a b) = ν.mul U s t w h (ρ₁.app U s a) (ρ₂.app U t b) := by
    intro U s t w h a b
    have := hlift w U (DirectSum.of _ ⟨(s, t), h⟩ (a ⊗ₜ b))
    rw [lift_of, bmap_of] at this
    exact this
  have key : ∀ (V : Scheme.{0}) (s : ℤ) (x : Tens I J V s),
      Sec.map (K'.d s (s + 1)) (bmap ν ρ₁ ρ₂ V s x) = φ (s + 1) V (Sec.map (T.d s (s + 1)) (τ.lift V s x)) := by
    intro V s x
    induction x using DirectSum.induction_on with
    | zero => simp
    | of p y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
        obtain ⟨⟨s₁, t₁⟩, hp⟩ := p
        rw [bmap_of, lift_of, ν.leibniz, τ.leibniz, map_add, Units.smul_def, Units.smul_def, map_zsmul, hmul, hmul,
          ρ₁.comm, ρ₂.comm]
      | add y₁ y₂ h₁ h₂ => have e := congrArg₂ (· + ·) h₁ h₂; simpa only [map_add] using e
    | add x y hx hy => have e := congrArg₂ (· + ·) hx hy; simpa only [map_add] using e
  refine ⟨⟨fun U w => φ w U, fun g w a => hnat w _ _ g a, ?_⟩, hmul⟩
  intro U s t y
  by_cases hst : (ComplexShape.up ℤ).Rel s t
  · have ht : t = s + 1 := hst.symm
    subst ht
    apply (GlobalTheory.T.etaleSheafSections_ext_and_glue R (K'.X (s + 1)) U).1
    obtain ⟨S, hS, hP⟩ := hτ.1 U s y
    refine ⟨S, hS, fun V g hg => ?_⟩
    obtain ⟨x, hx⟩ := hP V g hg
    rw [res_map, hnat, ← hx, hlift, key, hnat, res_map, ← hx]
  · rw [T.shape s t hst, K'.shape s t hst, map_zero', map_zero', map_zero]

end GlobalTheory.EtC
